/*
 *  Services
 *  Copyright (C) 2010 Andreas Öman
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include <pthread.h>
#include <assert.h>

#include <sys/types.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/ioctl.h>
#include <fcntl.h>
#include <errno.h>
#include <ctype.h>
#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>

#include "tvheadend.h"
#include "service.h"
#include "subscriptions.h"
#include "tsdemux.h"
#include "streaming.h"
#include "v4l.h"
#include "psi.h"
#include "packet.h"
#include "channels.h"
#include "cwc.h"
#include "capmt.h"
#include "notify.h"
#include "serviceprobe.h"
#include "atomic.h"
#include "dvb/dvb.h"
#include "htsp.h"

#define SERVICE_HASH_WIDTH 101


static void service_data_timeout(void *aux);

/**
 *
 */
static void
elementary_stream_create(service_t *s, elementary_stream_config_t *esc)
{
  elementary_stream_t *es = calloc(1, sizeof(elementary_stream_t));

  es->es_config = *esc;

  es->es_cc_valid = 0;

  es->es_startcond = 0xffffffff;
  es->es_curdts = PTS_UNSET;
  es->es_curpts = PTS_UNSET;
  es->es_prevdts = PTS_UNSET;
  
  es->es_pcr_real_last = PTS_UNSET;
  es->es_pcr_last      = PTS_UNSET;
  es->es_pcr_drift     = 0;
  es->es_pcr_recovery_fails = 0;

  es->es_blank = 0;

  LIST_INSERT_HEAD(&s->s_elementary_streams, es, es_link);
}


/**
 *
 */
static void
elementary_stream_destroy(elementary_stream_t *es)
{
  LIST_REMOVE(es, es_link);

  if(es->es_demuxer_fd != -1) {
    // XXX: Should be in DVB-code perhaps
    close(es->es_demuxer_fd);
    es->es_demuxer_fd = -1;
  }

  free(es->es_priv);

  /* Clear reassembly buffers */
  es->es_startcode = 0;
  
  sbuf_free(&es->es_buf);
  sbuf_free(&es->es_buf_ps);
  sbuf_free(&es->es_buf_a);

  if(es->es_curpkt != NULL)
    pkt_ref_dec(es->es_curpkt);

  free(es->es_global_data);


  free(es);
}

#if 0
/**
 *
 */
void
service_stream_destroy(service_t *t, elementary_stream_t *st)
{
  if(t->s_status == SERVICE_RUNNING)
    stream_clean(st);
  TAILQ_REMOVE(&t->s_components, st, es_link);
  free(->es_nicename);
  free(st);
}
#endif


/**
 * Service lock must be held
 */
static void
service_stop(service_t *s)
{
  th_descrambler_t *td;
  elementary_stream_t *es;
  const service_class_t *scl = s->s_config->sc_class;

  gtimer_disarm(&s->s_receive_timer);

  scl->scl_stop(s);

  pthread_mutex_lock(&s->s_stream_mutex);

  while((td = LIST_FIRST(&s->s_descramblers)) != NULL)
    td->td_stop(td);

  s->s_tt_commercial_advice = COMMERCIAL_UNKNOWN;
 
  assert(LIST_FIRST(&s->s_streaming_pad.sp_targets) == NULL);
  assert(LIST_FIRST(&s->s_subscriptions) == NULL);

  /**
   * Clean up each stream
   */
  while((es = LIST_FIRST(&s->s_elementary_streams)) != NULL)
    elementary_stream_destroy(es);

  s->s_status = SERVICE_IDLE;

  pthread_mutex_unlock(&s->s_stream_mutex);
}


/**
 * Remove the given subscriber from the service
 *
 * if s == NULL all subscribers will be removed
 *
 * Global lock must be held
 */
void
service_remove_subscriber(service_t *t, th_subscription_t *s, int reason)
{
  lock_assert(&global_lock);

  if(s == NULL) {
    while((s = LIST_FIRST(&t->s_subscriptions)) != NULL) {
      subscription_unlink_service(s, reason);
    }
  } else {
    subscription_unlink_service(s, reason);
  }

  if(LIST_FIRST(&t->s_subscriptions) == NULL)
    service_stop(t);
}


/**
 *
 */
int
service_start(service_t *s, unsigned int weight, int force_start)
{
  elementary_stream_config_t *esc;
  int r, timeout = 2;
  const service_class_t *scl = s->s_config->sc_class;

  lock_assert(&global_lock);

  assert(s->s_status != SERVICE_RUNNING);
  s->s_streaming_status = 0;
  s->s_pcr_drift = 0;

  if((r = scl->scl_start(s, weight, force_start)))
    return r;

  cwc_service_start(s);
  capmt_service_start(s);

  pthread_mutex_lock(&s->s_stream_mutex);

  s->s_status = SERVICE_RUNNING;
  s->s_current_pts = PTS_UNSET;

  TAILQ_FOREACH(esc, &s->s_config->sc_elementary_stream_configs, esc_link)
    elementary_stream_create(s, esc);

  pthread_mutex_unlock(&s->s_stream_mutex);

  if(scl->scl_grace_period != NULL)
    timeout = scl->scl_grace_period(s);

  gtimer_arm(&s->s_receive_timer, service_data_timeout, s, timeout);
  return 0;
}

/**
 * Return prio for the given service
 */
static int
service_get_prio(service_t *t)
{
  return 200;
}

/**
 * Return quality index for given service
 *
 * We invert the result (providers say that negative numbers are worse)
 *
 * But for sorting, we want low numbers first
 *
 * Also, we bias and trim with an offset of two to avoid counting any
 * transient errors.
 */

static int
service_get_quality(service_t *s)
{
  const service_class_t *scl = s->s_config->sc_class;
  return scl->scl_quality_index ? -MIN(scl->scl_quality_index(s) + 2, 0) : 0;
}




/**
 *  a - b  -> lowest number first
 */
static int
servicecmp(const void *A, const void *B)
{
  service_t *a = *(service_t **)A;
  service_t *b = *(service_t **)B;

  int q = service_get_quality(a) - service_get_quality(b);

  if(q != 0)
    return q; /* Quality precedes priority */

  return service_get_prio(a) - service_get_prio(b);
}


/**
 *
 */
service_t *
service_find(channel_t *ch, unsigned int weight, const char *loginfo,
	     int *errorp, service_t *skip)
{
  service_config_t *sc;
  service_t *s, **vec;
  int cnt = 0, i, r, off;
  int err = 0;

  lock_assert(&global_lock);

  /* First, sort all services in order */

  LIST_FOREACH(sc, &ch->ch_services, sc_ch_link)
    cnt++;

  vec = alloca(cnt * sizeof(service_t *));
  cnt = 0;
  LIST_FOREACH(sc, &ch->ch_services, sc_ch_link) {
    LIST_FOREACH(s, &sc->sc_services, s_config_link) {

      if(!s->s_enabled) {
	if(loginfo != NULL) {
	  tvhlog(LOG_NOTICE, "Service", "%s: Skipping \"%s\" -- not enabled",
		 loginfo, service_displayname(s));
	  err = SM_CODE_SVC_NOT_ENABLED;
	}
	continue;
      }

      if(sc->sc_class->scl_quality_index(s) < 10) {
	if(loginfo != NULL) {
	  tvhlog(LOG_NOTICE, "Service", 
		 "%s: Skipping \"%s\" -- Quality below 10%",
		 loginfo, service_displayname(s));
	  err = SM_CODE_BAD_SIGNAL;
	}
	continue;
      }
      vec[cnt++] = s;
    }
  }

  /* Sort services, lower priority should come come earlier in the vector
     (i.e. it will be more favoured when selecting a service */

  qsort(vec, cnt, sizeof(service_t *), servicecmp);

  // Skip up to the service that the caller didn't want
  // If the sorting above is not stable that might mess up things
  // temporary. But it should resolve itself eventually
  if(skip != NULL) {
    for(i = 0; i < cnt; i++) {
      if(skip == s)
	break;
    }
    off = i + 1;
  } else {
    off = 0;
  }

  /* First, try all services without stealing */
  for(i = off; i < cnt; i++) {
    s = vec[i];
    if(s->s_status == SERVICE_RUNNING) 
      return s;
    if((r = service_start(s, 0, 0)) == 0)
      return s;
    if(loginfo != NULL)
      tvhlog(LOG_DEBUG, "Service", "%s: Unable to use \"%s\" -- %s",
	     loginfo, service_displayname(s), streaming_code2txt(r));
  }

  /* Ok, nothing, try again, but supply our weight and thus, try to steal
     transponders */

  for(i = off; i < cnt; i++) {
    s = vec[i];
    if((r = service_start(s, weight, 0)) == 0)
      return s;
    *errorp = r;
  }
  if(err)
    *errorp = err;
  else if(*errorp == 0)
    *errorp = SM_CODE_NO_SERVICE;
  return NULL;
}


/**
 *
 */
unsigned int 
service_compute_weight(struct service_list *head)
{
  service_t *t;
  th_subscription_t *s;
  int w = 0;

  lock_assert(&global_lock);

  LIST_FOREACH(t, head, s_active_link) {
    LIST_FOREACH(s, &t->s_subscriptions, ths_service_link) {
      if(s->ths_weight > w)
	w = s->ths_weight;
    }
  }
  return w;
}

#if 0
/**
 *
 */
void
service_unref(service_t *t)
{
  if((atomic_add(&t->s_refcount, -1)) == 1)
    free(t);
}


/**
 *
 */
void
service_ref(service_t *t)
{
  atomic_add(&t->s_refcount, 1);
}
#endif


#if 0
/**
 * Destroy a service
 */
void
service_destroy(service_t *s)
{
  const service_class_t *sc = s->s_config->sc_class;
  elementary_stream_t *st;
  th_subscription_t *sub;
  channel_t *ch = s->s_ch;

  if(s->s_dtor != NULL)
    s->s_dtor(s);

  lock_assert(&global_lock);

  serviceprobe_delete(s);

  while((s = LIST_FIRST(&s->s_subscriptions)) != NULL) {
    subscription_unlink_service(s, SM_CODE_SOURCE_DELETED);
  }

  if(s->s_ch != NULL) {
    s->s_ch = NULL;
    LIST_REMOVE(s, s_ch_link);
  }

  LIST_REMOVE(s, s_group_link);
  LIST_REMOVE(s, s_hash_link);
  
  if(s->s_status != SERVICE_IDLE)
    service_stop(s);

  s->s_status = SERVICE_ZOMBIE;

  free(s->s_identifier);
  free(s->s_svcname);
  free(s->s_provider);
  free(s->s_dvb_default_charset);

  while((st = TAILQ_FIRST(&s->s_components)) != NULL) {
    TAILQ_REMOVE(&t->s_components, st, es_link);
    abort();
    //    free(st->es_nicename);
    free(st);
  }

  free(t->s_pat_section);
  free(t->s_pmt_section);

  service_unref(t);

  if(ch != NULL) {
    if(LIST_FIRST(&ch->ch_services) == NULL) 
      channel_delete(ch);
  }
}
#endif


/**
 *
 */
service_config_t *
service_config_create(service_class_t *scl)
{
  service_config_t *sc = calloc(1, sizeof(service_config_t));
  sc->sc_class = scl;
  return sc;
}


/**
 *
 */
service_t *
service_create(service_config_t *sc)
{
  service_t *s = calloc(1, sizeof(service_t));

  lock_assert(&global_lock);

  pthread_mutex_init(&s->s_stream_mutex, NULL);
  pthread_cond_init(&s->s_tss_cond, NULL);
  s->s_enabled = 1;
  s->s_pcr_last = PTS_UNSET;

  streaming_pad_init(&s->s_streaming_pad);
  LIST_INSERT_HEAD(&sc->sc_services, s, s_config_link);
  return s;
}


#if 0
/**
 *
 */
static void 
elementary_stream_make_nicename(service_t *s,
				elementary_stream_config_t *esc)
{
  char buf[200];
  if(esc->esc_pid != -1)
    snprintf(buf, sizeof(buf), "%s: %s @ #%d", 
	     service_displayname(s),
	     streaming_component_type2txt(esc->esc_type), esc->esc_pid);
  else
    snprintf(buf, sizeof(buf), "%s: %s", 
	     service_displayname(s),
	     streaming_component_type2txt(esc->esc_type));

  free(esc->esc_displayname);
  esc->esc_displayname = strdup(buf);
}


/**
 *
 */
void 
service_make_nicename(service_t *t)
{
  char buf[200];
  source_info_t si;
  elementary_stream_t *st;

  lock_assert(&t->s_stream_mutex);

  t->s_setsourceinfo(t, &si);

  snprintf(buf, sizeof(buf), 
	   "%s%s%s%s%s",
	   si.si_adapter ?: "", si.si_adapter && si.si_mux     ? "/" : "",
	   si.si_mux     ?: "", si.si_mux     && si.si_service ? "/" : "",
	   si.si_service ?: "");

  service_source_info_free(&si);

  free(t->s_nicename);
  t->s_nicename = strdup(buf);

  TAILQ_FOREACH(st, &t->s_components, es_link)
    service_stream_make_nicename(t, st);
}

#endif

/**
 * Add a new stream to a service
 */
elementary_stream_config_t *
elementary_stream_config_create(service_config_t *sc, int pid,
				streaming_component_type_t type)
{
  elementary_stream_config_t *esc;
  int i = 0;
  int idx = 0;

  TAILQ_FOREACH(esc, &sc->sc_elementary_stream_configs, esc_link) {
    if(esc->esc_index > idx)
      idx = esc->esc_index;
    i++;
    if(pid != -1 && esc->esc_pid == pid)
      return esc;
  }

  esc = calloc(1, sizeof(elementary_stream_config_t));
  esc->esc_index = idx + 1;
  esc->esc_type = type;

  TAILQ_INSERT_TAIL(&sc->sc_elementary_stream_configs, esc, esc_link);

  esc->esc_pid = pid;
  return esc;
}


/**
 * Find an ES based on PID
 */
elementary_stream_config_t *
service_stream_find(service_config_t *sc, int pid)
{
  elementary_stream_config_t *esc;
 
  lock_assert(&global_lock);

  TAILQ_FOREACH(esc, &sc->sc_elementary_stream_configs, esc_link)
    if(esc->esc_pid == pid)
      break;
  return NULL;
}



/**
 *
 */
void
service_map_channel(service_config_t *sc, channel_t *ch)
{
  lock_assert(&global_lock);

  if(sc->sc_ch != NULL) {
    LIST_REMOVE(sc, sc_ch_link);
    htsp_channel_update(sc->sc_ch);
    sc->sc_ch = NULL;
  }

  if(ch != NULL) {
    sc->sc_ch = ch;
    LIST_INSERT_HEAD(&ch->ch_services, sc, sc_ch_link);
    htsp_channel_update(sc->sc_ch);
  }
}

#if 0
/**
 *
 */
void
service_set_dvb_default_charset(service_t *t, const char *dvb_default_charset)
{
  lock_assert(&global_lock);

  if(t->s_dvb_default_charset != NULL && !strcmp(t->s_dvb_default_charset, dvb_default_charset))
    return;

  free(t->s_dvb_default_charset);
  t->s_dvb_default_charset = strdup(dvb_default_charset);
  t->s_config_save(t);
}
#endif


/**
 *
 */
static void
service_data_timeout(void *aux)
{
  service_t *t = aux;

  pthread_mutex_lock(&t->s_stream_mutex);

  if(!(t->s_streaming_status & TSS_PACKETS))
    service_set_streaming_status_flags(t, TSS_GRACEPERIOD);

  pthread_mutex_unlock(&t->s_stream_mutex);
}

/**
 *
 */
static struct strtab stypetab[] = {
  { "SDTV",         ST_SDTV },
  { "Radio",        ST_RADIO },
  { "HDTV",         ST_HDTV },
  { "SDTV-AC",      ST_AC_SDTV },
  { "HDTV-AC",      ST_AC_HDTV },
};

const char *
service_servicetype_txt(const service_config_t *sc)
{
  return val2str(sc->sc_servicetype, stypetab) ?: "Other";
}

/**
 *
 */
int
service_is_tv(const service_config_t *sc)
{
  return 
    sc->sc_servicetype == ST_SDTV    ||
    sc->sc_servicetype == ST_HDTV    ||
    sc->sc_servicetype == ST_AC_SDTV ||
    sc->sc_servicetype == ST_AC_HDTV;
}

/**
 *
 */
int
service_is_radio(const service_config_t *sc)
{
  return sc->sc_servicetype == ST_RADIO;
}

/**
 *
 */
void
service_set_streaming_status_flags(service_t *t, int set)
{
  int n;
  streaming_message_t *sm;
  lock_assert(&t->s_stream_mutex);
  
  n = t->s_streaming_status;
  
  n |= set;

  if(n == t->s_streaming_status)
    return; // Already set

  t->s_streaming_status = n;

  tvhlog(LOG_DEBUG, "Service", "%s: Status changed to %s%s%s%s%s%s%s",
	 "FIXME"__FILE__,
	 n & TSS_INPUT_HARDWARE ? "[Hardware input] " : "",
	 n & TSS_INPUT_SERVICE  ? "[Input on service] " : "",
	 n & TSS_MUX_PACKETS    ? "[Demuxed packets] " : "",
	 n & TSS_PACKETS        ? "[Reassembled packets] " : "",
	 n & TSS_NO_DESCRAMBLER ? "[No available descrambler] " : "",
	 n & TSS_NO_ACCESS      ? "[No access] " : "",
	 n & TSS_GRACEPERIOD    ? "[Graceperiod expired] " : "");

  sm = streaming_msg_create_code(SMT_SERVICE_STATUS,
				 t->s_streaming_status);
  streaming_pad_deliver(&t->s_streaming_pad, sm);
  streaming_msg_free(sm);

  pthread_cond_broadcast(&t->s_tss_cond);
}


/**
 * Restart output on a service.
 * Happens if the stream composition changes. 
 * (i.e. an AC3 stream disappears, etc)
 */
void
service_restart(service_t *s, int had_components)
{
  streaming_message_t *sm;
  const service_config_t *sc = s->s_config;
  const service_class_t *scl = sc->sc_class;

  lock_assert(&s->s_stream_mutex);

  if(had_components) {
    sm = streaming_msg_create_code(SMT_STOP, SM_CODE_SOURCE_RECONFIGURED);
    streaming_pad_deliver(&s->s_streaming_pad, sm);
    streaming_msg_free(sm);
  }

  if(scl->scl_refresh != NULL)
    scl->scl_refresh(s);

  if(TAILQ_FIRST(&sc->sc_elementary_stream_configs) != NULL) {

    sm = streaming_msg_create_data(SMT_START, 
				   service_build_stream_start(s));
    streaming_pad_deliver(&s->s_streaming_pad, sm);
    streaming_msg_free(sm);
  }
}


/**
 * Generate a message containing info about all components
 */
streaming_start_t *
service_build_stream_start(service_t *s)
{
  int n = 0;
  streaming_start_t *ss;
  const service_config_t *sc = s->s_config;
  const elementary_stream_config_t *esc;

  lock_assert(&global_lock);

  TAILQ_FOREACH(esc, &sc->sc_elementary_stream_configs, esc_link)
    n++;

  ss = calloc(1, sizeof(streaming_start_t) + 
	      sizeof(streaming_start_component_t) * n);

  ss->ss_num_components = n;
  
  n = 0;
  TAILQ_FOREACH(esc, &sc->sc_elementary_stream_configs, esc_link) {
    streaming_start_component_t *ssc = &ss->ss_components[n++];

    ssc->ssc_index = esc->esc_index;
    ssc->ssc_type  = esc->esc_type;
    memcpy(ssc->ssc_lang, esc->esc_lang, 4);
    ssc->ssc_composition_id = esc->esc_composition_id;
    ssc->ssc_ancillary_id = esc->esc_ancillary_id;
    ssc->ssc_pid = esc->esc_pid;
    ssc->ssc_width = esc->esc_width;
    ssc->ssc_height = esc->esc_height;
  }

  sc->sc_class->scl_getsourceinfo(s, &ss->ss_si);

  ss->ss_refcount = 1;
  ss->ss_pcr_pid = sc->sc_pcr_pid;
  return ss;
}


/**
 *
 */
void
service_set_enable(service_t *t, int enabled)
{
  if(t->s_enabled == enabled)
    return;

  t->s_enabled = enabled;
  abort(); // t->s_config_save(t);
  subscription_reschedule();
}


static pthread_mutex_t pending_save_mutex;
static pthread_cond_t pending_save_cond;
static struct service_queue pending_save_queue;

/**
 *
 */
void
service_request_save(service_t *t, int restart)
{
  pthread_mutex_lock(&pending_save_mutex);

  if(!t->s_ps_onqueue) {
    t->s_ps_onqueue = 1 + !!restart;
    TAILQ_INSERT_TAIL(&pending_save_queue, t, s_ps_link);
    service_ref(t);
    pthread_cond_signal(&pending_save_cond);
  } else if(restart) {
    t->s_ps_onqueue = 2; // upgrade to restart too
  }

  pthread_mutex_unlock(&pending_save_mutex);
}

#if 0

/**
 *
 */
static void *
service_saver(void *aux)
{
  service_t *t;
  int restart;
  pthread_mutex_lock(&pending_save_mutex);

  while(1) {

    if((t = TAILQ_FIRST(&pending_save_queue)) == NULL) {
      pthread_cond_wait(&pending_save_cond, &pending_save_mutex);
      continue;
    }
    assert(t->s_ps_onqueue != 0);
    restart = t->s_ps_onqueue == 2;

    TAILQ_REMOVE(&pending_save_queue, t, s_ps_link);
    t->s_ps_onqueue = 0;

    pthread_mutex_unlock(&pending_save_mutex);
    pthread_mutex_lock(&global_lock);

    if(t->s_status != SERVICE_ZOMBIE)
      t->s_config_save(t);
    if(t->s_status == SERVICE_RUNNING && restart) {
      pthread_mutex_lock(&t->s_stream_mutex);
      service_restart(t, 1);
      pthread_mutex_unlock(&t->s_stream_mutex);
    }
    service_unref(t);

    pthread_mutex_unlock(&global_lock);
    pthread_mutex_lock(&pending_save_mutex);
  }
  return NULL;
}
#endif


/**
 *
 */
void
service_init(void)
{
#if 0
  pthread_t tid;
  TAILQ_INIT(&pending_save_queue);
  pthread_mutex_init(&pending_save_mutex, NULL);
  pthread_cond_init(&pending_save_cond, NULL);
  pthread_create(&tid, NULL, service_saver, NULL);
#endif
}


/**
 *
 */
void
service_source_info_free(struct source_info *si)
{
  free(si->si_device);
  free(si->si_adapter);
  free(si->si_network);
  free(si->si_mux);
  free(si->si_provider);
  free(si->si_service);
}


void
service_source_info_copy(source_info_t *dst, const source_info_t *src)
{
#define COPY(x) dst->si_##x = src->si_##x ? strdup(src->si_##x) : NULL
  COPY(device);
  COPY(adapter);
  COPY(network);
  COPY(mux);
  COPY(provider);
  COPY(service);
#undef COPY
}


const char *
service_tss2text(int flags)
{
  if(flags & TSS_NO_ACCESS)
    return "No access";

  if(flags & TSS_NO_DESCRAMBLER)
    return "No descrambler";

  if(flags & TSS_PACKETS)
    return "Got valid packets";

  if(flags & TSS_MUX_PACKETS)
    return "Got multiplexed packets but could not decode further";

  if(flags & TSS_INPUT_SERVICE)
    return "Got packets for this service but could not decode further";

  if(flags & TSS_INPUT_HARDWARE)
    return "Sensed input from hardware but nothing for the service";

  if(flags & TSS_GRACEPERIOD)
    return "No input detected";

  return "No status";
}


/**
 *
 */
int
tss2errcode(int tss)
{
  if(tss & TSS_NO_ACCESS)
    return SM_CODE_NO_ACCESS;

  if(tss & TSS_NO_DESCRAMBLER)
    return SM_CODE_NO_DESCRAMBLER;

  if(tss & TSS_GRACEPERIOD)
    return SM_CODE_NO_INPUT;

  return SM_CODE_OK;
}

#if 0
/**
 *
 */
void
service_refresh_channel(service_t *t)
{
  if(t->s_ch != NULL)
    htsp_channel_update(t->s_ch);
}


/**
 * Get the encryption CAID from a service
 * only the first CA stream in a service is returned
 */
uint16_t
service_get_encryption(service_t *t)
{
  elementary_stream_t *st;
  caid_t *c;

  TAILQ_FOREACH(st, &t->s_components, es_link) {
    switch(st->es_type) {
    case SCT_CA:
      LIST_FOREACH(c, &st->es_caids, link)
	if(c->caid != 0)
	  return c->caid;
      break;
    default:
      break;
    }
  }
  return 0;
}


/**
 * Get the signal status from a service
 */
int
service_get_signal_status(service_t *t, signal_status_t *status)
{
  abort();
}

#endif

