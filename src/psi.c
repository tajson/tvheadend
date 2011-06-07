/*
 *  MPEG TS Program Specific Information code
 *  Copyright (C) 2007 - 2010 Andreas Öman
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

#include <assert.h>
#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>

#include "tvheadend.h"
#include "psi.h"
#include "dvb/dvb_support.h"
#include "tsdemux.h"
#include "parsers.h"

static int
psi_section_reassemble0(psi_section_t *ps, const uint8_t *data, 
			int len, int start, int crc,
			section_handler_t *cb, void *opaque)
{
  int excess, tsize;

  if(start) {
    // Payload unit start indicator
    ps->ps_offset = 0;
    ps->ps_lock = 1;
  }

  if(!ps->ps_lock)
    return -1;

  memcpy(ps->ps_data + ps->ps_offset, data, len);
  ps->ps_offset += len;

  if(ps->ps_offset < 3) {
    /* We don't know the total length yet */
    return len;
  }

  tsize = 3 + (((ps->ps_data[1] & 0xf) << 8) | ps->ps_data[2]);
 
  if(ps->ps_offset < tsize)
    return len; // Not there yet
  
  excess = ps->ps_offset - tsize;

  if(crc && crc32(ps->ps_data, tsize, 0xffffffff))
    return -1;

  cb(ps->ps_data, tsize - (crc ? 4 : 0), opaque);
  ps->ps_offset = 0;
  return len - excess;
}


/**
 *
 */
void
psi_section_reassemble(psi_section_t *ps, const uint8_t *tsb, int crc,
		       section_handler_t *cb, void *opaque)
{
  int off = tsb[3] & 0x20 ? tsb[4] + 5 : 4;
  int pusi = tsb[1] & 0x40;
  int r;

  if(off >= 188) {
    ps->ps_lock = 0;
    return;
  }
  
  if(pusi) {
    int len = tsb[off++];
    if(len > 0) {
      if(len > 188 - off) {
	ps->ps_lock = 0;
	return;
      }
      psi_section_reassemble0(ps, tsb + off, len, 0, crc, cb, opaque);
      off += len;
    }
  }

  while(off < 188 && tsb[off] != 0xff) {
    r = psi_section_reassemble0(ps, tsb + off, 188 - off, pusi, crc,
				cb, opaque);
    if(r < 0) {
      ps->ps_lock = 0;
      break;
    }
    off += r;
    pusi = 0;
  }
}


/** 
 * PAT parser, from ISO 13818-1
 */
int
psi_parse_pat(service_config_t *sc, const uint8_t *ptr, int len,
	      pid_section_callback_t *pmt_callback)
{
  uint16_t prognum;
  uint16_t pid;
  elementary_stream_config_t *esc;

  lock_assert(&global_lock);

  if(len < 5)
    return -1;

  ptr += 5;
  len -= 5;

  while(len >= 4) {
    
    prognum =  ptr[0]         << 8 | ptr[1];
    pid     = (ptr[2] & 0x1f) << 8 | ptr[3];

    if(prognum != 0) {
      if(service_stream_find(sc, pid) == NULL) {
	esc = elementary_stream_config_create(sc, pid, SCT_PMT);
	esc->esc_section_docrc = 1;
	esc->esc_got_section = pmt_callback;
      }
    }
    ptr += 4;
    len -= 4;
  }
  return 0;
}


/**
 * Append CRC
 */

static int
psi_append_crc32(uint8_t *buf, int offset, int maxlen)
{
  uint32_t crc;

  if(offset + 4 > maxlen)
    return -1;

  crc = crc32(buf, offset, 0xffffffff);

  buf[offset + 0] = crc >> 24;
  buf[offset + 1] = crc >> 16;
  buf[offset + 2] = crc >> 8;
  buf[offset + 3] = crc;

  assert(crc32(buf, offset + 4, 0xffffffff) == 0);

  return offset + 4;
}


/** 
 * PAT generator
 */

int
psi_build_pat(service_t *t, uint8_t *buf, int maxlen, int pmtpid)
{
  if(maxlen < 12)
    return -1;

  buf[0] = 0;
  buf[1] = 0xb0;       /* reserved */
  buf[2] = 12 + 4 - 3; /* Length */

  buf[3] = 0x00; /* transport stream id */
  buf[4] = 0x01;

  buf[5] = 0xc1; /* reserved + current_next_indicator + version */
  buf[6] = 0;
  buf[7] = 0;

  buf[8] = 0;    /* Program number, we only have one program */
  buf[9] = 1;

  buf[10] = 0xe0 | (pmtpid >> 8);
  buf[11] =         pmtpid;

  return psi_append_crc32(buf, 12, maxlen);
}


/**
 * PMT update reason flags
 */
#define PMT_UPDATE_PCR                0x1
#define PMT_UPDATE_NEW_STREAM         0x2
#define PMT_UPDATE_LANGUAGE           0x4
#define PMT_UPDATE_FRAME_DURATION     0x8
#define PMT_UPDATE_COMPOSITION_ID     0x10
#define PMT_UPDATE_ANCILLARY_ID       0x20
#define PMT_UPDATE_STREAM_DELETED     0x40
#define PMT_UPDATE_NEW_CA_STREAM      0x80
#define PMT_UPDATE_NEW_CAID           0x100
#define PMT_UPDATE_CA_PROVIDER_CHANGE 0x200
#define PMT_UPDATE_PARENT_PID         0x400
#define PMT_UPDATE_CAID_DELETED       0x800
#define PMT_REORDERED                 0x1000

/**
 * Add a CA descriptor
 */
static void
psi_desc_add_ca(service_config_t *sc, uint16_t caid, uint32_t provid,
		uint16_t pid)
{
  elementary_stream_config_t *esc;
  caid_t *c;
  int i, slot = -1;

  if((esc = service_stream_find(sc, pid)) == NULL)
    esc = elementary_stream_config_create(sc, pid, SCT_CA);

  esc->esc_delete_me = 0;

  for(i = 0; i < SERVICE_MAX_CAIDS; i++) {
    c = &esc->esc_caids[i];
    if(c->caid == caid) {
      c->providerid = provid;
      return;
    }
    if(c->caid == 0 && slot == -1)
      slot = i;
  }

  if(slot == -1)
    return;
  esc->esc_caids[slot].caid = caid;
  esc->esc_caids[slot].providerid = provid;
}

/**
 * Parser for CA descriptors
 */
static int 
psi_desc_ca(service_config_t *sc, const uint8_t *buffer, int size)
{
  int r = 0;
  int i;
  uint32_t provid = 0;
  uint16_t caid = (buffer[0] << 8) | buffer[1];
  uint16_t pid = ((buffer[2]&0x1F) << 8) | buffer[3];

#if 0
  printf("CA_DESC: ");
  for(i = 0; i < size; i++)
    printf("%02x.", buffer[i]);
  printf("\n");
#endif

  switch (caid & 0xFF00) {
  case 0x0100: // SECA/Mediaguard
    provid = (buffer[4] << 8) | buffer[5];

    //Add extra providers, if any
    for (i = 17; i < size; i += 15){
      uint16_t xpid = ((buffer[i]&0x1F) << 8) | buffer[i + 1];
      uint16_t xprovid = (buffer[i + 2] << 8) | buffer[i + 3];

      psi_desc_add_ca(sc, caid, xprovid, xpid);
    }
    break;
  case 0x0500:// Viaccess
    for (i = 4; i < size;) {
      unsigned char nano = buffer[i++];
      unsigned char nanolen = buffer[i++];

      if (nano == 0x14) {
        provid = (buffer[i] << 16) | (buffer[i + 1] << 8) | (buffer[i + 2] & 0xf0);
        break;
      }

      i += nanolen;
    }
    break;
  case 0x4a00://DRECrypt
    provid = size < 4 ? 0 : buffer[4];
    break;
  default:
    provid = 0;
    break;
  }

  psi_desc_add_ca(sc, caid, provid, pid);

  return r;
}

/**
 * Parser for teletext descriptor
 */
static int
psi_desc_teletext(service_config_t *sc, const uint8_t *ptr, int size,
		  int parent_pid)
{
  int r = 0;
  elementary_stream_config_t *esc;

  while(size >= 5) {
    int page = (ptr[3] & 0x7 ?: 8) * 100 + (ptr[4] >> 4) * 10 + (ptr[4] & 0xf);
    int type = ptr[3] >> 3;

    if(type == 2 || type == 5) {
      // 2 = subtitle page, 5 = subtitle page [hearing impaired]

      // We put the teletext subtitle driven streams on a list of pids
      // higher than normal MPEG TS (0x2000 ++)
      int pid = PID_TELETEXT_BASE + page;
    
      if((esc = service_stream_find(sc, pid)) == NULL) {
	r |= PMT_UPDATE_NEW_STREAM;
	esc = elementary_stream_config_create(sc, pid, SCT_TEXTSUB);
      }

      esc->esc_delete_me = 0;

      if(memcmp(esc->esc_lang, ptr, 3)) {
	r |= PMT_UPDATE_LANGUAGE;
	memcpy(esc->esc_lang, ptr, 3);
      }

      if(esc->esc_parent_pid != parent_pid) {
	r |= PMT_UPDATE_PARENT_PID;
	esc->esc_parent_pid = parent_pid;
      }
#if 0
      if(esc->esc_position != *position) {
	esc->esc_position = *position;
	r |= PMT_REORDERED;
      }
      (*position)++;
#endif
    }
    ptr += 5;
    size -= 5;
  }
  return r;
}

#if 0
/**
 *
 */
static int
pidcmp(const void *A, const void *B)
{
  elementary_stream_t *a = *(elementary_stream_t **)A;
  elementary_stream_t *b = *(elementary_stream_t **)B;
  return a->es_position - b->es_position;
}



/**
 *
 */
static void
sort_pids(service_t *t)
{
  elementary_stream_t *st, **v;
  int num = 0, i = 0;

  TAILQ_FOREACH(st, &t->s_components, es_link)
    num++;

  v = alloca(num * sizeof(elementary_stream_t *));
  TAILQ_FOREACH(st, &t->s_components, es_link)
    v[i++] = st;

  qsort(v, num, sizeof(elementary_stream_t *), pidcmp);

  TAILQ_INIT(&t->s_components);
  for(i = 0; i < num; i++)
    TAILQ_INSERT_TAIL(&t->s_components, v[i], es_link);
}
#endif


/** 
 * PMT parser, from ISO 13818-1 and ETSI EN 300 468
 */
int
psi_parse_pmt(struct service_config *sc, const uint8_t *ptr, int len,
	      int chksvcid, int delete)
{
  uint16_t pcr_pid, pid;
  uint8_t estype;
  int dllen;
  uint8_t dtag, dlen;
  uint16_t sid;
  streaming_component_type_t stream_type;
  elementary_stream_config_t *esc, *next;
  char lang[4];
  int update = 0;
  int had_components;
  int composition_id;
  int ancillary_id;
  int version;
  int position = 0;

  if(len < 9)
    return -1;

  lock_assert(&global_lock);

  had_components = !!TAILQ_FIRST(&sc->sc_elementary_stream_configs);

  sid     = ptr[0] << 8 | ptr[1];
  version = ptr[2] >> 1 & 0x1f;
  
  if((ptr[2] & 1) == 0) {
    /* current_next_indicator == next, skip this */
    return -1;
  }

  pcr_pid = (ptr[5] & 0x1f) << 8 | ptr[6];
  dllen   = (ptr[7] & 0xf) << 8 | ptr[8];
  
  if(chksvcid && sid != sc->sc_dvb_service_id)
    return -1;

  if(sc->sc_pcr_pid != pcr_pid) {
    sc->sc_pcr_pid = pcr_pid;
    update |= PMT_UPDATE_PCR;
  }

  ptr += 9;
  len -= 9;

  /* Mark all streams for deletion */
  if(delete) {
    TAILQ_FOREACH(esc, &sc->sc_elementary_stream_configs, esc_link) {
      esc->esc_delete_me = 1;
    }
  }

  // Common descriptors
  while(dllen > 1) {
    dtag = ptr[0];
    dlen = ptr[1];

    len -= 2; ptr += 2; dllen -= 2; 
    if(dlen > len)
      break;

    switch(dtag) {
    case DVB_DESC_CA:
      update |= psi_desc_ca(sc, ptr, dlen);
      break;

    default:
      break;
    }
    len -= dlen; ptr += dlen; dllen -= dlen;
  }



  while(len >= 5) {
    estype  = ptr[0];
    pid     = (ptr[1] & 0x1f) << 8 | ptr[2];
    dllen   = (ptr[3] & 0xf) << 8 | ptr[4];

    ptr += 5;
    len -= 5;

    stream_type = SCT_UNKNOWN;
    memset(lang, 0, 4);
    composition_id = -1;
    ancillary_id = -1;

    switch(estype) {
    case 0x01:
    case 0x02:
      stream_type = SCT_MPEG2VIDEO;
      break;

    case 0x03:
    case 0x04:
      stream_type = SCT_MPEG2AUDIO;
      break;

    case 0x81:
      stream_type = SCT_AC3;
      break;

    case 0x11:
      stream_type = SCT_AAC;
      break;

    case 0x1b:
      stream_type = SCT_H264;
      break;

    default:
      break;
    }

    while(dllen > 1) {
      dtag = ptr[0];
      dlen = ptr[1];

      len -= 2; ptr += 2; dllen -= 2; 
      if(dlen > len)
	break;

      switch(dtag) {
      case DVB_DESC_CA:
	update |= psi_desc_ca(sc, ptr, dlen);
	break;

      case DVB_DESC_REGISTRATION:
	if(dlen == 4 && 
	   ptr[0] == 'A' && ptr[1] == 'C' && ptr[2] == '-' &&  ptr[3] == '3')
	  stream_type = SCT_AC3;
	break;

      case DVB_DESC_LANGUAGE:
	memcpy(lang, ptr, 3);
	break;

      case DVB_DESC_TELETEXT:
	if(estype == 0x06)
	  stream_type = SCT_TELETEXT;
	
	update |= psi_desc_teletext(sc, ptr, dlen, pid);
	break;

      case DVB_DESC_AC3:
	if(estype == 0x06 || estype == 0x81)
	  stream_type = SCT_AC3;
	break;

      case DVB_DESC_AAC:
	if(estype == 0x11)
	  stream_type = SCT_AAC;
	break;

      case DVB_DESC_SUBTITLE:
	if(dlen < 8)
	  break;

	memcpy(lang, ptr, 3);
	composition_id = ptr[4] << 8 | ptr[5];
	ancillary_id   = ptr[6] << 8 | ptr[7];
	stream_type = SCT_DVBSUB;
	break;

      case DVB_DESC_EAC3:
	if(estype == 0x06 || estype == 0x81)
	  stream_type = SCT_EAC3;
	break;

      default:
	break;
      }
      len -= dlen; ptr += dlen; dllen -= dlen;
    }

    
    if(stream_type == SCT_UNKNOWN && estype == 0x06 &&
       pid == 3401 && sc->sc_dvb_service_id == 10510) {
      // Workaround for ITV HD
      stream_type = SCT_H264;
    }

    if(stream_type != SCT_UNKNOWN) {

      if((esc = service_stream_find(sc, pid)) == NULL) {
	update |= PMT_UPDATE_NEW_STREAM;
	esc = elementary_stream_config_create(sc, pid, stream_type);
      }

      esc->esc_delete_me = 0;

      if(memcmp(esc->esc_lang, lang, 4)) {
	update |= PMT_UPDATE_LANGUAGE;
	memcpy(esc->esc_lang, lang, 4);
      }

      if(composition_id != -1 && esc->esc_composition_id != composition_id) {
	esc->esc_composition_id = composition_id;
	update |= PMT_UPDATE_COMPOSITION_ID;
      }

      if(ancillary_id != -1 && esc->esc_ancillary_id != ancillary_id) {
	esc->esc_ancillary_id = ancillary_id;
	update |= PMT_UPDATE_ANCILLARY_ID;
      }
    }
    position++;
  }

  /* Scan again to see if any streams should be deleted */
  for(esc = TAILQ_FIRST(&sc->sc_elementary_stream_configs);
      esc != NULL; esc = next) {
    next = TAILQ_NEXT(esc, esc_link);

    if(esc->esc_delete_me) {
      service_stream_destroy(sc, esc);
      update |= PMT_UPDATE_STREAM_DELETED;
    }
  }

  if(update) {
    tvhlog(LOG_DEBUG, "PSI", "Service \"%s\" PMT (version %d) updated"
	   "%s%s%s%s%s%s%s%s%s%s%s%s%s",
	   "?FIXTHISNAME?", version,
	   update&PMT_UPDATE_PCR               ? ", PCR PID changed":"",
	   update&PMT_UPDATE_NEW_STREAM        ? ", New elementary stream":"",
	   update&PMT_UPDATE_LANGUAGE          ? ", Language changed":"",
	   update&PMT_UPDATE_FRAME_DURATION    ? ", Frame duration changed":"",
	   update&PMT_UPDATE_COMPOSITION_ID    ? ", Composition ID changed":"",
	   update&PMT_UPDATE_ANCILLARY_ID      ? ", Ancillary ID changed":"",
	   update&PMT_UPDATE_STREAM_DELETED    ? ", Stream deleted":"",
	   update&PMT_UPDATE_NEW_CA_STREAM     ? ", New CA stream":"",
	   update&PMT_UPDATE_NEW_CAID          ? ", New CAID":"",
	   update&PMT_UPDATE_CA_PROVIDER_CHANGE? ", CA provider changed":"",
	   update&PMT_UPDATE_PARENT_PID        ? ", Parent PID changed":"",
	   update&PMT_UPDATE_CAID_DELETED      ? ", CAID deleted":"",
	   update&PMT_REORDERED                ? ", PIDs reordered":"");
    
    abort(); // service_request_save(t, 0);

    // Only restart if something that our clients worry about did change
    if(update & !(PMT_UPDATE_NEW_CA_STREAM |
		  PMT_UPDATE_NEW_CAID |
		  PMT_UPDATE_CA_PROVIDER_CHANGE | 
		  PMT_UPDATE_CAID_DELETED)) {
      abort(); 
      /*
      if(sc->sc_status == SERVICE_RUNNING)
	service_restart(t, had_components);
      */
    }
  }
  return 0;
}


/** 
 * PMT generator
 */
int
psi_build_pmt(streaming_start_t *ss, uint8_t *buf0, int maxlen, int pcrpid)
{
  int c, tlen, dlen, l, i;
  uint8_t *buf, *buf1;

  buf = buf0;

  if(maxlen < 12)
    return -1;

  buf[0] = 2; /* table id, always 2 */

  buf[3] = 0x00; /* program id */
  buf[4] = 0x01;

  buf[5] = 0xc1; /* current_next_indicator + version */
  buf[6] = 0;
  buf[7] = 0;

  buf[8] = 0xe0 | (pcrpid >> 8);
  buf[9] =         pcrpid;

  buf[10] = 0xf0; /* Program info length */
  buf[11] = 0x00; /* We dont have any such things atm */

  buf += 12;
  tlen = 12;

  for(i = 0; i < ss->ss_num_components; i++) {
    streaming_start_component_t *ssc = &ss->ss_components[i];

    switch(ssc->ssc_type) {
    case SCT_MPEG2VIDEO:
      c = 0x02;
      break;

    case SCT_MPEG2AUDIO:
      c = 0x04;
      break;

    case SCT_DVBSUB:
      c = 0x06;
      break;

    case SCT_AAC:
      c = 0x11;
      break;

    case SCT_H264:
      c = 0x1b;
      break;

    case SCT_AC3:
      c = 0x81;
      break;

    default:
      continue;
    }


    buf[0] = c;
    buf[1] = 0xe0 | (ssc->ssc_pid >> 8);
    buf[2] =         ssc->ssc_pid;

    buf1 = &buf[3];
    tlen += 5;
    buf  += 5;
    dlen = 0;

    switch(ssc->ssc_type) {
    case SCT_MPEG2AUDIO:
    case SCT_AAC:
      buf[0] = DVB_DESC_LANGUAGE;
      buf[1] = 4;
      memcpy(&buf[2],ssc->ssc_lang,3);
      buf[5] = 0; /* Main audio */
      dlen = 6;
      break;
    case SCT_DVBSUB:
      buf[0] = DVB_DESC_SUBTITLE;
      buf[1] = 8;
      memcpy(&buf[2],ssc->ssc_lang,3);
      buf[5] = 16; /* Subtitling type */
      buf[6] = ssc->ssc_composition_id >> 8; 
      buf[7] = ssc->ssc_composition_id;
      buf[8] = ssc->ssc_ancillary_id >> 8; 
      buf[9] = ssc->ssc_ancillary_id;
      dlen = 10;
      break;
    case SCT_AC3:
      buf[0] = DVB_DESC_LANGUAGE;
      buf[1] = 4;
      memcpy(&buf[2],ssc->ssc_lang,3);
      buf[5] = 0; /* Main audio */
      buf[6] = DVB_DESC_AC3;
      buf[7] = 1;
      buf[8] = 0; /* XXX: generate real AC3 desc */
      dlen = 9;
      break;
    default:
      break;
    }

    tlen += dlen;
    buf  += dlen;

    buf1[0] = 0xf0 | (dlen >> 8);
    buf1[1] =         dlen;
  }

  l = tlen - 3 + 4;

  buf0[1] = 0xb0 | (l >> 8);
  buf0[2] =         l;

  return psi_append_crc32(buf0, tlen, maxlen);
}



static struct strtab caidnametab[] = {
  { "Seca",             0x0100 }, 
  { "CCETT",            0x0200 }, 
  { "Deutsche Telecom", 0x0300 }, 
  { "Eurodec",          0x0400 }, 
  { "Viaccess",         0x0500 }, 
  { "Irdeto",           0x0600 }, 
  { "Irdeto",           0x0602 }, 
  { "Irdeto",           0x0604 }, 
  { "Jerroldgi",        0x0700 }, 
  { "Matra",            0x0800 }, 
  { "NDS",              0x0900 }, 
  { "Nokia",            0x0A00 }, 
  { "Conax",            0x0B00 }, 
  { "NTL",              0x0C00 }, 
  { "CryptoWorks",      0x0D00 }, 
  { "PowerVu",          0x0E00 }, 
  { "Sony",             0x0F00 }, 
  { "Tandberg",         0x1000 }, 
  { "Thompson",         0x1100 }, 
  { "TV-Com",           0x1200 }, 
  { "HPT",              0x1300 }, 
  { "HRT",              0x1400 }, 
  { "IBM",              0x1500 }, 
  { "Nera",             0x1600 }, 
  { "BetaCrypt",        0x1700 }, 
  { "BetaCrypt",        0x1702 }, 
  { "BetaCrypt",        0x1722 }, 
  { "BetaCrypt",        0x1762 }, 
  { "NagraVision",      0x1800 }, 
  { "Titan",            0x1900 }, 
  { "Telefonica",       0x2000 }, 
  { "Stentor",          0x2100 }, 
  { "Tadiran Scopus",   0x2200 }, 
  { "BARCO AS",         0x2300 }, 
  { "StarGuide",        0x2400 }, 
  { "Mentor",           0x2500 }, 
  { "EBU",              0x2600 }, 
  { "GI",               0x4700 }, 
  { "Telemann",         0x4800 },
  { "DRECrypt",         0x4ae0 },
  { "DRECrypt2",        0x4ae1 }
};

const char *
psi_caid2name(uint16_t caid)
{
  const char *s = val2str(caid, caidnametab);
  static char buf[20];

  if(s != NULL)
    return s;
  snprintf(buf, sizeof(buf), "0x%x", caid);
  return buf;
}

/**
 *
 */
static struct strtab streamtypetab[] = {
  { "MPEG2VIDEO", SCT_MPEG2VIDEO },
  { "MPEG2AUDIO", SCT_MPEG2AUDIO },
  { "H264",       SCT_H264 },
  { "AC3",        SCT_AC3 },
  { "TELETEXT",   SCT_TELETEXT },
  { "DVBSUB",     SCT_DVBSUB },
  { "CA",         SCT_CA },
  { "PMT",        SCT_PMT },
  { "PAT",        SCT_PAT },
  { "AAC",        SCT_AAC },
  { "MPEGTS",     SCT_MPEGTS },
  { "TEXTSUB",    SCT_TEXTSUB },
  { "EAC3",       SCT_EAC3 },
};


/**
 *
 */
const char *
streaming_component_type2txt(streaming_component_type_t s)
{
  return val2str(s, streamtypetab) ?: "INVALID";
}

#if 0

/**
 * Store service settings into message
 */
void
psi_save_service_settings(htsmsg_t *m, service_t *t)
{
  elementary_stream_t *st;
  htsmsg_t *sub;

  htsmsg_add_u32(m, "pcr", t->s_pcr_pid);

  htsmsg_add_u32(m, "disabled", !t->s_enabled);

  lock_assert(&t->s_stream_mutex);

  TAILQ_FOREACH(st, &t->s_components, es_link) {
    sub = htsmsg_create_map();

    htsmsg_add_u32(sub, "pid", esc->esc_pid);
    htsmsg_add_str(sub, "type", val2str(esc->esc_type, streamtypetab) ?: "?");
    htsmsg_add_u32(sub, "position", esc->esc_position);

    if(esc->esc_lang[0])
      htsmsg_add_str(sub, "language", esc->esc_lang);

    if(esc->esc_type == SCT_CA) {

      caid_t *c;
      htsmsg_t *v = htsmsg_create_list();

      LIST_FOREACH(c, &esc->esc_caids, link) {
	htsmsg_t *caid = htsmsg_create_map();

	htsmsg_add_u32(caid, "caid", c->caid);
	if(c->providerid)
	  htsmsg_add_u32(caid, "providerid", c->providerid);
	htsmsg_add_msg(v, NULL, caid);
      }

      htsmsg_add_msg(sub, "caidlist", v);
    }

    if(esc->esc_type == SCT_DVBSUB) {
      htsmsg_add_u32(sub, "compositionid", esc->esc_composition_id);
      htsmsg_add_u32(sub, "ancillartyid", esc->esc_ancillary_id);
    }

    if(esc->esc_type == SCT_TEXTSUB)
      htsmsg_add_u32(sub, "parentpid", esc->esc_parent_pid);

    if(esc->esc_type == SCT_MPEG2VIDEO || esc->esc_type == SCT_H264) {
      if(esc->esc_width && esc->esc_height) {
	htsmsg_add_u32(sub, "width", esc->esc_width);
	htsmsg_add_u32(sub, "height", esc->esc_height);
      }
    }
    
    htsmsg_add_msg(m, "stream", sub);
  }
}


/**
 *
 */
static void
add_caid(elementary_stream_t *st, uint16_t caid, uint32_t providerid)
{
  caid_t *c = malloc(sizeof(caid_t));
  c->caid = caid;
  c->providerid = providerid;
  c->delete_me = 0;
  LIST_INSERT_HEAD(&esc->esc_caids, c, link);
}


/**
 *
 */
static void
load_legacy_caid(htsmsg_t *c, elementary_stream_t *st)
{
  uint32_t a, b;
  const char *v;

  if(htsmsg_get_u32(c, "caproviderid", &b))
    b = 0;

  if(htsmsg_get_u32(c, "caidnum", &a)) {
    if((v = htsmsg_get_str(c, "caid")) != NULL) {
      int i = str2val(v, caidnametab);
      a = i < 0 ? strtol(v, NULL, 0) : i;
    } else {
      return;
    }
  }

  add_caid(st, a, b);
}


/**
 *
 */
static void 
load_caid(htsmsg_t *m, elementary_stream_t *st)
{
  htsmsg_field_t *f;
  htsmsg_t *c, *v = htsmsg_get_list(m, "caidlist");
  uint32_t a, b;

  if(v == NULL)
    return;

  HTSMSG_FOREACH(f, v) {
    if((c = htsmsg_get_map_by_field(f)) == NULL)
      continue;
    
    if(htsmsg_get_u32(c, "caid", &a))
      continue;

    if(htsmsg_get_u32(c, "providerid", &b))
      b = 0;

    add_caid(st, a, b);
  }
}



/**
 * Load service info from htsmsg
 */
void
psi_load_service_settings(htsmsg_t *m, service_t *t)
{
  htsmsg_t *c;
  htsmsg_field_t *f;
  uint32_t u32, pid;
  elementary_stream_t *st;
  streaming_component_type_t type;
  const char *v;

  if(!htsmsg_get_u32(m, "pcr", &u32))
    t->s_pcr_pid = u32;

  if(!htsmsg_get_u32(m, "disabled", &u32))
    t->s_enabled = !u32;
  else
    t->s_enabled = 1;

  HTSMSG_FOREACH(f, m) {
    if(strcmp(f->hmf_name, "stream"))
      continue;

    if((c = htsmsg_get_map_by_field(f)) == NULL)
      continue;

    if((v = htsmsg_get_str(c, "type")) == NULL)
      continue;

    type = str2val(v, streamtypetab);
    if(type == -1)
      continue;

    if(htsmsg_get_u32(c, "pid", &pid))
      continue;

    st = service_stream_create(t, pid, type);
    
    if((v = htsmsg_get_str(c, "language")) != NULL)
      snprintf(esc->esc_lang, 4, "%s", v);

    if(!htsmsg_get_u32(c, "position", &u32))
      esc->esc_position = u32;
   
    load_legacy_caid(c, st);
    load_caid(c, st);

    if(type == SCT_DVBSUB) {
      if(!htsmsg_get_u32(c, "compositionid", &u32))
	esc->esc_composition_id = u32;

      if(!htsmsg_get_u32(c, "ancillartyid", &u32))
	esc->esc_ancillary_id = u32;
    }

    if(type == SCT_TEXTSUB) {
      if(!htsmsg_get_u32(c, "parentpid", &u32))
	esc->esc_parent_pid = u32;
    }

    if(type == SCT_MPEG2VIDEO || type == SCT_H264) {
      if(!htsmsg_get_u32(c, "width", &u32))
	esc->esc_width = u32;

      if(!htsmsg_get_u32(c, "height", &u32))
	esc->esc_height = u32;
    }

  }
  sort_pids(t);
}
#endif
