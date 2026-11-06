// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>

/* libFuzzer harness: the MIDI note map (omx_note_map.h), the one place omx-dsp reads bytes that
 * arrive from outside as they are: a stream of MIDI 1.0 channel messages through a leg's policy
 * (channel, key range, transpose, velocity curve), with the policy changed in the middle of it.
 *
 * Input:  [0..5]  the leg to start from: channel (0..16), key low, key high, transpose
 *                 (-48..48), curve, fixed velocity, each one byte read modulo its travel
 *         [6..]   records until the input ends: a u8 selector, then
 *                 0..199: a message, three raw bytes (status, data1, data2), ANY byte, a system
 *                         message or a data byte above 127 included;
 *                 200..229: omx_note_map_set_leg() with six words, each a raw int (an invalid leg
 *                         is refused and the old one stays);
 *                 230..255: omx_note_map_release_all() with a cap of 1..4 messages, until it
 *                         returns fewer than the cap.
 *
 * The harness keeps a model of what a downstream synth would be sounding: a count of note ons
 * delivered per (channel, output key), less the note offs delivered, cleared by the channel's all
 * notes off (controller 120 or 123, which the map passes through). It keeps its own copy of the
 * leg in force, the one from the first bytes or the last valid one set_leg was given, and each
 * check of the policy reads that copy, never the map's; and its own table of the keys held.
 *
 * Properties, each an abort():
 *   - a message is dropped, passed or rewritten: 0, 1 or 2 are written, each with a status in
 *     0x80..0xEF and data bytes in 0..127, a note on's velocity in 1..127;
 *   - NO NOTE STICKS AND NONE IS RELEASED THAT NEVER SOUNDED: every note off delivered is for a key
 *     the model has sounding, on the channel it was played on, and after releasing everything the
 *     model has nothing sounding and held_count is 0;
 *   - held_count is the population of the held table, always; an invalid leg is refused and leaves
 *     the policy as it was; a valid one is taken;
 *   - a note on outside the leg's channel, key range or transposed key range is never delivered,
 *     one inside them always is, and it sounds the transposed key;
 *   - the out_of_range counter is the count of note ons the leg takes whose transposed key is outside 0..127;
 *   - the velocity curves keep 1..127 for every note-on velocity, with linear the identity.
 */
#define OMX_CONTRACT_STORAGE 1
#include <omxdsp/omx_note_map.h>

#include "fuzz.h"

static int popcount_held(const struct omx_note_map *m) {
  int n = 0;
  for (int c = 0; c < OMX_NOTE_CHANNELS; c++)
    for (int w = 0; w < OMX_NOTE_KEYS / 32; w++) n += __builtin_popcount(m->held[c][w]);
  return n;
}

/* A leg as the header documents it, the harness's own reading. */
static int leg_valid(const struct omx_note_leg *l) {
  return l->channel >= 0 && l->channel <= 16 && l->key_low >= 0 && l->key_low <= l->key_high && l->key_high <= 127 &&
         l->transpose >= -48 && l->transpose <= 48 && l->velocity_curve >= 0 && l->velocity_curve < 4 &&
         l->velocity_fixed >= 1 && l->velocity_fixed <= 127;
}

struct model {
  int sounding[OMX_NOTE_CHANNELS][OMX_NOTE_KEYS];
  int held[OMX_NOTE_CHANNELS][OMX_NOTE_KEYS]; /* the input keys held, by the harness's own account */
  int held_count;
};

/* A message as the map's header reads it: what it does to the keys held under the leg in force. */
static void hold_model(struct model *md, const struct omx_note_leg *own, struct omx_note_msg msg) {
  if (msg.status < 0x80u || msg.status >= 0xF0u || msg.data1 > 127u || msg.data2 > 127u) return;
  const int kind = msg.status & 0xF0, ch = msg.status & 0x0F, key = msg.data1;
  const int takes = own->channel == 0 || own->channel == ch + 1;
  int *h = &md->held[ch][key];
  if (kind == 0x80 || (kind == 0x90 && msg.data2 == 0u)) {
    md->held_count -= *h;
    *h = 0;
  } else if (kind == 0x90) {
    const int to = key + own->transpose;
    if (takes && key >= own->key_low && key <= own->key_high && to >= 0 && to <= 127) {
      md->held_count += !*h;
      *h = 1;
    }
  } else if (kind == 0xB0 && takes && (msg.data1 == 120u || msg.data1 == 123u)) {
    for (int k = 0; k < OMX_NOTE_KEYS; k++) {
      md->held_count -= md->held[ch][k];
      md->held[ch][k] = 0;
    }
  }
}

static void deliver(struct model *md, const struct omx_note_leg *own, const struct omx_note_msg *o, int n, int max,
                    struct omx_note_msg in) {
  /* A call makes no more messages than it has room for.
   * mutant: include/omxdsp/omx_note_map.h:319 `return n;` -> `return n + 9;`
   * input: omni-linear */
  if (!(n >= 0 && n <= max)) {
    FUZZ_SAY("a call made %d outputs, room for %d", n, max);
    abort();
  }
  for (int i = 0; i < n; i++) {
    const int kind = o[i].status & 0xF0, ch = o[i].status & 0x0F;
    /* Each message delivered is a channel message with data bytes of 7 bits.
     * mutant: include/omxdsp/omx_note_map.h:301 `0x90 | ch` -> `0xF0 | ch`
     * input: omni-linear */
    if (!(o[i].status >= 0x80u && o[i].status < 0xF0u && o[i].data1 <= 127u && o[i].data2 <= 127u)) {
      FUZZ_SAY("output %d of %02x %02x %02x is %02x %02x %02x", i, in.status, in.data1, in.data2, o[i].status, o[i].data1, o[i].data2);
      abort();
    }
    if (kind == 0x90) {
      /* A note on delivered has a velocity of 1 or more.
       * mutant: include/omxdsp/omx_note_map.h:303 `omx_velocity_curve_apply(m->leg.velocity_curve, in.data2, m->leg.velocity_fixed)` -> `0`
       * input: omni-linear */
      if (!(o[i].data2 >= 1u)) {
        FUZZ_SAY("a note on with velocity 0 (a note off in disguise) was delivered");
        abort();
      }
      md->sounding[ch][o[i].data1]++;
      /* a note on is only ever delivered inside the leg's own range, on a channel it takes */
      /* A note on is delivered only on a channel the leg takes.
       * mutant: include/omxdsp/omx_note_map.h:289 `!omx_note_map_takes_channel(m, ch) || ` -> ``
       * input: channel-1-up-an-octave */
      if (!(own->channel == 0 || own->channel == ch + 1)) {
        FUZZ_SAY("a note on on channel %d, which the leg does not take", ch + 1);
        abort();
      }
    } else if (kind == 0x80) {
      /* A note off delivered is for a key the model has sounding on that channel.
       * mutant: include/omxdsp/omx_note_map.h:284 `m->out_key[ch][key]` -> `m->out_key[ch][key] + 1`
       * input: omni-linear */
      if (!(md->sounding[ch][o[i].data1] > 0)) {
        FUZZ_SAY("a note off for key %d on channel %d, which was not sounding", o[i].data1, ch + 1);
        abort();
      }
      md->sounding[ch][o[i].data1]--;
    } else if (kind == 0xB0 && (o[i].data1 == 120u || o[i].data1 == 123u)) {
      memset(md->sounding[ch], 0, sizeof md->sounding[ch]);
    }
  }
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  struct fuzz_in in = fuzz_in(data, size);
  fuzz_ledger_reset();

  struct omx_note_leg leg;
  leg.channel = fuzz_u8(&in) % (OMX_NOTE_CHANNELS + 1);
  leg.key_low = fuzz_u8(&in) % OMX_NOTE_KEYS;
  leg.key_high = leg.key_low + fuzz_u8(&in) % (OMX_NOTE_KEYS - leg.key_low);
  leg.transpose = (int)(fuzz_u8(&in) % (2 * OMX_NOTE_TRANSPOSE_MAX + 1)) - OMX_NOTE_TRANSPOSE_MAX;
  leg.velocity_curve = fuzz_u8(&in) % OMX_VELOCITY_CURVE_COUNT;
  leg.velocity_fixed = 1 + fuzz_u8(&in) % 127;
  /* The leg the harness builds is one the library takes.
   * mutant: include/omxdsp/omx_note_map.h:165 `l->velocity_fixed <= 127` -> `l->velocity_fixed <= 0`
   * input: omni-linear */
  if (!(omx_note_leg_valid(&leg))) {
    FUZZ_SAY("the harness built an invalid leg");
    abort();
  }

  static struct omx_note_map m;
  static struct model md;
  memset(&md, 0, sizeof md);
  omx_note_map_init(&m, &leg);
  struct omx_note_leg own = leg; /* the leg in force, by the harness's own account */
  uint32_t out_of_range = 0;

  while (in.n > 0) {
    const uint8_t sel = fuzz_u8(&in);
    if (sel < 200) {
      struct omx_note_msg msg, out[OMX_NOTE_MAP_OUT_MAX];
      msg.status = fuzz_u8(&in);
      msg.data1 = fuzz_u8(&in);
      msg.data2 = fuzz_u8(&in);
      const int was_held = msg.data1 < 128u ? md.held[msg.status & 0x0F][msg.data1] : 0;
      hold_model(&md, &own, msg);
      const int n = omx_note_map_event(&m, msg, out);
      deliver(&md, &own, out, n, OMX_NOTE_MAP_OUT_MAX, msg);
      const int note_on = (msg.status & 0xF0) == 0x90 && msg.data2 > 0u && msg.data2 < 128u && msg.data1 < 128u;
      const int taken_here = note_on && (own.channel == 0 || own.channel == (msg.status & 0x0F) + 1) &&
                             msg.data1 >= own.key_low && msg.data1 <= own.key_high;
      const int to_here = msg.data1 + own.transpose;
      if (taken_here && (to_here < 0 || to_here > 127)) out_of_range++;
      /* A note on that the leg takes and whose transposed key is a key is delivered.
       * mutant: include/omxdsp/omx_note_map.h:289 `if (!omx_note_map_takes_channel` -> `if (1 || !omx_note_map_takes_channel`
       * input: omni-linear */
      if (!(!taken_here || to_here < 0 || to_here > 127 || n > 0)) {
        FUZZ_SAY("note on %d on channel %d was dropped, inside the leg", msg.data1, (msg.status & 0x0F) + 1);
        abort();
      }
      if (n > 0 && (msg.status & 0xF0) == 0x90 && msg.data2 > 0u && msg.data1 < 128u) {
        const int to = msg.data1 + own.transpose;
        /* A note on is delivered only inside the leg's key range, and its output key is a key.
         * mutant: include/omxdsp/omx_note_map.h:289 ` || key > m->leg.key_high` -> ``
         * input: channel-1-up-an-octave */
        if (!(msg.data1 >= own.key_low && msg.data1 <= own.key_high && to >= 0 && to <= 127)) {
          FUZZ_SAY("note on %d was delivered outside the leg's key range %d..%d, transpose %d", msg.data1, own.key_low, own.key_high, own.transpose);
          abort();
        }
        /* A note on makes one message, or two when its key was held, and the last sounds the transposed key.
         * mutant: include/omxdsp/omx_note_map.h:302 `(uint8_t)to` -> `(uint8_t)key`
         * input: channel-1-up-an-octave
         * mutant: include/omxdsp/omx_note_map.h:199 `omx_note_leg_valid(leg) ? *leg : omx_note_leg_default()` -> `omx_note_leg_default()`
         * input: channel-1-up-an-octave */
        if (!(n == (was_held ? 2 : 1) && out[n - 1].data1 == (uint8_t)to)) {
          FUZZ_SAY("a note on of %d made %d messages", msg.data1, n);
          abort();
        }
      }
      /* out_of_range counts the note ons the leg takes whose transposed key is outside 0..127.
       * mutant: include/omxdsp/omx_note_map.h:292 `m->out_of_range++` -> `m->out_of_range--`
       * input: out-of-range-twice
       * mutant: include/omxdsp/omx_note_map.h:292 `m->out_of_range++` -> ``
       * input: out-of-range-twice */
      if (!(m.out_of_range == out_of_range)) {
        FUZZ_SAY("out_of_range is %u, the harness counted %u", (unsigned)m.out_of_range, (unsigned)out_of_range);
        abort();
      }
    } else if (sel < 230) {
      struct omx_note_leg l;
      l.channel = fuzz_int(&in);
      l.key_low = fuzz_int(&in);
      l.key_high = fuzz_int(&in);
      l.transpose = fuzz_int(&in);
      l.velocity_curve = fuzz_int(&in);
      l.velocity_fixed = fuzz_int(&in);
      if (fuzz_u8(&in) & 1) { /* a valid one, from bytes, so that most of these are taken */
        l.channel = fuzz_u8(&in) % (OMX_NOTE_CHANNELS + 1);
        l.key_low = fuzz_u8(&in) % OMX_NOTE_KEYS;
        l.key_high = l.key_low + fuzz_u8(&in) % (OMX_NOTE_KEYS - l.key_low);
        l.transpose = (int)(fuzz_u8(&in) % (2 * OMX_NOTE_TRANSPOSE_MAX + 1)) - OMX_NOTE_TRANSPOSE_MAX;
        l.velocity_curve = fuzz_u8(&in) % OMX_VELOCITY_CURVE_COUNT;
        l.velocity_fixed = 1 + fuzz_u8(&in) % 127;
      }
      const struct omx_note_leg before = own;
      if (leg_valid(&l)) own = l;
      const int taken = omx_note_map_set_leg(&m, &l);
      /* set_leg takes a leg exactly when it is valid, by the harness's own reading of a leg.
       * mutant: include/omxdsp/omx_note_map.h:216 `if (!omx_note_leg_valid(leg)) return 0;` -> ``
       * input: transposed-below-zero-and-change-leg */
      if (!(taken == leg_valid(&l))) {
        FUZZ_SAY("set_leg answered %d for a leg that is %svalid", taken, leg_valid(&l) ? "" : "in");
        abort();
      }
      /* A leg taken is the policy now, and a leg refused leaves the old one.
       * mutant: include/omxdsp/omx_note_map.h:217 `m->leg = *leg;` -> ``
       * input: transposed-below-zero-and-change-leg */
      if (!(taken ? memcmp(&m.leg, &l, sizeof l) == 0 : memcmp(&m.leg, &before, sizeof before) == 0)) {
        FUZZ_SAY("set_leg left a policy that is not the one it answered for");
        abort();
      }
    } else {
      const int cap = 1 + (int)(sel % 4);
      struct omx_note_msg out[4];
      int n;
      do {
        n = omx_note_map_release_all(&m, out, cap);
        /* release_all writes no more than its cap.
         * mutant: include/omxdsp/omx_note_map.h:342 `return n;` -> `return n + cap + 1;`
         * input: channel-1-up-an-octave */
        if (!(n >= 0 && n <= cap)) {
          FUZZ_SAY("release_all(%d) wrote %d", cap, n);
          abort();
        }
        const struct omx_note_msg none = {0, 0, 0};
        for (int i = 0; i < n; i++) {
          /* release_all writes only note offs.
           * mutant: include/omxdsp/omx_note_map.h:336 `0x80 | c` -> `0x90 | c`
           * input: channel-1-up-an-octave */
          if (!((out[i].status & 0xF0) == 0x80)) {
            FUZZ_SAY("release_all wrote a %02x", out[i].status);
            abort();
          }
        }
        deliver(&md, &own, out, n, cap, none);
      } while (n == cap);
      memset(md.held, 0, sizeof md.held);
      md.held_count = 0;
      /* After release_all, nothing is held.
       * mutant: include/omxdsp/omx_note_map.h:340 `omx_note_map_mark(m, c, k, 0);` -> ``
       * input: channel-1-up-an-octave */
      if (!(m.held_count == 0u)) {
        FUZZ_SAY("release_all left %u held", (unsigned)m.held_count);
        abort();
      }
      for (int c = 0; c < OMX_NOTE_CHANNELS; c++)
        for (int k = 0; k < OMX_NOTE_KEYS; k++)
          /* After release_all, the model has nothing sounding.
           * mutant: include/omxdsp/omx_note_map.h:339 `n++;` -> ``
           * input: channel-1-up-an-octave */
          if (!(md.sounding[c][k] == 0)) {
            FUZZ_SAY("after release_all, key %d on channel %d still sounds (%d)", k, c + 1, md.sounding[c][k]);
            abort();
          }
    }
    /* held_count is the population of the held table.
     * mutant: include/omxdsp/omx_note_map.h:246 `m->held_count++;` -> `m->held_count += 2;`
     * input: omni-linear */
    if (!((int)m.held_count == popcount_held(&m))) {
      FUZZ_SAY("held_count %u is not the table's population %d", (unsigned)m.held_count, popcount_held(&m));
      abort();
    }
    /* The table holds as many keys as the harness's own account of what was played.
     * mutant: include/omxdsp/omx_note_map.h:306 `omx_note_map_mark(m, ch, key, 1);` -> ``
     * input: omni-linear */
    if (!(popcount_held(&m) == md.held_count)) {
      FUZZ_SAY("the table holds %d keys, the harness counted %d", popcount_held(&m), md.held_count);
      abort();
    }
  }

  /* what is still held is exactly what still sounds, and releasing it silences the model */
  struct omx_note_msg out[OMX_NOTE_MAP_HELD_MAX];
  const int n = omx_note_map_release_all(&m, out, OMX_NOTE_MAP_HELD_MAX);
  const struct omx_note_msg none = {0, 0, 0};
  deliver(&md, &own, out, n, OMX_NOTE_MAP_HELD_MAX, none);
  /* The release at the end of the input leaves nothing held.
   * mutant: include/omxdsp/omx_note_map.h:340 `omx_note_map_mark(m, c, k, 0);` -> ``
   * input: held-at-the-end */
  if (!(m.held_count == 0u)) {
    FUZZ_SAY("the final release left %u held", (unsigned)m.held_count);
    abort();
  }
  for (int c = 0; c < OMX_NOTE_CHANNELS; c++)
    for (int k = 0; k < OMX_NOTE_KEYS; k++)
      /* No note sticks: after the release at the end, the model has nothing sounding.
       * mutant: include/omxdsp/omx_note_map.h:339 `n++;` -> ``
       * input: held-at-the-end */
      if (!(md.sounding[c][k] == 0)) {
        FUZZ_SAY("a note is stuck: key %d on channel %d sounds (%d)", k, c + 1, md.sounding[c][k]);
        abort();
      }

  for (int v = 1; v <= 127; v++) {
    for (int curve = 0; curve < OMX_VELOCITY_CURVE_COUNT; curve++) {
      const int o = omx_velocity_curve_apply(curve, v, leg.velocity_fixed);
      /* Each curve keeps a velocity in 1..127.
       * mutant: include/omxdsp/omx_note_map.h:130 `if (out > 127) out = 127;` -> `out = 128;`
       * input: leg-only */
      if (!(o >= 1 && o <= 127)) {
        FUZZ_SAY("curve %d at velocity %d gave %d", curve, v, o);
        abort();
      }
    }
    /* The linear curve is the identity.
     * mutant: include/omxdsp/omx_note_map.h:127 `out = v` -> `out = 1`
     * input: leg-only */
    if (!(omx_velocity_curve_apply(OMX_VELOCITY_LINEAR, v, 1) == v)) {
      FUZZ_SAY("the linear curve moved velocity %d", v);
      abort();
    }
  }
  fuzz_ledger_clean("note map");
  return 0;
}
