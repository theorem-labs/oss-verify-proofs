// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>

/* THE PROPS OBJECT A CONTROLLER WRITES, AS THE INPUT SPELLS IT (fuzz_headamp, fuzz_rate,
 * fuzz_role). Each of the three readers takes the SPA_PARAM_Props object pod a client
 * sets on a node, finds its SPA_PROP_params property, and walks the Struct it carries as
 * (String key, Pod value) pairs. This header writes that object from the input, byte for
 * byte in the SPA POD encoding, and keeps, beside the bytes, what it wrote: the kind of
 * the object, which property is the first SPA_PROP_params and what its value is, and each
 * pod of its Struct. The expectations of the harnesses are worked out from that record,
 * by the POD rules below, never from a reader's answer.
 *
 * The SPA POD encoding (spa/pod/pod.h, spa/utils/type.h, spa/param/props.h of SPA 1.6):
 * a pod is a u32 body size and a u32 type in host order, then the body, padded to 8 bytes.
 * An Object body is a u32 object type and a u32 object id, then its properties, each a
 * u32 key, a u32 flags word and a pod. A Struct body is its pods, one after the other.
 * The accessors the readers use accept a pod as:
 *   Bool    type 2, a body of 4 bytes or more, true when that int32 is not 0;
 *   Int     type 4, a body of 4 bytes or more, its first int32;
 *   Float   type 6, a body of 4 bytes or more, its first float;
 *   String  type 8, a body of 1 byte or more whose LAST byte is NUL; the text is the
 *           body up to its first NUL.
 * contract: SPA 1.6 spa/pod/body.h:134-238 (spa_pod_is_bool .. spa_pod_body_get_string)
 *
 * Input, read by pod_build:
 *   [0]   the object: 6 an Object of type PropInfo, 7 a Struct instead of an Object, any
 *         other value (mod 8) an Object of type Props;
 *   [1]   the number of its properties, mod 4;
 *   then each property: [sel] sel % 4 == 0 is SPA_PROP_volume with an Int value; any
 *         other is SPA_PROP_params, whose value is an Int when sel & 0x10, else a Struct
 *         of [count % 33] pods, each read by ent_build (below);
 *   then [c]: when c % 16 == 15, [u16 offset][u8 len % 8] and that many bytes overwrite
 *         the object past its own header. The record then no longer says what the bytes
 *         spell, and only the properties that hold for every pod are checked
 *         (`corrupt`). */
#ifndef REACPW_FUZZ_POD_H
#define REACPW_FUZZ_POD_H

#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include "fuzz.h"

/* contract: SPA 1.6 spa/utils/type.h:30-50 (the basic types, from None = 1) */
#define POD_NONE   1
#define POD_BOOL   2
#define POD_ID     3
#define POD_INT    4
#define POD_LONG   5
#define POD_FLOAT  6
#define POD_DOUBLE 7
#define POD_STRING 8
#define POD_STRUCT 14
#define POD_OBJECT 15
/* contract: SPA 1.6 spa/utils/type.h:77-79 (SPA_TYPE_OBJECT_START, PropInfo, Props) */
#define POD_OBJECT_PROPINFO 0x40001u
#define POD_OBJECT_PROPS    0x40002u
/* contract: SPA 1.6 spa/param/param.h (SPA_PARAM_Props = 2) */
#define POD_PARAM_PROPS 2u
/* contract: SPA 1.6 spa/param/props.h:112-113 (SPA_PROP_START_Other = 0x80000, then
 * SPA_PROP_params) and the volume key of the Audio block (0x10003) */
#define POD_PROP_PARAMS 0x80001u
#define POD_PROP_VOLUME 0x10003u

#define POD_BUF_MAX   16384
#define POD_ENT_MAX   32
#define POD_BODY_MAX  96

/* One pod of the params Struct, as written. */
struct pod_ent {
	uint32_t type;
	uint32_t size;
	uint8_t body[POD_BODY_MAX];
};

struct pod_props {
	uint8_t buf[POD_BUF_MAX];
	size_t len;
	int is_props;        /* an Object of type Props */
	int has_params;      /* its first SPA_PROP_params property exists */
	int params_struct;   /* ... and its value is a Struct */
	struct pod_ent ent[POD_ENT_MAX];
	int n_ent;           /* the pods of that Struct, in order */
	int corrupt;         /* bytes were overwritten after the record was made */
};

/* ---- the accessors' rules, over the record ------------------------------------------ */

static inline int pod_string(const struct pod_ent *e, const char **s)
{
	if (e->type != POD_STRING || e->size < 1 || e->body[e->size - 1] != 0)
		return 0;
	*s = (const char *)e->body;
	return 1;
}

static inline int pod_bool(const struct pod_ent *e, int *v)
{
	if (e->type != POD_BOOL || e->size < 4)
		return 0;
	int32_t i;
	memcpy(&i, e->body, 4);
	*v = i != 0;
	return 1;
}

static inline int pod_int(const struct pod_ent *e, int32_t *v)
{
	if (e->type != POD_INT || e->size < 4)
		return 0;
	memcpy(v, e->body, 4);
	return 1;
}

static inline int pod_float(const struct pod_ent *e, float *v)
{
	if (e->type != POD_FLOAT || e->size < 4)
		return 0;
	memcpy(v, e->body, 4);
	return 1;
}

/* THE PAIRS OF SPA_PROP_params: the walk all three readers document. A pod in a key slot
 * that is not a String is skipped and the key slot stays open; a String takes the key
 * slot; the pod after it is its value, whatever it is, and the pair is consumed.
 * contract: src/reac_headamp_prop.h:9-14 (a Struct of alternating String key, Pod value)
 * and src/reac_headamp_prop.c:135-137 (a non-string in a key slot is skipped, the next
 * String re-syncs). Returns the index of the value of the next pair at or after *at, its
 * key in *key, or -1 when no pair is left. */
static inline int pod_next_pair(const struct pod_props *pp, int *at, const char **key)
{
	const char *k = NULL;
	for (; *at < pp->n_ent; (*at)++) {
		if (!k) {
			const char *s;
			if (pod_string(&pp->ent[*at], &s))
				k = s;
			continue;
		}
		*key = k;
		return (*at)++;
	}
	return -1;
}

/* The nearest integer to a float, a half read upward, when it lies in [lo, hi]: the
 * reading the three readers document for a Float value. Worked out here from the float's
 * integer part and its fraction, not by the readers' own sum.
 * contract: src/reac_float_near.h:8-10 (the nearest integer, a half read upward; none
 * for NaN, an infinity or a value past the range) */
static inline int pod_nearest(float f, long long lo, long long hi, long long *out)
{
	if (f != f)
		return 0;   /* NaN has no nearest integer */
	/* the integer part and the fraction, exactly, in long double */
	long double d = (long double)f;
	if (d < (long double)lo - 1 || d > (long double)hi + 1)
		return 0;
	long long t = (long long)d;   /* toward zero */
	long double frac = d - (long double)t;
	long long r = t;
	if (frac >= 0.5L)
		r = t + 1;
	else if (frac < -0.5L)
		r = t - 1;
	if (r < lo || r > hi)
		return 0;
	*out = r;
	return 1;
}

/* ---- the writer --------------------------------------------------------------------- */

static inline size_t pod_put(struct pod_props *pp, const void *p, size_t n)
{
	if (pp->len + n > sizeof pp->buf)
		return 0;
	memcpy(pp->buf + pp->len, p, n);
	pp->len += n;
	return n;
}

static inline void pod_pad(struct pod_props *pp)
{
	static const uint8_t z[8];
	pod_put(pp, z, (8 - pp->len % 8) % 8);
}

static inline void pod_put32(struct pod_props *pp, uint32_t v)
{
	pod_put(pp, &v, 4);
}

static inline void pod_patch32(struct pod_props *pp, size_t at, uint32_t v)
{
	memcpy(pp->buf + at, &v, 4);
}

static inline void pod_write_ent(struct pod_props *pp, const struct pod_ent *e)
{
	pod_put32(pp, e->size);
	pod_put32(pp, e->type);
	pod_put(pp, e->body, e->size);
	pod_pad(pp);
}

/* The text of a key the input spells. */
static inline size_t ent_text(struct pod_ent *e, const char *s, size_t n, int nul)
{
	if (n > POD_BODY_MAX - 1)
		n = POD_BODY_MAX - 1;
	memcpy(e->body, s, n);
	if (nul)
		e->body[n++] = 0;
	e->type = POD_STRING;
	e->size = (uint32_t)n;
	return n;
}

/* A head-amp key: "reac.headamp." <channel> "." <param>, each part from a table or the
 * input, so that well-formed cells, cells past the channel space and keys that address
 * nothing are all common. */
static inline void ent_headamp_key(struct fuzz_in *in, struct pod_ent *e)
{
	static const char *const odd_ch[] = {
		"-1", "+3", " 7", "07", "99999999999999999999", "", "x", "3a", "-0", "\t5",
		"48", "47", "0x1", "-99999999999999999999",
	};
	static const char *const param[] = {
		"phantom", "pad", "sens", "PAD", "sensx", "", "phantom.x", "sens ",
	};
	char t[POD_BODY_MAX];
	uint8_t c = fuzz_u8(in), p = fuzz_u8(in);
	char ch[24];
	if (c < 200) {
		unsigned v = c % 64u, k = 0;
		char r[4];
		do {
			r[k++] = (char)('0' + v % 10);
			v /= 10;
		} while (v);
		for (unsigned i = 0; i < k; i++)
			ch[i] = r[k - 1 - i];
		ch[k] = 0;
	} else {
		const char *o = odd_ch[c % (sizeof odd_ch / sizeof odd_ch[0])];
		memcpy(ch, o, strlen(o) + 1);
	}
	const char *pa = param[p % 8];
	const char *sep = (p & 0x80) ? "" : ".";
	size_t n = 0;
	const char *parts[4] = { "reac.headamp.", ch, sep, pa };
	for (int i = 0; i < 4; i++) {
		size_t l = strlen(parts[i]);
		if (n + l >= sizeof t)
			l = sizeof t - 1 - n;
		memcpy(t + n, parts[i], l);
		n += l;
	}
	ent_text(e, t, n, 1);
}

/* One pod of the params Struct. [kind] picks its shape, mod 10. */
static inline void ent_build(struct fuzz_in *in, struct pod_ent *e)
{
	static const char *const vocab[] = {
		"reac.cfg.rate", "reac.cfg.role", "reac.headamp.", "reac.cfg.rate ", "REAC.cfg.rate",
		"some.other.control", "reac.headamp", "reac.cfg.role.x", "reac.cfg.rat",
	};
	static const int32_t ints[] = {
		0, 1, 2, -1, 44100, 48000, 96000, 0x37, 0x38, 255, 256, 47999, INT32_MIN, INT32_MAX,
	};
	static const float floats[] = {
		0.0f, 0.49999997f, 0.5f, 1.0f, -0.7f, -0.5f, -0.49999997f, 44100.4f, 47999.5f,
		96000.0f, 1e10f, -1e10f, 255.4f, 255.5f, 54.6f, 2147483520.0f, 2147483648.0f,
		-2147483648.0f, -2147483904.0f, 0.5000001f, 1.4999999f,
	};
	memset(e, 0, sizeof *e);
	uint8_t kind = fuzz_u8(in);
	switch (kind % 10) {
	case 0:
		ent_headamp_key(in, e);
		break;
	case 1: {
		const char *v = vocab[fuzz_u8(in) % (sizeof vocab / sizeof vocab[0])];
		size_t n = ent_text(e, v, strlen(v), 1);
		/* kind & 0x80: a NUL and more text inside the body; the text is still the
		 * body up to its first NUL */
		if ((kind & 0x80) && n + 2 <= POD_BODY_MAX) {
			e->body[n] = 'x';
			e->body[n + 1] = 0;
			e->size = (uint32_t)(n + 2);
		}
		break;
	}
	case 2: {
		uint8_t m = fuzz_u8(in);
		int32_t v = (m & 1) ? (int32_t)fuzz_u32(in)
		                    : ints[(m >> 1) % (sizeof ints / sizeof ints[0])];
		e->type = POD_INT;
		e->size = 4;
		memcpy(e->body, &v, 4);
		break;
	}
	case 3: {
		uint8_t m = fuzz_u8(in);
		float v;
		if (m & 1) {
			uint32_t bits = fuzz_u32(in);
			memcpy(&v, &bits, 4);
		} else if ((m >> 1) == 127) {
			uint32_t bits = 0x7fc00000u;   /* NaN */
			memcpy(&v, &bits, 4);
		} else if ((m >> 1) == 126) {
			uint32_t bits = (m & 2) ? 0xff800000u : 0x7f800000u;   /* -inf, inf */
			memcpy(&v, &bits, 4);
		} else {
			v = floats[(m >> 1) % (sizeof floats / sizeof floats[0])];
		}
		e->type = POD_FLOAT;
		e->size = 4;
		memcpy(e->body, &v, 4);
		break;
	}
	case 4: {
		int32_t v = (int32_t)(fuzz_u8(in) % 3);
		e->type = POD_BOOL;
		e->size = 4;
		memcpy(e->body, &v, 4);
		break;
	}
	case 5: {
		/* a String of the input's own bytes; kind & 0x80 leaves its NUL off */
		const uint8_t *p;
		size_t n = fuzz_take(in, fuzz_u8(in) % 32u, &p);
		ent_text(e, (const char *)p, n, !(kind & 0x80));
		break;
	}
	case 6: {
		/* another scalar: Long, Double, Id or None */
		static const uint32_t t[] = { POD_LONG, POD_DOUBLE, POD_ID, POD_NONE };
		const uint8_t *p;
		e->type = t[fuzz_u8(in) % 4];
		e->size = e->type == POD_NONE ? 0 : e->type == POD_ID ? 4 : 8;
		size_t n = fuzz_take(in, e->size, &p);
		memcpy(e->body, p, n);
		break;
	}
	case 7: {
		/* any type, any short body */
		const uint8_t *p;
		e->type = fuzz_u8(in) % 21u;
		e->size = fuzz_u8(in) % 12u;
		size_t n = fuzz_take(in, e->size, &p);
		memcpy(e->body, p, n);
		break;
	}
	case 8: {
		/* a scalar or a String with a body too short for its type */
		static const uint32_t t[] = { POD_INT, POD_FLOAT, POD_BOOL, POD_STRING };
		e->type = t[fuzz_u8(in) % 4];
		e->size = e->type == POD_STRING ? 0 : fuzz_u8(in) % 4u;
		memset(e->body, 0, e->size);
		break;
	}
	default: {
		/* a Struct holding one String: a pod that is neither a key nor a number */
		static const char s[] = "reac.cfg.rate";
		uint32_t sz = (uint32_t)sizeof s, ty = POD_STRING;
		e->type = POD_STRUCT;
		memcpy(e->body, &sz, 4);
		memcpy(e->body + 4, &ty, 4);
		memcpy(e->body + 8, s, sizeof s);
		e->size = 8 + 16;   /* the String's 14 bytes padded to 16 */
		break;
	}
	}
}

/* Write the object the input spells into pp, and record it. */
static inline void pod_build(struct fuzz_in *in, struct pod_props *pp)
{
	memset(pp, 0, sizeof *pp);
	uint8_t shape = fuzz_u8(in) % 8u;
	int nprops = fuzz_u8(in) % 4;
	size_t top = pp->len;
	pod_put32(pp, 0);
	if (shape == 7) {
		pod_put32(pp, POD_STRUCT);
	} else {
		pod_put32(pp, POD_OBJECT);
		pod_put32(pp, shape == 6 ? POD_OBJECT_PROPINFO : POD_OBJECT_PROPS);
		pod_put32(pp, POD_PARAM_PROPS);
		pp->is_props = shape != 6;
	}
	int seen_params = 0;
	for (int i = 0; i < nprops; i++) {
		uint8_t sel = fuzz_u8(in);
		int params = sel % 4 != 0;
		if (shape == 7) {
			/* a Struct has no properties: its pods are an Int each */
			struct pod_ent e = { .type = POD_INT, .size = 4 };
			pod_write_ent(pp, &e);
			continue;
		}
		pod_put32(pp, params ? POD_PROP_PARAMS : POD_PROP_VOLUME);
		pod_put32(pp, 0);
		int first = params && !seen_params;
		if (params)
			seen_params = 1;
		if (!params || (sel & 0x10)) {
			struct pod_ent e = { .type = POD_INT, .size = 4 };
			int32_t v = 7;
			memcpy(e.body, &v, 4);
			pod_write_ent(pp, &e);
			if (first)
				pp->has_params = 1;
			continue;
		}
		size_t at = pp->len;
		pod_put32(pp, 0);
		pod_put32(pp, POD_STRUCT);
		int count = fuzz_u8(in) % (POD_ENT_MAX + 1);
		for (int k = 0; k < count; k++) {
			struct pod_ent e;
			ent_build(in, &e);
			if (pp->len + 8 + POD_BODY_MAX + 8 > sizeof pp->buf)
				break;
			pod_write_ent(pp, &e);
			if (first)
				pp->ent[pp->n_ent++] = e;
		}
		pod_patch32(pp, at, (uint32_t)(pp->len - at - 8));
		if (first) {
			pp->has_params = 1;
			pp->params_struct = 1;
		}
	}
	pod_patch32(pp, top, (uint32_t)(pp->len - top - 8));
	uint8_t c = fuzz_u8(in);
	if (c % 16 == 15 && pp->len > 8) {
		size_t off = 8 + fuzz_u16(in) % (pp->len - 8);
		int n = fuzz_u8(in) % 8;
		for (int k = 0; k < n && off + (size_t)k < pp->len; k++)
			pp->buf[off + (size_t)k] = fuzz_u8(in);
		pp->corrupt = 1;
	}
}

#endif /* REACPW_FUZZ_POD_H */
