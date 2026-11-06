// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>

/* libFuzzer harness: THE FRAME (src/diginet_frame.c), the reading of protocol/diginet.ksy's
 * top-level seq, `header` and `announce` that every byte from the desk goes through first.
 *
 * Input: one Ethernet frame, FCS excluded, of any length and content. It is copied into an
 * allocation of exactly its length, so a read past the frame is a sanitizer report.
 *
 * The harness reads the frame itself, from the grammar (fuzz/spec.h, spec_read_frame), and
 * every check holds the library to that reading. No expected value comes from the library.
 *
 * Properties, each an abort() in a check_ function:
 *   - parse: diginet_frame_parse() refuses exactly what diginet.ksy refuses, each with the
 *     code diginet.h gives it (a frame shorter than the two headers, an EtherType that is not
 *     0x885F, a numbytes under 16 or past the buffer), and what it accepts it reads as the
 *     grammar does: every header field at its offset, the two MACs, the body right after the
 *     header with numbytes - 16 bytes, the rest padding, the body's 16-bit sum and whether
 *     the header carries it, and a keepalive exactly a data frame whose body is the one
 *     byte 00.
 *   - round-trip: diginet_frame_build() makes, from the fields the grammar reads, the frame
 *     diginet.h promises, whatever numbytes and sum the header it is given carries: the MACs,
 *     0x885F, numbytes, the body's sum (or zero in the zero-sum mode), the counters, retry, command and count, the body, zeros up to 60 bytes. It
 *     refuses a body past 1484 bytes, one holding F0 13 xx 70, and a buffer one byte short,
 *     and writes nothing into that buffer.
 *   - announce: diginet_announce_parse() reads only an e0 or e1 of at least 33 body bytes;
 *     `unknown` is the first 15 body bytes, the version the bytes at 15 and the name the
 *     bytes at 24, each up to its first NUL and at most 9, always terminated.
 */
#include <diginet/diginet.h>

#include "fuzz.h"

FUZZ_CHECK check_parse_refusal(int r, const struct spec_frame *w)
{
	/* A frame shorter than the Ethernet header and the DigiNet header is refused as short.
	 * contract: protocol/diginet.ksy seq `dst` `src` `ethertype` `header` (30 bytes); diginet.h:61
	 * mutant: src/diginet_frame.c:64 `len < DIGINET_BODY_OFFSET` -> `len < DIGINET_ETH_HDR_LEN`
	 * input: short */
	if (w->code == SPEC_E_SHORT && r != SPEC_E_SHORT)
		abort();
	/* An EtherType other than 0x885F is refused as such.
	 * contract: protocol/diginet.ksy seq `ethertype` (valid: 0x885f); diginet.h:62
	 * mutant: src/diginet_frame.c:67 `et != DIGINET_ETHERTYPE` -> `et == 0`
	 * input: wrong-ethertype */
	if (w->code == SPEC_E_ETHERTYPE && r != SPEC_E_ETHERTYPE)
		abort();
	/* A numbytes under 16, or one that runs past the buffer, is refused as a length.
	 * contract: protocol/diginet.ksy header `numbytes` (valid: min 16) and seq `body` (size:
	 * numbytes - 16); diginet.h:63
	 * mutant: src/diginet_frame.c:72 `(size_t)numbytes > len - DIGINET_ETH_HDR_LEN` -> `(size_t)numbytes > len`
	 * input: numbytes-past-buffer
	 * mutant: src/diginet_frame.c:73 `DIGINET_E_LENGTH` -> `DIGINET_E_SHORT`
	 * input: numbytes-under-16 */
	if (w->code == SPEC_E_LENGTH && r != SPEC_E_LENGTH)
		abort();
	/* Every frame the grammar reads is accepted.
	 * contract: protocol/diginet.ksy seq; diginet.h:107-109
	 * mutant: src/diginet_frame.c:72 `numbytes < DIGINET_HDR_LEN` -> `numbytes <= DIGINET_HDR_LEN`
	 * input: ack */
	if (w->code == SPEC_OK && r != SPEC_OK)
		abort();
}

FUZZ_CHECK check_parse_fields(const uint8_t *buf, const struct diginet_frame *f,
			      const struct spec_frame *w)
{
	/* Each header field is the big-endian value at its offset.
	 * contract: docs/protocol.md:37-43; protocol/diginet.ksy `header`
	 * mutant: src/diginet_frame.c:81 `rd32(h + 8)` -> `rd32(h + 4)`
	 * input: ack */
	if (f->h.numbytes != w->numbytes || f->h.sum != w->sum || f->h.send_counter != w->send ||
	    f->h.ack_counter != w->ack || f->h.retry != w->retry || f->h.cmd != w->cmd ||
	    f->h.num_commands != w->ncmds)
		abort();
	/* The destination is bytes 0..5, the source 6..11, then the EtherType.
	 * contract: protocol/diginet.ksy seq `dst` `src` `ethertype`
	 * mutant: src/diginet_frame.c:76 `buf + 6` -> `buf + 5`
	 * input: fader_move */
	if (memcmp(f->dst, w->dst, SPEC_MAC) || memcmp(f->src, w->src, SPEC_MAC) ||
	    f->ethertype != w->ethertype)
		abort();
	/* A source is a Digidesign desk's exactly when it carries the OUI 00:a0:7e.
	 * contract: docs/protocol.md:27; diginet.h:123
	 * mutant: src/diginet_frame.c:52 `mac[1] == DIGINET_OUI_1` -> `mac[1] == 0xa1`
	 * input: fader_move */
	if (diginet_mac_is_digidesign(f->src) != !memcmp(w->src, SPEC_OUI, sizeof SPEC_OUI))
		abort();
	/* The body follows the header inside the buffer, numbytes - 16 bytes, and every byte after
	 * it is padding.
	 * contract: protocol/diginet.ksy seq `body` (size: header.numbytes - 16) and `padding`
	 * mutant: src/diginet_frame.c:87 `len - DIGINET_BODY_OFFSET - f->body_len` -> `len - DIGINET_BODY_OFFSET`
	 * input: keepalive */
	if (f->body != buf + SPEC_BODY_AT || f->body_len != w->body_len || f->pad_len != w->pad_len)
		abort();
	/* The body's sum is the 16-bit additive sum of its bytes, padding excluded, and the frame
	 * says it matches exactly when the header carries that sum.
	 * contract: docs/protocol.md:38; diginet.h:100-101
	 * mutant: src/diginet_frame.c:46 `s += p[i];` -> `s |= p[i];`
	 * input: fader_move
	 * mutant: src/diginet_frame.c:89 `f->body_sum == f->h.sum` -> `f->body_sum != f->h.sum`
	 * input: fader_move */
	if (f->body_sum != w->body_sum || f->sum_matches != (w->sum == w->body_sum))
		abort();
	int ka = w->cmd == SPEC_CMD_DATA && w->body_len == 1 && w->body[0] == 0x00;
	/* A keepalive is a data frame whose body is the single byte 00, and nothing else is.
	 * contract: diginet.h:120; docs/protocol.md:64
	 * mutant: src/diginet_frame.c:57 `f->body[0] == 0x00` -> `f->body[0] == 0x01`
	 * input: keepalive */
	if (diginet_frame_is_keepalive(f) != ka)
		abort();
}

FUZZ_CHECK check_round_trip(const struct spec_frame *w)
{
	size_t n_want = SPEC_BODY_AT + w->body_len;
	if (n_want < SPEC_MIN_FRAME)
		n_want = SPEC_MIN_FRAME;
	uint8_t *out = fuzz_alloc(n_want), *want = fuzz_alloc(n_want);
	/* the builder ignores numbytes and sum (diginet.h:111): h carries the frame's own sum, and
	 * a numbytes that is never 16 plus the body length, so a builder that reads either shows */
	struct diginet_header h = {
		.numbytes = (uint16_t)~w->numbytes, .sum = w->sum,
		.send_counter = w->send, .ack_counter = w->ack, .retry = w->retry,
		.cmd = w->cmd, .num_commands = w->ncmds,
	};
	int fits = w->body_len <= SPEC_MAX_BODY;
	int sys = spec_system_at(w->body, w->body_len) >= 0;

	/* every build below writes over bytes that are not zero, so padding left unwritten shows */
	memset(out, 0xa5, n_want);
	int n = diginet_frame_build(out, n_want, w->dst, w->src, &h, w->body, w->body_len,
				    DIGINET_SUM_BODY);
	/* A body larger than an Ethernet frame carries is not built.
	 * contract: fuzz/spec.h SPEC_MAX_BODY (a 1500-byte payload); diginet.h:111-114
	 * mutant: src/diginet_frame.c:102 `body_len > DIGINET_MAX_BODY_LEN` -> `body_len > DIGINET_MAX_BODY_LEN + 1`
	 * input: body-past-max
	 * mutant: include/diginet/diginet.h:37 `1514` -> `1515`
	 * input: body-past-max */
	if (!fits && n != SPEC_E_LENGTH)
		abort();
	/* A body holding the system family F0 13 xx 70 is never built.
	 * contract: docs/protocol.md:140-144; diginet.h:113-114
	 * mutant: src/diginet_frame.c:104 `!= DIGINET_OK` -> `> DIGINET_OK`
	 * input: system-body */
	if (fits && sys && n != SPEC_E_REFUSED)
		abort();
	/* Every other body is built, into a frame of 30 bytes and the body, at least 60.
	 * contract: docs/protocol.md:30; diginet.h:111-114
	 * mutant: src/diginet_frame.c:106 `DIGINET_BODY_OFFSET + body_len;` -> `DIGINET_BODY_OFFSET + body_len + 1;`
	 * input: announce_cntrl24 */
	if (fits && !sys && n != (int)n_want)
		abort();
	spec_build_frame(want, w->dst, w->src, w->send, w->ack, w->retry, w->cmd, w->ncmds,
			 w->body, w->body_len, 0);
	/* The frame built is the frame its fields make, byte for byte, its sum the body's.
	 * contract: fuzz/spec.h spec_build_frame; docs/protocol.md:37-43; diginet.h:111-114
	 * mutant: src/diginet_frame.c:118 `h->ack_counter` -> `h->send_counter`
	 * input: ack
	 * mutant: src/diginet_frame.c:125 `memset(buf + len, 0,` -> `memset(buf + len, 1,`
	 * input: keepalive */
	if (n == (int)n_want && memcmp(out, want, n_want))
		abort();
	if (fits && !sys) {
		spec_build_frame(want, w->dst, w->src, w->send, w->ack, w->retry, w->cmd, w->ncmds,
				 w->body, w->body_len, 1);
		memset(out, 0xa5, n_want);
		n = diginet_frame_build(out, n_want, w->dst, w->src, &h, w->body, w->body_len,
					DIGINET_SUM_ZERO);
		/* In the zero-sum mode the same frame carries zero where the sum goes.
		 * contract: diginet.h:76-80, DIGINET_SUM_ZERO; docs/protocol.md:38
		 * mutant: src/diginet_frame.c:116 `: 0);` -> `: 1);`
		 * input: keepalive
		 * mutant: src/diginet_frame.c:116 `: 0);` -> `: h->sum);`
		 * input: fader_move */
		if (n != (int)n_want || memcmp(out, want, n_want))
			abort();
		/* an allocation of exactly one byte short of the frame, so a write past it is a
		 * sanitizer report, filled with a known byte, so a write into it shows */
		uint8_t *shy = fuzz_alloc(n_want - 1);
		memset(shy, 0x5a, n_want - 1);
		n = diginet_frame_build(shy, n_want - 1, w->dst, w->src, &h, w->body, w->body_len,
					DIGINET_SUM_BODY);
		/* A buffer one byte short of the frame is no room.
		 * contract: diginet.h:112-113, DIGINET_E_SPACE when cap is too small
		 * mutant: src/diginet_frame.c:108 `cap < out` -> `cap + 1 < out`
		 * input: keepalive */
		if (n != SPEC_E_SPACE)
			abort();
		/* No room means nothing is built: each byte of the buffer is as it was.
		 * contract: diginet.h:112-113, DIGINET_E_SPACE when cap is too small
		 * mutant: src/diginet_frame.c:108 `cap < out` -> `memset(buf, 0, out), cap < out`
		 * input: keepalive */
		if (!fuzz_all(shy, n_want - 1, 0x5a))
			abort();
		free(shy);
	}
	free(want);
	free(out);
}

/* the length of a string the library wrote into a field of `cap` bytes, or cap when no NUL
 * ends it there */
static size_t field_len(const char *s, size_t cap)
{
	size_t n = 0;
	while (n < cap && s[n])
		n++;
	return n;
}

FUZZ_CHECK check_announce(const struct diginet_frame *f, const struct spec_frame *w)
{
	struct diginet_announce a;
	int is_ann = w->cmd == SPEC_CMD_E0 || w->cmd == SPEC_CMD_E1;

	memset(&a, 0xa5, sizeof a);
	int r = diginet_announce_parse(f, &a);
	/* Only an e0 or an e1 is an announce.
	 * contract: protocol/diginet.ksy seq `body` (switch-on header.cmd: announce_offline,
	 * announce_session); diginet.h:126-134
	 * mutant: src/diginet_frame.c:142 `f->h.cmd != DIGINET_CMD_ANNOUNCE_SESSION` -> `f->h.cmd != DIGINET_CMD_DATA`
	 * input: keepalive */
	if (!is_ann && r != SPEC_E_NOT_ANNOUNCE)
		abort();
	/* An announce body shorter than its two fields is refused as a length.
	 * contract: protocol/diginet.ksy `announce` (15 + 9 + 9 = 33 bytes)
	 * mutant: src/diginet_frame.c:144 `f->body_len < 33` -> `f->body_len < 32`
	 * input: announce-body-32 */
	if (is_ann && w->body_len < SPEC_ANN_MIN && r != SPEC_E_LENGTH)
		abort();
	/* An e0 or e1 of 33 body bytes or more is read.
	 * contract: protocol/diginet.ksy `announce`
	 * mutant: src/diginet_frame.c:144 `f->body_len < 33` -> `f->body_len < 34`
	 * input: announce-body-33 */
	if (is_ann && w->body_len >= SPEC_ANN_MIN && r != SPEC_OK)
		abort();
	if (r != SPEC_OK)
		return;
	/* `unknown` is the first 15 body bytes.
	 * contract: protocol/diginet.ksy `announce` `unknown` (size: 15)
	 * mutant: src/diginet_frame.c:147 `15;` -> `14;`
	 * input: announce_cntrl24 */
	if (a.unknown != w->body || a.unknown_len != SPEC_ANN_UNKNOWN)
		abort();
	size_t vn = spec_strz_len(w->body + SPEC_ANN_VERSION);
	size_t nn = spec_strz_len(w->body + SPEC_ANN_NAME);
	/* The version is the body bytes from 15 up to the first NUL, at most 9, terminated.
	 * contract: protocol/diginet.ksy `announce` `version` (strz, size: 9)
	 * mutant: src/diginet_frame.c:148 `f->body + 15` -> `f->body + 14`
	 * input: announce_cntrl24
	 * mutant: src/diginet_frame.c:148 `15, 9);` -> `15, 8);`
	 * input: announce-unterminated */
	if (field_len(a.version, sizeof a.version) != vn ||
	    memcmp(a.version, w->body + SPEC_ANN_VERSION, vn))
		abort();
	/* The name is the body bytes from 24 up to the first NUL, at most 9, terminated.
	 * contract: protocol/diginet.ksy `announce` `name` (strz, size: 9)
	 * mutant: src/diginet_frame.c:149 `f->body + 24` -> `f->body + 23`
	 * input: announce_cntrl24 */
	if (field_len(a.name, sizeof a.name) != nn || memcmp(a.name, w->body + SPEC_ANN_NAME, nn))
		abort();
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	struct diginet_frame f;
	struct spec_frame w;

	if (size >= FUZZ_INPUT_MAX)
		return 0;
	uint8_t *buf = fuzz_dup(data, size);
	memset(&f, 0, sizeof f);
	int r = diginet_frame_parse(buf, size, &f);
	spec_read_frame(buf, size, &w);
	check_parse_refusal(r, &w);
	if (w.code == SPEC_OK) {
		check_parse_fields(buf, &f, &w);
		check_round_trip(&w);
		check_announce(&f, &w);
	}
	free(buf);
	return 0;
}
