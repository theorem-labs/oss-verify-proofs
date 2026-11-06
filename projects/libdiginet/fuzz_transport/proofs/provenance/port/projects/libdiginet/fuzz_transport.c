// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>

/* libFuzzer harness: THE SESSION (transport/src/diginet_session.c), the state machine of
 * include/diginet/transport/diginet_session.h fed desk frames in any order and from every
 * state, with commands submitted, time passing and the host waking and closing as the input
 * chooses.
 *
 * The session's io is the harness: send records each frame the session sends (and fails one
 * when the input asks), recv hands diginet_session_poll() a frame the input chose, and the
 * clock is a time the input moves. No socket, no clock, no thread.
 *
 * Input: [flags] [config], then up to OPS_MAX operations, each [op] and its arguments.
 *   flags: bit 0 auto_wake, bit 1 the zero header sum, bit 2 desk_mac_set (the Control|24
 *   below), bit 3 raw commands (else tagged, see op 4).
 *   config: max_retries u8 % 8, ack_timeout_ms 1 + u8, keepalive_ms 1 + u16, backoff_ms u8,
 *   offline_ms 1 + u16, wake_timeout_ms 1 + u16, display_gap_us u16, max_cmds 1 + u8 % 255,
 *   max_body 24 + u16 % 1461.
 *   op % 9:
 *     0 u16-len bytes      one raw frame to diginet_session_rx()
 *     1 sel s16 a16 retry u16-len bytes
 *                          one frame built from these fields (fuzz/spec.h, spec_build_frame):
 *                          sel & 7 the command (data, a0, e0, e1, e2, e3, an unknown 0x55,
 *                          data), sel >> 3 & 3 the source (the desk, another Digidesign desk,
 *                          this host, a non-Digidesign MAC), sel >> 5 & 3 the destination (this
 *                          host, broadcast, another host, this host); sel & 0x80 acks the last
 *                          data or e2 frame the session sent instead of a16; then the bytes
 *                          are the body (at most 1484)
 *     2 sel mac name       an announce: sel & 1 e1 else e0, from the desk to broadcast; the
 *                          host's MAC at body offset mac % 16 when that is under 10, another
 *                          host's at mac % 16 - 10 when under 13, else none; name % 3 is
 *                          "CNTRL|24", "MAINUNIT" or "OTHER"
 *     3 scale u16          time passes by u16 times 1 us, 1 ms, 100 ms or 1 s; then tick
 *     4                    a command to diginet_session_submit():
 *                            tagged: kind addr flags len, then len % 22 + 3 bytes of which
 *                            the harness writes the first three (A0 and a serial number, so
 *                            it can tell each command in a sent body) and the input the rest;
 *                            raw: kind addr flags, then u16-len bytes (at most 24)
 *                          kind % 9 + 1 is the key kind, addr its address, flags bit 0 the
 *                          display flag
 *     5                    diginet_session_wake()
 *     6                    diginet_session_close()
 *     7                    the next send fails (-EIO)
 *     8 pf u16-len bytes   diginet_session_poll(), its recv handing over this frame; pf bit 0:
 *                          twice (the drain after the tick), bit 1: recv fails instead
 *
 * THE MODEL. The harness runs the session the header describes, on its own: the desk it
 * learns, its state and the reason of each change, the handshake since the last e2, the
 * desk's latest announce, the frame in flight and its retransmissions, the keepalive clock,
 * the back-off after a desk retry, the display pacing, the host's counter and the queue of
 * commands. Before each operation (in a poll, each frame) it works out what the operation owes
 * (the state changes, the frames and notices); then the library runs, every frame it sends and
 * every notice it gives is held to the model as it happens, and the state, the timers and the
 * queue are held to it after. A frame the session sends is read with the harness's own reader.
 * No expected value comes from the library; the failure of a send is the harness's own choice.
 *
 * Properties, each an abort() in a check_ function:
 *   - sent: every frame the session sends is a frame of the grammar from this host to the
 *     known desk, padded to 60 bytes with zeros, its header sum the body's (or zero in the
 *     zero-sum mode), and holds no system family F0 13 xx 70.
 *   - ack: every desk data frame to this host is ACKed at once, while the session is not
 *     closed: one a0 echoing the frame's send counter, with no body; and no other frame is.
 *   - inflight: one host frame is in flight, and data goes only while online; a
 *     retransmission is that frame again, retry 1, 2, ... never past max_retries, never before
 *     ack_timeout, and always once it is due; DIGINET_N_ACKED comes for the ACK of the frame in
 *     flight and only for it, DIGINET_N_ACK_LOST after exactly max_retries; the deadline is
 *     never later than the next retransmission, nor than a second away.
 *   - state: the session changes state exactly as the header's diagram says, for the reason
 *     it names: ONLINE only after an a0 for its e2 and an e1 naming this host since that e2;
 *     an e2 exactly when the host wakes and never while the desk's latest announce is a session
 *     with another host; an e3 on close only to a desk not in another host's session; every
 *     announce, desk data frame and foreign session noticed as the header says, a desk's
 *     announce with the announce it carries.
 *   - keepalive: a keepalive goes every keepalive_ms on its own clock, never early, never
 *     skipped while nothing is in flight and no back-off holds; ACKs and data never move it.
 *   - latest: latest wins, and nothing is lost (tagged commands): a sent body is commands
 *     submitted and still pending, at most max_cmds and max_body, its count the commands in it,
 *     its counter the host's advanced by them, a display write never sooner than display_gap_us
 *     after the last; the queue is exactly the pending commands, in order, a newer one in its
 *     key's place, and after a tick a command that may go has gone; the queue refuses only
 *     when 512 commands are pending.
 *   - refusal: a command that holds F0 13 xx 70 is refused by diginet_session_submit() and
 *     not queued, and no other command is refused as such.
 */
#include <errno.h>

#include <diginet/diginet.h>
#include <diginet/diginet_codec.h>
#include <diginet/transport/diginet_session.h>

#include "fuzz.h"

#define OPS_MAX     1024
#define TAG         0xa0
#define CMDS_MAX    OPS_MAX
#define TRANS_MAX   16
/* The retry field of a frame: Ethernet header, then numbytes u2, sum u2, send u4, ack u4.
 * contract: protocol/diginet.ksy `header` `retry` (u2); docs/protocol.md:41 */
#define RETRY_AT    (SPEC_ETH_HDR + 12)

/* The states, the reasons and the notices. contract: diginet_session.h:39-57, :78-85 */
enum { S_IDLE = 0, S_WAKING, S_ONLINE, S_CLOSED };
enum { R_NONE = 0, R_WAKE, R_ONLINE, R_DESK_OFFLINE, R_SILENCE, R_FOREIGN, R_WAKE_TIMEOUT,
       R_DESK_DISCONNECT, R_CLOSED };
enum { N_DESK = 1, N_STATE, N_DATA, N_ACKED, N_ACK_LOST, N_FOREIGN };
/* The queue holds 512 commands. contract: diginet_session.h:109 */
#define QUEUE_MAX   512

static const uint8_t HOST[SPEC_MAC]  = { 0x02, 0x00, 0x00, 0x00, 0x00, 0x01 };
static const uint8_t OTHER[SPEC_MAC] = { 0x02, 0x00, 0x00, 0x00, 0x00, 0x02 };
static const uint8_t DESK[SPEC_MAC]  = { 0x00, 0xa0, 0x7e, 0x24, 0x00, 0x01 };
static const uint8_t DESK2[SPEC_MAC] = { 0x00, 0xa0, 0x7e, 0x08, 0x00, 0x01 };
static const uint8_t NOTDD[SPEC_MAC] = { 0x00, 0x11, 0x22, 0x33, 0x44, 0x55 };

static struct diginet_session g_s;
static struct diginet_session_config g_cfg;
static uint64_t g_now;
static int g_fail_next;
static int g_raw;
static uint32_t g_last_counter;   /* of the last data or e2 frame sent */
static uint32_t g_rx_send;        /* the send counter of the frame being received */

static uint64_t ms(uint32_t v)
{
	return (uint64_t)v * 1000u;
}

/* ---------------------------------------------------------------- the model */

static struct {
	int desk_known;
	uint8_t desk[SPEC_MAC];
	int state;
	int e2_acked, e1_us, foreign;     /* the handshake since the last e2; the latest announce */
	uint64_t last_rx, wake_sent, next_ka, backoff_until, last_display;
	int display_sent;
	int desk_counter_valid;
	uint32_t desk_counter;
	uint32_t host_counter;
	int fail;                         /* the next send fails */
	struct {
		int on;
		uint8_t cmd;
		uint32_t counter, retries;
		uint64_t sent;
		uint8_t frame[SPEC_MAX_FRAME];   /* the whole frame as it first went */
		size_t len;
	} fly;
} M;

/* the tagged commands, and the queue as the model holds it: their serials in order */
enum { PENDING = 1, SENT, REPLACED };
static struct tagged {
	int st;
	uint32_t key;
	int display;
	uint8_t bytes[SPEC_CMD_MAX];
	uint8_t len;
} g_cmd[CMDS_MAX];
static unsigned g_ncmd;
static unsigned g_q[CMDS_MAX], g_nq;

/* what one operation owes, worked out before the library runs, and what it got */
struct trans {
	int state, old, reason;
};
static struct {
	int n;
	struct trans t[TRANS_MAX];
	int e2, e3, acks, desk, foreign, acked, ndata;
	uint32_t acked_counter, acked_retry;
	int desk_off;
	const struct spec_desk *desk_p;
	const uint8_t *desk_body;         /* the body of the desk's latest announce */
	struct {
		const uint8_t *body;
		size_t len;
		uint32_t counter;
		uint16_t retry;
	} dn[2];
} OW;
static struct {
	int n;
	struct trans t[TRANS_MAX];
	int e2, e3, acks, desk, foreign, acked, ndata;
} GOT;

static int coalescable(uint32_t key)
{
	/* a key of a host-side address coalesces; desk-side input and the keepalive never do.
	 * contract: diginet_codec.h:57-58 */
	uint8_t k = (uint8_t)(key >> 16);
	return k != 0 && k != SPEC_KEY_INPUT && k != SPEC_KEY_KEEPALIVE;
}

static void m_set(int st, int why)
{
	if (M.state == st)
		return;
	if (OW.n < TRANS_MAX) {
		OW.t[OW.n].state = st;
		OW.t[OW.n].old = M.state;
		OW.t[OW.n].reason = why;
	}
	OW.n++;
	M.state = st;
}

/* a session that ends: nothing in flight, the desk's counter forgotten (diginet_session.h:9) */
static void m_lost(int why)
{
	M.fly.on = 0;
	M.desk_counter_valid = 0;
	m_set(S_IDLE, why);
}

/* diginet_session.h:169-171: the code a wake owes, and the e2 it sends */
static int m_wake(void)
{
	if (!M.desk_known)
		return SPEC_E_ARG;
	if (M.foreign)
		return SPEC_E_REFUSED;
	M.e1_us = M.e2_acked = 0;
	M.wake_sent = g_now;
	OW.e2++;
	int fails = M.fail;
	M.fail = 0;
	if (fails)
		return -EIO;
	m_set(S_WAKING, R_WAKE);
	return SPEC_OK;
}

/* WAKING --(desk a0 for the e2, and an e1 naming this host)--> ONLINE (diginet_session.h:8);
 * the keepalive clock starts then */
static void m_maybe_online(void)
{
	if (M.state == S_WAKING && M.e2_acked && M.e1_us) {
		M.next_ka = M.last_rx + ms(g_cfg.keepalive_ms);
		m_set(S_ONLINE, R_ONLINE);
	}
}

/* the timeouts of a tick: no answer to e2, silence (diginet_session.h:9, :54, :52) */
static void m_tick(void)
{
	if (M.state == S_WAKING && g_now - M.wake_sent >= ms(g_cfg.wake_timeout_ms))
		m_lost(R_WAKE_TIMEOUT);
	else if (M.state == S_ONLINE && g_now - M.last_rx >= ms(g_cfg.offline_ms))
		m_lost(R_SILENCE);
}

/* where this host's MAC sits in the 15 leading bytes of an e1 body, or -1
 * (docs/protocol.md:49, :203, A6) */
static int host_offset(const uint8_t *body)
{
	for (int i = 0; i + SPEC_MAC <= SPEC_ANN_UNKNOWN; i++)
		if (!memcmp(body + i, HOST, SPEC_MAC))
			return i;
	return -1;
}

/* the desk an announce name selects (docs/protocol.md:47) */
static const struct spec_desk *desk_named(const uint8_t *body)
{
	size_t n = spec_strz_len(body + SPEC_ANN_NAME);
	if (n == strlen(SPEC_C24.name) && !memcmp(body + SPEC_ANN_NAME, SPEC_C24.name, n))
		return &SPEC_C24;
	if (n == strlen(SPEC_PC.name) && !memcmp(body + SPEC_ANN_NAME, SPEC_PC.name, n))
		return &SPEC_PC;
	return NULL;
}

/* One frame received. The session reads only a frame of the grammar, from someone else, to
 * this host or to everyone; from the desk it knows, or, while it knows none, an announce from
 * a Digidesign MAC, which names the desk (docs/protocol.md:27, :31; diginet_session.h:61).
 * Nothing is read once the session is closed. Returns 1 when the session reads the frame,
 * which ends with a tick. */
static int m_rx(const uint8_t *frame, size_t n)
{
	struct spec_frame f;
	if (spec_read_frame(frame, n, &f) != SPEC_OK)
		return 0;
	if (!memcmp(f.src, HOST, SPEC_MAC) ||
	    (memcmp(f.dst, HOST, SPEC_MAC) && memcmp(f.dst, SPEC_BCAST, SPEC_MAC)))
		return 0;
	if (M.desk_known) {
		if (memcmp(f.src, M.desk, SPEC_MAC))
			return 0;
	} else {
		if (f.cmd != SPEC_CMD_E0 && f.cmd != SPEC_CMD_E1)
			return 0;
		if (memcmp(f.src, SPEC_OUI, sizeof SPEC_OUI))
			return 0;
		memcpy(M.desk, f.src, SPEC_MAC);
		M.desk_known = 1;
	}
	if (M.state == S_CLOSED)
		return 0;
	M.last_rx = g_now;
	switch (f.cmd) {
	case SPEC_CMD_E0:
	case SPEC_CMD_E1: {
		if (f.body_len < SPEC_ANN_MIN)
			break;
		int off = f.cmd == SPEC_CMD_E1 ? host_offset(f.body) : -1;
		OW.desk++;
		OW.desk_off = off;
		OW.desk_p = desk_named(f.body);
		OW.desk_body = f.body;
		if (f.cmd == SPEC_CMD_E0) {
			/* ONLINE --(e0)--> IDLE; auto_wake sends e2 on an e0 (diginet_session.h:9, :63) */
			M.foreign = 0;
			if (M.state == S_ONLINE)
				m_lost(R_DESK_OFFLINE);
			if (M.state == S_IDLE && g_cfg.auto_wake)
				m_wake();
		} else if (off >= 0) {
			M.foreign = 0;
			M.e1_us = 1;
			m_maybe_online();
		} else {
			/* an e1 naming another host ends ours (diginet_session.h:9, :53, :84) */
			M.foreign = 1;
			OW.foreign++;
			if (M.state == S_ONLINE || M.state == S_WAKING)
				m_lost(R_FOREIGN);
		}
		break;
	}
	case SPEC_CMD_ACK:
		if (M.fly.on && f.ack == M.fly.counter) {
			OW.acked++;
			OW.acked_counter = M.fly.counter;
			OW.acked_retry = M.fly.retries;
			M.fly.on = 0;
			if (M.state == S_WAKING) {
				M.e2_acked = 1;
				m_maybe_online();
			}
		}
		break;
	case SPEC_CMD_DATA:
		/* ACKed at once; a desk retry holds the host back; a retransmission of the frame
		 * just delivered is not delivered again; a keepalive is not delivered
		 * (diginet_session.h:13, :17, :81) */
		OW.acks++;
		M.fail = 0;
		if (f.retry)
			M.backoff_until = g_now + ms(g_cfg.backoff_ms);
		if (M.desk_counter_valid && f.send == M.desk_counter && f.retry)
			break;
		M.desk_counter = f.send;
		M.desk_counter_valid = 1;
		if (f.body_len == 1 && f.body[0] == 0x00)
			break;
		if (OW.ndata < 2) {
			OW.dn[OW.ndata].body = f.body;
			OW.dn[OW.ndata].len = f.body_len;
			OW.dn[OW.ndata].counter = f.send;
			OW.dn[OW.ndata].retry = f.retry;
		}
		OW.ndata++;
		break;
	case SPEC_CMD_E3:
		if (M.state == S_ONLINE || M.state == S_WAKING)
			m_lost(R_DESK_DISCONNECT);
		break;
	default:
		break;
	}
	m_tick();
	return 1;
}

/* diginet_session.h:173-174 */
static void m_close(void)
{
	if (M.desk_known && !M.foreign && M.state != S_CLOSED) {
		OW.e3++;
		M.fail = 0;
	}
	M.fly.on = 0;
	m_set(S_CLOSED, R_CLOSED);
}

static void op_begin(void)
{
	memset(&OW, 0, sizeof OW);
	memset(&GOT, 0, sizeof GOT);
	OW.desk_off = -1;
	M.fail = g_fail_next;
}

/* ---------------------------------------------------------------- the properties */

FUZZ_CHECK check_sent_frame(const uint8_t *frame, size_t len, const struct spec_frame *f)
{
	/* A frame the session sends is a frame of the grammar, from this host to the desk it
	 * knows, and carries no system family.
	 * contract: protocol/diginet.ksy seq; docs/protocol.md:31, :140-144; diginet.h:113-114
	 * mutant: transport/src/diginet_session.c:101 `s->desk_mac, s->cfg.host_mac` -> `s->cfg.host_mac, s->desk_mac`
	 * input: online */
	if (f->code != SPEC_OK || memcmp(f->src, HOST, SPEC_MAC) || !M.desk_known ||
	    memcmp(f->dst, M.desk, SPEC_MAC) || spec_system_at(f->body, f->body_len) >= 0)
		abort();
	size_t n = SPEC_BODY_AT + f->body_len < SPEC_MIN_FRAME ? SPEC_MIN_FRAME : SPEC_BODY_AT + f->body_len;
	int zeros = 1;
	for (size_t i = SPEC_BODY_AT + f->body_len; i < len; i++)
		zeros &= frame[i] == 0;
	/* It is padded with zeros to 60 bytes, and its header sum is the body's, or zero in the
	 * zero-sum mode.
	 * contract: docs/protocol.md:30, :38; diginet_session.h:64
	 * mutant: transport/src/diginet_session.c:394 `s->cfg.sum_mode` -> `DIGINET_SUM_ZERO`
	 * input: coalesce */
	if (len != n || !zeros ||
	    f->sum != (g_cfg.sum_mode == DIGINET_SUM_ZERO ? 0 : spec_sum(f->body, f->body_len)))
		abort();
}

FUZZ_CHECK check_ack_frame(const struct spec_frame *f)
{
	/* The ACK echoes the send counter of the frame it answers, and has no body.
	 * contract: diginet_session.h:13; docs/protocol.md:40, :56
	 * mutant: transport/src/diginet_session.c:242 `f->h.send_counter` -> `f->h.ack_counter`
	 * input: data-acked */
	if (f->ack != g_rx_send || f->body_len != 0 || f->retry != 0)
		abort();
}

FUZZ_CHECK check_inflight_new(void)
{
	/* A data frame goes only while online, and only when no frame is in flight.
	 * contract: diginet_session.h:14, :166
	 * mutant: transport/src/diginet_session.c:445 `s->state != DIGINET_S_ONLINE || s->inflight` -> `s->inflight`
	 * input: online
	 * mutant: transport/src/diginet_session.c:445 `s->inflight || now < s->backoff_until_us` -> `now < s->backoff_until_us`
	 * input: batches */
	if (M.state != S_ONLINE || M.fly.on)
		abort();
	/* A data frame never goes while a back-off after a desk retry holds.
	 * contract: diginet_session.h:16-17
	 * mutant: transport/src/diginet_session.c:445 `now < s->backoff_until_us` -> `(now < s->backoff_until_us && now >= s->next_keepalive_us)`
	 * input: backoff-exact */
	if (g_now < M.backoff_until)
		abort();
}

FUZZ_CHECK check_inflight_retry(const uint8_t *frame, size_t len, const struct spec_frame *f)
{
	/* A retransmission is the frame in flight again: each byte of the frame that first went,
	 * but the two of its retry field.
	 * contract: diginet_session.h:14-15; protocol/diginet.ksy `header` `retry`
	 * mutant: transport/src/diginet_session.c:136 `0, e2,` -> `0, s->inflight_frame,`
	 * input: wake-fails-in-flight
	 * mutant: transport/src/diginet_session.c:407 `DIGINET_ETH_HDR_LEN + 12` -> `DIGINET_ETH_HDR_LEN + 15`
	 * input: retransmit-data */
	if (!M.fly.on || len != M.fly.len || len < RETRY_AT + 2 || memcmp(frame, M.fly.frame, RETRY_AT) ||
	    memcmp(frame + RETRY_AT + 2, M.fly.frame + RETRY_AT + 2, len - RETRY_AT - 2))
		abort();
	/* Its retry field counts the retransmissions, 1, 2, ..., never past max_retries.
	 * contract: diginet_session.h:14-15; docs/protocol.md:41
	 * mutant: transport/src/diginet_session.c:431 `s->inflight_retries < s->cfg.max_retries` -> `s->inflight_retries <= s->cfg.max_retries`
	 * input: wake-unanswered */
	if (f->retry != M.fly.retries + 1 || f->retry > g_cfg.max_retries)
		abort();
	/* It goes no sooner than ack_timeout after the frame last went.
	 * contract: diginet_session.h:14-15
	 * mutant: transport/src/diginet_session.c:430 `>= ms(s->cfg.ack_timeout_ms)` -> `>= ms(s->cfg.ack_timeout_ms) / 2`
	 * input: retry-timing */
	if (g_now - M.fly.sent < ms(g_cfg.ack_timeout_ms))
		abort();
}

FUZZ_CHECK check_inflight_acked(const struct diginet_notice *n)
{
	/* DIGINET_N_ACKED comes for the ACK of the frame in flight, and names it.
	 * contract: diginet_session.h:82
	 * mutant: transport/src/diginet_session.c:231 `.counter = f->h.ack_counter` -> `.counter = f->h.ack_counter + 1`
	 * input: online */
	if (GOT.acked > OW.acked || n->counter != OW.acked_counter || n->retry != OW.acked_retry)
		abort();
}

FUZZ_CHECK check_inflight_lost(const struct diginet_notice *n)
{
	/* DIGINET_N_ACK_LOST comes for the frame in flight after exactly max_retries.
	 * contract: diginet_session.h:15, :83
	 * mutant: transport/src/diginet_session.c:440 `.retry = (uint16_t)s->inflight_retries` -> `.retry = 0`
	 * input: wake-unanswered */
	if (!M.fly.on || n->counter != M.fly.counter || M.fly.retries != g_cfg.max_retries ||
	    n->retry != g_cfg.max_retries)
		abort();
}

FUZZ_CHECK check_state_online(void)
{
	/* ONLINE only after the desk's a0 for the e2 and an e1 naming this host since that e2.
	 * contract: diginet_session.h:8, :50
	 * mutant: transport/src/diginet_session.c:178 `s->wake_acked && s->e1_named_us` -> `s->e1_named_us`
	 * input: e1-before-ack */
	if (!M.e2_acked || !M.e1_us)
		abort();
}

FUZZ_CHECK check_state_wake(void)
{
	/* Never an e2 while the desk's latest announce is a session with another host.
	 * contract: diginet_session.h:22, :169-170
	 * mutant: transport/src/diginet_session.c:125 `if (s->foreign)` -> `if (s->foreign && s->state == DIGINET_S_ONLINE)`
	 * input: wake-foreign */
	if (M.foreign)
		abort();
}

FUZZ_CHECK check_state_wake_code(int rc, int want)
{
	/* A wake is refused while another host holds the desk, and with no desk known.
	 * contract: diginet_session.h:169-171
	 * mutant: transport/src/diginet_session.c:127 `return DIGINET_E_REFUSED;` -> `return DIGINET_E_ARG;`
	 * input: wake-foreign */
	if (rc != want)
		abort();
}

FUZZ_CHECK check_state_desk(const struct diginet_notice *n)
{
	/* An announce from the desk is noticed with where this host's MAC sits in an e1 body
	 * and the desk its name selects.
	 * contract: diginet_session.h:79, :94; docs/protocol.md:47, :203
	 * mutant: transport/src/diginet_session.c:170 `i + DIGINET_MAC_LEN <= a->unknown_len` -> `i + DIGINET_MAC_LEN < a->unknown_len`
	 * input: e1-mac-at-9 */
	if (GOT.desk > OW.desk || n->mac_offset != OW.desk_off || !n->personality != !OW.desk_p ||
	    (n->personality && (n->personality->device != OW.desk_p->device ||
				n->personality->strips != OW.desk_p->strips)))
		abort();
	/* The notice carries the announce.
	 * contract: diginet_session.h:79
	 * mutant: transport/src/diginet_session.c:197 `.announce = &a` -> `.announce = NULL`
	 * input: online */
	if (!n->announce)
		abort();
	size_t vn = spec_strz_len(OW.desk_body + SPEC_ANN_VERSION);
	size_t nn = spec_strz_len(OW.desk_body + SPEC_ANN_NAME);
	/* Its version is the body bytes from 15 and its name the body bytes from 24, each up to
	 * its first NUL and at most 9, terminated. The body's first vn (nn) bytes there are not
	 * NUL, so equal bytes and a NUL after them are the field's whole length.
	 * contract: diginet_session.h:79; protocol/diginet.ksy `announce` `version` `name` (strz,
	 * size: 9)
	 * mutant: src/diginet_frame.c:148 `f->body + 15` -> `f->body + 14`
	 * input: online */
	if (memcmp(n->announce->version, OW.desk_body + SPEC_ANN_VERSION, vn) ||
	    n->announce->version[vn] || memcmp(n->announce->name, OW.desk_body + SPEC_ANN_NAME, nn) ||
	    n->announce->name[nn])
		abort();
}

FUZZ_CHECK check_state_data(const struct diginet_notice *n)
{
	/* A desk data frame is noticed with its body and counter.
	 * contract: diginet_session.h:81
	 * mutant: transport/src/diginet_session.c:258 `.body_len = f->body_len` -> `.body_len = f->body_len - 1`
	 * input: data-acked */
	if (GOT.ndata >= OW.ndata || GOT.ndata >= 2 || n->body_len != OW.dn[GOT.ndata].len ||
	    memcmp(n->body, OW.dn[GOT.ndata].body, n->body_len) || n->counter != OW.dn[GOT.ndata].counter ||
	    n->retry != OW.dn[GOT.ndata].retry)
		abort();
}

FUZZ_CHECK check_keepalive_due(void)
{
	/* A keepalive goes only when due on its own clock, while online, with nothing in flight
	 * and no back-off holding.
	 * contract: diginet_session.h:16-17
	 * mutant: transport/src/diginet_session.c:449 `now >= s->next_keepalive_us` -> `now + 5000 >= s->next_keepalive_us`
	 * input: keepalive-clock */
	if (M.state != S_ONLINE || M.fly.on || g_now < M.backoff_until || g_now < M.next_ka)
		abort();
}

FUZZ_CHECK check_latest_frame(const struct spec_frame *f, unsigned cmds)
{
	/* A frame holds at most max_cmds commands and max_body bytes, and its count is the
	 * commands in it.
	 * contract: diginet_session.h:20; docs/protocol.md:43
	 * mutant: transport/src/diginet_session.c:390 `.num_commands = (uint8_t)ncmds` -> `.num_commands = (uint8_t)(ncmds + 1)`
	 * input: batches */
	if (f->body_len > g_cfg.max_body || f->ncmds > g_cfg.max_cmds || (!g_raw && f->ncmds != cmds))
		abort();
	/* Its counter is the host's, advanced by the commands in it.
	 * contract: docs/protocol.md:39, :205, A8
	 * mutant: transport/src/diginet_session.c:391 `s->host_counter += ncmds;` -> `s->host_counter += 1;`
	 * input: batches */
	if (f->send != (uint32_t)(M.host_counter + f->ncmds))
		abort();
}

FUZZ_CHECK check_latest_control(const struct spec_frame *f)
{
	/* An ACK, an e2 or an e3 carries the host's counter unchanged.
	 * contract: docs/protocol.md:56, :205, A8
	 * mutant: transport/src/diginet_session.c:100 `.send_counter = s->host_counter` -> `.send_counter = s->host_counter + 1`
	 * input: online */
	if (f->send != M.host_counter)
		abort();
}

static struct tagged *tagged_of(const uint8_t *b, size_t n)
{
	if (n < 3 || b[0] != TAG)
		return NULL;
	unsigned serial = b[1] | (unsigned)b[2] << 7;
	return serial < g_ncmd ? &g_cmd[serial] : NULL;
}

static void q_remove(unsigned serial)
{
	unsigned k = 0;
	for (unsigned i = 0; i < g_nq; i++)
		if (g_q[i] != serial)
			g_q[k++] = g_q[i];
	g_nq = k;
}

FUZZ_CHECK check_latest_sent(const uint8_t *body, size_t len, int *display)
{
	size_t at = 0;
	*display = 0;
	while (at < len) {
		struct tagged *t = tagged_of(body + at, len - at);
		/* Each command of a sent body is one submitted, still the latest for its key, and
		 * not sent before.
		 * contract: diginet_session.h:18-19
		 * mutant: transport/src/diginet_session.c:365 `c->bytes, c->len);` -> `s->queue[0].bytes, c->len);`
		 * input: batches */
		if (!t || t->st != PENDING || t->len > len - at || memcmp(body + at, t->bytes, t->len))
			abort();
		t->st = SENT;
		q_remove((unsigned)(t - g_cmd));
		*display |= t->display;
		at += t->len;
	}
}

FUZZ_CHECK check_latest_display(void)
{
	/* A frame holding display writes follows the last one by at least display_gap_us.
	 * contract: diginet_session.h:20-21; docs/protocol.md:60
	 * mutant: transport/src/diginet_session.c:460 `now - s->last_display_us >= s->cfg.display_gap_us` -> `now - s->last_display_us + 1000 >= s->cfg.display_gap_us`
	 * input: batches */
	if (M.display_sent && g_now - M.last_display < g_cfg.display_gap_us)
		abort();
}

FUZZ_CHECK check_refusal_submit(const struct diginet_cmd *c, int rc, unsigned queued_before)
{
	/* A command holding F0 13 xx 70 is refused and not queued, and no other command is
	 * refused as such.
	 * contract: diginet_session.h:164-166; docs/protocol.md:140-144
	 * mutant: transport/src/diginet_session.c:332 `diginet_body_check(c->bytes, c->len)` -> `diginet_body_check(c->bytes, c->len - 1)`
	 * input: submit-system-cut-short */
	if (spec_system_at(c->bytes, c->len) >= 0 ? rc != SPEC_E_REFUSED || g_s.queued != queued_before : rc == SPEC_E_REFUSED)
		abort();
}

FUZZ_CHECK check_latest_submit(int rc, int want)
{
	/* A command is queued, or takes its key's place; the queue refuses only when 512
	 * commands are pending.
	 * contract: diginet_session.h:18-19, :109, :164-166
	 * mutant: include/diginet/transport/diginet_session.h:109 `512` -> `511`
	 * input: queue-full */
	if (rc != want)
		abort();
}

/* ---- the checks after each operation: what it owed is what it got */

FUZZ_CHECK check_ack_settle(void)
{
	/* Every desk data frame is ACKed, once each time it comes, and no other frame is.
	 * contract: diginet_session.h:13
	 * mutant: transport/src/diginet_session.c:293 `s->state == DIGINET_S_CLOSED` -> `s->state == DIGINET_S_ONLINE`
	 * input: data-acked */
	if (GOT.acks != OW.acks)
		abort();
}

FUZZ_CHECK check_state_settle(void)
{
	/* An e2 goes exactly when the host wakes: on a wake, and on an e0 with auto_wake.
	 * contract: diginet_session.h:7, :63, :169
	 * mutant: transport/src/diginet_session.c:204 `s->cfg.auto_wake` -> `!s->cfg.auto_wake`
	 * input: online */
	if (GOT.e2 != OW.e2)
		abort();
	/* An e3 goes on close, to a known desk not in another host's session, once.
	 * contract: diginet_session.h:173-174
	 * mutant: transport/src/diginet_session.c:153 `!s->foreign &&` -> ``
	 * input: close-foreign */
	if (GOT.e3 != OW.e3)
		abort();
	/* Every desk data frame but a keepalive is noticed, and a desk retry of the frame just
	 * noticed is not noticed again.
	 * contract: diginet_session.h:81
	 * mutant: transport/src/diginet_session.c:249 `f->h.send_counter == s->desk_counter && f->h.retry` -> `f->h.send_counter == s->desk_counter`
	 * input: data-repeat */
	if (GOT.ndata != OW.ndata)
		abort();
	/* Every announce of the desk is noticed, and an e1 naming another host as foreign.
	 * contract: diginet_session.h:79, :84
	 * mutant: transport/src/diginet_session.c:218 `s->notify(s->notify_ctx, &fn);` -> `(void)fn;`
	 * input: wake-foreign */
	if (GOT.desk != OW.desk || GOT.foreign != OW.foreign)
		abort();
	int same = GOT.n == OW.n && (int)g_s.state == M.state, why = 1;
	for (int i = 0; i < OW.n && i < TRANS_MAX; i++) {
		same &= GOT.t[i].state == OW.t[i].state && GOT.t[i].old == OW.t[i].old;
		why &= GOT.t[i].reason == OW.t[i].reason;
	}
	/* The session changes state exactly as the diagram says, in order.
	 * contract: diginet_session.h:7-10
	 * mutant: transport/src/diginet_session.c:426 `session_lost(s, DIGINET_R_SILENCE)` -> `(void)0`
	 * input: silence
	 * mutant: transport/src/diginet_session.c:203 `session_lost(s, DIGINET_R_DESK_OFFLINE)` -> `(void)0`
	 * input: offline-e0
	 * mutant: transport/src/diginet_session.c:311 `session_lost(s, DIGINET_R_DESK_DISCONNECT)` -> `(void)0`
	 * input: session-ends
	 * mutant: transport/src/diginet_session.c:421 `>= ms(s->cfg.wake_timeout_ms)` -> `> ms(s->cfg.wake_timeout_ms)`
	 * input: wake-timeout-exact
	 * mutant: transport/src/diginet_session.c:425 `>= ms(s->cfg.offline_ms)` -> `> ms(s->cfg.offline_ms)`
	 * input: silence-exact */
	if (!same)
		abort();
	/* Each change names its reason.
	 * contract: diginet_session.h:46-57
	 * mutant: transport/src/diginet_session.c:426 `DIGINET_R_SILENCE` -> `DIGINET_R_WAKE_TIMEOUT`
	 * input: silence */
	if (!why)
		abort();
}

FUZZ_CHECK check_inflight_settle(void)
{
	/* The ACK of the frame in flight is taken, and noticed.
	 * contract: diginet_session.h:82
	 * mutant: transport/src/diginet_session.c:225 `f->h.ack_counter != s->inflight_counter` -> `f->h.ack_counter != s->inflight_counter + 1`
	 * input: online */
	if (GOT.acked != OW.acked)
		abort();
	/* A frame in flight with no ACK after ack_timeout has been sent again, or dropped.
	 * contract: diginet_session.h:14-15
	 * mutant: transport/src/diginet_session.c:430 `if (s->inflight && now` -> `if (!s->inflight && now`
	 * input: wake-unanswered */
	if (M.fly.on && g_now - M.fly.sent >= ms(g_cfg.ack_timeout_ms))
		abort();
	uint64_t d = diginet_session_deadline(&g_s, g_now);
	/* The deadline is now or later, and never more than a second away.
	 * contract: diginet_session.h:157-158; transport/src/diginet_session.c:478
	 * mutant: transport/src/diginet_session.c:478 `now + 1000000` -> `now + 1000001`
	 * input: online */
	if (d < g_now || d > g_now + 1000000)
		abort();
	/* It is never later than the next retransmission of the frame in flight.
	 * contract: diginet_session.h:157-158, :14-15
	 * mutant: transport/src/diginet_session.c:492 `s->inflight_sent_us + ms(s->cfg.ack_timeout_ms)` -> `s->inflight_sent_us + 2 * ms(s->cfg.ack_timeout_ms)`
	 * input: wake-unanswered */
	if (M.fly.on && d > M.fly.sent + ms(g_cfg.ack_timeout_ms))
		abort();
}

FUZZ_CHECK check_keepalive_settle(void)
{
	/* A keepalive due while online, with nothing in flight and no back-off holding, has gone.
	 * In raw mode a command can be the byte 00 a keepalive is, so the clock is held in tagged
	 * mode only.
	 * contract: diginet_session.h:16-17
	 * mutant: transport/src/diginet_session.c:451 `+= ms(s->cfg.keepalive_ms);` -> `+= 2 * ms(s->cfg.keepalive_ms);`
	 * input: keepalive-clock */
	if (!g_raw && M.state == S_ONLINE && !M.fly.on && g_now >= M.backoff_until && g_now >= M.next_ka)
		abort();
}

FUZZ_CHECK check_latest_drain(void)
{
	int allow_display = !M.display_sent || g_now - M.last_display >= g_cfg.display_gap_us, ready = 0;
	for (unsigned i = 0; i < g_nq && !ready; i++)
		ready = !g_cmd[g_q[i]].display || allow_display;
	/* After a tick, a command that may go has gone: while online, with nothing in flight and
	 * no back-off holding, a pending command that is no display write, or any once the
	 * display gap has passed, leaves in a frame.
	 * contract: diginet_session.h:14, :17, :20-21
	 * mutant: transport/src/diginet_session.c:458 `if (!s->queued)` -> `if (s->queued)`
	 * input: coalesce
	 * mutant: transport/src/diginet_session.c:460 `now - s->last_display_us >= s->cfg.display_gap_us` -> `now - s->last_display_us > s->cfg.display_gap_us`
	 * input: display-gap-exact
	 * mutant: transport/src/diginet_session.c:445 `now < s->backoff_until_us` -> `now <= s->backoff_until_us`
	 * input: backoff-exact */
	if (M.state == S_ONLINE && !M.fly.on && g_now >= M.backoff_until && ready)
		abort();
}

FUZZ_CHECK check_latest_queue(void)
{
	int same = g_s.queued == g_nq;
	for (unsigned i = 0; same && i < g_nq; i++) {
		const struct tagged *t = &g_cmd[g_q[i]];
		same = g_s.queue[i].len == t->len && !memcmp(g_s.queue[i].bytes, t->bytes, t->len);
	}
	/* The queue is exactly the pending commands, in order, a newer one in its key's place.
	 * contract: diginet_session.h:18-19
	 * mutant: transport/src/diginet_session.c:339 `s->queue[i] = *c;` -> `s->queue[i].key = c->key;`
	 * input: coalesce
	 * mutant: transport/src/diginet_session.c:338 `if (s->queue[i].key == c->key) {` -> `if (0) {`
	 * input: coalesce */
	if (!same)
		abort();
}

/* ---------------------------------------------------------------- the io and the notices */

static int io_send(void *ctx, const uint8_t *frame, size_t len)
{
	struct spec_frame f;
	int fail = g_fail_next;

	(void)ctx;
	g_fail_next = 0;
	spec_read_frame(frame, len, &f);
	check_sent_frame(frame, len, &f);
	switch (f.cmd) {
	case SPEC_CMD_ACK:
		GOT.acks++;
		check_ack_frame(&f);
		check_latest_control(&f);
		break;
	case SPEC_CMD_E2:
	case SPEC_CMD_DATA:
		if (f.retry) {
			check_inflight_retry(frame, len, &f);
			M.fly.retries++;
			M.fly.sent = g_now;
			break;
		}
		if (f.cmd == SPEC_CMD_E2) {
			check_state_wake();
			check_latest_control(&f);
			GOT.e2++;
			g_last_counter = f.send;
			if (fail)
				break;   /* the wake fails, and leaves what was in flight */
		} else {
			int ka = f.body_len == 1 && f.body[0] == 0x00 && f.ncmds == 1;
			unsigned cmds = 0;
			int display = 0;
			check_inflight_new();
			if (!g_raw && !ka) {
				for (size_t at = 0; at < f.body_len; cmds++) {
					const struct tagged *t = tagged_of(f.body + at, f.body_len - at);
					at += t ? t->len : f.body_len - at;
				}
			} else {
				cmds = f.ncmds;
			}
			check_latest_frame(&f, cmds);
			M.host_counter = f.send;
			g_last_counter = f.send;
			if (!g_raw && ka) {
				check_keepalive_due();
				M.next_ka += ms(g_cfg.keepalive_ms);
				if (M.next_ka <= g_now)
					M.next_ka = g_now + ms(g_cfg.keepalive_ms);
			} else if (!g_raw) {
				check_latest_sent(f.body, f.body_len, &display);
				if (display) {
					check_latest_display();
					M.display_sent = 1;
					M.last_display = g_now;
				}
			}
		}
		M.fly.on = 1;
		M.fly.cmd = f.cmd;
		M.fly.counter = f.send;
		M.fly.retries = 0;
		M.fly.sent = g_now;
		M.fly.len = len < sizeof M.fly.frame ? len : sizeof M.fly.frame;
		memcpy(M.fly.frame, frame, M.fly.len);
		break;
	case SPEC_CMD_E3:
		GOT.e3++;
		check_latest_control(&f);
		break;
	default:
		break;
	}
	return fail ? -EIO : 0;
}

/* what poll's recv hands over: the frame, how many times, or a failure */
static const uint8_t *g_rx;
static size_t g_rx_len;
static int g_rx_times, g_rx_fail;

static int io_recv(void *ctx, uint8_t *buf, size_t cap, int timeout_ms)
{
	(void)ctx;
	(void)timeout_ms;
	if (g_rx_fail) {
		g_rx_fail = 0;
		return -EIO;
	}
	if (!g_rx || !g_rx_times)
		return 0;
	g_rx_times--;
	size_t n = g_rx_len < cap ? g_rx_len : cap;
	/* The model takes each frame just before the session reads it, so a second copy is held
	 * to what the session sent after the first; an empty frame leaves the poll's tick alone.
	 * The tick between two frames needs no model step: it comes at the time of the tick
	 * m_rx() ends with or, after a frame the session does not read, with nothing changed
	 * since the last tick, and every step of time ends in one. */
	if (n)
		m_rx(g_rx, n);
	else
		m_tick();
	memcpy(buf, g_rx, n);
	return (int)n;
}

static uint64_t io_now(void *ctx)
{
	(void)ctx;
	return g_now;
}

static void notice(void *ctx, const struct diginet_notice *n)
{
	(void)ctx;
	switch (n->kind) {
	case N_STATE:
		if (GOT.n < TRANS_MAX) {
			GOT.t[GOT.n].state = n->state;
			GOT.t[GOT.n].old = n->old_state;
			GOT.t[GOT.n].reason = n->reason;
		}
		GOT.n++;
		if (n->state == S_ONLINE)
			check_state_online();
		break;
	case N_ACKED:
		GOT.acked++;
		check_inflight_acked(n);
		break;
	case N_ACK_LOST:
		check_inflight_lost(n);
		M.fly.on = 0;
		break;
	case N_DESK:
		GOT.desk++;
		check_state_desk(n);
		break;
	case N_DATA:
		check_state_data(n);
		GOT.ndata++;
		break;
	case N_FOREIGN:
		GOT.foreign++;
		break;
	default:
		break;
	}
}

/* ---------------------------------------------------------------- the operations */

/* `ticked`: the operation ended with a tick (time passing, a frame the session read, a poll
 * whose recv did not fail), so what is due has gone; the queue's contents are the model's in
 * tagged mode only */
static void settle(int ticked)
{
	check_ack_settle();
	check_state_settle();
	check_inflight_settle();
	check_keepalive_settle();
	if (!g_raw) {
		check_latest_queue();
		if (ticked)
			check_latest_drain();
	}
}

/* a frame received, alone or through poll (poll_flags bit 0: recv hands it over twice, as a
 * desk's retransmission waiting behind it; bit 1: recv fails instead) */
static void receive(const uint8_t *p, size_t n, int by_poll, unsigned poll_flags)
{
	uint8_t *frame = fuzz_dup(p, n);
	struct spec_frame f;
	int ticked;

	op_begin();
	spec_read_frame(frame, n, &f);
	g_rx_send = f.send;
	if (by_poll) {
		size_t got = n > SPEC_MAX_FRAME ? SPEC_MAX_FRAME : n;   /* what recv hands over */
		int twice = poll_flags & 1, fails = poll_flags >> 1 & 1;
		spec_read_frame(frame, got, &f);
		g_rx_send = f.send;
		/* poll: recv, then the frame, then a tick, then whatever else is waiting; io_recv()
		 * runs the model of each */
		ticked = !fails;
		g_rx = frame;
		g_rx_len = got;
		g_rx_times = twice ? 2 : 1;
		g_rx_fail = fails;
		diginet_session_poll(&g_s, 0);
		g_rx = NULL;
		g_rx_fail = 0;
	} else {
		ticked = m_rx(frame, n);
		diginet_session_rx(&g_s, frame, n, g_now);
	}
	settle(ticked);
	free(frame);
}

static void build_and_receive(const uint8_t *dst, const uint8_t *src, uint32_t send, uint32_t ack,
			      uint16_t retry, uint8_t cmd, const uint8_t *body, size_t len)
{
	uint8_t frame[SPEC_MAX_FRAME];
	size_t n = spec_build_frame(frame, dst, src, send, ack, retry, cmd, 1, body, len, 0);
	receive(frame, n, 0, 0);
}

static void op_frame(struct fuzz_in *in)
{
	static const uint8_t CMD[7] = {
		SPEC_CMD_DATA, SPEC_CMD_ACK, SPEC_CMD_E0, SPEC_CMD_E1, SPEC_CMD_E2, SPEC_CMD_E3, 0x55,
	};
	static const uint8_t *const SRC[4] = { DESK, DESK2, HOST, NOTDD };
	static const uint8_t *const DST[4] = { HOST, SPEC_BCAST, OTHER, HOST };
	const uint8_t *body;
	uint8_t sel = fuzz_u8(in);
	uint32_t send = fuzz_u16(in), ack = fuzz_u16(in);
	if (sel & 0x80)
		ack = g_last_counter;
	uint16_t retry = fuzz_u8(in) & 3;
	size_t len = fuzz_take(in, fuzz_u16(in) % (SPEC_MAX_BODY + 1), &body);
	build_and_receive(DST[sel >> 5 & 3], SRC[sel >> 3 & 3], send, ack, retry, CMD[(sel & 7) % 7], body, len);
}

static void op_announce(struct fuzz_in *in)
{
	static const char *const NAME[3] = { "CNTRL|24", "MAINUNIT", "OTHER" };
	uint8_t sel = fuzz_u8(in), mac = fuzz_u8(in) % 16, name = fuzz_u8(in) % 3;
	uint8_t body[SPEC_ANN_MIN + 1];

	memset(body, 0, sizeof body);
	if (mac < 10)
		memcpy(body + mac, HOST, SPEC_MAC);
	else if (mac < 13)
		memcpy(body + mac - 10, OTHER, SPEC_MAC);
	memcpy(body + SPEC_ANN_VERSION, "1.37", 4);
	memcpy(body + SPEC_ANN_NAME, NAME[name], strlen(NAME[name]));
	build_and_receive(SPEC_BCAST, DESK, 0, 0, 0, sel & 1 ? SPEC_CMD_E1 : SPEC_CMD_E0, body, sizeof body);
}

static void op_submit(struct fuzz_in *in)
{
	struct diginet_cmd c;
	const uint8_t *p;
	unsigned before = g_s.queued;

	op_begin();
	memset(&c, 0, sizeof c);
	c.key = SPEC_KEY(fuzz_u8(in) % 9 + 1, fuzz_u8(in));
	c.display = fuzz_u8(in) & 1;
	if (g_raw) {
		c.len = (uint8_t)fuzz_take(in, fuzz_u16(in) % (SPEC_CMD_MAX + 1), &p);
		memcpy(c.bytes, p, c.len);
		int rc = diginet_session_submit(&g_s, &c);
		check_refusal_submit(&c, rc, before);
		settle(0);
		return;
	}
	unsigned serial = g_ncmd;
	memset(&g_cmd[serial], 0, sizeof g_cmd[serial]);
	c.len = (uint8_t)(fuzz_u8(in) % 22 + 3);
	c.bytes[0] = TAG;
	c.bytes[1] = serial & 0x7f;
	c.bytes[2] = serial >> 7 & 0x7f;
	size_t n = fuzz_take(in, c.len - 3u, &p);
	memcpy(c.bytes + 3, p, n);

	/* what the queue owes: the place of a pending command with this key, or the end */
	int sys = spec_system_at(c.bytes, c.len) >= 0;
	int at = -1;
	if (coalescable(c.key))
		for (unsigned i = 0; i < g_nq && at < 0; i++)
			if (g_cmd[g_q[i]].key == c.key)
				at = (int)i;
	int want = sys ? SPEC_E_REFUSED : at < 0 && g_nq == QUEUE_MAX ? SPEC_E_SPACE : SPEC_OK;
	int rc = diginet_session_submit(&g_s, &c);
	check_refusal_submit(&c, rc, before);
	if (!sys)
		check_latest_submit(rc, want);
	if (want == SPEC_OK) {
		g_cmd[serial].st = PENDING;
		g_cmd[serial].key = c.key;
		g_cmd[serial].display = c.display;
		g_cmd[serial].len = c.len;
		memcpy(g_cmd[serial].bytes, c.bytes, c.len);
		if (at >= 0) {
			g_cmd[g_q[at]].st = REPLACED;
			g_q[at] = serial;
		} else {
			g_q[g_nq++] = serial;
		}
	}
	g_ncmd++;
	settle(0);
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	static const uint64_t SCALE[4] = { 1, 1000, 100000, 1000000 };
	struct diginet_io io = { NULL, io_send, io_recv, io_now };
	const uint8_t *p;

	if (size >= FUZZ_INPUT_MAX)
		return 0;
	struct fuzz_in in = fuzz_in(data, size);
	uint8_t flags = fuzz_u8(&in);
	diginet_session_config_default(&g_cfg);
	memcpy(g_cfg.host_mac, HOST, SPEC_MAC);
	g_cfg.auto_wake = flags & 1;
	g_cfg.sum_mode = flags & 2 ? DIGINET_SUM_ZERO : DIGINET_SUM_BODY;
	g_cfg.desk_mac_set = flags >> 2 & 1;
	memcpy(g_cfg.desk_mac, DESK, SPEC_MAC);
	g_cfg.max_retries = fuzz_u8(&in) % 8;
	g_cfg.ack_timeout_ms = 1u + fuzz_u8(&in);
	g_cfg.keepalive_ms = 1u + fuzz_u16(&in);
	g_cfg.backoff_ms = fuzz_u8(&in);
	g_cfg.offline_ms = 1u + fuzz_u16(&in);
	g_cfg.wake_timeout_ms = 1u + fuzz_u16(&in);
	g_cfg.display_gap_us = fuzz_u16(&in);
	g_cfg.max_cmds = 1u + fuzz_u8(&in) % 255;
	g_cfg.max_body = SPEC_CMD_MAX + fuzz_u16(&in) % (SPEC_MAX_BODY - SPEC_CMD_MAX + 1);

	g_raw = flags >> 3 & 1;
	g_now = 1000000;
	g_fail_next = 0;
	g_last_counter = 0;
	memset(&M, 0, sizeof M);
	M.desk_known = g_cfg.desk_mac_set;
	memcpy(M.desk, DESK, SPEC_MAC);
	g_ncmd = g_nq = 0;
	g_rx = NULL;
	/* Every config made above is one the session takes: a count that fits the header's byte
	 * and a body that holds the longest command and fits a frame.
	 * contract: protocol/diginet.ksy header `num_commands` (u1); fuzz/spec.h SPEC_MAX_BODY,
	 * SPEC_CMD_MAX
	 * mutant: transport/src/diginet_session.c:62 `cfg->max_cmds > 255` -> `cfg->max_cmds > 254`
	 * input: split-system */
	if (diginet_session_init(&g_s, &g_cfg, &io, notice, NULL) != SPEC_OK)
		abort();

	for (int ops = 0; ops < OPS_MAX && in.n; ops++) {
		size_t n;
		switch (fuzz_u8(&in) % 9) {
		case 0:
			n = fuzz_record(&in, &p);
			receive(p, n, 0, 0);
			break;
		case 1:
			op_frame(&in);
			break;
		case 2:
			op_announce(&in);
			break;
		case 3: {
			uint64_t scale = SCALE[fuzz_u8(&in) % 4];
			op_begin();
			g_now += scale * fuzz_u16(&in);
			m_tick();
			diginet_session_tick(&g_s, g_now);
			settle(1);
			break;
		}
		case 4:
			op_submit(&in);
			break;
		case 5: {
			op_begin();
			int want = m_wake();
			check_state_wake_code(diginet_session_wake(&g_s, g_now), want);
			settle(0);
			break;
		}
		case 6:
			op_begin();
			m_close();
			diginet_session_close(&g_s, g_now);
			settle(0);
			break;
		case 7:
			g_fail_next = 1;
			break;
		default: {
			unsigned pf = fuzz_u8(&in);
			n = fuzz_record(&in, &p);
			receive(p, n, 1, pf);
			break;
		}
		}
	}
	return 0;
}
