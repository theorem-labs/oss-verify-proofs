// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>

/* libFuzzer harness: THE INTERFACE ALIAS (src/reac_link_alias.c) AND THE SERVED MARK
 * (src/reac_served_mark.c): the RTM_GETLINK reply the daemon reads a netdev's alias and
 * link kind from, the RTM_NEWLINK it writes an alias with, and the policy that marks the
 * interfaces a segment comes up on and takes the marks away at exit.
 *
 * Input:  operations, at most OPS_MAX, each [op] (mod 6):
 *           0 read     [name][kind cap][alias cap] then the kernel
 *           1 write    [name][alias] then the kernel
 *           2 mark     [name] then the kernel
 *           3 unmark   the kernel
 *           4 decide   [kind][alias]
 *           5 refused  [which]: a mark with no marks or no name
 *         the kernel: [flags: bit 0 socket() fails, bit 1 send() fails] [errno byte]
 *           [errno byte: recv's once the replies end] [chunks, mod 4] each [mode]:
 *           mode & 1 the input's own bytes, else [messages, mod 6] by msg_build;
 *         a name: [sel] below 64 "nl<sel>", the index sel + 2, with no index when
 *           sel % 16 is 15; 64 and up a name of the table `odd`; 255 a NULL name;
 *         a text: [sel] a text of the table `texts`, or with sel & 0x80 [u16 len % 320]
 *           and that many of the input's bytes, cut at a NUL.
 *
 * The expectations come from the bytes the fake kernel hands out, walked by the netlink
 * grammar of fuzz/netlink.h: the first RTM_NEWLINK of the reply answers 0, its
 * IFLA_IFALIAS the alias and the IFLA_INFO_KIND inside its IFLA_LINKINFO the kind, each
 * the last one there, cut at its NUL and to the buffer; an NLMSG_ERROR answers its code
 * (src/reac_link_alias.h:15-24). And from the marking policy of src/reac_served_mark.h:23-28.
 *
 * Properties, each an abort():
 *   - every socket opened is closed, and no other descriptor is used;
 *   - each operation sends exactly the requests it owes, byte for byte;
 *   - a read that cannot be made never opens a socket;
 *   - a read answers the reply's code, and on 0 the reply's kind and alias;
 *   - the kind and alias written never pass the buffers and always end in a NUL;
 *   - a write answers the reply's code, and refuses an alias too long for the kernel;
 *   - the verdict on an interface follows its alias, then its kind;
 *   - a mark answers its verdict, or the error that stopped it;
 *   - and the marks kept are exactly the interfaces this daemon marked (or found marked
 *     by a run of its own), until the unmark clears them. */
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "reac_link_alias.h"
#include "reac_served_mark.h"

#include "fuzz.h"
#include "netlink.h"

/* contract: linux/rtnetlink.h (RTM_NEWLINK 16, RTM_GETLINK 18; struct ifinfomsg: family,
 * pad, u16 type, int index, u32 flags, u32 change: 16 bytes, index at 4) and
 * linux/netlink.h (NLM_F_REQUEST 1, NLM_F_ACK 4) */
#define RTM_NEWLINK_  16
#define RTM_GETLINK_  18
#define IFI_LEN       16
#define F_REQUEST     0x1
#define F_ACK         0x4
/* contract: linux/if_link.h (IFLA_IFNAME 3, IFLA_LINKINFO 18, IFLA_IFALIAS 20;
 * IFLA_INFO_KIND 1) and linux/if.h (IFALIASZ 256) */
#define IFLA_IFNAME_   3
#define IFLA_LINKINFO_ 18
#define IFLA_IFALIAS_  20
#define INFO_KIND      1
#define ALIAS_MAX      256
/* contract: packaging/reac-pw-nm-unmanaged.sh:15 (the alias this daemon writes) and :66
 * (every alias starting `reac-pw:` is this daemon's mark); src/reac_served_mark.h:23-27
 * (a VLAN the host made, link kind `vlan`, is left alone) and :36 (32 marks kept) */
#define SERVED        "reac-pw:served"
#define PREFIX        "reac-pw:"
#define MARKS_MAX     32

#define OPS_MAX 48
/* An answer the kernel cannot give: a positive error code. The reader then answers
 * something other than 0, and the harness claims no more (netlink(7): an error is a
 * negative errno, 0 an ACK). */
#define RC_FAILS 1000000

/* ---- the interfaces, the texts -------------------------------------------------------- */

static char g_names[64][8];
static const char *const odd[] = { "", "enp131s0.33", "eth0", "wlan0", "veth-box", "gone0" };

static void interfaces(void)
{
	g_nl.n_if = 0;
	for (int k = 0; k < 64; k++) {
		snprintf(g_names[k], sizeof g_names[k], "nl%d", k);
		if (k % 16 == 15)
			continue;
		g_nl.if_name[g_nl.n_if] = g_names[k];
		g_nl.if_index[g_nl.n_if++] = (unsigned)k + 2;
	}
	for (int k = 1; k < 5; k++) {
		g_nl.if_name[g_nl.n_if] = odd[k];
		g_nl.if_index[g_nl.n_if++] = 100u + (unsigned)k;
	}
}

static const char *name_of(struct fuzz_in *in)
{
	uint8_t s = fuzz_u8(in);
	if (s == 255)
		return NULL;
	if (s < 64)
		return g_names[s];
	return odd[s % (sizeof odd / sizeof odd[0])];
}

static unsigned index_of(const char *name)
{
	for (int i = 0; i < g_nl.n_if; i++)
		if (strcmp(g_nl.if_name[i], name) == 0)
			return g_nl.if_index[i];
	return 0;
}

static const char *const texts[] = {
	"", SERVED, "reac-pw:minted", "host-alias", PREFIX, "reac-pw:served2", "reac-pw",
	"vlan", "veth", "vlanx", "vla",
};

/* A text from the table or the input; *own is the copy to free, or NULL. */
static const char *text_of(struct fuzz_in *in, char **own)
{
	uint8_t s = fuzz_u8(in);
	*own = NULL;
	if (!(s & 0x80))
		return texts[s % (sizeof texts / sizeof texts[0])];
	const uint8_t *p;
	size_t n = fuzz_take(in, fuzz_u16(in) % 320u, &p);
	*own = fuzz_str(p, n);
	return *own;
}

/* ---- A RUN WRITES NOTHING OF ITS OWN -------------------------------------------------- */

/* The marking policy reports a mark it could not read or write, a VLAN the host made, and
 * an interface carrying the host's own alias (src/reac_served_mark.c:55-58, 66-70, 82-83,
 * 86-88). Those lines are the daemon's and they stay as they are; the harness must still
 * write no byte of its own, because what a fuzz target writes is no part of what it
 * checks, and the output of a run belongs to its driver. So the harness points the
 * policy's stream (src/reac_served_mark.h:59-63) at a buffer in memory. The policy decides
 * and formats exactly as it does in the daemon, and what the program writes — the driver's
 * output, and the name each abort() prints — is unchanged.
 * The buffer is fixed, and the run rewinds it: a message past its end is cut there, and
 * nothing grows from one input to the next. */
static char g_said[4096];
static FILE *g_sink;

static int mark_quietly(struct reac_served_marks *m, const char *ifname)
{
	if (!g_sink) {
		g_sink = fmemopen(g_said, sizeof g_said, "w");
		/* not a property: the harness's own allocation failed */
		if (!g_sink)
			abort();
		reac_served_say_to(g_sink);
	}
	rewind(g_sink);
	return reac_served_mark(m, ifname);
}

/* ---- the replies the input spells ----------------------------------------------------- */

/* An attribute holding `s`, with its NUL unless `bare`. */
static void attr_text(struct nl_w *w, uint16_t type, const char *s, int bare)
{
	nl_attr_put(w, type, s, strlen(s) + !bare);
}

static void msg_build(struct fuzz_in *in, struct nl_w *w)
{
	static char long_alias[301];
	uint8_t kind = fuzz_u8(in);
	switch (kind % 8) {
	case 0: case 7: {
		size_t at = nl_begin(w, RTM_NEWLINK_);
		uint8_t ifi[IFI_LEN] = { 0 };
		nl_put(w, ifi, sizeof ifi);
		int nattr = fuzz_u8(in) % 5;
		for (int i = 0; i < nattr; i++) {
			uint8_t a = fuzz_u8(in);
			const char *t = texts[(a >> 3) % (sizeof texts / sizeof texts[0])];
			switch (a % 6) {
			case 0:
				attr_text(w, IFLA_IFALIAS_, t, a & 0x80);
				break;
			case 1:
				memset(long_alias, 'a', 300);
				attr_text(w, IFLA_IFALIAS_, long_alias, 0);
				break;
			case 2: case 3: {
				size_t n = nl_nest(w, IFLA_LINKINFO_);
				if (a % 6 == 3)
					nl_attr_put(w, 2, "data", 4);   /* IFLA_INFO_DATA, not read */
				attr_text(w, INFO_KIND, t, a & 0x80);
				nl_nest_end(w, n);
				break;
			}
			case 4:
				attr_text(w, IFLA_IFNAME_, "x", 0);
				break;
			default:
				nl_attr_put(w, 99, "abcd", 4);
				break;
			}
		}
		nl_end(w, at);
		/* 7: the message's length is not padded, and the chunk may end there */
		if (kind % 8 == 7 && w->n == NL_ALIGN(w->n)) {
			nl_put(w, "", 1);
			nl_end(w, at);
		} else {
			nl_pad(w);
		}
		break;
	}
	case 1:
		nl_error(w, 0, -1);
		break;
	case 2: {
		static const int32_t codes[] = { -EPERM, -ENODEV, -EOPNOTSUPP, 5 };
		uint8_t c = fuzz_u8(in);
		nl_error(w, codes[c % 4], (c & 0x80) ? (c >> 4 & 7) : -1);
		break;
	}
	case 3: {
		size_t at = nl_begin(w, NL_DONE);
		nl_put32(w, 0);
		nl_end(w, at);
		break;
	}
	case 4: {
		size_t at = nl_begin(w, 20);   /* RTM_NEWADDR */
		nl_put(w, "01234567", 8);
		nl_end(w, at);
		break;
	}
	case 5: {
		/* a link message too short for its ifinfomsg */
		size_t at = nl_begin(w, RTM_NEWLINK_);
		nl_put32(w, 0);
		nl_end(w, at);
		break;
	}
	default:
		nl_put32(w, 8);
		nl_put32(w, NL_DONE);
		break;
	}
}

/* The kernel of one operation: the failures and the replies it hands out. */
static void kernel(struct fuzz_in *in)
{
	uint8_t flags = fuzz_u8(in);
	int e = nl_errno(fuzz_u8(in));
	g_nl.end_errno = nl_errno(fuzz_u8(in));
	g_nl.socket_errno = (flags & 1) ? e : 0;
	g_nl.send_errno = (flags & 2) ? e : 0;
	/* the replies of this operation, after every chunk an earlier one left */
	g_nl.n_chunks = g_nl.next = 0;
	int n = fuzz_u8(in) % 4;
	for (int c = 0; c < n; c++) {
		uint8_t mode = fuzz_u8(in);
		if (mode & 1) {
			nl_queue_raw(in);
			continue;
		}
		struct nl_w w = { .n = 0 };
		int m = fuzz_u8(in) % 6;
		for (int k = 0; k < m && !w.full; k++)
			msg_build(in, &w);
		if (w.n == 0)
			nl_put32(&w, 0);
		nl_queue(&w);
	}
}

/* ---- what the readers owe -------------------------------------------------------------- */

/* The kernel as the model sees it: the failures still to come and the next chunk. */
struct model {
	int socket_errno, send_errno, next;
	/* the requests the operation owes, in order */
	uint8_t req[NL_SENT_MAX][NL_SENT_LEN];
	size_t req_len[NL_SENT_MAX];
	int n_req;
	/* the marks */
	char mark[MARKS_MAX][16];
	int n_mark;
};

static void owe(struct model *m, const uint8_t *r, size_t len)
{
	if (m->n_req < NL_SENT_MAX) {
		memcpy(m->req[m->n_req], r, len < NL_SENT_LEN ? len : NL_SENT_LEN);
		m->req_len[m->n_req++] = len;
	}
}

static size_t req_head(uint8_t *r, uint32_t len, uint16_t type, uint16_t flags, unsigned idx)
{
	uint32_t seq = 1;
	int32_t i = (int32_t)idx;
	memset(r, 0, len);
	memcpy(r, &len, 4);
	memcpy(r + 4, &type, 2);
	memcpy(r + 6, &flags, 2);
	memcpy(r + 8, &seq, 4);
	memcpy(r + NL_HDR + 4, &i, 4);
	return len;
}

/* `n` bytes of an attribute's data, cut at its NUL, into a buffer of `cap`. */
static void take_text(const uint8_t *d, size_t n, char *out, size_t cap)
{
	if (!out || !cap)
		return;
	size_t k = 0;
	while (k < n && d[k])
		k++;
	if (k > cap - 1)
		k = cap - 1;
	memcpy(out, d, k);
	out[k] = '\0';
}

/* One request and its reply: the code, and the kind and alias of the first link
 * message. */
static int talk(struct model *m, const uint8_t *r, size_t len, char *kind, size_t kind_n,
                char *alias, size_t alias_n)
{
	if (m->socket_errno) {
		int e = m->socket_errno;
		m->socket_errno = 0;
		return -e;
	}
	if (m->send_errno) {
		int e = m->send_errno;
		m->send_errno = 0;
		return -e;
	}
	owe(m, r, len);
	for (;;) {
		if (m->next >= g_nl.n_chunks)
			return -g_nl.end_errno;
		int c = m->next++;
		const uint8_t *b = g_nl.chunk[c];
		long off = 0, left = (long)g_nl.chunk_len[c];
		uint16_t type, t, l, ti, li;
		uint32_t ml;
		while ((ml = nl_msg(b, &off, &left, &type))) {
			if (type == NL_ERROR) {
				if (ml < NL_HDR + NL_ERR_BODY)
					return -EIO;
				int32_t e = (int32_t)nl_rd32(b + off + NL_HDR);
				return e > 0 ? RC_FAILS : e;
			}
			if (type != RTM_NEWLINK_) {
				nl_msg_next(ml, &off, &left);
				continue;
			}
			long a = off + NL_HDR + IFI_LEN, al = (long)ml - NL_HDR - IFI_LEN;
			while ((l = nl_attr(b, &a, &al, &t))) {
				if (t == IFLA_IFALIAS_) {
					take_text(b + a + RTA_HDR, l - RTA_HDR, alias, alias_n);
				} else if (t == IFLA_LINKINFO_) {
					long i = a + RTA_HDR, il = l - RTA_HDR;
					while ((li = nl_attr(b, &i, &il, &ti))) {
						if (ti == INFO_KIND)
							take_text(b + i + RTA_HDR, li - RTA_HDR, kind, kind_n);
						nl_attr_next(li, &i, &il);
					}
				}
				nl_attr_next(l, &a, &al);
			}
			return 0;
		}
	}
}

static int model_read(struct model *m, const char *name, char *kind, size_t kind_n,
                      char *alias, size_t alias_n)
{
	if (kind && kind_n)
		kind[0] = '\0';
	if (alias && alias_n)
		alias[0] = '\0';
	if (!name || !name[0])
		return -EINVAL;
	unsigned idx = index_of(name);
	if (!idx)
		return -ENODEV;
	uint8_t r[NL_HDR + IFI_LEN];
	req_head(r, sizeof r, RTM_GETLINK_, F_REQUEST, idx);
	return talk(m, r, sizeof r, kind, kind_n, alias, alias_n);
}

static int model_write(struct model *m, const char *name, const char *alias)
{
	if (!name || !name[0] || !alias)
		return -EINVAL;
	size_t alen = strlen(alias);
	if (alen >= ALIAS_MAX)
		return -ENAMETOOLONG;
	unsigned idx = index_of(name);
	if (!idx)
		return -ENODEV;
	uint8_t r[NL_SENT_LEN];
	uint32_t len = NL_HDR + IFI_LEN + NL_ALIGN(RTA_HDR + alen);
	req_head(r, len, RTM_NEWLINK_, F_REQUEST | F_ACK, idx);
	uint16_t al = (uint16_t)(RTA_HDR + alen), at = IFLA_IFALIAS_;
	memcpy(r + NL_HDR + IFI_LEN, &al, 2);
	memcpy(r + NL_HDR + IFI_LEN + 2, &at, 2);
	memcpy(r + NL_HDR + IFI_LEN + RTA_HDR, alias, alen);
	return talk(m, r, len, NULL, 0, NULL, 0);
}

static enum reac_served_verdict model_decide(const char *kind, const char *alias)
{
	if (alias && alias[0])
		return strncmp(alias, PREFIX, strlen(PREFIX)) == 0 ? REAC_SERVED_OURS
		                                                   : REAC_SERVED_LEAVE_HOST;
	if (kind && strcmp(kind, "vlan") == 0)
		return REAC_SERVED_LEAVE_VLAN;
	return REAC_SERVED_MARK;
}

static void model_remember(struct model *m, const char *name)
{
	for (int i = 0; i < m->n_mark; i++)
		if (strcmp(m->mark[i], name) == 0)
			return;
	if (m->n_mark < MARKS_MAX)
		snprintf(m->mark[m->n_mark++], sizeof m->mark[0], "%s", name);
}

static int model_mark(struct model *m, const char *name)
{
	if (!name || !name[0])
		return -EINVAL;
	char kind[32], alias[ALIAS_MAX];
	int rc = model_read(m, name, kind, sizeof kind, alias, sizeof alias);
	if (rc != 0)
		return rc;
	enum reac_served_verdict v = model_decide(kind, alias);
	if (v == REAC_SERVED_MARK) {
		rc = model_write(m, name, SERVED);
		if (rc != 0)
			return rc;
		model_remember(m, name);
	} else if (v == REAC_SERVED_OURS && strcmp(alias, SERVED) == 0) {
		model_remember(m, name);
	}
	return (int)v;
}

static void model_unmark(struct model *m)
{
	for (int i = 0; i < m->n_mark; i++) {
		char alias[ALIAS_MAX];
		if (model_read(m, m->mark[i], NULL, 0, alias, sizeof alias) != 0)
			continue;
		if (strcmp(alias, SERVED) != 0)
			continue;
		model_write(m, m->mark[i], "");
	}
	m->n_mark = 0;
}

/* The answer owed, against the answer given: RC_FAILS asks only for a failure. */
static int same_rc(int got, int want)
{
	return want == RC_FAILS ? got != 0 : got == want;
}

/* ---- the checks ------------------------------------------------------------------------ */

static int requests_are(const struct nl_kernel *k, const struct model *m);
static int text_within(const char *buf, size_t cap);
static int marks_are(const struct reac_served_marks *got, const struct model *m);

static FUZZ_NOINLINE void check_socket(const struct nl_kernel *k)
{
	/* Every socket the reader opens it closes before it returns, and it sends, reads
	 * and closes only that one.
	 * contract: src/reac_link_alias.c:4-5 (one request, one answer)
	 * mutant: src/reac_link_alias.c:91 `close(fd);` -> ``
	 * input: read-served */
	if (k->open || k->opened != k->closed || k->misuse)
		abort();
}

static FUZZ_NOINLINE void check_requests(const struct nl_kernel *k, const struct model *m)
{
	/* An operation sends exactly the requests it owes, in order and byte for byte: a
	 * read an RTM_GETLINK of the interface's index, a write an RTM_NEWLINK asking for an
	 * ACK with one IFLA_IFALIAS holding the alias, nothing for a mark the reply stopped,
	 * and at exit a removal only of the marks still this daemon's.
	 * contract: src/reac_link_alias.h:15-24, src/reac_served_mark.h:54-57, 65-67
	 * mutant: src/reac_link_alias.c:138 `NLM_F_REQUEST | NLM_F_ACK` -> `NLM_F_REQUEST`
	 * input: mark-plain-nic
	 * mutant: src/reac_link_alias.c:147 `RTA_ALIGN(a->rta_len)` -> `a->rta_len`
	 * input: mark-plain-nic
	 * mutant: src/reac_link_alias.c:117 `(int)idx` -> `(int)idx + 1`
	 * input: read-served
	 * mutant: src/reac_served_mark.c:102 `strcmp(alias, REAC_SERVED_ALIAS) != 0` -> `0`
	 * input: unmark-after-host-renamed
	 * mutant: src/reac_served_mark.c:64 `REAC_SERVED_ALIAS` -> `REAC_ALIAS_PREFIX`
	 * input: mark-plain-nic */
	if (!requests_are(k, m))
		abort();
}

static FUZZ_NOINLINE void check_refused(int opened_before, int opened)
{
	/* A read or a write that cannot be made, a NULL or empty name, an alias too long for
	 * the kernel or an interface with no index, opens no socket.
	 * contract: src/reac_link_alias.h:17, 23-24 (-errno, -ENODEV for no such interface)
	 * mutant: src/reac_link_alias.c:129 `if (!idx)` -> `if (0)`
	 * input: write-no-index
	 * mutant: src/reac_link_alias.c:126 `alen >= IFALIASZ` -> `alen > IFALIASZ`
	 * input: write-alias-256 */
	if (opened != opened_before)
		abort();
}

static FUZZ_NOINLINE void check_read(int rc, int want, const char *kind, const char *want_kind,
                                     const char *alias, const char *want_alias)
{
	/* A read answers the reply's code, -EIO for an error too short to hold one; on 0 the
	 * kind is the INFO_KIND inside the reply's IFLA_LINKINFO and the alias its
	 * IFLA_IFALIAS, each the last one, cut at its NUL and to the buffer, and empty when
	 * the reply has none.
	 * contract: src/reac_link_alias.h:15-19
	 * mutant: src/reac_link_alias.c:82 `IFLA_INFO_KIND` -> `IFLA_INFO_DATA`
	 * input: read-vlan-with-data
	 * mutant: src/reac_link_alias.c:77 `copy_attr(a, alias, alias_n);` -> `copy_attr(a, kind, kind_n);`
	 * input: read-served
	 * mutant: src/reac_link_alias.c:66 `nh->nlmsg_len < NLMSG_LENGTH(sizeof *err)` -> `0`
	 * input: read-error-short
	 * mutant: src/reac_link_alias.c:61 `NLMSG_OK(nh, n)` -> `NLMSG_OK(nh, (unsigned)n)`
	 * input: read-unpadded-last
	 * mutant: src/reac_link_alias.c:70 `!= RTM_NEWLINK` -> `== NLMSG_DONE`
	 * input: read-after-other */
	if (!same_rc(rc, want) || (rc == 0 && (strcmp(kind, want_kind) != 0 ||
	                                       strcmp(alias, want_alias) != 0)))
		abort();
}

static FUZZ_NOINLINE void check_bounds(const char *buf, size_t cap)
{
	/* A text written into a buffer of `cap` bytes ends in a NUL inside them, and the byte
	 * after them is as the harness left it.
	 * contract: src/reac_link_alias.h:15-17 (into `kind` and `alias`, of their sizes)
	 * mutant: src/reac_link_alias.c:32 `k >= n` -> `k > n`
	 * input: read-alias-fills-buffer
	 * mutant: src/reac_link_alias.c:101 `alias[0] = '\0';` -> ``
	 * input: read-plain-nic */
	if (!text_within(buf, cap))
		abort();
}

static FUZZ_NOINLINE void check_write(int rc, int want)
{
	/* A write answers the reply's code: 0 for the ACK, the error otherwise, and
	 * -ENAMETOOLONG for an alias the kernel cannot hold, IFALIASZ bytes or more.
	 * contract: src/reac_link_alias.h:21-24
	 * mutant: src/reac_link_alias.c:67 `: err->error;` -> `: 0;`
	 * input: write-refused */
	if (!same_rc(rc, want))
		abort();
}

static FUZZ_NOINLINE void check_verdict(enum reac_served_verdict got,
                                        enum reac_served_verdict want)
{
	/* An alias the host set is left alone and one starting `reac-pw:` is this daemon's;
	 * with no alias a VLAN the host made is left alone and anything else is marked.
	 * contract: src/reac_served_mark.h:23-28, 45-46
	 * mutant: src/reac_served_mark.c:29 `sizeof REAC_ALIAS_PREFIX - 1` -> `sizeof REAC_ALIAS_PREFIX`
	 * input: decide-all
	 * mutant: src/reac_served_mark.c:33 `strcmp(kind, "vlan") == 0` -> `strncmp(kind, "vlan", 3) == 0`
	 * input: decide-all
	 * mutant: src/reac_served_mark.c:28 `alias && alias[0]` -> `alias`
	 * input: decide-all */
	if (got != want)
		abort();
}

static FUZZ_NOINLINE void check_mark(int rc, int want)
{
	/* A mark answers its verdict, or the error of the read or the write that stopped it,
	 * and -EINVAL with no marks or no name.
	 * contract: src/reac_served_mark.h:54-57
	 * mutant: src/reac_served_mark.c:71 `return rc;` -> `break;`
	 * input: mark-write-refused
	 * mutant: src/reac_served_mark.c:91 `return (int)v;` -> `return 0;`
	 * input: mark-minted-vlan */
	if (!same_rc(rc, want))
		abort();
}

static FUZZ_NOINLINE void check_marks(const struct reac_served_marks *got, const struct model *m)
{
	/* The marks kept are the interfaces this daemon marked, and those a run of its own
	 * left marked, each once, at most 32; the unmark clears them all.
	 * contract: src/reac_served_mark.h:48-52, 65-67
	 * mutant: src/reac_served_mark.c:78 `strcmp(alias, REAC_SERVED_ALIAS) == 0` -> `1`
	 * input: mark-minted-vlan
	 * mutant: src/reac_served_mark.c:41 `strcmp(m->name[i], ifname) == 0` -> `0`
	 * input: mark-twice
	 * mutant: src/reac_served_mark.c:106 `memset(m, 0, sizeof *m);` -> ``
	 * input: unmark-after-host-renamed
	 * mutant: src/reac_served_mark.c:43 `m->n >= REAC_SERVED_MAX` -> `m->n > REAC_SERVED_MAX`
	 * input: mark-forty */
	if (!marks_are(got, m))
		abort();
}

/* ---- what the checks compare ----------------------------------------------------------- */

static int requests_are(const struct nl_kernel *k, const struct model *m)
{
	if (k->n_sent != m->n_req)
		return 0;
	for (int i = 0; i < m->n_req; i++)
		if (k->sent_len[i] != m->req_len[i] ||
		    memcmp(k->sent[i], m->req[i], m->req_len[i] < NL_SENT_LEN ? m->req_len[i]
		                                                             : NL_SENT_LEN) != 0)
			return 0;
	return 1;
}

static int text_within(const char *buf, size_t cap)
{
	return memchr(buf, 0, cap) != NULL && (uint8_t)buf[cap] == 0x5a;
}

static int marks_are(const struct reac_served_marks *got, const struct model *m)
{
	if (got->n != m->n_mark)
		return 0;
	for (int i = 0; i < m->n_mark; i++)
		if (strcmp(got->name[i], m->mark[i]) != 0)
			return 0;
	return 1;
}

/* A buffer of `cap` bytes the reader may write, and a guard byte after it; NULL for 0. */
static char *text_buf(size_t cap)
{
	if (!cap)
		return NULL;
	char *b = malloc(cap + 1);
	/* not a property: the harness's own allocation failed */
	if (!b)
		abort();
	memset(b, 0x5a, cap + 1);
	return b;
}

/* The model starts each operation from the kernel's own failures and its first chunk. */
static void model_begin(struct model *m)
{
	m->socket_errno = g_nl.socket_errno;
	m->send_errno = g_nl.send_errno;
	m->next = 0;
	m->n_req = 0;
	g_nl.n_sent = 0;
}

static void op_read(struct fuzz_in *in, struct model *m)
{
	const char *name = name_of(in);
	size_t kc = fuzz_u8(in) % 40, ac = fuzz_u8(in) % 40;
	kernel(in);
	model_begin(m);
	char *kind = text_buf(kc), *alias = text_buf(ac);
	char wk[40] = { 0 }, wa[40] = { 0 };
	int opened = g_nl.opened;
	int want = model_read(m, name, kc ? wk : NULL, kc, ac ? wa : NULL, ac);
	int rc = reac_link_alias_read(name, kind, kc, alias, ac);
	check_socket(&g_nl);
	/* refused by what it was asked, not by its answer: a reply can say -ENODEV too */
	if (!name || !name[0] || !index_of(name))
		check_refused(opened, g_nl.opened);
	if (kind)
		check_bounds(kind, kc);
	if (alias)
		check_bounds(alias, ac);
	check_read(rc, want, kind ? kind : wk, wk, alias ? alias : wa, wa);
	check_requests(&g_nl, m);
	free(kind);
	free(alias);
}

static void op_write(struct fuzz_in *in, struct model *m)
{
	const char *name = name_of(in);
	char *own;
	const char *alias = text_of(in, &own);
	kernel(in);
	model_begin(m);
	int opened = g_nl.opened;
	int want = model_write(m, name, alias);
	int rc = reac_link_alias_write(name, alias);
	check_socket(&g_nl);
	if (!name || !name[0] || strlen(alias) >= ALIAS_MAX || !index_of(name))
		check_refused(opened, g_nl.opened);
	check_write(rc, want);
	check_requests(&g_nl, m);
	free(own);
}

static void op_mark(struct fuzz_in *in, struct model *m, struct reac_served_marks *marks)
{
	const char *name = name_of(in);
	kernel(in);
	model_begin(m);
	int want = model_mark(m, name);
	int rc = mark_quietly(marks, name);
	check_socket(&g_nl);
	check_mark(rc, want);
	check_marks(marks, m);
	check_requests(&g_nl, m);
}

static void op_unmark(struct fuzz_in *in, struct model *m, struct reac_served_marks *marks)
{
	kernel(in);
	model_begin(m);
	model_unmark(m);
	reac_served_unmark_all(marks);
	check_socket(&g_nl);
	check_marks(marks, m);
	check_requests(&g_nl, m);
}

static void op_decide(struct fuzz_in *in)
{
	char *ok, *oa;
	const char *kind = text_of(in, &ok);
	const char *alias = text_of(in, &oa);
	check_verdict(reac_served_decide(kind, alias), model_decide(kind, alias));
	free(ok);
	free(oa);
}

/* No marks, or no name: refused, and nothing asked of the kernel. */
static void op_refused(struct fuzz_in *in, struct model *m, struct reac_served_marks *marks)
{
	uint8_t w = fuzz_u8(in);
	model_begin(m);
	int rc = mark_quietly((w & 1) ? NULL : marks, (w & 2) ? "" : NULL);
	check_mark(rc, -EINVAL);
	check_requests(&g_nl, m);
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	if (size >= FUZZ_INPUT_MAX)
		return 0;
	struct fuzz_in in = fuzz_in(data, size);
	memset(&g_nl, 0, sizeof g_nl);
	interfaces();
	struct model *m = calloc(1, sizeof *m);
	struct reac_served_marks *marks = calloc(1, sizeof *marks);
	/* not a property: the harness's own allocation failed */
	if (!m || !marks)
		abort();

	for (int op = 0; op < OPS_MAX && in.n; op++) {
		switch (fuzz_u8(&in) % 6) {
		case 0: op_read(&in, m); break;
		case 1: op_write(&in, m); break;
		case 2: op_mark(&in, m, marks); break;
		case 3: op_unmark(&in, m, marks); break;
		case 4: op_decide(&in); break;
		default: op_refused(&in, m, marks); break;
		}
	}
	free(marks);
	free(m);
	return 0;
}
