// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>

/* THE KERNEL ON THE OTHER END OF AN rtnetlink SOCKET, AS THE INPUT SPELLS IT (fuzz_qdisc,
 * fuzz_link). The two readers of rtnetlink replies are compiled with socket(), send(),
 * recv(), close() and if_nametoindex() renamed to the functions below (fuzz/build.sh), so
 * the reply bytes a reader walks are bytes of the input, and every request it sends is
 * kept for the harness to read.
 *
 * The fake kernel hands out each queued reply chunk to one recv(), whole (no chunk is
 * longer than a reader's buffer), and once the queue is empty it answers recv() with -1
 * and the errno the input chose: a netlink socket never returns 0 and a blocking one
 * would wait, so an error is the only end the input can give a reader that wants more.
 *
 * The rest is the netlink grammar, written here from the uapi headers and not from the
 * readers: a message is a 16-byte header (u32 length counting the header, u16 type, u16
 * flags, u32 sequence, u32 port) and its payload, and the next message starts at the
 * length rounded up to 4; a walk takes a message while at least a header is left, its
 * length is at least a header, and no more than what is left. An attribute is a u16
 * length counting its 4-byte header, a u16 type and the data, walked the same way.
 * contract: linux/netlink.h (struct nlmsghdr; NLMSG_ALIGN, NLMSG_OK, NLMSG_NEXT, NLMSG_DONE 3,
 * NLMSG_ERROR 2; struct nlmsgerr: an int error, then the request's header) and
 * linux/rtnetlink.h (struct rtattr; RTA_ALIGN, RTA_OK, RTA_NEXT, RTA_PAYLOAD) */
#ifndef REACPW_FUZZ_NETLINK_H
#define REACPW_FUZZ_NETLINK_H

#include <errno.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <sys/types.h>

#include "fuzz.h"

#define NL_HDR        16
#define NL_ERR_BODY   20    /* struct nlmsgerr: int error + struct nlmsghdr */
#define NL_DONE       3
#define NL_ERROR      2
#define NL_ALIGN(n)   (((n) + 3u) & ~3u)
#define RTA_HDR       4

#define NL_FD         7     /* the descriptor the fake socket() hands out */
#define NL_CHUNKS     64
#define NL_CHUNK_MAX  4096
#define NL_SENT_MAX   16
#define NL_SENT_LEN   512

struct nl_kernel {
	/* the queue of reply chunks, in the order recv() hands them out */
	uint8_t chunk[NL_CHUNKS][NL_CHUNK_MAX];
	size_t chunk_len[NL_CHUNKS];
	int n_chunks;
	int next;            /* the chunk the next recv() hands out */
	int end_errno;       /* recv()'s errno once the queue is empty */
	int socket_errno;    /* when not 0, the next socket() fails with it, once */
	int send_errno;      /* when not 0, the next send() fails with it, once */
	/* what the readers did with the socket */
	int open;            /* sockets open now */
	int opened, closed;
	int misuse;          /* a call on a descriptor that is not the open socket */
	uint8_t sent[NL_SENT_MAX][NL_SENT_LEN];
	size_t sent_len[NL_SENT_MAX];
	int n_sent;
	/* the interfaces if_nametoindex() knows */
	const char *if_name[80];
	unsigned if_index[80];
	int n_if;
};

static struct nl_kernel g_nl;

int fuzz_socket(int domain, int type, int protocol)
{
	(void)domain;
	(void)type;
	(void)protocol;
	if (g_nl.socket_errno) {
		errno = g_nl.socket_errno;
		g_nl.socket_errno = 0;
		return -1;
	}
	if (g_nl.open)
		g_nl.misuse = 1;   /* the readers hold one socket at a time */
	g_nl.open = 1;
	g_nl.opened++;
	return NL_FD;
}

ssize_t fuzz_send(int fd, const void *buf, size_t len, int flags)
{
	(void)flags;
	if (fd != NL_FD || !g_nl.open)
		g_nl.misuse = 1;
	if (g_nl.send_errno) {
		errno = g_nl.send_errno;
		g_nl.send_errno = 0;
		return -1;
	}
	if (g_nl.n_sent < NL_SENT_MAX) {
		size_t n = len < NL_SENT_LEN ? len : NL_SENT_LEN;
		memcpy(g_nl.sent[g_nl.n_sent], buf, n);
		g_nl.sent_len[g_nl.n_sent++] = len;
	}
	return (ssize_t)len;
}

ssize_t fuzz_recv(int fd, void *buf, size_t len, int flags)
{
	(void)flags;
	if (fd != NL_FD || !g_nl.open)
		g_nl.misuse = 1;
	if (g_nl.next >= g_nl.n_chunks) {
		errno = g_nl.end_errno;
		return -1;
	}
	size_t n = g_nl.chunk_len[g_nl.next];
	if (n > len)
		n = len;
	memcpy(buf, g_nl.chunk[g_nl.next++], n);
	/* PAST THE REPLY, A MESSAGE IT DID NOT SEND. The rest of the reader's buffer holds,
	 * from the next 4-byte boundary on, whole NLMSG_ERROR messages of -ENOTRECOVERABLE:
	 * a reader that walks past the bytes recv() returned answers that error, every time,
	 * where stale bytes would make it answer anything. */
	uint8_t *b = buf;
	size_t o = NL_ALIGN(n) < len ? NL_ALIGN(n) : len;
	memset(b + n, 0, o - n);
	for (; o + NL_HDR + NL_ERR_BODY <= len; o += NL_HDR + NL_ERR_BODY) {
		uint32_t l = NL_HDR + NL_ERR_BODY;
		uint16_t t = NL_ERROR;
		int32_t e = -ENOTRECOVERABLE;
		memset(b + o, 0, l);
		memcpy(b + o, &l, 4);
		memcpy(b + o + 4, &t, 2);
		memcpy(b + o + NL_HDR, &e, 4);
	}
	return (ssize_t)n;
}

int fuzz_close(int fd)
{
	if (fd != NL_FD || !g_nl.open)
		g_nl.misuse = 1;
	g_nl.open = 0;
	g_nl.closed++;
	return 0;
}

unsigned fuzz_if_nametoindex(const char *name)
{
	for (int i = 0; i < g_nl.n_if; i++)
		if (strcmp(g_nl.if_name[i], name) == 0)
			return g_nl.if_index[i];
	return 0;
}

/* The errno a failing call takes, from the input. */
static inline int nl_errno(uint8_t b)
{
	static const int e[] = { ENOBUFS, EINTR, EAGAIN, EPERM, EMFILE, ECONNREFUSED };
	return e[b % (sizeof e / sizeof e[0])];
}

/* ---- reading the grammar ------------------------------------------------------------ */

static inline uint16_t nl_rd16(const uint8_t *p)
{
	uint16_t v;
	memcpy(&v, p, 2);
	return v;
}

static inline uint32_t nl_rd32(const uint8_t *p)
{
	uint32_t v;
	memcpy(&v, p, 4);
	return v;
}

/* The next message of a chunk: from *off, with *left bytes left (which may be below 0
 * after an unpadded message). Returns its length, or 0 when the walk ends. */
static inline uint32_t nl_msg(const uint8_t *c, long *off, long *left, uint16_t *type)
{
	if (*left < NL_HDR)
		return 0;
	uint32_t len = nl_rd32(c + *off);
	if (len < NL_HDR || len > (unsigned long)*left)
		return 0;
	*type = nl_rd16(c + *off + 4);
	return len;
}

static inline void nl_msg_next(uint32_t len, long *off, long *left)
{
	*off += NL_ALIGN(len);
	*left -= (long)NL_ALIGN(len);
}

/* The next attribute of a region: at *off, *left bytes left. Returns its length, or 0
 * when the walk ends. */
static inline uint16_t nl_attr(const uint8_t *c, long *off, long *left, uint16_t *type)
{
	if (*left < RTA_HDR)
		return 0;
	uint16_t len = nl_rd16(c + *off);
	if (len < RTA_HDR || len > *left)
		return 0;
	*type = nl_rd16(c + *off + 2);
	return len;
}

static inline void nl_attr_next(uint16_t len, long *off, long *left)
{
	*off += NL_ALIGN(len);
	*left -= (long)NL_ALIGN(len);
}

/* ---- writing replies ---------------------------------------------------------------- */

struct nl_w {
	uint8_t b[NL_CHUNK_MAX];
	size_t n;
	int full;
};

static inline size_t nl_put(struct nl_w *w, const void *p, size_t n)
{
	if (w->n + n > sizeof w->b) {
		w->full = 1;
		return 0;
	}
	if (n)
		memcpy(w->b + w->n, p, n);
	w->n += n;
	return n;
}

static inline void nl_put16(struct nl_w *w, uint16_t v)
{
	nl_put(w, &v, 2);
}

static inline void nl_put32(struct nl_w *w, uint32_t v)
{
	nl_put(w, &v, 4);
}

static inline void nl_pad(struct nl_w *w)
{
	static const uint8_t z[4];
	nl_put(w, z, NL_ALIGN(w->n) - w->n);
}

static inline void nl_set16(struct nl_w *w, size_t at, uint16_t v)
{
	if (at + 2 <= w->n)
		memcpy(w->b + at, &v, 2);
}

static inline void nl_set32(struct nl_w *w, size_t at, uint32_t v)
{
	if (at + 4 <= w->n)
		memcpy(w->b + at, &v, 4);
}

/* A message header whose length is filled by nl_end. */
static inline size_t nl_begin(struct nl_w *w, uint16_t type)
{
	size_t at = w->n;
	nl_put32(w, 0);
	nl_put16(w, type);
	nl_put16(w, 0);
	nl_put32(w, 1);
	nl_put32(w, 0);
	return at;
}

static inline void nl_end(struct nl_w *w, size_t at)
{
	nl_set32(w, at, (uint32_t)(w->n - at));
}

/* An attribute of `n` data bytes. */
static inline void nl_attr_put(struct nl_w *w, uint16_t type, const void *p, size_t n)
{
	nl_put16(w, (uint16_t)(RTA_HDR + n));
	nl_put16(w, type);
	nl_put(w, p, n);
	nl_pad(w);
}

/* An attribute whose data is attributes, closed by nl_nest_end. */
static inline size_t nl_nest(struct nl_w *w, uint16_t type)
{
	size_t at = w->n;
	nl_put16(w, 0);
	nl_put16(w, type);
	return at;
}

static inline void nl_nest_end(struct nl_w *w, size_t at)
{
	nl_set16(w, at, (uint16_t)(w->n - at));
}

/* An NLMSG_ERROR: a whole one, with the code and a header, or one cut after `cut`
 * payload bytes. */
static inline void nl_error(struct nl_w *w, int32_t code, int cut)
{
	size_t at = nl_begin(w, NL_ERROR);
	uint8_t body[NL_ERR_BODY] = { 0 };
	memcpy(body, &code, 4);
	nl_put(w, body, cut >= 0 && cut < NL_ERR_BODY ? (size_t)cut : NL_ERR_BODY);
	nl_end(w, at);
	nl_pad(w);
}

/* Queue a reply chunk. */
static inline void nl_queue(const struct nl_w *w)
{
	if (g_nl.n_chunks >= NL_CHUNKS || w->n == 0)
		return;
	memcpy(g_nl.chunk[g_nl.n_chunks], w->b, w->n);
	g_nl.chunk_len[g_nl.n_chunks++] = w->n;
}

/* A chunk of the input's own bytes: [u16 len] then that many, 1 to NL_CHUNK_MAX. */
static inline void nl_queue_raw(struct fuzz_in *in)
{
	struct nl_w w = { .n = 0 };
	const uint8_t *p;
	size_t want = 1 + fuzz_u16(in) % NL_CHUNK_MAX;
	size_t n = fuzz_take(in, want, &p);
	nl_put(&w, p, n);
	nl_queue(&w);
}

#endif /* REACPW_FUZZ_NETLINK_H */
