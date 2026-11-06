/* SPDX-License-Identifier: GPL-3.0-or-later */
/*
 * This file is part of plugin-hostd.
 *
 * plugin-hostd is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * plugin-hostd is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with plugin-hostd.  If not, see <http://www.gnu.org/licenses/>.
 *
 * Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>
 */

/* libFuzzer harness: THE REPLY STREAM (src/relay.c), which reads what each worker writes on its feedback socket, cuts
 * it into NUL-terminated lines and writes them to the controller, ending the gestures a worker or an instance left
 * held. The relay is included whole, as tests/gesture_alloc_test.c does, with its socket calls answered here: recv
 * hands it the bytes the input chose, cut where the input chose, and send collects what the controller would read.
 * No socket is opened and no thread is started: the harness calls drain(), relay_remove(), relay_instance_gone() and
 * relay_event() where the relay's thread and the supervisor would.
 *
 * The relay is built with LINE_LIMIT at 6000 bytes, so an input of a few kilobytes reaches the drop of a long line,
 * and the buffer's growth past its first 8192 bytes.
 *
 * Input: a source (worker feedback socket) is open from the start; then up to OPS_MAX operations, each [op] and its
 *        arguments, op % 10:
 *          0          a worker more (at most SOURCES_MAX at once)
 *          1 s n ...  [s] [u16 LE n] n bytes: what source s writes next, handed to one recv or more, never two writes
 *                     to one recv
 *          2 s        the relay reads source s (its thread's drain on POLLIN)
 *          3 s        source s's worker closes its end: recv answers 0 once its bytes are read
 *          4 s        the supervisor removes source s (relay_remove): the worker died or was stopped
 *          5 id       instance id is removed (relay_instance_gone)
 *          6 s        the next recv of source s is interrupted (EINTR)
 *          7 n ...    [u16 LE n] n bytes: one event of the daemon's own (relay_event), up to its first NUL
 *          8 k        the controller's socket takes at most k bytes a send from now on (0: all of them), and its next
 *                     send is interrupted (EINTR)
 *          9 m        the controller goes away for the rest of the input: m & 1, it closes its connection
 *                     (relay_controller_gone); else its next send fails, as on a connection it reset
 *        s is taken modulo the open sources.
 *
 * The reference: the controller should read, for each source, every complete line (its bytes up to a NUL) the worker
 * wrote that is LINE_LIMIT bytes or shorter, once each, in order (PHD_RELAY VERBATIM and ORDER); for each gesture a
 * relayed "param_gesture <instance> <symbol> begin" opened and no relayed end closed, one
 * "param_gesture <instance> <symbol> end" when its source is removed or its instance is (PHD_EVENTS param_gesture).
 * Once the controller is gone it reads nothing more, and the relay still reads every worker (PHD_RELAY NO_CONTROLLER).
 *
 * Properties, each an abort():
 *   - bounded: after every operation each source's buffer holds at most LINE_LIMIT bytes of an unfinished line, and
 *     its capacity stays under 2 * (LINE_LIMIT + 4096).
 *     Mutant: fuzz/sabotage/reply-bounded.patch, the overflow check against the capacity instead of LINE_LIMIT.
 *   - no-loss: after every read the lines relayed for a source are exactly the reference's complete lines, none lost,
 *     none twice, none out of order, however the stream was cut and wherever the NULs fell; and after each drain(),
 *     relay_remove() and relay_instance_gone(), recv has handed over all the worker wrote to each source the relay
 *     read, so the reference, which takes what recv hands over, is every line the worker wrote (PHD_RELAY ORDER: what
 *     a worker wrote before it died goes out before its worker_died event).
 *     Mutant: fuzz/sabotage/reply-no-loss.patch, a line of exactly LINE_LIMIT bytes dropped.
 *     Mutant: fuzz/sabotage/reply-no-loss-read.patch, a removed source not read to its end.
 *   - shape: every line the relay writes of its own is a declared feedback line: an event as the daemon wrote it, or
 *     the end of a gesture still held, once for each such gesture and for no other; and the controller's stream
 *     always ends on a whole line.
 *     Mutant: fuzz/sabotage/reply-shape.patch, a held gesture ended with begin.
 *   - the controller's socket: the relay writes to the controller's socket and to no other.
 *
 * Each check's comment records a one-line change of the relay that makes that check abort on a named seed of
 * fuzz/corpus/reply/ (`mutant:` and `input:`), or says why the stop is not a property; make fuzz-records applies each
 * one alone (fuzz/records.sh).
 */

#include <errno.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>

#include <arpa/inet.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <poll.h>
#include <pthread.h>
#include <sys/socket.h>
#include <unistd.h>

#include "fuzz.h"

static ssize_t fuzz_recv(int fd, void *buf, size_t len, int flags);
static ssize_t fuzz_send(int fd, const void *buf, size_t len, int flags);
static int fuzz_shutdown(int fd, int how);
static int fuzz_close(int fd);
static int fuzz_fcntl(int fd, int cmd, ...);

#define recv fuzz_recv
#define send fuzz_send
#define shutdown fuzz_shutdown
#define close fuzz_close
#define fcntl fuzz_fcntl
#define LINE_LIMIT 6000
#include "../src/relay.c"
#undef recv
#undef send
#undef shutdown
#undef close
#undef fcntl

#define SOURCES_MAX 4
#define OPS_MAX     512
#define CLIENT_FD   3
#define FIRST_FD    100

/* a line the controller should read, or a gesture held: a copy of its bytes */
struct text {
    char *s;
    size_t n;
};

struct list {
    struct text *v;
    int n, cap;
};

static void list_push(struct list *l, const char *s, size_t n)
{
    if (l->n == l->cap)
    {
        int cap = l->cap ? l->cap * 2 : 8;
        struct text *v = realloc(l->v, (size_t)cap * sizeof(*v));

        /* not a property: the harness got no memory for its own list of lines */
        if (!v)
            abort();
        l->v = v;
        l->cap = cap;
    }
    l->v[l->n].s = malloc(n + 1);
    /* not a property: the harness got no memory for its own copy of a line */
    if (!l->v[l->n].s)
        abort();
    memcpy(l->v[l->n].s, s, n);
    l->v[l->n].s[n] = '\0';
    l->v[l->n].n = n;
    l->n++;
}

static void list_drop(struct list *l, int i)
{
    free(l->v[i].s);
    memmove(&l->v[i], &l->v[i + 1], (size_t)(l->n - i - 1) * sizeof(l->v[0]));
    l->n--;
}

static void list_free(struct list *l)
{
    while (l->n)
        list_drop(l, l->n - 1);
    free(l->v);
    l->v = NULL;
    l->cap = 0;
}

static int list_find(const struct list *l, const char *s, size_t n)
{
    int i;

    for (i = 0; i < l->n; i++)
        if (l->v[i].n == n && !memcmp(l->v[i].s, s, n))
            return i;
    return -1;
}

/* one worker's feedback socket, as the harness writes it and as the reference reads it */
struct source {
    int fd;
    int open;                   /* in the relay's table */
    int closed;                 /* the worker closed its end */
    int eintr;                  /* the next recv is interrupted */
    struct list pending;        /* what the worker wrote and recv has not handed over, one entry per write */
    size_t pending_off;         /* how much of the first entry recv has handed over */
    /* the reference splitter over the bytes recv handed over */
    char *partial;
    size_t npartial;
    int overlong;
    struct list expected;       /* complete lines the controller should read and has not */
    struct list held;           /* gestures the relayed lines opened and did not end, each its line up to the last word */
};

static struct source g_s[SOURCES_MAX];
static int g_nfd;

/* what the controller read during one operation */
static char *g_out;
static size_t g_nout, g_capout;
/* how the controller's socket takes a send: at most g_send_max bytes (0: all), the next one interrupted, the next one
 * failed; and whether the controller is gone */
static size_t g_send_max;
static int g_send_eintr, g_send_dead, g_gone;

static struct source *source_of(int fd)
{
    int i;

    for (i = 0; i < SOURCES_MAX; i++)
        if (g_s[i].open && g_s[i].fd == fd)
            return &g_s[i];
    return NULL;
}

/* the reference splitter: a line ends at a NUL, and one longer than LINE_LIMIT is not a line of the protocol */
static void reference_feed(struct source *s, const char *p, size_t n)
{
    size_t i;

    for (i = 0; i < n; i++)
    {
        if (p[i] == '\0')
        {
            if (!s->overlong)
                list_push(&s->expected, s->partial, s->npartial);
            s->npartial = 0;
            s->overlong = 0;
        }
        else if (!s->overlong)
        {
            if (s->npartial == LINE_LIMIT)
                s->overlong = 1;
            else
                s->partial[s->npartial++] = p[i];
        }
    }
}

static ssize_t fuzz_recv(int fd, void *buf, size_t len, int flags)
{
    struct source *s = source_of(fd);
    size_t n;

    (void)flags;
    if (s == NULL)
    {
        errno = EBADF;
        return -1;
    }
    if (s->eintr)
    {
        s->eintr = 0;
        errno = EINTR;
        return -1;
    }
    if (s->pending.n == 0)
    {
        if (s->closed)
            return 0;
        errno = EAGAIN;
        return -1;
    }
    n = s->pending.v[0].n - s->pending_off;
    if (n > len)
        n = len;
    memcpy(buf, s->pending.v[0].s + s->pending_off, n);
    reference_feed(s, s->pending.v[0].s + s->pending_off, n);
    s->pending_off += n;
    if (s->pending_off == s->pending.v[0].n)
    {
        list_drop(&s->pending, 0);
        s->pending_off = 0;
    }
    return (ssize_t)n;
}

static ssize_t fuzz_send(int fd, const void *buf, size_t len, int flags)
{
    (void)flags;
    /* the controller's socket property: the relay writes to the controller and to no other socket
     * mutant: src/relay.c:74 `send(g_client,` -> `send(g_client + 1,`
     * input: lines */
    if (fd != CLIENT_FD)
        abort();
    if (g_send_eintr)
    {
        g_send_eintr = 0;
        errno = EINTR;
        return -1;
    }
    if (g_send_dead)
    {
        errno = EPIPE;
        return -1;
    }
    if (g_send_max && len > g_send_max)
        len = g_send_max;
    if (g_nout + len > g_capout)
    {
        size_t cap = (g_nout + len) * 2;
        char *out = realloc(g_out, cap);

        /* not a property: the harness got no memory to keep what the controller reads */
        if (!out)
            abort();
        g_out = out;
        g_capout = cap;
    }
    memcpy(g_out + g_nout, buf, len);
    g_nout += len;
    return (ssize_t)len;
}

static int fuzz_shutdown(int fd, int how)
{
    (void)fd;
    (void)how;
    return 0;
}

static int fuzz_close(int fd)
{
    (void)fd;
    return 0;
}

static int fuzz_fcntl(int fd, int cmd, ...)
{
    (void)fd;
    (void)cmd;
    return 0;
}

/* ---------------------------------------------------------------- the properties */

/* the bounded property, over every source in the relay's table */
__attribute__((noinline)) static void check_bounded(void)
{
    int i;

    for (i = 0; i < g_nsrc; i++)
    {
        /* an unfinished line the relay keeps is never past LINE_LIMIT, nor past what holds it
         * mutant: src/relay.c:218 `s->used > LINE_LIMIT` -> `s->used > s->cap`
         * input: line-past-the-limit-in-parts */
        if (g_src[i].used > LINE_LIMIT || g_src[i].used > g_src[i].cap)
            abort();
        /* and what holds it does not grow without end
         * mutant: src/relay.c:180 `s->cap * 2` -> `s->cap * 3`
         * input: buffer-grows */
        if (g_src[i].cap >= 2 * ((size_t)LINE_LIMIT + 4096))
            abort();
    }
}

/* the controller's stream of one operation, cut into lines: *at is where the next one starts */
static int next_line(size_t *at, const char **line, size_t *len)
{
    const char *nul;

    if (*at == g_nout)
        return 0;
    nul = memchr(g_out + *at, '\0', g_nout - *at);
    /* the shape property: the stream ends on a whole line
     * mutant: src/relay.c:406 `strlen(line) + 1` -> `strlen(line)`
     * input: event */
    if (nul == NULL)
        abort();
    *line = g_out + *at;
    *len = (size_t)(nul - *line);
    *at += *len + 1;
    return 1;
}

/* a relayed line that opens or ends a gesture, read as PHD_EVENTS declares param_gesture */
static void gesture_model(struct source *s, const char *line, size_t len)
{
    size_t verb = strlen(PHD_EVENT_PARAM_GESTURE), last;
    const char *word;

    if (len <= verb || memcmp(line, PHD_EVENT_PARAM_GESTURE, verb) || line[verb] != ' ')
        return;
    for (last = len; last > 0 && line[last - 1] != ' '; last--)
        ;
    if (last == 0 || last - 1 == verb)
        return;
    word = line + last;
    if (len - last == strlen(PHD_GESTURE_BEGIN) && !memcmp(word, PHD_GESTURE_BEGIN, len - last))
    {
        if (list_find(&s->held, line, last - 1) < 0)
            list_push(&s->held, line, last - 1);
    }
    else if (len - last == strlen(PHD_GESTURE_END) && !memcmp(word, PHD_GESTURE_END, len - last))
    {
        int i = list_find(&s->held, line, last - 1);

        if (i >= 0)
            list_drop(&s->held, i);
    }
}

/* the no-loss property for one source: the next `n` lines of the stream are its expected lines, in order, and then
 * none is expected any more */
__attribute__((noinline)) static void check_no_loss(struct source *s, size_t *at)
{
    const char *line;
    size_t len;

    while (s->expected.n > 0)
    {
        if (g_gone)
        {
            /* read and dropped: its gestures are still followed */
            gesture_model(s, s->expected.v[0].s, s->expected.v[0].n);
            list_drop(&s->expected, 0);
            continue;
        }
        /* every complete line it wrote is read by the controller
         * mutant: src/relay.c:207 `> LINE_LIMIT` -> `>= LINE_LIMIT`
         * input: line-at-the-limit */
        if (!next_line(at, &line, &len))
            abort();
        /* as it wrote it
         * mutant: src/relay.c:211 `start, nul - start + 1` -> `start + 1, nul - start`
         * input: lines */
        if (len != s->expected.v[0].n || memcmp(line, s->expected.v[0].s, len))
            abort();
        gesture_model(s, line, len);
        list_drop(&s->expected, 0);
    }
}

/* the no-loss property for what the relay read of one source: the reference takes only what recv handed over, so this
 * holds the relay to all the worker wrote, not to what it asked recv for */
__attribute__((noinline)) static void check_no_loss_read(const struct source *s)
{
    /* recv handed over every byte the worker wrote to it before the relay went on
     * mutant: src/relay.c:464 `drain(&g_src[i]);` -> `;`
     * input: written-then-removed
     * mutant: src/relay.c:447 `drain(&g_src[i]);` -> `;`
     * input: written-then-instance-gone */
    if (s->pending.n > 0)
        abort();
}

static int has_prefix(const char *s, size_t n, const char *prefix)
{
    size_t p = strlen(prefix);

    return n >= p && !memcmp(s, prefix, p);
}

/* the shape property for the gesture ends the relay writes for a source: one "<held> end" for each held gesture
 * `prefix` selects, and no other line */
__attribute__((noinline)) static void check_shape_ends(struct source *s, const char *prefix, size_t *at)
{
    const char *line;
    size_t len, end = strlen(" " PHD_GESTURE_END);
    int want = 0, i;

    for (i = 0; i < s->held.n; i++)
        if (has_prefix(s->held.v[i].s, s->held.v[i].n, prefix))
            want++;
    if (g_gone)
    {
        /* ended where no controller reads them */
        for (i = s->held.n - 1; i >= 0; i--)
            if (has_prefix(s->held.v[i].s, s->held.v[i].n, prefix))
                list_drop(&s->held, i);
        return;
    }
    while (want-- > 0)
    {
        /* a gesture still held is ended
         * mutant: src/relay.c:138 `gesture_end(s->held[n]);` -> ``
         * input: gesture-held-then-removed */
        if (!next_line(at, &line, &len))
            abort();
        /* with a line that ends it
         * mutant: src/relay.c:128 `" " PHD_GESTURE_END, sizeof(" " PHD_GESTURE_END)` -> `" " PHD_GESTURE_BEGIN, sizeof(" " PHD_GESTURE_BEGIN)`
         * input: gesture-held-then-removed */
        if (len < end || memcmp(line + len - end, " " PHD_GESTURE_END, end))
            abort();
        i = list_find(&s->held, line, len - end);
        /* of a gesture still held, of the instance or the worker that went, and of each one only once
         * mutant: src/relay.c:127 `strlen(held)` -> `strlen(held) - 1`
         * input: gesture-held-then-removed */
        if (i < 0 || !has_prefix(line, len, prefix))
            abort();
        list_drop(&s->held, i);
    }
}

/* the whole stream of an operation was read: nothing is left over */
__attribute__((noinline)) static void check_shape_done(size_t at)
{
    /* no line the reference does not account for
     * mutant: src/relay.c:406 `send_line(line, strlen(line) + 1);` -> `send_line(line, strlen(line) + 1); send_line(line, strlen(line) + 1);`
     * input: event */
    if (at != g_nout)
        abort();
}

/* the shape property for an event of the daemon's own: the controller reads it as it was written */
__attribute__((noinline)) static void check_shape_event(const char *event)
{
    size_t at = 0, len;
    const char *line;

    if (g_gone)
    {
        check_shape_done(at);
        return;
    }
    /* an event of the daemon's own is relayed
     * mutant: src/relay.c:406 `send_line(line, strlen(line) + 1);` -> ``
     * input: event */
    if (!next_line(&at, &line, &len))
        abort();
    /* as the daemon wrote it
     * mutant: src/relay.c:406 `line, strlen(line) + 1` -> `line + 1, strlen(line)`
     * input: event */
    if (len != strlen(event) || memcmp(line, event, len))
        abort();
    check_shape_done(at);
}

/* ---------------------------------------------------------------- the operations */

static void source_reset(struct source *s)
{
    list_free(&s->pending);
    list_free(&s->expected);
    list_free(&s->held);
    free(s->partial);
    memset(s, 0, sizeof(*s));
}

static int open_count(void)
{
    int i, n = 0;

    for (i = 0; i < SOURCES_MAX; i++)
        n += g_s[i].open;
    return n;
}

/* the k-th open source, k taken modulo the open ones */
static struct source *pick(uint8_t k)
{
    int n = open_count(), i;

    if (n == 0)
        return NULL;
    k %= n;
    for (i = 0; i < SOURCES_MAX; i++)
        if (g_s[i].open && k-- == 0)
            return &g_s[i];
    return NULL;
}

static source_t *relay_source(int fd)
{
    int i;

    for (i = 0; i < g_nsrc; i++)
        if (g_src[i].fd == fd)
            return &g_src[i];
    return NULL;
}

static void op_add(void)
{
    int i;

    for (i = 0; i < SOURCES_MAX; i++)
        if (!g_s[i].open)
        {
            source_reset(&g_s[i]);
            g_s[i].fd = FIRST_FD + g_nfd++;
            g_s[i].partial = malloc(LINE_LIMIT);
            /* not a property: the harness got no memory for its reference splitter */
            if (!g_s[i].partial)
                abort();
            g_s[i].open = 1;
            /* the relay follows a worker it is handed
             * mutant: src/relay.c:412 `fd < 0` -> `fd >= 0`
             * input: lines */
            if (relay_add(g_s[i].fd) != 0)
                abort();
            return;
        }
}

static void op_drain(struct source *s)
{
    source_t *r = relay_source(s->fd);
    size_t at = 0;

    if (r == NULL || r->eof)
        return;
    pthread_mutex_lock(&g_lock);
    drain(r);
    pthread_mutex_unlock(&g_lock);
    check_no_loss_read(s);
    check_no_loss(s, &at);
    check_shape_done(at);
}

/* whether the relay reads source s: it follows it and has not seen its end */
static int relay_reads(const struct source *s)
{
    source_t *r = relay_source(s->fd);

    return r != NULL && !r->eof;
}

static void op_remove(struct source *s)
{
    size_t at = 0;
    int reads = relay_reads(s);

    relay_remove(s->fd);
    if (reads)
        check_no_loss_read(s);
    check_no_loss(s, &at);
    check_shape_ends(s, "", &at);
    check_shape_done(at);
    source_reset(s);
}

static void op_gone(int id)
{
    char prefix[48];
    size_t at = 0;
    int i, k, reads[SOURCES_MAX];

    snprintf(prefix, sizeof(prefix), "%s %d ", PHD_EVENT_PARAM_GESTURE, id);
    for (k = 0; k < SOURCES_MAX; k++)
        reads[k] = g_s[k].open && relay_reads(&g_s[k]);
    relay_instance_gone(id);
    for (k = 0; k < SOURCES_MAX; k++)
        if (reads[k])
            check_no_loss_read(&g_s[k]);
    /* the relay walks its table in order: each source's lines, then the ends of its gestures of that instance */
    for (i = 0; i < g_nsrc; i++)
        for (k = 0; k < SOURCES_MAX; k++)
            if (g_s[k].open && g_s[k].fd == g_src[i].fd)
            {
                check_no_loss(&g_s[k], &at);
                check_shape_ends(&g_s[k], prefix, &at);
            }
    check_shape_done(at);
}

static void op_event(const uint8_t *p, size_t n)
{
    char *event = malloc(n + 1);

    /* not a property: the harness got no memory for its copy of the event */
    if (!event)
        abort();
    memcpy(event, p, n);
    event[n] = '\0';
    relay_event(event);
    check_shape_event(event);
    free(event);
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
    struct fuzz_in in;
    int ops, i;

    if (size >= FUZZ_INPUT_MAX)
        return 0;
    in = fuzz_in(data, size);
    g_client = CLIENT_FD;
    g_client_broken = 0;
    g_nfd = 0;
    g_send_max = 0;
    g_send_eintr = g_send_dead = g_gone = 0;
    op_add();
    for (ops = 0; ops < OPS_MAX && in.n; ops++)
    {
        uint8_t op = fuzz_u8(&in) % 10;
        struct source *s = NULL;
        const uint8_t *p;
        size_t n;

        g_nout = 0;
        if (op == 1 || op == 2 || op == 3 || op == 4 || op == 6)
        {
            s = pick(fuzz_u8(&in));
            if (s == NULL && op != 1)
                continue;
        }
        switch (op)
        {
        case 0:
            op_add();
            break;
        case 1:
            n = fuzz_take(&in, fuzz_u16(&in), &p);
            if (s && n)
                list_push(&s->pending, (const char *)p, n);
            break;
        case 2:
            op_drain(s);
            break;
        case 3:
            s->closed = 1;
            break;
        case 4:
            op_remove(s);
            break;
        case 5:
            op_gone(fuzz_u8(&in));
            break;
        case 6:
            s->eintr = 1;
            break;
        case 7:
            n = fuzz_take(&in, fuzz_u16(&in), &p);
            op_event(p, strnlen((const char *)p, n));
            break;
        case 8:
            g_send_max = fuzz_u8(&in);
            g_send_eintr = 1;
            break;
        default:
            if (fuzz_u8(&in) & 1)
                relay_controller_gone();
            else
                g_send_dead = 1;
            g_gone = 1;
            break;
        }
        check_bounded();
    }
    /* the daemon stops: every source left is closed and every gesture still held is ended, in the relay's table order */
    {
        int order[SOURCES_MAX], norder = 0, k;
        size_t at = 0;

        for (i = 0; i < g_nsrc && norder < SOURCES_MAX; i++)
            order[norder++] = g_src[i].fd;
        g_nout = 0;
        relay_finish();
        for (i = 0; i < norder; i++)
            for (k = 0; k < SOURCES_MAX; k++)
                if (g_s[k].open && g_s[k].fd == order[i])
                    check_shape_ends(&g_s[k], "", &at);
        check_shape_done(at);
    }
    for (i = 0; i < SOURCES_MAX; i++)
        source_reset(&g_s[i]);
    return 0;
}
