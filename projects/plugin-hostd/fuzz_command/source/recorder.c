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

/* The recorder that stands in for everything below src/verbs.c (fuzz/recorder.h). */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <host-errors.h>
#include <mod-host.h>
#include <socket.h>

#include <plugin-hostd/protocol.h>

#include "descriptors.h"
#include "formats.h"
#include "pins.h"
#include "supervisor.h"

#include "recorder.h"
#include "syntax.h"

struct recorder g_rec;

const int rec_codes[] = {
    ERR_INSTANCE_INVALID, ERR_INSTANCE_ALREADY_EXISTS, ERR_INSTANCE_NON_EXISTS, ERR_INSTANCE_UNLICENSED,
    ERR_HOST_INVALID_URI, ERR_HOST_INSTANTIATION, ERR_HOST_INVALID_PARAM_SYMBOL, ERR_HOST_INVALID_PRESET_URI,
    ERR_HOST_CANT_LOAD_STATE, ERR_JACK_CLIENT_CREATION, ERR_JACK_CLIENT_ACTIVATION, ERR_JACK_CLIENT_DEACTIVATION,
    ERR_JACK_PORT_REGISTER, ERR_JACK_PORT_CONNECTION, ERR_JACK_PORT_DISCONNECTION, ERR_JACK_VALUE_OUT_OF_RANGE,
    ERR_ASSIGNMENT_ALREADY_EXISTS, ERR_ASSIGNMENT_INVALID_OP, ERR_ASSIGNMENT_LIST_FULL, ERR_ASSIGNMENT_FAILED,
    ERR_ASSIGNMENT_UNUSED, ERR_CONTROL_CHAIN_UNAVAILABLE, ERR_ABLETON_LINK_UNAVAILABLE, ERR_HMI_UNAVAILABLE,
    ERR_EXTERNAL_UI_UNAVAILABLE, ERR_MEMORY_ALLOCATION, ERR_INVALID_OPERATION,
#define X(id, meaning) PHD_ERR_##id,
    PHD_ERRORS(X)
#undef X
};
const int rec_ncodes = (int)(sizeof(rec_codes) / sizeof(rec_codes[0]));

int rec_code_declared(int code)
{
    int n;

    for (n = 0; n < rec_ncodes; n++)
        if (rec_codes[n] == code)
            return 1;
    return 0;
}

/* the reply shapes the daemon's verbs declare (PHD_VERBS, PHD_INSTANCE_VERBS) */
static const struct { const char *name, *reply; } g_shapes[] = {
#define X(id, name, arguments, reply, meaning) { name, reply },
    PHD_VERBS(X)
#undef X
#define X(id, name, arguments, reply, ledger, meaning) { name, reply },
    PHD_INSTANCE_VERBS(X)
#undef X
};

const char *rec_shape_of(const char *verb, size_t len)
{
    size_t n;

    for (n = 0; n < sizeof(g_shapes) / sizeof(g_shapes[0]); n++)
        if (strlen(g_shapes[n].name) == len && !memcmp(g_shapes[n].name, verb, len))
            return g_shapes[n].reply;
    return REC_MOD_HOST_SHAPE;
}

static void *xmalloc(size_t n)
{
    void *p = malloc(n ? n : 1);

    /* not a property: the recorder got no memory for what it records */
    if (p == NULL)
        abort();
    return p;
}

static char *xstrdup(const char *s)
{
    size_t n = strlen(s) + 1;

    return memcpy(xmalloc(n), s, n);
}

char *rec_canonical(const char *text, size_t len)
{
    char *out = xmalloc(len + 1);
    size_t i = 0, o = 0;

    while (i < len)
    {
        while (i < len && (text[i] == ' ' || text[i] == '\t'))
            i++;
        if (i == len)
            break;
        if (o)
            out[o++] = ' ';
        while (i < len && text[i] != ' ' && text[i] != '\t')
            out[o++] = text[i++];
    }
    out[o] = '\0';
    return out;
}

void rec_clear(void)
{
    rec_calls_free(g_rec.calls, g_rec.ncalls);
    g_rec.ncalls = 0;
    free(g_rec.answer);
    g_rec.answer = NULL;
    free(g_rec.reply);
    g_rec.reply = NULL;
    g_rec.reply_size = 0;
    g_rec.nreplies = 0;
}

void rec_calls_free(struct rec_call *calls, int n)
{
    int i, a;

    for (i = 0; i < n; i++)
    {
        for (a = 0; a < calls[i].nargs; a++)
            free(calls[i].args[a]);
        calls[i].nargs = 0;
    }
}

int rec_calls_copy(struct rec_call *dst)
{
    int i, a;

    for (i = 0; i < g_rec.ncalls; i++)
    {
        dst[i].fn = g_rec.calls[i].fn;
        dst[i].nargs = g_rec.calls[i].nargs;
        for (a = 0; a < dst[i].nargs; a++)
            dst[i].args[a] = xstrdup(g_rec.calls[i].args[a]);
    }
    return g_rec.ncalls;
}

int rec_calls_equal(const struct rec_call *a, int na, const struct rec_call *b, int nb)
{
    int i, k;

    if (na != nb)
        return 0;
    for (i = 0; i < na; i++)
    {
        if (a[i].fn != b[i].fn || a[i].nargs != b[i].nargs)
            return 0;
        for (k = 0; k < a[i].nargs; k++)
            if (strcmp(a[i].args[k], b[i].args[k]))
                return 0;
    }
    return 1;
}

/* FNV-1a, 64 bits */
static uint64_t mix(uint64_t h, const void *p, size_t n)
{
    const unsigned char *b = p;

    if (h == 0)
        h = 0xcbf29ce484222325ull;
    while (n--)
    {
        h ^= *b++;
        h *= 0x100000001b3ull;
    }
    return h;
}

static uint64_t mix_call(uint64_t h, const struct rec_call *c)
{
    int a;

    h = mix(h, &c->fn, sizeof(c->fn));
    for (a = 0; a < c->nargs; a++)
        h = mix(h, c->args[a], strlen(c->args[a]) + 1);
    return h;
}

/* a call, recorded with its arguments; returns it for the caller to fold into the state */
static struct rec_call *record(int fn)
{
    static struct rec_call spill;
    struct rec_call *c;

    if (g_rec.ncalls == REC_CALLS_MAX)
    {
        /* past the table: kept apart, so a runaway message still changes the state it would change */
        rec_calls_free(&spill, 1);
        c = &spill;
    }
    else
        c = &g_rec.calls[g_rec.ncalls++];
    c->fn = fn;
    c->nargs = 0;
    return c;
}

static void arg_s(struct rec_call *c, const char *s)
{
    if (c->nargs < REC_ARGS_MAX)
        c->args[c->nargs++] = xstrdup(s ? s : "(null)");
}

static void arg_line(struct rec_call *c, const char *line)
{
    if (c->nargs < REC_ARGS_MAX)
        c->args[c->nargs++] = rec_canonical(line, strlen(line));
}

static void arg_i(struct rec_call *c, int v)
{
    char b[16];

    snprintf(b, sizeof(b), "%d", v);
    arg_s(c, b);
}

static char *hand_back(const char *text)
{
    free(g_rec.answer);
    g_rec.answer = xstrdup(text);
    return xstrdup(text);
}

/* the answer to a call that can refuse: the input's refusal, or the verb's declared reply, which changes the state
 * when the call changes anything */
static char *answer(struct rec_call *c, const char *shape, int changes)
{
    char buf[PHD_LINE_MAX];

    if (g_rec.refuse)
    {
        snprintf(buf, sizeof(buf), "resp %d", g_rec.code);
        return hand_back(buf);
    }
    if (changes)
        g_rec.state = mix_call(g_rec.state, c);
    /* the reply a verb declares fits one line of the protocol
     * mutant: include/plugin-hostd/protocol.h:46 `4096` -> `4`
     * input: mod-host-bypass */
    if (syntax_instantiate(shape, buf, sizeof(buf)) < 0)
        abort();
    return hand_back(buf);
}

static const char *daemon_shape(const char *verb)
{
    return rec_shape_of(verb, strlen(verb));
}

/* ---------------------------------------------------------------- the supervisor (src/supervisor.h) */

/* the daemon's own reply: no call answered it, so it is no answer */
char *sup_resp(int code)
{
    char buf[32];

    snprintf(buf, sizeof(buf), "resp %d", code);
    return xstrdup(buf);
}

int sup_reply_code(const char *reply)
{
    return strncmp(reply, "resp ", 5) == 0 ? atoi(reply + 5) : -999;
}

char *sup_add(const char *uri, int id, const char *placement, const char *client)
{
    struct rec_call *c = record(REC_ADD);
    char buf[32];

    arg_s(c, uri);
    arg_i(c, id);
    arg_s(c, placement ? placement : "-");
    arg_s(c, client ? client : "-");
    /* the supervisor takes an instance number of its table only, and answers it back (PHD_VERBS add) */
    if (id < 0 || id >= MAX_INSTANCE)
    {
        snprintf(buf, sizeof(buf), "resp %d", ERR_INSTANCE_INVALID);
        return hand_back(buf);
    }
    if (g_rec.refuse)
        return answer(c, NULL, 0);
    g_rec.state = mix_call(g_rec.state, c);
    snprintf(buf, sizeof(buf), "resp %d", id);
    return hand_back(buf);
}

char *sup_call(int id, const char *line)
{
    struct rec_call *c = record(REC_CALL);

    arg_i(c, id);
    arg_line(c, line);
    return answer(c, REC_MOD_HOST_SHAPE, 1);
}

char *sup_remove(int id)
{
    struct rec_call *c = record(REC_REMOVE);

    arg_i(c, id);
    return answer(c, REC_MOD_HOST_SHAPE, 1);
}

char *sup_remove_all(void)
{
    return answer(record(REC_REMOVE_ALL), REC_MOD_HOST_SHAPE, 1);
}

char *sup_connect(const char *verb, const char *line, const char *port_a, const char *port_b)
{
    struct rec_call *c = record(REC_CONNECT);

    arg_s(c, verb);
    arg_line(c, line);
    arg_s(c, port_a);
    arg_s(c, port_b);
    return answer(c, REC_MOD_HOST_SHAPE, 1);
}

char *sup_broadcast(const char *line)
{
    struct rec_call *c = record(REC_BROADCAST);

    arg_line(c, line);
    return answer(c, REC_MOD_HOST_SHAPE, 1);
}

void sup_host_setting(const char *line, char **tok, int ntok)
{
    struct rec_call *c = record(REC_HOST_SETTING);
    size_t len = 0;
    char *words;
    int n;

    arg_line(c, line);
    arg_i(c, ntok);
    for (n = 0; n < ntok; n++)
        len += strlen(tok[n]) + 1;
    words = xmalloc(len + 1);
    words[0] = '\0';
    for (n = 0; n < ntok; n++)
    {
        if (n)
            strcat(words, " ");
        strcat(words, tok[n]);
    }
    arg_s(c, words);
    free(words);
    g_rec.host_settings = mix_call(g_rec.host_settings, c);
}

char *sup_instance_verb(const char *line, int ledger)
{
    struct rec_call *c = record(REC_INSTANCE_VERB);

    arg_line(c, line);
    arg_i(c, ledger);
    /* the verb is the first word of the line, past any space before it */
    line += strspn(line, " \t");
    return answer(c, rec_shape_of(line, strcspn(line, " \t")), 1);
}

char *sup_worker_list(void)
{
    return answer(record(REC_WORKER_LIST), daemon_shape(PHD_VERB_WORKER_LIST), 0);
}

char *sup_instance_info(int id)
{
    struct rec_call *c = record(REC_INSTANCE_INFO);

    arg_i(c, id);
    return answer(c, daemon_shape(PHD_VERB_INSTANCE_INFO), 0);
}

char *sup_reset(const char *which)
{
    struct rec_call *c = record(REC_RESET);

    arg_s(c, which);
    return answer(c, daemon_shape(PHD_VERB_SUPERVISOR_RESET), 1);
}

char *sup_quarantine_clear(const char *which)
{
    struct rec_call *c = record(REC_QUARANTINE_CLEAR);

    arg_s(c, which);
    return answer(c, daemon_shape(PHD_VERB_QUARANTINE_CLEAR), 1);
}

char *sup_policy_set(const char *format, const char *place)
{
    struct rec_call *c = record(REC_POLICY_SET);

    arg_s(c, format);
    arg_s(c, place);
    return answer(c, daemon_shape(PHD_VERB_POLICY_SET), 1);
}

char *sup_pin_accept(const char *uri)
{
    struct rec_call *c = record(REC_PIN_ACCEPT);

    arg_s(c, uri);
    return answer(c, daemon_shape(PHD_VERB_PIN_ACCEPT), 1);
}

char *sup_pool_config(const char *name, int max)
{
    struct rec_call *c = record(REC_POOL_CONFIG);

    arg_s(c, name);
    arg_i(c, max);
    return answer(c, daemon_shape(PHD_VERB_POOL_CONFIG), 1);
}

char *sup_lv2_worker_set(const char *uri, const char *worker)
{
    struct rec_call *c = record(REC_LV2_WORKER_SET);

    arg_s(c, uri);
    arg_s(c, worker);
    return answer(c, daemon_shape(PHD_VERB_LV2_WORKER_SET), 1);
}

char *sup_worker_env(const char *format, const char *cpus, const char *nice)
{
    struct rec_call *c = record(REC_WORKER_ENV);

    arg_s(c, format);
    arg_s(c, cpus);
    arg_s(c, nice);
    return answer(c, daemon_shape(PHD_VERB_WORKER_ENV), 1);
}

char *sup_chain(int id, const int *ids, int n)
{
    struct rec_call *c = record(REC_CHAIN);
    char *list = xmalloc((size_t)n * 12 + 1);
    size_t o = 0;
    int k;

    arg_i(c, id);
    arg_i(c, n);
    list[0] = '\0';
    for (k = 0; k < n; k++)
        o += (size_t)sprintf(list + o, k ? " %d" : "%d", ids[k]);
    arg_s(c, list);
    free(list);
    return answer(c, daemon_shape(PHD_VERB_CHAIN), 1);
}

char *sup_chain_clear(int id)
{
    struct rec_call *c = record(REC_CHAIN_CLEAR);

    arg_i(c, id);
    return answer(c, daemon_shape(PHD_VERB_CHAIN_CLEAR), 1);
}

/* a checkpoint of what a preset or patch changed: it writes down state, it changes none */
void sup_after_reply(int id, const char *verb)
{
    struct rec_call *c = record(REC_AFTER_REPLY);

    arg_i(c, id);
    arg_s(c, verb);
}

/* ---------------------------------------------------------------- the pins (src/pins.h) */

/* the pins answer a code, which the daemon replies as "resp <code>" with sup_resp: that text is their answer */
static int answer_code(int code)
{
    char buf[32];

    snprintf(buf, sizeof(buf), "resp %d", code);
    free(hand_back(buf));
    return code;
}

int pins_set(const char *uri, const char *files, const char *layout, const char *verdict)
{
    struct rec_call *c = record(REC_PINS_SET);

    arg_s(c, uri);
    arg_s(c, files);
    arg_s(c, layout);
    arg_s(c, verdict ? verdict : "-");
    if (g_rec.refuse)
        return answer_code(g_rec.code);
    g_rec.state = mix_call(g_rec.state, c);
    return answer_code(SUCCESS);
}

int pins_clear(const char *uri)
{
    struct rec_call *c = record(REC_PINS_CLEAR);

    arg_s(c, uri);
    if (g_rec.refuse)
        return answer_code(g_rec.code);
    g_rec.state = mix_call(g_rec.state, c);
    return answer_code(SUCCESS);
}

/* ---------------------------------------------------------------- the descriptors and the LV2 refusals */

/* a scan of the plugin's files starts: a change whatever the add was answered */
void descriptors_add(const char *uri)
{
    struct rec_call *c = record(REC_DESCRIPTORS_ADD);

    arg_s(c, uri);
    g_rec.state = mix_call(g_rec.state, c);
}

char *descriptors_get(const char *uri)
{
    struct rec_call *c = record(REC_DESCRIPTORS_GET);

    arg_s(c, uri);
    return answer(c, daemon_shape(PHD_VERB_DESCRIPTOR_GET), 0);
}

char *descriptors_panel_get(const char *uri)
{
    struct rec_call *c = record(REC_DESCRIPTORS_PANEL_GET);

    arg_s(c, uri);
    return answer(c, daemon_shape(PHD_VERB_PANEL_GET), 0);
}

/* the adapter is asked again about what it refused: a change */
void lv2_refusals_forget(const char *uri)
{
    struct rec_call *c = record(REC_LV2_REFUSALS_FORGET);

    arg_s(c, uri ? uri : "*");
    g_rec.state = mix_call(g_rec.state, c);
}

/* ---------------------------------------------------------------- the command socket (mod-host's socket.h) */

int socket_send(int destination, const char *buffer, int size)
{
    (void)destination;
    g_rec.nreplies++;
    free(g_rec.reply);
    g_rec.reply = NULL;
    g_rec.reply_size = 0;
    if (size > 0)
    {
        g_rec.reply = xmalloc((size_t)size);
        memcpy(g_rec.reply, buffer, (size_t)size);
        g_rec.reply_size = (size_t)size;
    }
    return size;
}
