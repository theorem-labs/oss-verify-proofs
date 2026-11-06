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

/* libFuzzer harness: THE COMMAND PARSER AND DISPATCHER (src/verbs.c, verbs_receive and everything it calls in that
 * file), with the mod-host side replaced by the recorder of fuzz/recorder.c. A controller's message is whatever bytes
 * it sends; the daemon reads its words, refuses what is outside its grammar, and hands the rest to the supervisor.
 *
 * Input: up to MESSAGES_MAX messages, each
 *          [flags] [u16 LE length] [that many bytes, at most MESSAGE_MAX]
 *        flags bit 0: the recorder refuses every call of this message that can refuse, with the declared code
 *        rec_codes[(flags >> 1) % rec_ncodes]; clear, it accepts with the reply each verb declares. Each message is
 *        copied into an allocation of exactly its length, with no terminator, as the socket hands it over.
 *
 * The words of a message, below, are what the daemon reads: its bytes up to the first NUL, the newlines, carriage
 * returns, spaces and tabs at its end removed, split at spaces and tabs. Its verb is the first word.
 *
 * Properties, each an abort():
 *   - reply: every message gets exactly one reply, one NUL-terminated string with no NUL before its end. When a call
 *     answered (the supervisor's text, or "resp <code>" of the code the pins returned), the reply is that answer,
 *     unchanged; when none did, it is one the daemon makes itself, a refusal or "resp 0" for quit. A refusal is
 *     "resp <code>" of a declared code, and anything else has the reply shape its verb declares (PHD_VERBS,
 *     PHD_INSTANCE_VERBS) or mod-host's "resp 0".
 *     Mutant: fuzz/sabotage/command-reply.patch, the reply sent without its NUL.
 *     Mutant: fuzz/sabotage/command-reply-answer.patch, a pin_set the pins refused replied "resp 0".
 *   - arity: a verb the daemon parses itself (PHD_VERBS, the rows tools/protocol-gen.c writes into
 *     protocol/plugin-hostd.json, and mod-host's remove, connect, disconnect and quit) is acted on, by its own call
 *     or by a broadcast to every worker, only with an argument count its declared syntax allows; a word past
 *     PHD_LINE_WORDS_MAX is not read. The broadcast of pin_layout, pin_expect, and connect or disconnect of another
 *     count is the workers' to refuse (passed_on).
 *     Mutant: fuzz/sabotage/command-arity.patch, pool_config taking three words or more.
 *     Mutant: fuzz/sabotage/command-arity-broadcast.patch, remove of another count sent to every worker.
 *   - words: each call the daemon makes is handed the message's words at the places its verb declares them, as the
 *     harness reads them (g_call_words): a word as written, a number as atoi reads it, a line as its words joined by
 *     one space; and the words a verb may leave out as the harness works them out from the message: the placement
 *     and the client of add, the members of chain and their count, the verdict of pin_set. The round trip below
 *     compares the daemon with itself, so a word put in the wrong place twice keeps it true; this does not.
 *     Mutant: fuzz/sabotage/command-words-add.patch, the placement and the client of add swapped.
 *     Mutant: fuzz/sabotage/command-words-chain.patch, a chain without its last member.
 *     Mutant: fuzz/sabotage/command-words-pin-set.patch, the verdict of pin_set with its key.
 *   - round-trip: the words of a command the daemon acted on, joined by one space as the declaration writes them,
 *     make the same calls with the same arguments, the same reply and the same state.
 *     Mutant: fuzz/sabotage/command-round-trip.patch, words split at spaces only.
 *   - refusal: a refused command (its reply's code is negative) leaves the daemon's state as it was: no call the
 *     supervisor took and none of the daemon's own follow-ups (a descriptor scan, the LV2 refusals asked again, quit).
 *     The host settings are not part of it: PHD_HOST_SETTINGS keeps them as sent, whatever the workers answer.
 *     Mutant: fuzz/sabotage/command-refusal.patch, a refused add still scanned.
 *
 * Each check's comment records a one-line change of the daemon that makes that check abort on a named seed of
 * fuzz/corpus/command/ (`mutant:` and `input:`), or says why the stop is not a property; make fuzz-records applies
 * each one alone (fuzz/records.sh).
 */

#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <host-errors.h>
#include <mod-host.h>

#include <plugin-hostd/protocol.h>

#include "supervisor.h"
#include "verbs.h"

#include "fuzz.h"
#include "recorder.h"
#include "syntax.h"

#define MESSAGES_MAX 32
#define MESSAGE_MAX  (2 * PHD_LINE_MAX)

/* the verbs the daemon parses itself, with their declared argument syntax */
static const struct {
    const char *name;
    const char *syntax;
    int format;                 /* 1: syntax is a mod-host command format, "<verb> %i ..." */
} g_parsed[] = {
#define X(id, name, arguments, reply, meaning) { name, arguments, 0 },
    PHD_VERBS(X)
#undef X
    { "remove", EFFECT_REMOVE, 1 },
    { "connect", EFFECT_CONNECT, 1 },
    { "disconnect", EFFECT_DISCONNECT, 1 },
    { "quit", QUIT, 1 },
};

/* the words of a message as the daemon reads them */
struct words {
    char *text;                 /* the message up to its first NUL, its end trimmed; the words point into a copy */
    char *copy;
    char **w;
    int n;
};

static void words_of(const char *data, size_t size, struct words *out)
{
    size_t len = strnlen(data, size), cap = len / 2 + 2;
    char *t;

    out->text = malloc(len + 1);
    out->copy = malloc(len + 1);
    out->w = malloc(cap * sizeof(char *));
    /* not a property: the harness got no memory for its own copy of the message's words */
    if (!out->text || !out->copy || !out->w)
        abort();
    memcpy(out->text, data, len);
    out->text[len] = '\0';
    while (len > 0 && (out->text[len - 1] == '\n' || out->text[len - 1] == '\r' || out->text[len - 1] == ' ' ||
                       out->text[len - 1] == '\t'))
        out->text[--len] = '\0';
    memcpy(out->copy, out->text, len + 1);
    out->n = 0;
    for (t = out->copy; *t;)
    {
        t += strspn(t, " \t");
        if (!*t)
            break;
        out->w[out->n++] = t;
        t += strcspn(t, " \t");
        if (*t)
            *t++ = '\0';
    }
}

static void words_free(struct words *w)
{
    free(w->text);
    free(w->copy);
    free(w->w);
}

/* the message's words joined by one space */
static char *joined(const struct words *w, size_t *len)
{
    size_t n = 0;
    char *s;
    int k;

    for (k = 0; k < w->n; k++)
        n += strlen(w->w[k]) + 1;
    s = malloc(n + 1);
    /* not a property: the harness got no memory for the words joined by one space */
    if (!s)
        abort();
    s[0] = '\0';
    for (k = 0, n = 0; k < w->n; k++)
    {
        size_t l = strlen(w->w[k]);

        if (k)
            s[n++] = ' ';
        memcpy(s + n, w->w[k], l);
        n += l;
    }
    s[n] = '\0';
    *len = n;
    return s;
}

/* one message to the daemon, in an allocation of exactly its length */
static void send_message(const uint8_t *bytes, size_t len)
{
    msg_t msg;

    msg.sender_id = 7;
    msg.data = fuzz_dup(bytes, len);
    msg.data_size = len;
    g_quitting = 0;
    rec_clear();
    verbs_receive(&msg);
    free(msg.data);
}

/* whether the daemon acted on the message: it called the supervisor, or it is quitting */
static int acted(void)
{
    return g_quitting || g_rec.ncalls > 0;
}

/* the reply property for where the reply comes from: the answer of the call that answered, or, when none did, a reply
 * the daemon makes itself */
__attribute__((noinline)) static void check_reply_answer(const struct words *w)
{
    if (g_rec.answer)
    {
        /* a call answered: the reply is its answer, as it answered it
         * mutant: src/verbs.c:120 `text, strlen(text) + 1` -> `text + 1, strlen(text)`
         * input: add-default
         * mutant: src/verbs.c:90 `return rc;` -> `return SUCCESS;`
         * input: plugin-hostd-pin_set-refused
         * mutant: src/verbs.c:214 `return reply_text;` -> `return sup_resp(SUCCESS);`
         * input: mod-host-set_bpm-refused */
        if (strcmp(g_rec.reply, g_rec.answer))
            abort();
        return;
    }
    /* no call answered: the reply is one the daemon makes itself, a refusal or the reply of quit, which check_reply
     * holds to "resp <code>" of a declared code and to "resp 0"
     * mutant: src/verbs.c:135 `return sup_resp(ERR_INVALID_OPERATION);` -> `return sup_resp(SUCCESS);`
     * input: add-too-few */
    if (sup_reply_code(g_rec.reply) >= 0 && !(w->n == 1 && verb_is(w->w[0], QUIT)))
        abort();
}

/* the reply property */
__attribute__((noinline)) static void check_reply(const struct words *w)
{
    char refusal[32];
    const char *shape;
    int code;

    /* one reply, and nothing sent empty
     * mutant: src/verbs.c:232 `reply(msg->sender_id, handle(line, tok, ntok));` -> `free(handle(line, tok, ntok));`
     * input: add-default */
    if (g_rec.nreplies != 1 || g_rec.reply_size == 0)
        abort();
    /* the reply is a string that ends where the message the socket sends ends
     * mutant: src/verbs.c:120 `strlen(text) + 1` -> `strlen(text)`
     * input: add-default */
    if (g_rec.reply[g_rec.reply_size - 1] != '\0' || memchr(g_rec.reply, '\0', g_rec.reply_size - 1))
        abort();
    check_reply_answer(w);
    code = sup_reply_code(g_rec.reply);
    if (code < 0)
    {
        snprintf(refusal, sizeof(refusal), "resp %d", code);
        /* a refusal is "resp <code>" of a declared code
         * mutant: src/verbs.c:79 `return ERR_INVALID_OPERATION;` -> `return -7777;`
         * input: pin-set-layout-unknown */
        if (!rec_code_declared(code) || strcmp(g_rec.reply, refusal))
            abort();
        return;
    }
    shape = w->n ? rec_shape_of(w->w[0], strlen(w->w[0])) : REC_MOD_HOST_SHAPE;
    /* anything else has the shape its verb declares, or mod-host's
     * mutant: src/verbs.c:203 `sup_resp(SUCCESS)` -> `sup_resp(1)`
     * input: mod-host-quit */
    if (!syntax_reply_matches(shape, g_rec.reply) && !syntax_reply_matches(REC_MOD_HOST_SHAPE, g_rec.reply))
        abort();
}

/* the verbs of g_parsed the daemon passes to every worker, whatever their count: pin_layout and pin_expect, which the
 * daemon sends a worker itself (PHD_VERBS) and handle() does not parse, so from a controller they go out as any line it
 * does not parse, for each worker to refuse; and connect and disconnect with another count than two ports, whose
 * grammar is mod-host's, so each worker's mod-host refuses them */
static int passed_on(const char *verb)
{
    return !strcmp(verb, PHD_VERB_PIN_LAYOUT) || !strcmp(verb, PHD_VERB_PIN_EXPECT) || verb_is(verb, EFFECT_CONNECT) ||
           verb_is(verb, EFFECT_DISCONNECT);
}

/* the arity property */
__attribute__((noinline)) static void check_arity(const struct words *w)
{
    size_t n;
    int read, min, max;

    if (w->n == 0 || !acted() || (g_rec.ncalls > 0 && g_rec.calls[0].fn == REC_BROADCAST && passed_on(w->w[0])))
        return;
    read = w->n < PHD_LINE_WORDS_MAX ? w->n : PHD_LINE_WORDS_MAX;
    for (n = 0; n < sizeof(g_parsed) / sizeof(g_parsed[0]); n++)
    {
        if (strcmp(w->w[0], g_parsed[n].name))
            continue;
        if (g_parsed[n].format)
            syntax_format_arity(g_parsed[n].syntax, &min, &max);
        else
            syntax_arity(g_parsed[n].syntax, &min, &max);
        /* acted on, by its own call or by a broadcast, with an argument count the declaration allows
         * mutant: src/verbs.c:175 `ntok == 3` -> `ntok >= 3`
         * input: plugin-hostd-pool_config-extra
         * mutant: src/verbs.c:152 `verb_is(verb, EFFECT_REMOVE)` -> `verb_is(verb, EFFECT_REMOVE) && ntok == 2`
         * input: mod-host-remove-extra */
        if (read - 1 < min || read - 1 > max)
            abort();
        return;
    }
}

/* how each call takes the message's words, one item for each argument it records (fuzz/recorder.c): "<k>" is word k
 * as written, "#<k>" word k as atoi reads it, "?<k>" word k when the message has one, "L" the words joined by one
 * space, and "*" an argument that is no word of the message as written: a count, a ledger, a word of the daemon's own,
 * or one the harness works out from the words below, in check_words_add, check_words_chain and check_words_pin_set
 * (the placement and the client of add, the members of chain and their count, the verdict of pin_set) */
static const char *const g_call_words[REC_FN_COUNT] = {
    [REC_ADD] = "1 #2 * *",
    [REC_CALL] = "#1 L",
    [REC_REMOVE] = "#1",
    [REC_REMOVE_ALL] = "",
    [REC_CONNECT] = "0 L 1 2",
    [REC_BROADCAST] = "L",
    [REC_HOST_SETTING] = "L * *",
    [REC_INSTANCE_VERB] = "L *",
    [REC_WORKER_LIST] = "",
    [REC_INSTANCE_INFO] = "#1",
    [REC_RESET] = "?1",
    [REC_QUARANTINE_CLEAR] = "1",
    [REC_POLICY_SET] = "1 2",
    [REC_PIN_ACCEPT] = "1",
    [REC_POOL_CONFIG] = "1 #2",
    [REC_LV2_WORKER_SET] = "1 2",
    [REC_WORKER_ENV] = "1 2 3",
    [REC_CHAIN] = "#1 * *",
    [REC_CHAIN_CLEAR] = "#1",
    [REC_AFTER_REPLY] = "#1 0",
    [REC_PINS_SET] = "1 2 3 *",
    [REC_PINS_CLEAR] = "1",
    [REC_DESCRIPTORS_ADD] = "1",
    [REC_DESCRIPTORS_GET] = "1",
    [REC_DESCRIPTORS_PANEL_GET] = "1",
    [REC_LV2_REFUSALS_FORGET] = "*",
};

static int is_placement(const char *word)
{
    return !strcmp(word, PHD_PLACE_OWN) || !strcmp(word, PHD_PLACE_DEFAULT) ||
           !strncmp(word, PHD_PLACE_POOL_PREFIX, strlen(PHD_PLACE_POOL_PREFIX));
}

/* the words property for add <uri> <instance> [<placement>] [<client>]: the placement is word 3 when that word is one,
 * else "-"; the client is the word after the placement, or word 3 when there is no placement, else "-" */
__attribute__((noinline)) static void check_words_add(const struct rec_call *call, const char *const *w, int read)
{
    const char *placement = read > 3 && is_placement(w[3]) ? w[3] : "-";
    int next = strcmp(placement, "-") ? 4 : 3;
    const char *client = read > next ? w[next] : "-";

    /* the placement and the client, each where the message has it
     * mutant: src/verbs.c:142 `placement, client` -> `client, placement`
     * input: add-pool-p-fuzz_client */
    if (call->nargs != 4 || strcmp(call->args[2], placement) || strcmp(call->args[3], client))
        abort();
}

/* the words property for chain <chain> <instance> [<instance> ...]: the members are word 2 and every word after it, as
 * numbers, and their count is how many they are */
__attribute__((noinline)) static void check_words_chain(const struct rec_call *call, const char *const *w, int read)
{
    char list[PHD_LINE_WORDS_MAX * 12 + 1], count[16];
    size_t o = 0;
    int k;

    list[0] = '\0';
    for (k = 2; k < read; k++)
        o += (size_t)snprintf(list + o, sizeof(list) - o, k > 2 ? " %d" : "%d", atoi(w[k]));
    snprintf(count, sizeof(count), "%d", read - 2);
    /* every member, in the order of the message, and their count
     * mutant: src/verbs.c:115 `ntok - 2` -> `ntok - 3`
     * input: plugin-hostd-chain */
    if (call->nargs != 3 || strcmp(call->args[1], count) || strcmp(call->args[2], list))
        abort();
}

/* the words property for pin_set <uri> <files> <layout> [verdict=<word>]: the verdict is word 4 without its prefix,
 * else "-" */
__attribute__((noinline)) static void check_words_pin_set(const struct rec_call *call, const char *const *w, int read)
{
    size_t key = strlen(PHD_PIN_VERDICT_KEY);
    const char *verdict = "-";

    if (read > 4)
        verdict = strncmp(w[4], PHD_PIN_VERDICT_KEY, key) ? w[4] : w[4] + key;
    /* the verdict, the word the controller wrote after its key
     * mutant: src/verbs.c:84 `tok[4] + key` -> `tok[4]`
     * input: plugin-hostd-pin_set-full */
    if (call->nargs != 4 || strcmp(call->args[3], verdict))
        abort();
}

/* the words property: every call of the message took the words g_call_words places in it, and the words the harness
 * works out for add, chain and pin_set */
__attribute__((noinline)) static void check_words(const struct words *w)
{
    char number[16], *line;
    size_t len;
    int read = w->n < PHD_LINE_WORDS_MAX ? w->n : PHD_LINE_WORDS_MAX, c;

    line = joined(w, &len);
    for (c = 0; c < g_rec.ncalls; c++)
    {
        const struct rec_call *call = &g_rec.calls[c];
        const char *item = g_call_words[call->fn] ? g_call_words[call->fn] : "";
        int a;

        for (a = 0; a < call->nargs && *item; a++)
        {
            const char *want;
            int k;

            item += strspn(item, " ");
            if (*item == '*')
                want = NULL;
            else if (*item == 'L')
                want = line;
            else
            {
                k = atoi(item + (*item == '#' || *item == '?'));
                if (*item == '?' && k >= read)
                    want = NULL;
                else if (k >= read)
                    want = "";
                else if (*item == '#')
                {
                    snprintf(number, sizeof(number), "%d", atoi(w->w[k]));
                    want = number;
                }
                else
                    want = w->w[k];
            }
            item += strcspn(item, " ");
            /* the argument is the word the declaration puts there, as the controller wrote it
             * mutant: src/verbs.c:142 `atoi(tok[2])` -> `atoi(tok[1])`
             * input: add-instance-past-the-table */
            if (want && (call->args[a] == NULL || strcmp(call->args[a], want)))
                abort();
        }
        if (call->fn == REC_ADD)
            check_words_add(call, (const char *const *)w->w, read);
        else if (call->fn == REC_CHAIN)
            check_words_chain(call, (const char *const *)w->w, read);
        else if (call->fn == REC_PINS_SET)
            check_words_pin_set(call, (const char *const *)w->w, read);
    }
    free(line);
}

/* the refusal property */
__attribute__((noinline)) static void check_refusal(uint64_t before)
{
    if (g_rec.reply == NULL || sup_reply_code(g_rec.reply) >= 0)
        return;
    /* nothing changed: no accepted call, no follow-up, no quit
     * mutant: src/verbs.c:144 `reply_text && sup_reply_code(reply_text) >= 0` -> `reply_text`
     * input: add-instance-past-the-table */
    if (g_rec.state != before || g_quitting)
        abort();
}

/* the round-trip property: the message has been sent, and the daemon acted on it */
__attribute__((noinline)) static void check_round_trip(const struct words *w, uint64_t state_before,
                                                       uint64_t host_before)
{
    struct rec_call first[REC_CALLS_MAX];
    int nfirst, quit_first;
    uint64_t state_first, host_first;
    char *reply_first, *line;
    size_t len;

    if (w->n == 0 || !acted())
        return;
    nfirst = rec_calls_copy(first);
    quit_first = g_quitting;
    state_first = g_rec.state;
    host_first = g_rec.host_settings;
    reply_first = strdup(g_rec.reply);
    /* not a property: the harness got no memory for its copy of the first reply */
    if (!reply_first)
        abort();

    /* the same command again, from the state it was sent in, as its words joined by one space */
    g_rec.state = state_before;
    g_rec.host_settings = host_before;
    line = joined(w, &len);
    send_message((const uint8_t *)line, len);
    free(line);

    /* the same calls with the same arguments
     * mutant: src/verbs.c:226 `strtok_r(copy, " \t", &save)` -> `strtok_r(copy, " ", &save)`
     * input: mod-host-add-tabs */
    if (!rec_calls_equal(first, nfirst, g_rec.calls, g_rec.ncalls))
        abort();
    /* the same reply
     * mutant: src/verbs.c:200 `ntok != 1` -> `ntok != 1 || line[0] != ' '`
     * input: quit-leading-space */
    if (g_rec.reply == NULL || strcmp(g_rec.reply, reply_first))
        abort();
    /* the same state, the same host settings, and quitting the same
     * mutant: src/verbs.c:202 `g_quitting = 1;` -> `g_quitting = line[0] == ' ';`
     * input: quit-leading-space */
    if (g_quitting != quit_first || g_rec.state != state_first || g_rec.host_settings != host_first)
        abort();
    rec_calls_free(first, nfirst);
    free(reply_first);
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
    struct fuzz_in in;
    int m;

    if (size >= FUZZ_INPUT_MAX)
        return 0;
    in = fuzz_in(data, size);
    rec_clear();
    g_rec.state = 0;
    g_rec.host_settings = 0;
    for (m = 0; m < MESSAGES_MAX && in.n; m++)
    {
        uint8_t flags = fuzz_u8(&in);
        uint16_t want = fuzz_u16(&in);
        const uint8_t *bytes;
        size_t len = fuzz_take(&in, want < MESSAGE_MAX ? want : MESSAGE_MAX, &bytes);
        uint64_t state_before = g_rec.state, host_before = g_rec.host_settings;
        struct words w;

        g_rec.refuse = flags & 1;
        g_rec.code = rec_codes[(flags >> 1) % rec_ncodes];
        send_message(bytes, len);
        words_of((const char *)bytes, len, &w);
        check_reply(&w);
        check_arity(&w);
        check_words(&w);
        check_refusal(state_before);
        check_round_trip(&w, state_before, host_before);
        words_free(&w);
    }
    rec_clear();
    g_quitting = 0;
    return 0;
}
