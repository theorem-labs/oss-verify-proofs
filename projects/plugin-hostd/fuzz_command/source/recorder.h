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

/* The mod-host side of the daemon, replaced by a recorder for fuzz/fuzz_command.c: every function src/verbs.c calls
 * below it (the supervisor, the pins, the descriptors, the LV2 refusals and the socket's send) is defined here. Each
 * records the call it was handed, answers with the reply its verb declares, or with the refusal the input chose, and
 * folds what an accepted call changes into a digest of the daemon's state. No socket, no process, no JACK, no file. */

#ifndef PLUGIN_HOSTD_FUZZ_RECORDER_H
#define PLUGIN_HOSTD_FUZZ_RECORDER_H

#include <stddef.h>
#include <stdint.h>

enum {
    REC_ADD, REC_CALL, REC_REMOVE, REC_REMOVE_ALL, REC_CONNECT, REC_BROADCAST, REC_HOST_SETTING, REC_INSTANCE_VERB,
    REC_WORKER_LIST, REC_INSTANCE_INFO, REC_RESET, REC_QUARANTINE_CLEAR, REC_POLICY_SET, REC_PIN_ACCEPT,
    REC_POOL_CONFIG, REC_LV2_WORKER_SET, REC_WORKER_ENV, REC_CHAIN, REC_CHAIN_CLEAR, REC_AFTER_REPLY, REC_PINS_SET,
    REC_PINS_CLEAR, REC_DESCRIPTORS_ADD, REC_DESCRIPTORS_GET, REC_DESCRIPTORS_PANEL_GET, REC_LV2_REFUSALS_FORGET,
    REC_FN_COUNT
};

#define REC_CALLS_MAX 16
#define REC_ARGS_MAX  6

/* one call, its arguments as text: a number as %d, a line as its words joined by one space */
struct rec_call {
    int fn;
    int nargs;
    char *args[REC_ARGS_MAX];
};

struct recorder {
    /* chosen by the input for the message: refuse every call that can refuse, with this declared code */
    int refuse;
    int code;

    /* what the message did */
    int ncalls;
    struct rec_call calls[REC_CALLS_MAX];
    char *answer;               /* the last answer of a call: a reply text of the supervisor or the descriptors, or
                                 * "resp <code>" of the code the pins returned; NULL when no call answered, since
                                 * sup_resp is the daemon's own reply and writes none */
    int nreplies;               /* socket_send calls */
    char *reply;                /* the bytes of the last one */
    size_t reply_size;

    /* the daemon's state: a digest of every change an accepted call made */
    uint64_t state;
    /* the host settings, which are kept as they were sent whatever the workers answer (PHD_HOST_SETTINGS) */
    uint64_t host_settings;
};

extern struct recorder g_rec;

/* the declared refusal codes: mod-host's (host-errors.h) and the daemon's own (PHD_ERRORS) */
extern const int rec_codes[];
extern const int rec_ncodes;
int rec_code_declared(int code);

/* mod-host answers a command it took "resp 0" */
#define REC_MOD_HOST_SHAPE "resp 0"

/* the declared reply shape of a verb of the daemon (PHD_VERBS, PHD_INSTANCE_VERBS), else mod-host's */
const char *rec_shape_of(const char *verb, size_t len);

/* forget what the last message did; the state stays */
void rec_clear(void);

/* whether two messages did the same: the same calls with the same arguments, in the same order */
int rec_calls_equal(const struct rec_call *a, int na, const struct rec_call *b, int nb);

/* a deep copy of the calls of the message, and its release */
int rec_calls_copy(struct rec_call *dst);
void rec_calls_free(struct rec_call *calls, int n);

/* the words of `text` up to `len` bytes, at spaces and tabs, joined by one space; malloc'd */
char *rec_canonical(const char *text, size_t len);

#endif
