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

/* The declared syntax of include/plugin-hostd/protocol.h read as words, the way tools/protocol-gen.c writes it into
 * README.md and protocol/plugin-hostd.json: the arguments of a verb ("<uri> <instance> [own | pool:<name> | default]"),
 * the shape of its reply ("resp 0 <worker> <pid>"), and mod-host's command formats ("remove %i", "add %s %i ...").
 *
 * An item of a syntax is a run of characters with no space outside <...> and [...]. "a | b" at the top is one word
 * that is a or b; [...] is a word that may be left out, and one holding "..." may repeat without end. */

#ifndef PLUGIN_HOSTD_FUZZ_SYNTAX_H
#define PLUGIN_HOSTD_FUZZ_SYNTAX_H

#include <limits.h>
#include <stddef.h>
#include <string.h>

#define SYNTAX_UNBOUNDED INT_MAX

/* the item that starts at or after *s, its length in *len; NULL when there is none */
static inline const char *syntax_item(const char **s, size_t *len)
{
    const char *p = *s, *start;
    int depth = 0;

    while (*p == ' ')
        p++;
    if (!*p)
        return NULL;
    start = p;
    for (; *p && (depth > 0 || *p != ' '); p++)
    {
        if (*p == '<' || *p == '[')
            depth++;
        else if ((*p == '>' || *p == ']') && depth > 0)
            depth--;
    }
    *len = (size_t)(p - start);
    *s = p;
    return start;
}

static inline int syntax_has(const char *item, size_t len, const char *what)
{
    size_t n = strlen(what), i;

    for (i = 0; i + n <= len; i++)
        if (!memcmp(item + i, what, n))
            return 1;
    return 0;
}

/* the fewest and the most words a declared argument syntax takes */
static inline void syntax_arity(const char *syntax, int *min, int *max)
{
    const char *s = syntax, *item;
    size_t len;

    *min = *max = 0;
    while ((item = syntax_item(&s, &len)))
    {
        if (len == 1 && *item == '|')
        {
            /* the alternative of the word before it: no word of its own */
            syntax_item(&s, &len);
            continue;
        }
        if (item[0] == '[' && item[len - 1] == ']')
        {
            if (syntax_has(item, len, "..."))
                *max = SYNTAX_UNBOUNDED;
            else if (*max != SYNTAX_UNBOUNDED)
                (*max)++;
            continue;
        }
        (*min)++;
        if (*max != SYNTAX_UNBOUNDED)
            (*max)++;
    }
}

/* the fewest and the most arguments of a mod-host command format, "<verb> %i %s ...": a %-word each, "..." for a tail
 * of any length */
static inline void syntax_format_arity(const char *format, int *min, int *max)
{
    const char *s = format, *item;
    size_t len;

    *min = *max = 0;
    syntax_item(&s, &len);
    while ((item = syntax_item(&s, &len)))
    {
        if (len == 3 && !memcmp(item, "...", 3))
            *max = SYNTAX_UNBOUNDED;
        else
        {
            (*min)++;
            if (*max != SYNTAX_UNBOUNDED)
                (*max)++;
        }
    }
}

/* a reply of the declared shape: the template with every <...> written as 1, into buf; the length, or -1 when it does
 * not fit */
static inline int syntax_instantiate(const char *shape, char *buf, size_t size)
{
    size_t o = 0;
    int depth = 0;

    for (; *shape; shape++)
    {
        char c = *shape;

        if (c == '<')
        {
            if (depth++ == 0)
                c = '1';
            else
                continue;
        }
        else if (c == '>' && depth > 0)
        {
            depth--;
            continue;
        }
        else if (depth > 0)
            continue;
        if (o + 1 >= size)
            return -1;
        buf[o++] = c;
    }
    buf[o] = '\0';
    return (int)o;
}

/* whether a reply has the declared shape: as many words as the shape has items, each literal item spelled the same, an
 * item holding a <...> standing for any one word */
static inline int syntax_reply_matches(const char *shape, const char *reply)
{
    const char *s = shape, *item;
    size_t len;

    while ((item = syntax_item(&s, &len)))
    {
        size_t w = strcspn(reply, " ");

        if (w == 0)
            return 0;
        if (!syntax_has(item, len, "<") && (w != len || memcmp(item, reply, len)))
            return 0;
        reply += w;
        if (*reply == ' ' && reply[1])
            reply++;
        else if (*reply)
            return 0;
    }
    return *reply == '\0';
}

#endif
