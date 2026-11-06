// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>

/* libFuzzer harness: THE OPERATOR'S OVERRIDE FILE (src/reac_segconf.c), the hand-written
 * `reac-pw.conf` and the drop-ins of `reac-pw.conf.d/` that pin, switch off or declare a
 * box on a segment, and the VLAN segments the file declares (src/reac_declared_vlan.c).
 *
 * Input:  [0] the capacity of the declared-VLAN table, mod 40;
 *         [1] flags: bit 0 the table already holds enp1s0.33;
 *         [2] the number of files, 1 + mod 4; then each file [label][u16 len][text]:
 *             every file but the last is a drop-in read with reac_segconf_parse_file
 *             under its label (0 none, which reads as the hand-written file; with bit 7 a
 *             label of 120 bytes; else "reac-pw.conf.d/<label>-x.conf"); the last is read
 *             with reac_segconf_parse, as the hand-written file, which then judges the
 *             keys that depend on each other. A text is cut at its first NUL.
 *
 * The expectations come from the grammar the header and the reader's comments document,
 * read here line by line on the harness's own copy (src/reac_segconf.h:4-37, 46-115,
 * 152-164, 227-229; src/reac_segconf.c:25-119, 269-303):
 *   - a line ends at '\n'; one of 512 bytes or more is refused whole, and one that
 *     opens a section ends the section before it; a '#' or ';' at the start or after a
 *     blank starts a comment; blanks are spaces, tabs and CRs;
 *   - `[segment <name>]` opens a section (the keyword in any case, then a blank); a
 *     header not closed, with text after its ']', of another keyword, with no name or a
 *     name of IFNAMSIZ bytes or more, or past REAC_SEGCONF_MAX segments is refused and
 *     ends the section; a header repeated in one file is refused and merged, across
 *     files it is an override;
 *   - `key = value`, the value without one pair of matching quotes, inside a section:
 *     role (auto|master|slave|tap|box, in any case), model (a token of the box-model
 *     table, in any case, folded), ignore (yes|true|1 or no|false|0, in any case for the
 *     words); a `knock` line is refused whatever its value (the knock takes no plan since
 *     1.0.41, reac-pw#61), and so is any other key; the last file to say a key wins it,
 *     and names it;
 *   - once every file is read: a model on a segment that is not a box is refused and
 *     dropped, a box with no model is refused and falls back to auto;
 *   - every refusal is counted, the first REAC_SEGCONF_REFUSALS kept, each addressed
 *     `<file>:<line>: ` (`<file>: ` for the cross-key ones);
 *   - a segment `<parent>.<vid>` that is not ignored declares that VLAN: a vid of digits
 *     from 1 to 4094, a parent of letters, digits, '.', '-', ':' and '_'.
 *
 * Properties, each an abort():
 *   - the segments are the names the sections opened, in order, and the overflow is the
 *     count of those past the bound;
 *   - each segment's role, model and ignore are the last ones its files gave it, after
 *     the cross-key rules;
 *   - each answer names the file that gave it;
 *   - every refusal is counted and the first ones kept, each with its address;
 *   - a name no section opened has no answer;
 *   - and the declared VLANs are those of the segments, each once, within the table. */
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "reac_declared_vlan.h"
#include "reac_segconf.h"

#include "catalogue.h"
#include "fuzz.h"

/* contract: src/reac_segconf.h:49 (32 segments), :53-54 (8 refusals kept, 200 bytes), :79
 * (a file label of 96 bytes), :59 (the hand-written file) */
#define SEGS_MAX      32
#define KEPT_MAX      8
#define LABEL_LEN     96
#define BASE_FILE     "reac-pw.conf"
/* contract: src/reac_segconf.c:135 (a line buffer of 512 bytes: 511 and a NUL) */
#define LINE_MAX_     512
/* contract: linux/if.h IFNAMSIZ (16) */
#define NAME_LEN      16
/* contract: src/reac_declared_vlan.h:23 (32 declared VLANs) is the daemon's bound; the
 * harness gives the table its own capacity, and src/reac_declared_vlan.h:35-38 (1 added,
 * 0 a duplicate, -1 full) */
#define VLAN_CAP_MAX  40

#define FILES_MAX     4

/* ---- the harness's reading of the grammar --------------------------------------------- */

struct mseg {
	char name[NAME_LEN];
	enum reac_role_intent role;
	int role_set, ignore, ignore_set, model_set;
	char model[24];
	char role_file[LABEL_LEN], ignore_file[LABEL_LEN];
	int gen;
};

struct mconf {
	struct mseg seg[SEGS_MAX];
	int n;
	unsigned overflow, refused;
	char kept[KEPT_MAX][LABEL_LEN + 16];   /* the address each kept refusal starts with */
	int kept_knock[KEPT_MAX];              /* the kept refusal was a `knock` line */
	int n_kept;
	int gen;
	char reading[LABEL_LEN];
};

static void m_refuse(struct mconf *c, int line)
{
	if (c->n_kept < KEPT_MAX) {
		if (line > 0)
			snprintf(c->kept[c->n_kept], sizeof c->kept[0], "%s:%d: ", c->reading, line);
		else
			snprintf(c->kept[c->n_kept], sizeof c->kept[0], "%s: ", c->reading);
		c->n_kept++;
	}
	c->refused++;
}

static int blank(char ch)
{
	return ch == ' ' || ch == '\t' || ch == '\r';
}

/* [s, e) without the blanks at either end */
static void strip(const char **s, const char **e)
{
	while (*s < *e && blank(**s))
		(*s)++;
	while (*e > *s && blank((*e)[-1]))
		(*e)--;
}

static int ieq(const char *s, size_t n, const char *word)
{
	size_t k = strlen(word);
	if (n != k)
		return 0;
	for (size_t i = 0; i < n; i++) {
		char a = s[i] >= 'A' && s[i] <= 'Z' ? (char)(s[i] - 'A' + 'a') : s[i];
		if (a != word[i])
			return 0;
	}
	return 1;
}

/* the value folded to lower case, its first `cap - 1` bytes */
static size_t fold(const char *s, size_t n, char *out, size_t cap)
{
	size_t k = n < cap - 1 ? n : cap - 1;
	for (size_t i = 0; i < k; i++)
		out[i] = s[i] >= 'A' && s[i] <= 'Z' ? (char)(s[i] - 'A' + 'a') : s[i];
	out[k] = '\0';
	return k;
}

static struct mseg *m_find(struct mconf *c, const char *name, size_t n)
{
	for (int i = 0; i < c->n; i++)
		if (strlen(c->seg[i].name) == n && memcmp(c->seg[i].name, name, n) == 0)
			return &c->seg[i];
	return NULL;
}

/* One header line [s, e), '[' first: the section it opens, or NULL. */
static struct mseg *m_header(struct mconf *c, const char *s, const char *e, int line)
{
	const char *close = memchr(s, ']', (size_t)(e - s));
	if (!close || close + 1 != e) {
		m_refuse(c, line);   /* not closed, or text after the ']' */
		return NULL;
	}
	const char *b = s + 1, *be = close;
	strip(&b, &be);
	if (be - b < 8 || !ieq(b, 7, "segment") || (b[7] != ' ' && b[7] != '\t')) {
		m_refuse(c, line);
		return NULL;
	}
	const char *nm = b + 7, *ne = be;
	strip(&nm, &ne);
	size_t n = (size_t)(ne - nm);
	if (n == 0 || n >= NAME_LEN) {
		m_refuse(c, line);
		return NULL;
	}
	struct mseg *g = m_find(c, nm, n);
	if (!g) {
		if (c->n >= SEGS_MAX) {
			c->overflow++;
			m_refuse(c, line);
			return NULL;
		}
		g = &c->seg[c->n++];
		memset(g, 0, sizeof *g);
		memcpy(g->name, nm, n);
	} else if (g->gen == c->gen) {
		m_refuse(c, line);   /* repeated in this file: merged */
	}
	g->gen = c->gen;
	return g;
}

/* One `key = value` line [s, e) of section g. */
static void m_key(struct mconf *c, struct mseg *g, const char *s, const char *e, int line)
{
	const char *eq = memchr(s, '=', (size_t)(e - s));
	if (!eq || !g) {
		m_refuse(c, line);
		return;
	}
	const char *k = s, *ke = eq, *v = eq + 1, *ve = e;
	strip(&k, &ke);
	strip(&v, &ve);
	if (ve - v >= 2 && (*v == '"' || *v == '\'') && ve[-1] == *v) {
		v++;
		ve--;
	}
	size_t kn = (size_t)(ke - k), vn = (size_t)(ve - v);
	char low[64];
	if (ieq(k, kn, "role")) {
		static const char *const words[] = { "auto", "master", "slave", "tap", "box" };
		static const enum reac_role_intent role[] = {
			REAC_ROLE_INTENT_AUTO, REAC_ROLE_INTENT_MASTER, REAC_ROLE_INTENT_SLAVE,
			REAC_ROLE_INTENT_TAP, REAC_ROLE_INTENT_BOX,
		};
		size_t ln = fold(v, vn, low, 64);
		for (int i = 0; i < 5; i++)
			if (strlen(words[i]) == ln && memcmp(words[i], low, ln) == 0) {
				g->role = role[i];
				g->role_set = 1;
				snprintf(g->role_file, sizeof g->role_file, "%s", c->reading);
				return;
			}
		m_refuse(c, line);
	} else if (ieq(k, kn, "model")) {
		size_t ln = fold(v, vn, low, 24);
		if (!fuzz_catalogue_row(low, ln)) {
			m_refuse(c, line);
			return;
		}
		memcpy(g->model, low, ln + 1);
		g->model_set = 1;
	} else if (ieq(k, kn, "ignore")) {
		int b;
		if (ieq(v, vn, "yes") || ieq(v, vn, "true") || (vn == 1 && *v == '1'))
			b = 1;
		else if (ieq(v, vn, "no") || ieq(v, vn, "false") || (vn == 1 && *v == '0'))
			b = 0;
		else {
			m_refuse(c, line);
			return;
		}
		g->ignore = b;
		g->ignore_set = 1;
		snprintf(g->ignore_file, sizeof g->ignore_file, "%s", c->reading);
	} else if (ieq(k, kn, "knock")) {
		/* refused whatever the value: the knock takes no plan (reac-pw#61) */
		if (c->n_kept < KEPT_MAX)
			c->kept_knock[c->n_kept] = 1;
		m_refuse(c, line);
	} else {
		m_refuse(c, line);
	}
}

static void m_file(struct mconf *c, const char *text, const char *label)
{
	snprintf(c->reading, sizeof c->reading, "%s", label ? label : BASE_FILE);
	c->gen++;
	struct mseg *cur = NULL;
	int line = 0;
	const char *p = text;
	while (*p) {
		const char *nl = strchr(p, '\n');
		const char *s = p, *e = nl ? nl : p + strlen(p);
		p = nl ? nl + 1 : e;
		line++;
		if (e - s >= LINE_MAX_) {
			const char *f = s;
			while (f < e && blank(*f))
				f++;
			if (f < e && *f == '[')
				cur = NULL;
			m_refuse(c, line);
			continue;
		}
		for (const char *q = s; q < e; q++)
			if ((*q == '#' || *q == ';') && (q == s || q[-1] == ' ' || q[-1] == '\t')) {
				e = q;
				break;
			}
		strip(&s, &e);
		if (s == e)
			continue;
		if (*s == '[')
			cur = m_header(c, s, e, line);
		else
			m_key(c, cur, s, e, line);
	}
}

/* The rules that need every file read. */
static void m_cross(struct mconf *c)
{
	for (int i = 0; i < c->n; i++) {
		struct mseg *g = &c->seg[i];
		int box = g->role_set && g->role == REAC_ROLE_INTENT_BOX;
		if (g->model_set && !box) {
			m_refuse(c, 0);
			g->model_set = 0;
		} else if (box && !g->model_set) {
			m_refuse(c, 0);
			g->role_set = 0;
			g->role = REAC_ROLE_INTENT_AUTO;
		}
	}
}

/* ---- the declared VLANs ------------------------------------------------------------------ */

struct mvlan {
	char parent[NAME_LEN];
	unsigned vid;
};

/* `<parent>.<vid>`: the last '.', digits after it from 1 to 4094, and a parent of the
 * characters a netdev name the daemon hands to rtnetlink may hold.
 * contract: src/reac_declared_vlan.h:26-33 (split at the LAST dot; the tail digits or not a
 * VID), src/reac_declared_vlan.c:16-19 (letters, digits, '.', '-', ':' and '_') */
static int m_split(const char *name, struct mvlan *v)
{
	const char *dot = strrchr(name, '.');
	if (!dot || dot == name || !dot[1])
		return 0;
	unsigned long vid = 0;
	for (const char *q = dot + 1; *q; q++) {
		if (*q < '0' || *q > '9')
			return 0;
		vid = vid * 10 + (unsigned long)(*q - '0');
		if (vid > 4094)
			return 0;
	}
	if (vid < 1)
		return 0;
	size_t pn = (size_t)(dot - name);
	for (size_t i = 0; i < pn; i++) {
		char ch = name[i];
		int ok = (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || (ch >= '0' && ch <= '9') ||
		         ch == '.' || ch == '-' || ch == ':' || ch == '_';
		if (!ok)
			return 0;
	}
	memcpy(v->parent, name, pn);
	v->parent[pn] = '\0';
	v->vid = (unsigned)vid;
	return 1;
}

/* What reac_segconf_declared owes a table of `cap` holding `n` entries. */
static int m_declared(const struct mconf *c, struct mvlan *tab, int cap, int *n)
{
	int added = 0;
	for (int i = 0; i < c->n; i++) {
		struct mvlan v;
		if (c->seg[i].ignore || !m_split(c->seg[i].name, &v))
			continue;
		int dup = 0;
		for (int k = 0; k < *n; k++)
			dup |= tab[k].vid == v.vid && strcmp(tab[k].parent, v.parent) == 0;
		if (dup)
			continue;
		if (*n >= cap)
			return -1;
		tab[(*n)++] = v;
		added++;
	}
	return added;
}

/* The table the reader wrote against the one the model wrote, and the guard entry after
 * the capacity as the harness left it. */
static int vlans_are(int got, int want, const struct reac_declared_vlan *tab, int n,
                     const struct mvlan *mt, int mn, int cap)
{
	if (got != want || n != mn)
		return 0;
	for (int i = 0; i < n; i++)
		if (tab[i].vid != mt[i].vid || strcmp(tab[i].parent, mt[i].parent) != 0)
			return 0;
	const uint8_t *g = (const uint8_t *)&tab[cap];
	for (size_t i = 0; i < sizeof tab[cap]; i++)
		if (g[i] != 0x5a)
			return 0;
	return 1;
}

/* ---- the checks ------------------------------------------------------------------------ */

static int segments_are(const struct reac_segconf *c, const struct mconf *m)
{
	if (c->n != m->n || c->overflow != m->overflow)
		return 0;
	for (int i = 0; i < m->n; i++)
		if (strcmp(c->seg[i].name, m->seg[i].name) != 0)
			return 0;
	return 1;
}

static int same_text(const char *got, const char *want)
{
	return got == want || (got && want && strcmp(got, want) == 0);
}

static FUZZ_NOINLINE void check_segments(const struct reac_segconf *c, const struct mconf *m,
                                         int returned)
{
	/* The segments are the names the sections opened, each once, in the order first
	 * opened; a section past the bound is counted as overflow and opens nothing.
	 * contract: src/reac_segconf.h:46-49, 85-89, src/reac_segconf.c:102-119, 155-157
	 * mutant: src/reac_segconf.c:107 `strcmp(c->seg[i].name, name) == 0` -> `strcasecmp(c->seg[i].name, name) == 0`
	 * input: names-differ-in-case
	 * mutant: src/reac_segconf.c:110 `c->overflow++;` -> ``
	 * input: thirty-three-segments
	 * mutant: src/reac_segconf.c:177 `strncasecmp(body, "segment", 7)` -> `strncmp(body, "segment", 7)`
	 * input: keyword-in-capitals
	 * mutant: src/reac_segconf.c:178 `body[7] != ' ' && body[7] != '\t'` -> `body[7] != ' '`
	 * input: tab-after-keyword
	 * mutant: src/reac_segconf.c:168 `if (close[1])` -> `if (0)`
	 * input: text-after-header
	 * mutant: src/reac_segconf.c:295 `return c->n;` -> `return 0;`
	 * input: operator-file
	 * mutant: src/reac_segconf.c:331 `return n;` -> `return 0;`
	 * input: operator-file */
	if (!segments_are(c, m) || !returned)
		abort();
}

static FUZZ_NOINLINE void check_role(int got_set, enum reac_role_intent got,
                                     const struct mseg *want)
{
	/* A segment's role is the last one its files pinned, a value of the vocabulary in any
	 * case and without its quotes; a box that names no model falls back to no pin.
	 * contract: src/reac_segconf.h:203-208, src/reac_segconf.c:271-316
	 * mutant: src/reac_segconf.c:237 `(char)(*q - 'A' + 'a')` -> `*q`
	 * input: role-in-capitals
	 * mutant: src/reac_segconf.c:244 `cur->role = i;` -> `cur->role = REAC_ROLE_INTENT_MASTER;`
	 * input: operator-file
	 * mutant: src/reac_segconf.c:321 `s->role_set = 0;` -> ``
	 * input: box-without-model
	 * mutant: src/reac_segconf.c:307 `s->role == REAC_ROLE_INTENT_BOX` -> `1`
	 * input: operator-file
	 * mutant: src/reac_segconf.c:223 `unquote(trim(eq + 1))` -> `trim(eq + 1)`
	 * input: operator-file
	 * mutant: src/reac_segconf.c:146 `cur = NULL;` -> ``
	 * input: long-header-line
	 * mutant: src/reac_segconf.c:190 `strlen(name) >= IFNAMSIZ` -> `strlen(name) > IFNAMSIZ`
	 * input: name-sixteen
	 * mutant: src/reac_segconf.c:255 `(char)(*q - 'A' + 'a')` -> `*q`
	 * input: model-in-capitals */
	if (got_set != want->role_set || (got_set && got != want->role))
		abort();
}

static FUZZ_NOINLINE void check_model(const char *got, const struct mseg *want)
{
	/* A segment's model is a token of the box-model table, folded to lower case, and
	 * only on a segment whose role is box; on any other role it is dropped.
	 * contract: src/reac_segconf.h:92-101, 221-225
	 * mutant: src/reac_segconf.c:308 `s->model_set && !is_box` -> `0`
	 * input: model-on-a-tap
	 * mutant: src/reac_segconf.c:268 `"%s", low` -> `"%s", val`
	 * input: model-in-capitals */
	if (!same_text(got, want->model_set ? want->model : NULL))
		abort();
}

static FUZZ_NOINLINE void check_ignore(int got, const struct mseg *want)
{
	/* A segment is switched off when the last file to say `ignore` said yes, true or 1,
	 * and on when it said no, false or 0.
	 * contract: src/reac_segconf.h:89, 199-201
	 * mutant: src/reac_segconf.c:90 `!strcmp(v, "1")` -> `!strcmp(v, "0")`
	 * input: ignore-words
	 * mutant: src/reac_segconf.c:278 `cur->ignore = b;` -> `cur->ignore = 1;`
	 * input: ignore-words
	 * mutant: src/reac_segconf.c:530 `s && s->ignore` -> `s != NULL`
	 * input: ignore-words */
	if (got != want->ignore)
		abort();
}

static FUZZ_NOINLINE void check_provenance(const char *role_file, const char *ignore_file,
                                           const struct mseg *want)
{
	/* Each answer names the file that gave it, per key: the hand-written file or the
	 * drop-in, and nothing when no file said that key.
	 * contract: src/reac_segconf.h:108-113, 210-219
	 * mutant: src/reac_segconf.c:246 `c->reading` -> `REAC_SEGCONF_FILE`
	 * input: dropin-overrides
	 * mutant: src/reac_segconf.c:280 `c->reading` -> `REAC_SEGCONF_FILE`
	 * input: dropin-overrides
	 * mutant: src/reac_segconf.c:122 `label ? label : REAC_SEGCONF_FILE` -> `REAC_SEGCONF_FILE`
	 * input: dropin-overrides */
	if (!same_text(role_file, want->role_set ? want->role_file : NULL) ||
	    !same_text(ignore_file, want->ignore_set ? want->ignore_file : NULL))
		abort();
}

static FUZZ_NOINLINE void check_knock_refused(const char *got, int was_knock)
{
	/* A `knock` line is refused by name with the reason, whatever its value: the knock
	 * takes no plan since 1.0.41, and a word in a file must not be able to select the
	 * stream (reac-pw#61). The refusal says so.
	 * contract: src/reac_segconf.c (the `knock` branch: refused, with "takes no plan")
	 * mutant: src/reac_segconf.c:286 `takes no plan` -> `takes a plan`
	 * input: knock-plans
	 * mutant: src/reac_segconf.c:286 `takes no plan` -> `takes a plan`
	 * input: knock-long-value */
	if (was_knock && !strstr(got, "takes no plan"))
		abort();
}

static FUZZ_NOINLINE void check_refusals(const struct reac_segconf *c, const struct mconf *m)
{
	/* Every line the grammar cannot use is refused and counted, and the first ones are
	 * kept.
	 * contract: src/reac_segconf.h:30-34, 51-54, 132-134
	 * mutant: src/reac_segconf.c:32 `c->refused++;` -> ``
	 * input: refusals-many
	 * mutant: src/reac_segconf.c:207 `!is_new && cur->seen_gen == c->gen` -> `0`
	 * input: header-twice-in-one-file
	 * mutant: src/reac_segconf.c:33 `c->n_refusals >= REAC_SEGCONF_REFUSALS` -> `c->n_refusals >= REAC_SEGCONF_REFUSALS - 1`
	 * input: refusals-many */
	if (c->refused != m->refused || c->n_refusals != m->n_kept)
		abort();
}

static FUZZ_NOINLINE void check_address(const char *got, const char *want)
{
	/* A kept refusal starts with its address: the file and the line, or the file alone
	 * for a rule that needed every file read.
	 * contract: src/reac_segconf.c:37-41 (the file is part of the address)
	 * mutant: src/reac_segconf.c:39 `where, line)` -> `where, line + 1)`
	 * input: refusals-many
	 * mutant: src/reac_segconf.c:38 `c->reading[0] ? c->reading : REAC_SEGCONF_FILE` -> `REAC_SEGCONF_FILE`
	 * input: dropin-refusal */
	if (strncmp(got, want, strlen(want)) != 0)
		abort();
}

static FUZZ_NOINLINE void check_absent(const struct reac_segconf *c, const char *name)
{
	/* A name no section opened has no entry and no answer.
	 * contract: src/reac_segconf.h:194-197 (the entry for `name`, or NULL; compared case
	 * sensitively)
	 * mutant: src/reac_segconf.c:522 `strcmp(c->seg[i].name, name) == 0` -> `strncmp(c->seg[i].name, name, 4) == 0`
	 * input: absent-probes */
	if (reac_segconf_find(c, name) || reac_segconf_role(c, name, NULL) ||
	    reac_segconf_ignored(c, name) || reac_segconf_model(c, name))
		abort();
}

static FUZZ_NOINLINE void check_declared(int got, int want, const struct reac_declared_vlan *tab,
                                         int n, const struct mvlan *mt, int mn, int cap)
{
	/* The declared VLANs are the segments named `<parent>.<vid>` that are not switched
	 * off, each (parent, vid) once, added after what the table held; a full table stops
	 * the declaration at -1, and nothing is written past it.
	 * contract: src/reac_segconf.h:231-238, src/reac_declared_vlan.h:26-38
	 * mutant: src/reac_declared_vlan.c:46 `v > 4094` -> `v > 4095`
	 * input: vlans
	 * mutant: src/reac_declared_vlan.c:43 `!isdigit((unsigned char)*p)` -> `!isalnum((unsigned char)*p)`
	 * input: vlans
	 * mutant: src/reac_declared_vlan.c:71 `strcmp(tab[i].parent, parent) == 0` -> `1`
	 * input: vlans
	 * mutant: src/reac_declared_vlan.c:73 `*n >= max` -> `*n > max`
	 * input: vlans-full
	 * mutant: src/reac_segconf.c:568 `if (c->seg[i].ignore)` -> `if (0)`
	 * input: vlans
	 * mutant: src/reac_declared_vlan.c:58 `!name_ok(parent)` -> `0`
	 * input: vlans */
	if (!vlans_are(got, want, tab, n, mt, mn, cap))
		abort();
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	if (size >= FUZZ_INPUT_MAX)
		return 0;
	struct fuzz_in in = fuzz_in(data, size);
	int cap = fuzz_u8(&in) % VLAN_CAP_MAX;
	uint8_t flags = fuzz_u8(&in);
	int nfiles = 1 + fuzz_u8(&in) % FILES_MAX;
	struct reac_segconf *c = malloc(sizeof *c);
	struct mconf *m = calloc(1, sizeof *m);
	/* not a property: the harness's own allocation failed */
	if (!c || !m)
		abort();
	reac_segconf_init(c);

	static char longl[121];
	/* each parse returns the running number of segments (src/reac_segconf.h:156-160) */
	int returned = 1;
	for (int f = 0; f < nfiles; f++) {
		uint8_t lb = fuzz_u8(&in);
		const uint8_t *p;
		size_t n = fuzz_take(&in, fuzz_u16(&in), &p);
		char *text = fuzz_str(p, n);
		char label[40];
		const char *l = NULL;
		if (lb & 0x80) {
			memset(longl, 'L', 120);
			l = longl;
		} else if (lb) {
			snprintf(label, sizeof label, "reac-pw.conf.d/%u-x.conf", lb);
			l = label;
		}
		if (f + 1 < nfiles) {
			m_file(m, text, l);
			returned &= reac_segconf_parse_file(c, text, l) == m->n;
		} else {
			m_file(m, text, NULL);
			m_cross(m);
			returned &= reac_segconf_parse(c, text) == m->n;
		}
		free(text);
	}

	check_segments(c, m, returned);
	for (int i = 0; i < m->n; i++) {
		const struct mseg *g = &m->seg[i];
		enum reac_role_intent r = (enum reac_role_intent)0x5a;
		int set = reac_segconf_role(c, g->name, &r);
		check_role(set, r, g);
		check_model(reac_segconf_model(c, g->name), g);
		check_ignore(reac_segconf_ignored(c, g->name), g);
		check_provenance(reac_segconf_role_file(c, g->name),
		                 reac_segconf_ignore_file(c, g->name), g);
	}
	check_refusals(c, m);
	for (int i = 0; i < m->n_kept && i < c->n_refusals; i++) {
		check_address(c->refusal[i], m->kept[i]);
		check_knock_refused(c->refusal[i], m->kept_knock[i]);
	}
	/* names no section opened: each segment's with a byte more, and one never named */
	for (int i = 0; i < m->n; i++) {
		char probe[NAME_LEN + 2];
		snprintf(probe, sizeof probe, "%sx", m->seg[i].name);
		if (!m_find(m, probe, strlen(probe)))
			check_absent(c, probe);
	}
	if (!m_find(m, "nosuch0", 7))
		check_absent(c, "nosuch0");

	/* the declared VLANs, into a table of `cap` and one guard entry */
	struct reac_declared_vlan *tab = calloc((size_t)cap + 1, sizeof *tab);
	struct mvlan *mt = calloc((size_t)cap + 1, sizeof *mt);
	/* not a property: the harness's own allocation failed */
	if (!tab || !mt)
		abort();
	memset(&tab[cap], 0x5a, sizeof tab[cap]);
	int n = 0, mn = 0;
	if ((flags & 1) && cap > 0) {
		snprintf(tab[0].parent, sizeof tab[0].parent, "enp1s0");
		tab[0].vid = 33;
		snprintf(mt[0].parent, sizeof mt[0].parent, "enp1s0");
		mt[0].vid = 33;
		n = mn = 1;
	}
	int want = m_declared(m, mt, cap, &mn);
	int got = reac_segconf_declared(c, tab, cap, &n);
	check_declared(got, want, tab, n, mt, mn, cap);

	free(mt);
	free(tab);
	free(m);
	free(c);
	return 0;
}
