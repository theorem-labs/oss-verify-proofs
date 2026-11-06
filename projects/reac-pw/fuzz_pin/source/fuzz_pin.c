// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>

/* libFuzzer harness: THE `--box MODEL[:LABEL]` PIN (src/reac_box_pin.c), the operator's
 * text that names a box before the wire has said anything.
 *
 * Input:  [0] flags: bit 0 hands the reader a NULL spec, bit 1 a NULL model out, bit 2 a
 *             NULL label out;
 *         [1..] the spec, as a C string (cut at its first NUL), in its own allocation.
 *
 * The expectations come from the pin's grammar (src/reac_box_pin.h:42-54): the token is
 * everything before the FIRST ':', it names a model only when it is a whole token of the
 * box-model table (fuzz/catalogue.c), and the label is what follows that ':' when it is
 * not empty, else the model's display name.
 *
 * Properties, each an abort():
 *   - the pin is accepted exactly when the token is a whole model token;
 *   - an accepted pin names that model's row;
 *   - and the label it names is the text after the first ':', or the display name. */
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "reac_box_pin.h"

#include "catalogue.h"
#include "fuzz.h"

static FUZZ_NOINLINE void check_known(int rc, const struct reac_box_model *want)
{
	/* The pin is accepted exactly when the arguments are there, the spec is not empty, and
	 * the text before its first ':' is a whole token of the table: no prefix of a token and
	 * no token with more after it.
	 * contract: src/reac_box_pin.h:48-54 (matched WHOLE; refused on NULL, empty or unknown)
	 * mutant: src/reac_box_pin.c:33 `strlen(table[i].token) == toklen &&` -> ``
	 * input: prefix-s16
	 * mutant: src/reac_box_pin.c:20 `strcspn(spec, ":")` -> `strlen(spec)`
	 * input: s1608-left */
	if ((rc == 0) != (want != NULL))
		abort();
}

static FUZZ_NOINLINE void check_row(const struct reac_box_model *got,
                                    const struct reac_box_model *want)
{
	/* An accepted pin names the row of the table its token is, not another one.
	 * contract: src/reac_box_pin.h:42 (parse into a known box model)
	 * mutant: src/reac_box_pin.c:35 `found = &table[i];` -> `found = &table[0];`
	 * input: s0808 */
	if (got != want)
		abort();
}

static FUZZ_NOINLINE void check_label(const char *got, const char *want)
{
	/* The label is the text after the first ':' (colons after it are the label's own), in the
	 * spec itself; with nothing after the ':', or no ':', it is the model's display name.
	 * contract: src/reac_box_pin.h:44-46 (points into spec just past the first ':', or the
	 * model's display name when no usable label was given)
	 * mutant: src/reac_box_pin.c:42 `spec + toklen + 1` -> `spec + toklen`
	 * input: s1608-left
	 * mutant: src/reac_box_pin.c:44 `!label || !*label` -> `!label`
	 * input: s1608-empty-label
	 * mutant: src/reac_box_pin.c:45 `found->display` -> `found->token`
	 * input: s0808 */
	if (got != want)
		abort();
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
	if (size >= FUZZ_INPUT_MAX)
		return 0;
	struct fuzz_in in = fuzz_in(data, size);
	uint8_t flags = fuzz_u8(&in);
	const uint8_t *rest;
	size_t n = fuzz_take(&in, in.n, &rest);
	char *spec = fuzz_str(rest, n);
	size_t len = strlen(spec);

	/* The expectation, from the grammar alone. */
	size_t tok = 0;
	while (tok < len && spec[tok] != ':')
		tok++;
	const struct reac_box_model *want = NULL;
	if (!(flags & 7) && len)
		want = fuzz_catalogue_row(spec, tok);
	const char *want_label = NULL;
	if (want)
		want_label = (tok < len && spec[tok + 1]) ? spec + tok + 1 : want->display;

	const struct reac_box_model *model = NULL;
	const char *label = NULL;
	int rc = reac_box_pin_parse((flags & 1) ? NULL : spec, (flags & 2) ? NULL : &model,
	                            (flags & 4) ? NULL : &label);
	check_known(rc, want);
	if (rc == 0) {
		check_row(model, want);
		check_label(label, want_label);
	}
	free(spec);
	return 0;
}
