// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>

/* THE BOX-MODEL TABLE THE HARNESSES LINK IN PLACE OF libreac's (fuzz/catalogue.c).
 *
 * reac-pw's config reader and its `--box` pin look a model token up in libreac's
 * catalogue (reac_box_catalogue, reac_box_catalogue_by_token). libreac is enrolled on its
 * own and its harnesses prove its tables; what these harnesses prove is reac-pw's USE of
 * a lookup. So the harness links this table, the rows of libreac 1.8.0 by token, display
 * and widths, and both the code under test and the harness's expectations read the same
 * rows: a token is a model exactly when it is one of these, byte for byte. No harness
 * links libreac itself, only its headers. */
#ifndef REACPW_FUZZ_CATALOGUE_H
#define REACPW_FUZZ_CATALOGUE_H

#include <stddef.h>

#include <reac/reac_ctrl.h>   /* struct reac_box_model */

extern const struct reac_box_model fuzz_catalogue[];
extern const size_t fuzz_catalogue_n;

/* The row whose token is the `n` bytes at s, or NULL: the harness's own lookup, a plain
 * whole-token compare, for the expectations. */
const struct reac_box_model *fuzz_catalogue_row(const char *s, size_t n);

#endif /* REACPW_FUZZ_CATALOGUE_H */
