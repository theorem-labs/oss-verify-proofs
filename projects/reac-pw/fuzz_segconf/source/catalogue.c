// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Pau Aliagas <linuxnow@gmail.com>

/* The box-model table of fuzz/catalogue.h, and the two libreac lookups reac-pw calls,
 * over it. */
#include "catalogue.h"

#include <string.h>

/* contract: libreac 1.8.0 src/reac_ctrlblk.c:413-654, the BOX_CATALOGUE rows in order:
 * token, display, input and output widths. */
const struct reac_box_model fuzz_catalogue[] = {
	{ .token = "s1608", .display = "S-1608 (16 in / 8 out)", .in_ch = 16, .out_ch = 8 },
	{ .token = "s0808", .display = "S-0808 (8 in / 8 out)", .in_ch = 8, .out_ch = 8 },
	{ .token = "s4000s", .display = "S-4000S-3208 (32 in / 8 out)", .in_ch = 32, .out_ch = 8 },
	{ .token = "s4000s-0832", .display = "S-4000S-0832 (8 in / 32 out)", .in_ch = 8,
	  .out_ch = 32 },
	{ .token = "s0816", .display = "S-0816 (8 in / 16 out)", .in_ch = 8, .out_ch = 16 },
	{ .token = "s2416", .display = "S-2416 (24 in / 16 out)", .in_ch = 24, .out_ch = 16 },
	{ .token = "s4000d", .display = "S-4000D (0 in / 32 out)", .in_ch = 0, .out_ch = 32 },
	{ .token = "s4000m", .display = "S-4000M (32 in / 0 out)", .in_ch = 32, .out_ch = 0 },
	{ .token = "fr4000", .display = "FreeREAC 40 in / 0 out", .in_ch = 40, .out_ch = 0 },
	{ .token = "fr0040", .display = "FreeREAC 0 in / 40 out", .in_ch = 0, .out_ch = 40 },
	{ .token = "fr2020", .display = "FreeREAC 20 in / 20 out", .in_ch = 20, .out_ch = 20 },
};

const size_t fuzz_catalogue_n = sizeof fuzz_catalogue / sizeof fuzz_catalogue[0];

const struct reac_box_model *fuzz_catalogue_row(const char *s, size_t n)
{
	for (size_t i = 0; i < fuzz_catalogue_n; i++)
		if (strlen(fuzz_catalogue[i].token) == n && memcmp(fuzz_catalogue[i].token, s, n) == 0)
			return &fuzz_catalogue[i];
	return NULL;
}

/* contract: libreac 1.8.0 include/reac/reac_ctrlblk.h:537 (the table and its count) */
const struct reac_box_model *reac_box_catalogue(size_t *count)
{
	if (count)
		*count = fuzz_catalogue_n;
	return fuzz_catalogue;
}

/* contract: libreac 1.8.0 include/reac/reac_ctrlblk.h:535 and src/reac_ctrlblk.c:667-674
 * (the row whose token is equal, NULL for none or for a NULL token) */
const struct reac_box_model *reac_box_catalogue_by_token(const char *token)
{
	return token ? fuzz_catalogue_row(token, strlen(token)) : NULL;
}
