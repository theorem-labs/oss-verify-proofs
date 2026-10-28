(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK AsanNodesExtraDefsK. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DefsK_b.
Import ListNotations. Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Definition as0_ranges : list (Z * nat) := [(0x51398, 102%nat); (0x51690, 85%nat); (0x53960, 395%nat); (0x54b70, 73%nat); (0x58200, 55%nat); (0x587b8, 62%nat); (0x5d430, 50%nat); (0x5dbf4, 16%nat); (0x5e4d0, 980%nat); (0x5feb8, 352%nat); (0x6054c, 12%nat); (0x60700, 251%nat); (0x612a0, 24%nat); (0x619f4, 176%nat); (0x61ed4, 17%nat); (0x626e0, 15%nat); (0x6324c, 108%nat); (0x6b08c, 35%nat); (0x6da98, 85%nat); (0x6e98c, 6626%nat); (0x77664, 91%nat); (0x77c80, 7%nat); (0x786d8, 134%nat); (0x78e88, 103%nat); (0x79478, 25%nat); (0x796a0, 91%nat); (0x7a08c, 5%nat); (0x7ab0c, 245%nat); (0x7b02c, 31%nat); (0x7b4b8, 109%nat); (0x7bee0, 145%nat); (0x801cc, 10%nat); (0x80964, 29%nat); (0x80e28, 190%nat); (0x81348, 57%nat); (0x815b8, 45%nat); (0x81920, 178%nat); (0x81dd4, 128%nat); (0x82aa8, 18%nat); (0x82d88, 35%nat); (0x83340, 7%nat); (0x834cc, 100%nat); (0x838dc, 726%nat); (0x854b8, 151%nat); (0x85c9c, 127%nat); (0x87498, 7%nat); (0x87b3c, 30%nat); (0x87df8, 40%nat); (0x8824c, 23%nat); (0x8855c, 46%nat); (0x88740, 14%nat); (0x88d98, 93%nat); (0x89244, 1206%nat); (0x8a9c0, 342%nat); (0x8b09c, 44%nat); (0x8b3dc, 144%nat); (0x8b810, 144%nat); (0x8bc54, 18%nat); (0x8bf3c, 25%nat); (0x8ca88, 76%nat); (0x8cebc, 27%nat); (0x8d0e0, 6%nat); (0x8d334, 130%nat); (0x8d87c, 136%nat); (0x8e020, 21%nat); (0x8e170, 14%nat); (0x8e7e4, 7%nat); (0x903e0, 36%nat); (0x9061c, 91%nat); (0x908c8, 19%nat); (0x90f3c, 272%nat); (0x915a8, 317%nat); (0x92384, 253%nat); (0x92f64, 26%nat); (0x93170, 7%nat); (0x9388c, 37%nat); (0x93cd8, 123%nat); (0x94070, 36%nat); (0x942e4, 152%nat); (0x94918, 5%nat); (0x94be0, 118%nat); (0x95138, 64%nat); (0x953b0, 74%nat); (0x95ac4, 46%nat); (0x95d10, 8%nat); (0x97518, 21%nat); (0x979c0, 147%nat); (0x984cc, 42%nat); (0x99cd4, 22%nat); (0x99fbc, 173%nat); (0x9a750, 203%nat); (0x9afa4, 74%nat); (0xa1a40, 265%nat); (0xa2124, 43%nat); (0xa48f8, 7%nat); (0xa7858, 174%nat); (0xb7030, 18%nat); (0x1176b4, 66%nat); (0x1178bc, 7%nat); (0x117d88, 455%nat); (0x118758, 53%nat); (0x118bc8, 123%nat); (0x11abf4, 5%nat); (0x11b2ac, 431%nat); (0x11bad4, 162%nat); (0x11be70, 290%nat); (0x11e9c4, 81%nat); (0x1298f8, 6%nat); (0x129a0c, 32%nat); (0x129cb8, 83%nat); (0x12a5b8, 7%nat); (0x12a7b0, 135%nat); (0x12c524, 11%nat); (0x12c690, 57%nat); (0x12d0dc, 159%nat); (0x12d978, 24%nat)].
Definition IT0 : itab := mk_itab_ranges ASEGS0 as0_ranges.
Definition BFUEL : nat := 400000%nat.
Definition KC0 : nat := 0%nat.
Definition FUEL : nat := 3000%nat.
