(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK AsanNodesExtraDefsK Ba0DefsK.
Import ListNotations. Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Definition as0_ranges : list (Z * nat) := [(0x50fd0, 102%nat); (0x512c8, 85%nat); (0x53598, 395%nat); (0x547a8, 73%nat); (0x57e38, 55%nat); (0x583f0, 62%nat); (0x5d068, 50%nat); (0x5d82c, 16%nat); (0x5e108, 980%nat); (0x5faf0, 352%nat); (0x60184, 12%nat); (0x60338, 251%nat); (0x60ed8, 24%nat); (0x6162c, 176%nat); (0x61b0c, 17%nat); (0x62318, 15%nat); (0x62e84, 108%nat); (0x6acc4, 35%nat); (0x6d6d0, 85%nat); (0x6e5c4, 6626%nat); (0x7729c, 91%nat); (0x778b8, 7%nat); (0x78310, 134%nat); (0x78ac0, 103%nat); (0x790b0, 25%nat); (0x792d8, 91%nat); (0x79cc4, 5%nat); (0x7a744, 245%nat); (0x7ac64, 31%nat); (0x7b0f0, 109%nat); (0x7bb18, 145%nat); (0x7fe04, 10%nat); (0x8059c, 29%nat); (0x80a60, 190%nat); (0x80f80, 57%nat); (0x811f0, 45%nat); (0x81558, 178%nat); (0x81a0c, 128%nat); (0x826e0, 18%nat); (0x829c0, 35%nat); (0x82f78, 7%nat); (0x83104, 100%nat); (0x83514, 726%nat); (0x850f0, 151%nat); (0x858d4, 127%nat); (0x870d0, 7%nat); (0x87774, 30%nat); (0x87a30, 40%nat); (0x87e84, 23%nat); (0x88194, 46%nat); (0x88378, 14%nat); (0x889d0, 93%nat); (0x88e7c, 1206%nat); (0x8a5f8, 342%nat); (0x8acd4, 44%nat); (0x8b014, 144%nat); (0x8b448, 144%nat); (0x8b88c, 18%nat); (0x8bb74, 25%nat); (0x8c6c0, 76%nat); (0x8caf4, 27%nat); (0x8cd18, 6%nat); (0x8cf6c, 130%nat); (0x8d4b4, 136%nat); (0x8dc58, 21%nat); (0x8dda8, 14%nat); (0x8e41c, 7%nat); (0x90018, 36%nat); (0x90254, 91%nat); (0x90500, 19%nat); (0x90b74, 272%nat); (0x911e0, 317%nat); (0x91fbc, 253%nat); (0x92b9c, 26%nat); (0x92da8, 7%nat); (0x934c4, 37%nat); (0x93910, 123%nat); (0x93ca8, 36%nat); (0x93f1c, 152%nat); (0x94550, 5%nat); (0x94818, 118%nat); (0x94d70, 64%nat); (0x94fe8, 74%nat); (0x956fc, 46%nat); (0x95948, 8%nat); (0x97150, 21%nat); (0x975f8, 147%nat); (0x98104, 42%nat); (0x9990c, 22%nat); (0x99bf4, 173%nat); (0x9a388, 203%nat); (0x9abdc, 74%nat); (0xa1678, 265%nat); (0xa1d5c, 43%nat); (0xa4530, 7%nat); (0xa7490, 174%nat); (0xb4a84, 18%nat); (0x115108, 66%nat); (0x115310, 7%nat); (0x1157dc, 455%nat); (0x1161ac, 53%nat); (0x11661c, 123%nat); (0x118648, 5%nat); (0x118d00, 431%nat); (0x119528, 162%nat); (0x1198c4, 290%nat); (0x11c418, 81%nat); (0x12734c, 6%nat); (0x127460, 32%nat); (0x12770c, 83%nat); (0x12800c, 7%nat); (0x128204, 135%nat); (0x129f78, 11%nat); (0x12a0e4, 57%nat); (0x12ab30, 159%nat); (0x12b3cc, 24%nat)].
Definition IT0 : itab := mk_itab_ranges ASEGS0 as0_ranges.
Definition BFUEL : nat := 400000%nat.
Definition KC0 : nat := 0%nat.
Definition FUEL : nat := 3000%nat.
