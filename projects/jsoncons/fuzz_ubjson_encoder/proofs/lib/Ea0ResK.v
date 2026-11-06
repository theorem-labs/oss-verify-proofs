(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK AsanNodesExtraDefsK Ea0DefsK.
Import ListNotations. Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Definition as0_ranges : list (Z * nat) := [(0x51b80, 102%nat); (0x51e78, 85%nat); (0x54148, 395%nat); (0x55358, 73%nat); (0x589e8, 55%nat); (0x58fa0, 62%nat); (0x5dc18, 50%nat); (0x5e3dc, 16%nat); (0x5ee54, 980%nat); (0x6083c, 352%nat); (0x60ed0, 12%nat); (0x61084, 251%nat); (0x61c24, 24%nat); (0x62378, 176%nat); (0x62858, 17%nat); (0x63064, 15%nat); (0x63bd0, 108%nat); (0x6ba10, 35%nat); (0x6e41c, 85%nat); (0x6f310, 6626%nat); (0x77fe8, 91%nat); (0x78604, 7%nat); (0x7905c, 134%nat); (0x7980c, 103%nat); (0x79dfc, 25%nat); (0x7a024, 91%nat); (0x7aa10, 5%nat); (0x7b490, 245%nat); (0x7b9b0, 31%nat); (0x7be3c, 109%nat); (0x7c864, 145%nat); (0x80b50, 10%nat); (0x812e8, 29%nat); (0x817ac, 190%nat); (0x81ccc, 57%nat); (0x81f3c, 45%nat); (0x822a4, 178%nat); (0x82758, 128%nat); (0x8342c, 18%nat); (0x8370c, 35%nat); (0x83cc4, 7%nat); (0x83e50, 100%nat); (0x84260, 726%nat); (0x85e3c, 151%nat); (0x86620, 127%nat); (0x87e1c, 7%nat); (0x884c0, 30%nat); (0x8877c, 40%nat); (0x88bd0, 23%nat); (0x88ee0, 46%nat); (0x890c4, 14%nat); (0x8971c, 93%nat); (0x89bc8, 1206%nat); (0x8b344, 342%nat); (0x8ba20, 44%nat); (0x8bd60, 144%nat); (0x8c194, 144%nat); (0x8c5d8, 18%nat); (0x8c8c0, 25%nat); (0x8d40c, 76%nat); (0x8d840, 27%nat); (0x8da64, 6%nat); (0x8dcb8, 130%nat); (0x8e200, 136%nat); (0x8e9a4, 21%nat); (0x8eaf4, 14%nat); (0x8f168, 7%nat); (0x90d64, 36%nat); (0x90fa0, 91%nat); (0x9124c, 19%nat); (0x918c0, 272%nat); (0x91f2c, 317%nat); (0x92d08, 253%nat); (0x938e8, 26%nat); (0x93af4, 7%nat); (0x94210, 37%nat); (0x9465c, 123%nat); (0x949f4, 36%nat); (0x94c68, 152%nat); (0x9529c, 5%nat); (0x95564, 118%nat); (0x95abc, 64%nat); (0x95d34, 74%nat); (0x96448, 46%nat); (0x96694, 8%nat); (0x97e9c, 21%nat); (0x98344, 147%nat); (0x98e50, 42%nat); (0x9a658, 22%nat); (0x9a940, 173%nat); (0x9b0d4, 203%nat); (0x9b928, 74%nat); (0xa23c4, 265%nat); (0xa2aa8, 43%nat); (0xa527c, 7%nat); (0xa81dc, 174%nat); (0xb80e4, 18%nat); (0x119238, 66%nat); (0x119440, 7%nat); (0x11990c, 455%nat); (0x11a2dc, 53%nat); (0x11a74c, 123%nat); (0x11c778, 5%nat); (0x11ce30, 431%nat); (0x11d658, 162%nat); (0x11d9f4, 290%nat); (0x12054c, 81%nat); (0x12b480, 6%nat); (0x12b594, 32%nat); (0x12b840, 83%nat); (0x12c140, 7%nat); (0x12c338, 135%nat); (0x12e0ac, 11%nat); (0x12e218, 57%nat); (0x12ec64, 159%nat); (0x12f500, 24%nat)].
Definition IT0 : itab := mk_itab_ranges ASEGS0 as0_ranges.
Definition BFUEL : nat := 400000%nat.
Definition KC0 : nat := 0%nat.
Definition FUEL : nat := 3000%nat.
