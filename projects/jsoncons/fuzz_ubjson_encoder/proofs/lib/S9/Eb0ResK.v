(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import AxSymExec3K AsanPlanCoreK AsanPlanK AsanNodesExtraDefsK Eb0DefsK.
Import ListNotations. Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Definition as0_ranges : list (Z * nat) := [(0x523a8, 102%nat); (0x526a0, 85%nat); (0x54970, 395%nat); (0x55b80, 73%nat); (0x59210, 55%nat); (0x597c8, 62%nat); (0x5e440, 50%nat); (0x5ec04, 16%nat); (0x5f67c, 980%nat); (0x61064, 352%nat); (0x616f8, 12%nat); (0x618ac, 251%nat); (0x6244c, 24%nat); (0x62ba0, 176%nat); (0x63080, 17%nat); (0x6388c, 15%nat); (0x643f8, 108%nat); (0x6c238, 35%nat); (0x6ec44, 85%nat); (0x6fb38, 6626%nat); (0x78810, 91%nat); (0x78e2c, 7%nat); (0x79884, 134%nat); (0x7a034, 103%nat); (0x7a624, 25%nat); (0x7a84c, 91%nat); (0x7b238, 5%nat); (0x7bcb8, 245%nat); (0x7c1d8, 31%nat); (0x7c664, 109%nat); (0x7d08c, 145%nat); (0x81378, 10%nat); (0x81b10, 29%nat); (0x81fd4, 190%nat); (0x824f4, 57%nat); (0x82764, 45%nat); (0x82acc, 178%nat); (0x82f80, 128%nat); (0x83c54, 18%nat); (0x83f34, 35%nat); (0x844ec, 7%nat); (0x84678, 100%nat); (0x84a88, 726%nat); (0x86664, 151%nat); (0x86e48, 127%nat); (0x88644, 7%nat); (0x88ce8, 30%nat); (0x88fa4, 40%nat); (0x893f8, 23%nat); (0x89708, 46%nat); (0x898ec, 14%nat); (0x89f44, 93%nat); (0x8a3f0, 1206%nat); (0x8bb6c, 342%nat); (0x8c248, 44%nat); (0x8c588, 144%nat); (0x8c9bc, 144%nat); (0x8ce00, 18%nat); (0x8d0e8, 25%nat); (0x8dc34, 76%nat); (0x8e068, 27%nat); (0x8e28c, 6%nat); (0x8e4e0, 130%nat); (0x8ea28, 136%nat); (0x8f1cc, 21%nat); (0x8f31c, 14%nat); (0x8f990, 7%nat); (0x9158c, 36%nat); (0x917c8, 91%nat); (0x91a74, 19%nat); (0x920e8, 272%nat); (0x92754, 317%nat); (0x93530, 253%nat); (0x94110, 26%nat); (0x9431c, 7%nat); (0x94a38, 37%nat); (0x94e84, 123%nat); (0x9521c, 36%nat); (0x95490, 152%nat); (0x95ac4, 5%nat); (0x95d8c, 118%nat); (0x962e4, 64%nat); (0x9655c, 74%nat); (0x96c70, 46%nat); (0x96ebc, 8%nat); (0x986c4, 21%nat); (0x98b6c, 147%nat); (0x99678, 42%nat); (0x9ae80, 22%nat); (0x9b168, 173%nat); (0x9b8fc, 203%nat); (0x9c150, 74%nat); (0xa2bec, 265%nat); (0xa32d0, 43%nat); (0xa5aa4, 7%nat); (0xa8a04, 174%nat); (0xbc878, 18%nat); (0x11d9e0, 66%nat); (0x11dbe8, 7%nat); (0x11e0b4, 455%nat); (0x11ea84, 53%nat); (0x11eef4, 123%nat); (0x120f20, 5%nat); (0x1215d8, 431%nat); (0x121e00, 162%nat); (0x12219c, 290%nat); (0x124cf4, 81%nat); (0x12fc28, 6%nat); (0x12fd3c, 32%nat); (0x12ffe8, 83%nat); (0x1308e8, 7%nat); (0x130ae0, 135%nat); (0x132854, 11%nat); (0x1329c0, 57%nat); (0x13340c, 159%nat); (0x133ca8, 24%nat)].
Definition IT0 : itab := mk_itab_ranges ASEGS0 as0_ranges.
Definition BFUEL : nat := 400000%nat.
Definition KC0 : nat := 0%nat.
Definition FUEL : nat := 3000%nat.
