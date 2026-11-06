(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK AsanNodesExtraDefsK As0DefsK.
Import ListNotations. Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Definition as0_ranges : list (Z * nat) := [(0x3c124, 102%nat); (0x3c41c, 85%nat); (0x3e6ec, 395%nat); (0x3f8fc, 73%nat); (0x42f8c, 55%nat); (0x43544, 62%nat); (0x481bc, 50%nat); (0x48980, 16%nat); (0x48fc4, 980%nat); (0x4a6fc, 352%nat); (0x4ad90, 12%nat); (0x4af44, 251%nat); (0x4bae4, 24%nat); (0x4c238, 176%nat); (0x4c718, 17%nat); (0x4cf24, 15%nat); (0x4da90, 99%nat); (0x527c8, 35%nat); (0x53ed8, 85%nat); (0x54dcc, 6626%nat); (0x5daa4, 91%nat); (0x5e0c0, 7%nat); (0x5eb18, 134%nat); (0x5f2c8, 103%nat); (0x5f8b8, 25%nat); (0x5fae0, 91%nat); (0x604cc, 5%nat); (0x60f4c, 245%nat); (0x6146c, 31%nat); (0x618f8, 109%nat); (0x6205c, 145%nat); (0x660cc, 10%nat); (0x66864, 29%nat); (0x66d28, 190%nat); (0x67248, 57%nat); (0x674b8, 45%nat); (0x67820, 178%nat); (0x67cd4, 128%nat); (0x689a8, 18%nat); (0x68c88, 35%nat); (0x69240, 7%nat); (0x693cc, 100%nat); (0x697dc, 726%nat); (0x6b3b8, 151%nat); (0x6bb9c, 127%nat); (0x6d398, 7%nat); (0x6da3c, 30%nat); (0x6dcf8, 40%nat); (0x6e14c, 23%nat); (0x6e45c, 46%nat); (0x6e640, 14%nat); (0x6ec98, 93%nat); (0x6f144, 1206%nat); (0x708c0, 342%nat); (0x70f9c, 44%nat); (0x712dc, 144%nat); (0x71710, 137%nat); (0x71b38, 18%nat); (0x71e20, 25%nat); (0x7296c, 76%nat); (0x72da0, 27%nat); (0x72fc4, 6%nat); (0x73218, 130%nat); (0x73760, 136%nat); (0x73f04, 21%nat); (0x74054, 14%nat); (0x746c8, 7%nat); (0x762c4, 36%nat); (0x76500, 91%nat); (0x767ac, 19%nat); (0x76e20, 272%nat); (0x7748c, 317%nat); (0x78268, 253%nat); (0x78e48, 26%nat); (0x79054, 7%nat); (0x79770, 37%nat); (0x79bbc, 123%nat); (0x79f54, 36%nat); (0x7a1c8, 152%nat); (0x7a7fc, 5%nat); (0x7aac4, 118%nat); (0x7b01c, 64%nat); (0x7b294, 74%nat); (0x7b9a8, 155%nat); (0x7d3fc, 21%nat); (0x7d8a4, 147%nat); (0x7e3b0, 42%nat); (0x7fbb8, 22%nat); (0x7fea0, 173%nat); (0x80634, 203%nat); (0x80e88, 74%nat); (0x87924, 265%nat); (0x88008, 43%nat); (0x8a7dc, 7%nat); (0x8d73c, 174%nat); (0x94440, 18%nat); (0xbc814, 66%nat); (0xbca1c, 463%nat); (0xbd344, 53%nat); (0xbd7b4, 123%nat); (0xbe090, 5%nat); (0xbe748, 431%nat); (0xbef70, 162%nat); (0xbf30c, 290%nat); (0xc1e60, 81%nat); (0xcb720, 6%nat); (0xcb834, 32%nat); (0xcbae0, 83%nat); (0xcc170, 7%nat); (0xcc368, 135%nat); (0xcd548, 11%nat); (0xcd8f0, 57%nat); (0xcdc68, 159%nat); (0xce504, 24%nat)].
Definition IT0 : itab := mk_itab_ranges ASEGS0 as0_ranges.
Definition BFUEL : nat := 400000%nat.
Definition KC0 : nat := 0%nat.
Definition FUEL : nat := 3000%nat.
