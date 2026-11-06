(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK AsanNodesExtraDefsK Bo0DefsK.
Import ListNotations. Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Definition as0_ranges : list (Z * nat) := [(0x3c3a4, 102%nat); (0x3c69c, 85%nat); (0x3e96c, 395%nat); (0x3fb7c, 73%nat); (0x4320c, 55%nat); (0x437c4, 62%nat); (0x4843c, 50%nat); (0x48c00, 16%nat); (0x49244, 980%nat); (0x4a97c, 352%nat); (0x4b010, 12%nat); (0x4b1c4, 251%nat); (0x4bd64, 24%nat); (0x4c4b8, 176%nat); (0x4c998, 17%nat); (0x4d1a4, 15%nat); (0x4dd10, 99%nat); (0x52a48, 35%nat); (0x54158, 85%nat); (0x5504c, 6626%nat); (0x5dd24, 91%nat); (0x5e340, 7%nat); (0x5ed98, 134%nat); (0x5f548, 103%nat); (0x5fb38, 25%nat); (0x5fd60, 91%nat); (0x6074c, 5%nat); (0x611cc, 245%nat); (0x616ec, 31%nat); (0x61b78, 109%nat); (0x622dc, 145%nat); (0x6634c, 10%nat); (0x66ae4, 29%nat); (0x66fa8, 190%nat); (0x674c8, 57%nat); (0x67738, 45%nat); (0x67aa0, 178%nat); (0x67f54, 128%nat); (0x68c28, 18%nat); (0x68f08, 35%nat); (0x694c0, 7%nat); (0x6964c, 100%nat); (0x69a5c, 726%nat); (0x6b638, 151%nat); (0x6be1c, 127%nat); (0x6d618, 7%nat); (0x6dcbc, 30%nat); (0x6df78, 40%nat); (0x6e3cc, 23%nat); (0x6e6dc, 46%nat); (0x6e8c0, 14%nat); (0x6ef18, 93%nat); (0x6f3c4, 1206%nat); (0x70b40, 342%nat); (0x7121c, 44%nat); (0x7155c, 144%nat); (0x71990, 137%nat); (0x71db8, 18%nat); (0x720a0, 25%nat); (0x72bec, 76%nat); (0x73020, 27%nat); (0x73244, 6%nat); (0x73498, 130%nat); (0x739e0, 136%nat); (0x74184, 21%nat); (0x742d4, 14%nat); (0x74948, 7%nat); (0x76544, 36%nat); (0x76780, 91%nat); (0x76a2c, 19%nat); (0x770a0, 272%nat); (0x7770c, 317%nat); (0x784e8, 253%nat); (0x790c8, 26%nat); (0x792d4, 7%nat); (0x799f0, 37%nat); (0x79e3c, 123%nat); (0x7a1d4, 36%nat); (0x7a448, 152%nat); (0x7aa7c, 5%nat); (0x7ad44, 118%nat); (0x7b29c, 64%nat); (0x7b514, 74%nat); (0x7bc28, 155%nat); (0x7d67c, 21%nat); (0x7db24, 147%nat); (0x7e630, 42%nat); (0x7fe38, 22%nat); (0x80120, 173%nat); (0x808b4, 203%nat); (0x81108, 74%nat); (0x87ba4, 265%nat); (0x88288, 43%nat); (0x8aa5c, 7%nat); (0x8d9bc, 174%nat); (0x95054, 18%nat); (0xbd428, 66%nat); (0xbd630, 463%nat); (0xbdf58, 53%nat); (0xbe3c8, 123%nat); (0xbeca4, 5%nat); (0xbf35c, 431%nat); (0xbfb84, 162%nat); (0xbff20, 290%nat); (0xc2a74, 81%nat); (0xcc334, 6%nat); (0xcc448, 32%nat); (0xcc6f4, 83%nat); (0xccd84, 7%nat); (0xccf7c, 135%nat); (0xce15c, 11%nat); (0xce504, 57%nat); (0xce87c, 159%nat); (0xcf118, 24%nat)].
Definition IT0 : itab := mk_itab_ranges ASEGS0 as0_ranges.
Definition BFUEL : nat := 400000%nat.
Definition KC0 : nat := 0%nat.
Definition FUEL : nat := 3000%nat.
