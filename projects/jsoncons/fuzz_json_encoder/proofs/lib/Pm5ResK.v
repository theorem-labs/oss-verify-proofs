(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK AsanNodesExtraDefsK Pm5DefsK.
Import ListNotations. Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition as0_ranges : list (Z * nat) := [(0x59eb4, 47%nat); (0x5a000, 15%nat); (0x5a1a4, 85%nat); (0x5c474, 395%nat); (0x5d684, 73%nat); (0x60d14, 55%nat); (0x612cc, 62%nat); (0x65f44, 50%nat); (0x66708, 16%nat); (0x6734c, 980%nat); (0x68d34, 352%nat); (0x693c8, 12%nat); (0x6957c, 251%nat); (0x6a11c, 24%nat); (0x6a870, 176%nat); (0x6ad50, 17%nat); (0x6b55c, 15%nat); (0x6c0c8, 106%nat); (0x73f08, 35%nat); (0x7688c, 117%nat); (0x77808, 6626%nat); (0x804e0, 91%nat); (0x80afc, 7%nat); (0x81554, 134%nat); (0x81d04, 103%nat); (0x822f4, 25%nat); (0x8251c, 91%nat); (0x82f08, 5%nat); (0x83988, 245%nat); (0x83ea8, 31%nat); (0x84334, 109%nat); (0x84d5c, 145%nat); (0x89048, 10%nat); (0x897e0, 29%nat); (0x89ca4, 190%nat); (0x8a1c4, 57%nat); (0x8a434, 45%nat); (0x8a79c, 178%nat); (0x8ac50, 128%nat); (0x8b924, 18%nat); (0x8bc04, 35%nat); (0x8c1bc, 7%nat); (0x8c348, 100%nat); (0x8c758, 726%nat); (0x8e334, 151%nat); (0x8eb18, 127%nat); (0x90314, 7%nat); (0x909b8, 30%nat); (0x90c74, 40%nat); (0x910c8, 23%nat); (0x913d8, 46%nat); (0x915bc, 14%nat); (0x91c14, 93%nat); (0x920c0, 1206%nat); (0x9383c, 342%nat); (0x93f18, 44%nat); (0x94258, 144%nat); (0x9468c, 142%nat); (0x94ad0, 18%nat); (0x94db8, 25%nat); (0x95904, 76%nat); (0x95d38, 27%nat); (0x95f5c, 6%nat); (0x961b0, 130%nat); (0x966f8, 136%nat); (0x96e9c, 21%nat); (0x96fec, 14%nat); (0x97660, 7%nat); (0x9925c, 36%nat); (0x99498, 91%nat); (0x99744, 19%nat); (0x99db8, 272%nat); (0x9a424, 317%nat); (0x9b200, 253%nat); (0x9bde0, 26%nat); (0x9bfec, 7%nat); (0x9c708, 37%nat); (0x9cb54, 123%nat); (0x9ceec, 36%nat); (0x9d160, 152%nat); (0x9d794, 5%nat); (0x9da5c, 118%nat); (0x9dfb4, 64%nat); (0x9e22c, 74%nat); (0x9e940, 76%nat); (0x9eb94, 4%nat); (0xa0394, 21%nat); (0xa083c, 147%nat); (0xa1348, 42%nat); (0xa2b50, 22%nat); (0xa2e38, 173%nat); (0xa35cc, 203%nat); (0xa3e20, 74%nat); (0xaa8bc, 265%nat); (0xaafa0, 43%nat); (0xad774, 7%nat); (0xb06d4, 174%nat); (0xe2d5c, 14%nat); (0x1441c8, 66%nat); (0x1443d0, 509%nat); (0x144ca0, 92%nat); (0x144e40, 92%nat); (0x1451a4, 101%nat); (0x1456dc, 123%nat); (0x147708, 5%nat); (0x147dc0, 431%nat); (0x1485e8, 162%nat); (0x148984, 290%nat); (0x14b57c, 81%nat); (0x1564b0, 6%nat); (0x1565c4, 32%nat); (0x156870, 83%nat); (0x157140, 17%nat); (0x157368, 135%nat); (0x15833c, 57%nat); (0x1590dc, 11%nat); (0x159250, 53%nat); (0x159c94, 159%nat); (0x15a530, 24%nat)].
Definition IT0 : itab := mk_itab_ranges ASEGS0 as0_ranges.
Definition BFUEL : nat := 400000%nat.
Definition KC0 : nat := 0%nat.
Definition FUEL : nat := 3000%nat.
