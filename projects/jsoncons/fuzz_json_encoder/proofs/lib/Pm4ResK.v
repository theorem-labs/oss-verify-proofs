(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK AsanNodesExtraDefsK Pm4DefsK.
Import ListNotations. Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition as0_ranges : list (Z * nat) := [(0x595e4, 47%nat); (0x59730, 15%nat); (0x598d4, 85%nat); (0x5bba4, 395%nat); (0x5cdb4, 73%nat); (0x60444, 55%nat); (0x609fc, 62%nat); (0x65674, 50%nat); (0x65e38, 16%nat); (0x66a7c, 980%nat); (0x68464, 352%nat); (0x68af8, 12%nat); (0x68cac, 251%nat); (0x6984c, 24%nat); (0x69fa0, 176%nat); (0x6a480, 17%nat); (0x6ac8c, 15%nat); (0x6b7f8, 106%nat); (0x73638, 35%nat); (0x75fbc, 117%nat); (0x76f38, 6626%nat); (0x7fc10, 91%nat); (0x8022c, 7%nat); (0x80c84, 134%nat); (0x81434, 103%nat); (0x81a24, 25%nat); (0x81c4c, 91%nat); (0x82638, 5%nat); (0x830b8, 245%nat); (0x835d8, 31%nat); (0x83a64, 109%nat); (0x8448c, 145%nat); (0x88778, 10%nat); (0x88f10, 29%nat); (0x893d4, 190%nat); (0x898f4, 57%nat); (0x89b64, 45%nat); (0x89ecc, 178%nat); (0x8a380, 128%nat); (0x8b054, 18%nat); (0x8b334, 35%nat); (0x8b8ec, 7%nat); (0x8ba78, 100%nat); (0x8be88, 726%nat); (0x8da64, 151%nat); (0x8e248, 127%nat); (0x8fa44, 7%nat); (0x900e8, 30%nat); (0x903a4, 40%nat); (0x907f8, 23%nat); (0x90b08, 46%nat); (0x90cec, 14%nat); (0x91344, 93%nat); (0x917f0, 1206%nat); (0x92f6c, 342%nat); (0x93648, 44%nat); (0x93988, 144%nat); (0x93dbc, 142%nat); (0x94200, 18%nat); (0x944e8, 25%nat); (0x95034, 76%nat); (0x95468, 27%nat); (0x9568c, 6%nat); (0x958e0, 130%nat); (0x95e28, 136%nat); (0x965cc, 21%nat); (0x9671c, 14%nat); (0x96d90, 7%nat); (0x9898c, 36%nat); (0x98bc8, 91%nat); (0x98e74, 19%nat); (0x994e8, 272%nat); (0x99b54, 317%nat); (0x9a930, 253%nat); (0x9b510, 26%nat); (0x9b71c, 7%nat); (0x9be38, 37%nat); (0x9c284, 123%nat); (0x9c61c, 36%nat); (0x9c890, 152%nat); (0x9cec4, 5%nat); (0x9d18c, 118%nat); (0x9d6e4, 64%nat); (0x9d95c, 74%nat); (0x9e070, 76%nat); (0x9e2c4, 4%nat); (0x9fac4, 21%nat); (0x9ff6c, 147%nat); (0xa0a78, 42%nat); (0xa2280, 22%nat); (0xa2568, 173%nat); (0xa2cfc, 203%nat); (0xa3550, 74%nat); (0xa9fec, 265%nat); (0xaa6d0, 43%nat); (0xacea4, 7%nat); (0xafe04, 174%nat); (0xdf3e4, 14%nat); (0x140850, 66%nat); (0x140a58, 509%nat); (0x141328, 92%nat); (0x1414c8, 92%nat); (0x14182c, 101%nat); (0x141d64, 123%nat); (0x143d90, 5%nat); (0x144448, 431%nat); (0x144c70, 162%nat); (0x14500c, 290%nat); (0x147b64, 81%nat); (0x152a98, 6%nat); (0x152bac, 32%nat); (0x152e58, 83%nat); (0x153728, 17%nat); (0x153950, 135%nat); (0x154924, 57%nat); (0x1556c4, 11%nat); (0x155838, 53%nat); (0x15627c, 159%nat); (0x156b18, 24%nat)].
Definition IT0 : itab := mk_itab_ranges ASEGS0 as0_ranges.
Definition BFUEL : nat := 400000%nat.
Definition KC0 : nat := 0%nat.
Definition FUEL : nat := 3000%nat.
