(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import RepEcp EcpCurves.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_ecp_defs () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.c1_P"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.c2_P"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.c3_P"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.c4_P"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.c5_P"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.c9_P"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.c10_P"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.c11_P"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.c12_P"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.c13_P"; "Corelib.Init.Datatypes.nil"].


Definition A_MT : list modp_ent := ltac2:(CDefT.buildp (gd_tbl_A_ecp_defs ()) "(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+=43>4.(5.$2.(3.(4.&40.))+27260.$6.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+=4:00.(5.$2.(3.(4.&40.))+273:0.$7.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+=5070.(5.$2.(3.(4.&40.))+274>0.$8.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+=5924.(5.$2.(3.(4.&40.))+27620.$9.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+=6640.(5.$2.(3.(4.&40.))+27800.$:.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+=695<.(5.$2.(3.(4.&40.))+32460.$;.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+=67;8.(5.$2.(3.(4.&40.))+27:80.$<.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+=6844.(5.$2.(3.(4.&40.))+27;<0.$=.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+=68=0.(5.$2.(3.(4.&40.))+27=00.$>.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+=6<78.(5.$2.(3.(4.&40.))+324>0.$?.))(10.(1.$2.(1.$2.(3.(4.&40.)))))))))))))))")
(* [comment removed for export] *).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition A_ONE : Z := 0x28440.   (* [comment removed for export] *)
Definition A_CA (id : Z) : curve_addrs :=
  match id with
  | 1 => mkCA 0x27260 0x0 0x272a0 0x272e0 0x27320 0x27360 0xd43e4 0xf2480
  | 2 => mkCA 0x273a0 0x0 0x273e0 0x27420 0x27460 0x274a0 0xd4a00 0xf2840
  | 3 => mkCA 0x274e0 0x0 0x27520 0x27560 0x275a0 0x275e0 0xd5070 0xf2c00
  | 4 => mkCA 0x27620 0x0 0x27680 0x276e0 0x27740 0x277a0 0xd5924 0xf2fc0
  | 5 => mkCA 0x27800 0x0 0x27880 0x27900 0x27980 0x27a00 0xd6640 0xf3740
  | 6 => mkCA 0x27e40 0x27e80 0x27ec0 0x27f00 0x27f40 0x27f80 0x0 0xf4a00
  | 7 => mkCA 0x27fc0 0x28020 0x28080 0x280e0 0x28140 0x281a0 0x0 0xf4dc0
  | 8 => mkCA 0x28200 0x28260 0x282c0 0x28320 0x28380 0x283e0 0x0 0xf5540
  | 9 => mkCA 0x32460 0x0 0x0 0x0 0x0 0x324a0 0xd695c 0x0
  | 10 => mkCA 0x27a80 0x27ac0 0x27ae0 0x27b00 0x27b40 0x27b80 0xd67b8 0xf3ec0
  | 11 => mkCA 0x27bc0 0x27c00 0x27c20 0x27c40 0x27c80 0x27cc0 0xd6844 0xf4280
  | 12 => mkCA 0x27d00 0x27d40 0x27d60 0x27d80 0x27dc0 0x27e00 0xd68d0 0xf4640
  | 13 => mkCA 0x324e0 0x0 0x0 0x0 0x0 0x32540 0xd6c78 0x0
  | _ => mkCA 0 0 0 0 0 0 0 0 end.
Definition A_GL_JT : Z := 0x2722c.   (* [comment removed for export] *)
Definition A_GL_CASE1 : Z := 0xd0a14.
Definition A_GL_CASE2 : Z := 0xd2268.
Definition A_GL_CASE3 : Z := 0xd18cc.
Definition A_GL_CASE4 : Z := 0xd1bec.
Definition A_GL_CASE5 : Z := 0xd10b0.
Definition A_GL_CASE6 : Z := 0xd2584.
Definition A_GL_CASE7 : Z := 0xd28fc.
Definition A_GL_CASE8 : Z := 0xd1f0c.
Definition A_GL_CASE9 : Z := 0xd2fe8.
Definition A_GL_CASE10 : Z := 0xd1550.
Definition A_GL_CASE11 : Z := 0xd2c58.
Definition A_GL_CASE12 : Z := 0xd0d34.
Definition A_GL_CASE13 : Z := 0xd13d0.
