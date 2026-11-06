(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import RepEcp EcpCurves.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_ecp_defs () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Spec.EcpCurves.c1_P"; "OSSVerify.KrLib.Spec.EcpCurves.c2_P"; "OSSVerify.KrLib.Spec.EcpCurves.c3_P"; "OSSVerify.KrLib.Spec.EcpCurves.c4_P"; "OSSVerify.KrLib.Spec.EcpCurves.c5_P"; "OSSVerify.KrLib.Spec.EcpCurves.c9_P"; "OSSVerify.KrLib.Spec.EcpCurves.c10_P"; "OSSVerify.KrLib.Spec.EcpCurves.c11_P"; "OSSVerify.KrLib.Spec.EcpCurves.c12_P"; "OSSVerify.KrLib.Spec.EcpCurves.c13_P"; "Corelib.Init.Datatypes.nil"].


Definition P_ONE : Z := 0x11bcc.   (* [comment removed for export] *)
Definition P_CA (id : Z) : curve_addrs :=
  match id with
  | 1 => mkCA 0x11314 0x0 0x1132c 0x11344 0x1135c 0x11374 0x39380 0x45848
  | 2 => mkCA 0x1138c 0x0 0x113ac 0x113c8 0x113e4 0x11400 0x39598 0x45b48
  | 3 => mkCA 0x1141c 0x0 0x1143c 0x1145c 0x1147c 0x1149c 0x39734 0x45e48
  | 4 => mkCA 0x114bc 0x0 0x114ec 0x1151c 0x1154c 0x1157c 0x399fc 0x46148
  | 5 => mkCA 0x115ac 0x0 0x115f0 0x11634 0x11678 0x116bc 0x39e1c 0x46748
  | 6 => mkCA 0x1186c 0x1188c 0x118ac 0x118cc 0x118ec 0x1190c 0x0 0x47648
  | 7 => mkCA 0x1192c 0x1195c 0x1198c 0x119bc 0x119ec 0x11a1c 0x0 0x47948
  | 8 => mkCA 0x11a4c 0x11a8c 0x11acc 0x11b0c 0x11b4c 0x11b8c 0x0 0x47f48
  | 9 => mkCA 0x16fd0 0x0 0x0 0x0 0x0 0x16ff0 0x3a4fc 0x0
  | 10 => mkCA 0x11700 0x11718 0x1171c 0x11720 0x11738 0x11750 0x39ed0 0x46d48
  | 11 => mkCA 0x11768 0x11784 0x11788 0x1178c 0x117a8 0x117c4 0x3a0b8 0x47048
  | 12 => mkCA 0x117e4 0x11804 0x11808 0x1180c 0x1182c 0x1184c 0x3a2c4 0x47348
  | 13 => mkCA 0x17010 0x0 0x0 0x0 0x0 0x17050 0x3a5cc 0x0
  | _ => mkCA 0 0 0 0 0 0 0 0 end.
Definition P_MT : list modp_ent := ltac2:(CDefT.buildp (gd_tbl_P_ecp_defs ()) "(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+39380.(5.$2.(3.(4.&40.))+11314.$6.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+39598.(5.$2.(3.(4.&40.))+1138<.$7.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+39734.(5.$2.(3.(4.&40.))+1141<.$8.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+399?<.(5.$2.(3.(4.&40.))+114;<.$9.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+39>1<.(5.$2.(3.(4.&40.))+115:<.$:.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+3:4?<.(5.$2.(3.(4.&40.))+16?=0.$;.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+39>=0.(5.$2.(3.(4.&40.))+11700.$<.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+3:0;8.(5.$2.(3.(4.&40.))+11768.$=.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+3:2<4.(5.$2.(3.(4.&40.))+117>4.$>.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+3:5<<.(5.$2.(3.(4.&40.))+17010.$?.))(10.(1.$2.(1.$2.(3.(4.&40.)))))))))))))))")
(* [comment removed for export] *).
Definition P_ECP_GROUP_LOAD : Z := 0x38a30.
Definition P_GL_CASE1 : Z := 0x38a80.
Definition P_GL_CASE2 : Z := 0x38fd0.
Definition P_GL_CASE3 : Z := 0x38dc8.
Definition P_GL_CASE4 : Z := 0x38e74.
Definition P_GL_CASE5 : Z := 0x38be8.
Definition P_GL_CASE6 : Z := 0x39084.
Definition P_GL_CASE7 : Z := 0x39144.
Definition P_GL_CASE8 : Z := 0x38f20.
Definition P_GL_CASE9 : Z := 0x392d8.
Definition P_GL_CASE10 : Z := 0x38d0c.
Definition P_GL_CASE11 : Z := 0x391f4.
Definition P_GL_CASE12 : Z := 0x38b2c.
Definition P_GL_CASE13 : Z := 0x38c94.
