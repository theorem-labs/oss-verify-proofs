(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import RepEcp EcpCurves.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_ecp_defs () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.c1_P"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.c2_P"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.c3_P"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.c4_P"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.c5_P"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.c9_P"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.c10_P"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.c11_P"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.c12_P"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.c13_P"; "Corelib.Init.Datatypes.nil"].


Definition U_ONE : Z := 0x11bdc.   (* [comment removed for export] *)
Definition U_CA (id : Z) : curve_addrs :=
  match id with
  | 1 => mkCA 0x11324 0x0 0x1133c 0x11354 0x1136c 0x11384 0x3c478 0x48f40
  | 2 => mkCA 0x1139c 0x0 0x113bc 0x113d8 0x113f4 0x11410 0x3c780 0x49240
  | 3 => mkCA 0x1142c 0x0 0x1144c 0x1146c 0x1148c 0x114ac 0x3ca24 0x49540
  | 4 => mkCA 0x114cc 0x0 0x114fc 0x1152c 0x1155c 0x1158c 0x3ce38 0x49840
  | 5 => mkCA 0x115bc 0x0 0x11600 0x11644 0x11688 0x116cc 0x3d404 0x49e40
  | 6 => mkCA 0x1187c 0x1189c 0x118bc 0x118dc 0x118fc 0x1191c 0x0 0x4ad40
  | 7 => mkCA 0x1193c 0x1196c 0x1199c 0x119cc 0x119fc 0x11a2c 0x0 0x4b040
  | 8 => mkCA 0x11a5c 0x11a9c 0x11adc 0x11b1c 0x11b5c 0x11b9c 0x0 0x4b640
  | 9 => mkCA 0x16fe0 0x0 0x0 0x0 0x0 0x17000 0x3d610 0x0
  | 10 => mkCA 0x11710 0x11728 0x1172c 0x11730 0x11748 0x11760 0x3d4f0 0x4a440
  | 11 => mkCA 0x11778 0x11794 0x11798 0x1179c 0x117b8 0x117d4 0x3d550 0x4a740
  | 12 => mkCA 0x117f4 0x11814 0x11818 0x1181c 0x1183c 0x1185c 0x3d5b0 0x4aa40
  | 13 => mkCA 0x17020 0x0 0x0 0x0 0x0 0x17060 0x3d710 0x0
  | _ => mkCA 0 0 0 0 0 0 0 0 end.
Definition U_MT : list modp_ent := ltac2:(CDefT.buildp (gd_tbl_P_ecp_defs ()) "(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+3<478.(5.$2.(3.(4.&40.))+11324.$6.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+3<780.(5.$2.(3.(4.&40.))+1139<.$7.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+3<:24.(5.$2.(3.(4.&40.))+1142<.$8.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+3<>38.(5.$2.(3.(4.&40.))+114<<.$9.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+3=404.(5.$2.(3.(4.&40.))+115;<.$:.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+3=610.(5.$2.(3.(4.&40.))+16?>0.$;.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+3=4?0.(5.$2.(3.(4.&40.))+11710.$<.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+3=550.(5.$2.(3.(4.&40.))+11778.$=.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+3=5;0.(5.$2.(3.(4.&40.))+117?4.$>.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+3=710.(5.$2.(3.(4.&40.))+17020.$?.))(10.(1.$2.(1.$2.(3.(4.&40.)))))))))))))))")
(* [comment removed for export] *).
Definition U_ECP_GROUP_LOAD : Z := 0x3bb18.
Definition U_GL_CASE1 : Z := 0x3bb74.
Definition U_GL_CASE2 : Z := 0x3c0c4.
Definition U_GL_CASE3 : Z := 0x3bebc.
Definition U_GL_CASE4 : Z := 0x3bf68.
Definition U_GL_CASE5 : Z := 0x3bcdc.
Definition U_GL_CASE6 : Z := 0x3c178.
Definition U_GL_CASE7 : Z := 0x3c238.
Definition U_GL_CASE8 : Z := 0x3c014.
Definition U_GL_CASE9 : Z := 0x3c3cc.
Definition U_GL_CASE10 : Z := 0x3be00.
Definition U_GL_CASE11 : Z := 0x3c2e8.
Definition U_GL_CASE12 : Z := 0x3bc20.
Definition U_GL_CASE13 : Z := 0x3bd88.
