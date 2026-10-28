(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AH0Spec0 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.BHeap.AModel.AL_"; "ARUN_1.bp_b6"; "ARUN_1.bp_sb"; "ARUN_1.bp_pa"; "ARUN_1.bp_T"; "ARUN_1.bp_ctx"; "ARUN_1.bp_fs"; "ARUN_1.bp_nb0"; "ARUN_1.bp_ss0"; "ARUN_1.bp_top"; "ARUN_1.bp_sp0"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.pow"; "ARUN_1.bp_stkhi"; "ARUN_1.bp_dtls"; "ARUN_1.bp_extra"; "ARUN_1.bp_gsh"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.AH"; "ARUN_1.L0_of"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.region0"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.pcl0"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.qcache0"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.sec0"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.DP"; "Corelib.Init.Datatypes.cons"; "ARUN_1.bp_tf"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.FK"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.AC"; "Corelib.Init.Datatypes.prod"].


Section ARUN_1. Context {hAR : arun}.
Record boot_params := BP {
  bp_b6 : Z; bp_sb : Z; bp_pa : Z; bp_T : Z; bp_ctx : Z; bp_fs : Z; bp_nb0 : Z; bp_ss0 : Z; bp_dtls : Z;
  bp_top : Z; bp_sp0 : Z; bp_stkhi : Z; bp_extra : list (Z * Z); bp_tf : Z; bp_gsh : list (Z * Z) }.

(* [comment removed for export] *)
Definition L0_of (bp : boot_params) : alayout := ltac2:(CDefT.buildp (gd_tbl_AH0Spec0 ()) "(0.(1.O1.)(2.O1.)(3.O1.)(4.O1.)(5.O1.)(6.O1.)(7.O1.)(8.O1.)(9.O1.)(:.O1.)(;.(:.O1.)+30.)(;.(:.O1.)(<.+2.+17.))(=.O1.)(>.O1.)(?.O1.)+10000.(10.O1.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition h0_of (bp : boot_params) : ahst := ltac2:(CDefT.buildp (gd_tbl_AH0Spec0 ()) "(11.(12.O1.)L,$13.$14.L,$13.$15.$16.(17.$18.)$19.$19.$1:.(1;.+1.(1<.$13.(7.O1.)(17.$13.))(1=.O1.)(1<.$13.(8.O1.)(17.$13.)))$16.(1>.L,$13.=L,$13.L,$13.$16.)==(1?.(17.(20.$13.$13.))==L,$13.$16.))")
(* [comment removed for export] *).
End ARUN_1.
