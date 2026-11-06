(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "cst_ok"; "xgl_ok"; "@Corelib.Init.Datatypes"; "list"; "prod"; "true"; "@Corelib.Init.Logic"; "False"; "and"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cN1"; "Erc_N1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8"; "QRD_img"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skeln"; "HBIGNE_stmt"; "HBIGN_stmt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells Iface F0A_rebuild InvQ8 F0A_skeln F0A_cN1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_hbN_cert.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require d4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require da.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dn.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cN1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d4.F0A_hbN1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_entry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cw.F0A_hbN_scand OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.da.F0A_hbN_disj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.F0A_hbN_qsz OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cw.F0A_hbN_du OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cw.F0A_hbN_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dn.F0A_hbN_asm.
Import ListNotations.
Open Scope Z_scope.
Ltac vmc := match goal with |- _ = ?b => vm_cast_no_check (eq_refl b) end.
Lemma E_N1_eq : Erc_N1 = E_N1. Proof. Time vmc. Qed.
Lemma CF_N1_1 : hbcertF 1 1 E_N1 FAM_N1_1.
Proof.
  constructor.
  - rewrite <- E_N1_eq. exact FAM_N1_1_ok.
  - Time vmc.
  - split; vmc.
  - split; vmc.
  - constructor. Time vmc.
Qed.
Lemma CV_N1_1L : hbcertV 1 1 true FAM_N1_1 VAR_N1_1L.
Proof.
  constructor.
  - exact VAR_N1_1L_ok.
  - constructor. Time vmc.
  - constructor. Time vmc.
  - constructor. Time vmc.
  - Time vmc.
  - Time vmc.
  - constructor; vmc.
Qed.
Lemma CV_N1_1M : hbcertV 1 1 false FAM_N1_1 VAR_N1_1M.
Proof.
  constructor.
  - exact VAR_N1_1M_ok.
  - constructor. Time vmc.
  - constructor. Time vmc.
  - constructor. Time vmc.
  - Time vmc.
  - Time vmc.
  - constructor; vmc.
Qed.
Lemma CF_N1_2 : hbcertF 1 2 E_N1 FAM_N1_2.
Proof.
  constructor.
  - rewrite <- E_N1_eq. exact FAM_N1_2_ok.
  - Time vmc.
  - split; vmc.
  - split; vmc.
  - constructor. Time vmc.
Qed.
Lemma CV_N1_2L : hbcertV 1 2 true FAM_N1_2 VAR_N1_2L.
Proof.
  constructor.
  - exact VAR_N1_2L_ok.
  - constructor. Time vmc.
  - constructor. Time vmc.
  - constructor. Time vmc.
  - Time vmc.
  - Time vmc.
  - constructor; vmc.
Qed.
Lemma CV_N1_2M : hbcertV 1 2 false FAM_N1_2 VAR_N1_2M.
Proof.
  constructor.
  - exact VAR_N1_2M_ok.
  - constructor. Time vmc.
  - constructor. Time vmc.
  - constructor. Time vmc.
  - Time vmc.
  - Time vmc.
  - constructor; vmc.
Qed.
Lemma TAG_N1_ok : hbtag_ok 1 true E_N1.
Proof. intros f FA. cbn [fam_allowed] in FA. destruct FA as [FA|FA]; subst f; [exists FAM_N1_1; split; [exact CF_N1_1 | intros [|]; [exists VAR_N1_1L; exact CV_N1_1L | exists VAR_N1_1M; exact CV_N1_1M]] | exists FAM_N1_2; split; [exact CF_N1_2 | intros [|]; [exists VAR_N1_2L; exact CV_N1_2L | exists VAR_N1_2M; exact CV_N1_2M]]]. Qed.
Theorem HBIGN_N1 : ltac2:(tb__ "0|1|
S4S5S0S0A2A1M0G0S2R2A1S3R2A1S0S1R5R1A2SaS1ScR2A2S8S10SdR2A2S11R2SeA2A2A2S7F_;F_;Fa;S0S1R6R1A2S9SfR2A1A1F_;Fa;S13R6R5S6U1SbA5F_;F_;F_;F_;FXGL;FCST;").
Proof. intros CST XGL H1 H2 H3 H4. rewrite E_N1_eq. exact (hb_tag CST XGL H1 H2 H3 H4 1 true E_N1 TAG_N1_ok). Qed.
Theorem HBIGNE_N1 : ltac2:(tb__ "0|1|
S4S5S0S0A2A1M0G0S2R2A1S3R2A1S0S1R5R1A2SaS1ScR2A2S8S10SdR2A2S11R2SeA2A2A2S7F_;F_;Fa;S0S1R6R1A2S9SfR2A1A1F_;Fa;S12R6R5S6U1SbA5F_;F_;F_;F_;FXGL;FCST;").
Proof. intros CST XGL H1 H2 H3 H4. rewrite E_N1_eq. exact (hb_tagE CST XGL H1 H2 H3 H4 1 true E_N1 TAG_N1_ok). Qed.
