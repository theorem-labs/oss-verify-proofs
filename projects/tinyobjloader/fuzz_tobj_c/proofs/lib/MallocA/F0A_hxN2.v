(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "cst_ok"; "xgl_ok"; "@Corelib.Init.Datatypes"; "list"; "prod"; "true"; "@Corelib.Init.Logic"; "False"; "and"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cN2"; "Erc_N2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8"; "QRD_img"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skeln"; "HBIGNE_stmt"; "HBIGN_stmt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells Iface F0A_rebuild InvQ8 F0A_skeln F0A_cN2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_hbN_cert.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require d4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require da.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dn.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cN2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d4.F0A_hbN2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_entry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cw.F0A_hbN_scand OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.da.F0A_hbN_disj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.F0A_hbN_qsz OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cw.F0A_hbN_du OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cw.F0A_hbN_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dn.F0A_hbN_asm.
Import ListNotations.
Open Scope Z_scope.
Ltac vmc := match goal with |- _ = ?b => vm_cast_no_check (eq_refl b) end.
Lemma E_N2_eq : Erc_N2 = E_N2. Proof. Time vmc. Qed.
Lemma CF_N2_1 : hbcertF 2 1 E_N2 FAM_N2_1.
Proof.
  constructor.
  - rewrite <- E_N2_eq. exact FAM_N2_1_ok.
  - Time vmc.
  - split; vmc.
  - split; vmc.
  - constructor. Time vmc.
Qed.
Lemma CV_N2_1L : hbcertV 2 1 true FAM_N2_1 VAR_N2_1L.
Proof.
  constructor.
  - exact VAR_N2_1L_ok.
  - constructor. Time vmc.
  - constructor. Time vmc.
  - constructor. Time vmc.
  - Time vmc.
  - Time vmc.
  - constructor; vmc.
Qed.
Lemma CV_N2_1M : hbcertV 2 1 false FAM_N2_1 VAR_N2_1M.
Proof.
  constructor.
  - exact VAR_N2_1M_ok.
  - constructor. Time vmc.
  - constructor. Time vmc.
  - constructor. Time vmc.
  - Time vmc.
  - Time vmc.
  - constructor; vmc.
Qed.
Lemma CF_N2_2 : hbcertF 2 2 E_N2 FAM_N2_2.
Proof.
  constructor.
  - rewrite <- E_N2_eq. exact FAM_N2_2_ok.
  - Time vmc.
  - split; vmc.
  - split; vmc.
  - constructor. Time vmc.
Qed.
Lemma CV_N2_2L : hbcertV 2 2 true FAM_N2_2 VAR_N2_2L.
Proof.
  constructor.
  - exact VAR_N2_2L_ok.
  - constructor. Time vmc.
  - constructor. Time vmc.
  - constructor. Time vmc.
  - Time vmc.
  - Time vmc.
  - constructor; vmc.
Qed.
Lemma CV_N2_2M : hbcertV 2 2 false FAM_N2_2 VAR_N2_2M.
Proof.
  constructor.
  - exact VAR_N2_2M_ok.
  - constructor. Time vmc.
  - constructor. Time vmc.
  - constructor. Time vmc.
  - Time vmc.
  - Time vmc.
  - constructor; vmc.
Qed.
Lemma TAG_N2_ok : hbtag_ok 2 true E_N2.
Proof. intros f FA. cbn [fam_allowed] in FA. destruct FA as [FA|FA]; subst f; [exists FAM_N2_1; split; [exact CF_N2_1 | intros [|]; [exists VAR_N2_1L; exact CV_N2_1L | exists VAR_N2_1M; exact CV_N2_1M]] | exists FAM_N2_2; split; [exact CF_N2_2 | intros [|]; [exists VAR_N2_2L; exact CV_N2_2L | exists VAR_N2_2M; exact CV_N2_2M]]]. Qed.
Theorem HBIGN_N2 : ltac2:(tb__ "0|1|
S4S5S0S0A2A1M0G0S2R2A1S3R2A1S0S1R5R1A2SaS1ScR2A2S8S10SdR2A2S11R2SeA2A2A2S7F_;F_;Fa;S0S1R6R1A2S9SfR2A1A1F_;Fa;S13R6R5S6U2SbA5F_;F_;F_;F_;FXGL;FCST;").
Proof. intros CST XGL H1 H2 H3 H4. rewrite E_N2_eq. exact (hb_tag CST XGL H1 H2 H3 H4 2 true E_N2 TAG_N2_ok). Qed.
Theorem HBIGNE_N2 : ltac2:(tb__ "0|1|
S4S5S0S0A2A1M0G0S2R2A1S3R2A1S0S1R5R1A2SaS1ScR2A2S8S10SdR2A2S11R2SeA2A2A2S7F_;F_;Fa;S0S1R6R1A2S9SfR2A1A1F_;Fa;S12R6R5S6U2SbA5F_;F_;F_;F_;FXGL;FCST;").
Proof. intros CST XGL H1 H2 H3 H4. rewrite E_N2_eq. exact (hb_tagE CST XGL H1 H2 H3 H4 2 true E_N2 TAG_N2_ok). Qed.
