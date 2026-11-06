(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State OSSVerify.glaze.binary_reflection.images.Asan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeLG OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsDrvM2SH.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeLG OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section M2SH.
Context {RC : run_ceil}.
Variable bt : as_boot.
Hypothesis BT_SEGS : bt_segs bt = ASEGS.
Hypothesis K_midbeg : In (0x108268, 8%nat, 0x0) (bt_consts bt).
Hypothesis K_hiend : In (0x108260, 8%nat, 0x7fffffffffff) (bt_consts bt).
Hypothesis K_midend : In (0x108270, 8%nat, 0x0) (bt_consts bt).

(* [comment removed for export] *)
Theorem M2S_H_P : forall (P : ast -> Prop) L LF B C K M mdl, AzBridgeH.AINVw (AzBridgeLG.AAINV_LG (AAINVP P bt)) L LF B C K M mdl ->
  rdn ASEGS M (Z_to_bv 64 0x108268) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn ASEGS M (Z_to_bv 64 0x108260) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff))
  /\ exists me : Z, rdn ASEGS M (Z_to_bv 64 0x108270) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 me)).
Proof.
  intros P L LF B C K M mdl (FF & _ & (HA & _)).
  destruct HA as (st & _ & RP & _).
  pose proof (read_consts bt st L FF M mdl RP) as CH. unfold cells_hold in CH. rewrite Forall_forall in CH. rewrite BT_SEGS in CH.
  pose proof (CH _ K_midbeg) as C1. pose proof (CH _ K_hiend) as C2. pose proof (CH _ K_midend) as C3.
  cbn beta iota in C1, C2, C3. unfold cellN in C1, C2, C3.
  split; [exact C1|]. split; [exact C2|]. exists 0. exact C3.
Qed.
Theorem M2S_H_h : forall h L LF B C K M mdl, AzBridgeH.AINVw (AzBridgeH.AAINV_HL bt h) L LF B C K M mdl ->
  rdn ASEGS M (Z_to_bv 64 0x108268) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn ASEGS M (Z_to_bv 64 0x108260) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff))
  /\ exists me : Z, rdn ASEGS M (Z_to_bv 64 0x108270) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 me)).
Proof. intros h. exact (M2S_H_P (AsAinvEntry3.AsAinvHole3.holes_lsopt h)). Qed.
End M2SH.
End AsDrvM2SH.
Require Stdlib.Strings.String LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvCertSoundZ OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvGlueA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsDrvDirSpecA.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvS0A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvS1A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3.AsDrvGSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA.AsDrvNodesAllA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvInstFactsA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA.AsDrvUinvA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA.AsDrvCertSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvCertSoundZ.AsDrvS0SpecA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvCertSoundZ OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvGlueA.AsDrvGlueLibA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvGlueA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

Lemma gplanD1 : gplan_ok planD1 = true. Proof. vmc. Qed.
Lemma M12_hM1d : M12 hM1d = Some (hZ1d, hN1d). Proof. vmc. Qed.   (* [comment removed for export] *)
Lemma reg_hM1d : reg hM1d 10 = ELit 65536. Proof. vmc. Qed.

(* [comment removed for export] *)
Section DirSpecA.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
Variable I : dinst.
Variables (a0 p : list byte) (fs : Fs.Fs) (data : list byte).
Hypothesis FHY : file_hyps I a0 p fs data.
#[local] Notation RZ := (realizes ASEGS).
#[local] Notation cs1x := (cs1 I a0 p fs data UX0).
Lemma UX0_a : uxa UX0. Proof. exact UX0_agree. Qed.

Lemma dir_readerr : forall E fx R M model, cs1x E hN1d fx R M model -> RZ (cfgF ASEGS fx R (pc hN1d) M model) (t_die (msg_read_error p) fs).
Proof.
  intros E fx R M model HC.
  eapply RZ_conseq_rz; [exact (run_1 I a0 p fs data FHY UX0 UX0_a (fun _ _ => t_nil) (fun _ _ _ _ => eq_refl) (fun _ _ => eq_refl) HS0 planD2 hN1d shapeD2 gplanD2 certD2
                                 (fun h ch Hh => ltac:(discriminate Hh)) E fx R M model HC)|].
  pose proof (proj1 (proj2 (proj1 (co_uinv HC)))) as Hp. rewrite <- Hp. apply sd_shapeD2.
Qed.

(* [comment removed for export] *)
Lemma dir_hole : forall E fx R M model, cs1x E hM1d fx R M model -> RZ (cfgF ASEGS fx R (pc hM1d) M model) (t_opened_dir p fs).
Proof.
  intros E fx R M model HC. rewrite t_opened_dir_eq.
  assert (Hsec : 64512 < uE E (reg hM1d 10)) by (rewrite reg_hM1d, uE_lit by lia; lia).
  exact (m1g1 I a0 p fs data FHY UX0 UX0_a hM1d hZ1d hN1d _ M12_hM1d (t_die_has_nil _ _) dir_readerr E fx R M model HC Hsec).
Qed.

Theorem dir_spec : forall E fx R M model, cs1x E tMod fx R M model ->
  RZ (cfgF ASEGS fx R (pc tMod) M model) (t_alt2 (t_die (msg_cannot_open p) fs) (t_opened_dir p fs)).
Proof.
  intros E fx R M model HC.
  pose proof (run_1 I a0 p fs data FHY UX0 UX0_a (fun _ fs' => t_opened_dir p fs') (fun _ _ _ _ => eq_refl) (fun _ fs' => t_opened_dir_has_nil p fs')
                (HSof1 hM1d) planD1 tMod shapeD1 gplanD1 certD1) as H.
  assert (HH : forall h ch, HSof1 hM1d h = Some ch -> forall E0 fx0 R0 M1 model0, cs1x E0 ch fx0 R0 M1 model0 ->
                 RZ (cfgF ASEGS fx0 R0 (pc ch) M1 model0) (t_opened_dir p fs)).
  { intros h ch Hh. destruct h as [|[|h]]; try discriminate Hh. injection Hh as <-. exact dir_hole. }
  eapply RZ_conseq_rz; [exact (H HH E fx R M model HC)|]. unfold shapeD1. cbn [GPS.sd]. apply Spec4.AgentLib.t_alt2_congr; [|apply t_eq_refl].
  pose proof (proj1 (proj2 (proj1 (co_uinv HC)))) as Hp. rewrite <- Hp. apply sd_shapeCOa.
Qed.
End DirSpecA.
End AsDrvDirSpecA.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAinvMuFrameB OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvDtorH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsDrvExtA.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAinvMuFrameB.AsAinvMuFrameA OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeLG OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3.AsDrvGSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA11 AsDrvM2SH OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvDtorH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import AzImageAsan.
Import ListNotations.
Open Scope Z_scope.
#[local] Notation u := bv_unsigned.

Section ExtA.
Context {RC : run_ceil}.
Variable hv : AsAinvBoot3.bvars.
#[local] Notation bt := (asan_bt hv).

Lemma bt_segs_A : bt_segs bt = ASEGS. Proof. reflexivity. Qed.
Ltac row := unfold asan_bt, asan_consts; cbn [bt_consts In]; repeat (first [left; reflexivity | right]).
Lemma K_midbeg_A : In (0x108268, 8%nat, 0x0) (bt_consts bt). Proof. row. Qed.
Lemma K_hiend_A : In (0x108260, 8%nat, 0x7fffffffffff) (bt_consts bt). Proof. row. Qed.
Lemma K_midend_A : In (0x108270, 8%nat, 0x0) (bt_consts bt). Proof. row. Qed.
Lemma K_mu_A : In (DNA.DTOR_MU, 8%nat, 0) (bt_consts bt). Proof. row. Qed.
Lemma K_cpm_A : In (0x106ddc, 1%nat, 1) (bt_consts bt). Proof. row. Qed.
Lemma K_rows_A : mu_rows_ok MU_A (bt_consts bt). Proof. apply mu_rows_ok_of_b. lazy. reflexivity. Qed.

(* [comment removed for export] *)
#[local] Notation GF P := (AzBridgeH.AINVw (AzBridgeLG.AAINV_LG (AAINVP P bt))).
Theorem M2S_H_AP : forall (P : ast -> Prop) L LF B C K M mdl, GF P L LF B C K M mdl ->
  rdn ASEGS M (Z_to_bv 64 0x108268) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn ASEGS M (Z_to_bv 64 0x108260) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff))
  /\ exists me : Z, rdn ASEGS M (Z_to_bv 64 0x108270) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 me)).
Proof. exact (M2S_H_P bt bt_segs_A K_midbeg_A K_hiend_A K_midend_A). Qed.
Theorem DTOR_H_AP : forall (P : ast -> Prop) L LF B C K M mdl, GF P L LF B C K M mdl ->
  rdn ASEGS M (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ exists cpm : byte, rdn ASEGS M (Z_to_bv 64 0x106ddc) 1 = Some [cpm] /\ u cpm <> 0.
Proof. exact (DTOR_H_P bt bt_segs_A K_mu_A K_cpm_A). Qed.
Theorem DTOR_FRAME_AP : forall (P : ast -> Prop) L LF B C K M M' mdl, GF P L LF B C K M mdl ->
  (forall a : word, M' a <> M a -> (in_lsb (u a) = true \/ in_mub (u a) = true) /\ M' a <> None) ->
  rdn ASEGS M' (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  GF P L LF B C K M' mdl.
Proof. exact (DTOR_FRAME_P bt GASAN asan_G_ro_img2 drvA_G_img_al GASAN_errno eq_refl eq_refl bt_segs_A eq_refl eq_refl K_rows_A). Qed.

(* [comment removed for export] *)
#[local] Notation AINVh h := (AzBridgeH.AINVw (AzBridgeH.AAINV_HL bt h)).
Theorem M2S_H_Ah : forall h L LF B C K M mdl, AINVh h L LF B C K M mdl ->
  rdn ASEGS M (Z_to_bv 64 0x108268) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn ASEGS M (Z_to_bv 64 0x108260) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff))
  /\ exists me : Z, rdn ASEGS M (Z_to_bv 64 0x108270) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 me)).
Proof. exact (M2S_H_h bt bt_segs_A K_midbeg_A K_hiend_A K_midend_A). Qed.
Theorem DTOR_H_Ah : forall h L LF B C K M mdl, AINVh h L LF B C K M mdl ->
  rdn ASEGS M (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ exists cpm : byte, rdn ASEGS M (Z_to_bv 64 0x106ddc) 1 = Some [cpm] /\ u cpm <> 0.
Proof. exact (DTOR_H_h bt bt_segs_A K_mu_A K_cpm_A). Qed.
Theorem DTOR_FRAME_Ah : forall h L LF B C K M M' mdl, AINVh h L LF B C K M mdl ->
  (forall a : word, M' a <> M a -> (in_lsb (u a) = true \/ in_mub (u a) = true) /\ M' a <> None) ->
  rdn ASEGS M' (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  AINVh h L LF B C K M' mdl.
Proof.
  exact (DTOR_FRAME_h bt GASAN asan_G_ro_img2 drvA_G_img_al GASAN_errno eq_refl eq_refl bt_segs_A eq_refl eq_refl K_rows_A).
Qed.

Theorem M2S_H_A : forall L LF B C K M mdl, AzBridgeH.AINVH_bt bt L LF B C K M mdl ->
  rdn ASEGS M (Z_to_bv 64 0x108268) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn ASEGS M (Z_to_bv 64 0x108260) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff))
  /\ exists me : Z, rdn ASEGS M (Z_to_bv 64 0x108270) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 me)).
Proof. exact (M2S_H_Ah None). Qed.
Theorem DTOR_H_A : forall L LF B C K M mdl, AzBridgeH.AINVH_bt bt L LF B C K M mdl ->
  rdn ASEGS M (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ exists cpm : byte, rdn ASEGS M (Z_to_bv 64 0x106ddc) 1 = Some [cpm] /\ u cpm <> 0.
Proof. exact (DTOR_H_Ah None). Qed.
Theorem DTOR_FRAME_A : forall L LF B C K M M' mdl, AzBridgeH.AINVH_bt bt L LF B C K M mdl ->
  (forall a : word, M' a <> M a -> (in_lsb (u a) = true \/ in_mub (u a) = true) /\ M' a <> None) ->
  rdn ASEGS M' (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  AzBridgeH.AINVH_bt bt L LF B C K M' mdl.
Proof. exact (DTOR_FRAME_Ah None). Qed.
End ExtA.
End AsDrvExtA.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS3A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvTSpecA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsDrvS3SpecA.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvS0A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvS1A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS3A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvTSpecA.AsDrvTA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA.AsDrvNodesAllA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA.AsDrvUinvA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA.AsDrvCertSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvCertSoundZ.AsDrvS0SpecA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvCertSoundZ OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvGlueA.AsDrvGlueLibA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvGlueA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvTSpecA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.
#[local] Notation RZ := (realizes ASEGS).

(* [comment removed for export] *)
Lemma CHKS_eq : forall hs cs pl, CHKS hs cs pl = CHKz hs BF FUEL cs pl. Proof. intros. unfold CHKS. reflexivity. Qed.
Lemma certC1n_a : CHKz HS0 BF FUEL tinC1n planD = COk (shapeD zmsg_short). Proof. rewrite <- CHKS_eq. exact certC1n. Qed.
Lemma certC2_a : CHKz HS0 BF FUEL tinC2 planD = COk (shapeD zmsg_overrun). Proof. rewrite <- CHKS_eq. exact certC2. Qed.
Lemma certC3_a : CHKz HSC BF FUEL tinC3 planC3 = COk shapeC3. Proof. rewrite <- CHKS_eq. exact certC3. Qed.

Lemma zmsg_short_ok : map (Z_to_bv 8) zmsg_short = msg_short. Proof. vm_compute. reflexivity. Qed.
Lemma zmsg_overrun_ok : map (Z_to_bv 8) zmsg_overrun = msg_overrun. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition fP0 : kentry := KRange PAYX 0 0.
Definition fC0 : kentry := KRange CFGX 0 0.
Lemma facts_holes :
  (DNA.has_fact (kn holeEA) fP0 && DNA.has_fact (kn holeEA) fC0 && DNA.has_fact (kn holePA) fP1 && DNA.has_fact (kn holePA) fC0
   && DNA.has_fact (kn holeEB) fP0 && DNA.has_fact (kn holeEB) fCFGB && DNA.has_fact (kn holePB) fP1 && DNA.has_fact (kn holePB) fCFGB)%bool = true.
Proof. vmc. Qed.

Section S3SpecA.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
Variable I : dinst.
Variables (a0 p : list byte) (fs : Fs.Fs) (data : list byte).
Hypothesis FHY : file_hyps I a0 p fs data.
#[local] Notation csAf := (cs1 I a0 p fs data (UXf data)).      (* [comment removed for export] *)
#[local] Notation csAx := (cs1 I a0 p fs data (UXc data)).
#[local] Notation CM := (hdr_count_mode data).
#[local] Notation CALLS := (hdr_calls data).
#[local] Notation LD := (Z.of_nat (length data)).

Definition D0s (E : env) (fs' : Fs.Fs) : TSet := t_nil.
Lemma no_holes_f : forall h ch, HS0 h = Some ch -> forall E fx R M model, csAf E ch fx R M model -> RZ (cfgF ASEGS fx R (pc ch) M model) (D0s E fs).
Proof. intros h ch Hh. discriminate Hh. Qed.

Theorem C1n_spec : forall E fx R M model, csAf E tinC1n fx R M model -> RZ (cfgF ASEGS fx R (pc tinC1n) M model) (t_die msg_short fs).
Proof.
  intros E fx R M model HC.
  eapply RZ_conseq_rz; [exact (run_1 I a0 p fs data FHY (UXf data) (UXf_a data) D0s (fun _ _ _ _ => eq_refl) (fun _ _ => eq_refl) HS0 planD tinC1n
                                 (shapeD zmsg_short) planD_ok certC1n_a no_holes_f E fx R M model HC)|].
  rewrite <- zmsg_short_ok. apply sd_lit1A.
Qed.
Theorem C2_spec : forall E fx R M model, csAf E tinC2 fx R M model -> RZ (cfgF ASEGS fx R (pc tinC2) M model) (t_die msg_overrun fs).
Proof.
  intros E fx R M model HC.
  eapply RZ_conseq_rz; [exact (run_1 I a0 p fs data FHY (UXf data) (UXf_a data) D0s (fun _ _ _ _ => eq_refl) (fun _ _ => eq_refl) HS0 planD tinC2
                                 (shapeD zmsg_overrun) planD_ok certC2_a no_holes_f E fx R M model HC)|].
  rewrite <- zmsg_overrun_ok. apply sd_lit1A.
Qed.

(* [comment removed for export] *)
Lemma hole_class : forall E cs fx R M model (fP fC : kentry), csAx E cs fx R M model ->
  DNA.has_fact (kn cs) fP = true -> DNA.has_fact (kn cs) fC = true ->
  kentry_ok ASEGS E (Mr (di_SHC I) (VSHf (di_HID I) (di_HIDF I)) E cs model M) fP
  /\ kentry_ok ASEGS E (Mr (di_SHC I) (VSHf (di_HID I) (di_HIDF I)) E cs model M) fC
  /\ uE E CFGX = hdr_cfglen data /\ uE E PAYX = (LD - hdr_cfglen data - 6) mod 2 ^ 64 /\ LD < 2 ^ 64.
Proof.
  intros E cs fx R M model fP fC HC HP HCf.
  pose proof (has_fact_sound E _ (kn cs) fP (co_know HC) HP) as H1. pose proof (has_fact_sound E _ (kn cs) fC (co_know HC) HCf) as H2.
  destruct (co_uinv HC) as [HU (HX & HL & _)]. pose proof (blob3 a0 p fs data E HU HX) as HB.
  split; [exact H1|]. split; [exact H2|]. split; [exact (cfgx_hdr data E HB)|].
  split; [apply (payx_val E LD (hdr_cfglen data) HL (cfgx_hdr data E HB)); apply hdr_cfglen_range|].
  rewrite <- HL. unfold uE. pose proof (u64_range (edenot E (EVar 3))). lia.
Qed.

Definition Dpay (E : env) (fs' : Fs.Fs) : TSet := t_payload CM (hdr_paylen data) CALLS fs'.

Theorem C3_spec : forall E fx R M model, csAx E tinC3 fx R M model ->
  RZ (cfgF ASEGS fx R (pc tinC3) M model) (t_payload CM (hdr_paylen data) CALLS fs).
Proof.
  intros E fx R M model HC.
  pose proof facts_holes as HF. repeat (apply andb_prop in HF as [HF ?F]).
  pose proof (hdr_cfglen_range data) as Rc.
  assert (HH : forall h ch, HSC h = Some ch -> forall E0 fx0 R0 M1 model0, csAx E0 ch fx0 R0 M1 model0 ->
                 RZ (cfgF ASEGS fx0 R0 (pc ch) M1 model0) (Dpay E0 fs)).
  { intros h ch Hh E0 fx0 R0 M1 model0 HC0. unfold Dpay.
    destruct h as [|[|[|[|[|h]]]]]; try discriminate Hh; injection Hh as <-.
    - (* [comment removed for export] *)
      destruct (hole_class E0 holeEA fx0 R0 M1 model0 fP0 fC0 HC0 HF F5) as (K1 & K2 & V1 & V2 & V3).
      cbn [kentry_ok fP0 fC0] in K1, K2. change (bv_unsigned (edenot E0 PAYX)) with (uE E0 PAYX) in K1. change (bv_unsigned (edenot E0 CFGX)) with (uE E0 CFGX) in K2.
      rewrite V1 in K2. rewrite V2 in K1.
      assert (Hc0 : hdr_cfglen data = 0) by lia.
      assert (Hp : hdr_paylen data <= 0).
      { unfold hdr_paylen. destruct (Z_lt_ge_dec (LD - hdr_cfglen data - 6) 0) as [Hn|Hn]; [lia|]. rewrite Z.mod_small in K1 by lia. lia. }
      rewrite (t_payload_none _ _ _ _ Hp), (calls1_hdr data Hc0). exact (T_EA I a0 p fs data FHY E0 fx0 R0 M1 model0 HC0).
    - (* [comment removed for export] *)
      destruct (hole_class E0 holePA fx0 R0 M1 model0 fP1 fC0 HC0 F4 F3) as (K1 & K2 & V1 & V2 & V3).
      cbn [kentry_ok fP1 fC0] in K1, K2. change (bv_unsigned (edenot E0 PAYX)) with (uE E0 PAYX) in K1. change (bv_unsigned (edenot E0 CFGX)) with (uE E0 CFGX) in K2.
      rewrite V1 in K2. rewrite V2 in K1.
      assert (Hc0 : hdr_cfglen data = 0) by lia.
      assert (Hp : 1 <= hdr_paylen data).
      { unfold hdr_paylen. destruct (Z_lt_ge_dec (LD - hdr_cfglen data - 6) 0) as [Hn|Hn].
        - exfalso. rewrite <- (Z.mod_add _ 1) in K1 by lia. rewrite Z.mod_small in K1 by lia. lia.
        - rewrite Z.mod_small in K1 by lia. lia. }
      rewrite (t_payload_some _ _ _ _ Hp), (calls1_hdr data Hc0). exact (T_PA I a0 p fs data FHY E0 fx0 R0 M1 model0 HC0).
    - (* [comment removed for export] *)
      destruct (hole_class E0 holeEB fx0 R0 M1 model0 fP0 fCFGB HC0 F2 F1) as (K1 & K2 & V1 & V2 & V3).
      cbn [kentry_ok fP0] in K1. change (bv_unsigned (edenot E0 PAYX)) with (uE E0 PAYX) in K1. rewrite V2 in K1.
      assert (Hp : hdr_paylen data <= 0).
      { unfold hdr_paylen. destruct (Z_lt_ge_dec (LD - hdr_cfglen data - 6) 0) as [Hn|Hn]; [lia|]. rewrite Z.mod_small in K1 by lia. lia. }
      rewrite (t_payload_none _ _ _ _ Hp). exact (T_EB I a0 p fs data FHY E0 fx0 R0 M1 model0 HC0).
    - (* [comment removed for export] *)
      destruct (hole_class E0 holePB fx0 R0 M1 model0 fP1 fCFGB HC0 F0 F) as (K1 & K2 & V1 & V2 & V3).
      cbn [kentry_ok fP1] in K1. change (bv_unsigned (edenot E0 PAYX)) with (uE E0 PAYX) in K1. rewrite V2 in K1.
      assert (Hp : 1 <= hdr_paylen data).
      { unfold hdr_paylen. destruct (Z_lt_ge_dec (LD - hdr_cfglen data - 6) 0) as [Hn|Hn].
        - exfalso. rewrite <- (Z.mod_add _ 1) in K1 by lia. rewrite Z.mod_small in K1 by lia. lia.
        - rewrite Z.mod_small in K1 by lia. lia. }
      rewrite (t_payload_some _ _ _ _ Hp). exact (T_PB I a0 p fs data FHY E0 fx0 R0 M1 model0 HC0). }
  pose proof (run_1 I a0 p fs data FHY (UXc data) (UXc_a data) Dpay (fun _ _ _ _ => eq_refl) (fun _ fs' => t_payload_has_nil _ _ _ fs') HSC planC3 tinC3 shapeC3
                planC3_ok certC3_a HH E fx R M model HC) as H.
  unfold shapeC3 in H. cbn [GPS.sd] in H. unfold Dpay in H.
  repeat match type of H with context [if ?b then _ else _] => destruct b end; exact H.
Qed.
End S3SpecA.
End AsDrvS3SpecA.
Module AsDrvK0SpecA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvS0A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvS1A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS3A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvK0A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA.AsDrvNodesAllA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA.AsDrvUinvA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA.AsDrvCertSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvCertSoundZ.AsDrvS0SpecA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvCertSoundZ OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvGlueA.AsDrvGlueLibA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvGlueA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvTSpecA AsDrvS3SpecA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.
#[local] Notation RZ := (realizes ASEGS).

Lemma gplanK0s : gplan_ok planK0s = true. Proof. reflexivity. Qed.
Lemma gplanK0 : gplan_ok planK0 = true. Proof. reflexivity. Qed.

(* [comment removed for export] *)
#[local] Notation THk h T := (infer_th 0 NXC [(25%nat, FLEN)] h T).
Lemma th_K0s : nth_error (THk hK0s tinC1n) 4%nat = Some (EVar 4). Proof. vmc. Qed.
Lemma th_K0s2 : nth_error (THk hK0s2 tinC1n) 4%nat = Some (EVar 4). Proof. vmc. Qed.
Lemma th_K0o : nth_error (THk hK0o tinC2) 4%nat = Some (EVar 4). Proof. vmc. Qed.
Lemma th_K0o2 : nth_error (THk hK0o2 tinC2) 4%nat = Some (EVar 4). Proof. vmc. Qed.
Lemma th_K0c : (nth_error (THk hK0c tinC3) 4%nat, nth_error (THk hK0c tinC3) 3%nat, nth_error (THk hK0c tinC3) 5%nat) = (Some (EVar 4), Some (EVar 4), Some (ELit 268435456)). Proof. vmc. Qed.
Lemma th_K0c2 : (nth_error (THk hK0c2 tinC3) 4%nat, nth_error (THk hK0c2 tinC3) 3%nat, nth_error (THk hK0c2 tinC3) 5%nat) = (Some (EVar 4), Some (EVar 4), Some (ELit 268435456)). Proof. vmc. Qed.

Lemma kr_ok : forall E M e lo hi, lo <= uE E e <= hi -> kentry_ok ASEGS E M (KRange e lo hi).
Proof. intros E M e lo hi H. cbn [kentry_ok]. unfold uE in H. lia. Qed.

Section K0SpecA.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
Variable I : dinst.
Variables (a0 p : list byte) (fs : Fs.Fs) (data : list byte).
Hypothesis FHY : file_hyps I a0 p fs data.
#[local] Notation csAf := (cs1 I a0 p fs data (UXf data)).      (* [comment removed for export] *)
#[local] Notation csAx := (cs1 I a0 p fs data (UXc data)).
#[local] Notation LD := (Z.of_nat (length data)).
#[local] Notation RUNf D := (run_1 I a0 p fs data FHY (UXf data) (UXf_a data) (fun _ fs' => D fs') (fun _ _ _ _ => eq_refl)).

(* [comment removed for export] *)
Lemma UXf_tenv : forall E th, nth_error th 4%nat = Some (EVar 4) -> UXf data E -> UXf data (tenv E th).
Proof. intros E th H4 HX. unfold UXf in *. rewrite (tenv_ev E th 4%nat (EVar 4) H4). exact HX. Qed.

Lemma to_C1n : forall h, ENT h tinC1n = true -> nth_error (THk h tinC1n) 4%nat = Some (EVar 4) ->
  forall E fx R M model, csAf E h fx R M model -> RZ (cfgF ASEGS fx R (pc h) M model) (t_die msg_short fs).
Proof.
  intros h He H4 E fx R M model HC.
  destruct (rebase I a0 p fs data (di_AINVH1 I) (UXf data) (UXf data) NXC _ h tinC1n E fx R M model HC He H4 (UXf_tenv E _ H4 (proj2 (co_uinv HC)))) as [HC2 Hpc].
  rewrite <- Hpc. exact (C1n_spec I a0 p fs data FHY _ fx R M model HC2).
Qed.
Lemma to_C2 : forall h, ENT h tinC2 = true -> nth_error (THk h tinC2) 4%nat = Some (EVar 4) ->
  forall E fx R M model, csAf E h fx R M model -> RZ (cfgF ASEGS fx R (pc h) M model) (t_die msg_overrun fs).
Proof.
  intros h He H4 E fx R M model HC.
  destruct (rebase I a0 p fs data (di_AINVH1 I) (UXf data) (UXf data) NXC _ h tinC2 E fx R M model HC He H4 (UXf_tenv E _ H4 (proj2 (co_uinv HC)))) as [HC2 Hpc].
  rewrite <- Hpc. exact (C2_spec I a0 p fs data FHY _ fx R M model HC2).
Qed.
Lemma to_C3 : forall h, ENT h tinC3 = true ->
  (nth_error (THk h tinC3) 4%nat, nth_error (THk h tinC3) 3%nat, nth_error (THk h tinC3) 5%nat) = (Some (EVar 4), Some (EVar 4), Some (ELit 268435456)) ->
  LD < 2 ^ 26 ->
  forall E fx R M model, csAf E h fx R M model ->
  RZ (cfgF ASEGS fx R (pc h) M model) (t_payload (hdr_count_mode data) (hdr_paylen data) (hdr_calls data) fs).
Proof.
  intros h He H435 HL E fx R M model HC.
  pose proof (f_equal (fun x => fst (fst x)) H435) as H4. pose proof (f_equal (fun x => snd (fst x)) H435) as H3. pose proof (f_equal snd H435) as H5. cbn [fst snd] in H4, H3, H5.
  pose proof (proj2 (co_uinv HC)) as HX.
  assert (HX' : UXc data (tenv E (THk h tinC3))).
  { split; [exact (UXf_tenv E _ H4 HX)|]. split.
    - rewrite (tenv_uE E _ 3%nat (EVar 4) H3). unfold uE. cbn [edenot]. unfold UXf in HX. rewrite HX. unfold APS.flen. lia.
    - intros _. rewrite (tenv_uE E _ 5%nat (ELit 268435456) H5), uE_lit by lia. unfold EVT. lia. }   (* [comment removed for export] *)
  destruct (rebase I a0 p fs data (di_AINVH1 I) (UXf data) (UXc data) NXC _ h tinC3 E fx R M model HC He H4 HX') as [HC2 Hpc].
  rewrite <- Hpc. exact (C3_spec I a0 p fs data FHY _ fx R M model HC2).
Qed.

Theorem K0_spec : LD < 65536 -> forall E fx R M model, csAf E hN1f fx R M model ->
  RZ (cfgF ASEGS fx R (pc hN1f) M model) (t_body data fs).
Proof.
  intros HL E fx R M model HC.
  destruct (co_uinv HC) as [HU HX]. pose proof (blob3 a0 p fs data E HU HX) as HB.
  assert (HF : uE E FLEN = LD) by (unfold uE, FLEN; cbn [edenot]; unfold UXf in HX; rewrite HX; unfold APS.flen; lia).
  pose proof (hdr_cfglen_range data) as Rc. pose proof (cfgx_hdr data E HB) as HCf.
  pose proof (b0_val data E HB) as HB0. pose proof (hdr_byte_range data 0) as RB0. pose proof (b2_rng E) as RB2.
  pose proof (u64_range (edenot E B1S)) as RB1. change (bv_unsigned (edenot E B1S)) with (uE E B1S) in RB1.
  unfold t_body. cbv zeta. unfold MAX_INPUT.
  destruct (Z.leb_spec 67108864 LD) as [X|_]; [lia|].
  destruct (Z.ltb_spec LD 6) as [H6|H6]; [|destruct (Z.ltb_spec LD (6 + hdr_cfglen data)) as [Ho|Ho]].
  - (* [comment removed for export] *)
    assert (HCk : csAf E tK0s fx R M model) by (apply add_facts; [exact HC|]; constructor; [apply kr_ok; lia | constructor]).
    pose proof (RUNf (t_die msg_short) (fun _ fs' => t_die_has_nil _ fs') (HS12 hK0s hK0s2) planK0s tK0s _ gplanK0s certK0s) as H.
    assert (HH : forall h ch, HS12 hK0s hK0s2 h = Some ch -> forall E0 fx0 R0 M1 model0, csAf E0 ch fx0 R0 M1 model0 ->
                   RZ (cfgF ASEGS fx0 R0 (pc ch) M1 model0) (t_die msg_short fs)).
    { intros h ch Hh. destruct h as [|[|[|h]]]; try discriminate Hh; injection Hh as <-; [exact (to_C1n hK0s entK0s th_K0s) | exact (to_C1n hK0s2 entK0s2 th_K0s2)]. }
    specialize (H HH E fx R M model HCk). cbn [GPS.sd] in H. destruct (_ <=? _) in H; exact H.
  - (* [comment removed for export] *)
    assert (HCk : csAf E tK0o fx R M model).
    { apply add_facts; [exact HC|].
      assert (HO : uE E OVXb = hdr_cfglen data + 5 - LD).
      { unfold OVXb. rewrite uE_esub, uE_eadd, uE_lit, HCf, HF by lia. rewrite (Z.mod_small (hdr_cfglen data + 5)) by lia. apply Z.mod_small. lia. }
      repeat (constructor; [apply kr_ok|]); [lia | lia | lia | lia | lia | lia | constructor]. }
    pose proof (RUNf (t_die msg_overrun) (fun _ fs' => t_die_has_nil _ fs') (HS12 hK0o hK0o2) planK0 tK0o _ gplanK0 certK0o) as H.
    assert (HH : forall h ch, HS12 hK0o hK0o2 h = Some ch -> forall E0 fx0 R0 M1 model0, csAf E0 ch fx0 R0 M1 model0 ->
                   RZ (cfgF ASEGS fx0 R0 (pc ch) M1 model0) (t_die msg_overrun fs)).
    { intros h ch Hh. destruct h as [|[|[|h]]]; try discriminate Hh; injection Hh as <-; [exact (to_C2 hK0o entK0o th_K0o) | exact (to_C2 hK0o2 entK0o2 th_K0o2)]. }
    specialize (H HH E fx R M model HCk). cbn [GPS.sd] in H. destruct (_ <=? _) in H; exact H.
  - (* [comment removed for export] *)
    assert (HCk : csAf E tK0c fx R M model).
    { apply add_facts; [exact HC|].
      assert (HO : uE E PAYXb = LD - (hdr_cfglen data + 6)).
      { unfold PAYXb. rewrite uE_esub, uE_eadd, uE_lit, HCf, HF by lia. rewrite (Z.mod_small (hdr_cfglen data + 6)) by lia. apply Z.mod_small. lia. }
      repeat (constructor; [apply kr_ok|]); [lia | lia | lia | lia | lia | lia | constructor]. }
    pose proof (RUNf (t_payload (hdr_count_mode data) (hdr_paylen data) (hdr_calls data)) (fun _ fs' => t_payload_has_nil _ _ _ fs')
                  (HS12 hK0c hK0c2) planK0 tK0c _ gplanK0 certK0c) as H.
    assert (HH : forall h ch, HS12 hK0c hK0c2 h = Some ch -> forall E0 fx0 R0 M1 model0, csAf E0 ch fx0 R0 M1 model0 ->
                   RZ (cfgF ASEGS fx0 R0 (pc ch) M1 model0) (t_payload (hdr_count_mode data) (hdr_paylen data) (hdr_calls data) fs)).
    { intros h ch Hh. destruct h as [|[|[|h]]]; try discriminate Hh; injection Hh as <-;
        [exact (to_C3 hK0c entK0c th_K0c ltac:(lia)) | exact (to_C3 hK0c2 entK0c2 th_K0c2 ltac:(lia))]. }
    specialize (H HH E fx R M model HCk). cbn [GPS.sd] in H. destruct (_ <=? _) in H; exact H.
Qed.
End K0SpecA.
End AsDrvK0SpecA.
Module AsDrvS2SpecA.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvS0A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvS1A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS3A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvK0A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvTSpecA.AsDrvZcertsA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA.AsDrvNodesAllA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA.AsDrvUinvA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA.AsDrvCertSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvCertSoundZ.AsDrvS0SpecA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvCertSoundZ OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvGlueA.AsDrvGlueLibA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvGlueA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvTSpecA AsDrvS3SpecA AsDrvK0SpecA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.
#[local] Notation RZ := (realizes ASEGS).

(* [comment removed for export] *)
Lemma CH_eq : forall hs cs pl, AsDrvS2A.CH hs cs pl = CHKz hs BF FUEL cs pl. Proof. intros. unfold AsDrvS2A.CH. reflexivity. Qed.
Lemma certVP_a : CHKz (HS12 hVP1 hVP2) BF FUEL tVP planVP = COk (SHole 1). Proof. rewrite <- CH_eq. exact certVP. Qed.
Lemma certVF_a : CHKz (HSof1 hVF) BF FUEL tVF planVF = COk (SHole 1). Proof. rewrite <- CH_eq. exact certVF. Qed.
Lemma certVG_a : CHKz (HSof1 hVG) BF FUEL hVFok planG = COk (SHole 1). Proof. rewrite <- CH_eq. exact certVG. Qed.
Lemma certVR_a : CHKz HS0 BF FUEL tVR planVR = COk shapeRF. Proof. rewrite <- CH_eq. exact certVR. Qed.
Lemma certVSc_a : CHKz (HSq hVSc) BF FUEL tVSc planVS = COk (SCase REMX 64 (SHole 1) (SHole 3)). Proof. rewrite <- CH_eq. exact certVSc. Qed.
Lemma certV0c_a : CHKz (HSof1 hV0c) BF FUEL tV0c planV0 = COk (SHole 1). Proof. rewrite <- CH_eq. exact certV0c. Qed.
Lemma gplanVP : gplan_ok planVP = true. Proof. reflexivity. Qed.
Lemma gplanVF : gplan_ok planVF = true. Proof. reflexivity. Qed.
Lemma gplanG : gplan_ok planG = true. Proof. reflexivity. Qed.
Lemma gplanVR : gplan_ok planVR = true. Proof. reflexivity. Qed.
Lemma gplanVS : gplan_ok planVS = true. Proof. reflexivity. Qed.
Lemma gplanV0 : gplan_ok planV0 = true. Proof. reflexivity. Qed.
Lemma gplanR1F : gplan_ok planR1F = true. Proof. reflexivity. Qed.
Lemma zmsg_rf_ok : map (Z_to_bv 8) MSG_RF = msg_refused. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition hVSc1 : acs := fst (fst (fst hVSc)).
Definition hVSc2 : acs := snd (fst (fst hVSc)).
Definition hVSc3 : acs := snd (fst hVSc).
Definition hVSc4 : acs := snd hVSc.
Lemma HSq_VSc : forall h ch, HSq hVSc h = Some ch -> ch = hVSc1 \/ ch = hVSc2 \/ ch = hVSc3 \/ ch = hVSc4.
Proof.
  unfold hVSc1, hVSc2, hVSc3, hVSc4, HSq. destruct hVSc as [[[a b] c] d]. cbn [fst snd]. intros h ch H.
  destruct h as [|[|[|[|[|h]]]]]; cbn [HS4] in H; try discriminate H; injection H as <-; auto.
Qed.
Lemma entVSc_all : ENTC hVSc1 tinC3 = true /\ ENTC hVSc2 tinC3 = true /\ ENTC hVSc3 tinC3 = true /\ ENTC hVSc4 tinC3 = true.
Proof.
  pose proof entVSc as H. unfold hVSc1, hVSc2, hVSc3, hVSc4. destruct hVSc as [[[a b] c] d]. cbn [fst snd].
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. auto.
Qed.

(* [comment removed for export] *)
#[local] Notation THr h T := (infer_th 0 NXR [] h T).
#[local] Notation THc h := (infer_th 0 NXC [(25%nat, ELit 65536)] h tinC3).
Definition LEN65 : expr := EAlu Instr.ALU_ADD (EVar 3) (ELit 65536).
Definition CAP2 : expr := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 3)) (ELit 131072).
Lemma th_RD2 : (nth_error (THr hRD2 TR) 4%nat, nth_error (THr hRD2 TR) 3%nat, nth_error (THr hRD2 TR) 2%nat) = (Some (EVar 4), Some (ELit 65536), Some (ELit 131072)).
Proof. vmc. Qed.
Lemma th_VP1 : (nth_error (THr hVP1 TR) 4%nat, nth_error (THr hVP1 TR) 3%nat, nth_error (THr hVP1 TR) 2%nat) = (Some (EVar 4), Some LEN65, Some (EVar 2)).
Proof. vmc. Qed.
Lemma th_VP2 : (nth_error (THr hVP2 TRw) 4%nat, nth_error (THr hVP2 TRw) 3%nat, nth_error (THr hVP2 TRw) 2%nat) = (Some (EVar 4), Some LEN65, Some (EVar 2)).
Proof. vmc. Qed.
Lemma th_VG : (nth_error (THr hVG TR) 4%nat, nth_error (THr hVG TR) 3%nat, nth_error (THr hVG TR) 2%nat) = (Some (EVar 4), Some LEN65, Some CAP2).
Proof. vmc. Qed.
Lemma th_V0c : (nth_error (THc hV0c) 4%nat, nth_error (THc hV0c) 3%nat) = (Some (EVar 4), Some (EVar 3)). Proof. vmc. Qed.
Lemma th_VSc : ((nth_error (THc hVSc1) 4%nat, nth_error (THc hVSc1) 3%nat), (nth_error (THc hVSc2) 4%nat, nth_error (THc hVSc2) 3%nat),
                (nth_error (THc hVSc3) 4%nat, nth_error (THc hVSc3) 3%nat), (nth_error (THc hVSc4) 4%nat, nth_error (THc hVSc4) 3%nat))
               = ((Some (EVar 4), Some (EVar 4)), (Some (EVar 4), Some (EVar 4)), (Some (EVar 4), Some (EVar 4)), (Some (EVar 4), Some (EVar 4))).
Proof. vmc. Qed.
Lemma reg_hVF : reg hVF 10 = CAP2. Proof. vmc. Qed.
Lemma reg_hG1 : reg hG1 10 = ELit 131072. Proof. vmc. Qed.
Definition fROOMw : kentry := KRange ROOMX 1 65535.
Lemma fact_TRw : DNA.has_fact (kn TRw) fROOMw = true. Proof. vmc. Qed.

Lemma uE_LEN65 : forall E len, uE E (EVar 3) = len -> 0 <= len < 2 ^ 63 -> uE E LEN65 = len + 65536.
Proof.
  intros E len H Hl. unfold LEN65, uE in *. cbn [edenot] in *. rewrite u_add64, H, u64_lit by lia. apply Z.mod_small. lia.
Qed.
Lemma uE_CAP2 : forall E len, uE E (EVar 3) = len -> 0 <= len < 2 ^ 60 -> uE E CAP2 = 2 * len + 131072.
Proof.
  intros E len H Hl. unfold CAP2, uE in *. cbn [edenot] in *. rewrite u_add64, u_mul64, H, !u64_lit by lia.
  rewrite (Z.mod_small (2 * len)) by lia. apply Z.mod_small. lia.
Qed.

Definition is_pow64k (cap : Z) : Prop := exists j, 1 <= j <= 10 /\ cap = 65536 * 2 ^ j.
Lemma pow64k_le : forall cap, is_pow64k cap -> 131072 <= cap <= 2 ^ 26 /\ (2 * cap <= 2 ^ 26 \/ cap = 2 ^ 26) /\ (65536 | cap).
Proof.
  intros cap (j & Hj & ->). assert (H : j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10) by lia.
  split; [|split; [|exists (2 ^ j); lia]];
    destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; cbn; lia.
Qed.
Lemma pow64k_double : forall cap, is_pow64k cap -> 2 * cap <= 2 ^ 26 -> is_pow64k (2 * cap).
Proof.
  intros cap (j & Hj & ->) H. exists (j + 1). rewrite Z.pow_add_r by lia. split; [|lia].
  assert (j <= 9 \/ j = 10) as [X | ->] by lia; [lia|]. cbn in H. lia.
Qed.

Section S2SpecA.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
Variable I : dinst.
Variables (a0 p : list byte) (fs : Fs.Fs) (data : list byte).
Hypothesis FHY : file_hyps I a0 p fs data.
#[local] Notation csAf := (cs1 I a0 p fs data (UXf data)).      (* [comment removed for export] *)
#[local] Notation csAr len cap := (cs1 I a0 p fs data (UXr data len cap)).
#[local] Notation LD := (Z.of_nat (length data)).
#[local] Notation L := (APS.flen data).
#[local] Notation RUNr len cap D := (run_1 I a0 p fs data FHY (UXr data len cap) (UXr_a data len cap) (fun _ fs' => D fs') (fun _ _ _ _ => eq_refl)).
#[local] Notation RUNf D := (run_1 I a0 p fs data FHY (UXf data) (UXf_a data) (fun _ fs' => D fs') (fun _ _ _ _ => eq_refl)).

Definition RD (cap : Z) (fs' : Fs.Fs) : TSet := t_body data fs'.
Lemma RD_has_nil : forall cap fs', RD cap fs' [].
Proof. intros cap fs'. unfold RD. apply t_body_has_nil. Qed.
Lemma RD_body : forall cap fs', LD < cap \/ 2 ^ 26 <= cap -> RD cap fs' = t_body data fs'.
Proof. intros cap fs' _. reflexivity. Qed.
Lemma body_ok : 65536 <= LD < 2 ^ 26 -> forall fs', t_body data fs' = t_payload (hdr_count_mode data) (hdr_paylen data) (hdr_calls data) fs'.
Proof.
  intros H fs'. pose proof (hdr_cfglen_range data). unfold t_body. cbv zeta. unfold MAX_INPUT.
  destruct (Z.leb_spec 67108864 LD); [lia|]. destruct (Z.ltb_spec LD 6); [lia|]. destruct (Z.ltb_spec LD (6 + hdr_cfglen data)); [lia|]. reflexivity.
Qed.
Lemma body_refused : 2 ^ 26 <= LD -> forall fs', t_body data fs' = t_die msg_refused fs'.
Proof. intros H fs'. unfold t_body. cbv zeta. unfold MAX_INPUT. destruct (Z.leb_spec 67108864 LD); [reflexivity | lia]. Qed.

(* [comment removed for export] *)
Definition WF (len cap : Z) : Prop := (65536 | len) /\ 65536 <= len /\ len + 65536 <= cap /\ is_pow64k cap /\ len <= L.

(* [comment removed for export] *)
Lemma tr_vals : forall len cap E cs fx R M model, csAr len cap E cs fx R M model ->
  uE E FLEN = L /\ uE E (EVar 3) = len /\ uE E (EVar 2) = cap /\ eb E 3%nat = APS.chunk 0 data.
Proof.
  intros len cap E cs fx R M model HC. destruct (co_uinv HC) as [HU (HX & H3 & H2)].
  split; [unfold uE, FLEN; cbn [edenot]; exact HX|]. split; [exact H3|]. split; [exact H2 | exact (blob3 a0 p fs data E HU HX)].
Qed.
Lemma UXf_tenv' : forall E th, nth_error th 4%nat = Some (EVar 4) -> UXf data E -> UXf data (tenv E th).
Proof. intros E th H4 HX. unfold UXf in *. rewrite (tenv_ev E th 4%nat (EVar 4) H4). exact HX. Qed.

(* [comment removed for export] *)
Lemma to_C3r : forall h e3 len cap, ENTC h tinC3 = true -> (nth_error (THc h) 4%nat, nth_error (THc h) 3%nat) = (Some (EVar 4), Some e3) ->
  65536 <= LD < 2 ^ 26 -> LD < cap ->
  forall E fx R M model, csAr len cap E h fx R M model -> uE E e3 = LD ->
  RZ (cfgF ASEGS fx R (pc h) M model) (RD cap fs).
Proof.
  intros h e3 len cap He H43 HL Hc E fx R M model HC H3v.
  pose proof (f_equal fst H43) as H4. pose proof (f_equal snd H43) as H3. cbn [fst snd] in H4, H3.
  destruct (co_uinv HC) as [_ (HX & _ & _)].
  assert (HX' : UXc data (tenv E (THc h))) by (split; [exact (UXf_tenv' E _ H4 HX) | split; [rewrite (tenv_uE E _ 3%nat e3 H3); exact H3v | intros X; lia]]).
  destruct (rebase I a0 p fs data (di_AINVH1 I) (UXr data len cap) (UXc data) NXC _ h tinC3 E fx R M model HC He H4 HX') as [HC2 Hpc].
  rewrite <- Hpc, (RD_body cap fs (or_introl Hc)), (body_ok HL). exact (C3_spec I a0 p fs data FHY _ fx R M model HC2).
Qed.

(* [comment removed for export] *)
Definition RDH (m : nat) : Prop := forall len cap E fx R M model,
  (Z.to_nat (L - len) < m)%nat -> WF len cap -> csAr len cap E TR fx R M model -> RZ (cfgF ASEGS fx R (pc TR) M model) (RD cap fs).

(* [comment removed for export] *)
Lemma to_TR : forall m h e3 e2 len cap len' cap', RDH m -> ENTR h TR = true ->
  (nth_error (THr h TR) 4%nat, nth_error (THr h TR) 3%nat, nth_error (THr h TR) 2%nat) = (Some (EVar 4), Some e3, Some e2) ->
  (Z.to_nat (L - len') < m)%nat -> WF len' cap' ->
  forall E fx R M model, csAr len cap E h fx R M model -> uE E e3 = len' -> uE E e2 = cap' ->
  RZ (cfgF ASEGS fx R (pc h) M model) (RD cap' fs).
Proof.
  intros m h e3 e2 len cap len' cap' IH He H432 Hm HW E fx R M model HC H3v H2v.
  pose proof (f_equal (fun x => fst (fst x)) H432) as H4. pose proof (f_equal (fun x => snd (fst x)) H432) as H3. pose proof (f_equal snd H432) as H2.
  cbn [fst snd] in H4, H3, H2.
  destruct (co_uinv HC) as [_ (HX & _ & _)].
  assert (HX' : UXr data len' cap' (tenv E (THr h TR))).
  { split; [exact (UXf_tenv' E _ H4 HX)|]. rewrite (tenv_uE E _ 3%nat e3 H3), (tenv_uE E _ 2%nat e2 H2). split; assumption. }
  destruct (rebase I a0 p fs data (di_AINVH1 I) (UXr data len cap) (UXr data len' cap') NXR _ h TR E fx R M model HC He H4 HX') as [HC2 Hpc].
  rewrite <- Hpc. exact (IH len' cap' _ fx R M model Hm HW HC2).
Qed.

Lemma round : forall m, RDH m -> RDH (Datatypes.S m).
Proof.
  intros m IH len cap E fx R M model Hm (Wd & Wl & Wc & Wp & WL) HC.
  destruct (tr_vals len cap E TR fx R M model HC) as (VF & V3 & V2 & VB).
  destruct (pow64k_le cap Wp) as (Pc & Pd & Pv).
  assert (HLle : L <= 2 ^ 26) by (unfold APS.flen; lia).
  assert (HLLD : L <= LD) by (unfold APS.flen; lia).
  assert (HREM : uE E REMX = L - len) by (unfold REMX, LEN; rewrite uE_esub, VF, V3; apply Z.mod_small; lia).
  assert (HROOM : uE E ROOMX = cap - len) by (unfold ROOMX, CAP, LEN; rewrite uE_esub, V2, V3; apply Z.mod_small; lia).
  pose proof (hdr_cfglen_range data) as Rc. pose proof (cfgx_hdr data E VB) as HCf.
  pose proof (b0_val data E VB) as HB0. pose proof (hdr_byte_range data 0) as RB0. pose proof (b2_rng E) as RB2.
  pose proof (u64_range (edenot E B1S)) as RB1. change (bv_unsigned (edenot E B1S)) with (uE E B1S) in RB1.
  assert (HFC : 65536 <= L -> Forall (kentry_ok ASEGS E (Mr (di_SHC I) (VSHf (di_HID I) (di_HIDF I)) E TR model M)) factsC).
  { intros HL6.
    assert (HO : uE E PAYXb = L - (hdr_cfglen data + 6)).
    { unfold PAYXb. rewrite uE_esub, uE_eadd, uE_lit, HCf, VF by lia. rewrite (Z.mod_small (hdr_cfglen data + 6)) by lia. apply Z.mod_small. lia. }
    unfold factsC. repeat (constructor; [apply kr_ok|]); [lia | lia | lia | lia | lia | constructor]. }
  destruct (Z.eq_dec (L - len) 0) as [R0 | R0]; [|destruct (Z_lt_ge_dec (L - len) 65536) as [RS | RF]].
  - (* [comment removed for export] *)
    assert (HLD : LD = L /\ 65536 <= LD < 2 ^ 26) by (unfold APS.flen in *; lia). destruct HLD as [HLD HLr].
    assert (HCk : csAr len cap E tV0c fx R M model).
    { unfold tV0c, tV0. apply add_facts; [apply add_facts; [exact HC|]; constructor; [apply kr_ok; lia | constructor] | apply HFC; lia]. }
    pose proof (RUNr len cap (RD cap) (fun _ fs' => RD_has_nil cap fs') (HSof1 hV0c) planV0 tV0c _ gplanV0 certV0c_a) as H.
    assert (HH : forall h ch, HSof1 hV0c h = Some ch -> forall E0 fx0 R0' M1 model0, csAr len cap E0 ch fx0 R0' M1 model0 ->
                   RZ (cfgF ASEGS fx0 R0' (pc ch) M1 model0) (RD cap fs)).
    { intros h ch Hh E0 fx0 R0' M1 model0 HC0. destruct h as [|[|h]]; try discriminate Hh. injection Hh as <-.
      destruct (tr_vals len cap E0 hV0c fx0 R0' M1 model0 HC0) as (_ & V3' & _ & _).
      exact (to_C3r hV0c (EVar 3) len cap entV0c th_V0c HLr ltac:(lia) E0 fx0 R0' M1 model0 HC0 ltac:(lia)). }
    exact (H HH E fx R M model HCk).
  - (* [comment removed for export] *)
    assert (HLD : LD = L /\ 65536 <= LD < 2 ^ 26) by (unfold APS.flen in *; lia). destruct HLD as [HLD HLr].
    assert (HCk : csAr len cap E tVSc fx R M model).
    { unfold tVSc, tVS. apply add_facts; [apply add_facts; [exact HC|]; constructor; [apply kr_ok; lia | constructor] | apply HFC; lia]. }
    pose proof (RUNr len cap (RD cap) (fun _ fs' => RD_has_nil cap fs') (HSq hVSc) planVS tVSc _ gplanVS certVSc_a) as H.
    assert (HH : forall h ch, HSq hVSc h = Some ch -> forall E0 fx0 R0' M1 model0, csAr len cap E0 ch fx0 R0' M1 model0 ->
                   RZ (cfgF ASEGS fx0 R0' (pc ch) M1 model0) (RD cap fs)).
    { intros h ch Hh E0 fx0 R0' M1 model0 HC0.
      destruct (tr_vals len cap E0 ch fx0 R0' M1 model0 HC0) as (VF' & _ & _ & _). unfold FLEN in VF'.
      destruct entVSc_all as (e1 & e2 & e3 & e4).
      pose proof th_VSc as T. pose proof (f_equal (fun x => fst (fst (fst x))) T) as T1. pose proof (f_equal (fun x => snd (fst (fst x))) T) as T2.
      pose proof (f_equal (fun x => snd (fst x)) T) as T3. pose proof (f_equal snd T) as T4. cbn [fst snd] in T1, T2, T3, T4.
      destruct (HSq_VSc h ch Hh) as [-> | [-> | [-> | ->]]].
      - exact (to_C3r hVSc1 (EVar 4) len cap e1 T1 HLr ltac:(lia) E0 fx0 R0' M1 model0 HC0 ltac:(lia)).
      - exact (to_C3r hVSc2 (EVar 4) len cap e2 T2 HLr ltac:(lia) E0 fx0 R0' M1 model0 HC0 ltac:(lia)).
      - exact (to_C3r hVSc3 (EVar 4) len cap e3 T3 HLr ltac:(lia) E0 fx0 R0' M1 model0 HC0 ltac:(lia)).
      - exact (to_C3r hVSc4 (EVar 4) len cap e4 T4 HLr ltac:(lia) E0 fx0 R0' M1 model0 HC0 ltac:(lia)). }
    specialize (H HH E fx R M model HCk). cbn [GPS.sd] in H. destruct (_ <=? _) in H; exact H.
  - (* [comment removed for export] *)
    assert (Hdiv : (65536 | cap - len)) by (apply Z.divide_sub_r; assumption).
    destruct (Z.eq_dec (cap - len) 65536) as [RM | RM].
    + (* [comment removed for export] *)
      destruct Pd as [Pd | Pd].
      * (* [comment removed for export] *)
        assert (HCk : csAr len cap E tVF fx R M model).
        { unfold tVF. apply add_facts; [exact HC|]. repeat (constructor; [apply kr_ok|]); [unfold FLENHI; lia | lia | unfold CAP; lia | constructor]. }
        assert (HW' : WF (len + 65536) (2 * cap)).
        { split; [apply Z.divide_add_r; [exact Wd | exists 1; lia]|]. split; [lia|]. split; [lia|]. split; [exact (pow64k_double cap Wp Pd) | lia]. }
        assert (Hm' : (Z.to_nat (L - (len + 65536)) < m)%nat) by lia.
        pose proof (RUNr len cap (RD (2 * cap)) (fun _ fs' => RD_has_nil (2 * cap) fs')
                      (HSof1 hVF) planVF tVF _ gplanVF certVF_a) as H.
        assert (HH : forall h ch, HSof1 hVF h = Some ch -> forall E0 fx0 R0' M1 model0, csAr len cap E0 ch fx0 R0' M1 model0 ->
                       RZ (cfgF ASEGS fx0 R0' (pc ch) M1 model0) (RD (2 * cap) fs)).
        { intros h ch Hh. destruct h as [|[|h]]; try discriminate Hh. injection Hh as <-.
          intros E0 fx0 R0' M1 model0 HC0. destruct (tr_vals len cap E0 hVF fx0 R0' M1 model0 HC0) as (_ & V30 & _ & _).
          assert (Hsec : 64512 < uE E0 (reg hVF 10)) by (rewrite reg_hVF, (uE_CAP2 E0 len V30) by lia; lia).
          revert E0 fx0 R0' M1 model0 HC0 V30 Hsec. intros E0 fx0 R0' M1 model0 HC0 _ Hsec.
          refine (m1g1 I a0 p fs data FHY (UXr data len cap) (UXr_a data len cap) hVF hVFz hVFok _ M12_hVF (RD_has_nil _ _) _ E0 fx0 R0' M1 model0 HC0 Hsec).
          + intros E1 fx1 R1 M2 model1 HC1.
            pose proof (RUNr len cap (RD (2 * cap)) (fun _ fs' => RD_has_nil (2 * cap) fs') (HSof1 hVG) planG hVFok _ gplanG certVG_a) as HG.
            refine (HG _ E1 fx1 R1 M2 model1 HC1).
            intros h ch Hh E2 fx2 R2 M3 model2 HC2. destruct h as [|[|h]]; try discriminate Hh. injection Hh as <-.
            destruct (tr_vals len cap E2 hVG fx2 R2 M3 model2 HC2) as (_ & V3' & _ & _).
            exact (to_TR m hVG LEN65 CAP2 len cap (len + 65536) (2 * cap) IH entVG th_VG Hm' HW' E2 fx2 R2 M3 model2 HC2
                     (uE_LEN65 E2 len V3' ltac:(lia)) ltac:(rewrite (uE_CAP2 E2 len V3') by lia; lia)). }
        eapply RZ_conseq_rz; [exact (H HH E fx R M model HCk)|]. cbn [GPS.sd]. unfold RD. apply t_eq_refl.
      * (* [comment removed for export] *)
        assert (HCk : csAr len cap E tVR fx R M model).
        { unfold tVR. apply add_facts; [exact HC|]. repeat (constructor; [apply kr_ok|]); [unfold FLENHI; lia | lia | unfold CAP; lia | constructor]. }
        assert (HLD : 2 ^ 26 <= LD) by (unfold APS.flen in *; lia).
        assert (Hc26 : 2 ^ 26 <= cap) by lia.
        rewrite (RD_body cap fs (or_intror Hc26)), (body_refused HLD).
        eapply RZ_conseq_rz; [exact (RUNr len cap (fun _ : Fs.Fs => t_nil) (fun _ _ => eq_refl) HS0 planVR tVR shapeRF gplanVR certVR_a
                                       (fun h ch Hh => ltac:(discriminate Hh)) E fx R M model HCk)|].
        rewrite <- zmsg_rf_ok. unfold shapeRF. apply sd_lit1A.
    + (* [comment removed for export] *)
      assert (Hroom : 131072 <= cap - len) by (destruct Hdiv as [q Hq]; nia).
      assert (HCk : csAr len cap E tVP fx R M model).
      { unfold tVP. apply add_facts; [exact HC|]. repeat (constructor; [apply kr_ok|]); [unfold FLENHI; lia | lia | constructor]. }
      assert (HW' : WF (len + 65536) cap).
      { split; [apply Z.divide_add_r; [exact Wd | exists 1; lia]|]. split; [lia|]. split; [lia|]. split; [exact Wp | lia]. }
      assert (Hm' : (Z.to_nat (L - (len + 65536)) < m)%nat) by lia.
      pose proof (RUNr len cap (RD cap) (fun _ fs' => RD_has_nil cap fs') (HS12 hVP1 hVP2) planVP tVP _ gplanVP certVP_a) as H.
      refine (H _ E fx R M model HCk).
      intros h ch Hh E0 fx0 R0' M1 model0 HC0. destruct (tr_vals len cap E0 ch fx0 R0' M1 model0 HC0) as (_ & V3' & V2' & _).
      destruct h as [|[|[|h]]]; try discriminate Hh; injection Hh as <-.
      * exact (to_TR m hVP1 LEN65 (EVar 2) len cap (len + 65536) cap IH entVP1 th_VP1 Hm' HW' E0 fx0 R0' M1 model0 HC0 (uE_LEN65 E0 len V3' ltac:(lia)) V2').
      * (* [comment removed for export] *)
        exfalso. pose proof th_VP2 as T. pose proof (f_equal (fun x => fst (fst x)) T) as T4. pose proof (f_equal (fun x => snd (fst x)) T) as T3.
        pose proof (f_equal snd T) as T2. cbn [fst snd] in T4, T3, T2.
        destruct (rebase I a0 p fs data (di_AINVH1 I) (UXr data len cap) (fun _ => True) NXR _ hVP2 TRw E0 fx0 R0' M1 model0 HC0 entVP2 T4 Logic.I) as [HCw _].
        pose proof (has_fact_sound _ _ (kn TRw) fROOMw (co_know HCw) fact_TRw) as K. cbn [kentry_ok fROOMw] in K.
        change (bv_unsigned (edenot ?e ROOMX)) with (uE e ROOMX) in K. unfold ROOMX, CAP, LEN in K.
        rewrite uE_esub, (tenv_uE _ _ 2%nat _ T2), (tenv_uE _ _ 3%nat _ T3), V2', (uE_LEN65 E0 len V3') in K by lia.
        rewrite Z.mod_small in K by lia. lia.
Qed.

Theorem rd_main : forall m, RDH m.
Proof. induction m as [|m IH]; [intros len cap E fx R M model Hm; lia | exact (round m IH)]. Qed.

(* [comment removed for export] *)
Theorem S2_spec : 65536 <= LD -> forall E fx R M model, csAf E hN1f fx R M model ->
  RZ (cfgF ASEGS fx R (pc hN1f) M model) (t_body data fs).
Proof.
  intros HL E fx R M model HC.
  destruct (co_uinv HC) as [HU HX].
  assert (HF : uE E FLEN = L) by (unfold uE, FLEN; cbn [edenot]; exact HX).
  assert (HLl : 65536 <= L <= 2 ^ 26) by (unfold APS.flen; lia).
  assert (HCk : csAf E tR1F fx R M model) by (unfold tR1F; apply add_facts; [exact HC|]; constructor; [apply kr_ok; unfold FLENHI; lia | constructor]).
  pose proof (RUNf (RD 131072) (fun _ fs' => RD_has_nil 131072 fs') (HSof1 hG1) planR1F tR1F _ gplanR1F certR1F) as H.
  eapply RZ_conseq_rz; [refine (H _ E fx R M model HCk) | cbn [GPS.sd]; unfold RD; apply t_eq_refl].
  intros h ch Hh. destruct h as [|[|h]]; try discriminate Hh. injection Hh as <-.
  intros E0 fx0 R0 M1 model0 HC0.
  assert (Hsec : 64512 < uE E0 (reg hG1 10)) by (rewrite reg_hG1, uE_lit by lia; lia).
  refine (m1g1 I a0 p fs data FHY (UXf data) (UXf_a data) hG1 hG1z hG1ok _ M12_hG1 (RD_has_nil _ _) _ E0 fx0 R0 M1 model0 HC0 Hsec).
  - intros E1 fx1 R1 M2 model1 HC1.
    pose proof (RUNf (RD 131072) (fun _ fs' => RD_has_nil 131072 fs') (HSof1 hRD2) planG hG1ok _ gplanG certG1) as HG.
    refine (HG _ E1 fx1 R1 M2 model1 HC1).
    intros h ch Hh E2 fx2 R2 M3 model2 HC2. destruct h as [|[|h]]; try discriminate Hh. injection Hh as <-.
    pose proof th_RD2 as T. pose proof (f_equal (fun x => fst (fst x)) T) as T4. pose proof (f_equal (fun x => snd (fst x)) T) as T3.
    pose proof (f_equal snd T) as T2. cbn [fst snd] in T4, T3, T2.
    pose proof (proj2 (co_uinv HC2)) as HX2.
    assert (HX' : UXr data 65536 131072 (tenv E2 (THr hRD2 TR))).
    { split; [exact (UXf_tenv' E2 _ T4 HX2)|]. rewrite (tenv_uE E2 _ 3%nat _ T3), (tenv_uE E2 _ 2%nat _ T2), !uE_lit by lia. split; reflexivity. }
    destruct (rebase I a0 p fs data (di_AINVH1 I) (UXf data) (UXr data 65536 131072) NXR _ hRD2 TR E2 fx2 R2 M3 model2 HC2 entG1 T4 HX') as [HC3 Hpc].
    rewrite <- Hpc.
    apply (rd_main (Datatypes.S (Z.to_nat (L - 65536))) 65536 131072 (tenv E2 (THr hRD2 TR)) fx2 R2 M3 model2 (Nat.lt_succ_diag_r _)); [|exact HC3].
    split; [exists 1; lia|]. split; [lia|]. split; [lia|]. split; [exists 1; split; [lia | reflexivity] | lia].
Qed.
End S2SpecA.
End AsDrvS2SpecA.
Module AsDrvFileSpecA.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvS0A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvS1A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvTSpecA.AsDrvZcertsA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA.AsDrvNodesAllA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA.AsDrvUinvA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA.AsDrvCertSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvCertSoundZ.AsDrvS0SpecA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvCertSoundZ OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvGlueA.AsDrvGlueLibA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvGlueA AsDrvK0SpecA AsDrvS2SpecA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.
#[local] Notation RZ := (realizes ASEGS).

Lemma gplanF0 : gplan_ok planF0 = true. Proof. vmc. Qed.
Lemma reg_hM1f : reg hM1f 10 = ELit 65536. Proof. vmc. Qed.

Section FileSpecA.
Context {RC : run_ceil}.
Context {SFL : stk_floor}.
Variable I : dinst.
Variables (a0 p : list byte) (fs : Fs.Fs) (data : list byte).
Hypothesis FHY : file_hyps I a0 p fs data.
#[local] Notation csAf := (cs1 I a0 p fs data (UXf data)).      (* [comment removed for export] *)
#[local] Notation LD := (Z.of_nat (length data)).

(* [comment removed for export] *)
Lemma file_hole : forall E fx R M model, csAf E hM1f fx R M model -> RZ (cfgF ASEGS fx R (pc hM1f) M model) (t_opened data fs).
Proof.
  intros E fx R M model HC. rewrite t_opened_eq.
  assert (Hsec : 64512 < uE E (reg hM1f 10)) by (rewrite reg_hM1f, uE_lit by lia; lia).
  refine (m1g1 I a0 p fs data FHY (UXf data) (UXf_a data) hM1f hZ1f hN1f _ M12_hM1f (t_body_has_nil _ _) _ E fx R M model HC Hsec).
  destruct (Z_lt_ge_dec LD 65536) as [HL | HL].
  - exact (K0_spec I a0 p fs data FHY HL).
  - exact (S2_spec I a0 p fs data FHY ltac:(lia)).
Qed.

Theorem file_spec : forall E fx R M model, csAf E tMf fx R M model ->
  RZ (cfgF ASEGS fx R (pc tMf) M model) (t_alt2 (t_die (msg_cannot_open p) fs) (t_opened data fs)).
Proof.
  intros E fx R M model HC.
  pose proof (run_1 I a0 p fs data FHY (UXf data) (UXf_a data) (fun _ fs' => t_opened data fs') (fun _ _ _ _ => eq_refl)
                (fun _ fs' => t_opened_has_nil data fs') (HSof1 hM1f) planF0 tMf shapeF0 gplanF0 certF0) as H.
  assert (HH : forall h ch, HSof1 hM1f h = Some ch -> forall E0 fx0 R0 M1 model0, csAf E0 ch fx0 R0 M1 model0 ->
                 RZ (cfgF ASEGS fx0 R0 (pc ch) M1 model0) (t_opened data fs)).
  { intros h ch Hh. destruct h as [|[|h]]; try discriminate Hh. injection Hh as <-. exact file_hole. }
  eapply RZ_conseq_rz; [exact (H HH E fx R M model HC)|]. unfold shapeF0. cbn [GPS.sd]. apply Spec4.AgentLib.t_alt2_congr; [|apply t_eq_refl].
  pose proof (proj1 (proj2 (proj1 (co_uinv HC)))) as Hp. rewrite <- Hp. apply sd_shapeCOa.
Qed.
End FileSpecA.
End AsDrvFileSpecA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeLG OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeE OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgePR OSSVerify.Proofs.glaze.binary_reflection.lib.AzInstA OSSVerify.Proofs.glaze.binary_reflection.lib.AzInstAE OSSVerify.Proofs.glaze.binary_reflection.lib.AzInstAN OSSVerify.Proofs.glaze.binary_reflection.lib.AzInstAP OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvMainA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvMainA2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs OSSVerify.Proofs.glaze.binary_reflection.lib.AsSInit OSSVerify.Proofs.glaze.binary_reflection.lib.AsImages OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvCertSoundZ OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvMainBridgeA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvMainCertA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvGlueA. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeLG OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeH OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeE OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AzBridgePR OSSVerify.Proofs.glaze.binary_reflection.lib.AzInstA OSSVerify.Proofs.glaze.binary_reflection.lib.AzInstAE OSSVerify.Proofs.glaze.binary_reflection.lib.AzInstAN OSSVerify.Proofs.glaze.binary_reflection.lib.AzInstAP OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIfaceNM3.AsIfacePR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvBoot3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvDrvHist3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvMainA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvMainA2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsSDefs OSSVerify.Proofs.glaze.binary_reflection.lib.AsSInit OSSVerify.Proofs.glaze.binary_reflection.lib.AsImages OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsStartupHSc OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA.AsDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvS0A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvS1A OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA3.AsDrvGSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvNodesSoundA11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS2A.AsDrvInstFactsA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA.AsDrvUinvA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA.AsDrvCertSoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvS0SoundA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvCertSoundZ.AsDrvS0SpecA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvMainBridgeA.AsDrvBridgeArgv OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvMainCertA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvMainBridgeA AsDrvExtA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvCertSoundZ AsDrvDirSpecA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvGlueA AsDrvFileSpecA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import AzImageAsan.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
#[local] Notation u := bv_unsigned.
#[local] Notation RZ := (realizes ASEGS).

(* [comment removed for export] *)
Definition DRV_EXT {RC : run_ceil} (hv : AsAinvBoot3.bvars) (KCAP : Z) : Prop :=
  AsIfaceNM3.as_contracts_n ASEGS fx_ok (bt_ia (asan_bt hv)) (AAINV_HS (asan_bt hv)) (AsAllocFFam.AsAinvPrist3.FRESH_bt (asan_bt hv)) (bt_fs (asan_bt hv))
  /\ AsIfaceNM3.as_contracts_nm ASEGS fx_ok (bt_ia (asan_bt hv)) (AAINV_H (asan_bt hv)) (bt_fs (asan_bt hv))
  /\ AsIfaceNM3.AsIfacePR3.as_contracts_pr ASEGS fx_ok (bt_ia (asan_bt hv)) (AsAllocFFam.AsAinvDrvHist3.AAINV_DRX (asan_bt hv)) (bt_fs (asan_bt hv))
  /\ callee_contract ASEGS PERM_A_lit GASAN fx_ok RZ (AzBridgeH.SHC_bt (asan_bt hv)) KCAP (AzBridgeH.AINVH_bt (asan_bt hv)) AsDrvHooksA.AsFZ.ceN
  /\ callee_contract ASEGS PERM_A_lit GASAN fx_ok RZ (AzBridgeH.SHC_bt (asan_bt hv)) KCAP (AzBridgeH.AINVH_bt (asan_bt hv)) AsDrvHooksA.AsFZ.ceE.

Lemma perm_lt47 : forall z, in_wins PERM_A_lit z -> z < two47.
Proof.
  intros z (lo & hi & Hin & Hz). destruct (SWIN_img_A lo hi Hin) as (_ & H2 & _). cbn [g_img_hi GASAN] in H2. unfold two47. lia.
Qed.

(* [comment removed for export] *)
Lemma ainv_wrap : forall {RC : run_ceil} (bt : as_boot) (X : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop)
    (SPTOP : Z) (M : word -> option byte) (model : Model),
  X [] [] 0 0 0 M model -> GlzConst.RunCeil.CEIL <= SPTOP -> SPTOP mod 8 = 0 ->
  AINV_f PERM_A_lit GASAN (AzBridgeH.AINVw (AzBridgeLG.AAINV_LG X)) PERM_A_lit SPTOP [] [] M 0 0 [] [] 0 0 0 M model.
Proof.
  intros RC bt X SPTOP M model HA H1 H2. unfold AINV_f. cbn [app]. change (0 + 0) with 0.
  split; [|split; [|split; [split; assumption|split]]].
  - exists []. split; [reflexivity|]. split; [exact HA|]. intros b n Hin. destruct Hin.
  - split; [intros z Hz; right; right; right; exact Hz | exact perm_lt47].
  - intros a _. reflexivity.
  - intros a _ X0. exact X0.
Qed.

Section MainA.
Variables (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word) (fs : Fs.Fs).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Variable KCAP : Z.
Hypothesis HKCAP : 0 <= KCAP.
Hypothesis HKG : GKCAP <= KCAP.
Hypothesis EXT : forall (RC : run_ceil) (hv : AsAinvBoot3.bvars),
  AsKSys10.AsAinvBootF3.boot_facts (asan_bt hv) -> AsKSys10.AsKSys11.boot_totals (asan_bt hv) -> @DRV_EXT RC hv KCAP.
#[local] Notation SINV := (AsSInit.SINV0 ph sp rdraw brk0 argv envp uid hw).
#[local] Notation argH := (AsSInit.argH0 ph sp rdraw argv envp uid hw).
#[local] Notation CSOK := (APS.cs_ok ASEGS AT_A LIMIT_S SINV argH ISP_S fs).

Variable hs : acs.
Hypothesis Hhs : hs = HS_1 \/ hs = HS_2.
Variables (E : env) (fx : GPS.FX) (R : bvmap 5 word) (M : word -> option byte) (model : Model).
Hypothesis HC : CSOK E hs R M model.
Hypothesis Hfx : fx_ok fx.

Lemma pc_hs : pc hs = P_MAIN. Proof. destruct Hhs as [-> | ->]; reflexivity. Qed.

Lemma alloc_top_main : alloc_top (m_vmmaps model) = u sp - 8388608.
Proof.
  unfold alloc_top. rewrite (APS.co_isp _ _ _ _ _ _ _ _ _ _ _ _ HC). rewrite stack_max_size_val.
  change ISP_S with e_sp0. rewrite (sp0_val ph sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit hs E R M model HC). reflexivity.
Qed.
Lemma at_rng : CEIL0 <= alloc_top (m_vmmaps model) <= CEILMAX.
Proof. rewrite alloc_top_main, <- stack_max_size_val. exact (alloc_top_rng_of_valid_sp sp Hsp). Qed.
Definition RCm : run_ceil := run_ceil_of_top (alloc_top (m_vmmaps model)) at_rng.
#[local] Existing Instance RCm.
Lemma RCm_ceil : @GlzConst.RunCeil.CEIL RCm = page_floor (u sp - 8388608).
Proof. cbn [GlzConst.RunCeil.CEIL RCm run_ceil_of_top]. rewrite alloc_top_main. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ainv_main : exists hv : AsAinvBoot3.bvars,
  @AsKSys10.AsAinvBootF3.boot_facts RCm (asan_bt hv) /\ AsKSys10.AsKSys11.boot_totals (asan_bt hv)
  /\ @AsAllocFFam.AsAinvDrvHist3.AAINV_DR RCm (asan_bt hv) [] [] 0 0 0 M model.
Proof.
  destruct Hhs as [Hh | Hh]; pose proof HC as HC'; rewrite Hh in HC'.
  - exists (@AsAinvMainA.hv RCm E model).
    split; [exact (@AsAinvMainA.boot_facts_main_1 RCm SINV argH fs E R M model HC' eq_refl)|].
    split; [exact (@AsAinvMainA.boot_totals_main RCm SINV argH fs E R M model HC' eq_refl)|].
    exact (@AsAinvMainA.AAINV_DR_at_main_1 RCm SINV argH fs asan_S_in_hull (AsSInit.argH0_high ph sp rdraw argv envp uid hw Hsp Hva) E R M model HC' eq_refl).
  - exists (@AsAinvMainA2.hv RCm E model).
    split; [exact (@AsAinvMainA2.boot_facts_main_2 RCm SINV argH fs E R M model HC' eq_refl)|].
    split; [exact (@AsAinvMainA2.boot_totals_main RCm SINV argH fs E R M model HC' eq_refl)|].
    exact (@AsAinvMainA2.AAINV_DR_at_main_2 RCm SINV argH fs asan_S_in_hull (AsSInit.argH0_high ph sp rdraw argv envp uid hw Hsp Hva) E R M model HC' eq_refl).
Qed.

(* [comment removed for export] *)
Section At.
Variable hv : AsAinvBoot3.bvars.
#[local] Notation bt := (asan_bt hv).
Hypothesis XT : @DRV_EXT RCm hv KCAP.
Let ASCN := proj1 XT.
Let ASCNM := proj1 (proj2 XT).   (* [comment removed for export] *)
Let ASCD := proj1 (proj2 (proj2 XT)).
Let FZN := proj1 (proj2 (proj2 (proj2 XT))).
Let FZE := proj2 (proj2 (proj2 (proj2 XT))).
Lemma HPbt : hprops PERM_A_lit GASAN (@AzBridgeH.SHC_bt RCm bt) (@AzBridgeH.AINVH_bt RCm bt).
Proof. exact (AzBridgeH.hprops_bt bt PERM_A_lit GASAN eq_refl eq_refl asan_G_ro_img2 drvA_G_img_al GASAN_errno SWIN_ok_A drvA_G_img_shlo). Qed.
Lemma GCA : forall SPTOPc fs0 a0 p data (UX : env -> Prop) M0, uxa UX ->
  gcontracts ASEGS ITA AASAN NXD PERM_A_lit SPTOPc fs0 (@AzBridgeH.SHC_bt RCm bt) (VSHf [] [])
    (AINV_f PERM_A_lit GASAN (@AzBridgeH.AINVH_bt RCm bt) PERM_A_lit SPTOPc [] [] M0 0 0) KCAP FMIN fx_ok (UINVd a0 p fs0 data UX) RZ GASAN BCAP CCAP.
Proof.
  intros SPTOPc fs0 a0 p data UX M0 HUX.
  exact (gcontracts_asan_all_f bt eq_refl (AsAllocFFam.AsAinvPrist3.FRESH_bt bt) ASCN PERM_A_lit SWIN_ok_A SWIN_img_A PERM_A_lit SPTOPc [] [] 0 0 (Z.le_refl 0) (Z.le_refl 0)
           BCAP CCAP ltac:(unfold BCAP; lia) ltac:(unfold CCAP; lia) FMIN ltac:(cbn; lia) KCAP HKG ITA ITA_ok NXD fs0 (UINVd a0 p fs0 data UX)
           (UINVd_agree a0 p fs0 data UX HUX) M0).
Qed.

(* [comment removed for export] *)
Definition Irun (SPTOP : Z) : dinst :=
  DI (@AzBridgeH.SHC_bt RCm bt) KCAP (@AzBridgePR.AINVH_pr RCm bt AsAllocFFam.AsAinvDrvHist3.drv_hist) (@AzBridgeH.AINVH_bt RCm bt)
     PERM_A_lit SPTOP [] [] M 0 0 FMIN.
Lemma fhyps : forall SPTOP a0 p data, @file_hyps RCm stk_floor_default (Irun SPTOP) a0 p fs data.
Proof.
  intros SPTOP a0 p data.
  constructor; cbn [Irun di_SHC di_KCAP di_AINVH1 di_AINVH di_SWIN di_SPTOP di_HID di_HIDF di_M0 di_B0 di_C0 di_FTOP].
  - exact (AzInstAP.hprops_asan_pr bt eq_refl AsAllocFFam.AsAinvDrvHist3.drv_hist PERM_A_lit SWIN_ok_A).
  - exact HPbt.
  - exact SWIN_img_A.
  - lia.
  - lia.
  - unfold BCAP; lia.
  - unfold CCAP; lia.
  - cbn; lia.
  - intros UX HUX M0. exact (GCA SPTOP fs a0 p data UX M0 HUX).
  - exact FZN.
  - exact FZE.
  - intros UX HUX M0.
    exact (AzInstAP.gcontracts_core_asan_pr_f bt eq_refl AsAllocFFam.AsAinvDrvHist3.drv_hist ASCD PERM_A_lit SWIN_ok_A SWIN_img_A PERM_A_lit SPTOP [] [] 0 0 (Z.le_refl 0) (Z.le_refl 0)
             FMIN ltac:(cbn; lia) KCAP HKG ITA ITA_ok NXD fs (UINVd a0 p fs data UX) (UINVd_agree a0 p fs data UX HUX) M0).
  - exact (conj (M2S_H_AP hv _) (conj (DTOR_H_AP hv _) (DTOR_FRAME_AP hv _))).
  - exact (conj (M2S_H_AP hv _) (conj (DTOR_H_AP hv _) (DTOR_FRAME_AP hv _))).
  - intros UX E0 cs fx0 R0 M1 model0 HC0.
    exact (AzBridgePR.cs_ok_pr_weaken bt AsAllocFFam.AsAinvDrvHist3.drv_hist ASEGS fx_ok GASAN PERM_A_lit PERM_A_lit SPTOP [] [] M 0 0 FMIN KCAP fs (UINVd a0 p fs data UX) E0 cs fx0 R0 M1 model0 HC0).
  - intros UX HUX tm csa csb E0 fx0 R0 M1 model0 Tb HC0 HM Hn HTb HB.
    exact (AzInstAP.malloc1_glue_asan_pr_f bt eq_refl AsAllocFFam.AsAinvDrvHist3.drv_hist ASCD PERM_A_lit SWIN_ok_A SWIN_img_A PERM_A_lit SPTOP [] [] 0 0 FMIN KCAP HKG NXD fs
             (UINVd a0 p fs data UX) (UINVd_agree a0 p fs data UX HUX) BCAP CCAP ltac:(unfold BCAP; lia) ltac:(unfold CCAP; lia) M [] tm csa csb E0 fx0 R0 M1 model0 Tb
             HC0 HM Hn HTb HB).
  - intros UX HUX tm csa csb E0 fx0 R0 M1 model0 Tb HC0 HM HF Hn Hk HTb HB.
    pose proof (AzBridgePR.cs_ok_pr_weaken bt AsAllocFFam.AsAinvDrvHist3.drv_hist ASEGS fx_ok GASAN PERM_A_lit PERM_A_lit SPTOP [] [] M 0 0 FMIN KCAP fs (UINVd a0 p fs data UX)
                  E0 tm fx0 R0 M1 model0 HC0) as HCw.
    assert (FS : AzBridgeM2.fresh_site (AsAllocFFam.AsAinvPrist3.FRESH_bt bt) [] [] 0 0 E0 tm M1 model0).
    { apply (AzBridgePR.fresh_site_q bt AsAllocFFam.AsAinvDrvHist3.drv_hist ASEGS fx_ok GASAN PERM_A_lit PERM_A_lit SPTOP [] [] M 0 0 FMIN KCAP fs (UINVd a0 p fs data UX)
               (AsAllocFFam.AsAinvPrist3.FRESH_bt bt) E0 tm fx0 R0 M1 model0 HC0).
      intros FF HPR. exact (AsAllocFFam.AsAinvDrvHist3.FRESH_PAY bt _ FF _ _ _ M1 model0 _ Hn HPR Hk). }
    exact (AzInstAN.malloc1_glue_asan_f bt eq_refl (AsAllocFFam.AsAinvPrist3.FRESH_bt bt) ASCN PERM_A_lit SWIN_ok_A SWIN_img_A PERM_A_lit SPTOP [] [] 0 0 FMIN KCAP HKG NXD fs
             (UINVd a0 p fs data UX) (UINVd_agree a0 p fs data UX HUX) BCAP CCAP ltac:(unfold BCAP; lia) ltac:(unfold CCAP; lia) M [] tm csa csb E0 fx0 R0 M1 model0 Tb
             HCw HM FS HTb HB).
Qed.
End At.

(* [comment removed for export] *)
Definition SPEC_T (tX : acs) (T : list byte -> list byte -> Fs.Fs -> list byte -> TSet) : Prop :=
  forall (RC : run_ceil) (SFL : stk_floor) (SHC : list (Z * Z)) (KCAP0 : Z)
    (AINVH : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop) (SWIN : list (Z * Z)),
    hprops SWIN GASAN SHC AINVH ->
    (forall lo hi, In (lo, hi) SWIN -> g_ro_hi GASAN <= lo /\ hi <= g_img_hi GASAN /\ (forall plo phi, In (plo, phi) (g_priv GASAN) -> hi <= plo \/ phi <= lo)) ->
    forall (SPTOPc : Z) (HIDc HIDFc : list (Z * Z)) (M0c : word -> option byte) (B0c C0c : Z),
    0 <= B0c -> 0 <= C0c -> B0c + BCAP <= GBUDGET -> C0c + CCAP <= GCOUNT ->
    forall FTOPc : Z, Z.of_nat (length HIDFc) + FTOPc <= FMIN ->
    forall (a0 p : list byte) (fs0 : Fs.Fs) (data : list byte),
    (forall M0 : word -> option byte,
       gcontracts ASEGS ITA AASAN NXD PERM_A_lit SPTOPc fs0 SHC (VSHf HIDc HIDFc) (AINV_f SWIN GASAN AINVH PERM_A_lit SPTOPc HIDc HIDFc M0 B0c C0c) KCAP0 FTOPc
         fx_ok (UINVd a0 p fs0 data UX0) RZ GASAN BCAP CCAP) ->
    callee_contract ASEGS SWIN GASAN fx_ok RZ SHC KCAP0 AINVH AsDrvHooksA.AsFZ.ceN ->
    callee_contract ASEGS SWIN GASAN fx_ok RZ SHC KCAP0 AINVH AsDrvHooksA.AsFZ.ceE ->
    (forall L LF B C K M1 mdl, AINVH L LF B C K M1 mdl ->
       rdn ASEGS M1 (Z_to_bv 64 0x108268) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
       /\ rdn ASEGS M1 (Z_to_bv 64 0x108260) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff))
       /\ exists me : Z, rdn ASEGS M1 (Z_to_bv 64 0x108270) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 me))) ->
    (forall L LF B C K M1 mdl, AINVH L LF B C K M1 mdl ->
       rdn ASEGS M1 (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
       /\ exists cpm : byte, rdn ASEGS M1 (Z_to_bv 64 0x106ddc) 1 = Some [cpm] /\ u cpm <> 0) ->
    (forall L LF B C K M1 M' mdl, AINVH L LF B C K M1 mdl ->
       (forall a : word, M' a <> M1 a -> (in_lsb (u a) = true \/ in_mub (u a) = true) /\ M' a <> None) ->
       rdn ASEGS M' (Z_to_bv 64 DNA.DTOR_MU) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
       AINVH L LF B C K M' mdl) ->
    forall Ex fx0 R0 M1 model0,
      GPS.cs_ok ASEGS PERM_A_lit SPTOPc fs0 SHC (VSHf HIDc HIDFc) (AINV_f SWIN GASAN AINVH PERM_A_lit SPTOPc HIDc HIDFc M0c B0c C0c) KCAP0 FTOPc fx_ok
        (UINVd a0 p fs0 data UX0) Ex tX fx0 R0 M1 model0 ->
      RZ (cfgF ASEGS fx0 R0 (pc tX) M1 model0) (T a0 p fs0 data).

Lemma spec_usage1 : SPEC_T tMu1n (fun a0 _ fs0 _ => t_die (msg_usage a0) fs0). Proof. exact @usage1_spec. Qed.
Lemma spec_usage3 : SPEC_T tMu3n (fun a0 _ fs0 _ => t_die (msg_usage a0) fs0). Proof. exact @usage3_spec. Qed.
Lemma spec_usage1z : SPEC_T tMu1z (fun _ _ fs0 _ => t_die (msg_usage []) fs0). Proof. exact @usage1z_spec. Qed.
Lemma spec_usage3z : SPEC_T tMu3z (fun _ _ fs0 _ => t_die (msg_usage []) fs0). Proof. exact @usage3z_spec. Qed.
Lemma spec_absent : SPEC_T tMoa (fun _ p fs0 _ => t_die (msg_cannot_open p) fs0). Proof. exact @cantopen_absent_spec. Qed.
Lemma spec_empty : SPEC_T tMoz (fun _ _ fs0 _ => t_die (msg_cannot_open []) fs0). Proof. exact @cantopen_empty_spec. Qed.
Lemma spec_toolong : SPEC_T tMot (fun _ p fs0 _ => t_die (msg_cannot_open p) fs0). Proof. exact @cantopen_toolong_spec. Qed.

(* [comment removed for export] *)
#[local] Notation E'x mk bl := (AsDrvMainBridgeA.E' ph sp rdraw argv envp uid hw hs E mk bl).
Lemma run_class : forall (tX : acs) (T : list byte -> list byte -> Fs.Fs -> list byte -> TSet) (a0 p data : list byte) (mk : Z) (bl : nat -> list byte),
  SPEC_T tX T -> pc tX = P_MAIN ->
  (forall (bt : as_boot), bt_ia bt = asan_addrs ->
     forall (AINVc : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop) (UINV : env -> Prop),
       AINVc [] [] 0 0 0 M model -> UINV (E'x mk bl) ->
       @GPS.cs_ok ASEGS RCm stk_floor_default PERM_A_lit (u sp - 48) fs (@AzBridgeH.SHC_bt RCm bt) [] AINVc KCAP FMIN fx_ok UINV (E'x mk bl) tX fx R M model) ->
  U_drv a0 p fs data (E'x mk bl) ->
  RZ (cfgF ASEGS fx R (pc hs) M model) (T a0 p fs data).
Proof.
  intros tX T a0 p data mk bl HSPEC Hpc CSX HUd.
  destruct ainv_main as (hv & HBF & HBT & HDR). set (bt := asan_bt hv) in *.
  pose proof (EXT RCm hv HBF HBT) as XT.
  pose proof (AsAllocFFam.AsAinvPrist3.AAINV_QX_HS bt AsAllocFFam.AsAinvDrvHist3.drv_hist _ _ _ _ _ _ _ HDR) as HAA.     (* [comment removed for export] *)
  pose proof (AsDrvMainBridgeA.AsDrvBridgeArgv.sp_rng sp Hsp) as (S1 & S2 & S3).
  assert (HCE : @GlzConst.RunCeil.CEIL RCm <= u sp - 48) by (rewrite RCm_ceil; pose proof (page_floor_le (u sp - 8388608)); lia).
  assert (HM8 : (u sp - 48) mod 8 = 0) by (clear - S3; Z.div_mod_to_equations; lia).
  pose proof (@ainv_wrap RCm bt (AAINV_HS bt None) (u sp - 48) M model HAA HCE HM8) as HAI.
  pose proof (CSX bt eq_refl _ (UINVd a0 p fs data UX0) HAI (conj HUd I)) as HCX.
  rewrite pc_hs, <- Hpc.
  apply (HSPEC RCm stk_floor_default (@AzBridgeH.SHC_bt RCm bt) KCAP (@AzBridgeH.AINVH_bt RCm bt) PERM_A_lit (HPbt hv) SWIN_img_A (u sp - 48) [] [] M 0 0
           ltac:(lia) ltac:(lia) ltac:(unfold BCAP; lia) ltac:(unfold CCAP; lia) FMIN ltac:(cbn; lia) a0 p fs data
           (fun M0 => GCA hv XT (u sp - 48) fs a0 p data UX0 M0 UX0_agree) (proj1 (proj2 (proj2 (proj2 XT)))) (proj2 (proj2 (proj2 (proj2 XT))))
           (M2S_H_A hv) (DTOR_H_A hv) (DTOR_FRAME_A hv) (E'x mk bl) fx R M model HCX).
Qed.

(* [comment removed for export] *)
#[local] Notation a0 := (nth 0 argv []).
#[local] Notation p1 := (nth 1 argv []).
Definition blA (data : list byte) (n : nat) : list byte :=
  match n with 0%nat => [] | 1%nat => a0 | 2%nat => p1 | S (S (S j)) => APS.chunk j data end.

Lemma U_at : forall (data : list byte) (mk : Z), 0 <= mk < 2 ^ 64 ->
  (mk = DNA.CLS_ABSENT -> p1 <> [] -> Open.openat_plain_name p1 = true /\ fs_lookup fs p1 = None) ->
  (mk <= DNA.FCAP -> p1 <> [] /\ Open.openat_plain_name p1 = true /\ fs_lookup fs p1 = Some data /\ mk = APS.flen data) ->
  (mk = DNA.CLS_DIR -> path_is_dirref p1 = true) ->
  U_drv a0 p1 fs data (E'x mk (blA data)).
Proof.
  intros data mk Hmk HA HF HD.
  assert (Hk0 : (0 < length argv)%nat) by (destruct Hva as [[? ?] _]; lia).
  assert (H4 : u (ev (E'x mk (blA data)) 4%nat) = mk) by (change (ev (E'x mk (blA data)) 4%nat) with (Z_to_bv 64 mk); apply u64_lit; exact Hmk).
  unfold U_drv. rewrite H4.
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact (valid_argv_str_nz argv 0 Hva Hk0)|].
  split. { destruct (Nat.lt_ge_cases 1 (length argv)) as [H1|H1]; [exact (valid_argv_str_nz argv 1 Hva H1) | rewrite nth_overflow by lia; intros X; destruct X]. }
  split; [exact HA|]. split; [|exact HD].
  intros Hle. destruct (HF Hle) as (F1 & F2 & F3 & F4). split; [exact F1|]. split; [exact F2|]. split; [exact F3|].
  split; [unfold GPS.uE; cbn [edenot]; rewrite H4; exact F4|]. intros j _. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma HCTm : @BE.ceil_top RCm model. Proof. unfold BE.ceil_top. apply Z.le_refl. Qed.
Lemma HCSm : @GlzConst.RunCeil.CEIL RCm <= u sp - 8388608. Proof. rewrite RCm_ceil. apply page_floor_le. Qed.
Lemma HSFm : @GPS.SFLOOR RCm stk_floor_default <= u sp - 8388608. Proof. exact HCSm. Qed.

Definition MKU : Z := DNA.CLS_ABSENT + 5.   (* [comment removed for export] *)
Lemma U_none : forall data, U_drv a0 p1 fs data (E'x MKU (blA data)).
Proof.
  intros data. apply U_at; unfold MKU, DNA.CLS_ABSENT, DNA.CLS_DIR, DNA.FCAP; lia.
Qed.

Lemma spec_not2 : length argv <> 2%nat -> spec argv fs = t_die (msg_usage a0) fs.
Proof. intros H. destruct argv as [|a [|b [|c l]]]; try reflexivity. exfalso. apply H. reflexivity. Qed.

Theorem main_usage : length argv <> 2%nat -> RZ (cfgF ASEGS fx R (pc hs) M model) (spec argv fs).
Proof.
  intros Hn2. rewrite (spec_not2 Hn2).
  assert (Hk0 : (0 < length argv)%nat) by (destruct Hva as [[? ?] _]; lia).
  destruct (Nat.eq_dec (length argv) 1) as [H1|H1]; destruct (Nat.eq_dec (length a0) 0) as [HL|HL].
  - replace a0 with (@nil byte) by (symmetry; apply length_zero_iff_nil; exact HL).
    apply (run_class tMu1z (fun _ _ fs0 _ => t_die (msg_usage []) fs0) a0 p1 [] MKU (blA []) spec_usage1z eq_refl); [|exact (U_none [])].
    intros bt BT AINVc UINV HA HUx.
    exact (@cs_tMu1z RCm ph sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit hs Hhs E R M model HC MKU (blA []) bt BT HCTm HCSm stk_floor_default HSFm KCAP HKCAP
             AINVc HA UINV HUx fx Hfx eq_refl H1 ltac:(unfold L0v; lia)).
  - apply (run_class tMu1n (fun x _ fs0 _ => t_die (msg_usage x) fs0) a0 p1 [] MKU (blA []) spec_usage1 eq_refl); [|exact (U_none [])].
    intros bt BT AINVc UINV HA HUx.
    exact (@cs_tMu1n RCm ph sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit hs Hhs E R M model HC MKU (blA []) bt BT HCTm HCSm stk_floor_default HSFm KCAP HKCAP
             AINVc HA UINV HUx fx Hfx eq_refl H1 ltac:(unfold L0v; lia)).
  - replace a0 with (@nil byte) by (symmetry; apply length_zero_iff_nil; exact HL).
    apply (run_class tMu3z (fun _ _ fs0 _ => t_die (msg_usage []) fs0) a0 p1 [] MKU (blA []) spec_usage3z eq_refl); [|exact (U_none [])].
    intros bt BT AINVc UINV HA HUx.
    exact (@cs_tMu3z RCm ph sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit hs Hhs E R M model HC MKU (blA []) bt BT HCTm HCSm stk_floor_default HSFm KCAP HKCAP
             AINVc HA UINV HUx fx Hfx eq_refl ltac:(lia) ltac:(unfold L0v; lia)).
  - apply (run_class tMu3n (fun x _ fs0 _ => t_die (msg_usage x) fs0) a0 p1 [] MKU (blA []) spec_usage3 eq_refl); [|exact (U_none [])].
    intros bt BT AINVc UINV HA HUx.
    exact (@cs_tMu3n RCm ph sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit hs Hhs E R M model HC MKU (blA []) bt BT HCTm HCSm stk_floor_default HSFm KCAP HKCAP
             AINVc HA UINV HUx fx Hfx eq_refl ltac:(lia) ltac:(unfold L0v; lia)).
Qed.

(* [comment removed for export] *)
Lemma spec_2 : length argv = 2%nat ->
  spec argv fs =
    (if (4096 <=? length p1)%nat then t_die (msg_cannot_open p1) fs
     else if path_eqb p1 [] then t_die (msg_cannot_open p1) fs
     else if Open.path_is_dirref p1 then t_alt2 (t_die (msg_cannot_open p1) fs) (t_opened_dir p1 fs)
     else match fs_lookup fs p1 with
          | None => t_die (msg_cannot_open p1) fs
          | Some data => t_alt2 (t_die (msg_cannot_open p1) fs) (t_opened data fs)
          end).
Proof. intros H. destruct argv as [|a [|b [|c l]]]; try discriminate H. reflexivity. Qed.

Theorem main_toolong : length argv = 2%nat -> (4096 <= length p1)%nat -> RZ (cfgF ASEGS fx R (pc hs) M model) (t_die (msg_cannot_open p1) fs).
Proof.
  intros H2 HL.
  apply (run_class tMot (fun _ x fs0 _ => t_die (msg_cannot_open x) fs0) a0 p1 [] MKU (blA []) spec_toolong eq_refl); [|exact (U_none [])].
  intros bt BT AINVc UINV HA HUx.
  exact (@cs_tMot RCm ph sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit hs Hhs E R M model HC MKU (blA []) bt BT HCTm HCSm stk_floor_default HSFm KCAP HKCAP
           AINVc HA UINV HUx fx Hfx eq_refl eq_refl H2 ltac:(unfold L1v; lia)).
Qed.

Theorem main_empty : length argv = 2%nat -> p1 = [] -> RZ (cfgF ASEGS fx R (pc hs) M model) (t_die (msg_cannot_open p1) fs).
Proof.
  intros H2 HE.
  assert (HU : U_drv a0 p1 fs [] (E'x DNA.CLS_ABSENT (blA []))).
  { apply U_at; unfold DNA.CLS_ABSENT, DNA.CLS_DIR, DNA.FCAP; try lia.
    intros _ Hne. exfalso. exact (Hne HE). }
  replace (msg_cannot_open p1) with (msg_cannot_open []) by (rewrite HE; reflexivity).
  apply (run_class tMoz (fun _ _ fs0 _ => t_die (msg_cannot_open []) fs0) a0 p1 [] DNA.CLS_ABSENT (blA []) spec_empty eq_refl); [|exact HU].
  intros bt BT AINVc UINV HA HUx.
  exact (@cs_tMoz RCm ph sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit hs Hhs E R M model HC DNA.CLS_ABSENT (blA []) bt BT HCTm HCSm stk_floor_default HSFm KCAP HKCAP
           AINVc HA UINV HUx fx Hfx eq_refl eq_refl H2 ltac:(unfold L1v; rewrite HE; reflexivity) eq_refl).
Qed.

Theorem main_absent : length argv = 2%nat -> (length p1 < 4096)%nat -> p1 <> [] -> Open.path_is_dirref p1 = false -> fs_lookup fs p1 = None ->
  RZ (cfgF ASEGS fx R (pc hs) M model) (t_die (msg_cannot_open p1) fs).
Proof.
  intros H2 HL Hne HD Hfs.
  assert (Hplain : Open.openat_plain_name p1 = true).
  { apply (valid_argv_str_plain argv 0 Hva ltac:(lia)). unfold Open.path_is_dirref in HD. apply Bool.orb_false_iff in HD as [HD _]. exact HD. }
  assert (HU : U_drv a0 p1 fs [] (E'x DNA.CLS_ABSENT (blA []))).
  { apply U_at; unfold DNA.CLS_ABSENT, DNA.CLS_DIR, DNA.FCAP; try lia.
    intros _ _. split; [exact Hplain | exact Hfs]. }
  apply (run_class tMoa (fun _ x fs0 _ => t_die (msg_cannot_open x) fs0) a0 p1 [] DNA.CLS_ABSENT (blA []) spec_absent eq_refl); [|exact HU].
  intros bt BT AINVc UINV HA HUx.
  assert (HLn : (0 < length p1)%nat) by (destruct p1; [exfalso; apply Hne; reflexivity | cbn; lia]).
  exact (@cs_tMoa RCm ph sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit hs Hhs E R M model HC DNA.CLS_ABSENT (blA []) bt BT HCTm HCSm stk_floor_default HSFm KCAP HKCAP
           AINVc HA UINV HUx fx Hfx eq_refl eq_refl H2 ltac:(unfold L1v; lia) eq_refl).
Qed.

(* [comment removed for export] *)
Theorem main_dir : length argv = 2%nat -> (length p1 < 4096)%nat -> p1 <> [] -> Open.path_is_dirref p1 = true ->
  RZ (cfgF ASEGS fx R (pc hs) M model) (t_alt2 (t_die (msg_cannot_open p1) fs) (t_opened_dir p1 fs)).
Proof.
  intros H2 HL Hne HD.
  assert (HU : U_drv a0 p1 fs [] (E'x DNA.CLS_DIR (blA []))).
  { apply U_at; unfold DNA.CLS_ABSENT, DNA.CLS_DIR, DNA.FCAP; try lia. intros _. exact HD. }
  destruct ainv_main as (hv & HBF & HBT & HDR). set (bt := asan_bt hv) in *.
  pose proof (EXT RCm hv HBF HBT) as XT.
  pose proof (AsDrvMainBridgeA.AsDrvBridgeArgv.sp_rng sp Hsp) as (S1 & S2 & S3).
  assert (HCE : @GlzConst.RunCeil.CEIL RCm <= u sp - 48) by (rewrite RCm_ceil; pose proof (page_floor_le (u sp - 8388608)); lia).
  assert (HM8 : (u sp - 48) mod 8 = 0) by (clear - S3; Z.div_mod_to_equations; lia).
  pose proof (@ainv_wrap RCm bt (AsAllocFFam.AsAinvPrist3.AAINV_QX bt AsAllocFFam.AsAinvDrvHist3.drv_hist None) (u sp - 48) M model HDR HCE HM8) as HAI.     (* [comment removed for export] *)
  assert (HLn : (0 < length p1)%nat) by (destruct p1; [exfalso; apply Hne; reflexivity | cbn; lia]).
  pose proof (@cs_tMod RCm ph sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit hs Hhs E R M model HC DNA.CLS_DIR (blA []) bt eq_refl HCTm HCSm stk_floor_default HSFm KCAP HKCAP
                _ HAI (UINVd a0 p1 fs [] UX0) (conj HU I) fx Hfx eq_refl eq_refl H2 ltac:(unfold L1v; lia) eq_refl) as HCX.
  rewrite pc_hs. change P_MAIN with (pc tMod).
  exact (@dir_spec RCm stk_floor_default (Irun hv (u sp - 48)) a0 p1 fs [] (fhyps hv XT (u sp - 48) a0 p1 []) (E'x DNA.CLS_DIR (blA [])) fx R M model HCX).
Qed.

(* [comment removed for export] *)
Theorem main_file : forall data, length argv = 2%nat -> (length p1 < 4096)%nat -> p1 <> [] -> Open.path_is_dirref p1 = false -> fs_lookup fs p1 = Some data ->
  RZ (cfgF ASEGS fx R (pc hs) M model) (t_alt2 (t_die (msg_cannot_open p1) fs) (t_opened data fs)).
Proof.
  intros data H2 HL Hne HD Hfs.
  assert (Hplain : Open.openat_plain_name p1 = true).
  { apply (valid_argv_str_plain argv 0 Hva ltac:(lia)). unfold Open.path_is_dirref in HD. apply Bool.orb_false_iff in HD as [HD _]. exact HD. }
  assert (Hfl : 0 <= APS.flen data <= 2 ^ 26) by (unfold APS.flen; lia).
  assert (HU : U_drv a0 p1 fs data (E'x (APS.flen data) (blA data))).
  { apply U_at; unfold DNA.CLS_ABSENT, DNA.CLS_DIR, DNA.FCAP; try lia. intros _. split; [exact Hne|]. split; [exact Hplain|]. split; [exact Hfs | reflexivity]. }
  assert (HX : UXf data (E'x (APS.flen data) (blA data))).
  { unfold UXf. change (ev (E'x (APS.flen data) (blA data)) 4%nat) with (Z_to_bv 64 (APS.flen data)). apply u64_lit. lia. }
  destruct ainv_main as (hv & HBF & HBT & HDR). set (bt := asan_bt hv) in *.
  pose proof (EXT RCm hv HBF HBT) as XT.
  pose proof (AsDrvMainBridgeA.AsDrvBridgeArgv.sp_rng sp Hsp) as (S1 & S2 & S3).
  assert (HCE : @GlzConst.RunCeil.CEIL RCm <= u sp - 48) by (rewrite RCm_ceil; pose proof (page_floor_le (u sp - 8388608)); lia).
  assert (HM8 : (u sp - 48) mod 8 = 0) by (clear - S3; Z.div_mod_to_equations; lia).
  pose proof (@ainv_wrap RCm bt (AsAllocFFam.AsAinvPrist3.AAINV_QX bt AsAllocFFam.AsAinvDrvHist3.drv_hist None) (u sp - 48) M model HDR HCE HM8) as HAI.     (* [comment removed for export] *)
  assert (HLn : (0 < length p1)%nat) by (destruct p1; [exfalso; apply Hne; reflexivity | cbn; lia]).
  pose proof (@cs_tMf RCm ph sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit hs Hhs E R M model HC (APS.flen data) (blA data) bt eq_refl HCTm HCSm stk_floor_default HSFm KCAP HKCAP
                _ HAI (UINVd a0 p1 fs data (UXf data)) (conj HU HX) fx Hfx eq_refl eq_refl H2 ltac:(unfold L1v; lia) ltac:(unfold FLENHI; lia)) as HCX.
  rewrite pc_hs. change P_MAIN with (pc tMf).
  exact (@file_spec RCm stk_floor_default (Irun hv (u sp - 48)) a0 p1 fs data (fhyps hv XT (u sp - 48) a0 p1 data) (E'x (APS.flen data) (blA data)) fx R M model HCX).
Qed.

(* [comment removed for export] *)
Theorem main_sound_A : RZ (cfgF ASEGS fx R (pc hs) M model) (spec argv fs).
Proof.
  destruct (Nat.eq_dec (length argv) 2) as [H2|H2]; [|exact (main_usage H2)].
  rewrite (spec_2 H2).
  destruct (Nat.leb_spec 4096 (length p1)) as [HL|HL]; [exact (main_toolong H2 HL)|].
  destruct (path_eqb p1 []) eqn:HE; [apply path_eqb_eq in HE; exact (main_empty H2 HE)|].
  assert (Hne : p1 <> []) by (intros X; rewrite X, path_eqb_refl in HE; discriminate HE).
  destruct (Open.path_is_dirref p1) eqn:HD; [exact (main_dir H2 HL Hne HD)|].
  destruct (fs_lookup fs p1) as [data|] eqn:Hfs; [exact (main_file data H2 HL Hne HD Hfs) | exact (main_absent H2 HL Hne HD Hfs)].
Qed.
End MainA.
