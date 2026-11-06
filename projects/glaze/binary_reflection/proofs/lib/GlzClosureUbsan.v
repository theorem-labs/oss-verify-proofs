(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.EscU OSSVerify.Proofs.glaze.binary_reflection.lib.B2JU OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUcM1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module B2JUcM7.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.EscU.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JU.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUcM1.B2JUOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.

(* [comment removed for export] *)
Lemma b2ju_cert_MS_51 : B2JU.cert_stmt MS 51.
Proof. apply B2JUcM1.B2JUOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2ju_cert_MS_53 : B2JU.cert_stmt MS 53.
Proof. apply B2JUcM1.B2JUOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2ju_cert_MS_55 : B2JU.cert_stmt MS 55.
Proof. apply B2JUcM1.B2JUOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2ju_cert_MS_57 : B2JU.cert_stmt MS 57.
Proof. apply B2JUcM1.B2JUOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2ju_cert_MS_59 : B2JU.cert_stmt MS 59.
Proof. apply B2JUcM1.B2JUOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2ju_cert_MS_61 : B2JU.cert_stmt MS 61.
Proof. apply B2JUcM1.B2JUOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2ju_cert_MS_63 : B2JU.cert_stmt MS 63.
Proof. apply B2JUcM1.B2JUOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2ju_cert_MS_65 : B2JU.cert_stmt MS 65.
Proof. apply B2JUcM1.B2JUOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2ju_cert_MS_67 : B2JU.cert_stmt MS 67.
Proof. apply B2JUcM1.B2JUOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2ju_top_ML : B2JU.top_stmt ML.
Proof. apply B2JUcM1.B2JUOk.top_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2ju_top_MS : B2JU.top_stmt MS.
Proof. apply B2JUcM1.B2JUOk.top_okb_sound. vm_cast_no_check (eq_refl true). Qed.
End B2JUcM7.
Require Stdlib.micromega.Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module B2JUcerts.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.EscU.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JU.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUcM1.B2JUcM0 OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUcM1 OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUcM1.B2JUcM2 OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUcM1.B2JUcM3 OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUcM1.B2JUcM4 OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUcM1.B2JUcM5 B2JUcM7.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUcM1.B2JUcM0 OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUcM1 OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUcM1.B2JUcM5 OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUcM1.B2JUcM6 B2JUcM7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import B2JU.
Lemma CUTS_len : forall w, length (CUTS w) = 69%nat. Proof. destruct w; reflexivity. Qed.
Lemma certs_ML : forall i, cert_stmt ML i.
Proof.
  intro i. destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ exact b2ju_cert_ML_0 | exact b2ju_cert_ML_1 | exact b2ju_cert_ML_2 | exact b2ju_cert_ML_3 | exact b2ju_cert_ML_4 | exact b2ju_cert_ML_5 | exact b2ju_cert_ML_6 | exact b2ju_cert_ML_7 | exact b2ju_cert_ML_8 | exact b2ju_cert_ML_9 | exact b2ju_cert_ML_10 | exact b2ju_cert_ML_11 | exact b2ju_cert_ML_12 | exact b2ju_cert_ML_13 | exact b2ju_cert_ML_14 | exact b2ju_cert_ML_15 | exact b2ju_cert_ML_16 | exact b2ju_cert_ML_17 | exact b2ju_cert_ML_18 | exact b2ju_cert_ML_19 | exact b2ju_cert_ML_20 | exact b2ju_cert_ML_21 | exact b2ju_cert_ML_22 | exact b2ju_cert_ML_23 | exact b2ju_cert_ML_24 | exact b2ju_cert_ML_25 | exact b2ju_cert_ML_26 | exact b2ju_cert_ML_27 | exact b2ju_cert_ML_28 | exact b2ju_cert_ML_29 | exact b2ju_cert_ML_30 | exact b2ju_cert_ML_31 | exact b2ju_cert_ML_32 | exact b2ju_cert_ML_33 | exact b2ju_cert_ML_34 | exact b2ju_cert_ML_35 | exact b2ju_cert_ML_36 | exact b2ju_cert_ML_37 | exact b2ju_cert_ML_38 | exact b2ju_cert_ML_39 | exact b2ju_cert_ML_40 | exact b2ju_cert_ML_41 | exact b2ju_cert_ML_42 | exact b2ju_cert_ML_43 | exact b2ju_cert_ML_44 | exact b2ju_cert_ML_45 | exact b2ju_cert_ML_46 | exact b2ju_cert_ML_47 | exact b2ju_cert_ML_48 | exact b2ju_cert_ML_49 | exact b2ju_cert_ML_50 | exact b2ju_cert_ML_51 | exact b2ju_cert_ML_52 | exact b2ju_cert_ML_53 | exact b2ju_cert_ML_54 | exact b2ju_cert_ML_55 | exact b2ju_cert_ML_56 | exact b2ju_cert_ML_57 | exact b2ju_cert_ML_58 | exact b2ju_cert_ML_59 | exact b2ju_cert_ML_60 | exact b2ju_cert_ML_61 | exact b2ju_cert_ML_62 | exact b2ju_cert_ML_63 | exact b2ju_cert_ML_64 | exact b2ju_cert_ML_65 | exact b2ju_cert_ML_66 | exact b2ju_cert_ML_67 | exact b2ju_cert_ML_68 | ].
  unfold cert_stmt. rewrite (proj2 (nth_error_None (CUTS ML) _)); [exact I|]. rewrite CUTS_len. lia.
Qed.
Definition top_ML : top_stmt ML := b2ju_top_ML.
(* [comment removed for export] *)
Definition lidx (i : nat) : bool := (Nat.leb 8 i && Nat.even i)%bool.
Lemma certs_MSx : forall i, lidx i = false -> cert_stmt MS i.
Proof.
  intros i H. destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ exact b2ju_cert_MS_0 | exact b2ju_cert_MS_1 | exact b2ju_cert_MS_2 | exact b2ju_cert_MS_3 | exact b2ju_cert_MS_4 | exact b2ju_cert_MS_5 | exact b2ju_cert_MS_6 | exact b2ju_cert_MS_7 | discriminate H | exact b2ju_cert_MS_9 | discriminate H | exact b2ju_cert_MS_11 | discriminate H | exact b2ju_cert_MS_13 | discriminate H | exact b2ju_cert_MS_15 | discriminate H | exact b2ju_cert_MS_17 | discriminate H | exact b2ju_cert_MS_19 | discriminate H | exact b2ju_cert_MS_21 | discriminate H | exact b2ju_cert_MS_23 | discriminate H | exact b2ju_cert_MS_25 | discriminate H | exact b2ju_cert_MS_27 | discriminate H | exact b2ju_cert_MS_29 | discriminate H | exact b2ju_cert_MS_31 | discriminate H | exact b2ju_cert_MS_33 | discriminate H | exact b2ju_cert_MS_35 | discriminate H | exact b2ju_cert_MS_37 | discriminate H | exact b2ju_cert_MS_39 | discriminate H | exact b2ju_cert_MS_41 | discriminate H | exact b2ju_cert_MS_43 | discriminate H | exact b2ju_cert_MS_45 | discriminate H | exact b2ju_cert_MS_47 | discriminate H | exact b2ju_cert_MS_49 | discriminate H | exact b2ju_cert_MS_51 | discriminate H | exact b2ju_cert_MS_53 | discriminate H | exact b2ju_cert_MS_55 | discriminate H | exact b2ju_cert_MS_57 | discriminate H | exact b2ju_cert_MS_59 | discriminate H | exact b2ju_cert_MS_61 | discriminate H | exact b2ju_cert_MS_63 | discriminate H | exact b2ju_cert_MS_65 | discriminate H | exact b2ju_cert_MS_67 | discriminate H | ].
  unfold cert_stmt. rewrite (proj2 (nth_error_None (CUTS MS) _)); [exact I|]. rewrite CUTS_len. lia.
Qed.
Definition top_MS : top_stmt MS := b2ju_top_MS.

(* [comment removed for export] *)
Lemma weave_len : forall ms c, length (weave ms c) = (2 * length ms)%nat.
Proof. induction ms as [|e r IH]; intros c; cbn [weave length]; [reflexivity|]. rewrite IH. lia. Qed.
Lemma weave_nth_L : forall ms c0 j, (j < length ms)%nat -> nth_error (weave ms c0) (2 * j + 1) = Some (CL (c0 + j)).
Proof.
  induction ms as [|e r IH]; intros c0 j Hj; cbn [length] in Hj; [lia|].
  destruct j as [|j]; [cbn; rewrite Nat.add_0_r; reflexivity|].
  replace (2 * Datatypes.S j + 1)%nat with (Datatypes.S (Datatypes.S (2 * j + 1))) by lia. cbn [weave nth_error].
  rewrite (IH (Datatypes.S c0) j) by lia. f_equal. f_equal. lia.
Qed.
Lemma weave_nth_S : forall ms c0 j, nth_error (weave ms c0) (2 * j) = nth_error ms j.
Proof.
  induction ms as [|e r IH]; intros c0 j.
  - cbn [weave]. destruct j; reflexivity.
  - destruct j as [|j]; [reflexivity|].
    replace (2 * Datatypes.S j)%nat with (Datatypes.S (Datatypes.S (2 * j))) by lia. cbn [weave nth_error]. apply IH.
Qed.
Lemma TAGS_len : length TAGS_ML = 7%nat /\ length TAGS_MS = 7%nat. Proof. split; reflexivity. Qed.
Lemma MSE_len : length MSE_ML = NC /\ length MSE_MS = NC. Proof. split; reflexivity. Qed.
Lemma MSE_ML_dead : forallb (fun e => kdeadb (fst e)) MSE_ML = true. Proof. reflexivity. Qed.
Lemma cuts_LS : forall i, lidx i = true -> nth_error (CUTS MS) i = nth_error (CUTS ML) i.
Proof.
  intros i H. unfold lidx in H. apply andb_prop in H as [H1 H2]. apply Nat.leb_le in H1. apply Nat.even_spec in H2. destruct H2 as [q Hq].
  destruct TAGS_len as [TL TS]. destruct MSE_len as [ML0 MS0].
  cbn [CUTS]. unfold CUTSL_MS, CUTSL_ML. rewrite !nth_error_app2 by lia. rewrite TL, TS.
  replace (i - 7)%nat with (2 * (q - 4) + 1)%nat by lia.
  destruct (Nat.lt_ge_cases (q - 4) NC) as [Hlt|Hge].
  - rewrite !weave_nth_L by lia. reflexivity.
  - assert (E1 : nth_error (weave MSE_MS 0) (2 * (q - 4) + 1) = None) by (apply nth_error_None; rewrite weave_len; lia).
    assert (E2 : nth_error (weave MSE_ML 0) (2 * (q - 4) + 1) = None) by (apply nth_error_None; rewrite weave_len; lia).
    rewrite E1, E2. reflexivity.
Qed.
Lemma cuts_L_dead : forall j c, (8 <= j)%nat -> lidx j = false -> nth_error (CUTS ML) j = Some c -> kdead (fst c).
Proof.
  intros j c H8 Hl Hn. unfold lidx in Hl. apply Nat.leb_le in H8. rewrite H8 in Hl. cbn [andb] in Hl.
  (* [comment removed for export] *)
  assert (Ho : Nat.odd j = true) by (unfold Nat.odd; rewrite Hl; reflexivity).
  apply Nat.odd_spec in Ho. destruct Ho as [q Hq].
  destruct TAGS_len as [TL _]. cbn [CUTS] in Hn. unfold CUTSL_ML in Hn. rewrite nth_error_app2 in Hn by lia. rewrite TL in Hn.
  replace (j - 7)%nat with (2 * (q - 3))%nat in Hn by lia. rewrite weave_nth_S in Hn.
  apply kdeadb_sound. pose proof MSE_ML_dead as D. rewrite forallb_forall in D.
  apply (D c). eapply nth_error_In. exact Hn.
Qed.
Lemma touts_ML : ce_touts (ce ML) = [tout ML; tout ML]. Proof. reflexivity. Qed.
Lemma touts_MS : ce_touts (ce MS) = [tout MS; tout ML]. Proof. reflexivity. Qed.
Lemma hs_LS : forall i, lidx i = true -> hs_sub (HScut (ce ML) (CUTS ML) (Datatypes.S i)) (HScut (ce MS) (CUTS MS) (Datatypes.S i)).
Proof.
  intros i Hi h ch Hh. unfold HScut, B2JCutShare.GlzCallCert.NT in Hh |- *. rewrite touts_ML in Hh. rewrite touts_MS.
  change (length [tout ML; tout ML]) with 2%nat in Hh. change (length [tout MS; tout ML]) with 2%nat.
  destruct (Nat.ltb h 2) eqn:Hlt.
  - left. exists 1%nat. cbn [Nat.ltb Nat.leb nth_error]. apply Nat.ltb_lt in Hlt.
    destruct h as [|[|h]]; [| |lia]; cbn [nth_error] in Hh; injection Hh as <-; reflexivity.
  - destruct (Nat.leb (Datatypes.S i) (h - 2)) eqn:Hle; [|discriminate Hh]. apply Nat.leb_le in Hle.
    assert (H8 : (8 <= i)%nat) by (unfold lidx in Hi; apply andb_prop in Hi as [X _]; apply Nat.leb_le in X; exact X).
    destruct (lidx (h - 2)) eqn:Hl.
    + left. exists h. rewrite Hlt. replace (Nat.leb (Datatypes.S i) (h - 2)) with true by (symmetry; apply Nat.leb_le; lia).
      rewrite (cuts_LS (h - 2) Hl). exact Hh.
    + right. destruct (nth_error (CUTS ML) (h - 2)) as [c|] eqn:Hn; [|discriminate Hh]. injection Hh as <-.
      apply (cuts_L_dead (h - 2) c); [lia | exact Hl | exact Hn].
Qed.
End B2JUcerts.
Require LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module B2JUC.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallRec.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.EscU.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JU B2JUcerts OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS. Import B2JU.
Open Scope Z_scope.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_mono : forall L B C B' C' M mdl, AINVH L B C M mdl -> B <= B' -> C <= C' -> AINVH L B' C' M mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
(* [comment removed for export] *)
Hypothesis CT0_sound : forall id c, CT0 id = Some c -> callee_contract USEGS [] GUBSAN fx_ok RZ AINVH c.
Hypothesis CT2_sound : forall id c, CT2 id = Some c -> callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (c2_merged c).
(* [comment removed for export] *)
Let CERTS_L : forall i, cert_stmt ML i := certs_ML.
Let TOP_L : top_stmt ML := top_ML.
Let CERTS_S : forall i, lidx i = false -> cert_stmt MS i := certs_MSx.   (* [comment removed for export] *)
Let TOP_S : top_stmt MS := top_MS.

Lemma idepth_lt : (14 < NXF)%nat. Proof. cbv. lia. Qed.

Lemma cuts_ok_of : forall w, (forall i, cert_stmt w i) ->
  forall i T k, nth_error (CUTS w) i = Some (T, k) -> exists sh,
    gplan_ok k = true /\ holes_only sh = true /\
    check USEGS IT AUBSAN (ce_nxf (ce w)) LIMIT (XN w) B2JCutShare.GlzCallCert.XE0 (XB w) B2JCutShare.GlzCallCert.XC0 (HScut (ce w) (CUTS w) (Datatypes.S i)) 0%nat BFUEL FUEL None T k = COk sh.
Proof.
  intros w H i T k Hn. pose proof (H i) as X. unfold cert_stmt in X. rewrite Hn in X. exact X.
Qed.

(* [comment removed for export] *)
Theorem b2jvU_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (ce ML).
Proof.
  destruct TOP_L as (s & Hgp & Hho & CERT).
  refine (contract_of_cert_rec_cut_all USEGS IT AUBSAN ubsan_in_hull ubsan_hull_ok IT_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH
            AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (ce ML) 14 idepth_lt (RUN_sound_fx USEGS) LIMIT 0%nat BFUEL FUEL (XN ML) _ (top ML) s Hgp Hho (XB ML) _ (CUTS ML) _ CERT).
  - intros n PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV Hn HB0 HC0 HBc HCc HUa HUm CC. unfold XN.
    apply (XNr_sound USEGS IT AUBSAN ubsan_in_hull ubsan_hull_ok IT_ok [] GUBSAN fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
             ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out NXF BCAP CCAP PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa
             213%nat 14%nat ceL1 CT0 CT0_sound n).
    + (apply GC_all; first [assumption | exact IT_ok]).
    + exact CC.
    + exact HUm.
  - intros n PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV Hn HB0 HC0 HBc HCc HUa HUm CC. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
             ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2 CT2_sound).
    (apply OBL2_all; assumption).
  - exact (cuts_ok_of ML CERTS_L).
Qed.

(* [comment removed for export] *)
Lemma CTs_sound : forall id c, CTs id = Some c -> callee_contract USEGS [] GUBSAN fx_ok RZ AINVH c.
Proof.
  intros id c H. unfold CTs in H. destruct (Nat.eqb id 213).
  - injection H as <-. exact b2jvU_callee_L1.
  - exact (CT0_sound _ _ H).
Qed.
Theorem b2jvU_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (ce MS).
Proof.
  destruct TOP_S as (s & Hgp & Hho & CERT).
  (* [comment removed for export] *)
  refine (contract_of_cert_rec_cut_allX USEGS IT AUBSAN ubsan_in_hull ubsan_hull_ok IT_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH
            AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (ce MS) 14 idepth_lt (RUN_sound_fx USEGS) LIMIT 0%nat BFUEL FUEL (XN MS) _ (top MS) s Hgp Hho (XB MS) _ (XN ML) _ (XB ML) _ (CUTS MS) _ CERT).
  - intros n PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV Hn HB0 HC0 HBc HCc HUa HUm CC. unfold XN.
    apply (XNc_sound USEGS IT AUBSAN ubsan_in_hull ubsan_hull_ok IT_ok NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
             ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CTs CTs_sound).
    (apply GC_all; first [assumption | exact IT_ok]).
  - intros n PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV Hn HB0 HC0 HBc HCc HUa HUm CC. unfold XB.
    apply (XBr_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
             ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out NXF BCAP CCAP PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa
             14%nat 210%nat (ce2 MS) CT2 CT2_sound n).
    + (apply OBL2_all; assumption).
    + exact CC.
    + exact HUm.
  - intros n PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV Hn HB0 HC0 HBc HCc HUa HUm CC. unfold XN.
    apply (XNr_sound USEGS IT AUBSAN ubsan_in_hull ubsan_hull_ok IT_ok [] GUBSAN fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
             ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out NXF BCAP CCAP PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa
             213%nat 14%nat ceL1 CT0 CT0_sound (2 ^ 64)).
    + (apply GC_all; first [assumption | exact IT_ok]).
    + exact (contract_upto_of_full USEGS [] GUBSAN fx_ok RZ AINVH 14 (2 ^ 64) ceL1 b2jvU_callee_L1).
    + intros E _. unfold DMEAS. pose proof (u64_range (ev E 14)). lia.
  - intros n PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV Hn HB0 HC0 HBc HCc HUa HUm CC. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
             ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2 CT2_sound).
    (apply OBL2_all; assumption).
  - intros i T k Hn. destruct (lidx i) eqn:Hl.
    + pose proof (CERTS_L i) as X. unfold cert_stmt in X. rewrite <- (cuts_LS i Hl), Hn in X.
      destruct X as (sh & H1 & H2 & H3). exists sh. split; [exact H1|]. split; [exact H2|].
      right. exists (HScut (ce ML) (CUTS ML) (Datatypes.S i)). split; [exact (hs_LS i Hl) | exact H3].
    + pose proof (CERTS_S i Hl) as X. unfold cert_stmt in X. rewrite Hn in X.
      destruct X as (sh & H1 & H2 & H3). exists sh. split; [exact H1|]. split; [exact H2|]. left. exact H3.
Qed.
End Contract.
End B2JUC.
Module EscUC.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.EscU OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.

(* [comment removed for export] *)
Lemma esc_callee_cut : forall (c : gcallee) (p : AP.plan) sh,
  ce_nxf c = NXF -> ce_bcap c = BCAP -> ce_ccap c = CCAP -> gplan_ok p = true -> holes_only sh = true ->
  (forall i T k, nth_error CUTS_E i = Some (T, k) -> exists sh, gplan_ok k = true /\ holes_only sh = true /\
     (check USEGS IT AUBSAN (ce_nxf c) LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c CUTS_E (Datatypes.S i)) 0%nat BFUEL FUEL None T k = COk sh \/
      exists HS', hs_sub HS' (HScut c CUTS_E (Datatypes.S i)) /\
        check USEGS IT AUBSAN (ce_nxf c) LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 HS' 0%nat BFUEL FUEL None T k = COk sh)) ->
  check USEGS IT AUBSAN (ce_nxf c) LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c CUTS_E 0) 0%nat BFUEL FUEL None (ce_tin c) p = COk sh ->
  callee_contract USEGS [] GUBSAN fx_ok RZ AINVH c.
Proof.
  intros c p sh HN HB HC HG HSH HCUTS CERT. unfold callee_contract.
  rewrite HN in HCUTS, CERT.
  refine (contract_of_cert_when_cutX USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            c IT IT_ok LIMIT 0%nat BFUEL FUEL XN QTRUE _ _ XB _ XN _ XB _ CUTS_E _ p sh HG HSH _).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa HUQ. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc. unfold XN.
    apply (XNc_sound USEGS IT AUBSAN ubsan_in_hull ubsan_hull_ok IT_ok NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact IT_ok]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa HUQ. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2).
    + intros id c2' H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa HUQ. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc. unfold XN.
    apply (XNc_sound USEGS IT AUBSAN ubsan_in_hull ubsan_hull_ok IT_ok NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact IT_ok]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa HUQ. rewrite HN in *. rewrite HB in HBc. rewrite HC in HCc. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2).
    + intros id c2' H. discriminate H.
    + (apply OBL2_all; assumption).
  - rewrite HN. exact HCUTS.
  - rewrite HN. exact CERT.
Qed.
Lemma esc_hs_L : hs_sub (HScut ceL1 CUTS_E 1) (HScut (ce MS) CUTS_E 1).
Proof.
  intros h ch Hh. left. exists 1%nat. unfold HScut, NT in Hh |- *.
  change (ce_touts ceL1) with [tout ML; tout ML] in Hh. change (ce_touts (ce MS)) with [tout MS; tout ML].
  change (length [tout ML; tout ML]) with 2%nat in Hh. change (length [tout MS; tout ML]) with 2%nat.
  cbn [Nat.ltb Nat.leb nth_error].
  destruct h as [|[|h]]; cbn [Nat.ltb Nat.leb nth_error] in Hh; [exact Hh | exact Hh |].
  destruct h as [|h]; cbn [Nat.sub Nat.leb] in Hh; [discriminate Hh|].
  unfold CUTS_E in Hh. cbn [nth_error] in Hh. destruct h; discriminate Hh.
Qed.
Theorem esc_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH ceL1.
Proof.
  refine (esc_callee_cut ceL1 (planX ML) (SHole 2) eq_refl eq_refl eq_refl (esc_gplanX ML) eq_refl _ esc_cert_L1).
  intros i T k Hn. destruct i as [|i]; [|destruct i; discriminate Hn].
  injection Hn as <- <-. exists (SHole 0). split; [exact esc_gplanC|]. split; [reflexivity|]. left. exact esc_cut_L.
Qed.

Theorem esc_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (ce MS).
Proof.
  refine (esc_callee_cut (ce MS) (planX MS) (SHole 0) eq_refl eq_refl eq_refl (esc_gplanX MS) eq_refl _ esc_cert_S).
  intros i T k Hn. destruct i as [|i]; [|destruct i; discriminate Hn].
  injection Hn as <- <-. exists (SHole 0). split; [exact esc_gplanC|]. split; [reflexivity|].
  right. exists (HScut ceL1 CUTS_E 1). split; [exact esc_hs_L | exact esc_cut_L].
Qed.

End Contract.
End EscUC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.GuI32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GuI32C.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuI32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_mono : forall L B C B' C' M mdl, AINVH L B C M mdl -> B <= B' -> C <= C' -> AINVH L B' C' M mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + 0 <= GBUDGET -> C0 + 0 <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN 0 0.

(* [comment removed for export] *)
Lemma callee_m : forall m p, gplan_ok p = true -> check USEGS IT AUBSAN NXF LIMIT (XN IT NXF) XE0 XB0 XC0 (HSce (cem m)) 0%nat BFUEL FUEL None (ce_tin (cem m)) p = COk (SHole 0) ->
  callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (cem m).
Proof.
  intros m p HG CERT.
  refine (contract_of_cert USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (cem m) IT IT_ok LIMIT 0%nat BFUEL FUEL (XN IT NXF) _ p _ HG hshape CERT).
  intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa.
  apply (XN_sound IT IT_ok NXF RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa).
  (apply GC_all; first [assumption | exact IT_ok]).
Qed.
Theorem to_chars40kb_i32_callee : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH ce.
Proof. exact (callee_m ML plan_i32 gplan cert). Qed.
Theorem to_chars40kb_i32_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH ceS.
Proof. exact (callee_m MS plan_i32S gplanS certS). Qed.
End Contract.
End GuI32C.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GuAA OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GuAAi32.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuI32 GuI32C OSSVerify.Proofs.glaze.binary_reflection.lib.GuAA OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuAAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuAAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := B2JUT.GuAAT.cfg_i32.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 132 then Some GuI32.ce else if Nat.eqb id 142 then Some GuI32.ceS else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF GUBSAN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan :=
  PRun [] (PBump BMP (match m with ML => PExt 132 [VAL; A1; S1; D1; IXv] k | MS => PExt 142 [VAL; ELit 0; EVar 130; ELit 0; IXv] k end)).

#[local] Notation CHK m := (check USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuAA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuAA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GuAA.ce cfg MS) 0 (GuAA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GuAA.ceL1 cfg) 0 (GuAA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GuAA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuAA.ceL1 cfg) (GuAA.IT cfg) (GuAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuAA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuAA.IT_ok cfg) GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 132). { injection H as <-. apply (GuI32C.to_chars40kb_i32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]). }
      destruct (Nat.eqb id 142); [|discriminate H]. injection H as <-.
      apply (GuI32C.to_chars40kb_i32_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuAA.ce cfg MS) (GuAA.IT cfg) (GuAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuAA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuAA.IT_ok cfg) GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 132). { injection H as <-. apply (GuI32C.to_chars40kb_i32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]). }
      destruct (Nat.eqb id 142); [|discriminate H]. injection H as <-.
      apply (GuI32C.to_chars40kb_i32_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuAA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuAA.IT_ok cfg) GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 132). { injection H as <-. apply (GuI32C.to_chars40kb_i32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]). }
      destruct (Nat.eqb id 142); [|discriminate H]. injection H as <-.
      apply (GuI32C.to_chars40kb_i32_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GuAA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_aligned_array_i32_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_aligned_array_i32_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GuAAi32.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GuI64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GuI64C.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuI64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_mono : forall L B C B' C' M mdl, AINVH L B C M mdl -> B <= B' -> C <= C' -> AINVH L B' C' M mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + 0 <= GBUDGET -> C0 + 0 <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN 0 0.

Theorem to_chars40kb_i64_callee : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH ce.
Proof.
  refine (contract_of_cert USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            ce IT IT_ok LIMIT 0%nat BFUEL FUEL (XN IT NXF) _ plan_i64 _ gplan hshape cert).
  intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa.
  apply (XN_sound IT IT_ok NXF RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa).
  (apply GC_all; first [assumption | exact IT_ok]).
Qed.
End Contract.
End GuI64C.
Module GuAAi64.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuI64 GuI64C OSSVerify.Proofs.glaze.binary_reflection.lib.GuAA OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuAAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuAAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := B2JUT.GuAAT.cfg_i64.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 134 then Some GuI64.ce else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF GUBSAN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan := PRun [] (PBump BMP (PExt 134 [VAL; A1; S1; D1; IXv] k)).

#[local] Notation CHK m := (check USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuAA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuAA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GuAA.ce cfg MS) 0 (GuAA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GuAA.ceL1 cfg) 0 (GuAA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GuAA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuAA.ceL1 cfg) (GuAA.IT cfg) (GuAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuAA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuAA.IT_ok cfg) GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 134); [|discriminate H]. injection H as <-.
      apply (GuI64C.to_chars40kb_i64_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuAA.ce cfg MS) (GuAA.IT cfg) (GuAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuAA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuAA.IT_ok cfg) GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 134); [|discriminate H]. injection H as <-.
      apply (GuI64C.to_chars40kb_i64_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuAA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuAA.IT_ok cfg) GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 134); [|discriminate H]. injection H as <-.
      apply (GuI64C.to_chars40kb_i64_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GuAA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_aligned_array_i64_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_aligned_array_i64_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GuAAi64.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GuU32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GuU32C.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuU32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_mono : forall L B C B' C' M mdl, AINVH L B C M mdl -> B <= B' -> C <= C' -> AINVH L B' C' M mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + 0 <= GBUDGET -> C0 + 0 <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN 0 0.

Lemma callee_m : forall m, check USEGS IT AUBSAN NXF LIMIT (XN IT NXF) XE0 XB0 XC0 (HSce (cem m)) 0%nat BFUEL FUEL None (ce_tin (cem m)) plan_u32 = COk (SHole 0) ->
  callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (cem m).
Proof.
  intros m CERT.
  refine (contract_of_cert USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (cem m) IT IT_ok LIMIT 0%nat BFUEL FUEL (XN IT NXF) _ plan_u32 _ gplan hshape CERT).
  intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa.
  apply (XN_sound IT IT_ok NXF RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa).
  (apply GC_all; first [assumption | exact IT_ok]).
Qed.
Theorem to_chars40kb_u32_callee : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH ce.
Proof. exact (callee_m ML cert). Qed.
Theorem to_chars40kb_u32_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH ceS.
Proof. exact (callee_m MS certS). Qed.
End Contract.
End GuU32C.
Module GuAAu32.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuU32 GuU32C OSSVerify.Proofs.glaze.binary_reflection.lib.GuAA OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuAAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuAAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := B2JUT.GuAAT.cfg_u32.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 133 then Some GuU32.ce else if Nat.eqb id 143 then Some GuU32.ceS else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF GUBSAN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan :=
  PRun [] (PBump BMP (match m with ML => PExt 133 [VAL; A1; S1; D1; IXv] k | MS => PExt 143 [VAL; ELit 0; EVar 130; ELit 0; IXv] k end)).

#[local] Notation CHK m := (check USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuAA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuAA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GuAA.ce cfg MS) 0 (GuAA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GuAA.ceL1 cfg) 0 (GuAA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GuAA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuAA.ceL1 cfg) (GuAA.IT cfg) (GuAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuAA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuAA.IT_ok cfg) GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 133). { injection H as <-. apply (GuU32C.to_chars40kb_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]). }
      destruct (Nat.eqb id 143); [|discriminate H]. injection H as <-.
      apply (GuU32C.to_chars40kb_u32_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuAA.ce cfg MS) (GuAA.IT cfg) (GuAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuAA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuAA.IT_ok cfg) GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 133). { injection H as <-. apply (GuU32C.to_chars40kb_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]). }
      destruct (Nat.eqb id 143); [|discriminate H]. injection H as <-.
      apply (GuU32C.to_chars40kb_u32_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuAA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuAA.IT_ok cfg) GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 133). { injection H as <-. apply (GuU32C.to_chars40kb_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]). }
      destruct (Nat.eqb id 143); [|discriminate H]. injection H as <-.
      apply (GuU32C.to_chars40kb_u32_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GuAA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_aligned_array_u32_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_aligned_array_u32_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GuAAu32.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GuU64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GuU64C.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuU64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_mono : forall L B C B' C' M mdl, AINVH L B C M mdl -> B <= B' -> C <= C' -> AINVH L B' C' M mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + 0 <= GBUDGET -> C0 + 0 <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN 0 0.

Theorem to_chars40kb_u64_callee : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH ce.
Proof.
  refine (contract_of_cert USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            ce IT IT_ok LIMIT 0%nat BFUEL FUEL (XN IT NXF) _ plan_u64 _ gplan hshape cert).
  intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa.
  apply (XN_sound IT IT_ok NXF RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa).
  (apply GC_all; first [assumption | exact IT_ok]).
Qed.
End Contract.
End GuU64C.
Module GuAAu64.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuU64 GuU64C OSSVerify.Proofs.glaze.binary_reflection.lib.GuAA OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuAAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuAAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := B2JUT.GuAAT.cfg_u64.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 135 then Some GuU64.ce else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF GUBSAN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan := PRun [] (PBump BMP (PExt 135 [VAL; A1; S1; D1; IXv] k)).

#[local] Notation CHK m := (check USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuAA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuAA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check USEGS (GuAA.IT cfg) AUBSAN GuAA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GuAA.ce cfg MS) 0 (GuAA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GuAA.ceL1 cfg) 0 (GuAA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GuAA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuAA.ceL1 cfg) (GuAA.IT cfg) (GuAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuAA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuAA.IT_ok cfg) GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 135); [|discriminate H]. injection H as <-.
      apply (GuU64C.to_chars40kb_u64_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuAA.ce cfg MS) (GuAA.IT cfg) (GuAA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuAA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuAA.IT_ok cfg) GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 135); [|discriminate H]. injection H as <-.
      apply (GuU64C.to_chars40kb_u64_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuAA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuAA.IT_ok cfg) GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 135); [|discriminate H]. injection H as <-.
      apply (GuU64C.to_chars40kb_u64_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuAA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuAA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GuAA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_aligned_array_u64_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_aligned_array_u64_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuAA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GuAAu64.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GuB2JT.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzDev OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Module B2JnUT.
Definition ENTRY : Z := 0x2f2f0.
Definition RETPC : Z := 0x2f4d8.
Definition HEAD : Z := 0x2f370.      (* [comment removed for export] *)
Definition JOINS : Z := 0x2f3bc.     (* [comment removed for export] *)
Definition CALLV : Z := 0x322ac.     (* [comment removed for export] *)
Definition IT : itab := mk_itab_ranges USEGS [(ENTRY, 123%nat)].   (* [comment removed for export] *)
Lemma IT_ok : itab_sound USEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition INSZ : Z := EscU.INSZ.            (* [comment removed for export] *)
Definition BIG : Z := EscU.BIG.              (* [comment removed for export] *)
Definition AHI : Z := EscU.AHI.
Definition CAPK : Z := EscU.CAPK.
Definition IXMAX : Z := 32 * INSZ.          (* [comment removed for export] *)
Definition CAPMAX : Z := 8 * INSZ.          (* [comment removed for export] *)
Definition CAPHI : Z := 4 * IXMAX + 8 * EscU.INSZ + EscU.CAPK + 256 * CAPMAX.
Definition FR : Z := 160.
Definition XDB : Z := 57536.                (* [comment removed for export] *)
Definition FRX : Z := FR + XDB.             (* [comment removed for export] *)

(* [comment removed for export] *)
Definition TP : expr := ELit (g_tp GUBSAN).
Definition DUM : expr := ELit 0.
Definition regs0 : list expr := sr_upd (ELit 0 :: map EVar (seq 0 31)) 4 TP.
Definition e_sp : expr := EVar 1.
Definition R : expr := EVar 9.        (* [comment removed for export] *)
Definition BV : expr := EVar 10.      (* [comment removed for export] *)
Definition OBJ : expr := EVar 11.     (* [comment removed for export] *)
Definition BSZ : expr := EVar 31.     (* [comment removed for export] *)
Definition INLO : expr := EVar 32.    (* [comment removed for export] *)
Definition NXF : nat := 33.
Definition G : expr := eaddz e_sp (- FR).           (* [comment removed for export] *)
Definition EEND : expr := eadd BSZ INLO.

(* [comment removed for export] *)
Definition img_apart (x : expr) (k : Z) (n : expr) : kentry := KDisj (SA x k) n (SA (ELit 0) 0x10000) (ELit 0x9c000).
Definition kn_fixed : list kentry :=
  [ KRange R CEIL HI47; KWr (SA R 0) (ELit 32); KRange (esub R e_sp) 0 (2 ^ 40);
    KRange BV CEIL HI47; KWord (SA BV 0) 8 INLO; KWord (SA BV 8) 8 EEND; KRange (esub BV e_sp) 0 (2 ^ 40); KWr (SA BV 0) (ELit 16);   (* [comment removed for export] *)
    KRange OBJ CEIL (HI47 - 24); (* [comment removed for export] *) KWr (SA OBJ 0) (ELit 24); KUnk (SA OBJ 0) (ELit 24); KRange (esub OBJ e_sp) 0 (2 ^ 40);
    KAlign OBJ 8;   (* [comment removed for export] *)
    KRange INLO PTRLO PTRHI; KRange BSZ 1 INSZ; KRange EEND (PTRLO + 1) PTRHI; KUnk (SA INLO 0) BSZ;
    KDisj (SA R 0) (ELit 32) (SA OBJ 0) (ELit 24); KDisj (SA R 0) (ELit 32) (SA BV 0) (ELit 16);
    KDisj (SA OBJ 0) (ELit 24) (SA BV 0) (ELit 16);
    KDisj (SA INLO 0) BSZ (SA R 0) (ELit 32); KDisj (SA INLO 0) BSZ (SA OBJ 0) (ELit 24); KDisj (SA INLO 0) BSZ (SA BV 0) (ELit 16);
    KAlign e_sp 16; KRange e_sp (CEIL + FRX) HI47; KWr (SA e_sp (- FRX)) (ELit FRX);
    KDisj (SA e_sp (- FRX)) (ELit FRX) (SA R 0) (ELit 32); KDisj (SA e_sp (- FRX)) (ELit FRX) (SA OBJ 0) (ELit 24);
    KDisj (SA e_sp (- FRX)) (ELit FRX) (SA BV 0) (ELit 16); KDisj (SA INLO 0) BSZ (SA e_sp (- FRX)) (ELit (FRX + WSTK)); img_apart INLO 0 BSZ;   (* [comment removed for export] *)
    KImg 0x10000 0x75000 ].

(* [comment removed for export] *)
Definition strS (s : expr) : list kentry := [ KWord (SA OBJ 0) 1 (escale 2 s); KRange s 0 22 ].
Definition capE0 (ix ito a : expr) : kentry :=
  KRange (esub (eaddz (eadd (escale 4 ix) (escale 8 ito)) CAPK) (escale 8 a)) 0 CAPHI.
(* [comment removed for export] *)
Definition placement (d a : expr) : list kentry :=
  [ KRange d PTRLO (PTRHI - 24); KRange (eadd d (escale 8 a)) (PTRLO + 24) PTRHI;
    KDisj (SA d 0) (escale 8 a) (SA e_sp (- FRX)) (ELit (FRX + WSTK)) ].
Definition strLc (ix ito d s a : expr) : list kentry :=
  [ KWord (SA OBJ 0) 8 (eaddz (escale 8 a) 1); KWord (SA OBJ 8) 8 s; KWord (SA OBJ 16) 8 d;
    KRange a 3 AHI; capE0 ix ito a;
    KRange s 0 (8 * AHI); KRange (esub (escale 8 a) s) 1 (8 * AHI);
    KRange d PTRLO (HI47 - 24); KRange (eadd d (escale 8 a)) (PTRLO + 24) HI47; KAlign d 16;
    KWr (SA d 0) (escale 8 a); KUnk (SA d 0) (escale 8 a);
    KDisj (SA d 0) (escale 8 a) (SA OBJ 0) (ELit 24); KDisj (SA d 0) (escale 8 a) (SA INLO 0) BSZ;
    KDisj (SA d 0) (escale 8 a) (SA R 0) (ELit 32); KDisj (SA d 0) (escale 8 a) (SA BV 0) (ELit 16); img_apart d 0 (escale 8 a) ].
Definition strL (ix ito d s a : expr) : list kentry := placement d a ++ strLc ix ito d s a.
Definition str (m : smode) (ix ito : expr) (v : nat) : list kentry :=
  match m with MS => strS (EVar v) | ML => strL ix ito (EVar v) (EVar (1 + v)) (EVar (2 + v)) end.

Definition vis (m : smode) (v : nat) : list (expr * expr) :=
  match m with MS => [] | ML => [(EVar v, escale 8 (EVar (2 + v)))] end.

Definition WS : list (expr * expr) := [(R, ELit 32); (OBJ, ELit 24); (INLO, BSZ)].
Definition mkcs (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vs : list (expr * expr)) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FRX 0 vs WS 0 e_sp FdStd false.   (* [comment removed for export] *)
Definition kn_in : list kentry := [ KWord (SA OBJ 0) 8 (ELit 0) ] ++ kn_fixed.   (* [comment removed for export] *)
Definition tin : acs := mkcs ENTRY regs0 kn_in NXF [].

(* [comment removed for export] *)
Definition XSTR : nat := 33. Definition XLO : nat := 36.
Definition clobbered : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Fixpoint sr_havoc (sr : list expr) (ixs : list nat) (v : nat) : list expr :=
  match ixs with [] => sr | i :: t => sr_havoc (sr_upd sr i (EVar v)) t (S v) end.
Definition regs_out : list expr := sr_havoc regs0 clobbered XLO.
(* [comment removed for export] *)
Definition strLx (d s a : expr) : list kentry :=     (* [comment removed for export] *)
  [ KWord (SA OBJ 0) 8 (eaddz (escale 8 a) 1); KWord (SA OBJ 16) 8 d; KRange a 3 AHI;
    KRange d PTRLO (HI47 - 24); KRange (eadd d (escale 8 a)) (PTRLO + 24) HI47; KAlign d 16;
    KWr (SA d 0) (escale 8 a); KUnk (SA d 0) (escale 8 a);
    KDisj (SA d 0) (escale 8 a) (SA OBJ 0) (ELit 24); KDisj (SA d 0) (escale 8 a) (SA INLO 0) BSZ;
    KDisj (SA d 0) (escale 8 a) (SA R 0) (ELit 32); KDisj (SA d 0) (escale 8 a) (SA BV 0) (ELit 16); img_apart d 0 (escale 8 a) ].
Definition kn_out (m : smode) : list kentry :=
  (match m with MS => strS (EVar XSTR) | ML => strLx (EVar XSTR) (EVar (1 + XSTR)) (EVar (2 + XSTR)) end) ++ kn_fixed.
Definition tout (m : smode) : acs := mkcs RETPC regs_out (kn_out m) (XLO + 15)%nat (vis m XSTR).
Definition BCAP : Z := 10 * 2 ^ 30 + 2 ^ 24.   (* [comment removed for export] *)
Definition CCAP : Z := 4.
Definition ce2 : gcallee2 := GCE2 NXF tin [tout MS] [tout ML] BCAP CCAP.
Definition ce : gcallee := c2_merged ce2.

End B2JnUT.
End GuB2JT.
Module GuB2J.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzDev OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.


Import GuB2JT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Module B2JnU.
Import B2JnUT.


(* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 201 then Some B2JUT.ceL1 else None.
Definition CT2 (id : nat) : option gcallee2 := if Nat.eqb id 200 then Some (B2JUT.ce2 MS) else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc USEGS IT AUBSAN NXF GUBSAN BCAP CCAP CT.
Definition XB : nat -> list expr -> acs -> option (acs * acs) := XBc USEGS AUBSAN NXF GUBSAN BCAP CCAP CT2.
Definition LIMIT : Z := 2 ^ 34.
Definition FUEL : nat := 2000.
Definition BFUEL : nat := 600.

(* [comment removed for export] *)
Definition frame : list kentry :=
  [ KWord (SA e_sp (-8)) 8 (EVar 0); KWord (SA e_sp (-16)) 8 (EVar 7); KWord (SA e_sp (-24)) 8 (EVar 8);
    KWord (SA e_sp (-32)) 8 (EVar 17); KWord (SA e_sp (-40)) 8 (EVar 18); KWord (SA e_sp (-48)) 8 (EVar 19) ].
(* [comment removed for export] *)
Definition ctx_fixed : list kentry :=
  [ KWord (SA e_sp (-152)) 8 (ELit 0); KWord (SA e_sp (-144)) 8 (ELit 0); KWord (SA e_sp (-136)) 8 (ELit 0);
    KUnk (SA e_sp (-128)) (ELit 4); KZero (SA e_sp (-120)) (ELit 48); KWord (SA e_sp (-72)) 8 EEND ].
(* [comment removed for export] *)
Definition posk (ito ix sep : expr) : list kentry :=
  [ KWord (SA e_sp (-160)) 4 (ELit 0); KWord (SA e_sp (-64)) 8 (eadd INLO ito); KWord (SA e_sp (-56)) 8 ix;
    KRange ito 0 INSZ; KRange (esub BSZ ito) 0 INSZ; KRange ix 0 BIG;
    KRange sep 0 1; KRange (esub (esub (escale 24 ito) ix) sep) 0 BIG ].

(* [comment removed for export] *)
Definition JV : nat := 60. Definition J : expr := EVar JV.
Definition SEP : expr := EVar 61. Definition ITOJ : expr := EVar 62. Definition IXJ : expr := EVar 63.
Definition SSTR : nat := 64. Definition S4 : expr := EVar 67.
Definition hv_loop : list nat := [1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition regs_at (a0 s4 : expr) (v : nat) : list expr :=
  sr_havoc (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd regs0
     2 G) 8 R) 9 OBJ) 18 (eaddz OBJ 1)) 19 (ELit 10)) 10 a0) 20 s4) hv_loop v.
Definition kn_loop (m : smode) (sep ito ix : expr) (sv : nat) : list kentry :=
  [ KRange (esub ito J) 0 INSZ ] ++ posk ito ix sep ++ frame ++ ctx_fixed ++ str m ix ito sv ++ kn_fixed.
Definition INV (m : smode) : acs := mkcs HEAD (regs_at SEP S4 68) (kn_loop m SEP ITOJ IXJ SSTR) 83 (vis m SSTR).

(* [comment removed for export] *)
Definition room (m : smode) (v : nat) (req : expr) : list kentry :=
  match m with
  | MS => [KRange (esub (EVar v) req) 0 22]                                    (* [comment removed for export] *)
  | ML => [KRange (esub (escale 8 (EVar (2 + v))) (eaddz req 1)) 0 (8 * AHI);   (* [comment removed for export] *)
           KRange (esub (EVar (1 + v)) req) 0 (8 * AHI)]                        (* [comment removed for export] *)
  end.
Definition S4J : expr := EVar 103.     (* [comment removed for export] *)
Definition JSEP (m : smode) : acs :=
  mkcs JOINS (regs_at IXJ S4J 104)
       ([ KRange J 0 INSZ; KRange (esub ITOJ J) 0 INSZ; KRange SEP 1 1; KRange S4J 0 1 ] ++ posk ITOJ IXJ SEP ++ frame ++ ctx_fixed
        ++ str m IXJ ITOJ 100 ++ room m 100 (eaddz IXJ 1) ++ kn_fixed)
       119 (vis m 100).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition EXIT (m : smode) : plan := PRun [] (PHandoffW (hole m) []).
(* [comment removed for export] *)
Definition RSZ (m : smode) (v : nat) : list expr :=
  match m with MS => [ELit 0; EVar v] | ML => [ELit 1; EVar v; EVar (2 + v); EVar (1 + v)] end.
(* [comment removed for export] *)
Definition VARGS (m : smode) (ito ix : expr) (sv : nat) : list expr :=
  [TP; DUM; DUM; DUM; ito; DUM; BSZ; ix; INLO] ++
  match m with MS => [EVar sv; DUM; DUM] | ML => [EVar sv; EVar (1 + sv); EVar (2 + sv)] end.
(* [comment removed for export] *)
Definition post (m' : smode) : plan := PRun [0x2f420] (PBranch (EXIT m') (PRun [HEAD] PNext)).
Definition VBMP : nat := 150.
Definition XD : expr := EVar (VBMP + (B2JUT.XSTR - B2JUT.NXF)).     (* [comment removed for export] *)
Definition CALL (m : smode) (ix : expr) (sv : nat) : plan :=
  PBump VBMP (match m with
  | MS => PExt2 200 (VARGS MS ITOJ ix sv) (post MS) (PExt 13 [XD] (post ML))
  | ML => PExt 201 (VARGS ML ITOJ ix sv) (PExt 13 [XD] (post ML))
  end).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition DONE (m : smode) (sv : nat) : plan :=
  PRun [] (match m with
           | MS => PExt2 31 (RSZ MS sv) (EXIT MS) (EXIT ML)
           | ML => PExt2 31 (RSZ ML sv) (EXIT ML) (EXIT ML)
           end).
(* [comment removed for export] *)
Definition after_sep (m : smode) : plan := PRun [CALLV] (CALL m (eaddz IXJ 1) 100).
Definition sep (m : smode) : plan :=
  PViaM 1 (match m with MS => [(JSEP MS, after_sep MS); (JSEP ML, after_sep ML)] | ML => [(JSEP ML, after_sep ML)] end) 100
    (PRun [0x2f3b8] (PBranch
       (PRun [JOINS] (PMerge 1))                                                               (* [comment removed for export] *)
       (PRun [] (PExt2 31 (RSZ m SSTR) (PRun [JOINS] (PMerge 1)) (PRun [JOINS] (PMerge 1)))))).  (* [comment removed for export] *)
(* [comment removed for export] *)
Definition body (m : smode) : plan :=
  PRun [0x2f378] (PBranch                                                                      (* [comment removed for export] *)
    (PCase2 SEP 0
       (PRun [CALLV] (CALL m IXJ SSTR))                                                         (* [comment removed for export] *)
       (PRun [0x2f394] (PBranch (sep m) (PRun [CALLV] (CALL m IXJ SSTR)))))                     (* [comment removed for export] *)
    (DONE m SSTR)).
Definition loop : plan :=
  PLoopM JV BSZ [(INV MS, body MS, DONE MS SSTR); (INV ML, body ML, DONE ML SSTR)] [].
Definition plan : plan := PJoin OBJ 0 1 (PRun [] (PExt 2 [] (PRun [HEAD] loop))).   (* [comment removed for export] *)

Definition SHAPE : shape := SHole 0.

Lemma cert : check USEGS IT AUBSAN NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce ce) 0%nat BFUEL FUEL None tin plan = COk SHAPE.
Proof. vm_cast_no_check (@eq_refl cres (COk SHAPE)). Qed.
Lemma gplan : gplan_ok plan = true. Proof. reflexivity. Qed.
Lemma hshape : holes_only SHAPE = true. Proof. reflexivity. Qed.


End B2JnU.
End GuB2J.
Module GuB2JC.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon.   (* [comment removed for export] *)

Import GuB2JT GuB2J.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Import B2JnUT. Import B2JnU.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
(* [comment removed for export] *)
Hypothesis B2JV_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (c2_merged (B2JUT.ce2 MS)).
Hypothesis B2JV_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH B2JUT.ceL1.

Theorem b2j_callee : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH ce.
Proof.
  refine (contract_of_cert_xb USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            ce IT IT_ok LIMIT 0%nat BFUEL FUEL XN _ XB _ plan _ gplan hshape cert).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS IT AUBSAN ubsan_in_hull ubsan_hull_ok IT_ok NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 201); [|discriminate H]. injection H as <-. exact B2JV_L1.
    + (apply GC_all; first [assumption | exact IT_ok]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2).
    + intros id c H. unfold CT2 in H. destruct (Nat.eqb id 200); [|discriminate H]. injection H as <-. exact B2JV_S.
    + (apply OBL2_all; assumption).
Qed.
End Contract.
End GuB2JC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GuFA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GuFAPlan.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuFA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma fa_cert : exists p : plan, gplan_ok p = true /\
  check USEGS IT AUBSAN NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) (B2JCutShare.GlzCallCert.XB0) XC0 (HSce ce) 0%nat BFUEL FUEL None (ce_tin ce) p = COk (SHole 0).
Proof.
  exists (
(PCase2 (esub (esub EE B) O) 0 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PRun [0x31464] (PCaseReg 19 127 (PCaseReg 19 63 (PCaseReg 19 31 (PCaseReg 19 15 (PCaseReg 19 7 (PCaseReg 19 3 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 4 (PRespell 19 (ELit 4) (PRun [] (PVia 5 (JCT 4) 200 (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31d08] (PCaseReg 5 1 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (2)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))))))) (PRespell 5 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (1))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (3)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))))))))) (PCaseReg 5 2 (PRespell 5 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (1))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (5)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))))))) (PRespell 5 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (1))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e20] (PBranch (PFactLeR 16 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (9)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))))) (PRun [0x31610] (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)]))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))))) (PCaseReg 19 11 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 12 (PRespell 19 (ELit 12) (PRun [] (PVia 5 (JCT 12) 200 (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31d08] (PCaseReg 5 1 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (2)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))))))) (PRespell 5 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (1))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (3)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))))))))) (PCaseReg 5 2 (PRespell 5 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (1))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (5)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))))))) (PRespell 5 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (1))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e20] (PBranch (PFactLeR 16 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (9)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))))) (PRun [0x31610] (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PCase2 (esub (esub EE B) (eaddz JO (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))) (PCase2 (esub (esub EE B) (eaddz JO (2))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (2))) 0 BUFMAX) (PFactLe (eaddz JO (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (2)))])))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (3))) 0 BUFMAX) (PFactLe (eaddz JO (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (3)))]))))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)]))))))) (PCaseReg 19 23 (PCaseReg 19 19 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 20 (PRespell 19 (ELit 20) (PRun [] (PVia 5 (JCT 20) 200 (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31d08] (PCaseReg 5 1 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (2)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))))))) (PRespell 5 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (1))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (3)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))))))))) (PCaseReg 5 2 (PRespell 5 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (1))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (5)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))))))) (PRespell 5 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (1))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e20] (PBranch (PFactLeR 16 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (9)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))))) (PRun [0x31610] (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PCase2 (esub (esub EE B) (eaddz JO (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))) (PCase2 (esub (esub EE B) (eaddz JO (2))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (2))) 0 BUFMAX) (PFactLe (eaddz JO (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (2)))])))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (3))) 0 BUFMAX) (PFactLe (eaddz JO (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (3)))]))))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))))) (PCaseReg 19 27 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 28 (PRespell 19 (ELit 28) (PRun [] (PVia 5 (JCT 28) 200 (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31d08] (PCaseReg 5 1 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (2)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))))))) (PRespell 5 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (1))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (3)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))))))))) (PCaseReg 5 2 (PRespell 5 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (1))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (5)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))))))) (PRespell 5 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (1))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e20] (PBranch (PFactLeR 16 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (9)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))))) (PRun [0x31610] (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)]))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))))))) (PCaseReg 19 47 (PCaseReg 19 39 (PCaseReg 19 35 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 36 (PRespell 19 (ELit 36) (PRun [] (PVia 5 (JCT 36) 200 (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31d08] (PCaseReg 5 1 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (2)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))))))) (PRespell 5 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (1))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (3)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))))))))) (PCaseReg 5 2 (PRespell 5 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (1))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (5)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))))))) (PRespell 5 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (1))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e20] (PBranch (PFactLeR 16 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (9)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))))) (PRun [0x31610] (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)]))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))))) (PCaseReg 19 43 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 44 (PRespell 19 (ELit 44) (PRun [] (PVia 5 (JCT 44) 200 (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31d08] (PCaseReg 5 1 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (2)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))))))) (PRespell 5 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (1))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (3)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))))))))) (PCaseReg 5 2 (PRespell 5 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (1))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (5)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))))))) (PRespell 5 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (1))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e20] (PBranch (PFactLeR 16 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (9)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))))) (PRun [0x31610] (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PCase2 (esub (esub EE B) JO) 1 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PCase2 (esub (esub EE B) (eaddz JO (2))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (2))) 0 BUFMAX) (PFactLe (eaddz JO (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (2)))])))) (PCase2 (esub (esub EE B) (eaddz JO (2))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (2))) 0 BUFMAX) (PFactLe (eaddz JO (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (2)))])))) (PCase2 (esub (esub EE B) (eaddz JO (4))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (4))) 0 BUFMAX) (PFactLe (eaddz JO (4)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (4)))])))) (PCase2 (esub (esub EE B) (eaddz JO (4))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (4))) 0 BUFMAX) (PFactLe (eaddz JO (4)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (4)))])))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (6))) 0 BUFMAX) (PFactLe (eaddz JO (6)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (6)))])))))))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)]))))))) (PCaseReg 19 55 (PCaseReg 19 51 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 52 (PRespell 19 (ELit 52) (PRun [] (PVia 5 (JCT 52) 200 (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31d08] (PCaseReg 5 1 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (2)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))))))) (PRespell 5 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (1))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (3)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))))))))) (PCaseReg 5 2 (PRespell 5 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (1))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (5)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))))))) (PRespell 5 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (1))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e20] (PBranch (PFactLeR 16 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (9)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))))) (PRun [0x31610] (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PCase2 (esub (esub EE B) JO) 1 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PCase2 (esub (esub EE B) (eaddz JO (2))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (2))) 0 BUFMAX) (PFactLe (eaddz JO (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (2)))])))) (PCase2 (esub (esub EE B) (eaddz JO (2))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (2))) 0 BUFMAX) (PFactLe (eaddz JO (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (2)))])))) (PCase2 (esub (esub EE B) (eaddz JO (4))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (4))) 0 BUFMAX) (PFactLe (eaddz JO (4)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (4)))])))) (PCase2 (esub (esub EE B) (eaddz JO (4))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (4))) 0 BUFMAX) (PFactLe (eaddz JO (4)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (4)))])))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (6))) 0 BUFMAX) (PFactLe (eaddz JO (6)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (6)))])))))))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))))) (PCaseReg 19 59 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 60 (PRespell 19 (ELit 60) (PRun [] (PVia 5 (JCT 60) 200 (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31d08] (PCaseReg 5 1 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (2)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))))))) (PRespell 5 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (1))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (3)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))))))))) (PCaseReg 5 2 (PRespell 5 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (1))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (5)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))))))) (PRespell 5 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (1))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e20] (PBranch (PFactLeR 16 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (9)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))))) (PRun [0x31610] (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)]))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)]))))))))) (PCaseReg 19 95 (PCaseReg 19 79 (PCaseReg 19 71 (PCaseReg 19 67 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 68 (PRespell 19 (ELit 68) (PRun [] (PVia 5 (JCT 68) 200 (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31d08] (PCaseReg 5 1 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (2)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))))))) (PRespell 5 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (1))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (3)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))))))))) (PCaseReg 5 2 (PRespell 5 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (1))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (5)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))))))) (PRespell 5 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (1))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e20] (PBranch (PFactLeR 16 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (9)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))))) (PRun [0x31610] (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)]))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))))) (PCaseReg 19 75 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 76 (PRespell 19 (ELit 76) (PRun [] (PVia 5 (JCT 76) 200 (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31d08] (PCaseReg 5 1 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (2)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))))))) (PRespell 5 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (1))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (3)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))))))))) (PCaseReg 5 2 (PRespell 5 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (1))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (5)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))))))) (PRespell 5 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (1))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e20] (PBranch (PFactLeR 16 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (9)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))))) (PRun [0x31610] (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PCase2 (esub (esub EE B) JO) 3 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PCase2 (esub (esub EE B) (eaddz JO (4))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (4))) 0 BUFMAX) (PFactLe (eaddz JO (4)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (4)))])))) (PCase2 (esub (esub EE B) (eaddz JO (4))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (4))) 0 BUFMAX) (PFactLe (eaddz JO (4)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (4)))])))) (PCase2 (esub (esub EE B) (eaddz JO (8))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (8))) 0 BUFMAX) (PFactLe (eaddz JO (8)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (8)))])))) (PCase2 (esub (esub EE B) (eaddz JO (8))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (8))) 0 BUFMAX) (PFactLe (eaddz JO (8)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (8)))])))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (12))) 0 BUFMAX) (PFactLe (eaddz JO (12)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (12)))])))))))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)]))))))) (PCaseReg 19 87 (PCaseReg 19 83 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 84 (PRespell 19 (ELit 84) (PRun [] (PVia 5 (JCT 84) 200 (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31d08] (PCaseReg 5 1 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (2)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))))))) (PRespell 5 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (1))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (3)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))))))))) (PCaseReg 5 2 (PRespell 5 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (1))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (5)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))))))) (PRespell 5 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (1))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e20] (PBranch (PFactLeR 16 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (9)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))))) (PRun [0x31610] (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PCase2 (esub (esub EE B) JO) 3 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PCase2 (esub (esub EE B) (eaddz JO (4))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (4))) 0 BUFMAX) (PFactLe (eaddz JO (4)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (4)))])))) (PCase2 (esub (esub EE B) (eaddz JO (4))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (4))) 0 BUFMAX) (PFactLe (eaddz JO (4)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (4)))])))) (PCase2 (esub (esub EE B) (eaddz JO (8))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (8))) 0 BUFMAX) (PFactLe (eaddz JO (8)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (8)))])))) (PCase2 (esub (esub EE B) (eaddz JO (8))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (8))) 0 BUFMAX) (PFactLe (eaddz JO (8)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (8)))])))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (12))) 0 BUFMAX) (PFactLe (eaddz JO (12)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (12)))])))))))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))))) (PCaseReg 19 91 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 92 (PRespell 19 (ELit 92) (PRun [] (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x314ac] (PCaseReg 11 127 (PCaseReg 11 63 (PCaseReg 11 31 (PCaseReg 11 15 (PCaseReg 11 7 (PCaseReg 11 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 4 (PRespell 11 (ELit 4) (PRun [] (PVia 6 (JBOT 4 1) 200 (PCase2 (esub (esub EE B) (eaddz O (2))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31824] (PCaseReg 17 1 (PCaseReg 17 0 (PRespell 17 (ELit 0) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (3)))]))) (PRespell 17 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (2))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (4)))]))))) (PCaseReg 17 2 (PRespell 17 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (2))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (6)))])))) (PRespell 17 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (2))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a6c] (PBranch (PFactLeR 14 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (10)))]))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (10))) 0 BUFMAX) (PFactLe (eaddz O (10)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (10)))])))))))))))) (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [0x31a94] (PCaseReg 15 0 (PBump 260 (PFresh 15 0 None (PRun [0x31aa4] (PBranch (PFactVia (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub (esub EE B) (eaddz JO (1))) (eadd (escale 1 JCNT) PAD)) 0 (2^57) (PFactLe (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub EE B) (eaddz JO (1))) BUFMAX (PRun [0x31abc] (PCaseReg 14 3 (PRun [0x31af4] (PCase2 (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))))) (PCaseReg 11 11 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 12 (PRespell 11 (ELit 12) (PRun [] (PVia 6 (JBOT 12 1) 200 (PCase2 (esub (esub EE B) (eaddz O (2))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31824] (PCaseReg 17 1 (PCaseReg 17 0 (PRespell 17 (ELit 0) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (3)))]))) (PRespell 17 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (2))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (4)))]))))) (PCaseReg 17 2 (PRespell 17 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (2))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (6)))])))) (PRespell 17 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (2))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a6c] (PBranch (PFactLeR 14 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (10)))]))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (10))) 0 BUFMAX) (PFactLe (eaddz O (10)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (10)))])))))))))))) (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [0x31a94] (PCaseReg 15 0 (PBump 260 (PFresh 15 0 None (PRun [0x31aa4] (PBranch (PFactVia (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub (esub EE B) (eaddz JO (1))) (eadd (escale 1 JCNT) PAD)) 0 (2^57) (PFactLe (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub EE B) (eaddz JO (1))) BUFMAX (PRun [0x31abc] (PCaseReg 14 3 (PRun [0x31af4] (PCase2 (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))) (PCase2 (esub (esub EE B) (eadd (eaddz JO (2)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (2)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (2)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (2)) PAD))])))) (PCase2 (esub (esub EE B) (eadd (eaddz JO (3)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (3)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (3)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (3)) PAD))])))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (4)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (4)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (4)) PAD))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))]))))))) (PCaseReg 11 23 (PCaseReg 11 19 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 20 (PRespell 11 (ELit 20) (PRun [] (PVia 6 (JBOT 20 1) 200 (PCase2 (esub (esub EE B) (eaddz O (2))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31824] (PCaseReg 17 1 (PCaseReg 17 0 (PRespell 17 (ELit 0) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (3)))]))) (PRespell 17 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (2))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (4)))]))))) (PCaseReg 17 2 (PRespell 17 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (2))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (6)))])))) (PRespell 17 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (2))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a6c] (PBranch (PFactLeR 14 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (10)))]))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (10))) 0 BUFMAX) (PFactLe (eaddz O (10)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (10)))])))))))))))) (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [0x31a94] (PCaseReg 15 0 (PBump 260 (PFresh 15 0 None (PRun [0x31aa4] (PBranch (PFactVia (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub (esub EE B) (eaddz JO (1))) (eadd (escale 1 JCNT) PAD)) 0 (2^57) (PFactLe (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub EE B) (eaddz JO (1))) BUFMAX (PRun [0x31abc] (PCaseReg 14 3 (PRun [0x31af4] (PCase2 (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))) (PCase2 (esub (esub EE B) (eadd (eaddz JO (2)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (2)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (2)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (2)) PAD))])))) (PCase2 (esub (esub EE B) (eadd (eaddz JO (3)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (3)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (3)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (3)) PAD))])))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (4)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (4)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (4)) PAD))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))))) (PCaseReg 11 27 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 28 (PRespell 11 (ELit 28) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))]))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))))))) (PCaseReg 11 47 (PCaseReg 11 39 (PCaseReg 11 35 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 36 (PRespell 11 (ELit 36) (PRun [] (PVia 6 (JBOT 36 2) 200 (PCase2 (esub (esub EE B) (eaddz O (2))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31824] (PCaseReg 17 1 (PCaseReg 17 0 (PRespell 17 (ELit 0) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (3)))]))) (PRespell 17 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (2))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (4)))]))))) (PCaseReg 17 2 (PRespell 17 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (2))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (6)))])))) (PRespell 17 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (2))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a6c] (PBranch (PFactLeR 14 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (10)))]))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (10))) 0 BUFMAX) (PFactLe (eaddz O (10)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (10)))])))))))))))) (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [0x31a94] (PCaseReg 15 1 (PBump 260 (PFresh 15 0 None (PRun [0x31aa4] (PBranch (PFactVia (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub (esub EE B) (eaddz JO (1))) (eadd (escale 2 JCNT) PAD)) 0 (2^57) (PFactLe (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub EE B) (eaddz JO (1))) BUFMAX (PRun [0x31abc] (PCaseReg 14 3 (PRun [0x31af4] (PCase2 (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))))) (PCaseReg 11 43 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 44 (PRespell 11 (ELit 44) (PRun [] (PVia 6 (JBOT 44 2) 200 (PCase2 (esub (esub EE B) (eaddz O (2))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31824] (PCaseReg 17 1 (PCaseReg 17 0 (PRespell 17 (ELit 0) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (3)))]))) (PRespell 17 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (2))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (4)))]))))) (PCaseReg 17 2 (PRespell 17 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (2))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (6)))])))) (PRespell 17 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (2))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a6c] (PBranch (PFactLeR 14 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (10)))]))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (10))) 0 BUFMAX) (PFactLe (eaddz O (10)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (10)))])))))))))))) (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [0x31a94] (PCaseReg 15 1 (PBump 260 (PFresh 15 0 None (PRun [0x31aa4] (PBranch (PFactVia (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub (esub EE B) (eaddz JO (1))) (eadd (escale 2 JCNT) PAD)) 0 (2^57) (PFactLe (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub EE B) (eaddz JO (1))) BUFMAX (PRun [0x31abc] (PCaseReg 14 3 (PRun [0x31af4] (PCase2 (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))) (PCase2 (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))) (PCase2 (esub (esub EE B) (eadd (eaddz JO (3)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (3)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (3)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (3)) PAD))])))) (PCase2 (esub (esub EE B) (eadd (eaddz JO (3)) PAD)) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (3)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (3)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (3)) PAD))])))) (PCase2 (esub (esub EE B) (eadd (eaddz JO (5)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (5)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (5)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (5)) PAD))])))) (PCase2 (esub (esub EE B) (eadd (eaddz JO (5)) PAD)) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (5)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (5)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (5)) PAD))])))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (7)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (7)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (7)) PAD))]))))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))]))))))) (PCaseReg 11 55 (PCaseReg 11 51 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 52 (PRespell 11 (ELit 52) (PRun [] (PVia 6 (JBOT 52 2) 200 (PCase2 (esub (esub EE B) (eaddz O (2))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31824] (PCaseReg 17 1 (PCaseReg 17 0 (PRespell 17 (ELit 0) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (3)))]))) (PRespell 17 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (2))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (4)))]))))) (PCaseReg 17 2 (PRespell 17 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (2))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (6)))])))) (PRespell 17 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (2))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a6c] (PBranch (PFactLeR 14 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (10)))]))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (10))) 0 BUFMAX) (PFactLe (eaddz O (10)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (10)))])))))))))))) (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [0x31a94] (PCaseReg 15 1 (PBump 260 (PFresh 15 0 None (PRun [0x31aa4] (PBranch (PFactVia (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub (esub EE B) (eaddz JO (1))) (eadd (escale 2 JCNT) PAD)) 0 (2^57) (PFactLe (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub EE B) (eaddz JO (1))) BUFMAX (PRun [0x31abc] (PCaseReg 14 3 (PRun [0x31af4] (PCase2 (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))) (PCase2 (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))) (PCase2 (esub (esub EE B) (eadd (eaddz JO (3)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (3)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (3)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (3)) PAD))])))) (PCase2 (esub (esub EE B) (eadd (eaddz JO (3)) PAD)) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (3)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (3)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (3)) PAD))])))) (PCase2 (esub (esub EE B) (eadd (eaddz JO (5)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (5)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (5)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (5)) PAD))])))) (PCase2 (esub (esub EE B) (eadd (eaddz JO (5)) PAD)) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (5)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (5)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (5)) PAD))])))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (7)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (7)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (7)) PAD))]))))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))))) (PCaseReg 11 59 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 60 (PRespell 11 (ELit 60) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))]))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))]))))))))) (PCaseReg 11 95 (PCaseReg 11 79 (PCaseReg 11 71 (PCaseReg 11 67 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 68 (PRespell 11 (ELit 68) (PRun [] (PVia 6 (JBOT 68 4) 200 (PCase2 (esub (esub EE B) (eaddz O (2))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31824] (PCaseReg 17 1 (PCaseReg 17 0 (PRespell 17 (ELit 0) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (3)))]))) (PRespell 17 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (2))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (4)))]))))) (PCaseReg 17 2 (PRespell 17 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (2))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (6)))])))) (PRespell 17 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (2))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a6c] (PBranch (PFactLeR 14 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (10)))]))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (10))) 0 BUFMAX) (PFactLe (eaddz O (10)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (10)))])))))))))))) (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [0x31a94] (PCaseReg 15 3 (PBump 260 (PFresh 15 0 None (PRun [0x31aa4] (PBranch (PFactVia (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub (esub EE B) (eaddz JO (1))) (eadd (escale 4 JCNT) PAD)) 0 (2^57) (PFactLe (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub EE B) (eaddz JO (1))) BUFMAX (PRun [0x31abc] (PCaseReg 14 3 (PRun [0x31af4] (PCase2 (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))))) (PCaseReg 11 75 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 76 (PRespell 11 (ELit 76) (PRun [] (PVia 6 (JBOT 76 4) 200 (PCase2 (esub (esub EE B) (eaddz O (2))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31824] (PCaseReg 17 1 (PCaseReg 17 0 (PRespell 17 (ELit 0) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (3)))]))) (PRespell 17 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (2))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (4)))]))))) (PCaseReg 17 2 (PRespell 17 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (2))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (6)))])))) (PRespell 17 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (2))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a6c] (PBranch (PFactLeR 14 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (10)))]))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (10))) 0 BUFMAX) (PFactLe (eaddz O (10)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (10)))])))))))))))) (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [0x31a94] (PCaseReg 15 3 (PBump 260 (PFresh 15 0 None (PRun [0x31aa4] (PBranch (PFactVia (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub (esub EE B) (eaddz JO (1))) (eadd (escale 4 JCNT) PAD)) 0 (2^57) (PFactLe (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub EE B) (eaddz JO (1))) BUFMAX (PRun [0x31abc] (PCaseReg 14 3 (PRun [0x31af4] (PCase2 (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))) (PCase2 (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))) (PCase2 (esub (esub EE B) (eadd (eaddz JO (5)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (5)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (5)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (5)) PAD))])))) (PCase2 (esub (esub EE B) (eadd (eaddz JO (5)) PAD)) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (5)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (5)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (5)) PAD))])))) (PCase2 (esub (esub EE B) (eadd (eaddz JO (9)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (9)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (9)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (9)) PAD))])))) (PCase2 (esub (esub EE B) (eadd (eaddz JO (9)) PAD)) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (9)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (9)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (9)) PAD))])))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (13)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (13)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (13)) PAD))]))))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))]))))))) (PCaseReg 11 87 (PCaseReg 11 83 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 84 (PRespell 11 (ELit 84) (PRun [] (PVia 6 (JBOT 84 4) 200 (PCase2 (esub (esub EE B) (eaddz O (2))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31824] (PCaseReg 17 1 (PCaseReg 17 0 (PRespell 17 (ELit 0) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (3)))]))) (PRespell 17 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (2))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (4)))]))))) (PCaseReg 17 2 (PRespell 17 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (2))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (6)))])))) (PRespell 17 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (2))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a6c] (PBranch (PFactLeR 14 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (10)))]))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (10))) 0 BUFMAX) (PFactLe (eaddz O (10)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (10)))])))))))))))) (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [0x31a94] (PCaseReg 15 3 (PBump 260 (PFresh 15 0 None (PRun [0x31aa4] (PBranch (PFactVia (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub (esub EE B) (eaddz JO (1))) (eadd (escale 4 JCNT) PAD)) 0 (2^57) (PFactLe (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub EE B) (eaddz JO (1))) BUFMAX (PRun [0x31abc] (PCaseReg 14 3 (PRun [0x31af4] (PCase2 (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))) (PCase2 (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))) (PCase2 (esub (esub EE B) (eadd (eaddz JO (5)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (5)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (5)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (5)) PAD))])))) (PCase2 (esub (esub EE B) (eadd (eaddz JO (5)) PAD)) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (5)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (5)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (5)) PAD))])))) (PCase2 (esub (esub EE B) (eadd (eaddz JO (9)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (9)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (9)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (9)) PAD))])))) (PCase2 (esub (esub EE B) (eadd (eaddz JO (9)) PAD)) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (9)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (9)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (9)) PAD))])))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (13)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (13)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (13)) PAD))]))))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))))) (PCaseReg 11 91 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 92 (PRespell 11 (ELit 92) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))]))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))))))) (PCaseReg 11 111 (PCaseReg 11 103 (PCaseReg 11 99 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 100 (PRespell 11 (ELit 100) (PRun [] (PVia 6 (JBOT 100 8) 200 (PCase2 (esub (esub EE B) (eaddz O (2))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31824] (PCaseReg 17 1 (PCaseReg 17 0 (PRespell 17 (ELit 0) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (3)))]))) (PRespell 17 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (2))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (4)))]))))) (PCaseReg 17 2 (PRespell 17 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (2))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (6)))])))) (PRespell 17 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (2))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a6c] (PBranch (PFactLeR 14 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (10)))]))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (10))) 0 BUFMAX) (PFactLe (eaddz O (10)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (10)))])))))))))))) (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [0x31a94] (PCaseReg 15 7 (PBump 260 (PFresh 15 0 None (PRun [0x31aa4] (PBranch (PFactVia (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub (esub EE B) (eaddz JO (1))) (eadd (escale 8 JCNT) PAD)) 0 (2^57) (PFactLe (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub EE B) (eaddz JO (1))) BUFMAX (PRun [0x31abc] (PCaseReg 14 3 (PRun [0x31af4] (PCase2 (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))))) (PCaseReg 11 107 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 108 (PRespell 11 (ELit 108) (PRun [] (PVia 6 (JBOT 108 8) 200 (PCase2 (esub (esub EE B) (eaddz O (2))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31824] (PCaseReg 17 1 (PCaseReg 17 0 (PRespell 17 (ELit 0) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (3)))]))) (PRespell 17 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (2))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (4)))]))))) (PCaseReg 17 2 (PRespell 17 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (2))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (6)))])))) (PRespell 17 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (2))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a6c] (PBranch (PFactLeR 14 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (10)))]))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (10))) 0 BUFMAX) (PFactLe (eaddz O (10)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (10)))])))))))))))) (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [0x31a94] (PCaseReg 15 7 (PBump 260 (PFresh 15 0 None (PRun [0x31aa4] (PBranch (PFactVia (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub (esub EE B) (eaddz JO (1))) (eadd (escale 8 JCNT) PAD)) 0 (2^57) (PFactLe (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub EE B) (eaddz JO (1))) BUFMAX (PRun [0x31abc] (PCaseReg 14 3 (PRun [0x31af4] (PCase2 (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))) (PCase2 (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))) (PCase2 (esub (esub EE B) (eadd (eaddz JO (9)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (9)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (9)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (9)) PAD))])))) (PCase2 (esub (esub EE B) (eadd (eaddz JO (9)) PAD)) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (9)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (9)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (9)) PAD))])))) (PCase2 (esub (esub EE B) (eadd (eaddz JO (17)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (17)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (17)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (17)) PAD))])))) (PCase2 (esub (esub EE B) (eadd (eaddz JO (17)) PAD)) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (17)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (17)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (17)) PAD))])))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (25)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (25)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (25)) PAD))]))))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))]))))))) (PCaseReg 11 119 (PCaseReg 11 115 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 116 (PRespell 11 (ELit 116) (PRun [] (PVia 7 JBUT 200 (PCase2 (esub (esub EE B) (eaddz O (2))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x314f0] (PCaseReg 14 1 (PCaseReg 14 0 (PRespell 14 (ELit 0) (PRun [0x31980] (PMergeW 7 [(200%nat, (eaddz O (3)))]))) (PRespell 14 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (2))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31980] (PMergeW 7 [(200%nat, (eaddz O (4)))]))))) (PCaseReg 14 2 (PRespell 14 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (2))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31980] (PMergeW 7 [(200%nat, (eaddz O (6)))])))) (PRespell 14 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (2))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31978] (PBranch (PFactLeR 10 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31980] (PMergeW 7 [(200%nat, (eaddz O (10)))]))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (10))) 0 BUFMAX) (PFactLe (eaddz O (10)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (10)))])))))))))))) (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [0x319a4] (PCaseReg 12 7 (PBump 260 (PFresh 12 0 None (PRun [0x319b4] (PBranch (PFactVia (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub (esub EE B) (eaddz JO (1))) (eadd (escale 8 JCNT) PAD)) 0 (2^57) (PFactLe (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub EE B) (eaddz JO (1))) BUFMAX (PRun [0x319cc] (PCaseReg 10 3 (PRun [0x31554] (PCaseReg 10 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))) (PBranch (PFact (KRange (escale 8 JCNT) 8 24) (PRun [] (PExt 1 [] (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eadd (eaddz JO (1)) PAD) (escale 8 JCNT))) 0 BUFMAX) (PFactLe (eadd (eadd (eaddz JO (1)) PAD) (escale 8 JCNT)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eadd (eaddz JO (1)) PAD) (escale 8 JCNT)))]))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))]))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))))) (PCaseReg 11 123 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 124 (PRespell 11 (ELit 124) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))]))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))))))))) (PCaseReg 11 191 (PCaseReg 11 159 (PCaseReg 11 143 (PCaseReg 11 135 (PCaseReg 11 131 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 132 (PRespell 11 (ELit 132) (PRun [] (PVia 6 (JBOT 132 16) 200 (PCase2 (esub (esub EE B) (eaddz O (2))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31824] (PCaseReg 17 1 (PCaseReg 17 0 (PRespell 17 (ELit 0) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (3)))]))) (PRespell 17 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (2))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (4)))]))))) (PCaseReg 17 2 (PRespell 17 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (2))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (6)))])))) (PRespell 17 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (2))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a6c] (PBranch (PFactLeR 14 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (10)))]))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (10))) 0 BUFMAX) (PFactLe (eaddz O (10)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (10)))])))))))))))) (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [0x31a94] (PCaseReg 15 15 (PBump 260 (PFresh 15 0 None (PRun [0x31aa4] (PBranch (PFactVia (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub (esub EE B) (eaddz JO (1))) (eadd (escale 16 JCNT) PAD)) 0 (2^57) (PFactLe (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub EE B) (eaddz JO (1))) BUFMAX (PRun [0x31abc] (PCaseReg 14 3 (PRun [0x31af4] (PCase2 (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))))) (PCaseReg 11 139 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 140 (PRespell 11 (ELit 140) (PRun [] (PVia 6 (JBOT 140 16) 200 (PCase2 (esub (esub EE B) (eaddz O (2))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31824] (PCaseReg 17 1 (PCaseReg 17 0 (PRespell 17 (ELit 0) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (3)))]))) (PRespell 17 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (2))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (4)))]))))) (PCaseReg 17 2 (PRespell 17 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (2))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (6)))])))) (PRespell 17 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (2))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a6c] (PBranch (PFactLeR 14 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (10)))]))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (10))) 0 BUFMAX) (PFactLe (eaddz O (10)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (10)))])))))))))))) (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [0x31a94] (PCaseReg 15 15 (PBump 260 (PFresh 15 0 None (PRun [0x31aa4] (PBranch (PFactVia (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub (esub EE B) (eaddz JO (1))) (eadd (escale 16 JCNT) PAD)) 0 (2^57) (PFactLe (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub EE B) (eaddz JO (1))) BUFMAX (PRun [0x31abc] (PCaseReg 14 3 (PRun [0x31af4] (PCase2 (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))]))))))) (PCaseReg 11 151 (PCaseReg 11 147 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 148 (PRespell 11 (ELit 148) (PRun [] (PVia 6 (JBOT 148 16) 200 (PCase2 (esub (esub EE B) (eaddz O (2))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31824] (PCaseReg 17 1 (PCaseReg 17 0 (PRespell 17 (ELit 0) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (3)))]))) (PRespell 17 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (2))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (4)))]))))) (PCaseReg 17 2 (PRespell 17 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (2))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (6)))])))) (PRespell 17 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (2))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a6c] (PBranch (PFactLeR 14 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (10)))]))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (10))) 0 BUFMAX) (PFactLe (eaddz O (10)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (10)))])))))))))))) (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [0x31a94] (PCaseReg 15 15 (PBump 260 (PFresh 15 0 None (PRun [0x31aa4] (PBranch (PFactVia (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub (esub EE B) (eaddz JO (1))) (eadd (escale 16 JCNT) PAD)) 0 (2^57) (PFactLe (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub EE B) (eaddz JO (1))) BUFMAX (PRun [0x31abc] (PCaseReg 14 3 (PRun [0x31af4] (PCase2 (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))))) (PCaseReg 11 155 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 156 (PRespell 11 (ELit 156) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))]))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))))))) (PCaseReg 11 175 (PCaseReg 11 167 (PCaseReg 11 163 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 164 (PRespell 11 (ELit 164) (PRun [] (PVia 6 (JBOT 164 32) 200 (PCase2 (esub (esub EE B) (eaddz O (2))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31824] (PCaseReg 17 1 (PCaseReg 17 0 (PRespell 17 (ELit 0) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (3)))]))) (PRespell 17 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (2))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (4)))]))))) (PCaseReg 17 2 (PRespell 17 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (2))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (6)))])))) (PRespell 17 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (2))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a6c] (PBranch (PFactLeR 14 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (10)))]))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (10))) 0 BUFMAX) (PFactLe (eaddz O (10)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (10)))])))))))))))) (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [0x31a94] (PCaseReg 15 31 (PBump 260 (PFresh 15 0 None (PRun [0x31aa4] (PBranch (PFactVia (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub (esub EE B) (eaddz JO (1))) (eadd (escale 32 JCNT) PAD)) 0 (2^57) (PFactLe (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub EE B) (eaddz JO (1))) BUFMAX (PRun [0x31abc] (PCaseReg 14 3 (PRun [0x31af4] (PCase2 (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))))) (PCaseReg 11 171 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 172 (PRespell 11 (ELit 172) (PRun [] (PVia 6 (JBOT 172 32) 200 (PCase2 (esub (esub EE B) (eaddz O (2))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31824] (PCaseReg 17 1 (PCaseReg 17 0 (PRespell 17 (ELit 0) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (3)))]))) (PRespell 17 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (2))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (4)))]))))) (PCaseReg 17 2 (PRespell 17 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (2))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (6)))])))) (PRespell 17 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (2))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a6c] (PBranch (PFactLeR 14 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (10)))]))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (10))) 0 BUFMAX) (PFactLe (eaddz O (10)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (10)))])))))))))))) (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [0x31a94] (PCaseReg 15 31 (PBump 260 (PFresh 15 0 None (PRun [0x31aa4] (PBranch (PFactVia (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub (esub EE B) (eaddz JO (1))) (eadd (escale 32 JCNT) PAD)) 0 (2^57) (PFactLe (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub EE B) (eaddz JO (1))) BUFMAX (PRun [0x31abc] (PCaseReg 14 3 (PRun [0x31af4] (PCase2 (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))]))))))) (PCaseReg 11 183 (PCaseReg 11 179 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 180 (PRespell 11 (ELit 180) (PRun [] (PVia 6 (JBOT 180 32) 200 (PCase2 (esub (esub EE B) (eaddz O (2))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31824] (PCaseReg 17 1 (PCaseReg 17 0 (PRespell 17 (ELit 0) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (3)))]))) (PRespell 17 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (2))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (4)))]))))) (PCaseReg 17 2 (PRespell 17 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (2))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (6)))])))) (PRespell 17 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (2))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a6c] (PBranch (PFactLeR 14 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (10)))]))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (10))) 0 BUFMAX) (PFactLe (eaddz O (10)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (10)))])))))))))))) (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [0x31a94] (PCaseReg 15 31 (PBump 260 (PFresh 15 0 None (PRun [0x31aa4] (PBranch (PFactVia (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub (esub EE B) (eaddz JO (1))) (eadd (escale 32 JCNT) PAD)) 0 (2^57) (PFactLe (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub EE B) (eaddz JO (1))) BUFMAX (PRun [0x31abc] (PCaseReg 14 3 (PRun [0x31af4] (PCase2 (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))))) (PCaseReg 11 187 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 188 (PRespell 11 (ELit 188) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))]))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))]))))))))) (PCaseReg 11 223 (PCaseReg 11 207 (PCaseReg 11 199 (PCaseReg 11 195 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 196 (PRespell 11 (ELit 196) (PRun [] (PVia 6 (JBOT 196 64) 200 (PCase2 (esub (esub EE B) (eaddz O (2))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31824] (PCaseReg 17 1 (PCaseReg 17 0 (PRespell 17 (ELit 0) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (3)))]))) (PRespell 17 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (2))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (4)))]))))) (PCaseReg 17 2 (PRespell 17 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (2))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (6)))])))) (PRespell 17 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (2))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a6c] (PBranch (PFactLeR 14 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (10)))]))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (10))) 0 BUFMAX) (PFactLe (eaddz O (10)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (10)))])))))))))))) (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [0x31a94] (PCaseReg 15 63 (PBump 260 (PFresh 15 0 None (PRun [0x31aa4] (PBranch (PFactVia (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub (esub EE B) (eaddz JO (1))) (eadd (escale 64 JCNT) PAD)) 0 (2^57) (PFactLe (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub EE B) (eaddz JO (1))) BUFMAX (PRun [0x31abc] (PCaseReg 14 3 (PRun [0x31af4] (PCase2 (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))))) (PCaseReg 11 203 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 204 (PRespell 11 (ELit 204) (PRun [] (PVia 6 (JBOT 204 64) 200 (PCase2 (esub (esub EE B) (eaddz O (2))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31824] (PCaseReg 17 1 (PCaseReg 17 0 (PRespell 17 (ELit 0) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (3)))]))) (PRespell 17 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (2))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (4)))]))))) (PCaseReg 17 2 (PRespell 17 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (2))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (6)))])))) (PRespell 17 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (2))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a6c] (PBranch (PFactLeR 14 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (10)))]))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (10))) 0 BUFMAX) (PFactLe (eaddz O (10)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (10)))])))))))))))) (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [0x31a94] (PCaseReg 15 63 (PBump 260 (PFresh 15 0 None (PRun [0x31aa4] (PBranch (PFactVia (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub (esub EE B) (eaddz JO (1))) (eadd (escale 64 JCNT) PAD)) 0 (2^57) (PFactLe (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub EE B) (eaddz JO (1))) BUFMAX (PRun [0x31abc] (PCaseReg 14 3 (PRun [0x31af4] (PCase2 (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))]))))))) (PCaseReg 11 215 (PCaseReg 11 211 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 212 (PRespell 11 (ELit 212) (PRun [] (PVia 6 (JBOT 212 64) 200 (PCase2 (esub (esub EE B) (eaddz O (2))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31824] (PCaseReg 17 1 (PCaseReg 17 0 (PRespell 17 (ELit 0) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (3)))]))) (PRespell 17 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (2))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (4)))]))))) (PCaseReg 17 2 (PRespell 17 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (2))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (6)))])))) (PRespell 17 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (2))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a6c] (PBranch (PFactLeR 14 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (10)))]))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (10))) 0 BUFMAX) (PFactLe (eaddz O (10)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (10)))])))))))))))) (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [0x31a94] (PCaseReg 15 63 (PBump 260 (PFresh 15 0 None (PRun [0x31aa4] (PBranch (PFactVia (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub (esub EE B) (eaddz JO (1))) (eadd (escale 64 JCNT) PAD)) 0 (2^57) (PFactLe (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub EE B) (eaddz JO (1))) BUFMAX (PRun [0x31abc] (PCaseReg 14 3 (PRun [0x31af4] (PCase2 (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))))) (PCaseReg 11 219 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 220 (PRespell 11 (ELit 220) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))]))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))))))) (PCaseReg 11 239 (PCaseReg 11 231 (PCaseReg 11 227 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 228 (PRespell 11 (ELit 228) (PRun [] (PVia 6 (JBOT 228 128) 200 (PCase2 (esub (esub EE B) (eaddz O (2))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31824] (PCaseReg 17 1 (PCaseReg 17 0 (PRespell 17 (ELit 0) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (3)))]))) (PRespell 17 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (2))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (4)))]))))) (PCaseReg 17 2 (PRespell 17 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (2))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (6)))])))) (PRespell 17 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (2))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a6c] (PBranch (PFactLeR 14 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (10)))]))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (10))) 0 BUFMAX) (PFactLe (eaddz O (10)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (10)))])))))))))))) (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [0x31a94] (PCaseReg 15 127 (PBump 260 (PFresh 15 0 None (PRun [0x31aa4] (PBranch (PFactVia (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub (esub EE B) (eaddz JO (1))) (eadd (escale 128 JCNT) PAD)) 0 (2^57) (PFactLe (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub EE B) (eaddz JO (1))) BUFMAX (PRun [0x31abc] (PCaseReg 14 3 (PRun [0x31af4] (PCase2 (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))))) (PCaseReg 11 235 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 236 (PRespell 11 (ELit 236) (PRun [] (PVia 6 (JBOT 236 128) 200 (PCase2 (esub (esub EE B) (eaddz O (2))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31824] (PCaseReg 17 1 (PCaseReg 17 0 (PRespell 17 (ELit 0) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (3)))]))) (PRespell 17 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (2))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (4)))]))))) (PCaseReg 17 2 (PRespell 17 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (2))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (6)))])))) (PRespell 17 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (2))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a6c] (PBranch (PFactLeR 14 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (10)))]))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (10))) 0 BUFMAX) (PFactLe (eaddz O (10)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (10)))])))))))))))) (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [0x31a94] (PCaseReg 15 127 (PBump 260 (PFresh 15 0 None (PRun [0x31aa4] (PBranch (PFactVia (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub (esub EE B) (eaddz JO (1))) (eadd (escale 128 JCNT) PAD)) 0 (2^57) (PFactLe (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub EE B) (eaddz JO (1))) BUFMAX (PRun [0x31abc] (PCaseReg 14 3 (PRun [0x31af4] (PCase2 (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))]))))))) (PCaseReg 11 247 (PCaseReg 11 243 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 244 (PRespell 11 (ELit 244) (PRun [] (PVia 6 (JBOT 244 128) 200 (PCase2 (esub (esub EE B) (eaddz O (2))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31824] (PCaseReg 17 1 (PCaseReg 17 0 (PRespell 17 (ELit 0) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (3)))]))) (PRespell 17 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (2))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (4)))]))))) (PCaseReg 17 2 (PRespell 17 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (2))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (6)))])))) (PRespell 17 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (2))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PRun [0x31a6c] (PBranch (PFactLeR 14 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31a74] (PMergeW 6 [(200%nat, (eaddz O (10)))]))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (10))) 0 BUFMAX) (PFactLe (eaddz O (10)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (10)))])))))))))))) (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [0x31a94] (PCaseReg 15 127 (PBump 260 (PFresh 15 0 None (PRun [0x31aa4] (PBranch (PFactVia (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub (esub EE B) (eaddz JO (1))) (eadd (escale 128 JCNT) PAD)) 0 (2^57) (PFactLe (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) (esub (esub EE B) (eaddz JO (1))) BUFMAX (PRun [0x31abc] (PCaseReg 14 3 (PRun [0x31af4] (PCase2 (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz JO (1)) PAD)) 0 BUFMAX) (PFactLe (eadd (eaddz JO (1)) PAD) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz JO (1)) PAD))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (1))) 0 BUFMAX) (PFactLe (eaddz JO (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (1)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))))) (PCaseReg 11 251 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PCaseReg 11 252 (PRespell 11 (ELit 252) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))]))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))]))))))))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))))))) (PCaseReg 19 111 (PCaseReg 19 103 (PCaseReg 19 99 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 100 (PRespell 19 (ELit 100) (PRun [] (PVia 5 (JCT 100) 200 (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31d08] (PCaseReg 5 1 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (2)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))))))) (PRespell 5 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (1))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (3)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))))))))) (PCaseReg 5 2 (PRespell 5 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (1))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (5)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))))))) (PRespell 5 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (1))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e20] (PBranch (PFactLeR 16 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (9)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))))) (PRun [0x31610] (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)]))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))))) (PCaseReg 19 107 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 108 (PRespell 19 (ELit 108) (PRun [] (PVia 5 (JCT 108) 200 (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31d08] (PCaseReg 5 1 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (2)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))))))) (PRespell 5 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (1))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (3)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))))))))) (PCaseReg 5 2 (PRespell 5 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (1))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (5)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))))))) (PRespell 5 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (1))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e20] (PBranch (PFactLeR 16 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (9)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))))) (PRun [0x31610] (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PCase2 (esub (esub EE B) JO) 7 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PCase2 (esub (esub EE B) (eaddz JO (8))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (8))) 0 BUFMAX) (PFactLe (eaddz JO (8)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (8)))])))) (PCase2 (esub (esub EE B) (eaddz JO (8))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (8))) 0 BUFMAX) (PFactLe (eaddz JO (8)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (8)))])))) (PCase2 (esub (esub EE B) (eaddz JO (16))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (16))) 0 BUFMAX) (PFactLe (eaddz JO (16)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (16)))])))) (PCase2 (esub (esub EE B) (eaddz JO (16))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (16))) 0 BUFMAX) (PFactLe (eaddz JO (16)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (16)))])))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz JO (24))) 0 BUFMAX) (PFactLe (eaddz JO (24)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz JO (24)))])))))))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)]))))))) (PCaseReg 19 119 (PCaseReg 19 115 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 116 (PRespell 19 (ELit 116) (PRun [] (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31d08] (PCaseReg 5 1 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x31554] (PCaseReg 10 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))) (PBranch (PFact (KRange (escale 8 CNT) 8 24) (PRun [] (PExt 1 [] (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz O (2)) (escale 8 CNT))) 0 BUFMAX) (PFactLe (eadd (eaddz O (2)) (escale 8 CNT)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz O (2)) (escale 8 CNT)))]))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))]))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))))))) (PRespell 5 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (1))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x31554] (PCaseReg 10 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))) (PBranch (PFact (KRange (escale 8 CNT) 8 24) (PRun [] (PExt 1 [] (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz O (3)) (escale 8 CNT))) 0 BUFMAX) (PFactLe (eadd (eaddz O (3)) (escale 8 CNT)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz O (3)) (escale 8 CNT)))]))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))]))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))))))))) (PCaseReg 5 2 (PRespell 5 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (1))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x31554] (PCaseReg 10 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))) (PBranch (PFact (KRange (escale 8 CNT) 8 24) (PRun [] (PExt 1 [] (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz O (5)) (escale 8 CNT))) 0 BUFMAX) (PFactLe (eadd (eaddz O (5)) (escale 8 CNT)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz O (5)) (escale 8 CNT)))]))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))))))) (PRespell 5 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (1))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e20] (PBranch (PFactLeR 16 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x31554] (PCaseReg 10 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))) (PBranch (PFact (KRange (escale 8 CNT) 8 24) (PRun [] (PExt 1 [] (PRun [] (PFact (KRange (esub (esub EE B) (eadd (eaddz O (9)) (escale 8 CNT))) 0 BUFMAX) (PFactLe (eadd (eaddz O (9)) (escale 8 CNT)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eadd (eaddz O (9)) (escale 8 CNT)))]))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))]))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))))) (PCaseReg 19 123 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 124 (PRespell 19 (ELit 124) (PRun [] (PVia 5 (JCT 124) 200 (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31d08] (PCaseReg 5 1 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (2)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))))))) (PRespell 5 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (1))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (3)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))))))))) (PCaseReg 5 2 (PRespell 5 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (1))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (5)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))))))) (PRespell 5 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (1))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e20] (PBranch (PFactLeR 16 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (9)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))))) (PRun [0x31610] (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)]))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))))))))) (PCaseReg 19 191 (PCaseReg 19 159 (PCaseReg 19 143 (PCaseReg 19 135 (PCaseReg 19 131 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 132 (PRespell 19 (ELit 132) (PRun [] (PVia 5 (JCT 132) 200 (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31d08] (PCaseReg 5 1 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (2)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))))))) (PRespell 5 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (1))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (3)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))))))))) (PCaseReg 5 2 (PRespell 5 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (1))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (5)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))))))) (PRespell 5 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (1))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e20] (PBranch (PFactLeR 16 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (9)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))))) (PRun [0x31610] (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)]))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))))) (PCaseReg 19 139 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 140 (PRespell 19 (ELit 140) (PRun [] (PVia 5 (JCT 140) 200 (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31d08] (PCaseReg 5 1 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (2)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))))))) (PRespell 5 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (1))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (3)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))))))))) (PCaseReg 5 2 (PRespell 5 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (1))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (5)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))))))) (PRespell 5 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (1))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e20] (PBranch (PFactLeR 16 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (9)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))))) (PRun [0x31610] (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)]))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)]))))))) (PCaseReg 19 151 (PCaseReg 19 147 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 148 (PRespell 19 (ELit 148) (PRun [] (PVia 5 (JCT 148) 200 (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31d08] (PCaseReg 5 1 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (2)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))))))) (PRespell 5 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (1))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (3)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))))))))) (PCaseReg 5 2 (PRespell 5 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (1))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (5)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))))))) (PRespell 5 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (1))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e20] (PBranch (PFactLeR 16 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (9)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))))) (PRun [0x31610] (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)]))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))))) (PCaseReg 19 155 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 156 (PRespell 19 (ELit 156) (PRun [] (PVia 5 (JCT 156) 200 (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31d08] (PCaseReg 5 1 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (2)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))))))) (PRespell 5 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (1))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (3)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))))))))) (PCaseReg 5 2 (PRespell 5 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (1))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (5)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))))))) (PRespell 5 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (1))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e20] (PBranch (PFactLeR 16 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (9)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))))) (PRun [0x31610] (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)]))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))))))) (PCaseReg 19 175 (PCaseReg 19 167 (PCaseReg 19 163 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 164 (PRespell 19 (ELit 164) (PRun [] (PVia 5 (JCT 164) 200 (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31d08] (PCaseReg 5 1 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (2)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))))))) (PRespell 5 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (1))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (3)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))))))))) (PCaseReg 5 2 (PRespell 5 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (1))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (5)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))))))) (PRespell 5 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (1))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e20] (PBranch (PFactLeR 16 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (9)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))))) (PRun [0x31610] (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)]))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))))) (PCaseReg 19 171 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 172 (PRespell 19 (ELit 172) (PRun [] (PVia 5 (JCT 172) 200 (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31d08] (PCaseReg 5 1 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (2)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))))))) (PRespell 5 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (1))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (3)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))))))))) (PCaseReg 5 2 (PRespell 5 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (1))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (5)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))))))) (PRespell 5 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (1))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e20] (PBranch (PFactLeR 16 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (9)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))))) (PRun [0x31610] (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)]))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)]))))))) (PCaseReg 19 183 (PCaseReg 19 179 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 180 (PRespell 19 (ELit 180) (PRun [] (PVia 5 (JCT 180) 200 (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31d08] (PCaseReg 5 1 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (2)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))))))) (PRespell 5 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (1))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (3)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))))))))) (PCaseReg 5 2 (PRespell 5 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (1))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (5)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))))))) (PRespell 5 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (1))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e20] (PBranch (PFactLeR 16 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (9)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))))) (PRun [0x31610] (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)]))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))))) (PCaseReg 19 187 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 188 (PRespell 19 (ELit 188) (PRun [] (PVia 5 (JCT 188) 200 (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31d08] (PCaseReg 5 1 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (2)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))))))) (PRespell 5 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (1))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (3)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))))))))) (PCaseReg 5 2 (PRespell 5 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (1))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (5)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))))))) (PRespell 5 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (1))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e20] (PBranch (PFactLeR 16 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (9)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))))) (PRun [0x31610] (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)]))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)]))))))))) (PCaseReg 19 223 (PCaseReg 19 207 (PCaseReg 19 199 (PCaseReg 19 195 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 196 (PRespell 19 (ELit 196) (PRun [] (PVia 5 (JCT 196) 200 (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31d08] (PCaseReg 5 1 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (2)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))))))) (PRespell 5 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (1))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (3)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))))))))) (PCaseReg 5 2 (PRespell 5 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (1))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (5)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))))))) (PRespell 5 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (1))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e20] (PBranch (PFactLeR 16 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (9)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))))) (PRun [0x31610] (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)]))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))))) (PCaseReg 19 203 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 204 (PRespell 19 (ELit 204) (PRun [] (PVia 5 (JCT 204) 200 (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31d08] (PCaseReg 5 1 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (2)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))))))) (PRespell 5 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (1))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (3)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))))))))) (PCaseReg 5 2 (PRespell 5 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (1))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (5)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))))))) (PRespell 5 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (1))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e20] (PBranch (PFactLeR 16 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (9)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))))) (PRun [0x31610] (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)]))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)]))))))) (PCaseReg 19 215 (PCaseReg 19 211 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 212 (PRespell 19 (ELit 212) (PRun [] (PVia 5 (JCT 212) 200 (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31d08] (PCaseReg 5 1 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (2)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))))))) (PRespell 5 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (1))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (3)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))))))))) (PCaseReg 5 2 (PRespell 5 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (1))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (5)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))))))) (PRespell 5 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (1))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e20] (PBranch (PFactLeR 16 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (9)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))))) (PRun [0x31610] (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)]))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))))) (PCaseReg 19 219 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 220 (PRespell 19 (ELit 220) (PRun [] (PVia 5 (JCT 220) 200 (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31d08] (PCaseReg 5 1 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (2)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))))))) (PRespell 5 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (1))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (3)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))))))))) (PCaseReg 5 2 (PRespell 5 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (1))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (5)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))))))) (PRespell 5 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (1))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e20] (PBranch (PFactLeR 16 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (9)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))))) (PRun [0x31610] (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)]))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))))))) (PCaseReg 19 239 (PCaseReg 19 231 (PCaseReg 19 227 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 228 (PRespell 19 (ELit 228) (PRun [] (PVia 5 (JCT 228) 200 (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31d08] (PCaseReg 5 1 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (2)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))))))) (PRespell 5 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (1))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (3)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))))))))) (PCaseReg 5 2 (PRespell 5 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (1))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (5)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))))))) (PRespell 5 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (1))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e20] (PBranch (PFactLeR 16 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (9)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))))) (PRun [0x31610] (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)]))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))))) (PCaseReg 19 235 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 236 (PRespell 19 (ELit 236) (PRun [] (PVia 5 (JCT 236) 200 (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31d08] (PCaseReg 5 1 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (2)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))))))) (PRespell 5 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (1))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (3)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))))))))) (PCaseReg 5 2 (PRespell 5 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (1))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (5)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))))))) (PRespell 5 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (1))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e20] (PBranch (PFactLeR 16 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (9)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))))) (PRun [0x31610] (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)]))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)]))))))) (PCaseReg 19 247 (PCaseReg 19 243 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 244 (PRespell 19 (ELit 244) (PRun [] (PVia 5 (JCT 244) 200 (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31d08] (PCaseReg 5 1 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (2)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))))))) (PRespell 5 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (1))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (3)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))))))))) (PCaseReg 5 2 (PRespell 5 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (1))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (5)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))))))) (PRespell 5 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (1))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e20] (PBranch (PFactLeR 16 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (9)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))))) (PRun [0x31610] (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)]))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))))) (PCaseReg 19 251 (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))) (PCaseReg 19 252 (PRespell 19 (ELit 252) (PRun [] (PVia 5 (JCT 252) 200 (PCase2 (esub (esub EE B) (eaddz O (1))) 0 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31d08] (PCaseReg 5 1 (PCaseReg 5 0 (PRespell 5 (ELit 0) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (2)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (2))) 0 BUFMAX) (PFactLe (eaddz O (2)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (2)))])))))))))) (PRespell 5 (ELit 1) (PCase2 (esub (esub EE B) (eaddz O (1))) 1 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (3)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (3))) 0 BUFMAX) (PFactLe (eaddz O (3)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (3)))])))))))))))) (PCaseReg 5 2 (PRespell 5 (ELit 2) (PCase2 (esub (esub EE B) (eaddz O (1))) 3 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (5)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (5))) 0 BUFMAX) (PFactLe (eaddz O (5)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (5)))]))))))))))) (PRespell 5 (ELit 3) (PCase2 (esub (esub EE B) (eaddz O (1))) 7 (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (1))) 0 BUFMAX) (PFactLe (eaddz O (1)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (1)))])))) (PRun [0x31e20] (PBranch (PFactLeR 16 0 (ELit 1125899906842627) 1125899906842627 (PRun [0x31e28] (PBump 150 (PFresh 12 0 None (PRun [0x31e44] (PBranch (PRun [0x31e6c] (PCaseReg 12 3 (PRun [0x315c0] (PMergeW 5 [(200%nat, (eaddz O (9)))])) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))) (PRun [] (PFact (KRange (esub (esub EE B) (eaddz O (9))) 0 BUFMAX) (PFactLe (eaddz O (9)) (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, (eaddz O (9)))])))))))))))) (PRun [0x31610] (PCase2 (esub (esub EE B) JO) 0 (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)])))) (PRun [] (PFact (KRange (esub (esub EE B) JO) 0 BUFMAX) (PFactLe JO (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, JO)]))))))))) (PRun [] (PFact (KRange (esub (esub EE B) O) 0 BUFMAX) (PFactLe O (esub EE B) BUFMAX (PHandoffW 0 [(40%nat, O)])))))))))))))
  ).
  split; [vm_compute; reflexivity | vm_cast_no_check (@eq_refl cres (COk (SHole 0)))].
Qed.
Lemma fa_shape : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
End GuFAPlan.
Module GuFAC.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuFA GuFAPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
(* [comment removed for export] *)
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.

Theorem fa_callee : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH ce.
Proof.
  destruct fa_cert as (p & Hg & Hc).
  refine (contract_of_cert USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            ce IT IT_ok LIMIT 0%nat BFUEL FUEL XN _ p _ Hg fa_shape Hc).
  intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
  apply (XNc_sound USEGS IT AUBSAN ubsan_in_hull ubsan_hull_ok IT_ok NXF [] GUBSAN 0 0 fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
            ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
  - intros id ce' H. discriminate H.
  - (apply GC_all; first [assumption | exact IT_ok]).
Qed.
End Contract.
End GuFAC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GuFMS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GuFMSPlan.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuFMS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP. Import GPS.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma fms_cert : exists p : plan, gplan_ok p = true /\
  check USEGS IT AUBSAN NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce ce) 0%nat 600%nat 3000%nat None tin p = COk (SHole 0).
Proof.
  exists (
(PVia 1 J1 64 (PCase2 (esub (esub E I) (ELit 0)) 0 (PRun [] (PHandoff 0)) (PRun [0x2feb0] (PBranch (PCase2 (esub (esub E I) (eaddz (ELit 0) (1))) 0 (PRun [] (PHandoff 0)) (PRun [0x2feec] (PCaseReg 14 1 (PCaseReg 14 0 (PRespell 14 (ELit 0) (PRun [0x30018] (PCaseReg 10 0 (PRun [] (PHandoff 0)) (PRun [0x3004c] (PMergeW 1 [(65%nat, ELit 2)]))))) (PRespell 14 (ELit 1) (PCase2 (esub (esub E I) (eaddz (ELit 0) (1))) 1 (PRun [] (PHandoff 0)) (PRun [0x30018] (PCaseReg 10 0 (PRun [] (PHandoff 0)) (PRun [0x3004c] (PMergeW 1 [(65%nat, ELit 3)]))))))) (PCaseReg 14 2 (PRespell 14 (ELit 2) (PCase2 (esub (esub E I) (eaddz (ELit 0) (1))) 3 (PRun [] (PHandoff 0)) (PRun [0x30018] (PCaseReg 10 0 (PRun [] (PHandoff 0)) (PRun [0x3004c] (PMergeW 1 [(65%nat, ELit 5)])))))) (PRespell 14 (ELit 3) (PCase2 (esub (esub E I) (eaddz (ELit 0) (1))) 7 (PRun [] (PHandoff 0)) (PRun [0x30008] (PBranch (PRun [0x30018] (PCaseReg 10 0 (PRun [] (PHandoff 0)) (PRun [0x3004c] (PMergeW 1 [(65%nat, ELit 9)])))) (PRun [] (PHandoff 0)))))))))) (PRun [] (PHandoff 0))))) (PLoopM 82 (eaddz NV (-1)) [(INV_S, (PVia 2 (J2S false) 130 (PCase2 (esub (esub E I) OJ) 0 (PRun [] (PHandoff 0)) (PRun [0x30068] (PCaseReg 14 1 (PCaseReg 14 0 (PRespell 14 (ELit 0) (PRun [0x30160] (PMergeW 2 [(130%nat, (eaddz OJ (1)))]))) (PRespell 14 (ELit 1) (PCase2 (esub (esub E I) OJ) 1 (PRun [] (PHandoff 0)) (PRun [0x30160] (PMergeW 2 [(130%nat, (eaddz OJ (2)))]))))) (PCaseReg 14 2 (PRespell 14 (ELit 2) (PCase2 (esub (esub E I) OJ) 3 (PRun [] (PHandoff 0)) (PRun [0x30160] (PMergeW 2 [(130%nat, (eaddz OJ (4)))])))) (PRespell 14 (ELit 3) (PCase2 (esub (esub E I) OJ) 7 (PRun [] (PHandoff 0)) (PRun [0x30158] (PBranch (PRun [0x30160] (PMergeW 2 [(130%nat, (eaddz OJ (8)))])) (PRun [] (PHandoff 0)))))))))) (PRun [] (PCaseReg 13 2 (PCaseReg 13 0 (PRespell 13 (ELit 0) (PCase2 (esub (esub E I) O2) 0 (PRun [] (PHandoff 0)) (PRun [0x3016c] (PBranch (PRun [] (PHandoff 0)) (PRun [] (PHandoff 0)))))) (PCaseReg 13 1 (PRespell 13 (ELit 1) (PCase2 (esub (esub E I) O2) 0 (PRun [] (PHandoff 0)) (PRun [0x30180] (PCaseReg 11 100 (PCaseReg 11 97 (PCaseReg 11 96 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))) (PRespell 11 (ELit 97) (PRun [] (PHandoff 0)))) (PCaseReg 11 99 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))) (PRespell 11 (ELit 100) (PRun [] (PRun [0x30588] (PBranch (PCase2 (esub (esub E I) (eaddz O2 (1))) 0 (PRun [] (PHandoff 0)) (PCase2 (esub (esub E I) (eaddz O2 (2))) 0 (PRun [] (PHandoff 0)) (PRun [0x305f4] (PBranch (PCase2 (esub (esub E I) (eaddz O2 (2))) 7 (PRun [] (PHandoff 0)) (PRun [0x3004c] (PFactLe (eaddz O2 (10)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (10))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (10)))]))))) (PRun [0x30680] (PCaseReg 13 0 (PRun [] (PHandoff 0)) (PCaseReg 13 1 (PRun [0x306a8] (PCaseReg 13 6 (PCaseReg 13 2 (PCaseReg 13 0 (PRespell 13 (ELit 0) (PRun [0x3004c] (PFactLe (eaddz O2 (3)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (3))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (3)))]))))) (PCaseReg 13 1 (PRespell 13 (ELit 1) (PRun [0x3004c] (PFactLe (eaddz O2 (3)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (3))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (3)))]))))) (PRespell 13 (ELit 2) (PRun [] (PHandoff 0))))) (PCaseReg 13 4 (PCaseReg 13 3 (PRespell 13 (ELit 3) (PRun [] (PHandoff 0))) (PRespell 13 (ELit 4) (PCase2 (esub (esub E I) (eaddz O2 (2))) 1 (PRun [] (PHandoff 0)) (PRun [0x3004c] (PFactLe (eaddz O2 (4)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (4))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (4)))]))))))) (PCaseReg 13 5 (PRespell 13 (ELit 5) (PCase2 (esub (esub E I) (eaddz O2 (2))) 1 (PRun [] (PHandoff 0)) (PRun [0x3004c] (PFactLe (eaddz O2 (4)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (4))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (4)))])))))) (PRespell 13 (ELit 6) (PRun [] (PHandoff 0)))))) (PCaseReg 13 10 (PCaseReg 13 8 (PCaseReg 13 7 (PRespell 13 (ELit 7) (PCase2 (esub (esub E I) (eaddz O2 (2))) 3 (PRun [] (PHandoff 0)) (PRun [0x3004c] (PFactLe (eaddz O2 (6)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (6))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (6)))])))))) (PRespell 13 (ELit 8) (PCase2 (esub (esub E I) (eaddz O2 (2))) 3 (PRun [] (PHandoff 0)) (PRun [0x3004c] (PFactLe (eaddz O2 (6)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (6))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (6)))]))))))) (PCaseReg 13 9 (PRespell 13 (ELit 9) (PCase2 (esub (esub E I) (eaddz O2 (2))) 3 (PRun [] (PHandoff 0)) (PRun [0x3004c] (PFactLe (eaddz O2 (6)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (6))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (6)))])))))) (PRespell 13 (ELit 10) (PRun [] (PHandoff 0))))) (PCaseReg 13 12 (PCaseReg 13 11 (PRespell 13 (ELit 11) (PCase2 (esub (esub E I) (eaddz O2 (2))) 7 (PRun [] (PHandoff 0)) (PRun [0x3004c] (PFactLe (eaddz O2 (10)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (10))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (10)))])))))) (PRespell 13 (ELit 12) (PCase2 (esub (esub E I) (eaddz O2 (2))) 7 (PRun [] (PHandoff 0)) (PRun [0x3004c] (PFactLe (eaddz O2 (10)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (10))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (10)))]))))))) (PCaseReg 13 13 (PRespell 13 (ELit 13) (PCase2 (esub (esub E I) (eaddz O2 (2))) 7 (PRun [] (PHandoff 0)) (PRun [0x3004c] (PFactLe (eaddz O2 (10)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (10))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (10)))])))))) (PRun [] (PHandoff 0))))))) (PRun [] (PHandoff 0))))))))) (PRun [] (PHandoff 0)))))))) (PCaseReg 11 104 (PCaseReg 11 103 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))) (PRespell 11 (ELit 104) (PRun [] (PHandoff 0)))) (PCaseReg 11 105 (PRespell 11 (ELit 105) (PRun [] (PRun [0x30374] (PBranch (PCase2 (esub (esub E I) (eaddz O2 (1))) 0 (PRun [] (PHandoff 0)) (PCase2 (esub (esub E I) (eaddz O2 (2))) 0 (PRun [] (PHandoff 0)) (PRun [0x303dc] (PBranch (PCase2 (esub (esub E I) (eaddz O2 (2))) 3 (PRun [] (PHandoff 0)) (PRun [0x3004c] (PFactLe (eaddz O2 (6)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (6))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (6)))]))))) (PRun [0x30438] (PCaseReg 10 0 (PRun [] (PHandoff 0)) (PCaseReg 10 1 (PRun [0x30460] (PCaseReg 10 6 (PCaseReg 10 2 (PCaseReg 10 0 (PRespell 10 (ELit 0) (PRun [0x3004c] (PFactLe (eaddz O2 (3)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (3))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (3)))]))))) (PCaseReg 10 1 (PRespell 10 (ELit 1) (PRun [0x3004c] (PFactLe (eaddz O2 (3)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (3))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (3)))]))))) (PRespell 10 (ELit 2) (PRun [] (PHandoff 0))))) (PCaseReg 10 4 (PCaseReg 10 3 (PRespell 10 (ELit 3) (PRun [] (PHandoff 0))) (PRespell 10 (ELit 4) (PCase2 (esub (esub E I) (eaddz O2 (2))) 1 (PRun [] (PHandoff 0)) (PRun [0x3004c] (PFactLe (eaddz O2 (4)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (4))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (4)))]))))))) (PCaseReg 10 5 (PRespell 10 (ELit 5) (PCase2 (esub (esub E I) (eaddz O2 (2))) 1 (PRun [] (PHandoff 0)) (PRun [0x3004c] (PFactLe (eaddz O2 (4)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (4))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (4)))])))))) (PRespell 10 (ELit 6) (PRun [] (PHandoff 0)))))) (PCaseReg 10 10 (PCaseReg 10 8 (PCaseReg 10 7 (PRespell 10 (ELit 7) (PRun [] (PHandoff 0))) (PRespell 10 (ELit 8) (PCase2 (esub (esub E I) (eaddz O2 (2))) 3 (PRun [] (PHandoff 0)) (PRun [0x3004c] (PFactLe (eaddz O2 (6)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (6))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (6)))]))))))) (PCaseReg 10 9 (PRespell 10 (ELit 9) (PCase2 (esub (esub E I) (eaddz O2 (2))) 3 (PRun [] (PHandoff 0)) (PRun [0x3004c] (PFactLe (eaddz O2 (6)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (6))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (6)))])))))) (PRespell 10 (ELit 10) (PRun [] (PHandoff 0))))) (PCaseReg 10 12 (PCaseReg 10 11 (PRespell 10 (ELit 11) (PRun [] (PHandoff 0))) (PRespell 10 (ELit 12) (PCase2 (esub (esub E I) (eaddz O2 (2))) 7 (PRun [] (PHandoff 0)) (PRun [0x3004c] (PFactLe (eaddz O2 (10)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (10))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (10)))]))))))) (PCaseReg 10 13 (PRespell 10 (ELit 13) (PCase2 (esub (esub E I) (eaddz O2 (2))) 7 (PRun [] (PHandoff 0)) (PRun [0x3004c] (PFactLe (eaddz O2 (10)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (10))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (10)))])))))) (PRun [] (PHandoff 0))))))) (PRun [] (PHandoff 0))))))))) (PRun [] (PHandoff 0)))))) (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))))))))) (PRespell 13 (ELit 2) (PCase2 (esub (esub E I) O2) 0 (PRun [] (PHandoff 0)) (PCase2 (esub (esub E I) O2) 1 (PRun [] (PHandoff 0)) (PRun [0x30180] (PCaseReg 11 100 (PCaseReg 11 97 (PCaseReg 11 96 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))) (PRespell 11 (ELit 97) (PRun [] (PHandoff 0)))) (PCaseReg 11 99 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))) (PRespell 11 (ELit 100) (PRun [] (PHandoff 0))))) (PCaseReg 11 104 (PCaseReg 11 103 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))) (PRespell 11 (ELit 104) (PRun [] (PHandoff 0)))) (PCaseReg 11 105 (PRespell 11 (ELit 105) (PRun [] (PHandoff 0))) (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0))))))))))))) (PCaseReg 13 4 (PCaseReg 13 3 (PRespell 13 (ELit 3) (PCase2 (esub (esub E I) O2) 0 (PRun [] (PHandoff 0)) (PCase2 (esub (esub E I) O2) 2 (PRun [] (PHandoff 0)) (PRun [0x30180] (PCaseReg 11 100 (PCaseReg 11 97 (PCaseReg 11 96 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))) (PRespell 11 (ELit 97) (PRun [] (PRun [0x302cc] (PBranch (PRun [0x302d8] (PBranch (PRun [] (PFactLe (eaddz O2 (3)) (esub E I) BUFMAX (PExt 100 [I; (eaddz O2 (3)); ERJ] (PRun [0x301c8] (PBranch (PRun [0x3004c] PNext) (PRun [] (PHandoff 0))))))) (PRun [] (PHandoff 0)))) (PRun [] (PHandoff 0))))))) (PCaseReg 11 99 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))) (PRespell 11 (ELit 100) (PRun [] (PHandoff 0))))) (PCaseReg 11 104 (PCaseReg 11 103 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))) (PRespell 11 (ELit 104) (PRun [] (PHandoff 0)))) (PCaseReg 11 105 (PRespell 11 (ELit 105) (PRun [] (PHandoff 0))) (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0))))))))))) (PRespell 13 (ELit 4) (PCase2 (esub (esub E I) O2) 0 (PRun [] (PHandoff 0)) (PCase2 (esub (esub E I) O2) 3 (PRun [] (PHandoff 0)) (PRun [0x30180] (PCaseReg 11 100 (PCaseReg 11 97 (PCaseReg 11 96 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))) (PRespell 11 (ELit 97) (PRun [] (PHandoff 0)))) (PCaseReg 11 99 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))) (PRespell 11 (ELit 100) (PRun [] (PHandoff 0))))) (PCaseReg 11 104 (PCaseReg 11 103 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))) (PRespell 11 (ELit 104) (PRun [] (PHandoff 0)))) (PCaseReg 11 105 (PRespell 11 (ELit 105) (PRun [] (PHandoff 0))) (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))))))))))) (PCaseReg 13 5 (PRespell 13 (ELit 5) (PCase2 (esub (esub E I) O2) 0 (PRun [] (PHandoff 0)) (PCase2 (esub (esub E I) O2) 4 (PRun [] (PHandoff 0)) (PRun [0x30180] (PCaseReg 11 100 (PCaseReg 11 97 (PCaseReg 11 96 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))) (PRespell 11 (ELit 97) (PRun [] (PHandoff 0)))) (PCaseReg 11 99 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))) (PRespell 11 (ELit 100) (PRun [] (PHandoff 0))))) (PCaseReg 11 104 (PCaseReg 11 103 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))) (PRespell 11 (ELit 104) (PRun [] (PRun [0x30848] (PBranch (PRun [0x30854] (PBranch (PRun [0x30894] (PCase2 (esub (esub E I) (eaddz O2 (5))) 0 (PRun [] (PHandoff 0)) (PRun [0x308a4] (PBranch (PCase2 (esub (esub E I) (eaddz O2 (6))) 0 (PRun [] (PHandoff 0)) (PRun [0x308cc] (PCaseReg 13 1 (PCaseReg 13 0 (PRespell 13 (ELit 0) (PRun [0x309ec] (PBump 200 (PFresh 8 0 None (PRun [0x309f8] (PBranch (PFactLe NNS (esub (esub E I) (eaddz O2 (7))) BUFMAX (PRun [] (PExt2 31 [ELit 0; SVJ] (PRun [] (PCase2 NNS 0 (PExt 1 [] (PRun [0x3004c] (PFactLe (eadd (eaddz O2 (7)) NNS) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eaddz O2 (7)) NNS)) 0 BUFMAX) (PNextW [(83%nat, (eadd (eaddz O2 (7)) NNS))]))))) (PExt 1 [] (PRun [0x3004c] (PFactLe (eadd (eaddz O2 (7)) NNS) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eaddz O2 (7)) NNS)) 0 BUFMAX) (PNextW [(83%nat, (eadd (eaddz O2 (7)) NNS))]))))))) (PRun [] (PExt 1 [] (PRun [0x3004c] (PFactLe (eadd (eaddz O2 (7)) NNS) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eaddz O2 (7)) NNS)) 0 BUFMAX) (PNextW [(83%nat, (eadd (eaddz O2 (7)) NNS))]))))))))) (PRun [] (PHandoff 0)))))))) (PRespell 13 (ELit 1) (PCase2 (esub (esub E I) (eaddz O2 (6))) 1 (PRun [] (PHandoff 0)) (PRun [0x309ec] (PBump 200 (PFresh 8 0 None (PRun [0x309f8] (PBranch (PFactLe NNS (esub (esub E I) (eaddz O2 (8))) BUFMAX (PRun [] (PExt2 31 [ELit 0; SVJ] (PRun [] (PCase2 NNS 0 (PExt 1 [] (PRun [0x3004c] (PFactLe (eadd (eaddz O2 (8)) NNS) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eaddz O2 (8)) NNS)) 0 BUFMAX) (PNextW [(83%nat, (eadd (eaddz O2 (8)) NNS))]))))) (PExt 1 [] (PRun [0x3004c] (PFactLe (eadd (eaddz O2 (8)) NNS) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eaddz O2 (8)) NNS)) 0 BUFMAX) (PNextW [(83%nat, (eadd (eaddz O2 (8)) NNS))]))))))) (PRun [] (PExt 1 [] (PRun [0x3004c] (PFactLe (eadd (eaddz O2 (8)) NNS) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eaddz O2 (8)) NNS)) 0 BUFMAX) (PNextW [(83%nat, (eadd (eaddz O2 (8)) NNS))]))))))))) (PRun [] (PHandoff 0)))))))))) (PCaseReg 13 2 (PRespell 13 (ELit 2) (PCase2 (esub (esub E I) (eaddz O2 (6))) 3 (PRun [] (PHandoff 0)) (PRun [0x309ec] (PBump 200 (PFresh 8 0 None (PRun [0x309f8] (PBranch (PFactLe NNS (esub (esub E I) (eaddz O2 (10))) BUFMAX (PRun [] (PExt2 31 [ELit 0; SVJ] (PRun [] (PCase2 NNS 0 (PExt 1 [] (PRun [0x3004c] (PFactLe (eadd (eaddz O2 (10)) NNS) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eaddz O2 (10)) NNS)) 0 BUFMAX) (PNextW [(83%nat, (eadd (eaddz O2 (10)) NNS))]))))) (PExt 1 [] (PRun [0x3004c] (PFactLe (eadd (eaddz O2 (10)) NNS) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eaddz O2 (10)) NNS)) 0 BUFMAX) (PNextW [(83%nat, (eadd (eaddz O2 (10)) NNS))]))))))) (PRun [] (PExt 1 [] (PRun [0x3004c] (PFactLe (eadd (eaddz O2 (10)) NNS) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eaddz O2 (10)) NNS)) 0 BUFMAX) (PNextW [(83%nat, (eadd (eaddz O2 (10)) NNS))]))))))))) (PRun [] (PHandoff 0))))))))) (PRespell 13 (ELit 3) (PCase2 (esub (esub E I) (eaddz O2 (6))) 7 (PRun [] (PHandoff 0)) (PRun [0x309e4] (PBranch (PRun [0x309ec] (PBump 200 (PFresh 8 0 None (PRun [0x309f8] (PBranch (PFactLe NNS (esub (esub E I) (eaddz O2 (14))) BUFMAX (PRun [] (PExt2 31 [ELit 0; SVJ] (PRun [] (PCase2 NNS 0 (PExt 1 [] (PRun [0x3004c] (PFactLe (eadd (eaddz O2 (14)) NNS) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eaddz O2 (14)) NNS)) 0 BUFMAX) (PNextW [(83%nat, (eadd (eaddz O2 (14)) NNS))]))))) (PExt 1 [] (PRun [0x3004c] (PFactLe (eadd (eaddz O2 (14)) NNS) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eaddz O2 (14)) NNS)) 0 BUFMAX) (PNextW [(83%nat, (eadd (eaddz O2 (14)) NNS))]))))))) (PRun [] (PExt 1 [] (PRun [0x3004c] (PFactLe (eadd (eaddz O2 (14)) NNS) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eaddz O2 (14)) NNS)) 0 BUFMAX) (PNextW [(83%nat, (eadd (eaddz O2 (14)) NNS))]))))))))) (PRun [] (PHandoff 0))))))) (PRun [] (PHandoff 0)))))))))) (PRun [] (PHandoff 0)))))) (PRun [] (PHandoff 0)))) (PRun [] (PHandoff 0))))))) (PCaseReg 11 105 (PRespell 11 (ELit 105) (PRun [] (PHandoff 0))) (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0))))))))))) (PCase2 (esub (esub E I) O2) 0 (PRun [] (PHandoff 0)) (PRun [0x3016c] (PBranch (PRun [] (PHandoff 0)) (PRun [] (PHandoff 0)))))))))), (PVia 2 (J2S true) 130 (PCase2 (esub (esub E I) OJ) 0 (PRun [] (PHandoff 0)) (PRun [0x30068] (PCaseReg 14 1 (PCaseReg 14 0 (PRespell 14 (ELit 0) (PRun [0x30160] (PMergeW 2 [(130%nat, (eaddz OJ (1)))]))) (PRespell 14 (ELit 1) (PCase2 (esub (esub E I) OJ) 1 (PRun [] (PHandoff 0)) (PRun [0x30160] (PMergeW 2 [(130%nat, (eaddz OJ (2)))]))))) (PCaseReg 14 2 (PRespell 14 (ELit 2) (PCase2 (esub (esub E I) OJ) 3 (PRun [] (PHandoff 0)) (PRun [0x30160] (PMergeW 2 [(130%nat, (eaddz OJ (4)))])))) (PRespell 14 (ELit 3) (PCase2 (esub (esub E I) OJ) 7 (PRun [] (PHandoff 0)) (PRun [0x30158] (PBranch (PRun [0x30160] (PMergeW 2 [(130%nat, (eaddz OJ (8)))])) (PRun [] (PHandoff 0)))))))))) (PRun [] (PCaseReg 13 2 (PCaseReg 13 0 (PRespell 13 (ELit 0) (PCase2 (esub (esub E I) O2) 0 (PRun [] (PHandoff 0)) (PRun [0x3016c] (PBranch (PRun [] (PHandoff 0)) (PRun [] (PHandoff 0)))))) (PCaseReg 13 1 (PRespell 13 (ELit 1) (PCase2 (esub (esub E I) O2) 0 (PRun [] (PHandoff 0)) (PRun [0x30180] (PCaseReg 11 100 (PCaseReg 11 97 (PCaseReg 11 96 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))) (PRespell 11 (ELit 97) (PRun [] (PHandoff 0)))) (PCaseReg 11 99 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))) (PRespell 11 (ELit 100) (PRun [] (PRun [0x30588] (PBranch (PCase2 (esub (esub E I) (eaddz O2 (1))) 0 (PRun [] (PHandoff 0)) (PCase2 (esub (esub E I) (eaddz O2 (2))) 0 (PRun [] (PHandoff 0)) (PRun [0x305f4] (PBranch (PCase2 (esub (esub E I) (eaddz O2 (2))) 7 (PRun [] (PHandoff 0)) (PRun [] (PHandoff 0))) (PRun [0x30680] (PCaseReg 13 0 (PRun [] (PHandoff 0)) (PCaseReg 13 1 (PRun [0x306a8] (PCaseReg 13 6 (PCaseReg 13 2 (PCaseReg 13 0 (PRespell 13 (ELit 0) (PRun [] (PHandoff 0))) (PCaseReg 13 1 (PRespell 13 (ELit 1) (PRun [] (PHandoff 0))) (PRespell 13 (ELit 2) (PRun [] (PHandoff 0))))) (PCaseReg 13 4 (PCaseReg 13 3 (PRespell 13 (ELit 3) (PRun [] (PHandoff 0))) (PRespell 13 (ELit 4) (PCase2 (esub (esub E I) (eaddz O2 (2))) 1 (PRun [] (PHandoff 0)) (PRun [] (PHandoff 0))))) (PCaseReg 13 5 (PRespell 13 (ELit 5) (PCase2 (esub (esub E I) (eaddz O2 (2))) 1 (PRun [] (PHandoff 0)) (PRun [] (PHandoff 0)))) (PRespell 13 (ELit 6) (PRun [] (PHandoff 0)))))) (PCaseReg 13 10 (PCaseReg 13 8 (PCaseReg 13 7 (PRespell 13 (ELit 7) (PCase2 (esub (esub E I) (eaddz O2 (2))) 3 (PRun [] (PHandoff 0)) (PRun [] (PHandoff 0)))) (PRespell 13 (ELit 8) (PCase2 (esub (esub E I) (eaddz O2 (2))) 3 (PRun [] (PHandoff 0)) (PRun [] (PHandoff 0))))) (PCaseReg 13 9 (PRespell 13 (ELit 9) (PCase2 (esub (esub E I) (eaddz O2 (2))) 3 (PRun [] (PHandoff 0)) (PRun [] (PHandoff 0)))) (PRespell 13 (ELit 10) (PRun [] (PHandoff 0))))) (PCaseReg 13 12 (PCaseReg 13 11 (PRespell 13 (ELit 11) (PCase2 (esub (esub E I) (eaddz O2 (2))) 7 (PRun [] (PHandoff 0)) (PRun [] (PHandoff 0)))) (PRespell 13 (ELit 12) (PCase2 (esub (esub E I) (eaddz O2 (2))) 7 (PRun [] (PHandoff 0)) (PRun [] (PHandoff 0))))) (PCaseReg 13 13 (PRespell 13 (ELit 13) (PCase2 (esub (esub E I) (eaddz O2 (2))) 7 (PRun [] (PHandoff 0)) (PRun [] (PHandoff 0)))) (PRun [] (PHandoff 0))))))) (PRun [] (PHandoff 0))))))))) (PRun [] (PHandoff 0)))))))) (PCaseReg 11 104 (PCaseReg 11 103 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))) (PRespell 11 (ELit 104) (PRun [] (PHandoff 0)))) (PCaseReg 11 105 (PRespell 11 (ELit 105) (PRun [] (PRun [0x30374] (PBranch (PCase2 (esub (esub E I) (eaddz O2 (1))) 0 (PRun [] (PHandoff 0)) (PCase2 (esub (esub E I) (eaddz O2 (2))) 0 (PRun [] (PHandoff 0)) (PRun [0x303dc] (PBranch (PCase2 (esub (esub E I) (eaddz O2 (2))) 3 (PRun [] (PHandoff 0)) (PRun [] (PHandoff 0))) (PRun [0x30438] (PCaseReg 10 0 (PRun [] (PHandoff 0)) (PCaseReg 10 1 (PRun [0x30460] (PCaseReg 10 6 (PCaseReg 10 2 (PCaseReg 10 0 (PRespell 10 (ELit 0) (PRun [] (PHandoff 0))) (PCaseReg 10 1 (PRespell 10 (ELit 1) (PRun [] (PHandoff 0))) (PRespell 10 (ELit 2) (PRun [] (PHandoff 0))))) (PCaseReg 10 4 (PCaseReg 10 3 (PRespell 10 (ELit 3) (PRun [] (PHandoff 0))) (PRespell 10 (ELit 4) (PCase2 (esub (esub E I) (eaddz O2 (2))) 1 (PRun [] (PHandoff 0)) (PRun [] (PHandoff 0))))) (PCaseReg 10 5 (PRespell 10 (ELit 5) (PCase2 (esub (esub E I) (eaddz O2 (2))) 1 (PRun [] (PHandoff 0)) (PRun [] (PHandoff 0)))) (PRespell 10 (ELit 6) (PRun [] (PHandoff 0)))))) (PCaseReg 10 10 (PCaseReg 10 8 (PCaseReg 10 7 (PRespell 10 (ELit 7) (PRun [] (PHandoff 0))) (PRespell 10 (ELit 8) (PCase2 (esub (esub E I) (eaddz O2 (2))) 3 (PRun [] (PHandoff 0)) (PRun [] (PHandoff 0))))) (PCaseReg 10 9 (PRespell 10 (ELit 9) (PCase2 (esub (esub E I) (eaddz O2 (2))) 3 (PRun [] (PHandoff 0)) (PRun [] (PHandoff 0)))) (PRespell 10 (ELit 10) (PRun [] (PHandoff 0))))) (PCaseReg 10 12 (PCaseReg 10 11 (PRespell 10 (ELit 11) (PRun [] (PHandoff 0))) (PRespell 10 (ELit 12) (PCase2 (esub (esub E I) (eaddz O2 (2))) 7 (PRun [] (PHandoff 0)) (PRun [] (PHandoff 0))))) (PCaseReg 10 13 (PRespell 10 (ELit 13) (PCase2 (esub (esub E I) (eaddz O2 (2))) 7 (PRun [] (PHandoff 0)) (PRun [] (PHandoff 0)))) (PRun [] (PHandoff 0))))))) (PRun [] (PHandoff 0))))))))) (PRun [] (PHandoff 0)))))) (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))))))))) (PRespell 13 (ELit 2) (PCase2 (esub (esub E I) O2) 0 (PRun [] (PHandoff 0)) (PCase2 (esub (esub E I) O2) 1 (PRun [] (PHandoff 0)) (PRun [0x30180] (PCaseReg 11 100 (PCaseReg 11 97 (PCaseReg 11 96 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))) (PRespell 11 (ELit 97) (PRun [] (PHandoff 0)))) (PCaseReg 11 99 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))) (PRespell 11 (ELit 100) (PRun [] (PHandoff 0))))) (PCaseReg 11 104 (PCaseReg 11 103 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))) (PRespell 11 (ELit 104) (PRun [] (PHandoff 0)))) (PCaseReg 11 105 (PRespell 11 (ELit 105) (PRun [] (PHandoff 0))) (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0))))))))))))) (PCaseReg 13 4 (PCaseReg 13 3 (PRespell 13 (ELit 3) (PCase2 (esub (esub E I) O2) 0 (PRun [] (PHandoff 0)) (PCase2 (esub (esub E I) O2) 2 (PRun [] (PHandoff 0)) (PRun [0x30180] (PCaseReg 11 100 (PCaseReg 11 97 (PCaseReg 11 96 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))) (PRespell 11 (ELit 97) (PRun [] (PRun [0x302cc] (PBranch (PRun [0x302d8] (PBranch (PRun [] (PFactLe (eaddz O2 (3)) (esub E I) BUFMAX (PExt 100 [I; (eaddz O2 (3)); ERJ] (PRun [0x301c8] (PBranch (PRun [] (PHandoff 0)) (PRun [] (PHandoff 0))))))) (PRun [] (PHandoff 0)))) (PRun [] (PHandoff 0))))))) (PCaseReg 11 99 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))) (PRespell 11 (ELit 100) (PRun [] (PHandoff 0))))) (PCaseReg 11 104 (PCaseReg 11 103 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))) (PRespell 11 (ELit 104) (PRun [] (PHandoff 0)))) (PCaseReg 11 105 (PRespell 11 (ELit 105) (PRun [] (PHandoff 0))) (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0))))))))))) (PRespell 13 (ELit 4) (PCase2 (esub (esub E I) O2) 0 (PRun [] (PHandoff 0)) (PCase2 (esub (esub E I) O2) 3 (PRun [] (PHandoff 0)) (PRun [0x30180] (PCaseReg 11 100 (PCaseReg 11 97 (PCaseReg 11 96 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))) (PRespell 11 (ELit 97) (PRun [] (PHandoff 0)))) (PCaseReg 11 99 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))) (PRespell 11 (ELit 100) (PRun [] (PHandoff 0))))) (PCaseReg 11 104 (PCaseReg 11 103 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))) (PRespell 11 (ELit 104) (PRun [] (PHandoff 0)))) (PCaseReg 11 105 (PRespell 11 (ELit 105) (PRun [] (PHandoff 0))) (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))))))))))) (PCaseReg 13 5 (PRespell 13 (ELit 5) (PCase2 (esub (esub E I) O2) 0 (PRun [] (PHandoff 0)) (PCase2 (esub (esub E I) O2) 4 (PRun [] (PHandoff 0)) (PRun [0x30180] (PCaseReg 11 100 (PCaseReg 11 97 (PCaseReg 11 96 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))) (PRespell 11 (ELit 97) (PRun [] (PHandoff 0)))) (PCaseReg 11 99 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))) (PRespell 11 (ELit 100) (PRun [] (PHandoff 0))))) (PCaseReg 11 104 (PCaseReg 11 103 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0)))) (PRespell 11 (ELit 104) (PRun [] (PRun [0x30848] (PBranch (PRun [0x30854] (PBranch (PRun [0x30894] (PCase2 (esub (esub E I) (eaddz O2 (5))) 0 (PRun [] (PHandoff 0)) (PRun [0x308a4] (PBranch (PCase2 (esub (esub E I) (eaddz O2 (6))) 0 (PRun [] (PHandoff 0)) (PRun [0x308cc] (PCaseReg 13 1 (PCaseReg 13 0 (PRespell 13 (ELit 0) (PRun [0x309ec] (PBump 200 (PFresh 8 0 None (PRun [0x309f8] (PBranch (PFactLe NNS (esub (esub E I) (eaddz O2 (7))) BUFMAX (PRun [] (PExt2 31 [ELit 0; SVJ] (PRun [] (PCase2 NNS 0 (PExt 1 [] (PRun [] (PHandoff 0))) (PExt 1 [] (PRun [] (PHandoff 0))))) (PRun [] (PExt 1 [] (PRun [] (PHandoff 1))))))) (PRun [] (PHandoff 0)))))))) (PRespell 13 (ELit 1) (PCase2 (esub (esub E I) (eaddz O2 (6))) 1 (PRun [] (PHandoff 0)) (PRun [0x309ec] (PBump 200 (PFresh 8 0 None (PRun [0x309f8] (PBranch (PFactLe NNS (esub (esub E I) (eaddz O2 (8))) BUFMAX (PRun [] (PExt2 31 [ELit 0; SVJ] (PRun [] (PCase2 NNS 0 (PExt 1 [] (PRun [] (PHandoff 0))) (PExt 1 [] (PRun [] (PHandoff 0))))) (PRun [] (PExt 1 [] (PRun [] (PHandoff 1))))))) (PRun [] (PHandoff 0)))))))))) (PCaseReg 13 2 (PRespell 13 (ELit 2) (PCase2 (esub (esub E I) (eaddz O2 (6))) 3 (PRun [] (PHandoff 0)) (PRun [0x309ec] (PBump 200 (PFresh 8 0 None (PRun [0x309f8] (PBranch (PFactLe NNS (esub (esub E I) (eaddz O2 (10))) BUFMAX (PRun [] (PExt2 31 [ELit 0; SVJ] (PRun [] (PCase2 NNS 0 (PExt 1 [] (PRun [] (PHandoff 0))) (PExt 1 [] (PRun [] (PHandoff 0))))) (PRun [] (PExt 1 [] (PRun [] (PHandoff 1))))))) (PRun [] (PHandoff 0))))))))) (PRespell 13 (ELit 3) (PCase2 (esub (esub E I) (eaddz O2 (6))) 7 (PRun [] (PHandoff 0)) (PRun [0x309e4] (PBranch (PRun [0x309ec] (PBump 200 (PFresh 8 0 None (PRun [0x309f8] (PBranch (PFactLe NNS (esub (esub E I) (eaddz O2 (14))) BUFMAX (PRun [] (PExt2 31 [ELit 0; SVJ] (PRun [] (PCase2 NNS 0 (PExt 1 [] (PRun [] (PHandoff 0))) (PExt 1 [] (PRun [] (PHandoff 0))))) (PRun [] (PExt 1 [] (PRun [] (PHandoff 1))))))) (PRun [] (PHandoff 0))))))) (PRun [] (PHandoff 0)))))))))) (PRun [] (PHandoff 0)))))) (PRun [] (PHandoff 0)))) (PRun [] (PHandoff 0))))))) (PCaseReg 11 105 (PRespell 11 (ELit 105) (PRun [] (PHandoff 0))) (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 0))))))))))) (PCase2 (esub (esub E I) O2) 0 (PRun [] (PHandoff 0)) (PRun [0x3016c] (PBranch (PRun [] (PHandoff 0)) (PRun [] (PHandoff 0))))))))))); (INV_L, (PVia 2 (J2L false) 130 (PCase2 (esub (esub E I) OK) 0 (PRun [] (PHandoff 1)) (PRun [0x30068] (PCaseReg 14 1 (PCaseReg 14 0 (PRespell 14 (ELit 0) (PRun [0x30160] (PMergeW 2 [(130%nat, (eaddz OK (1)))]))) (PRespell 14 (ELit 1) (PCase2 (esub (esub E I) OK) 1 (PRun [] (PHandoff 1)) (PRun [0x30160] (PMergeW 2 [(130%nat, (eaddz OK (2)))]))))) (PCaseReg 14 2 (PRespell 14 (ELit 2) (PCase2 (esub (esub E I) OK) 3 (PRun [] (PHandoff 1)) (PRun [0x30160] (PMergeW 2 [(130%nat, (eaddz OK (4)))])))) (PRespell 14 (ELit 3) (PCase2 (esub (esub E I) OK) 7 (PRun [] (PHandoff 1)) (PRun [0x30158] (PBranch (PRun [0x30160] (PMergeW 2 [(130%nat, (eaddz OK (8)))])) (PRun [] (PHandoff 1)))))))))) (PRun [] (PCaseReg 13 2 (PCaseReg 13 0 (PRespell 13 (ELit 0) (PCase2 (esub (esub E I) O2) 0 (PRun [] (PHandoff 1)) (PRun [0x3016c] (PBranch (PRun [] (PHandoff 1)) (PRun [] (PHandoff 1)))))) (PCaseReg 13 1 (PRespell 13 (ELit 1) (PCase2 (esub (esub E I) O2) 0 (PRun [] (PHandoff 1)) (PRun [0x30180] (PCaseReg 11 100 (PCaseReg 11 97 (PCaseReg 11 96 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))) (PRespell 11 (ELit 97) (PRun [] (PHandoff 1)))) (PCaseReg 11 99 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))) (PRespell 11 (ELit 100) (PRun [] (PRun [0x30588] (PBranch (PCase2 (esub (esub E I) (eaddz O2 (1))) 0 (PRun [] (PHandoff 1)) (PCase2 (esub (esub E I) (eaddz O2 (2))) 0 (PRun [] (PHandoff 1)) (PRun [0x305f4] (PBranch (PCase2 (esub (esub E I) (eaddz O2 (2))) 7 (PRun [] (PHandoff 1)) (PRun [0x3004c] (PFactLe (eaddz O2 (10)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (10))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (10)))]))))) (PRun [0x30680] (PCaseReg 13 0 (PRun [] (PHandoff 1)) (PCaseReg 13 1 (PRun [0x306a8] (PCaseReg 13 6 (PCaseReg 13 2 (PCaseReg 13 0 (PRespell 13 (ELit 0) (PRun [0x3004c] (PFactLe (eaddz O2 (3)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (3))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (3)))]))))) (PCaseReg 13 1 (PRespell 13 (ELit 1) (PRun [0x3004c] (PFactLe (eaddz O2 (3)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (3))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (3)))]))))) (PRespell 13 (ELit 2) (PRun [] (PHandoff 1))))) (PCaseReg 13 4 (PCaseReg 13 3 (PRespell 13 (ELit 3) (PRun [] (PHandoff 1))) (PRespell 13 (ELit 4) (PCase2 (esub (esub E I) (eaddz O2 (2))) 1 (PRun [] (PHandoff 1)) (PRun [0x3004c] (PFactLe (eaddz O2 (4)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (4))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (4)))]))))))) (PCaseReg 13 5 (PRespell 13 (ELit 5) (PCase2 (esub (esub E I) (eaddz O2 (2))) 1 (PRun [] (PHandoff 1)) (PRun [0x3004c] (PFactLe (eaddz O2 (4)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (4))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (4)))])))))) (PRespell 13 (ELit 6) (PRun [] (PHandoff 1)))))) (PCaseReg 13 10 (PCaseReg 13 8 (PCaseReg 13 7 (PRespell 13 (ELit 7) (PCase2 (esub (esub E I) (eaddz O2 (2))) 3 (PRun [] (PHandoff 1)) (PRun [0x3004c] (PFactLe (eaddz O2 (6)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (6))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (6)))])))))) (PRespell 13 (ELit 8) (PCase2 (esub (esub E I) (eaddz O2 (2))) 3 (PRun [] (PHandoff 1)) (PRun [0x3004c] (PFactLe (eaddz O2 (6)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (6))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (6)))]))))))) (PCaseReg 13 9 (PRespell 13 (ELit 9) (PCase2 (esub (esub E I) (eaddz O2 (2))) 3 (PRun [] (PHandoff 1)) (PRun [0x3004c] (PFactLe (eaddz O2 (6)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (6))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (6)))])))))) (PRespell 13 (ELit 10) (PRun [] (PHandoff 1))))) (PCaseReg 13 12 (PCaseReg 13 11 (PRespell 13 (ELit 11) (PCase2 (esub (esub E I) (eaddz O2 (2))) 7 (PRun [] (PHandoff 1)) (PRun [0x3004c] (PFactLe (eaddz O2 (10)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (10))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (10)))])))))) (PRespell 13 (ELit 12) (PCase2 (esub (esub E I) (eaddz O2 (2))) 7 (PRun [] (PHandoff 1)) (PRun [0x3004c] (PFactLe (eaddz O2 (10)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (10))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (10)))]))))))) (PCaseReg 13 13 (PRespell 13 (ELit 13) (PCase2 (esub (esub E I) (eaddz O2 (2))) 7 (PRun [] (PHandoff 1)) (PRun [0x3004c] (PFactLe (eaddz O2 (10)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (10))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (10)))])))))) (PRun [] (PHandoff 1))))))) (PRun [] (PHandoff 1))))))))) (PRun [] (PHandoff 1)))))))) (PCaseReg 11 104 (PCaseReg 11 103 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))) (PRespell 11 (ELit 104) (PRun [] (PHandoff 1)))) (PCaseReg 11 105 (PRespell 11 (ELit 105) (PRun [] (PRun [0x30374] (PBranch (PCase2 (esub (esub E I) (eaddz O2 (1))) 0 (PRun [] (PHandoff 1)) (PCase2 (esub (esub E I) (eaddz O2 (2))) 0 (PRun [] (PHandoff 1)) (PRun [0x303dc] (PBranch (PCase2 (esub (esub E I) (eaddz O2 (2))) 3 (PRun [] (PHandoff 1)) (PRun [0x3004c] (PFactLe (eaddz O2 (6)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (6))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (6)))]))))) (PRun [0x30438] (PCaseReg 10 0 (PRun [] (PHandoff 1)) (PCaseReg 10 1 (PRun [0x30460] (PCaseReg 10 6 (PCaseReg 10 2 (PCaseReg 10 0 (PRespell 10 (ELit 0) (PRun [0x3004c] (PFactLe (eaddz O2 (3)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (3))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (3)))]))))) (PCaseReg 10 1 (PRespell 10 (ELit 1) (PRun [0x3004c] (PFactLe (eaddz O2 (3)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (3))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (3)))]))))) (PRespell 10 (ELit 2) (PRun [] (PHandoff 1))))) (PCaseReg 10 4 (PCaseReg 10 3 (PRespell 10 (ELit 3) (PRun [] (PHandoff 1))) (PRespell 10 (ELit 4) (PCase2 (esub (esub E I) (eaddz O2 (2))) 1 (PRun [] (PHandoff 1)) (PRun [0x3004c] (PFactLe (eaddz O2 (4)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (4))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (4)))]))))))) (PCaseReg 10 5 (PRespell 10 (ELit 5) (PCase2 (esub (esub E I) (eaddz O2 (2))) 1 (PRun [] (PHandoff 1)) (PRun [0x3004c] (PFactLe (eaddz O2 (4)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (4))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (4)))])))))) (PRespell 10 (ELit 6) (PRun [] (PHandoff 1)))))) (PCaseReg 10 10 (PCaseReg 10 8 (PCaseReg 10 7 (PRespell 10 (ELit 7) (PRun [] (PHandoff 1))) (PRespell 10 (ELit 8) (PCase2 (esub (esub E I) (eaddz O2 (2))) 3 (PRun [] (PHandoff 1)) (PRun [0x3004c] (PFactLe (eaddz O2 (6)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (6))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (6)))]))))))) (PCaseReg 10 9 (PRespell 10 (ELit 9) (PCase2 (esub (esub E I) (eaddz O2 (2))) 3 (PRun [] (PHandoff 1)) (PRun [0x3004c] (PFactLe (eaddz O2 (6)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (6))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (6)))])))))) (PRespell 10 (ELit 10) (PRun [] (PHandoff 1))))) (PCaseReg 10 12 (PCaseReg 10 11 (PRespell 10 (ELit 11) (PRun [] (PHandoff 1))) (PRespell 10 (ELit 12) (PCase2 (esub (esub E I) (eaddz O2 (2))) 7 (PRun [] (PHandoff 1)) (PRun [0x3004c] (PFactLe (eaddz O2 (10)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (10))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (10)))]))))))) (PCaseReg 10 13 (PRespell 10 (ELit 13) (PCase2 (esub (esub E I) (eaddz O2 (2))) 7 (PRun [] (PHandoff 1)) (PRun [0x3004c] (PFactLe (eaddz O2 (10)) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eaddz O2 (10))) 0 BUFMAX) (PNextW [(83%nat, (eaddz O2 (10)))])))))) (PRun [] (PHandoff 1))))))) (PRun [] (PHandoff 1))))))))) (PRun [] (PHandoff 1)))))) (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))))))))) (PRespell 13 (ELit 2) (PCase2 (esub (esub E I) O2) 0 (PRun [] (PHandoff 1)) (PCase2 (esub (esub E I) O2) 1 (PRun [] (PHandoff 1)) (PRun [0x30180] (PCaseReg 11 100 (PCaseReg 11 97 (PCaseReg 11 96 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))) (PRespell 11 (ELit 97) (PRun [] (PHandoff 1)))) (PCaseReg 11 99 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))) (PRespell 11 (ELit 100) (PRun [] (PHandoff 1))))) (PCaseReg 11 104 (PCaseReg 11 103 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))) (PRespell 11 (ELit 104) (PRun [] (PHandoff 1)))) (PCaseReg 11 105 (PRespell 11 (ELit 105) (PRun [] (PHandoff 1))) (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1))))))))))))) (PCaseReg 13 4 (PCaseReg 13 3 (PRespell 13 (ELit 3) (PCase2 (esub (esub E I) O2) 0 (PRun [] (PHandoff 1)) (PCase2 (esub (esub E I) O2) 2 (PRun [] (PHandoff 1)) (PRun [0x30180] (PCaseReg 11 100 (PCaseReg 11 97 (PCaseReg 11 96 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))) (PRespell 11 (ELit 97) (PRun [] (PRun [0x302cc] (PBranch (PRun [0x302d8] (PBranch (PRun [] (PFactLe (eaddz O2 (3)) (esub E I) BUFMAX (PExt 100 [I; (eaddz O2 (3)); ERK] (PRun [0x301c8] (PBranch (PRun [0x3004c] PNext) (PRun [] (PHandoff 1))))))) (PRun [] (PHandoff 1)))) (PRun [] (PHandoff 1))))))) (PCaseReg 11 99 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))) (PRespell 11 (ELit 100) (PRun [] (PHandoff 1))))) (PCaseReg 11 104 (PCaseReg 11 103 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))) (PRespell 11 (ELit 104) (PRun [] (PHandoff 1)))) (PCaseReg 11 105 (PRespell 11 (ELit 105) (PRun [] (PHandoff 1))) (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1))))))))))) (PRespell 13 (ELit 4) (PCase2 (esub (esub E I) O2) 0 (PRun [] (PHandoff 1)) (PCase2 (esub (esub E I) O2) 3 (PRun [] (PHandoff 1)) (PRun [0x30180] (PCaseReg 11 100 (PCaseReg 11 97 (PCaseReg 11 96 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))) (PRespell 11 (ELit 97) (PRun [] (PHandoff 1)))) (PCaseReg 11 99 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))) (PRespell 11 (ELit 100) (PRun [] (PHandoff 1))))) (PCaseReg 11 104 (PCaseReg 11 103 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))) (PRespell 11 (ELit 104) (PRun [] (PHandoff 1)))) (PCaseReg 11 105 (PRespell 11 (ELit 105) (PRun [] (PHandoff 1))) (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))))))))))) (PCaseReg 13 5 (PRespell 13 (ELit 5) (PCase2 (esub (esub E I) O2) 0 (PRun [] (PHandoff 1)) (PCase2 (esub (esub E I) O2) 4 (PRun [] (PHandoff 1)) (PRun [0x30180] (PCaseReg 11 100 (PCaseReg 11 97 (PCaseReg 11 96 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))) (PRespell 11 (ELit 97) (PRun [] (PHandoff 1)))) (PCaseReg 11 99 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))) (PRespell 11 (ELit 100) (PRun [] (PHandoff 1))))) (PCaseReg 11 104 (PCaseReg 11 103 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))) (PRespell 11 (ELit 104) (PRun [] (PRun [0x30848] (PBranch (PRun [0x30854] (PBranch (PRun [0x30894] (PCase2 (esub (esub E I) (eaddz O2 (5))) 0 (PRun [] (PHandoff 1)) (PRun [0x308a4] (PBranch (PCase2 (esub (esub E I) (eaddz O2 (6))) 0 (PRun [] (PHandoff 1)) (PRun [0x308cc] (PCaseReg 13 1 (PCaseReg 13 0 (PRespell 13 (ELit 0) (PRun [0x309ec] (PBump 400 (PFresh 8 0 None (PRun [0x309f8] (PBranch (PFactLe NNL (esub (esub E I) (eaddz O2 (7))) BUFMAX (PRun [] (PExt2 31 [ELit 1; DK; AK; SK] (PRun [] (PCase2 NNL 0 (PExt 1 [] (PRun [0x3004c] (PFactLe (eadd (eaddz O2 (7)) NNL) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eaddz O2 (7)) NNL)) 0 BUFMAX) (PNextW [(83%nat, (eadd (eaddz O2 (7)) NNL))]))))) (PExt 1 [] (PRun [0x3004c] (PFactLe (eadd (eaddz O2 (7)) NNL) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eaddz O2 (7)) NNL)) 0 BUFMAX) (PNextW [(83%nat, (eadd (eaddz O2 (7)) NNL))]))))))) (PFactVia NNL (esub NNL (escale 8 AK)) 1 (2^28) (PRun [] (PExt 1 [] (PRun [0x3004c] (PFactLe (eadd (eaddz O2 (7)) NNL) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eaddz O2 (7)) NNL)) 0 BUFMAX) (PNextW [(83%nat, (eadd (eaddz O2 (7)) NNL))])))))))))) (PRun [] (PHandoff 1)))))))) (PRespell 13 (ELit 1) (PCase2 (esub (esub E I) (eaddz O2 (6))) 1 (PRun [] (PHandoff 1)) (PRun [0x309ec] (PBump 400 (PFresh 8 0 None (PRun [0x309f8] (PBranch (PFactLe NNL (esub (esub E I) (eaddz O2 (8))) BUFMAX (PRun [] (PExt2 31 [ELit 1; DK; AK; SK] (PRun [] (PCase2 NNL 0 (PExt 1 [] (PRun [0x3004c] (PFactLe (eadd (eaddz O2 (8)) NNL) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eaddz O2 (8)) NNL)) 0 BUFMAX) (PNextW [(83%nat, (eadd (eaddz O2 (8)) NNL))]))))) (PExt 1 [] (PRun [0x3004c] (PFactLe (eadd (eaddz O2 (8)) NNL) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eaddz O2 (8)) NNL)) 0 BUFMAX) (PNextW [(83%nat, (eadd (eaddz O2 (8)) NNL))]))))))) (PFactVia NNL (esub NNL (escale 8 AK)) 1 (2^28) (PRun [] (PExt 1 [] (PRun [0x3004c] (PFactLe (eadd (eaddz O2 (8)) NNL) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eaddz O2 (8)) NNL)) 0 BUFMAX) (PNextW [(83%nat, (eadd (eaddz O2 (8)) NNL))])))))))))) (PRun [] (PHandoff 1)))))))))) (PCaseReg 13 2 (PRespell 13 (ELit 2) (PCase2 (esub (esub E I) (eaddz O2 (6))) 3 (PRun [] (PHandoff 1)) (PRun [0x309ec] (PBump 400 (PFresh 8 0 None (PRun [0x309f8] (PBranch (PFactLe NNL (esub (esub E I) (eaddz O2 (10))) BUFMAX (PRun [] (PExt2 31 [ELit 1; DK; AK; SK] (PRun [] (PCase2 NNL 0 (PExt 1 [] (PRun [0x3004c] (PFactLe (eadd (eaddz O2 (10)) NNL) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eaddz O2 (10)) NNL)) 0 BUFMAX) (PNextW [(83%nat, (eadd (eaddz O2 (10)) NNL))]))))) (PExt 1 [] (PRun [0x3004c] (PFactLe (eadd (eaddz O2 (10)) NNL) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eaddz O2 (10)) NNL)) 0 BUFMAX) (PNextW [(83%nat, (eadd (eaddz O2 (10)) NNL))]))))))) (PFactVia NNL (esub NNL (escale 8 AK)) 1 (2^28) (PRun [] (PExt 1 [] (PRun [0x3004c] (PFactLe (eadd (eaddz O2 (10)) NNL) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eaddz O2 (10)) NNL)) 0 BUFMAX) (PNextW [(83%nat, (eadd (eaddz O2 (10)) NNL))])))))))))) (PRun [] (PHandoff 1))))))))) (PRespell 13 (ELit 3) (PCase2 (esub (esub E I) (eaddz O2 (6))) 7 (PRun [] (PHandoff 1)) (PRun [0x309e4] (PBranch (PRun [0x309ec] (PBump 400 (PFresh 8 0 None (PRun [0x309f8] (PBranch (PFactLe NNL (esub (esub E I) (eaddz O2 (14))) BUFMAX (PRun [] (PExt2 31 [ELit 1; DK; AK; SK] (PRun [] (PCase2 NNL 0 (PExt 1 [] (PRun [0x3004c] (PFactLe (eadd (eaddz O2 (14)) NNL) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eaddz O2 (14)) NNL)) 0 BUFMAX) (PNextW [(83%nat, (eadd (eaddz O2 (14)) NNL))]))))) (PExt 1 [] (PRun [0x3004c] (PFactLe (eadd (eaddz O2 (14)) NNL) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eaddz O2 (14)) NNL)) 0 BUFMAX) (PNextW [(83%nat, (eadd (eaddz O2 (14)) NNL))]))))))) (PFactVia NNL (esub NNL (escale 8 AK)) 1 (2^28) (PRun [] (PExt 1 [] (PRun [0x3004c] (PFactLe (eadd (eaddz O2 (14)) NNL) (esub E I) BUFMAX (PFact (KRange (esub (esub E I) (eadd (eaddz O2 (14)) NNL)) 0 BUFMAX) (PNextW [(83%nat, (eadd (eaddz O2 (14)) NNL))])))))))))) (PRun [] (PHandoff 1))))))) (PRun [] (PHandoff 1)))))))))) (PRun [] (PHandoff 1)))))) (PRun [] (PHandoff 1)))) (PRun [] (PHandoff 1))))))) (PCaseReg 11 105 (PRespell 11 (ELit 105) (PRun [] (PHandoff 1))) (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1))))))))))) (PCase2 (esub (esub E I) O2) 0 (PRun [] (PHandoff 1)) (PRun [0x3016c] (PBranch (PRun [] (PHandoff 1)) (PRun [] (PHandoff 1)))))))))), (PVia 2 (J2L true) 130 (PCase2 (esub (esub E I) OK) 0 (PRun [] (PHandoff 1)) (PRun [0x30068] (PCaseReg 14 1 (PCaseReg 14 0 (PRespell 14 (ELit 0) (PRun [0x30160] (PMergeW 2 [(130%nat, (eaddz OK (1)))]))) (PRespell 14 (ELit 1) (PCase2 (esub (esub E I) OK) 1 (PRun [] (PHandoff 1)) (PRun [0x30160] (PMergeW 2 [(130%nat, (eaddz OK (2)))]))))) (PCaseReg 14 2 (PRespell 14 (ELit 2) (PCase2 (esub (esub E I) OK) 3 (PRun [] (PHandoff 1)) (PRun [0x30160] (PMergeW 2 [(130%nat, (eaddz OK (4)))])))) (PRespell 14 (ELit 3) (PCase2 (esub (esub E I) OK) 7 (PRun [] (PHandoff 1)) (PRun [0x30158] (PBranch (PRun [0x30160] (PMergeW 2 [(130%nat, (eaddz OK (8)))])) (PRun [] (PHandoff 1)))))))))) (PRun [] (PCaseReg 13 2 (PCaseReg 13 0 (PRespell 13 (ELit 0) (PCase2 (esub (esub E I) O2) 0 (PRun [] (PHandoff 1)) (PRun [0x3016c] (PBranch (PRun [] (PHandoff 1)) (PRun [] (PHandoff 1)))))) (PCaseReg 13 1 (PRespell 13 (ELit 1) (PCase2 (esub (esub E I) O2) 0 (PRun [] (PHandoff 1)) (PRun [0x30180] (PCaseReg 11 100 (PCaseReg 11 97 (PCaseReg 11 96 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))) (PRespell 11 (ELit 97) (PRun [] (PHandoff 1)))) (PCaseReg 11 99 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))) (PRespell 11 (ELit 100) (PRun [] (PRun [0x30588] (PBranch (PCase2 (esub (esub E I) (eaddz O2 (1))) 0 (PRun [] (PHandoff 1)) (PCase2 (esub (esub E I) (eaddz O2 (2))) 0 (PRun [] (PHandoff 1)) (PRun [0x305f4] (PBranch (PCase2 (esub (esub E I) (eaddz O2 (2))) 7 (PRun [] (PHandoff 1)) (PRun [] (PHandoff 1))) (PRun [0x30680] (PCaseReg 13 0 (PRun [] (PHandoff 1)) (PCaseReg 13 1 (PRun [0x306a8] (PCaseReg 13 6 (PCaseReg 13 2 (PCaseReg 13 0 (PRespell 13 (ELit 0) (PRun [] (PHandoff 1))) (PCaseReg 13 1 (PRespell 13 (ELit 1) (PRun [] (PHandoff 1))) (PRespell 13 (ELit 2) (PRun [] (PHandoff 1))))) (PCaseReg 13 4 (PCaseReg 13 3 (PRespell 13 (ELit 3) (PRun [] (PHandoff 1))) (PRespell 13 (ELit 4) (PCase2 (esub (esub E I) (eaddz O2 (2))) 1 (PRun [] (PHandoff 1)) (PRun [] (PHandoff 1))))) (PCaseReg 13 5 (PRespell 13 (ELit 5) (PCase2 (esub (esub E I) (eaddz O2 (2))) 1 (PRun [] (PHandoff 1)) (PRun [] (PHandoff 1)))) (PRespell 13 (ELit 6) (PRun [] (PHandoff 1)))))) (PCaseReg 13 10 (PCaseReg 13 8 (PCaseReg 13 7 (PRespell 13 (ELit 7) (PCase2 (esub (esub E I) (eaddz O2 (2))) 3 (PRun [] (PHandoff 1)) (PRun [] (PHandoff 1)))) (PRespell 13 (ELit 8) (PCase2 (esub (esub E I) (eaddz O2 (2))) 3 (PRun [] (PHandoff 1)) (PRun [] (PHandoff 1))))) (PCaseReg 13 9 (PRespell 13 (ELit 9) (PCase2 (esub (esub E I) (eaddz O2 (2))) 3 (PRun [] (PHandoff 1)) (PRun [] (PHandoff 1)))) (PRespell 13 (ELit 10) (PRun [] (PHandoff 1))))) (PCaseReg 13 12 (PCaseReg 13 11 (PRespell 13 (ELit 11) (PCase2 (esub (esub E I) (eaddz O2 (2))) 7 (PRun [] (PHandoff 1)) (PRun [] (PHandoff 1)))) (PRespell 13 (ELit 12) (PCase2 (esub (esub E I) (eaddz O2 (2))) 7 (PRun [] (PHandoff 1)) (PRun [] (PHandoff 1))))) (PCaseReg 13 13 (PRespell 13 (ELit 13) (PCase2 (esub (esub E I) (eaddz O2 (2))) 7 (PRun [] (PHandoff 1)) (PRun [] (PHandoff 1)))) (PRun [] (PHandoff 1))))))) (PRun [] (PHandoff 1))))))))) (PRun [] (PHandoff 1)))))))) (PCaseReg 11 104 (PCaseReg 11 103 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))) (PRespell 11 (ELit 104) (PRun [] (PHandoff 1)))) (PCaseReg 11 105 (PRespell 11 (ELit 105) (PRun [] (PRun [0x30374] (PBranch (PCase2 (esub (esub E I) (eaddz O2 (1))) 0 (PRun [] (PHandoff 1)) (PCase2 (esub (esub E I) (eaddz O2 (2))) 0 (PRun [] (PHandoff 1)) (PRun [0x303dc] (PBranch (PCase2 (esub (esub E I) (eaddz O2 (2))) 3 (PRun [] (PHandoff 1)) (PRun [] (PHandoff 1))) (PRun [0x30438] (PCaseReg 10 0 (PRun [] (PHandoff 1)) (PCaseReg 10 1 (PRun [0x30460] (PCaseReg 10 6 (PCaseReg 10 2 (PCaseReg 10 0 (PRespell 10 (ELit 0) (PRun [] (PHandoff 1))) (PCaseReg 10 1 (PRespell 10 (ELit 1) (PRun [] (PHandoff 1))) (PRespell 10 (ELit 2) (PRun [] (PHandoff 1))))) (PCaseReg 10 4 (PCaseReg 10 3 (PRespell 10 (ELit 3) (PRun [] (PHandoff 1))) (PRespell 10 (ELit 4) (PCase2 (esub (esub E I) (eaddz O2 (2))) 1 (PRun [] (PHandoff 1)) (PRun [] (PHandoff 1))))) (PCaseReg 10 5 (PRespell 10 (ELit 5) (PCase2 (esub (esub E I) (eaddz O2 (2))) 1 (PRun [] (PHandoff 1)) (PRun [] (PHandoff 1)))) (PRespell 10 (ELit 6) (PRun [] (PHandoff 1)))))) (PCaseReg 10 10 (PCaseReg 10 8 (PCaseReg 10 7 (PRespell 10 (ELit 7) (PRun [] (PHandoff 1))) (PRespell 10 (ELit 8) (PCase2 (esub (esub E I) (eaddz O2 (2))) 3 (PRun [] (PHandoff 1)) (PRun [] (PHandoff 1))))) (PCaseReg 10 9 (PRespell 10 (ELit 9) (PCase2 (esub (esub E I) (eaddz O2 (2))) 3 (PRun [] (PHandoff 1)) (PRun [] (PHandoff 1)))) (PRespell 10 (ELit 10) (PRun [] (PHandoff 1))))) (PCaseReg 10 12 (PCaseReg 10 11 (PRespell 10 (ELit 11) (PRun [] (PHandoff 1))) (PRespell 10 (ELit 12) (PCase2 (esub (esub E I) (eaddz O2 (2))) 7 (PRun [] (PHandoff 1)) (PRun [] (PHandoff 1))))) (PCaseReg 10 13 (PRespell 10 (ELit 13) (PCase2 (esub (esub E I) (eaddz O2 (2))) 7 (PRun [] (PHandoff 1)) (PRun [] (PHandoff 1)))) (PRun [] (PHandoff 1))))))) (PRun [] (PHandoff 1))))))))) (PRun [] (PHandoff 1)))))) (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))))))))) (PRespell 13 (ELit 2) (PCase2 (esub (esub E I) O2) 0 (PRun [] (PHandoff 1)) (PCase2 (esub (esub E I) O2) 1 (PRun [] (PHandoff 1)) (PRun [0x30180] (PCaseReg 11 100 (PCaseReg 11 97 (PCaseReg 11 96 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))) (PRespell 11 (ELit 97) (PRun [] (PHandoff 1)))) (PCaseReg 11 99 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))) (PRespell 11 (ELit 100) (PRun [] (PHandoff 1))))) (PCaseReg 11 104 (PCaseReg 11 103 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))) (PRespell 11 (ELit 104) (PRun [] (PHandoff 1)))) (PCaseReg 11 105 (PRespell 11 (ELit 105) (PRun [] (PHandoff 1))) (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1))))))))))))) (PCaseReg 13 4 (PCaseReg 13 3 (PRespell 13 (ELit 3) (PCase2 (esub (esub E I) O2) 0 (PRun [] (PHandoff 1)) (PCase2 (esub (esub E I) O2) 2 (PRun [] (PHandoff 1)) (PRun [0x30180] (PCaseReg 11 100 (PCaseReg 11 97 (PCaseReg 11 96 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))) (PRespell 11 (ELit 97) (PRun [] (PRun [0x302cc] (PBranch (PRun [0x302d8] (PBranch (PRun [] (PFactLe (eaddz O2 (3)) (esub E I) BUFMAX (PExt 100 [I; (eaddz O2 (3)); ERK] (PRun [0x301c8] (PBranch (PRun [] (PHandoff 1)) (PRun [] (PHandoff 1))))))) (PRun [] (PHandoff 1)))) (PRun [] (PHandoff 1))))))) (PCaseReg 11 99 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))) (PRespell 11 (ELit 100) (PRun [] (PHandoff 1))))) (PCaseReg 11 104 (PCaseReg 11 103 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))) (PRespell 11 (ELit 104) (PRun [] (PHandoff 1)))) (PCaseReg 11 105 (PRespell 11 (ELit 105) (PRun [] (PHandoff 1))) (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1))))))))))) (PRespell 13 (ELit 4) (PCase2 (esub (esub E I) O2) 0 (PRun [] (PHandoff 1)) (PCase2 (esub (esub E I) O2) 3 (PRun [] (PHandoff 1)) (PRun [0x30180] (PCaseReg 11 100 (PCaseReg 11 97 (PCaseReg 11 96 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))) (PRespell 11 (ELit 97) (PRun [] (PHandoff 1)))) (PCaseReg 11 99 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))) (PRespell 11 (ELit 100) (PRun [] (PHandoff 1))))) (PCaseReg 11 104 (PCaseReg 11 103 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))) (PRespell 11 (ELit 104) (PRun [] (PHandoff 1)))) (PCaseReg 11 105 (PRespell 11 (ELit 105) (PRun [] (PHandoff 1))) (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))))))))))) (PCaseReg 13 5 (PRespell 13 (ELit 5) (PCase2 (esub (esub E I) O2) 0 (PRun [] (PHandoff 1)) (PCase2 (esub (esub E I) O2) 4 (PRun [] (PHandoff 1)) (PRun [0x30180] (PCaseReg 11 100 (PCaseReg 11 97 (PCaseReg 11 96 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))) (PRespell 11 (ELit 97) (PRun [] (PHandoff 1)))) (PCaseReg 11 99 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))) (PRespell 11 (ELit 100) (PRun [] (PHandoff 1))))) (PCaseReg 11 104 (PCaseReg 11 103 (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1)))) (PRespell 11 (ELit 104) (PRun [] (PRun [0x30848] (PBranch (PRun [0x30854] (PBranch (PRun [0x30894] (PCase2 (esub (esub E I) (eaddz O2 (5))) 0 (PRun [] (PHandoff 1)) (PRun [0x308a4] (PBranch (PCase2 (esub (esub E I) (eaddz O2 (6))) 0 (PRun [] (PHandoff 1)) (PRun [0x308cc] (PCaseReg 13 1 (PCaseReg 13 0 (PRespell 13 (ELit 0) (PRun [0x309ec] (PBump 400 (PFresh 8 0 None (PRun [0x309f8] (PBranch (PFactLe NNL (esub (esub E I) (eaddz O2 (7))) BUFMAX (PRun [] (PExt2 31 [ELit 1; DK; AK; SK] (PRun [] (PCase2 NNL 0 (PExt 1 [] (PRun [] (PHandoff 1))) (PExt 1 [] (PRun [] (PHandoff 1))))) (PFactVia NNL (esub NNL (escale 8 AK)) 1 (2^28) (PRun [] (PExt 1 [] (PRun [] (PHandoff 1)))))))) (PRun [] (PHandoff 1)))))))) (PRespell 13 (ELit 1) (PCase2 (esub (esub E I) (eaddz O2 (6))) 1 (PRun [] (PHandoff 1)) (PRun [0x309ec] (PBump 400 (PFresh 8 0 None (PRun [0x309f8] (PBranch (PFactLe NNL (esub (esub E I) (eaddz O2 (8))) BUFMAX (PRun [] (PExt2 31 [ELit 1; DK; AK; SK] (PRun [] (PCase2 NNL 0 (PExt 1 [] (PRun [] (PHandoff 1))) (PExt 1 [] (PRun [] (PHandoff 1))))) (PFactVia NNL (esub NNL (escale 8 AK)) 1 (2^28) (PRun [] (PExt 1 [] (PRun [] (PHandoff 1)))))))) (PRun [] (PHandoff 1)))))))))) (PCaseReg 13 2 (PRespell 13 (ELit 2) (PCase2 (esub (esub E I) (eaddz O2 (6))) 3 (PRun [] (PHandoff 1)) (PRun [0x309ec] (PBump 400 (PFresh 8 0 None (PRun [0x309f8] (PBranch (PFactLe NNL (esub (esub E I) (eaddz O2 (10))) BUFMAX (PRun [] (PExt2 31 [ELit 1; DK; AK; SK] (PRun [] (PCase2 NNL 0 (PExt 1 [] (PRun [] (PHandoff 1))) (PExt 1 [] (PRun [] (PHandoff 1))))) (PFactVia NNL (esub NNL (escale 8 AK)) 1 (2^28) (PRun [] (PExt 1 [] (PRun [] (PHandoff 1)))))))) (PRun [] (PHandoff 1))))))))) (PRespell 13 (ELit 3) (PCase2 (esub (esub E I) (eaddz O2 (6))) 7 (PRun [] (PHandoff 1)) (PRun [0x309e4] (PBranch (PRun [0x309ec] (PBump 400 (PFresh 8 0 None (PRun [0x309f8] (PBranch (PFactLe NNL (esub (esub E I) (eaddz O2 (14))) BUFMAX (PRun [] (PExt2 31 [ELit 1; DK; AK; SK] (PRun [] (PCase2 NNL 0 (PExt 1 [] (PRun [] (PHandoff 1))) (PExt 1 [] (PRun [] (PHandoff 1))))) (PFactVia NNL (esub NNL (escale 8 AK)) 1 (2^28) (PRun [] (PExt 1 [] (PRun [] (PHandoff 1)))))))) (PRun [] (PHandoff 1))))))) (PRun [] (PHandoff 1)))))))))) (PRun [] (PHandoff 1)))))) (PRun [] (PHandoff 1)))) (PRun [] (PHandoff 1))))))) (PCaseReg 11 105 (PRespell 11 (ELit 105) (PRun [] (PHandoff 1))) (PRun [0x30184] (PExt 42 [] (PRun [] (PHandoff 1))))))))))) (PCase2 (esub (esub E I) O2) 0 (PRun [] (PHandoff 1)) (PRun [0x3016c] (PBranch (PRun [] (PHandoff 1)) (PRun [] (PHandoff 1)))))))))))] []))
  ).
  split; [vm_compute; reflexivity | vm_cast_no_check (@eq_refl cres (COk (SHole 0)))].
Qed.
Lemma fms_shape : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
End GuFMSPlan.
Module GuFMSC.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuFA GuFAC OSSVerify.Proofs.glaze.binary_reflection.lib.GuFMS GuFMSPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
(* [comment removed for export] *)
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.

Lemma CT_sound : forall id ce', CT id = Some ce' -> callee_contract USEGS [] GUBSAN fx_ok RZ AINVH ce'.
Proof.
  intros id ce' H. unfold CT in H. destruct (Nat.eqb id 100); [|discriminate H]. injection H as <-.
  exact (fa_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm GC_all).
Qed.

Theorem fms_callee : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH ce.
Proof.
  destruct fms_cert as (p & Hg & Hc).
  refine (contract_of_cert_xb USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            ce IT IT_ok LIMIT 0%nat 600%nat 3000%nat XN _ XB _ p _ Hg fms_shape Hc).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS IT AUBSAN ubsan_in_hull ubsan_hull_ok IT_ok NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + exact CT_sound.
    + (apply GC_all; first [assumption | exact IT_ok]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
Qed.
End Contract.
End GuFMSC.
Module GuRead.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition IT : itab := mk_itab_ranges USEGS [(0x2fc24, 42%nat); (0x2fcf8, 61%nat)].
Lemma IT_ok : itab_sound USEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
Definition NXF : nat := 35.
Definition regs0 : list expr := ELit 0 :: map EVar (seq 0 3) ++ [ELit 0x8ab90] ++ map EVar (seq 4 27).
Definition e_sp : expr := EVar 1.
Definition R : expr := EVar 9.      (* [comment removed for export] *)
Definition v : expr := EVar 10.     (* [comment removed for export] *)
Definition BV : expr := EVar 11.    (* [comment removed for export] *)
Definition I : expr := EVar 31.
Definition E : expr := EVar 32.
Definition sv : expr := EVar 33.
Definition CAPW : expr := EVar 34.
Definition FRX : Z := 4352.         (* [comment removed for export] *)
Definition img_apart (x : expr) (k : Z) (n : expr) : kentry := KDisj (SA x k) n (SA (ELit 0) 0x10000) (ELit 0x9c000).
Definition BUFMAX : Z := 2 ^ 26.    (* [comment removed for export] *)
Definition kn_common : list kentry :=
  [KWord (SA BV 0) 8 I; KWord (SA BV 8) 8 E; KWord (SA BV 16) 8 CAPW;
   KUnk (SA I 0) (esub E I); KWr (SA I 0) (esub E I); KRange (esub E I) 0 BUFMAX; KRange I PTRLO PTRHI; KRange E PTRLO PTRHI;
   img_apart I 0 (esub E I); KDisj (SA I 0) (esub E I) (SA e_sp (- FRX)) (ELit (FRX + WSTK));      (* [comment removed for export] *)
   KWr (SA v 0) (ELit 16); KWr (SA v 16) (ELit 24); KWr (SA v 40) (ELit 24); KWr (SA R 0) (ELit 32); KWr (SA BV 0) (ELit 24);   (* [comment removed for export] *)
   KRange v CEIL HI47; KRange (eaddz v 64) (CEIL + 64) HI47; KRange R CEIL HI47; KRange BV CEIL HI47;   (* [comment removed for export] *)
   KRange (esub v e_sp) 0 (2^40); KRange (esub R e_sp) 0 (2^40); KRange (esub BV e_sp) 0 (2^40); (* [comment removed for export] *)
   KDisj (SA v 0) (ELit 64) (SA R 0) (ELit 32); KDisj (SA v 0) (ELit 64) (SA BV 0) (ELit 24); KDisj (SA R 0) (ELit 32) (SA BV 0) (ELit 24);
   KDisj (SA v 0) (ELit 64) (SA I 0) (esub E I); KDisj (SA R 0) (ELit 32) (SA I 0) (esub E I); KDisj (SA BV 0) (ELit 24) (SA I 0) (esub E I);
   KWr (SA e_sp (- FRX)) (ELit FRX);
   KDisj (SA e_sp (- FRX)) (ELit FRX) (SA v 0) (ELit 64); KDisj (SA e_sp (- FRX)) (ELit FRX) (SA R 0) (ELit 32);
   KDisj (SA e_sp (- FRX)) (ELit FRX) (SA BV 0) (ELit 24); KDisj (SA e_sp (- FRX)) (ELit FRX) (SA I 0) (esub E I);
   KAlign v 8; KAlign R 8; KAlign BV 8;
   KAlign e_sp 16; KRange e_sp (CEIL + 8368) HI47; 
    KImg 0x10000 0x75000].
Definition kn0 : list kentry := [KWord (SA v 16) 1 (escale 2 sv); KRange sv 0 22] ++ kn_common.
Definition WS : list (expr * expr) := [(v, ELit 64); (R, ELit 32); (I, esub E I); (eaddz e_sp (- FRX), ELit FRX)].
Definition mkcs (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vis : list (expr * expr)) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FRX 0 vis WS 0 e_sp FdStd false.   (* [comment removed for export] *)
Definition tin : acs := mkcs 0x2fc24 regs0 kn0 NXF [].

(* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := None.
Definition BCAP : Z := 2 ^ 28.  Definition CCAP : Z := 8.   (* [comment removed for export] *)
Definition XN : nat -> list expr -> acs -> option acs := XNc USEGS IT AUBSAN NXF GUBSAN BCAP CCAP CT.
Definition CT2 (id : nat) : option gcallee2 := if Nat.eqb id 101 then Some GuFMS.ce2 else None.
Definition XB : nat -> list expr -> acs -> option (acs * acs) := XBc USEGS AUBSAN NXF GUBSAN BCAP CCAP CT2.
Definition LIMIT : Z := 2 ^ 34.

(* [comment removed for export] *)
Definition RET : Z := 0x2fcc8.
Definition clobbered : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Fixpoint sr_havoc (sr : list expr) (ixs : list nat) (w : nat) : list expr :=
  match ixs with [] => sr | i :: t => sr_havoc (sr_upd sr i (EVar w)) t (S w) end.
Definition x_regs : list expr := sr_havoc regs0 clobbered 40.
Definition CNT : expr := EVar 55.      (* [comment removed for export] *)
Definition ER : expr := EVar 56.       (* [comment removed for export] *)
Definition resk : list kentry := [KWord (SA R 0) 8 CNT; KWord (SA R 8) 4 ER; KWord (SA R 16) 8 (ELit 0); KWord (SA R 24) 8 (ELit 0)].
(* [comment removed for export] *)
Definition SV2 : expr := EVar 57.
Definition x_kn_S : list kentry := resk ++ [KWord (SA v 16) 1 (escale 2 SV2); KRange SV2 0 22] ++ kn_common.
Definition toutS : acs := mkcs RET x_regs x_kn_S 58 [].
(* [comment removed for export] *)
Definition DL : expr := EVar 57. Definition SL : expr := EVar 58. Definition AL : expr := EVar 59.
Definition strL (d s a : expr) : list kentry :=
  [KWord (SA v 16) 8 (eaddz (escale 8 a) 1); KWord (SA v 24) 8 s; KWord (SA v 32) 8 d;
   KRange a 3 (2^24 + 1); KRange s 0 (2^27 + 8); KRange (esub (escale 8 a) s) 1 (2^27 + 8);
   KRange d PTRLO PTRHI; KRange (eadd d (escale 8 a)) PTRLO PTRHI; KAlign d 16; KWr (SA d 0) (escale 8 a); KUnk (SA d 0) (escale 8 a);
   KDisj (SA d 0) (escale 8 a) (SA v 0) (ELit 64); KDisj (SA d 0) (escale 8 a) (SA R 0) (ELit 32);
   KDisj (SA d 0) (escale 8 a) (SA BV 0) (ELit 24); KDisj (SA d 0) (escale 8 a) (SA I 0) (esub E I);
   KDisj (SA d 0) (escale 8 a) (SA e_sp (- FRX)) (ELit (FRX + WSTK)); img_apart d 0 (escale 8 a)].
Definition x_kn_L : list kentry := resk ++ strL DL SL AL ++ kn_common.
Definition toutL : acs := mkcs RET x_regs x_kn_L 60 [(DL, escale 8 AL)].


(* [comment removed for export] *)
Definition ce2 : gcallee2 := GCE2 NXF tin [toutS] [toutL] BCAP CCAP.
Definition ce : gcallee := c2_merged ce2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FMS_ARGS : list expr := [ELit 0; I; ELit 0; sv; ELit 0; ELit 0].
Definition after (h : nat) : plan := PRun [0x2fd78] (PBranch (PRun [] (PHandoff h)) (PRun [] (PHandoff h))).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition afterL (h : nat) : plan :=
  PRun [0x2fd78] (PBranch (PRun [] (PExt 13 [EVar 218] (PHandoff h))) (PRun [] (PExt 13 [EVar 218] (PHandoff h)))).
Definition call : plan := PRun [] (PBump 200 (PExt2 101 FMS_ARGS (after 0) (afterL 1))).               (* [comment removed for export] *)
Definition plan_read : plan :=
  PRun [] (PExt 2 []                                                   (* [comment removed for export] *)
   (PRun [0x2fd1c] (PCase2 (esub E I) 0
      (PRun [] (PHandoff 0))                                           (* [comment removed for export] *)
      (PRun [0x2fd50] (PBranch call call))))).



End GuRead.
Module GuVecPush.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzDev OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Module VecPushU.
Definition ENTRY : Z := 0x2f8b8.
Definition RETPC : Z := 0x2f998.
Definition IT : itab := mk_itab_ranges USEGS [(0x2f8b8, 57%nat); (0x2f9bc, 36%nat); (0x2fa50, 45%nat); (0x2fb08, 18%nat)].
Lemma IT_ok : itab_sound USEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
Definition regs0 : list expr := sr_upd (ELit 0 :: map EVar (seq 0 31)) 4 (ELit (g_tp GUBSAN)).
Definition e_sp : expr := EVar 1.
Definition V : expr := EVar 9.        (* [comment removed for export] *)
Definition VAL : expr := EVar 10.     (* [comment removed for export] *)
Definition SZ : expr := EVar 31.      (* [comment removed for export] *)
Definition B : expr := EVar 32.       (* [comment removed for export] *)
Definition NXF (w : bool) : nat := if w then 33 else 31.
Definition img_apart (x : expr) (k : Z) (n : expr) : kentry := KDisj (SA x k) n (SA (ELit 0) 0x10000) (ELit 0x9c000).
(* [comment removed for export] *)
Definition SZHI : Z := 2 ^ 26 - 1.
Definition FR : Z := 112.             (* [comment removed for export] *)
Definition FRS : Z := FR + MSTK.

Definition kn_fixed : list kentry :=
  [ KRange V CEIL HI47; KWr (SA V 0) (ELit 24); KRange (esub V e_sp) 0 (2 ^ 40);
    KRange VAL CEIL HI47; KUnk (SA VAL 0) (ELit 1); KRange (esub VAL e_sp) 0 (2 ^ 40);
    KDisj (SA V 0) (ELit 24) (SA VAL 0) (ELit 1);
    KAlign e_sp 16; KRange e_sp (CEIL + FRS + 16) HI47; KWr (SA e_sp (- FRS)) (ELit FRS);
    KDisj (SA e_sp (- FRS)) (ELit FRS) (SA V 0) (ELit 24); KDisj (SA e_sp (- FRS)) (ELit FRS) (SA VAL 0) (ELit 1);
    KImg 0x10000 0x75000 ].
(* [comment removed for export] *)
Definition blk (p n : expr) (nlo : Z) : list kentry :=
  [ KRange p PTRLO (PTRHI - nlo); KRange (eadd n p) (PTRLO + nlo) PTRHI; KAlign p 16; KWr (SA p 0) n; KUnk (SA p 0) n;
    KDisj (SA p 0) n (SA V 0) (ELit 24); KDisj (SA p 0) n (SA VAL 0) (ELit 1); KDisj (SA p 0) n (SA e_sp (- FRS)) (ELit (FRS + WSTK)); img_apart p 0 n ].   (* [comment removed for export] *)
Definition kn_in (w : bool) : list kentry :=
  (if w then [ KWord (SA V 0) 8 B; KWord (SA V 8) 8 (eadd SZ B); KWord (SA V 16) 8 (eadd SZ B); KRange SZ 1 SZHI ] ++ blk B SZ 1
   else [ KWord (SA V 0) 8 (ELit 0); KWord (SA V 8) 8 (ELit 0); KWord (SA V 16) 8 (ELit 0) ])
  ++ kn_fixed.
Definition WS : list (expr * expr) := [(V, ELit 24); (VAL, ELit 1)].   (* [comment removed for export] *)
Definition mkcs (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vis : list (expr * expr)) : acs :=
  ACS (mk_ss p regs k nx) [] 0 FRS 0 vis WS 0 e_sp FdStd false.   (* [comment removed for export] *)
Definition vis_in (w : bool) : list (expr * expr) := if w then [(B, SZ)] else [].
Definition tin (w : bool) : acs := mkcs ENTRY regs0 (kn_in w) (NXF w) (vis_in w).

(* [comment removed for export] *)
Definition P (w : bool) : expr := EVar (NXF w).
Definition clobbered : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Fixpoint sr_havoc (sr : list expr) (ixs : list nat) (v : nat) : list expr :=
  match ixs with [] => sr | i :: t => sr_havoc (sr_upd sr i (EVar v)) t (S v) end.
(* [comment removed for export] *)
Definition CAPN : expr := EVar 34.
Definition XLO (w : bool) : nat := if w then 35 else 32.
Definition regs_out (w : bool) : list expr := sr_havoc regs0 clobbered (XLO w).
Definition NEWCAP (w : bool) : expr := if w then CAPN else ELit 1.
Definition NEWEND (w : bool) : expr := if w then eaddz (eadd SZ (P w)) 1 else eaddz (P w) 1.
Definition kn_out (w : bool) : list kentry :=
  [ KWord (SA V 0) 8 (P w); KWord (SA V 8) 8 (NEWEND w); KWord (SA V 16) 8 (eadd (NEWCAP w) (P w)) ]
  ++ (if w then [KRange SZ 1 SZHI; KRange CAPN 2 (2 * SZHI); KRange (esub CAPN (escale 2 SZ)) 0 0] else [])
  ++ blk (P w) (NEWCAP w) (if w then 2 else 1) ++ kn_fixed.
Definition tout (w : bool) : acs := mkcs RETPC (regs_out w) (kn_out w) (XLO w + 15)%nat [(P w, NEWCAP w)].
Definition BCAP : Z := 2 ^ 28.   (* [comment removed for export] *)
Definition CCAP : Z := 2.
Definition ce (w : bool) : gcallee := GCE (NXF w) (tin w) [tout w] BCAP CCAP.

(* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := None.
Definition XN (w : bool) : nat -> list expr -> acs -> option acs := XNc USEGS IT AUBSAN (NXF w) GUBSAN BCAP CCAP CT.
Definition LIMIT : Z := 2 ^ 34.
Definition FUEL : nat := 400.
Definition BFUEL : nat := 300.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PF : expr := EVar 33.
Definition disjP (k : plan) : plan :=
  PFact (KDisj (SA PF 0) (escale 2 SZ) (SA e_sp (- FRS)) (ELit FRS))
  (PFact (KDisj (SA PF 0) (escale 2 SZ) (SA V 0) (ELit 24))
  (PFact (KDisj (SA PF 0) (escale 2 SZ) (SA VAL 0) (ELit 1)) k)).
Definition tail : plan :=             (* [comment removed for export] *)
  PRun [] (PExt 20 [] (disjP (PRun [] (PExt 1 [] (PRun [] (PExt 21 [] (PRun [] (PHandoff 0)))))))).
Definition tailE : plan :=            (* [comment removed for export] *)
  PRun [] (PExt 20 [] (PRun [] (PExt 1 [] (PRun [] (PHandoff 0))))).
Definition plan (w : bool) : plan :=
  if w then
    (* [comment removed for export] *)
    PCase2 SZ 1 (PRun [0x2f91c] (PRespell 11 (escale 2 SZ) tail)) tail
  else tailE.

Definition SHAPE : shape := SHole 0.

Lemma cert_full : check USEGS IT AUBSAN (NXF true) LIMIT (XN true) (B2JCutShare.GlzCallCert.XE0) (B2JCutShare.GlzCallCert.XB0) XC0 (HSce (ce true)) 0%nat BFUEL FUEL None (tin true) (plan true) = COk SHAPE.
Proof. vm_cast_no_check (@eq_refl cres (COk SHAPE)). Qed.
Lemma cert_empty : check USEGS IT AUBSAN (NXF false) LIMIT (XN false) (B2JCutShare.GlzCallCert.XE0) (B2JCutShare.GlzCallCert.XB0) XC0 (HSce (ce false)) 0%nat BFUEL FUEL None (tin false) (plan false) = COk SHAPE.
Proof. vm_cast_no_check (@eq_refl cres (COk SHAPE)). Qed.
Lemma gplan : forall w, gplan_ok (plan w) = true. Proof. intros [|]; reflexivity. Qed.
Lemma hshape : holes_only SHAPE = true. Proof. reflexivity. Qed.


End VecPushU.
End GuVecPush.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GuFuzz.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzDev OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.

Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon.GuVecCtor GuVecPush GuB2JT OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks.GuFuzzT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Module FuzzNP.
Import FuzzN.
Definition DTORV : Z := 0x2f83c.      (* [comment removed for export] *)
Definition DTORS : Z := 0x2f888.      (* [comment removed for export] *)
Definition IT : itab := mk_itab_ranges USEGS [(ENTRY, NINSTR); (DTORV, 18%nat); (DTORS, 11%nat)].
Lemma IT_ok : itab_sound USEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
Definition CT (id : nat) : option gcallee :=
  if Nat.eqb id 110 then Some VecCtorU.ce
  else if Nat.eqb id 111 then Some GuCommon.GuStrCtor.ce
  else if Nat.eqb id 114 then Some (VecPushU.ce true)
  else None.
Definition CT2 (id : nat) : option gcallee2 :=
  if Nat.eqb id 112 then Some GuRead.ce2
  else if Nat.eqb id 113 then Some B2JnUT.ce2
  else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc USEGS IT AUBSAN NXF GUBSAN BCAP CCAP CT.
Definition XB : nat -> list expr -> acs -> option (acs * acs) := XBc USEGS AUBSAN NXF GUBSAN BCAP CCAP CT2.
Definition LIMIT : Z := 2 ^ 34.
Definition FUEL : nat := 2000.
Definition BFUEL : nat := 600.

(* [comment removed for export] *)
Definition P1 : expr := EVar 31.      (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition BLK (p : expr) (k : plan) : plan := PExt 13 [p] k.
(* [comment removed for export] *)
Definition REHEL (k : plan) : plan := PFact (KRange HEL (CEIL + YLO - 80) (HI47 - 80)) k.
(* [comment removed for export] *)
Definition RESP (k : plan) : plan := PFact (KRange SX (CEIL + YLO - 224) (HI47 - 224)) k.
Definition FIN : plan := PRun [] (PExt 21 [] (PRun [] (PHandoff 0))).         (* [comment removed for export] *)
Definition P2 : expr := EVar 200.      (* [comment removed for export] *)
Definition CAP2 : expr := EVar 201.    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition after_read2 (h2 : smode) : plan :=
  (PRun [0x2f17c] (PBranch
    (match h2 with MS => FIN | ML => PRun [] (PExt 21 [] FIN) end)      (* [comment removed for export] *)
    (match h2 with MS => FIN | ML => PRun [] (PExt 21 [] FIN) end))).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition call_read2 (p2 e2 c2 : expr) : plan := PExt2 112 [DUM; p2; e2; ELit 11; c2] (after_read2 MS) (after_read2 ML).
(* [comment removed for export] *)
Definition after_push (p2 e2 c2 : expr) : plan :=
  PRun [] (PExt 111 [] (REHEL (PRun [0x2fc24] (call_read2 p2 e2 c2)))).
(* [comment removed for export] *)
Definition blk2 : list kentry :=
  [ KRange P2 PTRLO (HI47 - 2); KRange (eadd P2 CAP2) (PTRLO + 2) HI47; KAlign P2 16; KWr (SA P2 0) CAP2; KUnk (SA P2 0) CAP2;
    KRange CAP2 2 (2 * SZHI); KRange (eadd (escale (-2) SIZE) CAP2) 0 0;
    KDisj (SA P2 0) CAP2 (SA e_sp (-152)) (ELit 24); KDisj (SA P2 0) CAP2 (SA e_sp (-224)) (ELit 1);   (* [comment removed for export] *)
    img_apart P2 0 CAP2 ].
Definition frame : list kentry :=
  [ KWord (SA e_sp (-8)) 8 (EVar 0); KWord (SA e_sp (-16)) 8 (EVar 7); KWord (SA e_sp (-24)) 8 (EVar 8); KWord (SA e_sp (-32)) 8 (EVar 17) ].
Definition hvJ : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.   (* [comment removed for export] *)
Definition regsJ : list expr :=
  sr_havoc (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd regsT 1 (ELit 0x2f134)) 2 SX) 8 HEL) 9 (eaddz e_sp (-56)))
              18 (ELit 4614253070214989087)) hvJ 202.
Definition JS : acs :=
  mkcs 0x2f134 regsJ
       ([ KWord (SA e_sp (-152)) 8 P2; KWord (SA e_sp (-144)) 8 (eaddz (eadd SIZE P2) 1); KWord (SA e_sp (-136)) 8 (eadd P2 CAP2) ] ++ blk2 ++ frame ++ kn_fixed)
       217 [(DATA, SIZE); (P2, CAP2)].
Definition PUSH : plan := PRun [] (PBump 200 (PExt 114 [DUM; SIZE; P1] (PMerge 1))).
Definition KAFTER : plan := BLK P2 (RESP (after_push P2 (eaddz (eadd SIZE P2) 1) (eadd P2 CAP2))).
(* [comment removed for export] *)
Definition JPr : list expr :=
  [ELit 0; ELit 192820; EAlu Instr.ALU_ADD (EVar 1) (ELit (-224)); EVar 2; ELit 568208; EVar 150; EVar 151; EVar 152; EAlu Instr.ALU_ADD (EVar 1) (ELit (-80)); EAlu Instr.ALU_ADD (EVar 1) (ELit (-56));
  EAlu Instr.ALU_ADD (EVar 1) (ELit (-152)); EAlu Instr.ALU_ADD (EVar 1) (ELit (-224)); EVar 153; EVar 154; EVar 155; EVar 156; EVar 157; EVar 158; ELit 4614253070214989087; EVar 18; EVar 19; EVar 20;
  EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 159; EVar 160; EVar 161; EVar 162].
Definition JPk : list kentry :=
  [KWord {| a_base := EVar 1; a_off := -224 |} 1 (ELit 0); KRange (EAlu Instr.ALU_ADD (EVar 1) (ELit (-96))) 140735332483072 140737488355328; KWr {| a_base := EVar 1; a_off := -96 |} (ELit 32); KRange
  (ELit 128) 0 1099511627776; KRange (EAlu Instr.ALU_ADD (EVar 1) (ELit (-152))) 140735332483072 140737488355328; KWord {| a_base := EVar 1; a_off := -152 |} 8 (EVar 31); KWord {| a_base := EVar 1;
  a_off := -144 |} 8 (EAlu Instr.ALU_ADD (EVar 10) (EVar 31)); KRange (ELit 72) 0 1099511627776; KWr {| a_base := EVar 1; a_off := -152 |} (ELit 16); KRange (EAlu Instr.ALU_ADD (EVar 1) (ELit (-128)))
  140735332483072 140737488355304; KWr {| a_base := EVar 1; a_off := -128 |} (ELit 24); KUnk {| a_base := EVar 1; a_off := -128 |} (ELit 24); KRange (ELit 96) 0 1099511627776; KAlign (EAlu Instr.ALU_ADD
  (EVar 1) (ELit (-128))) 8; KRange (EVar 31) 4112 140737479966720; KRange (EVar 10) 1 67108864; KRange (EAlu Instr.ALU_ADD (EVar 10) (EVar 31)) 4113 140737479966720; KUnk {| a_base := EVar 31; a_off :=
  0 |} (EVar 10); KDisj {| a_base := EVar 1; a_off := -96 |} (ELit 32) {| a_base := EVar 1; a_off := -128 |} (ELit 24); KDisj {| a_base := EVar 1; a_off := -96 |} (ELit 32) {| a_base := EVar 1; a_off :=
  -152 |} (ELit 16); KDisj {| a_base := EVar 1; a_off := -128 |} (ELit 24) {| a_base := EVar 1; a_off := -152 |} (ELit 16); KDisj {| a_base := EVar 31; a_off := 0 |} (EVar 10) {| a_base := EVar 1; a_off
  := -96 |} (ELit 32); KDisj {| a_base := EVar 31; a_off := 0 |} (EVar 10) {| a_base := EVar 1; a_off := -128 |} (ELit 24); KDisj {| a_base := EVar 31; a_off := 0 |} (EVar 10) {| a_base := EVar 1; a_off
  := -152 |} (ELit 16); KAlign (EAlu Instr.ALU_ADD (EVar 1) (ELit (-224))) 16; KRange (EAlu Instr.ALU_ADD (EVar 1) (ELit (-224))) 140735332540768 140737488355328; KWr {| a_base := EVar 1; a_off :=
  -57920 |} (ELit 57696); KDisj {| a_base := EVar 1; a_off := -57920 |} (ELit 57696) {| a_base := EVar 1; a_off := -96 |} (ELit 32); KDisj {| a_base := EVar 1; a_off := -57920 |} (ELit 57696) {| a_base
  := EVar 1; a_off := -128 |} (ELit 24); KDisj {| a_base := EVar 1; a_off := -57920 |} (ELit 57696) {| a_base := EVar 1; a_off := -152 |} (ELit 16); KDisj {| a_base := EVar 31; a_off := 0 |} (EVar 10)
  {| a_base := EVar 1; a_off := -57920 |} (ELit 4611686018427445600); KDisj {| a_base := EVar 31; a_off := 0 |} (EVar 10) {| a_base := ELit 0; a_off := 65536 |} (ELit 638976); KImg 65536 479232; KWr {|
  a_base := EVar 31; a_off := 0 |} (EVar 10); KWr {| a_base := EVar 1; a_off := -96 |} (ELit 16); KWr {| a_base := EVar 1; a_off := -80 |} (ELit 24); KWr {| a_base := EVar 1; a_off := -56 |} (ELit 24);
  KWr {| a_base := EVar 1; a_off := -128 |} (ELit 32); KWr {| a_base := EVar 1; a_off := -152 |} (ELit 24); KWr {| a_base := EVar 1; a_off := -4576 |} (ELit 4352); KWr {| a_base := EVar 1; a_off := -288
  |} (ELit 64); KWr {| a_base := EVar 9; a_off := 0 |} (EVar 10); KUnk {| a_base := EVar 9; a_off := 0 |} (EVar 10); KWr {| a_base := EVar 1; a_off := -2368 |} (ELit 2144); KWr {| a_base := EVar 1;
  a_off := -57920 |} (ELit 57920); KUnk {| a_base := EVar 1; a_off := -57920 |} (ELit 57920); KWord {| a_base := EVar 1; a_off := -104 |} 8 (ELit 0); KWord {| a_base := EVar 1; a_off := -136 |} 8 (EAlu
  Instr.ALU_ADD (EVar 10) (EVar 31)); KRange (EVar 10) 0 67108864; KRange (EAlu Instr.ALU_ADD (EVar 10) (EVar 31)) 4112 140737479966720; KDisj {| a_base := EVar 31; a_off := 0 |} (EVar 10) {| a_base :=
  EVar 1; a_off := -4576 |} (ELit 4611686018427392256); KRange (EAlu Instr.ALU_ADD (EVar 1) (ELit (-32))) 140735332483136 140737488355328; KRange (EAlu Instr.ALU_ADD (EVar 1) (ELit (-128)))
  140735332483072 140737488355328; KDisj {| a_base := EVar 1; a_off := -96 |} (ELit 64) {| a_base := EVar 1; a_off := -128 |} (ELit 32); KDisj {| a_base := EVar 1; a_off := -96 |} (ELit 64) {| a_base :=
  EVar 1; a_off := -152 |} (ELit 24); KDisj {| a_base := EVar 1; a_off := -128 |} (ELit 32) {| a_base := EVar 1; a_off := -152 |} (ELit 24); KDisj {| a_base := EVar 1; a_off := -96 |} (ELit 64) {|
  a_base := EVar 31; a_off := 0 |} (EVar 10); KDisj {| a_base := EVar 1; a_off := -128 |} (ELit 32) {| a_base := EVar 31; a_off := 0 |} (EVar 10); KDisj {| a_base := EVar 1; a_off := -152 |} (ELit 24)
  {| a_base := EVar 31; a_off := 0 |} (EVar 10); KDisj {| a_base := EVar 1; a_off := -4576 |} (ELit 4352) {| a_base := EVar 1; a_off := -96 |} (ELit 64); KDisj {| a_base := EVar 1; a_off := -4576 |}
  (ELit 4352) {| a_base := EVar 1; a_off := -128 |} (ELit 32); KDisj {| a_base := EVar 1; a_off := -4576 |} (ELit 4352) {| a_base := EVar 1; a_off := -152 |} (ELit 24); KDisj {| a_base := EVar 1; a_off
  := -4576 |} (ELit 4352) {| a_base := EVar 31; a_off := 0 |} (EVar 10); KAlign (EAlu Instr.ALU_ADD (EVar 1) (ELit (-96))) 8; KAlign (EAlu Instr.ALU_ADD (EVar 1) (ELit (-152))) 8; KRange (EAlu
  Instr.ALU_ADD (EVar 1) (ELit (-224))) 140735332491440 140737488355328; KRange (EAlu Instr.ALU_ADD (EVar 1) (ELit (-80))) 140735332540912 140737488355248; KRange (EAlu Instr.ALU_ADD (EVar 1) (ELit
  (-80))) 140735332483072 140737488355328; KDisj {| a_base := EVar 1; a_off := -80 |} (ELit 24) {| a_base := EVar 1; a_off := -288 |} (ELit 64); KRange (EAlu Instr.ALU_ADD (EVar 1) (ELit (-224)))
  140735332487168 140737488355328; KRange (EVar 31) 4112 140737479966719; KDisj {| a_base := EVar 31; a_off := 0 |} (EVar 10) {| a_base := EVar 1; a_off := -57920 |} (ELit 4611686018427445824); KDisj {|
  a_base := EVar 31; a_off := 0 |} (EVar 10) {| a_base := EVar 9; a_off := 0 |} (EVar 10); KDisj {| a_base := EVar 31; a_off := 0 |} (EVar 10) {| a_base := EVar 1; a_off := -8 |} (ELit 8); KDisj {|
  a_base := EVar 31; a_off := 0 |} (EVar 10) {| a_base := EVar 1; a_off := -16 |} (ELit 8); KDisj {| a_base := EVar 31; a_off := 0 |} (EVar 10) {| a_base := EVar 1; a_off := -24 |} (ELit 8); KDisj {|
  a_base := EVar 31; a_off := 0 |} (EVar 10) {| a_base := EVar 1; a_off := -32 |} (ELit 8); KDisj {| a_base := EVar 31; a_off := 0 |} (EVar 10) {| a_base := EVar 1; a_off := -136 |} (ELit 8); KDisj {|
  a_base := EVar 31; a_off := 0 |} (EVar 10) {| a_base := EVar 1; a_off := -144 |} (ELit 8); KDisj {| a_base := EVar 31; a_off := 0 |} (EVar 10) {| a_base := EVar 1; a_off := -152 |} (ELit 8); KDisj {|
  a_base := EVar 31; a_off := 0 |} (EVar 10) {| a_base := EVar 1; a_off := -57920 |} (ELit 57920); KDisj {| a_base := EVar 31; a_off := 0 |} (EVar 10) {| a_base := EVar 1; a_off := -2368 |} (ELit 2144);
  KDisj {| a_base := EVar 31; a_off := 0 |} (EVar 10) {| a_base := EVar 1; a_off := -152 |} (ELit 24); KAlign (EVar 31) 16; KDisj {| a_base := EVar 31; a_off := 0 |} (EVar 10) {| a_base := EVar 1; a_off
  := -2368 |} (ELit 4611686018427390048); KRange (EVar 10) 1 67108863; KRange (EVar 9) 4112 140737479966720; KRange (EAlu Instr.ALU_ADD (EVar 9) (EVar 10)) 4113 140737479966720; KDisj {| a_base := EVar
  9; a_off := 0 |} (EVar 10) {| a_base := ELit 0; a_off := 65536 |} (ELit 638976); KDisj {| a_base := EVar 9; a_off := 0 |} (EVar 10) {| a_base := EVar 1; a_off := -152 |} (ELit 24); KRange (EAlu
  Instr.ALU_ADD (EVar 1) (ELit (-224))) 140735332485232 140737488355328; KDisj {| a_base := EVar 1; a_off := -2368 |} (ELit 2144) {| a_base := EVar 1; a_off := -152 |} (ELit 24); KDisj {| a_base := EVar
  9; a_off := 0 |} (EVar 10) {| a_base := EVar 1; a_off := -2368 |} (ELit 4611686018427390048); KWord {| a_base := EVar 1; a_off := -32 |} 8 (EVar 17); KWord {| a_base := EVar 1; a_off := -24 |} 8 (EVar
  8); KWord {| a_base := EVar 1; a_off := -16 |} 8 (EVar 7); KWord {| a_base := EVar 1; a_off := -8 |} 8 (EVar 0); KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 10)) (ELit (-2))) 0
  134217724; KRange (EVar 9) 4112 140737479966719; KAlign (EVar 9) 16; KAlign (EVar 1) 16; KRange (EVar 1) 140735332540992 140737488355328; KDisj {| a_base := EVar 9; a_off := 0 |} (EVar 10) {| a_base
  := EVar 1; a_off := -57920 |} (ELit 4611686018427445824)].
Definition JP : acs := mkcs 0x2f8b8 JPr JPk 163 [(P1, SIZE); (DATA, SIZE)].
Definition PUSHJ : plan := PRun [] (PMerge 2).
(* [comment removed for export] *)
Definition after_b2j (h1 j : smode) (hv : bool) (push : plan) : plan :=
  let X := if hv then match h1 with ML => PRun [] (PExt 21 [] push) | MS => push end else push in
  (match j with ML => PRun [] (PExt 21 [] X) | MS => X end).
Definition B2J_ARGS : list expr := [DUM; SIZE; P1].
Definition call_b2j (h1 : smode) (hv : bool) (push : plan) : plan :=
  PExt2 113 B2J_ARGS (after_b2j h1 MS hv push) (after_b2j h1 ML hv push).
(* [comment removed for export] *)
Definition after_read1 (h1 : smode) (push : plan) : plan :=
  (PRun [0x2f084] (PBranch
    (PRun [B2JnUT.ENTRY] (call_b2j h1 true push))                                         (* [comment removed for export] *)
    (match h1 with MS => PRun [B2JnUT.ENTRY] (call_b2j MS false push)                      (* [comment removed for export] *)
                 | ML => PRun [] (PExt 21 [] (PRun [B2JnUT.ENTRY] (call_b2j ML false push))) end))).
Definition READ1_ARGS : list expr := [DUM; P1; eadd SIZE P1; ELit 11; eadd SIZE P1].

Definition ARMSJ : plan :=
  PRun [] (PExt 111 [] (REHEL (PRun [] (PExt2 112 READ1_ARGS (after_read1 MS PUSHJ) (after_read1 ML PUSHJ))))).
Definition planN : plan :=
  PRun [] (PExt 110 [TP; DUM] (BLK P1 (PVia 1 JS 200 (PVia 2 JP 150 ARMSJ PUSH) KAFTER))).

Definition SHAPE : shape := SHole 0.
Lemma gplan : gplan_ok planN = true. Proof. reflexivity. Qed.
Lemma hshape : holes_only SHAPE = true. Proof. reflexivity. Qed.



End FuzzNP.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Module FuzzEP.
Import FuzzN. Import FuzzNP. Import FuzzE.
Definition IT : itab := mk_itab_ranges USEGS
  [(ENTRY, NINSTR); (DTORV, 18%nat); (DTORS, 11%nat); (VecCtorU.ENTRY, 27%nat); (0x2fc24, 42%nat); (0x2fcf8, 61%nat);
   (B2JnUT.ENTRY, 123%nat)].
Lemma IT_ok : itab_sound USEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition CT (id : nat) : option gcallee :=
  if Nat.eqb id 111 then Some GuCommon.GuStrCtor.ce
  else if Nat.eqb id 115 then Some (VecPushU.ce false)
  else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc USEGS IT AUBSAN NXF GUBSAN BCAP CCAP CT.
Definition XB : nat -> list expr -> acs -> option (acs * acs) := XBc USEGS AUBSAN NXF GUBSAN BCAP CCAP CT2.
(* [comment removed for export] *)
Definition PUSH : plan :=
  PRun [] (PBump 200 (PExt 115 [DUM] (BLK P2 (RESP (after_push P2 (eaddz P2 1) (eaddz P2 1)))))).
Definition planE : plan :=
  PRun [] (PExt 111 [] (REHEL              (* [comment removed for export] *)
  (PRun [] (PExt 2 []                      (* [comment removed for export] *)
  (PRun [0x2f1fc]                          (* [comment removed for export] *)
  (PRun [] (PExt 2 []                      (* [comment removed for export] *)
  (PRun [] PUSH)))))))).                   (* [comment removed for export] *)
Definition SHAPE : shape := SHole 0.
Lemma gplan : gplan_ok planE = true. Proof. reflexivity. Qed.
Lemma hshape : holes_only SHAPE = true. Proof. reflexivity. Qed.



End FuzzEP.
End GuFuzz.
Module GuFuzzNcert.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks.GuFuzzT GuFuzz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Lemma cert : check USEGS FuzzNP.IT AUBSAN FuzzN.NXF FuzzNP.LIMIT FuzzNP.XN (B2JCutShare.GlzCallCert.XE0) FuzzNP.XB B2JCutShare.GlzCallCert.XC0 (HSce FuzzN.ce) 0%nat
                   FuzzNP.BFUEL FuzzNP.FUEL None FuzzN.tin FuzzNP.planN = COk FuzzNP.SHAPE.
Proof. vm_cast_no_check (@eq_refl cres (COk FuzzNP.SHAPE)). Qed.
End GuFuzzNcert.
Module GuFuzzEcert.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks.GuFuzzT GuFuzz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Lemma cert : check USEGS FuzzEP.IT AUBSAN FuzzN.NXF FuzzNP.LIMIT FuzzEP.XN (B2JCutShare.GlzCallCert.XE0) FuzzEP.XB B2JCutShare.GlzCallCert.XC0 (HSce FuzzE.ce) 0%nat
                   FuzzNP.BFUEL FuzzNP.FUEL None FuzzE.tin FuzzEP.planE = COk FuzzEP.SHAPE.
Proof. vm_cast_no_check (@eq_refl cres (COk FuzzEP.SHAPE)). Qed.
End GuFuzzEcert.
Module GuFuzzC.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon.   (* [comment removed for export] *)

Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon.GuVecCtor GuVecPush GuB2JT GuB2J OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks.GuFuzzT GuFuzz.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
(* [comment removed for export] *)
Hypothesis VEC_CTOR : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH VecCtorU.ce.            (* [comment removed for export] *)
Hypothesis VEC_PUSH_FULL : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (VecPushU.ce true).  (* [comment removed for export] *)
Hypothesis VEC_PUSH_EMPTY : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (VecPushU.ce false). (* [comment removed for export] *)
Hypothesis B2J : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (c2_merged B2JnUT.ce2).          (* [comment removed for export] *)
Hypothesis STR_CTOR : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH GuCommon.GuStrCtor.ce.          (* [comment removed for export] *)
Hypothesis READ : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (c2_merged GuRead.ce2).      (* [comment removed for export] *)

Lemma CT_N_sound : forall id c, FuzzNP.CT id = Some c -> callee_contract USEGS [] GUBSAN fx_ok RZ AINVH c.
Proof.
  intros id c H. unfold FuzzNP.CT in H.
  destruct (Nat.eqb id 110); [injection H as <-; exact VEC_CTOR|].
  destruct (Nat.eqb id 111); [injection H as <-; exact STR_CTOR|].
  destruct (Nat.eqb id 114); [injection H as <-; exact VEC_PUSH_FULL|]. discriminate H.
Qed.
Lemma CT2_sound : forall id c, FuzzNP.CT2 id = Some c -> callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (c2_merged c).
Proof.
  intros id c H. unfold FuzzNP.CT2 in H.
  destruct (Nat.eqb id 112); [injection H as <-; exact READ|].
  destruct (Nat.eqb id 113); [injection H as <-; exact B2J|]. discriminate H.
Qed.
Lemma CT_E_sound : forall id c, FuzzEP.CT id = Some c -> callee_contract USEGS [] GUBSAN fx_ok RZ AINVH c.
Proof.
  intros id c H. unfold FuzzEP.CT in H.
  destruct (Nat.eqb id 111); [injection H as <-; exact STR_CTOR|].
  destruct (Nat.eqb id 115); [injection H as <-; exact VEC_PUSH_EMPTY|]. discriminate H.
Qed.

Theorem fuzz_callee_N : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH FuzzN.ce.
Proof.
  refine (contract_of_cert_xb USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            FuzzN.ce FuzzNP.IT FuzzNP.IT_ok FuzzNP.LIMIT 0%nat FuzzNP.BFUEL FuzzNP.FUEL FuzzNP.XN _ FuzzNP.XB _ FuzzNP.planN _
            FuzzNP.gplan FuzzNP.hshape GuFuzzNcert.cert).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold FuzzNP.XN.
    apply (XNc_sound USEGS FuzzNP.IT AUBSAN ubsan_in_hull ubsan_hull_ok FuzzNP.IT_ok FuzzN.NXF [] GUBSAN FuzzN.BCAP FuzzN.CCAP fx_ok RZ RZ_step
              AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa FuzzNP.CT).
    + exact CT_N_sound.
    + (apply GC_all; first [assumption | exact FuzzNP.IT_ok]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold FuzzNP.XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok FuzzN.NXF [] GUBSAN FuzzN.BCAP FuzzN.CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa FuzzNP.CT2).
    + exact CT2_sound.
    + (apply OBL2_all; assumption).
Qed.

Theorem fuzz_callee_E : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH FuzzE.ce.
Proof.
  refine (contract_of_cert_xb USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            FuzzE.ce FuzzEP.IT FuzzEP.IT_ok FuzzNP.LIMIT 0%nat FuzzNP.BFUEL FuzzNP.FUEL FuzzEP.XN _ FuzzEP.XB _ FuzzEP.planE _
            FuzzEP.gplan FuzzEP.hshape GuFuzzEcert.cert).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold FuzzEP.XN.
    apply (XNc_sound USEGS FuzzEP.IT AUBSAN ubsan_in_hull ubsan_hull_ok FuzzEP.IT_ok FuzzN.NXF [] GUBSAN FuzzE.BCAP FuzzE.CCAP fx_ok RZ RZ_step
              AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa FuzzEP.CT).
    + exact CT_E_sound.
    + (apply GC_all; first [assumption | exact FuzzEP.IT_ok]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold FuzzEP.XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok FuzzN.NXF [] GUBSAN FuzzE.BCAP FuzzE.CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa FuzzNP.CT2).
    + exact CT2_sound.
    + (apply OBL2_all; assumption).
Qed.
End Contract.
End GuFuzzC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GuWFT OSSVerify.Proofs.glaze.binary_reflection.lib.GuNum OSSVerify.Proofs.glaze.binary_reflection.lib.GuWDT OSSVerify.Proofs.glaze.binary_reflection.lib.GuWN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GuNumC.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuU32 GuU32C OSSVerify.Proofs.glaze.binary_reflection.lib.GuI32 GuI32C OSSVerify.Proofs.glaze.binary_reflection.lib.GuU64 GuU64C OSSVerify.Proofs.glaze.binary_reflection.lib.GuI64 GuI64C OSSVerify.Proofs.glaze.binary_reflection.lib.GuWFT OSSVerify.Proofs.glaze.binary_reflection.lib.GuNum.GuWFC OSSVerify.Proofs.glaze.binary_reflection.lib.GuWDT OSSVerify.Proofs.glaze.binary_reflection.lib.GuNum.GuWDC OSSVerify.Proofs.glaze.binary_reflection.lib.GuWN OSSVerify.Proofs.glaze.binary_reflection.lib.GuNum.GuWNf32 OSSVerify.Proofs.glaze.binary_reflection.lib.GuNum.GuWNf64 OSSVerify.Proofs.glaze.binary_reflection.lib.GuNum.GuWNi8 OSSVerify.Proofs.glaze.binary_reflection.lib.GuNum.GuWNi16 OSSVerify.Proofs.glaze.binary_reflection.lib.GuNum.GuWNu8 OSSVerify.Proofs.glaze.binary_reflection.lib.GuNum.GuWNu16 OSSVerify.Proofs.glaze.binary_reflection.lib.GuNum.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

#[local] Notation CHK m B := (check USEGS (B2JUT.GuNumT.IT B) AUBSAN B2JUT.GuNumT.NXF LIMIT (GuNum.XN B) (B2JCutShare.GlzCallCert.XE0) (GuNum.XB B) XC0 (HSce (B2JUT.GuNumT.ce m B)) 0%nat BFUEL FUELN None).
#[local] Notation CHK1 B := (check USEGS (B2JUT.GuNumT.IT B) AUBSAN B2JUT.GuNumT.NXF LIMIT (GuNum.XN1 B) (B2JCutShare.GlzCallCert.XE0) (GuNum.XB B) XC0 (HSce (B2JUT.GuNumT.ceL1 B)) 0%nat BFUEL FUELN None).
Lemma numu_cert_S : CHK MS BNU (B2JUT.GuNumT.tin MS BNU) (GuNum.PLAN BNU MS) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma numi_cert_S : CHK MS BNI (B2JUT.GuNumT.tin MS BNI) (GuNum.PLAN BNI MS) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma numu_cert_L1 : CHK1 BNU (B2JUT.GuNumT.tin ML BNU) (GuNum.PLANL1 BNU ML) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma numi_cert_L1 : CHK1 BNI (B2JUT.GuNumT.tin ML BNI) (GuNum.PLANL1 BNI ML) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma num_gplan : forall B m, gplan_ok (GuNum.PLAN B m) = true. Proof. intros B [|]; vm_compute; reflexivity. Qed.
Lemma num_gplan1 : forall B, gplan_ok (GuNum.PLANL1 B ML) = true. Proof. intros B; vm_compute; reflexivity. Qed.
Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.

Lemma ZMIJF_callee : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH GuWFT.ce.
Proof. apply (GuNum.GuWFC.write_float_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]). Qed.
Lemma ZMIJD_callee : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH GuWDT.ce.
Proof. apply (GuNum.GuWDC.write_double_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]). Qed.

Lemma CT_ok : forall id ce', GuNum.CT id = Some ce' -> callee_contract USEGS [] GUBSAN fx_ok RZ AINVH ce'.
Proof.
  intros id ce' H. unfold GuNum.CT in H.
  destruct (Nat.eqb id 132). { injection H as <-. apply (GuI32C.to_chars40kb_i32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros; (apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]). }
  destruct (Nat.eqb id 133). { injection H as <-. apply (GuU32C.to_chars40kb_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros; (apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]). }
  destruct (Nat.eqb id 134). { injection H as <-. apply (GuI64C.to_chars40kb_i64_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros; (apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]). }
  destruct (Nat.eqb id 135). { injection H as <-. apply (GuU64C.to_chars40kb_u64_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros; (apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]). }
  destruct (Nat.eqb id 142). { injection H as <-. apply (GuI32C.to_chars40kb_i32_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros; (apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]). }
  destruct (Nat.eqb id 143); [|discriminate H]. injection H as <-.
  apply (GuU32C.to_chars40kb_u32_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros; (apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]).
Qed.

(* [comment removed for export] *)
Lemma CT1_ok : forall B id ce', GuNum.CT1 B id = Some ce' -> callee_contract USEGS [] GUBSAN fx_ok RZ AINVH ce'.
Proof.
  intros B id ce'. unfold GuNum.CT1.
  destruct (Nat.eqb id 170).
  { intro H; injection H as <-; unfold lamB; destruct (is_int B).
    - apply (GuNum.GuWNf32.write_number_f32_inttag_callee_L1 RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption)].
    - apply (GuNum.GuWNf32.write_number_f32_u8tag_callee_L1 RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption)]. }
  destruct (Nat.eqb id 171).
  { intro H; injection H as <-; unfold lamB; destruct (is_int B).
    - apply (GuNum.GuWNf64.write_number_f64_inttag_callee_L1 RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption)].
    - apply (GuNum.GuWNf64.write_number_f64_u8tag_callee_L1 RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption)]. }
  destruct (Nat.eqb id 172).
  { intro H; injection H as <-; unfold lamB; destruct (is_int B).
    - apply (GuNum.GuWNi8.write_number_i8_inttag_callee_L1 RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption)].
    - apply (GuNum.GuWNi8.write_number_i8_u8tag_callee_L1 RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption)]. }
  destruct (Nat.eqb id 173).
  { intro H; injection H as <-; unfold lamB; destruct (is_int B).
    - apply (GuNum.GuWNi16.write_number_i16_inttag_callee_L1 RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption)].
    - apply (GuNum.GuWNi16.write_number_i16_u8tag_callee_L1 RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption)]. }
  destruct (Nat.eqb id 174).
  { intro H; injection H as <-; unfold lamB; destruct (is_int B).
    - apply (GuNum.GuWNu8.write_number_u8_inttag_callee_L1 RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption)].
    - apply (GuNum.GuWNu8.write_number_u8_u8tag_callee_L1 RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption)]. }
  destruct (Nat.eqb id 175).
  { intro H; injection H as <-; unfold lamB; destruct (is_int B).
    - apply (GuNum.GuWNu16.write_number_u16_inttag_callee_L1 RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption)].
    - apply (GuNum.GuWNu16.write_number_u16_u8tag_callee_L1 RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption)]. }
  intro H. exact (CT_ok id ce' H).
Qed.

Lemma CT2_ok : forall B id c, GuNum.CT2 B id = Some c -> callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (c2_merged c).
Proof.
  intros B id c. unfold GuNum.CT2.
  destruct (Nat.eqb id 150).
  { intro H; injection H as <-; unfold lamB; destruct (is_int B).
    - apply (GuNum.GuWNf32.write_number_f32_inttag_callee_L RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption) | exact ZMIJF_callee | exact ZMIJD_callee].
    - apply (GuNum.GuWNf32.write_number_f32_u8tag_callee_L RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption) | exact ZMIJF_callee | exact ZMIJD_callee]. }
  destruct (Nat.eqb id 151).
  { intro H; injection H as <-; unfold lamB; destruct (is_int B).
    - apply (GuNum.GuWNf32.write_number_f32_inttag_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption) | exact ZMIJF_callee | exact ZMIJD_callee].
    - apply (GuNum.GuWNf32.write_number_f32_u8tag_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption) | exact ZMIJF_callee | exact ZMIJD_callee]. }
  destruct (Nat.eqb id 152).
  { intro H; injection H as <-; unfold lamB; destruct (is_int B).
    - apply (GuNum.GuWNf64.write_number_f64_inttag_callee_L RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption) | exact ZMIJF_callee | exact ZMIJD_callee].
    - apply (GuNum.GuWNf64.write_number_f64_u8tag_callee_L RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption) | exact ZMIJF_callee | exact ZMIJD_callee]. }
  destruct (Nat.eqb id 153).
  { intro H; injection H as <-; unfold lamB; destruct (is_int B).
    - apply (GuNum.GuWNf64.write_number_f64_inttag_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption) | exact ZMIJF_callee | exact ZMIJD_callee].
    - apply (GuNum.GuWNf64.write_number_f64_u8tag_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption) | exact ZMIJF_callee | exact ZMIJD_callee]. }
  destruct (Nat.eqb id 154).
  { intro H; injection H as <-; unfold lamB; destruct (is_int B).
    - apply (GuNum.GuWNi8.write_number_i8_inttag_callee_L RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption) | exact ZMIJF_callee | exact ZMIJD_callee].
    - apply (GuNum.GuWNi8.write_number_i8_u8tag_callee_L RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption) | exact ZMIJF_callee | exact ZMIJD_callee]. }
  destruct (Nat.eqb id 155).
  { intro H; injection H as <-; unfold lamB; destruct (is_int B).
    - apply (GuNum.GuWNi8.write_number_i8_inttag_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption) | exact ZMIJF_callee | exact ZMIJD_callee].
    - apply (GuNum.GuWNi8.write_number_i8_u8tag_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption) | exact ZMIJF_callee | exact ZMIJD_callee]. }
  destruct (Nat.eqb id 156).
  { intro H; injection H as <-; unfold lamB; destruct (is_int B).
    - apply (GuNum.GuWNi16.write_number_i16_inttag_callee_L RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption) | exact ZMIJF_callee | exact ZMIJD_callee].
    - apply (GuNum.GuWNi16.write_number_i16_u8tag_callee_L RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption) | exact ZMIJF_callee | exact ZMIJD_callee]. }
  destruct (Nat.eqb id 157).
  { intro H; injection H as <-; unfold lamB; destruct (is_int B).
    - apply (GuNum.GuWNi16.write_number_i16_inttag_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption) | exact ZMIJF_callee | exact ZMIJD_callee].
    - apply (GuNum.GuWNi16.write_number_i16_u8tag_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption) | exact ZMIJF_callee | exact ZMIJD_callee]. }
  destruct (Nat.eqb id 158).
  { intro H; injection H as <-; unfold lamB; destruct (is_int B).
    - apply (GuNum.GuWNu8.write_number_u8_inttag_callee_L RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption) | exact ZMIJF_callee | exact ZMIJD_callee].
    - apply (GuNum.GuWNu8.write_number_u8_u8tag_callee_L RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption) | exact ZMIJF_callee | exact ZMIJD_callee]. }
  destruct (Nat.eqb id 159).
  { intro H; injection H as <-; unfold lamB; destruct (is_int B).
    - apply (GuNum.GuWNu8.write_number_u8_inttag_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption) | exact ZMIJF_callee | exact ZMIJD_callee].
    - apply (GuNum.GuWNu8.write_number_u8_u8tag_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption) | exact ZMIJF_callee | exact ZMIJD_callee]. }
  destruct (Nat.eqb id 160).
  { intro H; injection H as <-; unfold lamB; destruct (is_int B).
    - apply (GuNum.GuWNu16.write_number_u16_inttag_callee_L RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption) | exact ZMIJF_callee | exact ZMIJD_callee].
    - apply (GuNum.GuWNu16.write_number_u16_u8tag_callee_L RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption) | exact ZMIJF_callee | exact ZMIJD_callee]. }
  destruct (Nat.eqb id 161).
  { intro H; injection H as <-; unfold lamB; destruct (is_int B).
    - apply (GuNum.GuWNu16.write_number_u16_inttag_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption) | exact ZMIJF_callee | exact ZMIJD_callee].
    - apply (GuNum.GuWNu16.write_number_u16_u8tag_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm); intros; first [(apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]) | (apply OBL2_all; assumption) | exact ZMIJF_callee | exact ZMIJD_callee]. }
  intro H; discriminate H.
Qed.

Lemma num_callee : forall m B sh, holes_only sh = true -> CHK m B (B2JUT.GuNumT.tin m B) (GuNum.PLAN B m) = COk sh ->
  callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (B2JUT.GuNumT.ce m B).
Proof.
  intros m B sh HSH CERT.
  refine (contract_of_cert_xb USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (B2JUT.GuNumT.ce m B) (B2JUT.GuNumT.IT B) (B2JUT.GuNumT.IT_ok B) LIMIT 0%nat BFUEL FUELN (GuNum.XN B) _ (GuNum.XB B) _ (GuNum.PLAN B m) _ (num_gplan B m) HSH CERT).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold GuNum.XN.
    apply (XNc_sound USEGS (B2JUT.GuNumT.IT B) AUBSAN ubsan_in_hull ubsan_hull_ok (B2JUT.GuNumT.IT_ok B) B2JUT.GuNumT.NXF [] GUBSAN B2JUT.GuNumT.BCAP B2JUT.GuNumT.CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa GuNum.CT).
    + intros id ce' H. exact (CT_ok id ce' H).
    + (apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold GuNum.XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok B2JUT.GuNumT.NXF [] GUBSAN B2JUT.GuNumT.BCAP B2JUT.GuNumT.CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa (GuNum.CT2 B)).
    + intros id c H. exact (CT2_ok B id c H).
    + (apply OBL2_all; assumption).
Qed.
Lemma num_callee1 : forall B sh, holes_only sh = true -> CHK1 B (B2JUT.GuNumT.tin ML B) (GuNum.PLANL1 B ML) = COk sh ->
  callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (B2JUT.GuNumT.ceL1 B).
Proof.
  intros B sh HSH CERT.
  refine (contract_of_cert_xb USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (B2JUT.GuNumT.ceL1 B) (B2JUT.GuNumT.IT B) (B2JUT.GuNumT.IT_ok B) LIMIT 0%nat BFUEL FUELN (GuNum.XN1 B) _ (GuNum.XB B) _ (GuNum.PLANL1 B ML) _ (num_gplan1 B) HSH CERT).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold GuNum.XN1.
    apply (XNc_sound USEGS (B2JUT.GuNumT.IT B) AUBSAN ubsan_in_hull ubsan_hull_ok (B2JUT.GuNumT.IT_ok B) B2JUT.GuNumT.NXF [] GUBSAN B2JUT.GuNumT.BCAP B2JUT.GuNumT.CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa (GuNum.CT1 B)).
    + intros id ce' H. exact (CT1_ok B id ce' H).
    + (apply GC_all; first [assumption | exact (B2JUT.GuNumT.IT_ok B)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold GuNum.XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok B2JUT.GuNumT.NXF [] GUBSAN B2JUT.GuNumT.BCAP B2JUT.GuNumT.CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa (GuNum.CT2 B)).
    + intros id c H. exact (CT2_ok B id c H).
    + (apply OBL2_all; assumption).
Qed.

Theorem number_u8tag_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (B2JUT.GuNumT.ce MS BNU).
Proof. exact (num_callee MS BNU _ hs0 numu_cert_S). Qed.
Theorem number_inttag_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (B2JUT.GuNumT.ce MS BNI).
Proof. exact (num_callee MS BNI _ hs0 numi_cert_S). Qed.
Theorem number_u8tag_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (B2JUT.GuNumT.ceL1 BNU).
Proof. exact (num_callee1 BNU _ hs1 numu_cert_L1). Qed.

Theorem number_inttag_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (B2JUT.GuNumT.ceL1 BNI).
Proof. exact (num_callee1 BNI _ hs1 numi_cert_L1). Qed.

End Contract.
End GuNumC.
Module GuReadC.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuFMS GuFMSC GuRead.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Lemma read_cert :
  check USEGS IT AUBSAN NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce ce) 0%nat 600%nat 3000%nat None tin plan_read = COk (SHole 0).
Proof. vm_compute. reflexivity. Qed.
Lemma read_gplan : gplan_ok plan_read = true. Proof. vm_compute. reflexivity. Qed.
Lemma read_shape : holes_only (SHole 0) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.

Lemma CT2_sound : forall id c, CT2 id = Some c -> callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (c2_merged c).
Proof.
  intros id c H. unfold CT2 in H. destruct (Nat.eqb id 101); [|discriminate H]. injection H as <-.
  exact (fms_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm GC_all OBL2_all).
Qed.

Theorem read_callee : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH ce.
Proof.
  refine (contract_of_cert_xb USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            ce IT IT_ok LIMIT 0%nat 600%nat 3000%nat XN _ XB _ plan_read _ read_gplan read_shape read_cert).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS IT AUBSAN ubsan_in_hull ubsan_hull_ok IT_ok NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. discriminate H.
    + (apply GC_all; first [assumption | exact IT_ok]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2).
    + exact CT2_sound.
    + (apply OBL2_all; assumption).
Qed.
End Contract.
End GuReadC.
Module GuStrCtorC.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon.GuStrCtor.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
(* [comment removed for export] *)
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.

Theorem str_ctor_callee : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH ce.
Proof.
  refine (contract_of_cert USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            ce IT IT_ok LIMIT 0%nat BFUEL FUEL XN _ plan_ctor _ ctor_gplan ctor_shape ctor_cert).
  intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
  apply (XNc_sound USEGS IT AUBSAN ubsan_in_hull ubsan_hull_ok IT_ok NXF [] GUBSAN 0 0 fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
            ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
  - intros id ce' H. discriminate H.
  - (apply GC_all; first [assumption | exact IT_ok]).
Qed.
End Contract.
End GuStrCtorC.
Module GuVecCtorC.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon.GuVecCtor.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Import VecCtorU.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.

Theorem vec_ctor_callee : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH ce.
Proof.
  refine (contract_of_cert USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            ce IT IT_ok LIMIT 0%nat BFUEL FUEL XN _ plan _ gplan hshape cert).
  intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
  apply (XNc_sound USEGS IT AUBSAN ubsan_in_hull ubsan_hull_ok IT_ok NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
            ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
  - intros id ce' H. discriminate H.
  - (apply GC_all; first [assumption | exact IT_ok]).
Qed.
End Contract.
End GuVecCtorC.
Module GuVecPushC.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon.   (* [comment removed for export] *)
Import GuVecPush.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Import VecPushU.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.

Lemma vec_push_callee_w : forall w,
  check USEGS IT AUBSAN (NXF w) LIMIT (XN w) (B2JCutShare.GlzCallCert.XE0) (B2JCutShare.GlzCallCert.XB0) XC0 (HSce (ce w)) 0%nat BFUEL FUEL None (tin w) (plan w) = COk SHAPE ->
  callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (ce w).
Proof.
  intros w CERT.
  refine (contract_of_cert USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (ce w) IT IT_ok LIMIT 0%nat BFUEL FUEL (XN w) _ (plan w) _ (gplan w) hshape CERT).
  intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
  apply (XNc_sound USEGS IT AUBSAN ubsan_in_hull ubsan_hull_ok IT_ok (NXF w) [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
            ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
  - intros id ce' H. discriminate H.
  - (apply GC_all; first [assumption | exact IT_ok]).
Qed.
Theorem vec_push_full_callee : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (ce true).
Proof. exact (vec_push_callee_w true cert_full). Qed.
Theorem vec_push_empty_callee : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (ce false).
Proof. exact (vec_push_callee_w false cert_empty). Qed.
End Contract.
End GuVecPushC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GuWA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GuWAi32.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuI32 GuI32C OSSVerify.Proofs.glaze.binary_reflection.lib.GuWA OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuWAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuWAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := B2JUT.GuWAT.cfg_i32.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 132 then Some GuI32.ce else if Nat.eqb id 142 then Some GuI32.ceS else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF GUBSAN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan :=
  PRun [] (PBump BMP (match m with ML => PExt 132 [VAL; A1; S1; D1; IXv] k | MS => PExt 142 [VAL; ELit 0; EVar 130; ELit 0; IXv] k end)).

#[local] Notation CHK m := (check USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuWA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuWA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GuWA.ce cfg MS) 0 (GuWA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GuWA.ceL1 cfg) 0 (GuWA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GuWA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWA.ceL1 cfg) (GuWA.IT cfg) (GuWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuWA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWA.IT_ok cfg) GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 132). { injection H as <-. apply (GuI32C.to_chars40kb_i32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]). }
      destruct (Nat.eqb id 142); [|discriminate H]. injection H as <-.
      apply (GuI32C.to_chars40kb_i32_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWA.ce cfg MS) (GuWA.IT cfg) (GuWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuWA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWA.IT_ok cfg) GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 132). { injection H as <-. apply (GuI32C.to_chars40kb_i32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]). }
      destruct (Nat.eqb id 142); [|discriminate H]. injection H as <-.
      apply (GuI32C.to_chars40kb_i32_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuWA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWA.IT_ok cfg) GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 132). { injection H as <-. apply (GuI32C.to_chars40kb_i32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]). }
      destruct (Nat.eqb id 142); [|discriminate H]. injection H as <-.
      apply (GuI32C.to_chars40kb_i32_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GuWA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_array_i32_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_array_i32_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GuWAi32.
Module GuWAi64.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuI64 GuI64C OSSVerify.Proofs.glaze.binary_reflection.lib.GuWA OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuWAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuWAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := B2JUT.GuWAT.cfg_i64.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 134 then Some GuI64.ce else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF GUBSAN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan := PRun [] (PBump BMP (PExt 134 [VAL; A1; S1; D1; IXv] k)).

#[local] Notation CHK m := (check USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuWA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuWA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GuWA.ce cfg MS) 0 (GuWA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GuWA.ceL1 cfg) 0 (GuWA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GuWA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWA.ceL1 cfg) (GuWA.IT cfg) (GuWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuWA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWA.IT_ok cfg) GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 134); [|discriminate H]. injection H as <-.
      apply (GuI64C.to_chars40kb_i64_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWA.ce cfg MS) (GuWA.IT cfg) (GuWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuWA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWA.IT_ok cfg) GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 134); [|discriminate H]. injection H as <-.
      apply (GuI64C.to_chars40kb_i64_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuWA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWA.IT_ok cfg) GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 134); [|discriminate H]. injection H as <-.
      apply (GuI64C.to_chars40kb_i64_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GuWA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_array_i64_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_array_i64_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GuWAi64.
Module GuWAu32.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuU32 GuU32C OSSVerify.Proofs.glaze.binary_reflection.lib.GuWA OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuWAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuWAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := B2JUT.GuWAT.cfg_u32.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 133 then Some GuU32.ce else if Nat.eqb id 143 then Some GuU32.ceS else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF GUBSAN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan :=
  PRun [] (PBump BMP (match m with ML => PExt 133 [VAL; A1; S1; D1; IXv] k | MS => PExt 143 [VAL; ELit 0; EVar 130; ELit 0; IXv] k end)).

#[local] Notation CHK m := (check USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuWA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuWA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GuWA.ce cfg MS) 0 (GuWA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GuWA.ceL1 cfg) 0 (GuWA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GuWA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWA.ceL1 cfg) (GuWA.IT cfg) (GuWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuWA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWA.IT_ok cfg) GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 133). { injection H as <-. apply (GuU32C.to_chars40kb_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]). }
      destruct (Nat.eqb id 143); [|discriminate H]. injection H as <-.
      apply (GuU32C.to_chars40kb_u32_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWA.ce cfg MS) (GuWA.IT cfg) (GuWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuWA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWA.IT_ok cfg) GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 133). { injection H as <-. apply (GuU32C.to_chars40kb_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]). }
      destruct (Nat.eqb id 143); [|discriminate H]. injection H as <-.
      apply (GuU32C.to_chars40kb_u32_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuWA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWA.IT_ok cfg) GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 133). { injection H as <-. apply (GuU32C.to_chars40kb_u32_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]). }
      destruct (Nat.eqb id 143); [|discriminate H]. injection H as <-.
      apply (GuU32C.to_chars40kb_u32_callee_S RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GuWA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_array_u32_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_array_u32_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GuWAu32.
Module GuWAu64.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuU64 GuU64C OSSVerify.Proofs.glaze.binary_reflection.lib.GuWA OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuWAT.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GpCalleeSub.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT.GuWAX OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Definition cfg : acfg := B2JUT.GuWAT.cfg_u64.     (* [comment removed for export] *)
Definition CT (id : nat) : option gcallee := if Nat.eqb id 135 then Some GuU64.ce else None.
Definition XN : nat -> list expr -> acs -> option acs := XNc USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF GUBSAN BCAP CCAP CT.
Definition BMP : nat := 170.   (* [comment removed for export] *)
Definition elem (m : smode) (k : plan) : plan := PRun [] (PBump BMP (PExt 135 [VAL; A1; S1; D1; IXv] k)).

#[local] Notation CHK m := (check USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuWA.ce cfg m)) 0%nat BFUEL FUELA None).
#[local] Notation CHK1 := (check USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HSce (GuWA.ceL1 cfg)) 0%nat BFUEL FUELA None).

#[local] Notation CHKX c k := (check USEGS (GuWA.IT cfg) AUBSAN GuWA.NXF LIMIT XN (B2JCutShare.GlzCallCert.XE0) XB XC0 (HScut c (XCUTS cfg elem) k) 0%nat BFUEL FUELA None).
(* [comment removed for export] *)
Lemma gplan_XS : gplan_ok (XPLAN_S cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XL1 : gplan_ok (XPLAN_L1 cfg) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gplan_XC : gplan_ok (XLOOPC cfg elem) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cert_SX : CHKX (GuWA.ce cfg MS) 0 (GuWA.tin cfg MS) (XPLAN_S cfg elem) = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma cert_L1X : CHKX (GuWA.ceL1 cfg) 0 (GuWA.tin cfg ML) (XPLAN_L1 cfg) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.
Lemma cert_CX : CHKX (GuWA.ceL1 cfg) 1 (XTL cfg) (XLOOPC cfg elem) = COk (SHole 1).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 1))). Qed.

Lemma hs0 : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
Lemma hs1 : holes_only (SHole 1) = true. Proof. reflexivity. Qed.

Section Contract.
Context {RC : run_ceil}.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT USEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins [] (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis AINVH_perm : forall L L' B C M mdl, Permutation.Permutation L L' -> AINVH L B C M mdl -> AINVH L' B C M mdl.
Hypothesis GC_all : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  AX2.itab_sound USEGS IT -> 0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Hypothesis OBL2_all : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV,
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT -> (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f [] GUBSAN AINVH PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.


(* [comment removed for export] *)
Lemma xL1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ceL1 cfg).
Proof.
  refine (contract_of_cert_xb_cut USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWA.ceL1 cfg) (GuWA.IT cfg) (GuWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN _ XB _ (XCUTS cfg elem) _ (XPLAN_L1 cfg) _ gplan_XL1 hs1 cert_L1X).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XN.
    apply (XNc_sound USEGS (GuWA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWA.IT_ok cfg) GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 135); [|discriminate H]. injection H as <-.
      apply (GuU64C.to_chars40kb_u64_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. exact cert_CX.
Qed.
(* [comment removed for export] *)
Lemma xS : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ce cfg MS).
Proof.
  unfold callee_contract.
  refine (contract_of_cert_when_cutX USEGS AUBSAN ubsan_in_hull ubsan_hull_ok [] GUBSAN fx_ok RZ RZ_step RZ_msteps RZ_exit RZ_conseq (RUN_sound_fx USEGS)
            AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil
            (GuWA.ce cfg MS) (GuWA.IT cfg) (GuWA.IT_ok cfg) LIMIT 0%nat BFUEL FUELA XN QTRUE _ _ XB _ XN _ XB _ (XCUTS cfg elem) _ (XPLAN_S cfg elem) _ gplan_XS hs0 cert_SX).
  - intros E E' _ _. exact I.
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuWA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWA.IT_ok cfg) GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 135); [|discriminate H]. injection H as <-.
      apply (GuU64C.to_chars40kb_u64_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XN.
    apply (XNc_sound USEGS (GuWA.IT cfg) AUBSAN ubsan_in_hull ubsan_hull_ok (GuWA.IT_ok cfg) GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT).
    + intros id ce' H. unfold CT in H. destruct (Nat.eqb id 135); [|discriminate H]. injection H as <-.
      apply (GuU64C.to_chars40kb_u64_callee RZ RZ_step RZ_msteps RZ_exit RZ_conseq AINVH AINVH_frame AINVH_zone AINVH_disj AINVH_perm). intros. (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
    + (apply GC_all; first [assumption | exact (GuWA.IT_ok cfg)]).
  - intros PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa _. unfold XB.
    apply (XBc_sound USEGS AUBSAN ubsan_in_hull ubsan_hull_ok GuWA.NXF [] GUBSAN BCAP CCAP fx_ok RZ RZ_step AINVH AINVH_zone AINVH_disj AINVH_perm
              ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull nil_SWIN_img ubsan_SEGS_out PERMf TOPf FS0 FDS0 HID M0 B0 C0 HB0 HC0 HBc HCc UINV HUa CT2_0).
    + intros id c H. discriminate H.
    + (apply OBL2_all; assumption).
  - intros i T k H. destruct i as [|i]; [|destruct i; discriminate H]. injection H as <- <-.
    exists (SHole 1). split; [exact gplan_XC|]. split; [reflexivity|]. right.
    exists (HScut (GuWA.ceL1 cfg) (XCUTS cfg elem) 1). split; [exact (xhs_sub cfg (XCUTS cfg elem) eq_refl) | exact cert_CX].
Qed.
Theorem write_array_u64_callee_S : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ce cfg MS).
Proof. exact xS. Qed.
Theorem write_array_u64_callee_L1 : callee_contract USEGS [] GUBSAN fx_ok RZ AINVH (GuWA.ceL1 cfg).
Proof. exact xL1. Qed.

End Contract.
End GuWAu64.
Require Stdlib.NArith.NArith LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzNodesResize OSSVerify.Proofs.glaze.binary_reflection.lib.GlzStrResizeUbsan2 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzStrGrowUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzStrGrowUbsan2 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzStrGrowUbsan3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GlzStrSpecsUbsan.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzNodesAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrameStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzNodesResize OSSVerify.Proofs.glaze.binary_reflection.lib.GlzStrResizeUbsan2 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzStrGrowUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzStrGrowUbsan2 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzStrGrowUbsan3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import GPS. Import GCL.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Plain.
Context {RC : run_ceil}.
(* [comment removed for export] *)
Variable SWIN : list (Z * Z).
Variable RZ : GPS.rz_t.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Variable AINVH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINVH_frame : forall L B C M M' mdl,
  AINVH L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins SWIN (bv_unsigned a)) /\ M' a <> None) ->
  AINVH L B C M' mdl.
Hypothesis AINVH_mono : forall L B C B' C' M mdl, AINVH L B C M mdl -> B <= B' -> C <= C' -> AINVH L B' C' M mdl.
Hypothesis AINVH_zone : forall L B C M mdl b m, AINVH L B C M mdl -> In (b, m) L -> blk_ok GUBSAN b m.
Hypothesis AINVH_disj : forall L B C M mdl L1 L2 b m b' m',
  AINVH L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_ro_hi GUBSAN <= lo /\ hi <= g_img_hi GUBSAN /\ (forall plo phi, In (plo, phi) (g_priv GUBSAN) -> hi <= plo \/ phi <= lo).
(* [comment removed for export] *)
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable HIDc : list (Z * Z).
Variable M0c : word -> option byte.
Variable B0c C0c : Z.
Hypothesis B0c_nonneg : 0 <= B0c.
Hypothesis C0c_nonneg : 0 <= C0c.
Variable bcap ccap : Z.
Hypothesis bcap_ok : B0c + bcap <= GBUDGET.
Hypothesis ccap_ok : C0c + ccap <= GCOUNT.
#[local] Notation AINVc := (AINV_f SWIN GUBSAN AINVH PERMc SPTOPc HIDc M0c B0c C0c).

(* [comment removed for export] *)
Definition RSTK : Z := MSTK_MALLOC + 16.
Hypothesis OPN : GlzSpecsStr.GlzContracts.opnew_mspecR USEGS AINVH fx_ok RZ GUBSAN RSTK GBUDGET GCOUNT 0x749a4.
Hypothesis DEL : GlzSpecsStr.GlzContracts.free_mspecR USEGS AINVH fx_ok RZ GUBSAN MSTK_MALLOC 0x5a5a4.

(* [comment removed for export] *)
Lemma priv_img : forall z, in_wins (g_priv GUBSAN) z -> g_img_lo GUBSAN <= z < g_img_hi GUBSAN.
Proof. intros z (lo & hi & Hin & Hz). destruct (GUBSAN_priv lo hi Hin) as [H1 H2]. cbn [g_img_lo g_ro_hi g_img_hi GUBSAN] in *. lia. Qed.
Lemma priv_below : forall z, in_wins (g_priv GUBSAN) z -> z < CEIL_run.
Proof. intros z Hz. pose proof (priv_img z Hz). pose proof ubsan_G_img_ceil. lia. Qed.
Lemma img_ok : 0 <= g_img_lo GUBSAN <= g_img_hi GUBSAN /\ g_img_hi GUBSAN <= CEIL_run.
Proof. pose proof ubsan_G_img_ceil. cbn [g_img_lo g_img_hi GUBSAN] in *. lia. Qed.

Lemma AINVH_app : forall Lc B C M M' mdl,
  AINVH Lc B C M mdl ->
  (forall a : word, M' a <> M a -> (in_blocks Lc (bv_unsigned a) \/ CEIL_run <= bv_unsigned a) /\ M' a <> None) ->
  AINVH Lc B C M' mdl.
Proof.
  intros Lc B C M M' mdl HA Hch. eapply AINVH_frame; [exact HA|]. intros a Ha. destruct (Hch a Ha) as [[X|X] D]; (split; [|exact D]); [left; exact X | right; left; exact X].
Qed.

Lemma opdel_at : GlzSpecsStr.GlzContracts.free_mspecR USEGS AINVH fx_ok RZ GUBSAN RSTK 0x5a5a4.
Proof.
  unfold RSTK. apply (free_mspecR_mono USEGS AINVH fx_ok RZ GUBSAN priv_below MSTK_MALLOC); [unfold MSTK_MALLOC; lia|]. exact DEL.
Qed.
Lemma RSTK_ok : 0 <= RSTK /\ RSTK + 80 <= MSTK.
Proof. unfold RSTK, MSTK_MALLOC, MSTK. lia. Qed.

(* [comment removed for export] *)
Lemma entry_lit : Z_to_bv 64 0x5c1d8 = (0x5c1d8%bv : word).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma ubsan_keepS : resize_keepS_spec USEGS 0x5c1d8.
Proof.
  intros fx regs M obj sp ret w0 cw s n RD8 Hw0 Hs Hn Hobj Hsp Hapart STF STO Hret H1 H2 H10 H11 H12.
  unfold mkstF. rewrite entry_lit.
  exact (@resize_short_any fx (seg_rom USEGS) regs M obj sp ret w0 cw s n RD8 Hw0 Hs Hn Hobj Hsp Hapart STF STO Hret H1 H2 H10 H11 H12).
Qed.
Lemma ubsan_keepL : resize_keepL_spec USEGS 0x5c1d8.
Proof.
  intros fx regs M obj sp ret d w0 cw cap s n RD8 Hw0 Hcap RDs RDd Hs Hn Hcap62 Hobj Hd Hsp Hapart Hdfr Hdobj STF STO STD Hret H1 H2 H10 H11 H12.
  unfold mkstF. rewrite entry_lit.
  exact (@resize_long_inplace_any fx (seg_rom USEGS) regs M obj sp ret d w0 cw cap s n RD8 Hw0 Hcap RDs RDd Hs Hn Hcap62 Hobj Hd Hsp Hapart Hdfr Hdobj
           STF STO STD Hret H1 H2 H10 H11 H12).
Qed.

(* [comment removed for export] *)
Lemma ubsan_growL_mspec : resize_growL_mspec USEGS AINVH fx_ok RZ GUBSAN RSTK GBUDGET GCOUNT 0x5c1d8.
Proof.
  exact (resize_grow_long AINVH fx_ok GUBSAN RZ RZ_msteps AINVH_app priv_img img_ok RSTK GBUDGET GCOUNT (proj1 RSTK_ok) OPN opdel_at).
Qed.
Lemma ubsan_growS_mspec : resize_growS_mspec USEGS AINVH fx_ok RZ GUBSAN RSTK GBUDGET GCOUNT 0x5c1d8.
Proof.
  exact (resize_grow_short AINVH fx_ok GUBSAN RZ RZ_msteps AINVH_app priv_img img_ok RSTK GBUDGET GCOUNT (proj1 RSTK_ok) OPN).
Qed.

(* [comment removed for export] *)
Theorem ubsan_resize_specs : resize_specs USEGS SWIN PERMc SPTOPc AINVc fx_ok RZ GUBSAN bcap ccap 0x5c1d8.
Proof.
  constructor.
  - exact ubsan_keepS.
  - exact ubsan_keepL.
  - eapply (growS_nspec_of_mspec USEGS SWIN GUBSAN fx_ok RZ AINVH);
      first [exact AINVH_zone | exact AINVH_disj | exact AINVH_mono | exact AINVH_frame | exact ubsan_G_ro_img | exact ubsan_G_img_ceil | exact GUBSAN_priv | exact SWIN_img
            | exact ubsan_SEGS_out | exact B0c_nonneg | exact C0c_nonneg | exact RSTK_ok | exact bcap_ok | exact ccap_ok | exact ubsan_growS_mspec].
  - eapply (growL_nspec_of_mspec USEGS SWIN GUBSAN fx_ok RZ AINVH);
      first [exact AINVH_zone | exact AINVH_disj | exact AINVH_mono | exact AINVH_frame | exact ubsan_G_ro_img | exact ubsan_G_img_ceil | exact GUBSAN_priv | exact SWIN_img
            | exact ubsan_SEGS_out | exact B0c_nonneg | exact C0c_nonneg | exact RSTK_ok | exact bcap_ok | exact ccap_ok | exact ubsan_growL_mspec].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Variable nx0 : nat.
Variable FS0 : Fs.Fs.
Variable FDS0 : list (word * FdEntry).
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.

Theorem ubsan_OBL_str_resize2 : OBL_str_resize2 USEGS nx0 PERMc SPTOPc FS0 FDS0 AINVc fx_ok UINV RZ GUBSAN bcap ccap.
Proof.
  unfold OBL_str_resize2.
  apply (node_str_resize2_sound USEGS nx0 SWIN PERMc SPTOPc FS0 FDS0 AINVc
           (AINV_f_frame SWIN GUBSAN AINVH AINVH_frame AINVH_zone AINVH_disj ubsan_G_ro_img ubsan_G_img_ceil PERMc SPTOPc HIDc M0c B0c C0c)
           (AINV_f_mono SWIN GUBSAN AINVH AINVH_mono PERMc SPTOPc HIDc M0c B0c C0c)
           fx_ok UINV UINV_agree RZ RZ_msteps GUBSAN bcap ccap ubsan_SEGS_out ubsan_G_ro_img ubsan_G_img_ceil ubsan_G_img_hull ubsan_segs_wr_ok).
  exact ubsan_resize_specs.
Qed.

End Plain.
End GlzStrSpecsUbsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzAllocUbsanIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzOpNewUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzNodesLibcUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GlzAllocUbsan.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.MhKInst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzAllocUbsanIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzOpNewUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzNodesAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.GlzNodesLibcUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon GlzStrSpecsUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AP. Import GPS.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section OpNew.
Context {RC : run_ceil}.
(* [comment removed for export] *)
Variable AINV : ainv_t.
Variable SWOK : list (Z * Z) -> Prop.
Hypothesis U : ubmh AINV SWOK.
(* [comment removed for export] *)
Lemma AINV_stack : forall L B C (M M' : word -> option byte) mdl,
  AINV L B C M mdl -> (forall a : word, M' a <> M a -> GlzConst.RunCeil.CEIL <= bv_unsigned a /\ M' a <> None) -> AINV L B C M' mdl.
Proof. exact (um_stack AINV SWOK U). Qed.

Lemma same_csr : GlzSpecsStr.GlzContracts.callee_saved_regs = GlzAllocUbsanIface.callee_saved_regs.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Theorem ubsan_opnew_mspecR : forall bc cc,
  bc <= GBUDGET -> cc <= GCOUNT ->
  opnew_mspecR USEGS AINV fx_ok (realizes USEGS) GUBSAN (MSTK_MALLOC + 16) bc cc 0x749a4.
Proof.
  intros bc cc Hbc Hcc.
  unfold opnew_mspecR. intros fx R M mdl Lc B C ret n sp T PRE HT HK.
  destruct PRE as (Hh & Hl & Hm & HFX & HA & Hra & Hret & Hev & Hn & Hnr & Hsp & Hal & Hceil & Htp & Hstk & HB & HC).
  assert (HPRE : malloc_pre (MSTK_M + 16) R M mdl B C ret n sp).
  { unfold malloc_pre. unfold MSTK_M. unfold MSTK_MALLOC in Hceil, Hstk.
    unfold NMAX in Hnr. unfold MH_NMAX. unfold mcost, GlzIface.MBLK, GBUDGET in HB, Hbc. unfold MH_GBUDGET, GlzAllocUbsanIface.MBLK.
    unfold MCNT, GCOUNT, GlzIface.LMAX in HC, Hcc. unfold GlzAllocUbsanIface.LMAX.
    cbn [g_tp GUBSAN] in Htp. unfold TPV.
    repeat match goal with |- _ /\ _ => split end; try assumption; try lia. }
  unfold mkstF.
  apply (opnew_retry AINV (um_malloc AINV SWOK U fx) AINV_stack R M mdl Lc B C ret n sp HA HPRE T HT).
  intros d Hok.
  destruct Hok as (R' & M' & mdl' & p & -> & RK & H10 & Hp16 & Hblk & Hdisj & Hdef & CH & ST & HA' & Hh' & Hl' & Hm' & Hfs' & Hfd').
  apply (HK fx R' M' mdl' p).
  unfold alloc_post_ok.
  repeat match goal with |- _ /\ _ => split end; try assumption;
  lazymatch goal with
  | |- forall r, In r _ -> _ => rewrite same_csr; exact RK
  | |- GlzSpecsStr.GlzContracts.blk_ok _ _ _ =>
      unfold GlzSpecsStr.GlzContracts.blk_ok; cbn [g_img_lo g_img_hi GUBSAN]; unfold PTRLO; unfold GlzAllocUbsanIface.blk_ok, HEAPLO in Hblk; lia
  | |- forall a : word, M' a <> M a -> _ =>
      intros a Ha; pose proof (CH a Ha) as X; unfold mh_changed in X; unfold alloc_changed;
      cbn [g_img_lo g_img_hi g_priv GUBSAN]; unfold MSTK_M in X; unfold MSTK_MALLOC;
      unfold GlzAllocUbsanIface.in_blocks in X; unfold GPS.in_blocks, GPS.in_wins;
      unfold CTX_END, CTX, A_ERRNO, TPV in X;
      destruct X as [(X1 & X2 & X3)|[X|[X|X]]];
      [ left; split; [lia | split; [lia | exact X3]]
      | right; left; lia
      | right; right; exists 0xaae90, 0xab240; split; [cbv; tauto | lia]
      | right; right; exists 0x8aaec, 0xaabd4; split; [cbv; tauto | lia] ]
  | |- forall a : word, _ -> RiscvSemantics.store_ok _ _ _ _ = true =>
      intros a Ha; apply ST; unfold MSTK_M; unfold MSTK_MALLOC in Ha; lia
  | |- AINV _ _ _ _ _ => unfold mcost, GlzIface.MBLK, MCNT; unfold GlzAllocUbsanIface.MBLK in HA'; exact HA'
  | |- _ => idtac
  end.
Qed.
End OpNew.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Free.
Context {RC : run_ceil}.
Variable AINV : ainv_t.
Variable SWOK : list (Z * Z) -> Prop.
Hypothesis U : ubmh AINV SWOK.
Variable RZ : GPS.rz_t.
Hypothesis RZ_kc : forall T, kclosed USEGS (fun c => RZ c T).
(* [comment removed for export] *)
Let HF : forall fx : FPState, @FREE_KAT fx RC AINV MSTK_M := um_free AINV SWOK U.

Lemma same_csr' : GlzSpecsStr.GlzContracts.callee_saved_regs = GlzAllocUbsanIface.callee_saved_regs.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma free_mspecR_via : forall e : Z,
  (forall (fx : FPState) R M, msteps USEGS (@mkst fx R (Z_to_bv 64 e) M (seg_rom USEGS)) (@mkst fx R (Z_to_bv 64 0x66190) M (seg_rom USEGS))) ->
  free_mspecR USEGS AINV fx_ok RZ GUBSAN MSTK_MALLOC e.
Proof.
  intros e STEPS. unfold free_mspecR.
  intros fx R M mdl Lc Lc' B C B' C' ret sp p T Hh Hl Hm HFX HA Hra Hret Hev H10 Hcase Hsp Hal Hceil Htp Hstk HK.
  unfold mkstF. apply (K_msteps USEGS (fun c => RZ c T) _ _ mdl (RZ_kc T) Hh Hl (STEPS fx R M)).
  assert (HPRE : free_pre MSTK_M R M mdl Lc Lc' B C B' C' ret sp p).
  { unfold free_pre. unfold MSTK_M. unfold MSTK_MALLOC in Hceil, Hstk. unfold mcost, GlzIface.MBLK, MCNT in Hcase. unfold GlzAllocUbsanIface.MBLK.
    cbn [g_tp GUBSAN] in Htp. unfold TPV.
    repeat match goal with |- _ /\ _ => split end; try assumption; lia. }
  pose proof (HF fx R M mdl Lc Lc' B C B' C' ret sp p HA HPRE) as KAT.
  unfold free_cfg, A_FREE in KAT. apply (KAT (fun c => RZ c T) (RZ_kc T)).
  intros c' (R' & M' & mdl' & -> & RK & CH & ST & HA' & Hh' & Hl' & Hm' & Hfs' & Hfd').
  apply (HK fx R' M' mdl' HFX).
  - rewrite same_csr'. exact RK.
  - intros a Ha. pose proof (CH a Ha) as X. unfold mh_changed in X. unfold alloc_changed.
    cbn [g_img_lo g_img_hi g_priv GUBSAN]. unfold MSTK_M in X. unfold MSTK_MALLOC.
    unfold GlzAllocUbsanIface.in_blocks in X. unfold GPS.in_blocks, GPS.in_wins.
    unfold CTX_END, CTX, A_ERRNO, TPV in X.
    destruct X as [(X1 & X2 & X3)|[X|[X|X]]];
      [ left; split; [lia | split; [lia | exact X3]]
      | right; left; lia
      | right; right; exists 0xaae90, 0xab240; split; [cbv; tauto | lia]
      | right; right; exists 0x8aaec, 0xaabd4; split; [cbv; tauto | lia] ].
  - intros a Ha. apply ST. unfold MSTK_M. unfold MSTK_MALLOC in Ha. lia.
  - exact HA'.
  - exact Hh'. - exact Hl'. - exact Hm'. - exact Hfs'. - exact Hfd'.
Qed.

Theorem ubsan_free_mspecR : free_mspecR USEGS AINV fx_ok RZ GUBSAN MSTK_MALLOC 0x66190.
Proof. apply free_mspecR_via. intros fx R M. apply mst_refl. Qed.

Lemma zbv_w : forall z (w : word), bv_unsigned w = z -> Z_to_bv 64 z = w.
Proof. intros z w <-. apply Z_to_bv_bv_unsigned. Qed.

Theorem ubsan_opdel_mspecR : free_mspecR USEGS AINV fx_ok RZ GUBSAN MSTK_MALLOC 0x5a5a4.
Proof.
  apply free_mspecR_via. intros fx R M.
  rewrite (zbv_w 0x5a5a4 (0x5a5a4%bv : word) eq_refl), (zbv_w 0x66190 (0x66190%bv : word) eq_refl). apply opdel_jj.
Qed.
Theorem ubsan_opdel_sized_mspecR : free_mspecR USEGS AINV fx_ok RZ GUBSAN MSTK_MALLOC 0x5a5a0.
Proof.
  apply free_mspecR_via. intros fx R M.
  rewrite (zbv_w 0x5a5a0 (0x5a5a0%bv : word) eq_refl), (zbv_w 0x66190 (0x66190%bv : word) eq_refl). apply opdel_sized_j.
Qed.
End Free.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section GC.
Context {RC : run_ceil}.
Variable AINV : ainv_t.
Variable SWOK : list (Z * Z) -> Prop.
Hypothesis U : ubmh AINV SWOK.
Variable SWIN : list (Z * Z).
Hypothesis SWIN_ok : SWOK SWIN.
Hypothesis SWIN_img : forall lo hi, In (lo, hi) SWIN -> g_ro_hi GUBSAN <= lo /\ hi <= g_img_hi GUBSAN /\ (forall plo phi, In (plo, phi) (g_priv GUBSAN) -> hi <= plo \/ phi <= lo).
#[local] Notation RZ := (realizes USEGS).

(* [comment removed for export] *)
Lemma RZ_step_rr : GPS.RZ_STEP USEGS RZ.
Proof. intros ms model ms' T. apply rz_step. Qed.
Lemma RZ_msteps_rr : GPS.RZ_MSTEPS USEGS RZ.
Proof. intros ms ms' model T. apply rz_msteps. Qed.
Lemma RZ_exit_rr : GPS.RZ_EXIT USEGS RZ.
Proof. intros ms model x8. apply rz_exit. Qed.
Lemma RZ_conseq_rr : GPS.RZ_CONSEQ RZ.
Proof. intros c T T'. apply rz_conseq. Qed.
Lemma rr_kc : forall T, kclosed USEGS (fun c => realizes USEGS c T).
Proof. exact (kclosed_realizes USEGS). Qed.

(* [comment removed for export] *)
Lemma P_frame : forall L B C M M' mdl,
  AINV L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins SWIN (bv_unsigned a)) /\ M' a <> None) ->
  AINV L B C M' mdl.
Proof. intros L B C M M' mdl HA H. exact (um_frame AINV SWOK U SWIN L B C M M' mdl SWIN_ok HA H). Qed.
Lemma P_zone : forall L B C M mdl b m, AINV L B C M mdl -> In (b, m) L -> GlzSpecsStr.GlzContracts.blk_ok GUBSAN b m.
Proof.
  intros L B C M mdl b m HA Hin. destruct (um_zone AINV SWOK U L B C M mdl b m HA Hin) as (Z1 & Z2 & Z3).
  unfold GlzSpecsStr.GlzContracts.blk_ok. cbn [g_img_lo g_img_hi GUBSAN]. unfold HEAPLO in Z1. unfold PTRLO. lia.
Qed.
Lemma P_disj : forall L B C M mdl L1 L2 b m b' m',
  AINV L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Proof. exact (um_disj AINV SWOK U). Qed.
Lemma P_mono : forall L B C B' C' M mdl, AINV L B C M mdl -> B <= B' -> C <= C' -> AINV L B' C' M mdl.
Proof. exact (um_mono AINV SWOK U). Qed.

Lemma MM_ok : 0 <= MSTK_MALLOC <= GlzIface.MSTK. Proof. unfold MSTK_MALLOC, GlzIface.MSTK. lia. Qed.
Lemma RSTK16_ok : 0 <= MSTK_MALLOC + 16 <= GlzIface.MSTK. Proof. unfold MSTK_MALLOC, GlzIface.MSTK. lia. Qed.

(* [comment removed for export] *)
Theorem GC_ALL : forall IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 (UINV : env -> Prop),
  itab_sound USEGS IT ->
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  gcontracts USEGS IT AUBSAN NXF PERMf TOPf FS0 FDS0 (AINV_f SWIN GUBSAN AINV PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Proof.
  intros IT NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV IT_ok HB0 HC0 HBc HCc HUa.
  pose proof (AINV_f_frame SWIN GUBSAN AINV P_frame P_zone P_disj ubsan_G_ro_img ubsan_G_img_ceil PERMf TOPf HID M0 B0 C0) as AFR.
  pose proof (fun entry FS => free_nspec_of_mspec USEGS SWIN GUBSAN fx_ok RZ AINV P_mono P_zone ubsan_G_ro_img ubsan_G_img_ceil GUBSAN_priv SWIN_img ubsan_SEGS_out
                                PERMf TOPf HID M0 B0 C0 HB0 HC0 MSTK_MALLOC MM_ok entry FS) as FNS.
  pose proof (opnew_nspec_of_mspec USEGS SWIN GUBSAN fx_ok RZ AINV P_zone P_disj ubsan_G_ro_img ubsan_G_img_ceil GUBSAN_priv SWIN_img ubsan_SEGS_out
                PERMf TOPf HID M0 B0 C0 (MSTK_MALLOC + 16) RSTK16_ok bc cc HBc HCc 0x749a4
                (ubsan_opnew_mspecR AINV SWOK U GBUDGET GCOUNT ltac:(lia) ltac:(lia))) as ONS.
  constructor.
  - exact (node_imgload_sound USEGS IT IT_ok NXF SWIN PERMf TOPf FS0 FDS0 _ AFR fx_ok UINV HUa RZ RZ_step_rr GUBSAN ubsan_rom_ok ltac:(cbn; lia)).
  - apply (node_opnew_sound USEGS NXF SWIN PERMf TOPf FS0 FDS0 _ fx_ok UINV HUa RZ GUBSAN bc cc); [cbn; lia | cbn; lia | exact ONS].
  - apply (node_free_sound USEGS NXF SWIN PERMf TOPf FS0 FDS0 _ fx_ok UINV HUa RZ GUBSAN); exact (FNS 0x66190 (ubsan_free_mspecR AINV SWOK U RZ rr_kc)).
  - exact (node_blkfact_sound USEGS NXF PERMf TOPf FS0 FDS0 _ fx_ok UINV RZ GUBSAN ubsan_G_img_hull ltac:(cbn; lia)
             (AINV_f_zone SWIN GUBSAN AINV P_zone PERMf TOPf HID M0 B0 C0)
             (AINV_f_disj SWIN GUBSAN AINV P_disj PERMf TOPf HID M0 B0 C0)
             (AINV_f_perm_apart SWIN GUBSAN AINV P_zone P_disj ubsan_G_ro_img SWIN_img PERMf TOPf HID M0 B0 C0)
             (AINV_f_top SWIN GUBSAN AINV PERMf TOPf HID M0 B0 C0)).
  - apply (node_opdel_sound USEGS NXF SWIN PERMf TOPf FS0 FDS0 _ fx_ok UINV HUa RZ GUBSAN). exact (FNS 0x5a5a4 (ubsan_opdel_mspecR AINV SWOK U RZ rr_kc)).
  - apply (node_opdel_sized_sound USEGS NXF SWIN PERMf TOPf FS0 FDS0 _ fx_ok UINV HUa RZ GUBSAN). exact (FNS 0x5a5a0 (ubsan_opdel_sized_mspecR AINV SWOK U RZ rr_kc)).
  - exact (ubsan_OBL_memcpy AUBSAN NXF SWIN PERMf TOPf FS0 FDS0 _ AFR fx_ok UINV HUa RZ RZ_msteps_rr GUBSAN eq_refl).
  - exact (ubsan_OBL_memset AUBSAN NXF SWIN PERMf TOPf FS0 FDS0 _ AFR fx_ok UINV HUa RZ RZ_msteps_rr GUBSAN eq_refl).
  - exact (ubsan_OBL_memmove AUBSAN NXF SWIN PERMf TOPf FS0 FDS0 _ AFR fx_ok UINV HUa RZ RZ_msteps_rr GUBSAN eq_refl ubsan_in_hull ubsan_hull_ok).
  - exact (ubsan_OBL_strlen NXF SWIN PERMf TOPf FS0 FDS0 _ AFR fx_ok UINV HUa RZ RZ_msteps_rr GUBSAN eq_refl (conj eq_refl eq_refl) eq_refl).
Qed.

(* [comment removed for export] *)
Theorem OBL2_ALL : forall NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 (UINV : env -> Prop),
  0 <= B0 -> 0 <= C0 -> B0 + bc <= GBUDGET -> C0 + cc <= GCOUNT ->
  (forall E E', env_agree NXF E E' -> UINV E -> UINV E') ->
  OBL_str_resize2 USEGS NXF PERMf TOPf FS0 FDS0 (AINV_f SWIN GUBSAN AINV PERMf TOPf HID M0 B0 C0) fx_ok UINV RZ GUBSAN bc cc.
Proof.
  intros NXF bc cc PERMf TOPf HID M0 B0 C0 FS0 FDS0 UINV HB0 HC0 HBc HCc HUa.
  exact (ubsan_OBL_str_resize2 SWIN RZ RZ_msteps_rr AINV P_frame P_mono P_zone P_disj SWIN_img PERMf TOPf HID M0 B0 C0 HB0 HC0 bc cc HBc HCc
           (ubsan_opnew_mspecR AINV SWOK U GBUDGET GCOUNT (Z.le_refl _) (Z.le_refl _)) (ubsan_opdel_mspecR AINV SWOK U RZ rr_kc) NXF FS0 FDS0 UINV HUa).
Qed.
End GC.
End GlzAllocUbsan.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzAllocUbsanIface OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.GlzAllocUbsanIface GlzAllocUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GuTc32 OSSVerify.Proofs.glaze.binary_reflection.lib.GuNum OSSVerify.Proofs.glaze.binary_reflection.lib.GuU32 OSSVerify.Proofs.glaze.binary_reflection.lib.GuI32 OSSVerify.Proofs.glaze.binary_reflection.lib.GuU64 OSSVerify.Proofs.glaze.binary_reflection.lib.GuI64 OSSVerify.Proofs.glaze.binary_reflection.lib.GuWFT OSSVerify.Proofs.glaze.binary_reflection.lib.GuWDT OSSVerify.Proofs.glaze.binary_reflection.lib.GuTc16 OSSVerify.Proofs.glaze.binary_reflection.lib.GuWN OSSVerify.Proofs.glaze.binary_reflection.lib.B2JUT OSSVerify.Proofs.glaze.binary_reflection.lib.GuAA OSSVerify.Proofs.glaze.binary_reflection.lib.GuWA OSSVerify.Proofs.glaze.binary_reflection.lib.EscU OSSVerify.Proofs.glaze.binary_reflection.lib.B2JU OSSVerify.Proofs.glaze.binary_reflection.lib.GuCommon OSSVerify.Proofs.glaze.binary_reflection.lib.GuFA OSSVerify.Proofs.glaze.binary_reflection.lib.GuFMS OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Section Closure.
Context {RC : run_ceil}.
Variable AINV : ainv_t.
Variable SWOK : list (Z * Z) -> Prop.
Hypothesis U : ubmh AINV SWOK.

#[local] Notation RZ := (realizes USEGS).
#[local] Notation CC := (callee_contract USEGS [] GUBSAN fx_ok (realizes USEGS) AINV).

Let swin_ok_nil : SWOK (@nil (Z * Z)) := um_swok_nil AINV SWOK U.
Lemma nil_SWIN_img3 : forall lo hi, In (lo, hi) (@nil (Z * Z)) ->
  g_ro_hi GUBSAN <= lo /\ hi <= g_img_hi GUBSAN /\ (forall plo phi, In (plo, phi) (g_priv GUBSAN) -> hi <= plo \/ phi <= lo).
Proof. intros lo hi []. Qed.

(* [comment removed for export] *)
Let P_frame0 := P_frame AINV SWOK U [] swin_ok_nil.
Let P_zone0 := P_zone AINV SWOK U.
Let P_disj0 := P_disj AINV SWOK U.
Let P_mono0 := P_mono AINV SWOK U.
Let P_perm0 := um_perm AINV SWOK U.
(* [comment removed for export] *)
Let GC := GC_ALL AINV SWOK U [] swin_ok_nil nil_SWIN_img3.
Let OB := OBL2_ALL AINV SWOK U [] swin_ok_nil nil_SWIN_img3.

(* [comment removed for export] *)
Ltac hyp := first
  [ exact RZ_step_rr | exact RZ_msteps_rr | exact RZ_exit_rr | exact RZ_conseq_rr
  | exact P_frame0 | exact P_mono0 | exact P_zone0 | exact P_disj0 | exact P_perm0
  | exact GC | exact OB
  | (intros; eapply GC; eassumption)
  | (intros; eapply OB; eassumption) ].










Lemma C_escS : CC (EscU.ce MS).          Proof. eapply EscUC.esc_callee_S; hyp. Qed.

Lemma C_escL1 : CC EscU.ceL1.            Proof. eapply EscUC.esc_callee_L1; hyp. Qed.
Lemma NUM_U_L1 : CC (B2JUT.NUML1 B2JUT.GuNumT.BNU).  Proof. eapply GuNumC.number_u8tag_callee_L1; hyp. Qed.
Lemma NUM_I_L1 : CC (B2JUT.NUML1 B2JUT.GuNumT.BNI).  Proof. eapply GuNumC.number_inttag_callee_L1; hyp. Qed.
Lemma NUM_U_S : CC (B2JUT.GuNumT.ce MS B2JUT.GuNumT.BNU). Proof. eapply GuNumC.number_u8tag_callee_S; hyp. Qed.
Lemma NUM_I_S : CC (B2JUT.GuNumT.ce MS B2JUT.GuNumT.BNI). Proof. eapply GuNumC.number_inttag_callee_S; hyp. Qed.

Ltac ten k := destruct k as [|[|[|[|[|[|[|[|[|[|k]]]]]]]]]]; [cbv [B2JUT.AAcfg B2JUT.WAcfg B2JUT.AAL1 B2JUT.WAL1 nth] .. | lia].
Lemma AA_L1 : forall k, (k < 10)%nat -> CC (B2JUT.AAL1 (B2JUT.AAcfg k)).
Proof.
  intros k Hk. ten k.
  - eapply GuNum.GuAAi8.write_aligned_array_i8_callee_L1; hyp.
  - eapply GuNum.GuAAi16.write_aligned_array_i16_callee_L1; hyp.
  - eapply GuAAi32.write_aligned_array_i32_callee_L1; hyp.
  - eapply GuAAi64.write_aligned_array_i64_callee_L1; hyp.
  - eapply B2JUT.GuAAu8.write_aligned_array_u8_callee_L1; hyp.
  - eapply GuNum.GuAAu16.write_aligned_array_u16_callee_L1; hyp.
  - eapply GuAAu32.write_aligned_array_u32_callee_L1; hyp.
  - eapply GuAAu64.write_aligned_array_u64_callee_L1; hyp.
  - eapply GuNum.GuAAf32.write_aligned_array_f32_callee_L1; hyp.
  - eapply GuNum.GuAAf64.write_aligned_array_f64_callee_L1; hyp.
Qed.
Lemma AA_S : forall k, (k < 10)%nat -> CC (GuAA.ce (B2JUT.AAcfg k) MS).
Proof.
  intros k Hk. ten k.
  - eapply GuNum.GuAAi8.write_aligned_array_i8_callee_S; hyp.
  - eapply GuNum.GuAAi16.write_aligned_array_i16_callee_S; hyp.
  - eapply GuAAi32.write_aligned_array_i32_callee_S; hyp.
  - eapply GuAAi64.write_aligned_array_i64_callee_S; hyp.
  - eapply B2JUT.GuAAu8.write_aligned_array_u8_callee_S; hyp.
  - eapply GuNum.GuAAu16.write_aligned_array_u16_callee_S; hyp.
  - eapply GuAAu32.write_aligned_array_u32_callee_S; hyp.
  - eapply GuAAu64.write_aligned_array_u64_callee_S; hyp.
  - eapply GuNum.GuAAf32.write_aligned_array_f32_callee_S; hyp.
  - eapply GuNum.GuAAf64.write_aligned_array_f64_callee_S; hyp.
Qed.
Lemma WA_L1 : forall k, (k < 10)%nat -> CC (B2JUT.WAL1 (B2JUT.WAcfg k)).
Proof.
  intros k Hk. ten k.
  - eapply GuNum.GuWAi8.write_array_i8_callee_L1; hyp.
  - eapply GuNum.GuWAi16.write_array_i16_callee_L1; hyp.
  - eapply GuWAi32.write_array_i32_callee_L1; hyp.
  - eapply GuWAi64.write_array_i64_callee_L1; hyp.
  - eapply B2JUT.GuWAu8.write_array_u8_callee_L1; hyp.
  - eapply GuNum.GuWAu16.write_array_u16_callee_L1; hyp.
  - eapply GuWAu32.write_array_u32_callee_L1; hyp.
  - eapply GuWAu64.write_array_u64_callee_L1; hyp.
  - eapply GuNum.GuWAf32.write_array_f32_callee_L1; hyp.
  - eapply GuNum.GuWAf64.write_array_f64_callee_L1; hyp.
Qed.
Lemma WA_S : forall k, (k < 10)%nat -> CC (GuWA.ce (B2JUT.WAcfg k) MS).
Proof.
  intros k Hk. ten k.
  - eapply GuNum.GuWAi8.write_array_i8_callee_S; hyp.
  - eapply GuNum.GuWAi16.write_array_i16_callee_S; hyp.
  - eapply GuWAi32.write_array_i32_callee_S; hyp.
  - eapply GuWAi64.write_array_i64_callee_S; hyp.
  - eapply B2JUT.GuWAu8.write_array_u8_callee_S; hyp.
  - eapply GuNum.GuWAu16.write_array_u16_callee_S; hyp.
  - eapply GuWAu32.write_array_u32_callee_S; hyp.
  - eapply GuWAu64.write_array_u64_callee_S; hyp.
  - eapply GuNum.GuWAf32.write_array_f32_callee_S; hyp.
  - eapply GuNum.GuWAf64.write_array_f64_callee_S; hyp.
Qed.

(* [comment removed for export] *)
Lemma CT0_ok : forall id c, B2JUT.CT0 id = Some c -> CC c.
Proof.
  intros id c H.
  do 340 (destruct id as [|id];
    [ cbv [B2JUT.CT0 Nat.leb Nat.ltb Nat.sub andb] in H;
      first [ discriminate H
            | (injection H as <-;
               first [ exact C_escL1 | exact NUM_U_L1 | exact NUM_I_L1
                     | (apply AA_L1; cbv; lia) | (apply WA_L1; cbv; lia) ]) ]
    | ]).
  cbv [B2JUT.CT0 Nat.leb Nat.ltb Nat.sub andb] in H. discriminate H.
Qed.
Lemma CT2_ok : forall id c, B2JUT.CT2 id = Some c -> CC (c2_merged c).
Proof.
  intros id c H.
  do 330 (destruct id as [|id];
    [ cbv [B2JUT.CT2 Nat.leb Nat.ltb Nat.sub andb] in H;
      first [ discriminate H
            | (injection H as <-;
               first [ exact C_escS | exact NUM_U_S | exact NUM_I_S
                     | (apply AA_S; cbv; lia) | (apply WA_S; cbv; lia) ]) ]
    | ]).
  cbv [B2JUT.CT2 Nat.leb Nat.ltb Nat.sub andb] in H. discriminate H.
Qed.
Lemma C_b2jvL1 : CC (B2JUT.ce ML).      Proof. eapply B2JUC.b2jvU_callee_L1; first [hyp | exact CT0_ok | exact CT2_ok]. Qed.
Lemma C_b2jvS : CC (B2JUT.ce MS).       Proof. eapply B2JUC.b2jvU_callee_S; first [hyp | exact CT0_ok | exact CT2_ok | exact C_b2jvL1]. Qed.

(* [comment removed for export] *)
Lemma C_strctor : CC GuCommon.GuStrCtor.ce.     Proof. eapply GuStrCtorC.str_ctor_callee; hyp. Qed.


Lemma C_read : CC GuRead.ce.           Proof. eapply GuReadC.read_callee; hyp. Qed.

(* [comment removed for export] *)
Lemma C_vctor : CC GuCommon.GuVecCtor.VecCtorU.ce.          Proof. eapply GuVecCtorC.vec_ctor_callee; hyp. Qed.
Lemma C_vpushF : CC (GuVecPush.VecPushU.ce true).  Proof. eapply GuVecPushC.vec_push_full_callee; hyp. Qed.
Lemma C_vpushE : CC (GuVecPush.VecPushU.ce false). Proof. eapply GuVecPushC.vec_push_empty_callee; hyp. Qed.
Lemma C_b2j : CC GuB2JT.B2JnUT.ce.
Proof. eapply GuB2JC.b2j_callee; first [hyp | exact C_b2jvS | exact C_b2jvL1]. Qed.

(* [comment removed for export] *)
Theorem fuzz_closed_N : CC UbDrvHooks.GuFuzzT.FuzzN.ce.
Proof. eapply GuFuzzC.fuzz_callee_N; first [hyp | exact C_vctor | exact C_vpushF | exact C_vpushE | exact C_b2j | exact C_strctor | exact C_read]. Qed.
Theorem fuzz_closed_E : CC UbDrvHooks.GuFuzzT.FuzzE.ce.
Proof. eapply GuFuzzC.fuzz_callee_E; first [hyp | exact C_vctor | exact C_vpushF | exact C_vpushE | exact C_b2j | exact C_strctor | exact C_read]. Qed.
End Closure.
