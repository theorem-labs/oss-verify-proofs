(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.Esc OSSVerify.Proofs.glaze.binary_reflection.lib.B2J.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module B2JOk.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Esc.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2J.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Import B2J.

(* [comment removed for export] *)
Lemma okb_sound_gen : forall (c : cres) (g : bool),
  match c with COk sh => g && holes_only sh | _ => false end = true ->
  exists sh, g = true /\ holes_only sh = true /\ c = COk sh.
Proof.
  intros c g H. destruct c as [sh|? ? ?]; [|discriminate].
  apply andb_prop in H. destruct H as [H1 H2]. exists sh. split; [exact H1|]. split; [exact H2|]. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CUTS_ML : list (acs * plan) := CUTS ML.   (* [comment removed for export] *)
Definition CUTS_MS : list (acs * plan) := CUTS MS.   (* [comment removed for export] *)
Definition cuts_c (w : smode) : list (acs * plan) := match w with ML => CUTS_ML | MS => CUTS_MS end.
Lemma cuts_c_eq : forall w, cuts_c w = CUTS w.
Proof. intros w; destruct w; reflexivity. Qed.

Definition cert_okb (w : smode) (i : nat) : bool :=
  match nth_error (cuts_c w) i with
  | Some (T, k) =>
      match check PSEGS IT APLAIN (ce_nxf (ce w)) LIMIT (XN w) (B2JCutShare.GlzCallCert.XE0) (XB w) (B2JCutShare.GlzCallCert.XC0) (HScut (ce w) (cuts_c w) (Datatypes.S i)) 0%nat BFUEL FUEL None T k with
      | COk sh => gplan_ok k && holes_only sh
      | _ => false
      end
  | None => true
  end.

Lemma cert_okb_sound : forall w i, cert_okb w i = true -> B2J.cert_stmt w i.
Proof.
  intros w i. unfold cert_okb, B2J.cert_stmt. rewrite cuts_c_eq.
  generalize (nth_error (CUTS w) i). intros o. destruct o as [[T k]|]; [|intros _; exact I].
  intros H. exact (okb_sound_gen _ _ H).
Qed.

Definition top_okb (w : smode) : bool :=
  match check PSEGS IT APLAIN (ce_nxf (ce w)) LIMIT (XN w) (B2JCutShare.GlzCallCert.XE0) (XB w) (B2JCutShare.GlzCallCert.XC0) (HScut (ce w) (cuts_c w) 0) 0%nat BFUEL FUEL None (ce_tin (ce w)) (top w) with
  | COk sh => gplan_ok (top w) && holes_only sh
  | _ => false
  end.

Lemma top_okb_sound : forall w, top_okb w = true -> B2J.top_stmt w.
Proof.
  intros w. unfold top_okb, B2J.top_stmt. rewrite cuts_c_eq. intros H. exact (okb_sound_gen _ _ H).
Qed.
End B2JOk.
Module B2JcM0.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Esc.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2J.
Import B2JOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.

(* [comment removed for export] *)
Lemma b2j_cert_ML_0 : B2J.cert_stmt ML 0.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_1 : B2J.cert_stmt ML 1.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_2 : B2J.cert_stmt ML 2.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_3 : B2J.cert_stmt ML 3.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_4 : B2J.cert_stmt ML 4.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_5 : B2J.cert_stmt ML 5.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_6 : B2J.cert_stmt ML 6.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_7 : B2J.cert_stmt ML 7.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_8 : B2J.cert_stmt ML 8.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_9 : B2J.cert_stmt ML 9.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_0 : B2J.cert_stmt MS 0.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_1 : B2J.cert_stmt MS 1.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_2 : B2J.cert_stmt MS 2.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_3 : B2J.cert_stmt MS 3.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
End B2JcM0.
Module B2JcM2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Esc.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2J.
Import B2JOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.

(* [comment removed for export] *)
Lemma b2j_cert_ML_19 : B2J.cert_stmt ML 19.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_20 : B2J.cert_stmt ML 20.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_21 : B2J.cert_stmt ML 21.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_22 : B2J.cert_stmt ML 22.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_23 : B2J.cert_stmt ML 23.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_24 : B2J.cert_stmt ML 24.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_25 : B2J.cert_stmt ML 25.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_26 : B2J.cert_stmt ML 26.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_27 : B2J.cert_stmt ML 27.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_28 : B2J.cert_stmt ML 28.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_29 : B2J.cert_stmt ML 29.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_30 : B2J.cert_stmt ML 30.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_31 : B2J.cert_stmt ML 31.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_32 : B2J.cert_stmt ML 32.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
End B2JcM2.
Module B2JcM3.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Esc.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2J.
Import B2JOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.

(* [comment removed for export] *)
Lemma b2j_cert_ML_33 : B2J.cert_stmt ML 33.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_34 : B2J.cert_stmt ML 34.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_35 : B2J.cert_stmt ML 35.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_36 : B2J.cert_stmt ML 36.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_37 : B2J.cert_stmt ML 37.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_38 : B2J.cert_stmt ML 38.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_39 : B2J.cert_stmt ML 39.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_40 : B2J.cert_stmt ML 40.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_41 : B2J.cert_stmt ML 41.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_42 : B2J.cert_stmt ML 42.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_43 : B2J.cert_stmt ML 43.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_44 : B2J.cert_stmt ML 44.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_45 : B2J.cert_stmt ML 45.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_46 : B2J.cert_stmt ML 46.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
End B2JcM3.
Module B2JcM4.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Esc.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2J.
Import B2JOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.

(* [comment removed for export] *)
Lemma b2j_cert_ML_47 : B2J.cert_stmt ML 47.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_48 : B2J.cert_stmt ML 48.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_49 : B2J.cert_stmt ML 49.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_50 : B2J.cert_stmt ML 50.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_51 : B2J.cert_stmt ML 51.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_52 : B2J.cert_stmt ML 52.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_53 : B2J.cert_stmt ML 53.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_54 : B2J.cert_stmt ML 54.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_55 : B2J.cert_stmt ML 55.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_56 : B2J.cert_stmt ML 56.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_57 : B2J.cert_stmt ML 57.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_58 : B2J.cert_stmt ML 58.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_59 : B2J.cert_stmt ML 59.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_60 : B2J.cert_stmt ML 60.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
End B2JcM4.
Module B2JcM5.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Esc.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2J.
Import B2JOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.

(* [comment removed for export] *)
Lemma b2j_cert_ML_61 : B2J.cert_stmt ML 61.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_62 : B2J.cert_stmt ML 62.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_63 : B2J.cert_stmt ML 63.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_64 : B2J.cert_stmt ML 64.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_65 : B2J.cert_stmt ML 65.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_66 : B2J.cert_stmt ML 66.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_11 : B2J.cert_stmt MS 11.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_13 : B2J.cert_stmt MS 13.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_15 : B2J.cert_stmt MS 15.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_17 : B2J.cert_stmt MS 17.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_19 : B2J.cert_stmt MS 19.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_21 : B2J.cert_stmt MS 21.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_23 : B2J.cert_stmt MS 23.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_25 : B2J.cert_stmt MS 25.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
End B2JcM5.
Module B2JcM6.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Esc.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2J.
Import B2JOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.

(* [comment removed for export] *)
Lemma b2j_cert_MS_27 : B2J.cert_stmt MS 27.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_29 : B2J.cert_stmt MS 29.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_31 : B2J.cert_stmt MS 31.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_33 : B2J.cert_stmt MS 33.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_35 : B2J.cert_stmt MS 35.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_37 : B2J.cert_stmt MS 37.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_39 : B2J.cert_stmt MS 39.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_41 : B2J.cert_stmt MS 41.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_43 : B2J.cert_stmt MS 43.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_45 : B2J.cert_stmt MS 45.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_47 : B2J.cert_stmt MS 47.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_49 : B2J.cert_stmt MS 49.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_51 : B2J.cert_stmt MS 51.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_53 : B2J.cert_stmt MS 53.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
End B2JcM6.
Module B2JcM7.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Esc.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.B2J.
Import B2JOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.

(* [comment removed for export] *)
Lemma b2j_cert_MS_55 : B2J.cert_stmt MS 55.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_57 : B2J.cert_stmt MS 57.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_59 : B2J.cert_stmt MS 59.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_61 : B2J.cert_stmt MS 61.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_63 : B2J.cert_stmt MS 63.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_65 : B2J.cert_stmt MS 65.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_top_ML : B2J.top_stmt ML.
Proof. apply B2JOk.top_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_top_MS : B2J.top_stmt MS.
Proof. apply B2JOk.top_okb_sound. vm_cast_no_check (eq_refl true). Qed.
End B2JcM7.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import Esc.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import B2J.
Import B2JOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.

(* [comment removed for export] *)
Lemma b2j_cert_MS_4 : B2J.cert_stmt MS 4.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_5 : B2J.cert_stmt MS 5.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_6 : B2J.cert_stmt MS 6.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_7 : B2J.cert_stmt MS 7.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_MS_9 : B2J.cert_stmt MS 9.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_10 : B2J.cert_stmt ML 10.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_11 : B2J.cert_stmt ML 11.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_12 : B2J.cert_stmt ML 12.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_13 : B2J.cert_stmt ML 13.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_14 : B2J.cert_stmt ML 14.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_15 : B2J.cert_stmt ML 15.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_16 : B2J.cert_stmt ML 16.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_17 : B2J.cert_stmt ML 17.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma b2j_cert_ML_18 : B2J.cert_stmt ML 18.
Proof. apply B2JOk.cert_okb_sound. vm_cast_no_check (eq_refl true). Qed.
