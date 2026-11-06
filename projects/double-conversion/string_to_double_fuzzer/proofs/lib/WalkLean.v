(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Lemma tset_tset_same {A} (p : positive) (x y : A) (t : tree A) : tset p x (tset p y t) = tset p x t.
Proof. revert t; induction p as [p IH|p IH|]; intros [|l v r]; cbn; try rewrite IH; reflexivity. Qed.

Lemma tset_tset_comm {A} (p q : positive) (x y : A) (t : tree A) :
  p <> q -> tset p x (tset q y t) = tset q y (tset p x t).
Proof.
  revert q t; induction p as [p IH|p IH|]; intros [q|q|] [|l v r] Hne; cbn; try reflexivity;
    try (rewrite IH by congruence; reflexivity); congruence.
Qed.

Lemma regupd_same : forall (R : bvmap 5 word) (r : reg) v v', regupd (regupd R r v') r v = regupd R r v.
Proof. intros. unfold regupd, bvmap_set. apply tset_tset_same. Qed.

Lemma regupd_comm : forall (R : bvmap 5 word) (r r' : reg) v v',
  bv_eqb r r' = false -> regupd (regupd R r' v') r v = regupd (regupd R r v) r' v'.
Proof.
  intros R r r' v v' H. unfold regupd, bvmap_set. apply tset_tset_comm.
  intro E. apply bv_key_inj in E. subst r'. rewrite bv_eqb_refl in H. discriminate H.
Qed.

Lemma bv_eqb_true_eq : forall {n} (a b : bv n), bv_eqb a b = true -> a = b.
Proof. intros n a b H. apply bv_eq. apply Z.eqb_eq. exact H. Qed.

(* [comment removed for export] *)
Definition rfl := list (reg * word).

Fixpoint rf_apply (l : rfl) (regs : bvmap 5 word) : bvmap 5 word :=
  match l with [] => regs | (r, v) :: l' => regupd (rf_apply l' regs) r v end.

Fixpoint rf_get (l : rfl) (regs : bvmap 5 word) (r : reg) : word :=
  match l with [] => getr regs r | (r', v) :: l' => if bv_eqb r r' then v else rf_get l' regs r end.

Fixpoint rf_set (l : rfl) (r : reg) (v : word) : rfl :=
  match l with
  | [] => [(r, v)]
  | (r', v') :: l' => if bv_eqb r r' then (r', v) :: l' else (r', v') :: rf_set l' r v
  end.

Lemma rf_get_ok : forall l regs r, bv_eqb r 0 = false -> getr (rf_apply l regs) r = rf_get l regs r.
Proof.
  induction l as [|[r' v'] l IH]; intros regs r H0; cbn [rf_apply rf_get]; [reflexivity|].
  destruct (bv_eqb r r') eqn:E.
  - apply bv_eqb_true_eq in E. subst r'. apply getr_same. intro Z0. subst r. discriminate H0.
  - rewrite getr_other; [apply IH; exact H0|]. intro Z0. subst r'. rewrite bv_eqb_refl in E. discriminate E.
Qed.

Lemma rf_get_ok' : forall l regs r v, bv_eqb r 0 = false -> rf_get l regs r = v -> getr (rf_apply l regs) r = v.
Proof. intros l regs r v H0 <-. apply rf_get_ok. exact H0. Qed.

Lemma rf_set_ok : forall l r v regs, regupd (rf_apply l regs) r v = rf_apply (rf_set l r v) regs.
Proof.
  induction l as [|[r' v'] l IH]; intros r v regs; cbn [rf_apply rf_set]; [reflexivity|].
  destruct (bv_eqb r r') eqn:E; cbn [rf_apply].
  - apply bv_eqb_true_eq in E. subst r'. apply regupd_same.
  - rewrite regupd_comm by exact E. rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint rf_notin (l : rfl) (r : reg) : Prop :=
  match l with [] => True | (r', _) :: l' => r <> r' /\ rf_notin l' r end.
Lemma rf_frame : forall l regs r, rf_notin l r -> getr (rf_apply l regs) r = getr regs r.
Proof.
  induction l as [|[r' v'] l IH]; intros regs r H; cbn [rf_apply]; [reflexivity|].
  destruct H as [Hne H]. rewrite getr_other by exact Hne. apply IH. exact H.
Qed.

Section WL.
Context {fx : FPState}.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma wl_step_rd : forall L regs pc mem rom (rd : reg) (val X : word) (pc1 pc' : word) L' sF,
  bv_eqb rd 0 = false ->
  RiscvSemantics.step segs (mkst (rf_apply L regs) pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then rf_apply L regs else regupd (rf_apply L regs) rd val) pc1 mem rom) ->
  val = X -> bv_unsigned pc1 = bv_unsigned pc' -> rf_set L rd X = L' ->
  msteps segs (mkst (rf_apply L' regs) pc' mem rom) sF ->
  msteps segs (mkst (rf_apply L regs) pc mem rom) sF.
Proof.
  intros L regs pc mem rom rd val X pc1 pc' L' sF Hrd Hst HV Hpc HL HK.
  eapply mst_step; [reflexivity | exact Hst |].
  rewrite Hrd, HV, rf_set_ok, HL, (proj2 (bv_eq _ _ _) Hpc). exact HK.
Qed.

(* [comment removed for export] *)
Lemma wl_step_pc : forall L regs pc mem rom (pc1 pc' : word) sF,
  RiscvSemantics.step segs (mkst (rf_apply L regs) pc mem rom) = MachineOk (mkst (rf_apply L regs) pc1 mem rom) ->
  bv_unsigned pc1 = bv_unsigned pc' ->
  msteps segs (mkst (rf_apply L regs) pc' mem rom) sF ->
  msteps segs (mkst (rf_apply L regs) pc mem rom) sF.
Proof.
  intros L regs pc mem rom pc1 pc' sF Hst Hpc HK.
  eapply mst_step; [reflexivity | exact Hst |]. rewrite (proj2 (bv_eq _ _ _) Hpc). exact HK.
Qed.

Lemma wl_begin_eq : forall regs pc mem rom sF,
  msteps segs (mkst (rf_apply [] regs) pc mem rom) sF -> msteps segs (mkst regs pc mem rom) sF.
Proof. intros. assumption. Qed.
End WL.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac wl_eval t := eval cbv beta iota fix delta [rf_get rf_set bv_eqb bv_unsigned Z.eqb Pos.eqb] in t.

(* [comment removed for export] *)
Ltac wl_imm t :=
  lazymatch t with
  | context C [bv_signed (@BV ?n ?z ?p)] =>
      let v := eval vm_compute in (bv_signed (@BV n z p)) in let t' := context C [v] in wl_imm t'
  | context C [bv_unsigned (@BV ?n ?z ?p)] =>
      let v := eval vm_compute in (bv_unsigned (@BV n z p)) in let t' := context C [v] in wl_imm t'
  | context C [Z.shiftl ?a ?b] =>
      let v := eval vm_compute in (Z.shiftl a b) in let t' := context C [v] in wl_imm t'
  | _ => t
  end.

(* [comment removed for export] *)
Ltac wl_subst L regs val k :=
  lazymatch val with
  | context C [getr (rf_apply L regs) ?r] =>
      let v := wl_eval (rf_get L regs r) in
      let f := constr:(fun x : word => ltac:(let t := context C [x] in exact t)) in
      let p := constr:(f_equal f (rf_get_ok' L regs r v (@eq_refl bool false) (@eq_refl word v))) in
      let val1 := context C [v] in
      wl_subst L regs val1 ltac:(fun val2 q => k val2 constr:(eq_trans p q))
  | _ => k val constr:(@eq_refl word val)
  end.

(* [comment removed for export] *)
Ltac wl_name v k :=
  match goal with
  | x := ?b |- _ => constr_eq b v; k x
  | _ => let X := fresh "X" in pose (X := v); k X
  end.

Ltac wl_begin := lazymatch goal with |- msteps _ (mkst _ _ _ _) _ => apply wl_begin_eq end.

(* [comment removed for export] *)
Ltac wl_getr :=
  repeat match goal with
  | |- context [getr (rf_apply ?L ?regs) ?r] =>
      let v := wl_eval (rf_get L regs r) in
      rewrite (rf_get_ok' L regs r v (@eq_refl bool false) (@eq_refl word v))
  end.

(* [comment removed for export] *)
Ltac wl_step T :=
  lazymatch goal with
  | |- msteps ?segs (mkst (rf_apply ?L ?regs) ?pc ?mem ?rom) ?sF =>
    let H := fresh "Hst" in
    eassert (H : RiscvSemantics.step segs (mkst (rf_apply L regs) pc mem rom) = MachineOk _) by T;
    lazymatch type of H with
    | _ = MachineOk (mkst (if bv_eqb ?rd 0 then _ else regupd _ ?rd ?val) ?pc1 _ _) =>
      wl_subst L regs val ltac:(fun val1 p =>
        let val2 := wl_imm val1 in
        wl_name val2 ltac:(fun X =>
          let z := eval vm_compute in (bv_unsigned pc1) in
          let L' := wl_eval (rf_set L rd X) in
          refine (wl_step_rd segs L regs pc mem rom rd val X pc1 (@BV 64 z I) L' sF
                    (@eq_refl bool false) H p (@eq_refl Z z) (@eq_refl rfl L') _); clear H))
    end
  end.

Ltac wl_end := apply mst_refl.
