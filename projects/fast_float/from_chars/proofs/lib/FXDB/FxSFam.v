(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxStep FxSubst.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxEnt FxLoop FxPlan FxFacts.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxWvC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import FxSNodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition sfam : Type := (list srec * list srec)%type.
Definition sf_strs (a : sfam) : list srec := fst a.
Definition sf_copies (a : sfam) : list srec := snd a.
(* [comment removed for export] *)
Definition strs_bl (a : sfam) : list (lin * lin) := List.map (fun r => (fst (fst r), snd (fst r))) (sf_strs a).
(* [comment removed for export] *)
Definition acopy3 (a : sfam) : list srec := sf_strs a ++ sf_copies a.

Section Fam.
Variable sarg : nat -> list byte.

Definition HA3 (E : valu) (M : smodel) (a : sfam) (m0 : word -> option byte) : Prop :=
  Forall (fun r => cstr_ok E M m0 (fst (fst r)) (snd (fst r)) /\ sbytes_ok sarg E m0 r) (sf_strs a) /\
  Forall (sbytes_ok sarg E m0) (sf_copies a).
Definition rwf3 (n : positive) (r : srec) : bool := (lwf n (fst (fst r)) && lwf n (snd (fst r)))%bool.
Definition awf3 (n : positive) (a : sfam) : bool := (forallb (rwf3 n) (sf_strs a) && forallb (rwf3 n) (sf_copies a))%bool.
Definition anil3 (a : sfam) : bool := match a with ([], []) => true | _ => false end.
Fixpoint recs_eqb (x y : list srec) : bool :=
  match x, y with
  | [], [] => true
  | (b, l, j) :: x', (b', l', j') :: y' => (lin_eqb b b' && lin_eqb l l' && Nat.eqb j j' && recs_eqb x' y')%bool
  | _, _ => false
  end.
Definition aeqb3 (a b : sfam) : bool := (recs_eqb (sf_strs a) (sf_strs b) && recs_eqb (sf_copies a) (sf_copies b))%bool.

#[using="Type"] Lemma recs_eqb_eq : forall x y, recs_eqb x y = true -> x = y.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction x as [|[[b l] j] x IH]; intros [|[[b' l'] j'] y] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply lin_eqb_eq in H1, H2. apply Nat.eqb_eq in H3. subst. f_equal. exact (IH y H4).
Qed.
#[using="Type"] Lemma aeqb3_eq : forall a b, aeqb3 a b = true -> a = b.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros [x1 x2] [y1 y2] H. unfold aeqb3, sf_strs, sf_copies in H. cbn [fst snd] in H.
  apply andb_prop in H as [H1 H2]. rewrite (recs_eqb_eq _ _ H1), (recs_eqb_eq _ _ H2). reflexivity.
Qed.
#[using="Type"] Lemma awf3_mono : forall n n' a, (n <= n')%positive -> awf3 n a = true -> awf3 n' a = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n n' a Hle H. unfold awf3, rwf3 in *. apply andb_prop in H as [H1 H2]. apply andb_true_intro.
  split; rewrite forallb_forall in *; intros r Hr; [specialize (H1 r Hr) | specialize (H2 r Hr)]; apply andb_prop in H1 || apply andb_prop in H2;
    [destruct H1 as [X Y] | destruct H2 as [X Y]]; rewrite (lwf_mono _ _ _ Hle X), (lwf_mono _ _ _ Hle Y); reflexivity.
Qed.
#[using="Type"] Lemma HA3_nil : forall E M a m0, anil3 a = true -> HA3 E M a m0.
Proof. LiaFast.lf_pins LiaFast.u0. intros E M [[|] [|]] m0 H; cbn in H; try discriminate. split; constructor. Qed.
#[using="Type"] Lemma sbytes_agree : forall n E E' m0 r, rwf3 n r = true -> agree n E E' -> sbytes_ok sarg E m0 r -> sbytes_ok sarg E' m0 r.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n E E' m0 [[b l] j] Hw Ha H. unfold rwf3 in Hw. cbn [fst snd] in Hw. apply andb_prop in Hw as [Hb Hl].
  unfold sbytes_ok in *. rewrite (uE_agree n E E' _ Hb Ha), (uE_agree n E E' _ Hl Ha). exact H.
Qed.
#[using="Type"] Lemma HA3_agree : forall n E E' M a m0, sm_wf n M = true -> awf3 n a = true -> agree n E E' -> HA3 E M a m0 -> HA3 E' M a m0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n E E' M a m0 Hwf Hwa Ha [H1 H2]. unfold awf3 in Hwa. apply andb_prop in Hwa as [W1 W2].
  split; rewrite Forall_forall in *; intros r Hr; rewrite forallb_forall in W1, W2.
  - destruct (H1 r Hr) as [Hc Hs]. split; [|exact (sbytes_agree n E E' m0 r (W1 r Hr) Ha Hs)].
    pose proof (HAS_agree n E E' M [(fst (fst r), snd (fst r))] m0 Hwf) as X.
    assert (Hw2 : awfS n [(fst (fst r), snd (fst r))] = true).
    { unfold awfS. cbn [forallb fst snd]. unfold rwf3 in W1. rewrite (W1 r Hr). reflexivity. }
    specialize (X Hw2 Ha ltac:(constructor; [exact Hc | constructor])). inversion X. assumption.
  - exact (sbytes_agree n E E' m0 r (W2 r Hr) Ha (H2 r Hr)).
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma HA3_HAS : forall E M a m0, HA3 E M a m0 -> HAS E M (strs_bl a) m0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E M a m0 [H1 _]. unfold HAS, strs_bl. rewrite Forall_map. eapply Forall_impl; [|exact H1].
  intros r [Hc _]. exact Hc.
Qed.
#[using="Type"] Lemma awf3_awfS : forall n a, awf3 n a = true -> awfS n (strs_bl a) = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n a H. unfold awf3 in H. apply andb_prop in H as [H _]. unfold awfS, strs_bl. rewrite forallb_forall in *.
  intros p Hp. apply in_map_iff in Hp as (r & <- & Hr). exact (H r Hr).
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma HA3_copy : forall E M a m0, HA3 E M a m0 -> forall r, In r (acopy3 a) -> sbytes_ok sarg E m0 r.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E M a m0 [H1 H2] r Hr. unfold acopy3 in Hr. apply in_app_or in Hr as [Hr|Hr].
  - rewrite Forall_forall in H1. exact (proj2 (H1 r Hr)).
  - rewrite Forall_forall in H2. exact (H2 r Hr).
Qed.
End Fam.
(* [comment removed for export] *)
