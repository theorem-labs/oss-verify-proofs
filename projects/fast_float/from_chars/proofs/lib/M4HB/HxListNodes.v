(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFold FxRgs FxFacts FxImg FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFold OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require Import HxDerive.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition syn_range (fs : list fact) (l : lin) : option (Z * Z) :=
  match l with
  | LIN 0 [(z, 1)] => Some (var_range fs z)
  | _ => frange_syn fs l
  end.
Definition tighter (r d : Z * Z) : bool := if Z.ltb (snd r) (snd d) then true else Z.ltb (fst d) (fst r).
Definition ixf1 (l : lin) (S : sst) : sst :=
  let fs := s_facts S in
  let r := irange_x fs l in
  if (match syn_range fs l with Some d => tighter r d | None => true end)
  then (let f := FRange l (fst r) (snd r) in if fwf (s_next S) f then add_fact S f else S)
  else S.
Fixpoint ixfl_go (ls : list lin) (S : sst) : sst := match ls with [] => S | l :: ls' => ixfl_go ls' (ixf1 l S) end.
Definition hx_ixfl (ls : list lin) (S : sst) : option sst := Some (ixfl_go ls S).

Definition fsum1 (p : lin * lin) (S : sst) : sst := match hx_fsum (fst p) (snd p) S with Some K => K | None => S end.
Fixpoint fsuml_go (ps : list (lin * lin)) (S : sst) : sst := match ps with [] => S | p :: ps' => fsuml_go ps' (fsum1 p S) end.
Definition hx_fsuml (ps : list (lin * lin)) (S : sst) : option sst := Some (fsuml_go ps S).

Section Rule.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition adds (S K : sst) : Prop :=
  (forall E ms, sden segs E S ms -> sden segs E K ms) /\ s_next K = s_next S /\ s_rgs K = s_rgs S.
#[using="Type"] Lemma adds_refl : forall S, adds S S.
Proof. LiaFast.lf_pins LiaFast.u0. intros S. split; [intros E ms H; exact H | split; reflexivity]. Qed.
#[using="Type"] Lemma adds_trans : forall S K L, adds S K -> adds K L -> adds S L.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros S K L (H1 & N1 & R1) (H2 & N2 & R2). split; [intros E ms H; exact (H2 E ms (H1 E ms H))|].
  split; [rewrite N2; exact N1 | rewrite R2; exact R1].
Qed.
#[using="Type"] Lemma adds_rule : forall S K, adds S K ->
  hcall_rule1 segs S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros S K (H & N & R). split; [|split; [rewrite N; apply Pos.le_refl | rewrite R; reflexivity]].
  intros E ms Hd. exists ms, E. split; [apply ist_refl|]. split; [exact (H E ms Hd)|].
  split; [intros x Hx; reflexivity | intros x _; reflexivity].
Qed.
#[using="Type"] Lemma adds_fact : forall S f, fwf (s_next S) f = true ->
  (forall E, Forall (fact_ok E) (s_facts S) -> fact_ok E f) -> adds S (add_fact S f).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros S f Hw Hf. split; [|split; reflexivity].
  intros E ms Hd. apply (fx_add_fact segs E S ms f Hd Hw).
  destruct (Hd E (agree_refl _ _)) as (_ & _ & _ & _ & _ & _ & HF & _). exact (Hf E HF).
Qed.

#[using="Type"] Lemma ixf1_adds : forall l S, adds S (ixf1 l S).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros l S. unfold ixf1. cbv zeta.
  destruct (match syn_range (s_facts S) l with Some d => tighter (irange_x (s_facts S) l) d | None => true end); [|apply adds_refl].
  destruct (fwf (s_next S) (FRange l (fst (irange_x (s_facts S) l)) (snd (irange_x (s_facts S) l)))) eqn:Hw; [|apply adds_refl].
  apply (adds_fact S _ Hw). intros E HF. cbn [fact_ok]. exact (irange_x_sound E (s_facts S) l HF).
Qed.
#[using="Type"] Lemma ixfl_go_adds : forall ls S, adds S (ixfl_go ls S).
Proof. LiaFast.lf_pins LiaFast.u0.
  induction ls as [|l ls IH]; intros S; cbn [ixfl_go]; [apply adds_refl|].
  exact (adds_trans _ _ _ (ixf1_adds l S) (IH (ixf1 l S))).
Qed.
#[using="Type"] Theorem hx_ixfl_ok : forall ls S K, hx_ixfl ls S = Some K ->
  hcall_rule1 segs S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0. intros ls S K H. unfold hx_ixfl in H. injection H as <-. exact (adds_rule _ _ (ixfl_go_adds ls S)). Qed.

#[using="Type"] Lemma fsum1_adds : forall p S, adds S (fsum1 p S).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros [l1 l2] S. unfold fsum1. cbn [fst snd]. destruct (hx_fsum l1 l2 S) as [K|] eqn:H; [|apply adds_refl].
  unfold hx_fsum in H. cbv zeta in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hb; [|discriminate] end. injection H as <-.
  apply andb_prop in Hb as [Hlt Hw]. apply Z.ltb_lt in Hlt.
  apply (adds_fact S _ Hw). intros E HF. cbn [fact_ok].
  pose proof (frange_best_sound E (s_facts S) l1 HF) as R1. pose proof (frange_best_sound E (s_facts S) l2 HF) as R2.
  pose proof (bv_unsigned_in_range _ (lden E l1)) as U1. pose proof (bv_unsigned_in_range _ (lden E l2)) as U2.
  rewrite lden_ladd, bv_add_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
  rewrite Z.mod_small by lia. lia.
Qed.
#[using="Type"] Lemma fsuml_go_adds : forall ps S, adds S (fsuml_go ps S).
Proof. LiaFast.lf_pins LiaFast.u0.
  induction ps as [|p ps IH]; intros S; cbn [fsuml_go]; [apply adds_refl|].
  exact (adds_trans _ _ _ (fsum1_adds p S) (IH (fsum1 p S))).
Qed.
#[using="Type"] Theorem hx_fsuml_ok : forall ps S K, hx_fsuml ps S = Some K ->
  hcall_rule1 segs S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0. intros ps S K H. unfold hx_fsuml in H. injection H as <-. exact (adds_rule _ _ (fsuml_go_adds ps S)). Qed.
End Rule.
(* [comment removed for export] *)
