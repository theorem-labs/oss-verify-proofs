(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step ValProofs.
Import ListNotations.
Import W64 Val Mem FI St Step ValP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module KnownT.

Definition tiers {A} (fs : list fact) (vs : list int) (q : list fact -> option A) : option A :=
  match q (rel_facts vs fs) with
  | Some r => Some r
  | None => match q (rel_facts (close_vs fs vs vs) fs) with
            | Some r => Some r
            | None => q fs
            end
  end.

Definition decide_ltu_tt (fs : list fact) (a b : sv) : option bool := tiers fs (sv_vs a (sv_vs b [])) (fun l => decide_ltu l a b).
Definition decide_eq_tt (fs : list fact) (a b : sv) : option bool := tiers fs (sv_vs a (sv_vs b [])) (fun l => decide_eq l a b).
Definition decide_eq0_tt (fs : list fact) (v : sv) : option bool := tiers fs (sv_vs v []) (fun l => decide_eq0 l v).

Definition dec_true (o : option bool) : bool := match o with Some true => true | _ => false end.
Definition dec_false (o : option bool) : bool := match o with Some false => true | _ => false end.
Definition known_ltu_t (fs : list fact) (a b : sv) : bool := dec_true (decide_ltu_tt fs a b).
Definition known_leu_t (fs : list fact) (a b : sv) : bool := dec_false (decide_ltu_tt fs b a).
Definition known_eq_t (fs : list fact) (a b : sv) : bool := dec_true (decide_eq_tt fs a b).
Definition known_ne_t (fs : list fact) (a b : sv) : bool := dec_false (decide_eq_tt fs a b).
Definition known_nz_t (fs : list fact) (v : sv) : bool := dec_false (decide_eq0_tt fs v).
Definition known_z_t (fs : list fact) (v : sv) : bool := dec_true (decide_eq0_tt fs v).

Section Sound.
Variable E : env.
Variable fs : list fact.
Hypothesis Hfs : facts_hold E fs.

Lemma tiers_ind : forall {A} vs (q : list fact -> option A) (P : A -> Prop),
  (forall l r, facts_hold E l -> q l = Some r -> P r) -> forall r, tiers fs vs q = Some r -> P r.
Proof.
  intros A vs q P HQ r H. unfold tiers in H.
  destruct (q (rel_facts vs fs)) as [r1|] eqn:Q1; [injection H as <-; exact (HQ _ _ (rel_facts_hold E _ fs Hfs) Q1)|].
  destruct (q (rel_facts (close_vs fs vs vs) fs)) as [r2|] eqn:Q2; [injection H as <-; exact (HQ _ _ (rel_facts_hold E _ fs Hfs) Q2)|].
  exact (HQ _ _ Hfs H).
Qed.

Lemma decide_ltu_tt_sound : forall a b r, decide_ltu_tt fs a b = Some r -> bv_ltu (den E a) (den E b) = r.
Proof. intros a b r H. unfold decide_ltu_tt in H. revert r H. apply tiers_ind. intros l r Hl Q. exact (decide_ltu_sound E l Hl a b r Q). Qed.
Lemma decide_eq_tt_sound : forall a b r, decide_eq_tt fs a b = Some r -> bv_eqb (den E a) (den E b) = r.
Proof. intros a b r H. unfold decide_eq_tt in H. revert r H. apply tiers_ind. intros l r Hl Q. exact (decide_eq_sound E l Hl a b r Q). Qed.
Lemma decide_eq0_tt_sound : forall v r, decide_eq0_tt fs v = Some r -> bv_eqb (den E v) (Z_to_bv 64 0) = r.
Proof. intros v r H. unfold decide_eq0_tt in H. revert r H. apply tiers_ind. intros l r Hl Q. exact (decide_eq0_sound E l Hl v r Q). Qed.

Lemma known_ltu_t_sound : forall a b, known_ltu_t fs a b = true -> bv_unsigned (den E a) < bv_unsigned (den E b).
Proof.
  intros a b H. unfold known_ltu_t, dec_true in H. destruct (decide_ltu_tt fs a b) as [[|]|] eqn:D; try discriminate.
  exact (proj1 (ltu_iff _ _ true) (decide_ltu_tt_sound a b true D)).
Qed.
Lemma known_leu_t_sound : forall a b, known_leu_t fs a b = true -> bv_unsigned (den E a) <= bv_unsigned (den E b).
Proof.
  intros a b H. unfold known_leu_t, dec_false in H. destruct (decide_ltu_tt fs b a) as [[|]|] eqn:D; try discriminate.
  exact (proj1 (ltu_iff _ _ false) (decide_ltu_tt_sound b a false D)).
Qed.
Lemma known_eq_t_sound : forall a b, known_eq_t fs a b = true -> den E a = den E b.
Proof.
  intros a b H. unfold known_eq_t, dec_true in H. destruct (decide_eq_tt fs a b) as [[|]|] eqn:D; try discriminate.
  exact (proj1 (eqb_iff _ _ true) (decide_eq_tt_sound a b true D)).
Qed.
Lemma known_ne_t_sound : forall a b, known_ne_t fs a b = true -> den E a <> den E b.
Proof.
  intros a b H. unfold known_ne_t, dec_false in H. destruct (decide_eq_tt fs a b) as [[|]|] eqn:D; try discriminate.
  exact (proj1 (eqb_iff _ _ false) (decide_eq_tt_sound a b false D)).
Qed.
Lemma known_nz_t_sound : forall v, known_nz_t fs v = true -> bv_unsigned (den E v) <> 0.
Proof.
  intros v H. unfold known_nz_t, dec_false in H. destruct (decide_eq0_tt fs v) as [[|]|] eqn:D; try discriminate.
  pose proof (proj1 (eqb_iff _ _ false) (decide_eq0_tt_sound v false D)) as N. intros Z0. apply N. apply bv_eq. rewrite Z0. reflexivity.
Qed.
Lemma known_z_t_sound : forall v, known_z_t fs v = true -> bv_unsigned (den E v) = 0.
Proof.
  intros v H. unfold known_z_t, dec_true in H. destruct (decide_eq0_tt fs v) as [[|]|] eqn:D; try discriminate.
  rewrite (proj1 (eqb_iff _ _ true) (decide_eq0_tt_sound v true D)). reflexivity.
Qed.
End Sound.
End KnownT.
