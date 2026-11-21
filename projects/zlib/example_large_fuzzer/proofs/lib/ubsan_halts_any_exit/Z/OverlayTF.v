(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition ffreq (F : Z -> Z) (Fl : list Z) (c : Z) : Z := if existsb (Z.eqb c) Fl then 1 else F c.

Lemma existsb_In : forall (Fl : list Z) c, existsb (Z.eqb c) Fl = true <-> In c Fl.
Proof.
  intros Fl c. rewrite existsb_exists. split.
  - intros (x & Hx & Ex). apply Z.eqb_eq in Ex. subst x. exact Hx.
  - intros Hc. exists c. split; [exact Hc | apply Z.eqb_refl].
Qed.

Record tree_facts (z : ztree) (E ML : Z) (F : Z -> Z) (Fl : list Z) : Prop := {
  tf_ok : ztree_ok z;
  tf_E : zt_E z = E;
  tf_ML : zt_ML z = ML;
  tf_Fl : (length Fl <= 2)%nat /\ NoDup Fl /\ (forall f, In f Fl -> 0 <= f <= 2 /\ f < E /\ F f = 0);
  tf_noforce : forall a b, 0 <= a < E -> 0 <= b < E -> a <> b -> F a <> 0 -> F b <> 0 -> Fl = [];
  tf_two : exists a b, 0 <= a < E /\ 0 <= b < E /\ a <> b /\ ffreq F Fl a <> 0 /\ ffreq F Fl b <> 0;
  tf_used : forall c, 0 <= c < E -> (zt_used z c <-> ffreq F Fl c <> 0);
  tf_wt : forall i, g_pos (zt_g z) i -> g_leaf (zt_g z) i = true ->
            0 <= g_code (zt_g z) i < E /\ g_wt (zt_g z) i = ffreq F Fl (g_code (zt_g z) i) }.

Definition zt_kraft (z : ztree) : Prop :=
  kraftZ (zt_ML z) (g_hist (zt_g z) (fun i => zt_len z (g_code (zt_g z) i))) = 2 ^ (zt_ML z).

Lemma ffreq_ext : forall F F' Fl c, F c = F' c -> ffreq F Fl c = ffreq F' Fl c.
Proof. intros F F' Fl c H. unfold ffreq. rewrite H. reflexivity. Qed.

Lemma tree_facts_ext : forall z E ML F F' Fl,
  (forall c, 0 <= c < E -> F c = F' c) ->
  tree_facts z E ML F Fl -> tree_facts z E ML F' Fl.
Proof.
  intros z E ML F F' Fl HF T. destruct T as [OK EE EML [L1 [L2 L3]] NOF TWO USED WT].
  constructor.
  - exact OK.
  - exact EE.
  - exact EML.
  - split; [exact L1|]. split; [exact L2|]. intros f Hf. destruct (L3 f Hf) as (A & B & C). rewrite <- (HF f) by lia. auto.
  - intros a b Ha Hb N Fa Fb. rewrite <- (HF a) in Fa by lia. rewrite <- (HF b) in Fb by lia. exact (NOF a b Ha Hb N Fa Fb).
  - destruct TWO as (a & b & Ha & Hb & N & Fa & Fb). exists a, b.
    rewrite <- (ffreq_ext F F' Fl a) by (apply HF; lia). rewrite <- (ffreq_ext F F' Fl b) by (apply HF; lia). tauto.
  - intros c Hc. rewrite <- (ffreq_ext F F' Fl c) by (apply HF; lia). apply USED. exact Hc.
  - intros i Hi Li. destruct (WT i Hi Li) as [R W]. split; [exact R|]. rewrite <- (ffreq_ext F F' Fl) by (apply HF; lia). exact W.
Qed.
