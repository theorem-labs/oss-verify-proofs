(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan ValProofs PlanSound.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Unset Lia Cache.

Module StEqb.
Import W64 Val Mem FI St Plan.

Lemma int_eq : forall a b : int, PrimInt63.eqb a b = true -> a = b.
Proof. intros a b H. apply Uint63.eqb_correct. exact H. Qed.

Lemma bool_eq : forall a b : bool, Bool.eqb a b = true -> a = b.
Proof. intros [] [] H; try reflexivity; discriminate H. Qed.

Fixpoint list_eqb {A} (e : A -> A -> bool) (x y : list A) : bool :=
  match x, y with
  | [], [] => true
  | a :: x', b :: y' => e a b && list_eqb e x' y'
  | _, _ => false
  end.

Lemma list_eqb_eq : forall {A} (e : A -> A -> bool), (forall a b, e a b = true -> a = b) ->
  forall x y, list_eqb e x y = true -> x = y.
Proof.
  intros A e He. induction x as [|a x IH]; intros [|b y] H; cbn [list_eqb] in H; try discriminate H; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply He in H1. apply IH in H2. subst. reflexivity.
Qed.

Definition cell_eqb (a b : cell) : bool :=
  PrimInt63.eqb (c_idx a) (c_idx b) && PrimInt63.eqb (c_w a) (c_w b) && sv_eqb (c_v a) (c_v b).
Lemma cell_eqb_eq : forall a b, cell_eqb a b = true -> a = b.
Proof.
  intros [i w v] [i' w' v'] H. unfold cell_eqb in H. cbn [c_idx c_w c_v] in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply int_eq in H1. apply int_eq in H2. apply ValP.sv_eqb_eq in H3. subst. reflexivity.
Qed.

Definition gran_eqb (a b : gran) : bool := Bool.eqb (g_dirty a) (g_dirty b) && list_eqb cell_eqb (g_cells a) (g_cells b).
Lemma gran_eqb_eq : forall a b, gran_eqb a b = true -> a = b.
Proof.
  intros [d c] [d' c'] H. unfold gran_eqb in H. cbn [g_dirty g_cells] in H. apply andb_prop in H as [H1 H2].
  apply bool_eq in H1. apply (list_eqb_eq cell_eqb cell_eqb_eq) in H2. subst. reflexivity.
Qed.

Definition bg_eqb (a b : bg) : bool :=
  match a, b with
  | BGNone, BGNone | BGZero, BGZero | BGImage, BGImage | BGUnk, BGUnk => true
  | BGBlob j s, BGBlob j' s' => PrimInt63.eqb j j' && PrimInt63.eqb s s'
  | _, _ => false
  end.
Lemma bg_eqb_eq : forall a b, bg_eqb a b = true -> a = b.
Proof.
  intros [] [] H; cbn [bg_eqb] in H; try discriminate H; try reflexivity.
  apply andb_prop in H as [H1 H2]. apply int_eq in H1. apply int_eq in H2. subst. reflexivity.
Qed.

Fixpoint imap_eqb {A} (e : A -> A -> bool) (x y : IMap.t A) : bool :=
  match x, y with
  | IMap.Leaf, IMap.Leaf => true
  | IMap.Node h l k v r, IMap.Node h' l' k' v' r' =>
      PrimInt63.eqb h h' && PrimInt63.eqb k k' && e v v' && imap_eqb e l l' && imap_eqb e r r'
  | _, _ => false
  end.
Lemma imap_eqb_eq : forall {A} (e : A -> A -> bool), (forall a b, e a b = true -> a = b) ->
  forall x y, imap_eqb e x y = true -> x = y.
Proof.
  intros A e He. induction x as [|h l IHl k v r IHr]; intros [|h' l' k' v' r'] H; cbn [imap_eqb] in H;
    try discriminate H; [reflexivity|].
  apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3].
  apply andb_prop in H as [H1 H2]. apply int_eq in H1. apply int_eq in H2. apply He in H3.
  apply IHl in H4. apply IHr in H5. subst. reflexivity.
Qed.

Definition region_eqb (a b : region) : bool :=
  PrimInt63.eqb (rg_lo a) (rg_lo b) && sv_eqb (rg_hi a) (rg_hi b) && Bool.eqb (rg_w a) (rg_w b)
  && bg_eqb (rg_bg a) (rg_bg b) && imap_eqb gran_eqb (rg_cells a) (rg_cells b).
Lemma region_eqb_eq : forall a b, region_eqb a b = true -> a = b.
Proof.
  intros [lo hi w g c] [lo' hi' w' g' c'] H. unfold region_eqb in H. cbn [rg_lo rg_hi rg_w rg_bg rg_cells] in H.
  apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3].
  apply andb_prop in H as [H1 H2]. apply int_eq in H1. apply ValP.sv_eqb_eq in H2. apply bool_eq in H3.
  apply bg_eqb_eq in H4. apply (imap_eqb_eq gran_eqb gran_eqb_eq) in H5. subst. reflexivity.
Qed.

Lemma rf_eqb_eq : forall {A} (e : A -> A -> bool), (forall a b, e a b = true -> a = b) ->
  forall x y : rf A, rf_forallb2 e x y = true -> x = y.
Proof.
  intros A e He x y H. unfold rf_forallb2 in H.
  repeat match type of H with (_ && _)%bool = true => let G := fresh "G" in apply andb_prop in H as [H G]; apply He in G end.
  apply He in H. destruct x, y. cbn in *. subst. reflexivity.
Qed.

Definition sresv_eqb (a b : sresv) : bool :=
  match a, b with
  | RNone, RNone | RUnk, RUnk => true
  | RAddr x, RAddr y => sv_eqb x y
  | _, _ => false
  end.
Lemma sresv_eqb_eq : forall a b, sresv_eqb a b = true -> a = b.
Proof. intros [] [] H; cbn [sresv_eqb] in H; try discriminate H; try reflexivity. apply ValP.sv_eqb_eq in H. subst. reflexivity. Qed.

Definition opinst_eqb (a b : opinst) : bool := PrimInt63.eqb (op_id a) (op_id b) && list_eqb sv_eqb (op_args a) (op_args b).
Lemma opinst_eqb_eq : forall a b, opinst_eqb a b = true -> a = b.
Proof.
  intros [i l] [i' l'] H. unfold opinst_eqb in H. cbn [op_id op_args] in H. apply andb_prop in H as [H1 H2].
  apply int_eq in H1. apply (list_eqb_eq sv_eqb ValP.sv_eqb_eq) in H2. subst. reflexivity.
Qed.

Definition pr_eqb (a b : int * int) : bool := PrimInt63.eqb (fst a) (fst b) && PrimInt63.eqb (snd a) (snd b).
Lemma pr_eqb_eq : forall a b, pr_eqb a b = true -> a = b.
Proof.
  intros [x y] [x' y'] H. unfold pr_eqb in H. cbn [fst snd] in H. apply andb_prop in H as [H1 H2].
  apply int_eq in H1. apply int_eq in H2. subst. reflexivity.
Qed.

Definition st_eqb (a b : sstate) : bool :=
  PrimInt63.eqb (s_pc a) (s_pc b) && rf_forallb2 sv_eqb (s_rf a) (s_rf b) && rf_forallb2 sv_eqb (s_ff a) (s_ff b)
  && sresv_eqb (s_resv a) (s_resv b) && imap_eqb region_eqb (s_regs a) (s_regs b)
  && list_eqb fact_eqb (s_facts a) (s_facts b) && list_eqb opinst_eqb (s_ops a) (s_ops b)
  && list_eqb pr_eqb (s_priv a) (s_priv b) && PrimInt63.eqb (s_next a) (s_next b).

Theorem st_eqb_eq : forall a b, st_eqb a b = true -> a = b.
Proof.
  intros [pc rfx ffx rv rg fs ops pv nx] [pc' rfx' ffx' rv' rg' fs' ops' pv' nx'] H. unfold st_eqb in H.
  cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next] in H.
  apply andb_prop in H as [H H9]. apply andb_prop in H as [H H8]. apply andb_prop in H as [H H7].
  apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply int_eq in H1. apply (rf_eqb_eq sv_eqb ValP.sv_eqb_eq) in H2. apply (rf_eqb_eq sv_eqb ValP.sv_eqb_eq) in H3.
  apply sresv_eqb_eq in H4. apply (imap_eqb_eq region_eqb region_eqb_eq) in H5.
  apply (list_eqb_eq fact_eqb ValP.fact_eqb_eq) in H6. apply (list_eqb_eq opinst_eqb opinst_eqb_eq) in H7.
  apply (list_eqb_eq pr_eqb pr_eqb_eq) in H8. apply int_eq in H9. subst. reflexivity.
Qed.

Definition sts_eqb : list sstate -> list sstate -> bool := list_eqb st_eqb.
Lemma sts_eqb_eq : forall x y, sts_eqb x y = true -> x = y.
Proof. exact (list_eqb_eq st_eqb st_eqb_eq). Qed.

End StEqb.
