(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk As0Tables ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInitCache_b BatPopulate1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatClsRep_b BatSecAllocPost_b BatRecycle2C_b BatRecycle3L_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Inductive art_rel : Type :=
| REP (c w d b1 n : Z)      (* [comment removed for export] *)
| RES (mb ms m b1 n : Z)    (* [comment removed for export] *)
| REB (wb : Z).             (* [comment removed for export] *)

(* [comment removed for export] *)
Definition art_rel_addr (spb : Z) (e : art_rel) : Z :=
  match e with REP c w d _ _ => spb + c * 2 ^ 32 + 16 * w + d | RES _ _ m _ _ => m | REB wb => spb + 24 * 2 ^ 32 + 16 * wb end.
(* [comment removed for export] *)
Definition art_rel_zone (spb : Z) (e : art_rel) : Z * Z :=
  match e with REP c w _ _ _ => (spb + c * 2 ^ 32 + 16 * w, AsanTab.class_size c) | RES mb ms _ _ _ => (mb, ms) | REB wb => (spb + 24 * 2 ^ 32 + 16 * wb, 8192) end.

(* [comment removed for export] *)
Record art_rg : Type := RG { rg_cls : Z -> art_cls; rg_bl : list (Z * Z) }.
Definition art_cls_upd (f : Z -> art_cls) (c : Z) (cl : art_cls) : Z -> art_cls := fun c' => if c' =? c then cl else f c'.
Fixpoint art_bl_idx (mb : Z) (bl : list (Z * Z)) : nat :=
  match bl with [] => O | b :: r => if fst b =? mb then O else S (art_bl_idx mb r) end.
Definition art_rel_step (e : art_rel) (G : art_rg) : art_rg :=
  match e with
  | REP c w _ _ _ => RG (art_cls_upd (rg_cls G) c (art_cls_dealloc c w (rg_cls G c))) (rg_bl G)
  | RES mb _ _ _ _ => RG (rg_cls G) (art_swap_remove (0, 0) (art_bl_idx mb (rg_bl G)) (rg_bl G))
  | REB wb => RG (art_cls_upd (rg_cls G) 24 (art_cls_dealloc 24 wb (rg_cls G 24))) (rg_bl G)
  end.
Definition art_rel_steps (es : list art_rel) (G : art_rg) : art_rg := fold_left (fun g e => art_rel_step e g) es G.

Lemma art_cls_upd_same : forall f c cl, art_cls_upd f c cl c = cl.
Proof. intros. unfold art_cls_upd. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma art_cls_upd_other : forall f c cl c', c' <> c -> art_cls_upd f c cl c' = f c'.
Proof. intros f c cl c' H. unfold art_cls_upd. destruct (c' =? c) eqn:E; [apply Z.eqb_eq in E; lia|reflexivity]. Qed.

(* [comment removed for export] *)
Lemma art_bl_idx_nth : forall bl mb ms, In (mb, ms) bl -> (forall b b', In b bl -> In b' bl -> fst b = fst b' -> b = b') ->
  nth_error bl (art_bl_idx mb bl) = Some (mb, ms).
Proof.
  induction bl as [|b r IH]; intros mb ms Hin Hinj; [destruct Hin|]. cbn [art_bl_idx].
  destruct (Z.eqb_spec (fst b) mb) as [E|NE].
  - cbn. f_equal. apply Hinj; [left; reflexivity|exact Hin|exact E].
  - cbn. apply IH.
    + destruct Hin as [Eb|Hin]; [exfalso; apply NE; rewrite Eb; reflexivity|exact Hin].
    + intros x y Hx Hy. apply Hinj; right; assumption.
Qed.

(* [comment removed for export] *)
Lemma art_swap_remove_keeps : forall A (d : A) i l x, (i < length l)%nat -> In x l -> x <> nth i l d -> In x (art_swap_remove d i l).
Proof.
  intros A d i l x Hi Hx Hne. destruct (In_nth _ _ d Hx) as (j & Hj & Ej).
  assert (Hji : j <> i) by (intros ->; apply Hne; symmetry; exact Ej).
  destruct (Nat.eq_dec j (length l - 1)) as [Elast|Nlast].
  - (* [comment removed for export] *)
    assert (Hil : (i < length l - 1)%nat) by lia.
    apply (nth_error_In _ i). rewrite art_swap_remove_nth by exact Hil. rewrite Nat.eqb_refl. rewrite <- Elast. rewrite (nth_error_nth' l d Hj). f_equal. exact Ej.
  - assert (Hjl : (j < length l - 1)%nat) by lia.
    apply (nth_error_In _ j). rewrite art_swap_remove_nth by exact Hjl. replace (j =? i)%nat with false by (symmetry; apply Nat.eqb_neq; exact Hji).
    rewrite (nth_error_nth' l d Hj). f_equal. exact Ej.
Qed.

(* [comment removed for export] *)
Lemma art_sec_geo_remove : forall HI t ctx parr bl i, art_sec_geo HI t ctx parr bl -> art_sec_geo HI t ctx parr (art_swap_remove (0, 0) i bl).
Proof.
  intros HI t ctx parr bl i (G1 & G2 & G3 & G4 & G5 & G6 & GB & GD).
  assert (L : Z.of_nat (length (art_swap_remove (0, 0) i bl)) <= Z.of_nat (length bl)) by (rewrite art_swap_remove_length; lia).
  pose proof (Nat2Z.is_nonneg (length (art_swap_remove (0, 0) i bl))) as L0.
  unfold art_sec_geo. split; [exact G1|]. split; [lia|]. split; [lia|].
  split. { unfold appmem in *. lia. }
  split. { unfold apart in *. lia. }
  split. { unfold apart in *. lia. }
  split.
  - intros b Hb. apply art_swap_remove_in in Hb. destruct (GB b Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
    repeat (split; [assumption|]). split; [|split; assumption]. unfold apart in *. lia.
  - intros j1 j2 b b' H1 H2 Hne.
    assert (Hj1 : (j1 < length bl - 1)%nat) by (rewrite <- (art_swap_remove_length _ (0, 0) i bl); apply nth_error_Some; congruence).
    assert (Hj2 : (j2 < length bl - 1)%nat) by (rewrite <- (art_swap_remove_length _ (0, 0) i bl); apply nth_error_Some; congruence).
    rewrite art_swap_remove_nth in H1 by exact Hj1. rewrite art_swap_remove_nth in H2 by exact Hj2.
    apply (GD _ _ b b' H1 H2). destruct (j1 =? i)%nat eqn:E1; destruct (j2 =? i)%nat eqn:E2; try lia.
    apply Nat.eqb_eq in E1. apply Nat.eqb_eq in E2. lia.
Qed.

(* [comment removed for export] *)
Lemma art_sec_geo_inj : forall HI t ctx parr bl, art_sec_geo HI t ctx parr bl -> forall b b', In b bl -> In b' bl -> fst b = fst b' -> b = b'.
Proof.
  intros HI t ctx parr bl (_ & _ & _ & _ & _ & _ & GB & GD) b b' Hb Hb' E.
  destruct (In_nth_error _ _ Hb) as (j & Hj). destruct (In_nth_error _ _ Hb') as (j' & Hj').
  destruct (Nat.eq_dec j j') as [->|NE]; [congruence|].
  pose proof (GD j j' b b' Hj Hj' NE) as Ap. destruct (GB b Hb) as (_ & _ & S1 & _). destruct (GB b' Hb') as (_ & _ & S2 & _). unfold apart in Ap. lia.
Qed.

(* [comment removed for export] *)
Lemma art_cls_dealloc_au : forall c w cl, cl_au (art_cls_dealloc c w cl) = cl_au cl /\ cl_mu (art_cls_dealloc c w cl) = cl_mu cl /\ cl_mfa (art_cls_dealloc c w cl) = cl_mfa cl.
Proof. intros c w cl. unfold art_cls_dealloc. destruct (art_cls_full c cl); cbn; auto. Qed.

Lemma art_cls_dealloc_perm : forall c w cl, Z.of_nat (length (cl_cache cl)) <= art_ic_mc c -> 1 <= c <= 31 ->
  Permutation (w :: cl_cache cl ++ cl_free cl) (cl_cache (art_cls_dealloc c w cl) ++ cl_free (art_cls_dealloc c w cl)).
Proof.
  intros c w cl Hlen Hc. unfold art_cls_dealloc. destruct (art_cls_full c cl) eqn:EF.
  - unfold art_cls_push, art_cls_return. cbn [cl_cache cl_free].
    set (k := (length (cl_cache cl) - Z.to_nat (art_ic_mc c / 2))%nat).
    rewrite <- (firstn_skipn k (cl_cache cl)) at 1. rewrite <- !app_assoc. cbn [app].
    eapply Permutation_trans; [apply Permutation_middle|]. apply Permutation_app_head. apply perm_skip. apply Permutation_app_comm.
  - unfold art_cls_push. cbn [cl_cache cl_free]. rewrite <- app_assoc. cbn [app]. apply Permutation_middle.
Qed.

Lemma art_cls_dealloc_in : forall c w cl x, Z.of_nat (length (cl_cache cl)) <= art_ic_mc c -> 1 <= c <= 31 ->
  (In x (cl_cache (art_cls_dealloc c w cl) ++ cl_free (art_cls_dealloc c w cl)) <-> x = w \/ In x (cl_cache cl ++ cl_free cl)).
Proof.
  intros c w cl x Hlen Hc. pose proof (art_cls_dealloc_perm c w cl Hlen Hc) as P. split.
  - intros H. apply (Permutation_in _ (Permutation_sym P)) in H. destruct H as [<-|H]; [left; reflexivity|right; exact H].
  - intros H. apply (Permutation_in _ P). destruct H as [->|H]; [left; reflexivity|right; exact H].
Qed.

Lemma art_cls_dealloc_total : forall c w cl, Z.of_nat (length (cl_cache cl)) <= art_ic_mc c -> 1 <= c <= 31 ->
  Z.of_nat (length (cl_cache (art_cls_dealloc c w cl))) + Z.of_nat (length (cl_free (art_cls_dealloc c w cl)))
  = Z.of_nat (length (cl_cache cl)) + Z.of_nat (length (cl_free cl)) + 1.
Proof.
  intros c w cl Hlen Hc. pose proof (Permutation_length (art_cls_dealloc_perm c w cl Hlen Hc)) as L. cbn [length] in L. rewrite !length_app in L. lia.
Qed.

Lemma art_cls_dealloc_cache_le : forall c w cl, Z.of_nat (length (cl_cache cl)) <= art_ic_mc c -> 1 <= c <= 31 ->
  Z.of_nat (length (cl_cache (art_cls_dealloc c w cl))) <= art_ic_mc c.
Proof.
  intros c w cl Hlen Hc. destruct (art_ic_mc_half c Hc) as (Emc & Hh). unfold art_cls_dealloc. destruct (art_cls_full c cl) eqn:EF; unfold art_cls_full in EF.
  - apply Z.eqb_eq in EF. unfold art_cls_push, art_cls_return. cbn [cl_cache]. rewrite length_app, length_firstn. cbn [length]. lia.
  - apply Z.eqb_neq in EF. unfold art_cls_push. cbn [cl_cache]. rewrite length_app. cbn [length]. lia.
Qed.
