(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import ITree.
From OSSVerify.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Prog Harness LB_PTarget.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require MI_Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bptr_eqb_eq : forall p q : bptr, bptr_eqb p q = true -> p = q.
Proof.
  intros p q E. unfold bptr_eqb in E. apply andb_true_iff in E. destruct E as [E1 E2].
  apply MI_Kit.aptr_eqb_eq in E1. apply Z.eqb_eq in E2. destruct p as [c1 o1], q as [c2 o2]. cbn in *. subst. reflexivity.
Qed.
Lemma bptr_eqb_refl : forall p : bptr, bptr_eqb p p = true.
Proof. intros p. unfold bptr_eqb. rewrite MI_Kit.aptr_eqb_refl, Z.eqb_refl. reflexivity. Qed.

Lemma lb_remove_cons_eq : forall (p : bptr) b LB, blk_id b = p -> lb_remove p (b :: LB) = lb_remove p LB.
Proof.
  intros p b LB E. unfold lb_remove. rewrite filter_cons. destruct (decide (negb (bptr_eqb (blk_id b) p))) as [D|D]; [| reflexivity].
  exfalso. rewrite E, bptr_eqb_refl in D. exact D.
Qed.
Lemma lb_remove_cons_ne : forall (p : bptr) b LB, blk_id b <> p -> lb_remove p (b :: LB) = b :: lb_remove p LB.
Proof.
  intros p b LB NE. unfold lb_remove. rewrite filter_cons. destruct (decide (negb (bptr_eqb (blk_id b) p))) as [D|D]; [reflexivity|].
  exfalso. apply D. destruct (bptr_eqb (blk_id b) p) eqn:EB; [| exact I]. exfalso. apply NE. apply bptr_eqb_eq. exact EB.
Qed.

Lemma lb_remove_notin' : forall (p : bptr) LB, ~ In p (map blk_id LB) -> lb_remove p LB = LB.
Proof.
  intros p LB. induction LB as [|b LB IH]; intros NI; [reflexivity|].
  rewrite lb_remove_cons_ne by (intros E; apply NI; left; exact E). f_equal. apply IH. intros H. apply NI. right. exact H.
Qed.

Lemma lb_remove_app : forall (p : bptr) l1 l2, lb_remove p (l1 ++ l2) = lb_remove p l1 ++ lb_remove p l2.
Proof.
  intros p l1 l2. induction l1 as [|b l1 IH]; [reflexivity|]. cbn [app].
  destruct (decide (blk_id b = p)) as [E|NE].
  - rewrite !lb_remove_cons_eq by exact E. exact IH.
  - rewrite !lb_remove_cons_ne by exact NE. cbn [app]. f_equal. exact IH.
Qed.

Lemma lb_remove_In : forall (p : bptr) LB b, In b (lb_remove p LB) <-> In b LB /\ blk_id b <> p.
Proof.
  intros p LB b. induction LB as [|c LB IH]; [cbn; tauto|].
  destruct (decide (blk_id c = p)) as [E|NE].
  - rewrite lb_remove_cons_eq by exact E. rewrite IH. cbn [In]. split; [tauto|]. intros [[->|H] N]; [contradiction| tauto].
  - rewrite lb_remove_cons_ne by exact NE. cbn [In]. rewrite IH. split; [| tauto]. intros [->|H]; tauto.
Qed.

Lemma lb_remove_perm : forall (p : bptr) l l', Permutation l l' -> Permutation (lb_remove p l) (lb_remove p l').
Proof.
  intros p l l' H. induction H as [|b l l' _ IH|b c l|l l' l'' _ IH1 _ IH2].
  - apply Permutation_refl.
  - destruct (decide (blk_id b = p)) as [E|NE].
    + rewrite !lb_remove_cons_eq by exact E. exact IH.
    + rewrite !lb_remove_cons_ne by exact NE. apply perm_skip. exact IH.
  - destruct (decide (blk_id b = p)) as [E|NE]; destruct (decide (blk_id c = p)) as [E'|NE'];
      rewrite ?(lb_remove_cons_eq p b) by exact E; rewrite ?(lb_remove_cons_eq p c) by exact E';
      rewrite ?(lb_remove_cons_ne p b) by exact NE; rewrite ?(lb_remove_cons_ne p c) by exact NE';
      rewrite ?(lb_remove_cons_eq p b) by exact E; rewrite ?(lb_remove_cons_eq p c) by exact E';
      rewrite ?(lb_remove_cons_ne p b) by exact NE; rewrite ?(lb_remove_cons_ne p c) by exact NE';
      try apply Permutation_refl. apply perm_swap.
  - eapply Permutation_trans; eassumption.
Qed.

(* [comment removed for export] *)
Lemma lb_remove_split : forall (p : bptr) l1 b l2, blk_id b = p -> List.NoDup (map blk_id (l1 ++ b :: l2)) -> lb_remove p (l1 ++ b :: l2) = l1 ++ l2.
Proof.
  intros p l1 b l2 E ND. rewrite lb_remove_app, lb_remove_cons_eq by exact E.
  rewrite map_app in ND. cbn [map] in ND. apply List.NoDup_remove in ND. destruct ND as [_ NI]. rewrite E in NI.
  rewrite !lb_remove_notin'; [reflexivity| |]; intros H; apply NI; apply in_or_app; [right| left]; exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CList.
Context {ptr : Type}.
Implicit Types L : @clist ptr.

Lemma cremove_split : forall L i x, nth_error L i = Some x -> exists l1 l2, L = l1 ++ x :: l2 /\ length l1 = i /\ cremove i L = l1 ++ l2.
Proof.
  induction L as [|y L IH]; intros i x H; destruct i; cbn in H; try discriminate.
  - inversion H; subst. exists [], L. auto.
  - destruct (IH i x H) as (l1 & l2 & -> & Hl & E). exists (y :: l1), l2. cbn. rewrite E, Hl. auto.
Qed.

Lemma In_nth_error_pair : forall L (p : ptr) nm, In (p, nm) L -> exists i, nth_error L i = Some (p, nm).
Proof. intros L p nm H. apply In_nth_error in H. exact H. Qed.

(* [comment removed for export] *)
Definition wA (n : Z) : Z := if n <=? TIER_A_MAX then 1 else 0.
Definition wB (n : Z) : Z := if TIER_A_MAX <? n then 1 else 0.
Definition wBig (n : Z) : Z := if TIER_A_MAX <? n then n + 8192 else 0.

Lemma wA_small : forall n, n <= TIER_A_MAX -> wA n = 1 /\ wB n = 0 /\ wBig n = 0.
Proof. intros n H. unfold wA, wB, wBig. destruct (Z.leb_spec n TIER_A_MAX); destruct (Z.ltb_spec TIER_A_MAX n); try lia; auto. Qed.
Lemma wB_big : forall n, TIER_A_MAX < n -> wA n = 0 /\ wB n = 1 /\ wBig n = n + 8192.
Proof. intros n H. unfold wA, wB, wBig. destruct (Z.leb_spec n TIER_A_MAX); destruct (Z.ltb_spec TIER_A_MAX n); try lia; auto. Qed.
Lemma w_bounds : forall n, 0 <= n -> 0 <= wA n <= 1 /\ 0 <= wB n <= 1 /\ wA n + wB n = 1 /\ 0 <= wBig n <= n + 8192.
Proof. intros n H. unfold wA, wB, wBig. destruct (Z.leb_spec n TIER_A_MAX); destruct (Z.ltb_spec TIER_A_MAX n); lia. Qed.

Definition croom L (na nb big : Z) : Prop := cntA L + na <= CAP_A /\ cntB L + nb <= CAP_B /\ bigsum L + big <= BIG_ROOM.
Definition cgrow L L' (da db dbig : Z) : Prop := cntA L' <= cntA L + da /\ cntB L' <= cntB L + db /\ bigsum L' <= bigsum L + dbig.

Lemma croom_cvalid : forall L n, croom L (wA n) (wB n) (wBig n) -> 0 <= n < SZ_MAX -> cvalid L (Cho 1 n 0).
Proof.
  intros L n (H1 & H2 & H3) Hn. cbn [cvalid]. split; [exact Hn|]. split.
  - intros Hs. destruct (wA_small n Hs) as (E & _ & _). lia.
  - intros Hb. destruct (wB_big n Hb) as (_ & E1 & E2). lia.
Qed.
(* [comment removed for export] *)
Lemma croom_cvalid' : forall L n, croom L 1 1 (n + 8192) -> 0 <= n < SZ_MAX -> cvalid L (Cho 1 n 0).
Proof. intros L n (H1 & H2 & H3) Hn. apply croom_cvalid; [| exact Hn]. pose proof (w_bounds n ltac:(lia)). unfold croom. lia. Qed.

Lemma croom_weaken : forall L na nb big na' nb' big', croom L na nb big -> na' <= na -> nb' <= nb -> big' <= big -> croom L na' nb' big'.
Proof. unfold croom. intros. lia. Qed.
Lemma croom_grow : forall L L' na nb big da db dbig, croom L na nb big -> cgrow L L' da db dbig -> croom L' (na - da) (nb - db) (big - dbig).
Proof. unfold croom, cgrow. intros. lia. Qed.

Lemma cgrow_refl : forall L, cgrow L L 0 0 0.
Proof. unfold cgrow. intros. lia. Qed.
Lemma cgrow_trans : forall L1 L2 L3 a b c a' b' c', cgrow L1 L2 a b c -> cgrow L2 L3 a' b' c' -> cgrow L1 L3 (a + a') (b + b') (c + c').
Proof. unfold cgrow. intros. lia. Qed.
Lemma cgrow_weaken : forall L L' a b c a' b' c', cgrow L L' a b c -> a <= a' -> b <= b' -> c <= c' -> cgrow L L' a' b' c'.
Proof. unfold cgrow. intros. lia. Qed.
Lemma cgrow_cons : forall L (p : ptr) n, cgrow L ((p, n) :: L) (wA n) (wB n) (wBig n).
Proof. intros L p n. unfold cgrow, wA, wB, wBig. rewrite cntA_cons, cntB_cons, bigsum_cons. cbn [snd]. lia. Qed.
Lemma cgrow_remove : forall L i (p : ptr) nm, nth_error L i = Some (p, nm) -> cgrow L (cremove i L) (- wA nm) (- wB nm) (- wBig nm).
Proof.
  intros L i p nm H. destruct (perm_counts _ _ (cremove_perm L i _ H)) as (E1 & E2 & E3).
  rewrite cntA_cons in E1. rewrite cntB_cons in E2. rewrite bigsum_cons in E3. cbn [snd] in *. unfold cgrow, wA, wB, wBig. lia.
Qed.
End CList.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cown (LBall : list block) (L : @clist bptr) (p : bptr) (A n nm : Z) : Prop := In (p, A, n) LBall /\ In (p, nm) L.

Definition cl_own (LBall LB : list block) (L : @clist bptr) : Prop :=
  exists CLB, Permutation LBall (CLB ++ LB) /\ map blk_id CLB = map fst L.

Lemma cl_own_nil : forall LB, cl_own LB LB [].
Proof. intros LB. exists []. split; [apply Permutation_refl| reflexivity]. Qed.

Lemma cl_own_cons : forall LBall LB L p A n nm, cl_own LBall LB L -> cl_own ((p, A, n) :: LBall) LB ((p, nm) :: L).
Proof.
  intros LBall LB L p A n nm (CLB & HP & HM). exists ((p, A, n) :: CLB). split; [cbn [app]; apply perm_skip; exact HP|].
  cbn [map fst blk_id]. f_equal. exact HM.
Qed.

Lemma cl_own_nodup : forall LBall LB L, cl_own LBall LB L -> List.NoDup (map blk_id LBall) -> List.NoDup (map fst L).
Proof.
  intros LBall LB L (CLB & HP & HM) ND. rewrite <- HM.
  assert (ND' : List.NoDup (map blk_id (CLB ++ LB))) by (eapply Permutation.Permutation_NoDup; [apply Permutation_map; exact HP| exact ND]).
  rewrite map_app in ND'. apply List.NoDup_app_remove_r in ND'. exact ND'.
Qed.

(* [comment removed for export] *)
Lemma cl_own_relist : forall LBall LB L p A n A' n' nm, cl_own ((p, A, n) :: LBall) LB L -> List.NoDup (map blk_id ((p, A, n) :: LBall)) -> In (p, nm) L ->
  cl_own ((p, A', n') :: LBall) LB L.
Proof.
  intros LBall LB L p A n A' n' nm (CLB & HP & HM) ND HL.
  assert (ND' : List.NoDup (map blk_id (CLB ++ LB))) by (eapply Permutation.Permutation_NoDup; [apply Permutation_map; exact HP| exact ND]).
  assert (IN : In (p, A, n) (CLB ++ LB)) by (eapply Permutation_in; [exact HP| left; reflexivity]).
  assert (I1 : In p (map blk_id CLB)) by (rewrite HM; apply in_map_iff; exists (p, nm); auto).
  assert (INC : In (p, A, n) CLB).
  { apply in_app_or in IN. destruct IN as [IN|IN]; [exact IN|]. exfalso.
    assert (I2 : In p (map blk_id LB)) by (apply in_map_iff; exists (p, A, n); auto).
    rewrite map_app in ND'. clear - ND' I1 I2. induction (map blk_id CLB) as [|x l IH]; [destruct I1|]. cbn [app] in ND'. inversion ND'; subst.
    destruct I1 as [->|I1]; [apply H1; apply in_or_app; right; exact I2| apply IH; assumption]. }
  apply in_split in INC. destruct INC as (c1 & c2 & ->).
  exists (c1 ++ (p, A', n') :: c2). split.
  - rewrite <- app_assoc in HP |- *. cbn [app] in HP |- *. apply Permutation_cons_app. eapply Permutation_cons_app_inv. exact HP.
  - rewrite <- HM, !map_app. reflexivity.
Qed.

Lemma cl_own_remove : forall LBall LB L i p nm, cl_own LBall LB L -> List.NoDup (map blk_id LBall) -> nth_error L i = Some (p, nm) ->
  cl_own (lb_remove p LBall) LB (cremove i L).
Proof.
  intros LBall LB L i p nm (CLB & HP & HM) ND HN.
  destruct (cremove_split L i _ HN) as (l1 & l2 & EL & Hl & EC).
  assert (ND' : List.NoDup (map blk_id (CLB ++ LB))) by (eapply Permutation.Permutation_NoDup; [apply Permutation_map; exact HP| exact ND]).
  (* [comment removed for export] *)
  rewrite EL, map_app in HM. cbn [map fst] in HM.
  apply map_eq_app in HM. destruct HM as (c1 & c2' & EC1 & M1 & M2).
  destruct c2' as [|b c2]; [discriminate|]. cbn [map] in M2. injection M2 as Eb M2.
  subst CLB. exists (c1 ++ c2). split.
  - eapply Permutation_trans; [apply lb_remove_perm; exact HP|].
    rewrite <- app_assoc in ND' |- *. cbn [app] in ND' |- *. rewrite (lb_remove_split p c1 b (c2 ++ LB) Eb ND'). rewrite app_assoc. apply Permutation_refl.
  - rewrite EC, !map_app, M1, M2. reflexivity.
Qed.

Lemma cown_nth : forall LBall L p A n nm, cown LBall L p A n nm -> exists i, nth_error L i = Some (p, nm).
Proof. intros LBall L p A n nm [_ H]. apply In_nth_error in H. exact H. Qed.

Lemma cown_new : forall LBall L p A n nm, cown ((p, A, n) :: LBall) ((p, nm) :: L) p A n nm.
Proof. intros. split; left; reflexivity. Qed.
Lemma cown_cons : forall LBall L b x q A n nm, cown LBall L q A n nm -> cown (b :: LBall) (x :: L) q A n nm.
Proof. intros LBall L b x q A n nm [H1 H2]. split; right; assumption. Qed.
Lemma cown_remove : forall LBall L i p nm0 q A n nm, cown LBall L q A n nm -> nth_error L i = Some (p, nm0) -> q <> p ->
  cown (lb_remove p LBall) (cremove i L) q A n nm.
Proof.
  intros LBall L i p nm0 q A n nm [H1 H2] HN NE. split.
  - apply lb_remove_In. split; [exact H1| exact NE].
  - destruct (cremove_split L i _ HN) as (l1 & l2 & EL & _ & EC). rewrite EC. rewrite EL in H2.
    apply in_app_or in H2. apply in_or_app. destruct H2 as [H2|[H2|H2]]; [left; exact H2| | right; exact H2].
    exfalso. apply NE. inversion H2. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cown_not_driver : forall LBall LB L p A n nm b, cl_own LBall LB L -> List.NoDup (map blk_id LBall) -> cown LBall L p A n nm -> In b LB -> blk_id b <> p.
Proof.
  intros LBall LB L p A n nm b (CLB & HP & HM) ND [_ H2] Hb E.
  assert (ND' : List.NoDup (map blk_id (CLB ++ LB))) by (eapply Permutation.Permutation_NoDup; [apply Permutation_map; exact HP| exact ND]).
  rewrite map_app in ND'. assert (I1 : In p (map blk_id CLB)) by (rewrite HM; apply in_map_iff; exists (p, nm); auto).
  assert (I2 : In p (map blk_id LB)) by (apply in_map_iff; exists b; auto).
  clear - ND' I1 I2. induction (map blk_id CLB) as [|x l IH]; [destruct I1|]. cbn [app] in ND'. inversion ND'; subst.
  destruct I1 as [->|I1]; [apply H1; apply in_or_app; right; exact I2| apply IH; assumption].
Qed.

(* [comment removed for export] *)
Lemma cown_block_eq : forall LBall (p : bptr) A n A' n', List.NoDup (map blk_id LBall) -> In (p, A, n) LBall -> In (p, A', n') LBall -> A = A' /\ n = n'.
Proof.
  intros LBall p A n A' n' ND. induction LBall as [|b LBall IH]; intros H1 H2; [destruct H1|]. cbn [map] in ND. inversion ND; subst.
  destruct H1 as [->|H1], H2 as [E|H2].
  - inversion E. auto.
  - exfalso. apply H3. apply in_map_iff. exists (p, A', n'). auto.
  - exfalso. apply H3. subst b. apply in_map_iff. exists (p, A, n). auto.
  - apply IH; assumption.
Qed.
