(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image Arr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prog.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma lb_remove_cons : forall p b L,
  lb_remove p (b :: L) = if bptr_eqb (blk_id b) p then lb_remove p L else b :: lb_remove p L.
Proof.
  intros p b L. unfold lb_remove. rewrite filter_cons. destruct (bptr_eqb (blk_id b) p); cbn [negb];
    destruct (decide _) as [Y|N]; try reflexivity; [exfalso; exact Y| exfalso; apply N; exact I].
Qed.

Lemma lb_remove_In : forall p L b, In b (lb_remove p L) <-> In b L /\ blk_id b <> p.
Proof.
  intros p L b. induction L as [|c L IH]; [cbn; tauto|].
  rewrite lb_remove_cons. destruct (bptr_eqb (blk_id c) p) eqn:E.
  - apply bptr_eqb_eq in E. rewrite IH. cbn [In]. split; [intros [H N]; split; [right; exact H| exact N]|].
    intros [[<-|H] N]; [contradiction| split; assumption].
  - cbn [In]. rewrite IH. split; [intros [<-|[H N]]; [split; [left; reflexivity|]| split; [right; exact H| exact N]]|].
    + intros E2. rewrite E2, bptr_eqb_refl in E. discriminate.
    + intros [[<-|H] N]; [left; reflexivity| right; split; assumption].
Qed.

Lemma lb_remove_app : forall p L1 L2, lb_remove p (L1 ++ L2) = lb_remove p L1 ++ lb_remove p L2.
Proof.
  intros p L1 L2. induction L1 as [|c L1 IH]; [reflexivity|].
  cbn [app]. rewrite !lb_remove_cons. destruct (bptr_eqb (blk_id c) p); [exact IH| cbn [app]; rewrite IH; reflexivity].
Qed.

Lemma lb_remove_incl : forall p L b, In b (lb_remove p L) -> In b L.
Proof. intros p L b H. apply lb_remove_In in H. tauto. Qed.

Lemma lb_remove_app_l : forall p OW LB, List.NoDup (map blk_id (OW ++ LB)) -> In p (map blk_id OW) ->
  lb_remove p (OW ++ LB) = lb_remove p OW ++ LB.
Proof.
  intros p OW LB ND Hin. rewrite lb_remove_app. f_equal. apply lb_remove_notin.
  rewrite map_app in ND. intros H. revert ND Hin H. generalize (map blk_id OW) (map blk_id LB). clear.
  intros l1 l2 ND H1 H2. induction l1 as [|x l1 IH]; [contradiction|].
  cbn [app] in ND. apply NoDup_cons_iff in ND. destruct ND as [Hx ND]. destruct H1 as [->|H1]; [|auto].
  apply Hx. apply in_or_app. right. exact H2.
Qed.

Lemma nodup_app_l : forall {A} (l1 l2 : list A), List.NoDup (l1 ++ l2) -> List.NoDup l1.
Proof. intros A l1 l2 H. induction l1 as [|x l1 IH]; [constructor|]. cbn in H. apply NoDup_cons_iff in H. destruct H as [Hx H].
  constructor; [intros Hin; apply Hx; apply in_or_app; left; exact Hin| auto]. Qed.

Lemma nodup_app_r : forall {A} (l1 l2 : list A), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof. intros A l1 l2 H. induction l1 as [|x l1 IH]; [exact H|]. cbn in H. apply NoDup_cons_iff in H. tauto. Qed.

Lemma nodup_app_disj : forall {A} (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  intros A l1 l2 x H H1 H2. induction l1 as [|y l1 IH]; [contradiction|]. cbn in H. apply NoDup_cons_iff in H. destruct H as [Hy H].
  destruct H1 as [->|H1]; [apply Hy; apply in_or_app; right; exact H2| auto].
Qed.

Lemma RH_nodup_l : forall s OW LB m, RHEAP s (OW ++ LB) m -> List.NoDup (map blk_id OW).
Proof. intros s OW LB m H. apply LH_nodup in H. rewrite map_app in H. eapply nodup_app_l; exact H. Qed.

Lemma RH_range : forall s OW LB m p A n, RHEAP s (OW ++ LB) m -> In (p, A, n) OW -> rblock_range A n.
Proof. intros s OW LB m p A n H Hin. exact (LH_block_range s (OW ++ LB) m (p, A, n) H ltac:(apply in_or_app; left; exact Hin)). Qed.

Lemma RH_disjoint : forall s OW LB m p A n p' A' n',
  RHEAP s (OW ++ LB) m -> In (p, A, n) OW -> In (p', A', n') OW -> p <> p' -> A + n <= A' \/ A' + n' <= A.
Proof.
  intros s OW LB m p A n p' A' n' H H1 H2 NE.
  exact (LH_disjoint s (OW ++ LB) m (p, A, n) (p', A', n') H ltac:(apply in_or_app; left; exact H1) ltac:(apply in_or_app; left; exact H2) NE).
Qed.

Lemma RH_addr_unique : forall (OW : list block) p A n A' n',
  List.NoDup (map blk_id OW) -> In (p, A, n) OW -> In (p, A', n') OW -> A = A' /\ n = n'.
Proof.
  intros OW p A n A' n' ND H1 H2. induction OW as [|c OW IH]; [contradiction|].
  cbn [map] in ND. apply NoDup_cons_iff in ND. destruct ND as [Hc ND].
  destruct H1 as [->|H1], H2 as [E|H2].
  - inversion E. auto.
  - exfalso. apply Hc. apply (in_map blk_id) in H2. exact H2.
  - subst c. exfalso. apply Hc. apply (in_map blk_id) in H1. exact H1.
  - auto.
Qed.

End WithCeiling0.
