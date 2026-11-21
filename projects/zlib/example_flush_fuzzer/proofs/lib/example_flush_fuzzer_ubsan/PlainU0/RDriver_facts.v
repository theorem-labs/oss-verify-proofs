(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PlainU0 Require Import PImg.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Spec Require Import Prelim STree Malloc MallocCtrl KInv Monad MI_Tree MI_Inv MI_Kit MI_Geom MI_WSlot MI_Sim MI_Contracts.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Malloc Require Import MallocRep MallocBlocks MallocTree MallocHINV Malloc_iface MallocFacts_inv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PlainU0 Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PlainU0 Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.



Section CANSEC1. Context {rc : runConstT}.
Fixpoint tleaf {R} (t : itree node R) (r : R) : Prop :=
  match t with
  | ITree.Ret r' => r' = r
  | ITree.Vis n k => exists rsp, tleaf (k rsp) r
  end.

Definition mleaf {A} (c : M PState A) (s : PState) (a : A) (s' : PState) : Prop := tleaf (c s) (Ok (a, s')).

Lemma impl_leaves : forall {R} (t : itree node R) (Q : R -> machine_state -> Prop) ms,
  impl psegs (at_node psegs) t Q ms -> impl psegs (at_node psegs) t (fun r ms' => Q r ms' /\ tleaf t r) ms.
Proof.
  induction t as [r|n k IH]; intros Q ms H; cbn in *.
  - eapply evt_mono; [exact H|]. intros ms' HQ. split; [exact HQ| reflexivity].
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp.
    eapply impl_mono; [apply IH; apply Hk|]. intros r ms' [HQ HL]. split; [exact HQ|]. exists rsp. exact HL.
Qed.

Lemma implM_leaves : forall {A} (c : M PState A) s (Q : A -> PState -> machine_state -> Prop) ms,
  implM psegs c s Q ms -> implM psegs c s (fun a s' ms' => Q a s' ms' /\ mleaf c s a s') ms.
Proof.
  intros A c s Q ms H. unfold implM, mleaf in *. eapply impl_mono; [apply impl_leaves; exact H|].
  intros [|[a s']] ms' [HQ HL]; cbn in *; [exact HQ|]. split; assumption.
Qed.

















Lemma bptr_eqb_refl' : forall p, bptr_eqb p p = true.
Proof. intros [[r o] z]. unfold bptr_eqb, aptr_eqb. cbn. rewrite N.eqb_refl, !Z.eqb_refl. reflexivity. Qed.

Lemma bptr_eqb_eq : forall p q, bptr_eqb p q = true -> p = q.
Proof.
  intros [[r o] z] [[r' o'] z'] H. unfold bptr_eqb, aptr_eqb in H. cbn in H.
  apply andb_true_iff in H. destruct H as [H1 H2]. apply andb_true_iff in H1. destruct H1 as [H0 H1].
  apply N.eqb_eq in H0. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.

Lemma lb_remove_notin : forall p LB, ~ In p (map blk_id LB) -> lb_remove p LB = LB.
Proof.
  intros p LB. unfold lb_remove. induction LB as [|b LB IH]; intros H; [reflexivity|].
  rewrite filter_cons. cbn [map In] in H. destruct (decide _) as [Y|N].
  - rewrite IH; [reflexivity|]. intros H'. apply H. right. exact H'.
  - exfalso. destruct (bptr_eqb (blk_id b) p) eqn:E.
    + apply H. left. apply bptr_eqb_eq in E. exact E.
    + apply N. cbn [negb]. exact I.
Qed.

Lemma lb_remove_head : forall b LB, List.NoDup (map blk_id (b :: LB)) -> lb_remove (blk_id b) (b :: LB) = LB.
Proof.
  intros b LB ND. cbn [map] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _].
  unfold lb_remove. rewrite filter_cons, bptr_eqb_refl'. destruct (decide _) as [Y|N]; [exfalso; exact Y|].
  apply (lb_remove_notin (blk_id b) LB). exact NI.
Qed.


Lemma lb_remove_second : forall p b0 b LB,
  blk_id b = p -> List.NoDup (map blk_id (b0 :: b :: LB)) -> lb_remove p (b0 :: b :: LB) = b0 :: LB.
Proof.
  intros p b0 b LB <- ND. unfold lb_remove. rewrite filter_cons.
  cbn [map] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI ND].
  destruct (decide _) as [Y|N].
  - f_equal. apply (lb_remove_head b LB). exact ND.
  - exfalso. apply N. destruct (bptr_eqb (blk_id b0) (blk_id b)) eqn:E; [| exact I].
    apply bptr_eqb_eq in E. apply NI. left. symmetry. exact E.
Qed.
End CANSEC1.
