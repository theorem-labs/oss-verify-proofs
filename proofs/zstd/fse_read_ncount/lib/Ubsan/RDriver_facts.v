(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim STree Malloc MallocCtrl KInv Monad MI_Tree MI_Inv MI_Kit MI_Geom MI_WSlot MI_Sim MI_Contracts.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import ProgDeps.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocRep MallocBlocks MallocTree MallocHINV Malloc_iface MallocFacts_inv.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
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
#[using="Type"] Lemma impl_leaves : forall {R} (t : itree node R) (Q : R -> machine_state -> Prop) ms,
impl usegs (at_node usegs) t Q ms -> impl usegs (at_node usegs) t (fun r ms' => Q r ms' /\ tleaf t r) ms.
Proof.
induction t as [r|n k IH]; intros Q ms H; cbn in *.
- eapply evt_mono; [exact H|]. intros ms' HQ. split; [exact HQ| reflexivity].
- eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp.
eapply impl_mono; [apply IH; apply Hk|]. intros r ms' [HQ HL]. split; [exact HQ|]. exists rsp. exact HL.
Qed.
#[using="Type"] Lemma implM_leaves : forall {A} (c : M PState A) s (Q : A -> PState -> machine_state -> Prop) ms,
implM usegs c s Q ms -> implM usegs c s (fun a s' ms' => Q a s' ms' /\ mleaf c s a s') ms.
Proof.
intros A c s Q ms H. unfold implM, mleaf in *. eapply impl_mono; [apply impl_leaves; exact H|].
intros [|[a s']] ms' [HQ HL]; cbn in *; [exact HQ|]. split; assumption.
Qed.
#[using="Type"] Lemma tleaf_bind {A B} (t : itree node A) (f : A -> itree node B) r :
tleaf (ITree.bind _ t f) r -> exists x, tleaf t x /\ tleaf (f x) r.
Proof.
induction t as [a|n k IH]; cbn; intros H.
- exists a. split; [reflexivity| exact H].
- destruct H as [rsp H]. destruct (IH rsp H) as (x & Hx & Hf). exists x. split; [exists rsp; exact Hx| exact Hf].
Qed.
#[using="Type"] Lemma tleaf_ebind {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) r :
tleaf (ebind t f) (Ok r) -> exists a, tleaf t (Ok a) /\ tleaf (f a) (Ok r).
Proof.
unfold ebind. intros H. destruct (tleaf_bind _ _ _ H) as (x & Hx & Hf).
destruct x as [|a]; [cbn in Hf; discriminate Hf|]. exists a. split; assumption.
Qed.
#[using="Type"] Lemma mleaf_bind {A B} (c : Monad.M PState A) (f : A -> Monad.M PState B) s b s' :
mleaf (mbind c f) s b s' -> exists a s1, mleaf c s a s1 /\ mleaf (f a) s1 b s'.
Proof.
unfold mleaf, mbind. intros H. destruct (tleaf_ebind _ _ _ H) as ([a s1] & H1 & H2). exists a, s1. split; assumption.
Qed.
#[using="Type"] Lemma mleaf_ret {A} (a : A) s b s' : mleaf (mret a) s b s' -> b = a /\ s' = s.
Proof. unfold mleaf, mret. cbn. intros H. inversion H. auto. Qed.
#[using="Type"] Lemma bptr_eqb_refl' : forall p, bptr_eqb p p = true.
Proof. intros [[r o] z]. unfold bptr_eqb, aptr_eqb. cbn. rewrite N.eqb_refl, !Z.eqb_refl. reflexivity. Qed.
#[using="Type"] Lemma bptr_eqb_eq : forall p q, bptr_eqb p q = true -> p = q.
Proof.
intros [[r o] z] [[r' o'] z'] H. unfold bptr_eqb, aptr_eqb in H. cbn in H.
apply andb_true_iff in H. destruct H as [H1 H2]. apply andb_true_iff in H1. destruct H1 as [H0 H1].
apply N.eqb_eq in H0. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.
#[using="Type"] Lemma lb_remove_notin : forall p LB, ~ In p (map blk_id LB) -> lb_remove p LB = LB.
Proof.
intros p LB. unfold lb_remove. induction LB as [|b LB IH]; intros H; [reflexivity|].
rewrite filter_cons. cbn [map In] in H. destruct (decide _) as [Y|N].
- rewrite IH; [reflexivity|]. intros H'. apply H. right. exact H'.
- exfalso. destruct (bptr_eqb (blk_id b) p) eqn:E.
+ apply H. left. apply bptr_eqb_eq in E. exact E.
+ apply N. cbn [negb]. exact I.
Qed.
#[using="Type"] Lemma lb_remove_head : forall b LB, List.NoDup (map blk_id (b :: LB)) -> lb_remove (blk_id b) (b :: LB) = LB.
Proof.
intros b LB ND. cbn [map] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _].
unfold lb_remove. rewrite filter_cons, bptr_eqb_refl'. destruct (decide _) as [Y|N]; [exfalso; exact Y|].
apply (lb_remove_notin (blk_id b) LB). exact NI.
Qed.
#[using="Type"] Lemma lb_remove_hd : forall p b LB, blk_id b = p -> List.NoDup (map blk_id (b :: LB)) -> lb_remove p (b :: LB) = LB.
Proof. intros p b LB <- ND. apply lb_remove_head. exact ND. Qed.
#[using="Type"] Lemma lb_remove_second : forall p b0 b LB,
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
