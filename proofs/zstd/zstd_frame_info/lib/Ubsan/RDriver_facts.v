(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim STree Malloc MallocCtrl KInv Monad MI_Tree MI_Inv MI_Kit MI_Geom MI_WSlot MI_Sim MI_Contracts.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import ProgDeps.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import MallocRep MallocBlocks MallocTree MallocHINV Malloc_iface MallocFacts_inv.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

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


(* [comment removed for export] *)
Definition rfree_keeps_ptr_stmt : Prop :=
  forall (s s' : PState) (LB : list block) (m : mem) (p : bptr) (A n : Z) (b : block),
    RHEAP s LB m -> In (p, A, n) LB -> mleaf (raw_free p) s tt s' ->
    In b (lb_remove p LB) -> ptr_addr s' (blk_id b) = ptr_addr s (blk_id b).

(* [comment removed for export] *)
(* [comment removed for export] *)

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

#[using="Type"] Lemma mleaf_msys {A} n (dec : resp -> option A) s a s' : mleaf (msys n dec) s a s' -> s' = s.
Proof.
  unfold mleaf, msys, enode. cbn. intros [rsp H]. destruct (dec rsp); cbn in H; [| discriminate H]. inversion H. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ev_step_leaf atop e s z s1 : mleaf (ev_step atop e) s z s1 ->
  ps_m s1 = ps_m s /\ match e with EPeek _ _ _ | EUndef _ => False | _ => True end.
Proof.
  destruct e as [rq|a len prot flags|a len|a len prot|p c h|w]; cbn [ev_step]; intros H.
  - destruct (rq =? 0).
    + apply mleaf_bind in H as (r & s2 & H1 & H2). apply mleaf_msys in H1. subst s2.
      apply mleaf_bind in H2 as (u & s3 & H2 & H3). unfold mleaf, mupd in H2. cbn in H2. inversion H2. subst.
      apply mleaf_ret in H3 as [_ ->]. split; [reflexivity| exact I].
    + apply mleaf_bind in H as (s0 & s2 & H1 & H2). unfold mleaf, mget in H1. cbn in H1. inversion H1. subst.
      apply mleaf_bind in H2 as (aa & s3 & H2 & H3). apply mleaf_msys in H2. subst s3.
      destruct aa.
      * apply mleaf_bind in H3 as (u & s4 & H3 & H4). unfold mleaf, mupd in H3. cbn in H3. inversion H3. subst.
        apply mleaf_ret in H4 as [_ ->]. split; [reflexivity| exact I].
      * apply mleaf_ret in H3 as [_ ->]. split; [reflexivity| exact I].
  - destruct (negb (Z.land flags MAP_FIXED_Z =? 0)); [| destruct (prot =? 0)].
    all: apply mleaf_bind in H as (aa & s2 & H1 & H2); apply mleaf_msys in H1; subst s2; apply mleaf_ret in H2 as [_ ->]; split; [reflexivity| exact I].
  - apply mleaf_bind in H as (aa & s2 & H1 & H2); apply mleaf_msys in H1; subst s2; apply mleaf_ret in H2 as [_ ->]; split; [reflexivity| exact I].
  - apply mleaf_bind in H as (aa & s2 & H1 & H2); apply mleaf_msys in H1; subst s2; apply mleaf_ret in H2 as [_ ->]; split; [reflexivity| exact I].
  - unfold mleaf, munr in H. cbn in H. discriminate H.
  - unfold mleaf, munr in H. cbn in H. discriminate H.
Qed.

#[using="Type"] Lemma membed_leaf {R} (t : stree ev Z R) : forall s r s',
  forall atop, mleaf (membed atop t) s r s' -> ps_m s' = ps_m s /\ exists ans, follow t ans = Some r.
Proof.
  induction t as [r0|e k IH]; intros s r s' atop H; cbn [membed] in H.
  - apply mleaf_ret in H as [-> ->]. split; [reflexivity|]. exists []. reflexivity.
  - apply mleaf_bind in H as (z & s1 & H1 & H2). destruct (ev_step_leaf atop e s z s1 H1) as [E1 NE].
    destruct (IH z s1 r s' atop H2) as [E2 [ans Hf]]. split; [rewrite E2; exact E1|].
    exists (z :: ans). destruct e; try exact Hf; destruct NE.
Qed.

#[using="Type"] Lemma raw_free_leaf p s s' : mleaf (raw_free p) s tt s' ->
  exists ans, follow (cfree (ps_m s) (Some (fst p))) ans = Some (ps_m s').
Proof.
  unfold raw_free. intros H.
  apply mleaf_bind in H as (s0 & s1 & H1 & H2). unfold mleaf, mget in H1. cbn in H1. inversion H1. subst s0 s1.
  apply mleaf_bind in H2 as (cs' & s2 & H2 & H3). destruct (membed_leaf _ _ _ _ _ H2) as [E [ans Hf]].
  unfold mleaf, mupd in H3. cbn in H3. inversion H3. subst s'. exists ans. cbn. exact Hf.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma conc_strip_eq st q : conc (strip st) q = conc st q.
Proof. reflexivity. Qed.

#[using="Type"] Theorem rfree_keeps_ptr_proof : rfree_keeps_ptr_stmt.
Proof.
  intros s s' LB m p A n b (st & LB0 & PERM & STRIP & MREP & [_ AR]) Hp FL Hb.
  destruct (areach_inv _ st LB0 AR) as (L & LS & BL & INV & LIVE & _ & _ & CR).
  (* [comment removed for export] *)
  assert (Hp0 : In (p, A, n) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hp]).
  unfold lb_remove in Hb. apply list_elem_of_In in Hb. apply list_elem_of_filter in Hb as [NEQ Hb]. apply list_elem_of_In in Hb.
  assert (Hb0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb]).
  destruct (Forall2_In_l _ _ _ _ CR Hp0) as (k & Hk & (C1 & C2 & C3)). cbn [blk_slot blk_size blk_addr fst snd] in C1, C2, C3.
  destruct k as [[c off] nn]. cbn [bslot boff bsize fst snd] in C1, C2, C3, Hk. subst nn.
  destruct (Forall2_In_l _ _ _ _ CR Hb0) as (kk & Hkk & (D1 & D2 & D3)).
  (* [comment removed for export] *)
  assert (NE : bslot kk <> c).
  { intros E.
    assert (EM : map blk_slot LB0 = map bslot BL) by (apply (Forall2_map_eq _ _ _ _ _ CR); intros ? ? (X1 & _); exact X1).
    pose proof (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))) as ND. rewrite <- EM in ND. apply NoDup_ListNoDup in ND.
    assert (SS : blk_slot b = blk_slot (p, A, n)) by (rewrite D1, E, C1; reflexivity).
    assert (EQ : forall l (x y : block), List.NoDup (map blk_slot l) -> In x l -> In y l -> blk_slot x = blk_slot y -> x = y).
    { clear. induction l as [|z l IH]; intros x y ND Hx Hy Es; [destruct Hx|]. cbn in ND. inversion ND; subst.
      destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
      - reflexivity.
      - exfalso. apply H1. rewrite Es. apply in_map. exact Hy.
      - exfalso. apply H1. rewrite <- Es. apply in_map. exact Hx.
      - exact (IH x y ltac:(assumption) Hx Hy Es). }
    pose proof (EQ LB0 b (p, A, n) ND Hb0 Hp0 SS) as Eb. subst b.
    unfold bptr_eqb in NEQ. cbn [blk_id fst snd] in NEQ. rewrite aptr_eqb_refl, Z.eqb_refl in NEQ. exact NEQ. }
  (* [comment removed for export] *)
  destruct (raw_free_leaf p s s' FL) as [ans Hf]. rewrite <- STRIP in Hf. change (fst p) with (blk_slot (p, A, n)) in Hf. rewrite C1 in Hf.
  pose proof (strel_follow (free_control pans0 pupd0 st (aadd c (UNIT * off)) c tt (INVL_hdr_ok pans0 pupd0 st L BL LS c off n INV Hk)) ans) as SF.
  rewrite Hf in SF.
  destruct (follow (prun pans0 pupd0 tt (free st (Some (aadd c (UNIT * off))))) ans) as [[o1 st1]|] eqn:FF; [| destruct SF].
  unfold FREL in SF. cbn [snd] in SF.
  destruct (free_leaf_facts pans0 pupd0 st L BL LS c off n tt ans o1 st1 INV Hk FF) as [SUB _].
  destruct (free_sim pans0 pupd0 pans0_range st L BL LS c off n tt ans o1 st1 INV Hk FF) as (_ & _ & _ & LS1 & INV1).
  (* [comment removed for export] *)
  assert (Hk2 : In kk (bl_remove c BL)).
  { rewrite (bl_remove_filter c BL (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))))).
    apply list_elem_of_In. apply list_elem_of_filter. split; [| apply list_elem_of_In; exact Hkk].
    rewrite (MI_Kit.aptr_eqb_neq _ _ NE). exact I. }
  destruct (blk_region _ _ _ _ _ kk INV1 Hk2) as (r1 & Hr1 & _).
  unfold ptr_addr. change (fst (blk_id b)) with (blk_slot b). rewrite D1, <- SF, <- STRIP, !conc_strip_eq.
  rewrite (conc_same st st1 (bslot kk)); [reflexivity|]. exists r1. split; [exact (SUB _ _ Hr1)| exact Hr1].
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
#[using="Type"] Lemma lb_remove_head : forall b LB, List.NoDup (map blk_id (b :: LB)) -> lb_remove (blk_id b) (b :: LB) = LB.
Proof.
  intros b LB ND. cbn [map] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _].
  unfold lb_remove. rewrite filter_cons, bptr_eqb_refl'. destruct (decide _) as [Y|N]; [exfalso; exact Y|].
  apply (lb_remove_notin (blk_id b) LB). exact NI.
Qed.

#[using="Type"] Lemma lb_remove_hd : forall p b LB, blk_id b = p -> List.NoDup (map blk_id (b :: LB)) -> lb_remove p (b :: LB) = LB.
Proof. intros p b LB <- ND. apply lb_remove_head. exact ND. Qed.

(* [comment removed for export] *)
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
