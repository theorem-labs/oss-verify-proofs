(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad STree Malloc Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive sysop : Type := SyGetuid | SyGeteuid | SyGetgid | SyGetegid | SyOpenCnf.

Inductive lprog (A : Type) : Type :=
| LRet (a : A)
| LUnr
| LMalloc (n : Z) (k : option bptr -> lprog A)
| LFree (p : bptr) (k : lprog A)
| LRealloc (p : bptr) (n : Z) (k : option bptr -> lprog A)
| LSys (o : sysop) (k : Z -> lprog A)                              (* [comment removed for export] *)
| LAligned (al n : Z) (k : option bptr -> lprog A)                 (* [comment removed for export] *)
| LReallocS (p : bptr) (n : Z) (k : option bptr -> lprog A)        (* [comment removed for export] *)
| LReallocI (p : bptr) (n : Z) (k : option bptr -> lprog A).       (* [comment removed for export] *)
Arguments LRet {A} a.
Arguments LUnr {A}.
Arguments LMalloc {A} n k.
Arguments LFree {A} p k.
Arguments LRealloc {A} p n k.
Arguments LSys {A} o k.
Arguments LAligned {A} al n k.
Arguments LReallocS {A} p n k.
Arguments LReallocI {A} p n k.

Fixpoint lbind {A B} (m : lprog A) (f : A -> lprog B) : lprog B :=
  match m with
  | LRet a => f a
  | LUnr => LUnr
  | LMalloc n k => LMalloc n (fun r => lbind (k r) f)
  | LFree p k => LFree p (lbind k f)
  | LRealloc p n k => LRealloc p n (fun r => lbind (k r) f)
  | LSys o k => LSys o (fun r => lbind (k r) f)
  | LAligned al n k => LAligned al n (fun r => lbind (k r) f)
  | LReallocS p n k => LReallocS p n (fun r => lbind (k r) f)
  | LReallocI p n k => LReallocI p n (fun r => lbind (k r) f)
  end.

(* [comment removed for export] *)
Definition lmalloc (n : Z) : lprog (option bptr) := LMalloc n (fun r => LRet r).
Definition lfree (p : bptr) : lprog unit := LFree p (LRet tt).
Definition lrealloc (p : bptr) (n : Z) : lprog (option bptr) := LRealloc p n (fun r => LRet r).
Definition lmalloc' (n : Z) : lprog bptr :=
  LMalloc n (fun r => match r with Some p => LRet p | None => LUnr end).
Definition lrealloc' (p : bptr) (n : Z) : lprog bptr :=
  LRealloc p n (fun r => match r with Some q => LRet q | None => LUnr end).
(* [comment removed for export] *)
Definition lreallocS' (p : bptr) (n : Z) : lprog bptr :=
  LReallocS p n (fun r => match r with Some q => LRet q | None => LUnr end).
(* [comment removed for export] *)
Definition lreallocI' (p : bptr) (n : Z) : lprog bptr :=
  LReallocI p n (fun r => match r with Some q => LRet q | None => LUnr end).
(* [comment removed for export] *)
Definition lfree_opt (p : option bptr) : lprog unit := match p with Some q => lfree q | None => LRet tt end.
(* [comment removed for export] *)
Definition lsys_ (o : sysop) : lprog Z := LSys o (fun r => LRet r).

Lemma lbind_ret_l {A B} (a : A) (f : A -> lprog B) : lbind (LRet a) f = f a.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive lop : Type :=
| OpMalloc (n : Z)
| OpFree (k : nat)
| OpRealloc (k : nat) (n : Z)
| OpAligned (al n : Z).          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition lenv : Type := list (option (bptr * Z)).

(* [comment removed for export] *)
Definition aligned_req (al n : Z) : Z := n + al - 16.

Fixpoint set_nth {A} (k : nat) (x : A) (l : list A) : list A :=
  match k, l with
  | _, [] => []
  | O, _ :: l' => x :: l'
  | S k', y :: l' => y :: set_nth k' x l'
  end.

(* [comment removed for export] *)
Fixpoint run_ops (ops : list lop) (env : lenv) : lprog lenv :=
  match ops with
  | [] => LRet env
  | OpMalloc n :: ops' =>
      LMalloc n (fun r => match r with Some p => run_ops ops' (env ++ [Some (p, n)]) | None => LUnr end)
  | OpFree k :: ops' =>
      match nth k env None with
      | Some (p, _) => LFree p (run_ops ops' (set_nth k None env))
      | None => LUnr
      end
  | OpRealloc k n :: ops' =>
      match nth k env None with
      | Some (p, _) =>
          LRealloc p n (fun r => match r with
                                 | Some q => run_ops ops' (set_nth k None env ++ [Some (q, n)])
                                 | None => LUnr
                                 end)
      | None => LUnr
      end
  | OpAligned al n :: ops' =>      (* [comment removed for export] *)
      LAligned al n (fun r => match r with Some p => run_ops ops' (env ++ [Some (p, n)]) | None => LUnr end)
  end.

(* [comment removed for export] *)
Fixpoint live_env (env : lenv) : list (bptr * Z) :=
  match env with
  | [] => []
  | Some b :: env' => b :: live_env env'
  | None :: env' => live_env env'
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeiling. Context {CE__ : Ceiling}.

Local Notation MP := (Monad.M PState) (only parsing).

(* [comment removed for export] *)
Definition realloc_moves (cs : mstate) (slot : cptr) (n : Z) : bool :=
  match (s_slots cs) !! slot with
  | Some (g, idx) =>
      let mr := get_meta_rec cs g in
      (get_stride mr - IB <? n) && ((m_sizeclass mr <? 48) || (n <? MMAP_THRESHOLD))
  | None => false
  end.

Definition raw_realloc (p : bptr) (n : Z) : MP (option bptr) :=
  s <- mget ;;
  if size_overflows n then mret None
  else if realloc_moves (ps_m s) (fst p) n then
    r <- raw_malloc n ;;
    match r with
    | None => mret None
    | Some q => raw_free p ;;; mret (Some q)
    end
  else munr.

(* [comment removed for export] *)
Definition realloc_shrinks (cs : mstate) (slot : cptr) (n : Z) : bool :=
  match (s_slots cs) !! slot with
  | Some (g, idx) =>
      let mr := get_meta_rec cs g in
      (size_to_class n + 1 <? m_sizeclass mr) && (m_sizeclass mr <? 48)
  | None => false
  end.

(* [comment removed for export] *)
Lemma realloc_shrinks_true : forall cs slot n,
  realloc_shrinks cs slot n = true <->
  exists g idx, (s_slots cs) !! slot = Some (g, idx)
                /\ size_to_class n + 1 < m_sizeclass (get_meta_rec cs g) /\ m_sizeclass (get_meta_rec cs g) < 48.
Proof.
  intros cs slot n. unfold realloc_shrinks. destruct (s_slots cs !! slot) as [[g idx]|].
  - split.
    + intros H. apply andb_prop in H as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. exists g, idx. auto.
    + intros (g' & idx' & E & H1 & H2). injection E as <- <-. apply andb_true_intro. split; apply Z.ltb_lt; assumption.
  - split; [discriminate|]. intros (g' & idx' & E & _). discriminate E.
Qed.

Definition raw_realloc_shrink (p : bptr) (n : Z) : MP (option bptr) :=
  s <- mget ;;
  if size_overflows n then mret None
  else if realloc_shrinks (ps_m s) (fst p) n then
    r <- raw_malloc n ;;
    match r with
    | None => mret None
    | Some q => raw_free p ;;; mret (Some q)
    end
  else munr.

(* [comment removed for export] *)
Definition realloc_inplace (cs : mstate) (slot : cptr) (n : Z) : bool :=
  match (s_slots cs) !! slot with
  | Some (g, idx) =>
      let mr := get_meta_rec cs g in
      (n <? MMAP_THRESHOLD) && (m_sizeclass mr <=? size_to_class n + 1) && (m_sizeclass mr <? 48)
  | None => false
  end.

(* [comment removed for export] *)
Lemma realloc_inplace_true : forall cs slot n,
  realloc_inplace cs slot n = true <->
  exists g idx, (s_slots cs) !! slot = Some (g, idx)
                /\ n < MMAP_THRESHOLD /\ m_sizeclass (get_meta_rec cs g) <= size_to_class n + 1 /\ m_sizeclass (get_meta_rec cs g) < 48.
Proof.
  intros cs slot n. unfold realloc_inplace. destruct (s_slots cs !! slot) as [[g idx]|].
  - split.
    + intros H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
      apply Z.ltb_lt in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3. exists g, idx. auto.
    + intros (g' & idx' & E & H1 & H2 & H3). injection E as <- <-.
      apply andb_true_intro. split; [apply andb_true_intro; split; [apply Z.ltb_lt| apply Z.leb_le]| apply Z.ltb_lt]; assumption.
  - split; [discriminate|]. intros (g' & idx' & E & _). discriminate E.
Qed.

Definition raw_realloc_inplace (p : bptr) (n : Z) : MP (option bptr) :=
  s <- mget ;;
  if size_overflows n then mret None
  else if realloc_inplace (ps_m s) (fst p) n then mret (Some p)
  else munr.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sys_node (o : sysop) : node :=
  match o with
  | SyGetuid => NGetid IdUid | SyGeteuid => NGetid IdEuid | SyGetgid => NGetid IdGid | SyGetegid => NGetid IdEgid
  | SyOpenCnf => NOpenCnf
  end.
Definition sys_dec (o : sysop) : resp -> option Z :=
  match o with SyOpenCnf => dec_cnf | _ => dec_getid end.

Definition lsys (o : sysop) : MP Z := msys (sys_node o) (sys_dec o).

(* [comment removed for export] *)
Definition sys_res (o : sysop) (r : Z) : Prop :=
  match o with SyOpenCnf => r = - ENOENT | _ => 0 <= r < 2^64 end.

(* [comment removed for export] *)
Definition sys_pre (o : sysop) : Prop :=
  match o with SyOpenCnf => cnf_arm_present | _ => True end.
Lemma sys_pre_nsafe : forall o mo, sys_pre o -> nsafe (sys_node o) mo.
Proof. intros o mo H. destruct o; cbn [sys_node nsafe sys_pre] in *; first [exact I| exact H]. Qed.
Lemma sys_dec_res : forall o rsp r, sys_dec o rsp = Some r -> sys_res o r.
Proof.
  intros o rsp r H. destruct o; cbn [sys_dec sys_res] in *;
    try (apply dec_getid_Some in H; exact (proj2 H)). apply dec_cnf_Some in H. exact (proj2 H).
Qed.

(* [comment removed for export] *)
Definition raw_aligned_alloc (al n : Z) : MP (option bptr) := raw_malloc (aligned_req al n).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint interp {A} (t : lprog A) : MP A :=
  match t with
  | LRet a => mret a
  | LUnr => munr
  | LMalloc n k => r <- raw_malloc n ;; interp (k r)
  | LFree p k => raw_free p ;;; interp k
  | LRealloc p n k => r <- raw_realloc p n ;; interp (k r)
  | LSys o k => r <- lsys o ;; interp (k r)
  | LAligned al n k => r <- raw_aligned_alloc al n ;; interp (k r)
  | LReallocS p n k => r <- raw_realloc_shrink p n ;; interp (k r)
  | LReallocI p n k => r <- raw_realloc_inplace p n ;; interp (k r)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Machine.
Variable segs : list Segment.

Lemma implM_interp_ret : forall {A} (a : A) s Q ms, evt segs (Q a s) ms -> implM segs (interp (LRet a)) s Q ms.
Proof. intros. apply implM_ret. assumption. Qed.

Lemma implM_interp_unr : forall {A} s (Q : A -> PState -> machine_state -> Prop) ms, implM segs (interp LUnr) s Q ms.
Proof. intros. apply implM_unr. Qed.

Lemma implM_interp_malloc : forall {A} n (k : option bptr -> lprog A) s Q1 Q ms,
  implM segs (raw_malloc n) s Q1 ms ->
  (forall r s' ms', Q1 r s' ms' -> implM segs (interp (k r)) s' Q ms') ->
  implM segs (interp (LMalloc n k)) s Q ms.
Proof. intros A n k s Q1 Q ms H1 H2. cbn [interp]. eapply implM_bind; eauto. Qed.

Lemma implM_interp_free : forall {A} p (k : lprog A) s Q1 Q ms,
  implM segs (raw_free p) s Q1 ms ->
  (forall u s' ms', Q1 u s' ms' -> implM segs (interp k) s' Q ms') ->
  implM segs (interp (LFree p k)) s Q ms.
Proof. intros A p k s Q1 Q ms H1 H2. cbn [interp]. eapply implM_bind; eauto. Qed.

Lemma implM_interp_realloc : forall {A} p n (k : option bptr -> lprog A) s Q1 Q ms,
  implM segs (raw_realloc p n) s Q1 ms ->
  (forall r s' ms', Q1 r s' ms' -> implM segs (interp (k r)) s' Q ms') ->
  implM segs (interp (LRealloc p n k)) s Q ms.
Proof. intros A p n k s Q1 Q ms H1 H2. cbn [interp]. eapply implM_bind; eauto. Qed.

(* [comment removed for export] *)
Lemma implM_lsys : forall o s Q ms,
  evt segs (fun ms1 => at_node segs (sys_node o) ms1 /\
                       forall rsp r, sys_dec o rsp = Some r -> evt segs (Q r s) (nret ms1 rsp)) ms ->
  implM segs (lsys o) s Q ms.
Proof. intros o s Q ms H. unfold lsys. apply implM_sys. exact H. Qed.

Lemma implM_interp_sys : forall {A} o (k : Z -> lprog A) s Q1 Q ms,
  implM segs (lsys o) s Q1 ms ->
  (forall r s' ms', Q1 r s' ms' -> implM segs (interp (k r)) s' Q ms') ->
  implM segs (interp (LSys o k)) s Q ms.
Proof. intros A o k s Q1 Q ms H1 H2. cbn [interp]. eapply implM_bind; eauto. Qed.

Lemma implM_interp_reallocS : forall {A} p n (k : option bptr -> lprog A) s Q1 Q ms,
  implM segs (raw_realloc_shrink p n) s Q1 ms ->
  (forall r s' ms', Q1 r s' ms' -> implM segs (interp (k r)) s' Q ms') ->
  implM segs (interp (LReallocS p n k)) s Q ms.
Proof. intros A p n k s Q1 Q ms H1 H2. cbn [interp]. eapply implM_bind; eauto. Qed.

(* [comment removed for export] *)
Lemma implM_interp_reallocI : forall {A} p n (k : option bptr -> lprog A) s Q1 Q ms,
  implM segs (raw_realloc_inplace p n) s Q1 ms ->
  (forall r s' ms', Q1 r s' ms' -> implM segs (interp (k r)) s' Q ms') ->
  implM segs (interp (LReallocI p n k)) s Q ms.
Proof. intros A p n k s Q1 Q ms H1 H2. cbn [interp]. eapply implM_bind; eauto. Qed.
Lemma implM_interp_aligned : forall {A} al n (k : option bptr -> lprog A) s Q1 Q ms,
  implM segs (raw_aligned_alloc al n) s Q1 ms ->
  (forall r s' ms', Q1 r s' ms' -> implM segs (interp (k r)) s' Q ms') ->
  implM segs (interp (LAligned al n k)) s Q ms.
Proof. intros A al n k s Q1 Q ms H1 H2. cbn [interp]. eapply implM_bind; eauto. Qed.

(* [comment removed for export] *)
Lemma impl_ebind_assoc : forall {A B C} (t : itree node (exc A)) (g : A -> itree node (exc B)) (h : B -> itree node (exc C)) Q ms,
  impl segs (at_node segs) (ebind (ebind t g) h) Q ms ->
  impl segs (at_node segs) (ebind t (fun a => ebind (g a) h)) Q ms.
Proof.
  intros A B C t. induction t as [r|n k IH]; intros g h Q ms H.
  - destruct r as [|a]; exact H.
  - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp. apply IH. exact (Hk rsp).
Qed.

Lemma impl_ebind_cont : forall {A B} (t : itree node (exc A)) (g g' : A -> itree node (exc B)) Q ms,
  (forall a ms', impl segs (at_node segs) (g a) Q ms' -> impl segs (at_node segs) (g' a) Q ms') ->
  impl segs (at_node segs) (ebind t g) Q ms -> impl segs (at_node segs) (ebind t g') Q ms.
Proof.
  intros A B t. induction t as [r|n k IH]; intros g g' Q ms Hg H.
  - destruct r as [|a]; [exact H| apply Hg; exact H].
  - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp. eapply IH; [exact Hg| exact (Hk rsp)].
Qed.

Lemma implM_interp_bind_gen : forall {A B} (m : lprog A) (f : A -> lprog B) s Q ms,
  implM segs (mbind (interp m) (fun a => interp (f a))) s Q ms ->
  implM segs (interp (lbind m f)) s Q ms.
Proof.
  intros A B m. induction m as [a| |n k IH|p k IH|p n k IH|o k IH|al n k IH|p n k IH|p n k IH]; intros f s Q ms H.
  - exact H.
  - exact H.
  - cbn [interp lbind]. unfold implM, mbind in *. apply impl_ebind_assoc in H.
    eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r f s1). exact H1.
  - cbn [interp lbind]. unfold implM, mbind in *. apply impl_ebind_assoc in H.
    eapply impl_ebind_cont; [|exact H]. intros [u s1] ms1 H1. cbn [fst snd] in *. apply (IH f s1). exact H1.
  - cbn [interp lbind]. unfold implM, mbind in *. apply impl_ebind_assoc in H.
    eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r f s1). exact H1.
  - cbn [interp lbind]. unfold implM, mbind in *. apply impl_ebind_assoc in H.
    eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r f s1). exact H1.
  - cbn [interp lbind]. unfold implM, mbind in *. apply impl_ebind_assoc in H.
    eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r f s1). exact H1.
  - cbn [interp lbind]. unfold implM, mbind in *. apply impl_ebind_assoc in H.
    eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r f s1). exact H1.
  - cbn [interp lbind]. unfold implM, mbind in *. apply impl_ebind_assoc in H.
    eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r f s1). exact H1.
Qed.

(* [comment removed for export] *)
Lemma implM_interp_bind : forall {A B} (m : lprog A) (f : A -> lprog B) s Q1 Q ms,
  implM segs (interp m) s Q1 ms ->
  (forall a s' ms', Q1 a s' ms' -> implM segs (interp (f a)) s' Q ms') ->
  implM segs (interp (lbind m f)) s Q ms.
Proof. intros A B m f s Q1 Q ms H1 H2. apply implM_interp_bind_gen. eapply implM_bind; eauto. Qed.

End Machine.
End WithCeiling.
