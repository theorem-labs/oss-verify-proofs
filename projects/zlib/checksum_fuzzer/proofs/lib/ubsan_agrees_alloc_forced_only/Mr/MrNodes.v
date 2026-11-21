(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import CatSim ShapeAlg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.MSafe.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Mr Require Import MrBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

Definition mm_node (n : node) : Prop :=
  match n with NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ => True | _ => False end.

Fixpoint mmtree {R} (t : itree node R) : Prop :=
  match t with
  | Ret _ => True
  | Vis n k => mm_node n /\ forall rsp, mmtree (k rsp)
  end.

Lemma mmtree_tsilent : forall {R} (t : itree node R) mo, mmtree t -> B.tsilent node nstep nexit t mo.
Proof.
  intros R t. induction t as [r | n k IH]; intros mo H; cbn in *; [exact I|].
  destruct H as [Hn Hk]. split.
  - intros code mo' Hex. destruct n; cbn in Hn; try contradiction; exact Hex.
  - intros rsp mo' evs Hst. split.
    + exact (proj2 (nstep_mm_vm_only n mo rsp mo' evs Hn Hst)).
    + apply IH. apply Hk.
Qed.

Lemma mmtree_bind : forall {A C} (t : itree node A) (f : A -> itree node C),
  mmtree t -> (forall a, mmtree (f a)) -> mmtree (ITree.bind node t f).
Proof.
  intros A C t f. induction t as [r | n k IH]; intros Ht Hf; cbn in *; [apply Hf|].
  destruct Ht as [Hn Hk]. split; [exact Hn|]. intros rsp. apply IH; [apply Hk | exact Hf].
Qed.

Lemma mmtree_ebind : forall {A C} (t : itree node (exc A)) (f : A -> itree node (exc C)),
  mmtree t -> (forall a, mmtree (f a)) -> mmtree (ebind t f).
Proof.
  intros A C t f Ht Hf. unfold ebind. apply mmtree_bind; [exact Ht|]. intros [|a]; [exact I | apply Hf].
Qed.

Lemma mmtree_enode : forall {A} n (pl : resp -> option A), mm_node n -> mmtree (enode n pl).
Proof. intros A n pl Hn. cbn. split; [exact Hn|]. intros rsp. destruct (pl rsp); exact I. Qed.

Section WithRC.
Context {rc : runConstT}.

Lemma mmtree_msys : forall {A} n (dec : resp -> option A) (s : PState), mm_node n -> mmtree (Monad.msys n dec s).
Proof. intros. unfold Monad.msys. apply mmtree_enode. assumption. Qed.

Lemma mmtree_mbind : forall {A C} (m : Monad.M PState A) (f : A -> Monad.M PState C) s,
  mmtree (m s) -> (forall a s', mmtree (f a s')) -> mmtree (Monad.mbind m f s).
Proof. intros. unfold Monad.mbind. apply mmtree_ebind; [assumption|]. intros [a s']. cbn. auto. Qed.

Lemma mmtree_ev_step : forall atop e s, mmtree (ev_step atop e s).
Proof.
  intros atop e s. destruct e as [req | addr len prot flags | addr len | addr len prot | p c h | why]; cbn [ev_step].
  - destruct (req =? 0)%Z.
    + apply mmtree_mbind; [apply mmtree_msys; exact I|]. intros r s1.
      apply mmtree_mbind; [exact I|]. intros _ s2. exact I.
    + apply mmtree_mbind; [exact I|]. intros s0 s1.
      apply mmtree_mbind; [apply mmtree_msys; exact I|]. intros a s2.
      destruct a; [apply mmtree_mbind; [exact I|]; intros; exact I | exact I].
  - destruct (negb (Z.land flags MAP_FIXED_Z =? 0)%Z).
    + apply mmtree_mbind; [apply mmtree_msys; exact I|]. intros; exact I.
    + destruct (prot =? 0)%Z; (apply mmtree_mbind; [apply mmtree_msys; exact I|]; intros; exact I).
  - apply mmtree_mbind; [apply mmtree_msys; exact I|]. intros; exact I.
  - apply mmtree_mbind; [apply mmtree_msys; exact I|]. intros; exact I.
  - exact I.
  - exact I.
Qed.

Lemma mmtree_membed : forall {R} atop (t : stree ev Z R) s, mmtree (membed atop t s).
Proof.
  intros R atop t. induction t as [r | e k IH]; intros s; cbn [membed]; [exact I|].
  apply mmtree_mbind; [apply mmtree_ev_step|]. intros z s'. apply IH.
Qed.

Lemma mmtree_raw_malloc : forall n s, mmtree (raw_malloc n s).
Proof.
  intros n s. unfold raw_malloc. apply mmtree_mbind; [exact I|]. intros s0 s1.
  apply mmtree_mbind; [apply mmtree_membed|]. intros [st' p] s2.
  apply mmtree_mbind; [exact I|]. intros; exact I.
Qed.

Lemma mmtree_raw_free : forall p s, mmtree (raw_free p s).
Proof.
  intros p s. unfold raw_free. apply mmtree_mbind; [exact I|]. intros s0 s1.
  apply mmtree_mbind; [apply mmtree_membed|]. intros st' s2. exact I.
Qed.

Lemma twf_bridge : forall {R} (t : itree node R) mo P, MSafe.twf t mo P -> B.twf node nstep nsafe t mo P.
Proof.
  intros R t. induction t as [r | n k IH]; intros mo P H; cbn in *; [exact H|].
  destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. apply IH. eapply Hk; exact Hst.
Qed.

End WithRC.
