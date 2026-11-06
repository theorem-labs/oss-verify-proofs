(* CARRIED from commit d692856bfecbb98b2d89a0bba73b457c2098f96d,
   proofs/cgif/cgif_file_fuzzer/lib/YK04M.v, sha256 bd90e54b1f871b39608ae00931dbdfe655d3765cc836128ba2c3f806855f39b3 (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The only change made here is the module
   prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec). *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file (SRr_stepM engine row srrm-matadds, additive; no existing text changed):
   materialize only adds accessed pages. LPS's materialize_model_accesses (State.v) sets the materialized-page ledger to
   newly_materialized_pages ++ the old ledger (or leaves it), and newly_materialized_pages is a filter of the accesses'
   pages, so every page of the new ledger is an old page or a page of one of the step's accesses. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04.
Import ListNotations.

(* The ledger after materialize_model_accesses: the old pages, or a page of the accesses (LPS's accesses_pages). *)
Lemma materialize_mat_adds : forall m accs m',
  materialize_model_accesses m accs = Some m' ->
  forall p, In p (m_vm_materialized m') ->
  In p (m_vm_materialized m) \/ In p (accesses_pages accs []).
Proof.
intros m accs m' Hm p Hp.
assert (HM : m_vm_materialized m' = m_vm_materialized m \/
  m_vm_materialized m' = newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) accs ++ m_vm_materialized m).
{ unfold materialize_model_accesses, materialize_accesses in Hm. cbv zeta in Hm.
  destruct (newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) accs) as [|q new].
  - injection Hm as <-. left. reflexivity.
  - destruct (_ <=? _)%Z; [|discriminate]. injection Hm as <-. right. reflexivity. }
destruct HM as [E|E]; rewrite E in Hp; [left; exact Hp|].
apply in_app_or in Hp as [Hp|Hp]; [right|left; exact Hp].
unfold newly_materialized_pages in Hp. exact (proj1 (proj1 (filter_In _ _ _) Hp)).
Qed.

(* The same with the accessed page made explicit (YK04.accesses_pages_in at an empty start list): a new page is the page
   base of byte k of an access (a, n) of the step, k < n. *)
Lemma materialize_mat_adds_acc : forall m accs m',
  materialize_model_accesses m accs = Some m' ->
  forall p, In p (m_vm_materialized m') ->
  In p (m_vm_materialized m) \/
  exists a n k, In (a, n) accs /\ (k < n)%nat /\ p = page_base_of (bv_unsigned a + Z.of_nat k)%Z.
Proof.
intros m accs m' Hm p Hp. destruct (materialize_mat_adds m accs m' Hm p Hp) as [H|H]; [left; exact H|right].
destruct (accesses_pages_in accs [] p H) as [H0|H0]; [destruct H0|exact H0].
Qed.

(* materialize_model_accesses leaves the lazy ledger as it is. *)
Lemma materialize_lazy_same : forall m accs m',
  materialize_model_accesses m accs = Some m' -> m_vm_lazy m' = m_vm_lazy m.
Proof.
intros m accs m' Hm. unfold materialize_model_accesses, materialize_accesses in Hm.
destruct (newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) accs) as [|q new].
- injection Hm as <-. reflexivity.
- destruct (_ <=? _)%Z; [|discriminate]. injection Hm as <-. reflexivity.
Qed.

(* materialize_model_accesses changes only the materialized ledger (YK04.same_but_materialized: every Some result is
   with_vm_backing (m_vm_lazy m) _ m). *)
Lemma materialize_same_but : forall m accs m',
  materialize_model_accesses m accs = Some m' -> same_but_materialized m m'.
Proof.
intros m accs m' Hm. unfold materialize_model_accesses in Hm.
destruct (materialize_accesses _ _ _ _ _) as [pages|]; [|discriminate]. injection Hm as <-.
unfold same_but_materialized. reflexivity.
Qed.

(* The statement srrm-chain consumes (a Theorem Labs lane, 05:25Z). *)
Lemma materialize_adds_only : forall m accs m',
  materialize_model_accesses m accs = Some m' ->
  m_vm_lazy m' = m_vm_lazy m /\ same_but_materialized m m' /\
  (forall p, In p (m_vm_materialized m') -> In p (m_vm_materialized m) \/ In p (accesses_pages accs [])).
Proof.
intros m accs m' Hm.
exact (conj (materialize_lazy_same m accs m' Hm) (conj (materialize_same_but m accs m' Hm) (materialize_mat_adds m accs m' Hm))).
Qed.
