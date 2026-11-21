(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.AS Require Import DivergeSim.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.







Lemma page_insert_in : forall p q pages,
  In p (page_insert q pages) -> p = q \/ In p pages.
Proof.
  intros p q pages H. unfold page_insert in H.
  destruct (page_mem q pages); [right; exact H|].
  destruct H as [Hqp | H]; [left; symmetry; exact Hqp | right; exact H].
Qed.

Lemma access_pages_acc_in : forall n base pages p,
  In p (access_pages_acc base n pages) ->
  In p pages
  \/ exists k, (k < n)%nat /\ p = page_base_of (base + Z.of_nat k)%Z.
Proof.
  induction n as [|n IH]; cbn [access_pages_acc]; intros base pages p H.
  - left; exact H.
  - destruct (IH (base + 1)%Z _ p H) as [Hin | (k & Hk & ->)].
    + destruct (page_insert_in _ _ _ Hin) as [-> | Hin'].
      * right. exists 0%nat. split; [lia|]. f_equal. lia.
      * left; exact Hin'.
    + right. exists (S k). split; [lia|]. f_equal. lia.
Qed.

Lemma accesses_pages_in : forall accs pages p,
  In p (accesses_pages accs pages) ->
  In p pages
  \/ exists a n k, In (a, n) accs /\ (k < n)%nat /\
                   p = page_base_of (bv_unsigned a + Z.of_nat k)%Z.
Proof.
  induction accs as [|[a n] accs IH]; cbn [accesses_pages];
    intros pages p H.
  - left; exact H.
  - destruct (IH _ p H) as [Hin | (a' & n' & k & Hin & Hk & Hp)].
    + destruct (access_pages_acc_in n (bv_unsigned a) pages p Hin)
        as [Hp | (k & Hk & Hp)].
      * left; exact Hp.
      * right. exists a, n, k.
        split; [left; reflexivity | split; assumption].
    + right. exists a', n', k.
      split; [right; exact Hin | split; assumption].
Qed.







