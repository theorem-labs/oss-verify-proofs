(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0k.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Definition access_outside_range (a : word) (n : nat) (lo sz : word) : Prop :=
(bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z /\
(bv_unsigned a + Z.of_nat n <= bv_unsigned lo
\/ bv_unsigned lo + bv_unsigned sz <= bv_unsigned a)%Z.
Definition accesses_outside_lazy
(accs : list (word * nat)) (lazy : list (word * word)) : Prop :=
forall a n lo sz, In (a, n) accs -> In (lo, sz) lazy ->
access_outside_range a n lo sz.
Lemma filter_all_false {A} : forall (f : A -> bool) (l : list A),
(forall x, In x l -> f x = false) -> List.filter f l = [].
Proof.
intros f l H; induction l as [|x l IH]; cbn; [reflexivity|].
rewrite (H x (or_introl eq_refl)).
apply IH. intros y Hy. apply H. right. exact Hy.
Qed.
Lemma with_vm_backing_id : forall m,
with_vm_backing (m_vm_lazy m) (m_vm_materialized m) m = m.
Proof.
intros [fd [maps lazy materialized] io fs proc lim tm]. reflexivity.
Qed.

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





