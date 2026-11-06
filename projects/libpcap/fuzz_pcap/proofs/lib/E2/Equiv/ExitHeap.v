(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog HeapFull. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require Import HaltsAdq ExitBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section WithCeil.
Context {CE : CEIL}.

Section Full.
Context {St : Type} {AS : AllocSt St}.
Variable peek : Z -> Monad.M St Z.
Hypothesis PEEK : forall caddr, mne (peek caddr).

Lemma mne_ev_step e : mne (St:=St) (ev_step e).
Proof. unfold ev_step. mne_go. Qed.

Lemma mne_ev_stepF e : mne (ev_stepF peek e).
Proof. unfold ev_stepF. destruct e; first [apply PEEK | apply mne_ev_step]. Qed.

Lemma mne_membedF {R} (t : stree ev Z R) : mne (membedF peek t).
Proof.
  induction t as [r|e k IH]; cbn [membedF]; [apply mne_ret|].
  apply mne_bind; [apply mne_ev_stepF| intros z; apply IH].
Qed.
Hint Resolve mne_membedF : mne.

Lemma mne_raw_mallocF n : mne (raw_mallocF peek n).
Proof. unfold raw_mallocF. mne_go. Qed.
Lemma mne_raw_freeF p : mne (raw_freeF peek p).
Proof. unfold raw_freeF. mne_go. Qed.
Lemma mne_raw_reallocF p n : mne (raw_reallocF peek p n).
Proof. unfold raw_reallocF. mne_go. Qed.
Lemma mne_raw_callocF m n : mne (raw_callocF peek m n).
Proof. unfold raw_callocF. mne_go. Qed.
End Full.

Lemma mne_peekG {St : Type} caddr : mne (St:=St) (peekG caddr).
Proof. unfold peekG. mne_go. Qed.

#[local] Hint Resolve mne_peekG : mne.
#[local] Hint Extern 1 (mne (raw_mallocF _ _)) => apply mne_raw_mallocF; intros; apply mne_peekG : mne.
#[local] Hint Extern 1 (mne (raw_freeF _ _)) => apply mne_raw_freeF; intros; apply mne_peekG : mne.
#[local] Hint Extern 1 (mne (raw_reallocF _ _ _)) => apply mne_raw_reallocF; intros; apply mne_peekG : mne.
#[local] Hint Extern 1 (mne (raw_callocF _ _ _)) => apply mne_raw_callocF; intros; apply mne_peekG : mne.

Lemma mne_tok_fresh p n : mne (tok_fresh p n).
Proof. unfold tok_fresh. mne_go. Qed.
Lemma mne_tok_drop k : mne (tok_drop k).
Proof. unfold tok_drop. mne_go. Qed.
Lemma mne_tok_lookup k : mne (tok_lookup k).
Proof. unfold tok_lookup. mne_go. Qed.
#[local] Hint Resolve mne_tok_fresh mne_tok_drop mne_tok_lookup : mne.

Lemma mne_hf_malloc n : mne (hf_malloc n).
Proof. unfold hf_malloc. mne_go. Qed.
Lemma mne_hf_calloc m n : mne (hf_calloc m n).
Proof. unfold hf_calloc. mne_go. Qed.
Lemma mne_hf_realloc k n : mne (hf_realloc k n).
Proof. unfold hf_realloc. mne_go. Qed.
Lemma mne_hf_free k : mne (hf_free k).
Proof. unfold hf_free. mne_go. Qed.

(* [comment removed for export] *)
Record heap_noexit {H hptr : Type} (HO : HeapOps H hptr) : Prop := mkHeapNoexit {
  hn_malloc : forall n, mne (ho_malloc HO n);
  hn_calloc : forall m n, mne (ho_calloc HO m n);
  hn_realloc : forall q n, mne (ho_realloc HO q n);
  hn_free : forall q, mne (ho_free HO q)
}.

Lemma full_ops_noexit : heap_noexit full_ops.
Proof.
  constructor; cbn [full_ops ho_malloc ho_calloc ho_realloc ho_free].
  - exact mne_hf_malloc.
  - exact mne_hf_calloc.
  - exact mne_hf_realloc.
  - exact mne_hf_free.
Qed.

End WithCeil.
