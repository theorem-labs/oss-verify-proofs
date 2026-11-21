(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import ITree Nodes CTree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import Prelim Monad CMonad.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import ExecF ITreeA CTreeA.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg AProto CProto.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section PostF.
Variable segs : list Segment.
Variable at_node : node -> footprint -> machine_state -> Prop.
Variable fstep : node -> resp -> footprint -> footprint -> Prop.

Lemma implFC_post_evtF : forall {R} (c : ctree node R) RNG (Q Q' : R -> footprint -> machine_state -> Prop) ms,
  implFC segs at_node fstep RNG c Q' ms ->
  (forall r RNG' ms', Q' r RNG' ms' -> evtF segs RNG' (Q r RNG') ms') ->
  implFC segs at_node fstep RNG c Q ms.
Proof.
  intros R c. induction c as [r|n k IH|a IHa b IHb]; intros RNG Q Q' ms H K; cbn in *.
  - eapply evtF_cut; [exact H|]. cbv beta. intros ms' H'. apply K. exact H'.
  - eapply evtF_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp RNG' HF. eapply IH; [apply Hk; exact HF| exact K].
  - eapply evtF_mono; [exact H|]. intros ms1 [Hl|Hr]; [left; eapply IHa; eauto| right; eapply IHb; eauto].
Qed.
End PostF.

Section CANSEC1. Context {rc : runConstT}.
Lemma implMAC_post_evtF : forall {St A} RNG (mc : MC St A) (s : St) (Q Q' : A -> St -> footprint -> machine_state -> Prop) ms,
  implMAC RNG mc s Q' ms ->
  (forall a s' RNG' ms', Q' a s' RNG' ms' -> evtF bsegs RNG' (Q a s' RNG') ms') ->
  implMAC RNG mc s Q ms.
Proof.
  intros St A RNG mc s Q Q' ms H K. unfold implMAC in *. eapply implFC_post_evtF; [exact H|].
  intros [|[a s']] RNG' ms' HQ; cbn in HQ |- *; [apply evtF_done; exact I| apply K; exact HQ].
Qed.
End CANSEC1.
