(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import ITree Nodes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma implS_sbind : forall {A B} (t : AM A) (f : A -> AM B) RNG
    (Q1 : A -> footprint -> machine_state -> Prop) (Q : B -> footprint -> machine_state -> Prop) ms,
  implS asegs RNG (aembed ATOP t) (epostF Q1) ms ->
  (forall a RNG' ms', Q1 a RNG' ms' -> implS asegs RNG' (aembed ATOP (f a)) (epostF Q) ms') ->
  implS asegs RNG (aembed ATOP (sbind t f)) (epostF Q) ms.
Proof.
  intros A B t f. induction t as [a|e k IH]; intros RNG Q1 Q ms H Hf.
  - rewrite aembed_sbind_ret. rewrite aembed_ret in H.
    eapply implF_evtF; [exact H|]. intros ms' HQ. exact (Hf _ _ _ HQ).
  - rewrite aembed_sbind_vis. rewrite aembed_vis in H.
    destruct e; cbn [aev_tree] in H |- *;
      try (unfold enode, ebind in H |- *; cbn [bind] in H |- *; cbn [implF] in H |- *;
           eapply evtF_mono; [exact H|]; intros ms1 [Hat Hk]; split; [exact Hat|];
           intros rsp RNG' HF; specialize (Hk rsp RNG' HF);
           match goal with |- context [match ?d with Some _ => _ | None => _ end] => destruct d end;
           cbn [bind] in Hk |- *; [eapply IH; [exact Hk| exact Hf] | exact Hk]).

    unfold ebind. cbn [bind]. apply implF_ret_unr.
Qed.
End CANSEC1.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma implS_sbind : forall {A B} (t : AM A) (f : A -> AM B) RNG
    (Q1 : A -> footprint -> machine_state -> Prop) (Q : B -> footprint -> machine_state -> Prop) ms,
  implS bsegs RNG (aembed ATOP t) (epostF Q1) ms ->
  (forall a RNG' ms', Q1 a RNG' ms' -> implS bsegs RNG' (aembed ATOP (f a)) (epostF Q) ms') ->
  implS bsegs RNG (aembed ATOP (sbind t f)) (epostF Q) ms.
Proof.
  intros A B t f. induction t as [a|e k IH]; intros RNG Q1 Q ms H Hf.
  - rewrite aembed_sbind_ret. rewrite aembed_ret in H.
    eapply implF_evtF; [exact H|]. intros ms' HQ. exact (Hf _ _ _ HQ).
  - rewrite aembed_sbind_vis. rewrite aembed_vis in H.
    destruct e; cbn [aev_tree] in H |- *;
      try (unfold enode, ebind in H |- *; cbn [bind] in H |- *; cbn [implF] in H |- *;
           eapply evtF_mono; [exact H|]; intros ms1 [Hat Hk]; split; [exact Hat|];
           intros rsp RNG' HF; specialize (Hk rsp RNG' HF);
           match goal with |- context [match ?d with Some _ => _ | None => _ end] => destruct d end;
           cbn [bind] in Hk |- *; [eapply IH; [exact Hk| exact Hf] | exact Hk]).

    unfold ebind. cbn [bind]. apply implF_ret_unr.
Qed.
End CANSEC1.
End TwinB.
