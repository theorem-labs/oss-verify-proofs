(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin SRealizes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require ShapeAlg DivergeSim SpinAlg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Section J2.
Variable segs : list Segment.

Lemma to_jself_to_spin_AS : forall ms mo,
  Spin.to_jself segs ms mo -> AS.DivergeSim.to_spin segs ms mo.
Proof.
  intros ms mo H. induction H as [ms mo Hsvc Hf | ms mo ms' mo' Hsvc Hacc H IH].
  - apply AS.DivergeSim.ts_spin; [exact Hsvc|].
    apply (self_jump_account_fix segs ms mo JWORD (Z_to_bv 5 0) (Z_to_bv 21 0) 4 Hsvc Hf);
      [reflexivity| vm_compute; reflexivity| reflexivity| reflexivity].
  - eapply AS.DivergeSim.ts_step; eassumption.
Qed.

(* [comment removed for export] *)
Lemma node_ok_AS : forall c I evs nx,
  ShapeAlg.node_ok segs c I evs nx -> AS.ShapeAlg.node_ok segs c I evs nx.
Proof. intros c I evs nx H. exact H. Qed.

Theorem srealizes_LRT_AS : forall c (T : TSet),
  SRealizes.srealizes segs c T -> AS.SpinAlg.srealizes segs c T.
Proof.
  intros c T H.
  induction H as [c I evs nx T i0 Hnode Hk IH | c Hh | c Hj | c T T' H IH Heq].
  - exact (AS.SpinAlg.srz_node segs c I evs nx T i0 (node_ok_AS c I evs nx Hnode) IH).
  - exact (AS.SpinAlg.srz_halt segs c Hh).
  - destruct Hj as [Hj Hh]. apply (AS.SpinAlg.srz_spin segs c); [apply to_jself_to_spin_AS; exact Hj| exact Hh].
  - exact (AS.SpinAlg.srz_conseq segs c T T' IH Heq).
Qed.

End J2.
