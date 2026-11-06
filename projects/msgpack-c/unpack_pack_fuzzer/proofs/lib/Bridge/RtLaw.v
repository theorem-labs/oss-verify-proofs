(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import Mem Cells Step Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface AMalloc_iface2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AHolesD.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Section RtLaw.
Context {rc : runConstT}.

Lemma artcells_agree : forall m m' : amem, artcells m -> (forall x, 0 <= x < AIMG_HI -> m' (wa x) = m (wa x)) -> artcells m'.
Proof.
  unfold artcells. intros m m' H E.
  repeat match type of H with
         | _ /\ _ => let A := fresh "A" in destruct H as [A H]; split;
                     [eapply AHolesD.rw_cells_agreeD; [exact A| intros x Hx; apply E; cbn [cells_size csize Nat.add] in Hx; unfold AIMG_HI; lia]|]
         end.
  eapply AHolesD.rw_cells_agreeD; [exact H| intros x Hx; apply E; cbn [cells_size csize Nat.add] in Hx; unfold AIMG_HI; lia].
Qed.

Variable AI : AMallocIface2.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Hypothesis AI_fake : AI_fake_law AI.

Lemma aw_holds_rt : forall W aw LB m mo, aw_holds_w AI ACCT UNIV W aw LB m mo ->
  (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) /\ artcells m.
Proof.
  intros W aw LB m mo HW. pose proof HW as (AH & HT & _ & _ & _ & _ & EQ & _).
  assert (IMG : forall x, 0 <= x < AIMG_HI -> m (wa x) = w_ms W (wa x)).
  { intros x Hx. symmetry. apply EQ; [unfold W64.two64, AIMG_HI in *; lia|]. intros X. apply in_ivs_In in X as (v & Hv & Hin).
    apply in_map_iff in Hv as (b & <- & Hb). destruct (LB_twin_facts AI ACCT UNIV W aw LB m mo b HW Hb) as (T1 & _).
    unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin. unfold AIMG_HI in Hx. lia. }
  split.
  - intros i Hi. rewrite IMG by (unfold ARELRO_LO, ARELRO_HI, AIMG_HI in *; lia). exact (AI_relro AI _ _ _ _ _ AH i Hi).
  - exact (artcells_agree (w_ms W) m (AI_rtcells AI _ _ _ _ _ AH) IMG).
Qed.

Theorem heap_holds_rt : forall args m mo, heap_holdsX AI ACCT UNIV Cw args m mo ->
  (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) /\ artcells m.
Proof. intros args m mo (md & aw & ws & ca & LB & W & _ & HW & _). exact (aw_holds_rt W aw LB m mo HW). Qed.
End RtLaw.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB AMalloc_iface2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import Ledger.TwinB Op.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Section RtLaw.
Context {rc : runConstT}.

Lemma artcells_agree : forall m m' : amem, artcells m -> (forall x, 0 <= x < AIMG_HI -> m' (wa x) = m (wa x)) -> artcells m'.
Proof.
  unfold artcells. intros m m' H E.
  repeat match type of H with
         | _ /\ _ => let A := fresh "A" in destruct H as [A H]; split;
                     [eapply AHolesD.TwinB.rw_cells_agreeD; [exact A| intros x Hx; apply E; cbn [cells_size csize Nat.add] in Hx; unfold AIMG_HI; lia]|]
         end.
  eapply AHolesD.TwinB.rw_cells_agreeD; [exact H| intros x Hx; apply E; cbn [cells_size csize Nat.add] in Hx; unfold AIMG_HI; lia].
Qed.

Variable AI : AMallocIface2.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Hypothesis AI_fake : AI_fake_law AI.

Lemma aw_holds_rt : forall W aw LB m mo, aw_holds_w AI ACCT UNIV W aw LB m mo ->
  (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) /\ artcells m.
Proof.
  intros W aw LB m mo HW. pose proof HW as (AH & HT & _ & _ & _ & _ & EQ & _).
  assert (IMG : forall x, 0 <= x < AIMG_HI -> m (wa x) = w_ms W (wa x)).
  { intros x Hx. symmetry. apply EQ; [unfold W64.two64, AIMG_HI in *; lia|]. intros X. apply in_ivs_In in X as (v & Hv & Hin).
    apply in_map_iff in Hv as (b & <- & Hb). destruct (LB_twin_facts AI ACCT UNIV W aw LB m mo b HW Hb) as (T1 & _).
    unfold in_iv, twin_iv in Hin. cbn [fst snd] in Hin. unfold AIMG_HI in Hx. lia. }
  split.
  - intros i Hi. rewrite IMG by (unfold ARELRO_LO, ARELRO_HI, AIMG_HI in *; lia). exact (AI_relro AI _ _ _ _ _ AH i Hi).
  - exact (artcells_agree (w_ms W) m (AI_rtcells AI _ _ _ _ _ AH) IMG).
Qed.

Theorem heap_holds_rt : forall args m mo, heap_holdsX AI ACCT UNIV Cw args m mo ->
  (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) /\ artcells m.
Proof. intros args m mo (md & aw & ws & ca & LB & W & _ & HW & _). exact (aw_holds_rt W aw LB m mo HW). Qed.
End RtLaw.
End TwinB.
