(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import ActrB.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan CtrLib.
Open Scope Z_scope.
Unset Lia Cache.

Lemma aheap_windows_hargs : forall st h wl, ActrA.aheap_windows st = Some (h, wl) -> find_op HEAP_ID (s_ops st) = Some h.
Proof.
  intros st h wl H. unfold ActrA.aheap_windows in H.
  destruct (find_op HEAP_ID (s_ops st)) as [hargs|]; [|discriminate H].
  destruct (CtrA.count_op HEAP_ID (s_ops st)) as [|[|?]]; try discriminate H.
  destruct (IMap.find STACK_ID (s_regs st)) as [r1|]; [|discriminate H].
  destruct (heap_nwin hargs) as [n|]; [|discriminate H].
  destruct hargs as [|? [|? [|? rest]]]; try discriminate H.
  match type of H with (if ?c then _ else _) = _ => destruct c; [|discriminate H] end.
  destruct (CtrA.nonstack_windows n rest) as [wl0|]; [|discriminate H].
  match type of H with (if ?c then _ else _) = _ => destruct c; [|discriminate H] end.
  injection H as <- _. reflexivity.
Qed.

Lemma acall_pre_bridge : forall room st r hargs st1,
  ActrB.acall_pre ActrA.ATPi room st = Some (r, hargs) -> ActrA.forget_stack_below_sp_g st = Some st1 ->
  exists wl, ActrA.acall_pre room None st = Some (r, hargs, wl, st1).
Proof.
  intros room st r hargs st1 H FS. unfold ActrB.acall_pre in H. unfold ActrA.acall_pre.
  destruct (call_pre st) as [r0|]; [|discriminate H].
  destruct (getr st X4) as [tp| | | | | | | | | |]; try discriminate H.
  destruct (find_op HEAP_ID (s_ops st)) as [h0|] eqn:FO; [|discriminate H].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate H] end.
  injection H as <- <-.
  repeat match type of CK with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in CK as [CK X] end.
  unfold ActrA.twins_intact in Q. destruct (ActrA.aheap_windows st) as [[h wl]|] eqn:AW; [|discriminate Q].
  pose proof (aheap_windows_hargs st h wl AW) as FH. rewrite FO in FH. injection FH as <-.
  exists wl. unfold ActrB.stack_room_g in Q2. rewrite CK, Q2, Q1, Q0. cbn [andb]. rewrite FS. reflexivity.
Qed.

Definition sm_size (cls : int) : int := PrimInt63.lsl 64%uint63 cls.
Definition sm_usz (cls : int) : int := PrimInt63.sub (sm_size cls) 8%uint63.
Definition sm_tlen (cls : int) : int := PrimInt63.lsr (sm_size cls) 3%uint63.
Definition sm_fr (cls : int) (sp : sv) : region :=
  region_store (Region 0%uint63 (VL (wlit (sm_usz cls))) true BGUnk IMap.empty) 24%uint63 8%uint63 sp.
Definition sm_tw (cls : int) : region := Region 0%uint63 (VL (wlit (sm_tlen cls))) true BGZero IMap.empty.

Definition sm_post (st st1 : sstate) (r : int) (cls : int) (h2 : list sv) : sstate :=
  let kf := s_next (clobber st1) in let shf := PrimInt63.add kf 1%uint63 in
  SS r (rf_set (s_rf (clobber st1)) X10 (VP kf wzero)) (s_ff (clobber st1)) (s_resv (clobber st1))
     (IMap.add shf (sm_tw cls) (IMap.add kf (sm_fr cls (getr st X2)) (s_regs (clobber st1))))
     (ActrB.link_fact shf kf :: FAlign kf 6%uint63 :: FRange kf ActrB.BLK_LO ActrB.BLK_HI :: s_facts (clobber st1))
     (set_op HEAP_ID h2 (s_ops (clobber st1))) (s_priv (clobber st1)) (PrimInt63.add shf 1%uint63).

Lemma sm_apply_shape : forall segs TP cls st sts, ActrB.stack_malloc_apply segs TP cls st = Some sts ->
  exists r hargs st1 h1 h2,
    ActrB.acall_pre TP 4096%uint63 st = Some (r, hargs) /\ PrimInt63.leb cls 2%uint63 = true /\ ActrB.frames_pre segs st hargs cls = true
    /\ ActrA.sp_altop_ok st hargs = true
    /\ ActrA.forget_stack_below_sp_g st = Some st1
    /\ heap_add_window hargs (VP (s_next (clobber st1)) wzero) (VL (wlit (sm_usz cls))) (VL ActrB.K_FRAME) = Some h1
    /\ heap_add_window h1 (VP (PrimInt63.add (s_next (clobber st1)) 1%uint63) wzero) (VL (wlit (sm_tlen cls))) (VL ActrB.K_FTWIN) = Some h2
    /\ sts = [sm_post st st1 r cls h2].
Proof.
  intros segs TP cls st sts H. unfold ActrB.stack_malloc_apply in H.
  destruct (ActrB.acall_pre TP 4096%uint63 st) as [[r hargs]|] eqn:PRE; [|discriminate H].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate H] end.
  apply andb_prop in CK as [CK SAO]. apply andb_prop in CK as [C2 FP].
  unfold ActrB.forget_stack_below_sp_g in H.
  destruct (ActrA.forget_stack_below_sp_g st) as [st1|] eqn:FS; [|discriminate H].
  unfold fresh in H. cbv zeta in H. cbn [fst snd s_next set_next] in H.
  fold (sm_size cls) in H. fold (sm_usz cls) in H. fold (sm_tlen cls) in H.
  destruct (heap_add_window hargs (VP (s_next (clobber st1)) wzero) (VL (wlit (sm_usz cls))) (VL ActrB.K_FRAME)) as [h1|] eqn:H1; [|discriminate H].
  destruct (heap_add_window h1 (VP (PrimInt63.add (s_next (clobber st1)) 1%uint63) wzero) (VL (wlit (sm_tlen cls))) (VL ActrB.K_FTWIN)) as [h2|] eqn:H2; [|discriminate H].
  injection H as <-.
  exists r, hargs, st1, h1, h2. repeat (split; [reflexivity || assumption|]).
  unfold sm_post. reflexivity.
Qed.

Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Actr.TwinB.
Import ActrB.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan CtrLib.
Open Scope Z_scope.
Unset Lia Cache.

Lemma aheap_windows_hargs : forall st h wl, ActrA.aheap_windows st = Some (h, wl) -> find_op HEAP_ID (s_ops st) = Some h.
Proof.
  intros st h wl H. unfold ActrA.aheap_windows in H.
  destruct (find_op HEAP_ID (s_ops st)) as [hargs|]; [|discriminate H].
  destruct (CtrA.count_op HEAP_ID (s_ops st)) as [|[|?]]; try discriminate H.
  destruct (IMap.find STACK_ID (s_regs st)) as [r1|]; [|discriminate H].
  destruct (heap_nwin hargs) as [n|]; [|discriminate H].
  destruct hargs as [|? [|? [|? rest]]]; try discriminate H.
  match type of H with (if ?c then _ else _) = _ => destruct c; [|discriminate H] end.
  destruct (CtrA.nonstack_windows n rest) as [wl0|]; [|discriminate H].
  match type of H with (if ?c then _ else _) = _ => destruct c; [|discriminate H] end.
  injection H as <- _. reflexivity.
Qed.

Lemma acall_pre_bridge : forall room st r hargs st1,
  ActrB.TwinB.ActrB.acall_pre ActrA.ATPi room st = Some (r, hargs) -> ActrA.forget_stack_below_sp_g st = Some st1 ->
  exists wl, ActrA.acall_pre room None st = Some (r, hargs, wl, st1).
Proof.
  intros room st r hargs st1 H FS. unfold ActrB.TwinB.ActrB.acall_pre in H. unfold ActrA.acall_pre.
  destruct (call_pre st) as [r0|]; [|discriminate H].
  destruct (getr st X4) as [tp| | | | | | | | | |]; try discriminate H.
  destruct (find_op HEAP_ID (s_ops st)) as [h0|] eqn:FO; [|discriminate H].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate H] end.
  injection H as <- <-.
  repeat match type of CK with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in CK as [CK X] end.
  unfold ActrA.twins_intact in Q. destruct (ActrA.aheap_windows st) as [[h wl]|] eqn:AW; [|discriminate Q].
  pose proof (aheap_windows_hargs st h wl AW) as FH. rewrite FO in FH. injection FH as <-.
  exists wl. unfold ActrB.TwinB.ActrB.stack_room_g in Q2. rewrite CK, Q2, Q1, Q0. cbn [andb]. rewrite FS. reflexivity.
Qed.

Definition sm_size (cls : int) : int := PrimInt63.lsl 64%uint63 cls.
Definition sm_usz (cls : int) : int := PrimInt63.sub (sm_size cls) 8%uint63.
Definition sm_tlen (cls : int) : int := PrimInt63.lsr (sm_size cls) 3%uint63.
Definition sm_fr (cls : int) (sp : sv) : region :=
  region_store (Region 0%uint63 (VL (wlit (sm_usz cls))) true BGUnk IMap.empty) 24%uint63 8%uint63 sp.
Definition sm_tw (cls : int) : region := Region 0%uint63 (VL (wlit (sm_tlen cls))) true BGZero IMap.empty.

Definition sm_post (st st1 : sstate) (r : int) (cls : int) (h2 : list sv) : sstate :=
  let kf := s_next (clobber st1) in let shf := PrimInt63.add kf 1%uint63 in
  SS r (rf_set (s_rf (clobber st1)) X10 (VP kf wzero)) (s_ff (clobber st1)) (s_resv (clobber st1))
     (IMap.add shf (sm_tw cls) (IMap.add kf (sm_fr cls (getr st X2)) (s_regs (clobber st1))))
     (ActrB.TwinB.ActrB.link_fact shf kf :: FAlign kf 6%uint63 :: FRange kf ActrB.TwinB.ActrB.BLK_LO ActrB.TwinB.ActrB.BLK_HI :: s_facts (clobber st1))
     (set_op HEAP_ID h2 (s_ops (clobber st1))) (s_priv (clobber st1)) (PrimInt63.add shf 1%uint63).

Lemma sm_apply_shape : forall segs TP cls st sts, ActrB.TwinB.ActrB.stack_malloc_apply segs TP cls st = Some sts ->
  exists r hargs st1 h1 h2,
    ActrB.TwinB.ActrB.acall_pre TP 4096%uint63 st = Some (r, hargs) /\ PrimInt63.leb cls 2%uint63 = true /\ ActrB.TwinB.ActrB.frames_pre segs st hargs cls = true
    /\ ActrA.sp_altop_ok st hargs = true
    /\ ActrA.forget_stack_below_sp_g st = Some st1
    /\ heap_add_window hargs (VP (s_next (clobber st1)) wzero) (VL (wlit (sm_usz cls))) (VL ActrB.TwinB.ActrB.K_FRAME) = Some h1
    /\ heap_add_window h1 (VP (PrimInt63.add (s_next (clobber st1)) 1%uint63) wzero) (VL (wlit (sm_tlen cls))) (VL ActrB.TwinB.ActrB.K_FTWIN) = Some h2
    /\ sts = [sm_post st st1 r cls h2].
Proof.
  intros segs TP cls st sts H. unfold ActrB.TwinB.ActrB.stack_malloc_apply in H.
  destruct (ActrB.TwinB.ActrB.acall_pre TP 4096%uint63 st) as [[r hargs]|] eqn:PRE; [|discriminate H].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate H] end.
  apply andb_prop in CK as [CK SAO]. apply andb_prop in CK as [C2 FP].
  unfold ActrB.TwinB.ActrB.forget_stack_below_sp_g in H.
  destruct (ActrA.forget_stack_below_sp_g st) as [st1|] eqn:FS; [|discriminate H].
  unfold fresh in H. cbv zeta in H. cbn [fst snd s_next set_next] in H.
  fold (sm_size cls) in H. fold (sm_usz cls) in H. fold (sm_tlen cls) in H.
  destruct (heap_add_window hargs (VP (s_next (clobber st1)) wzero) (VL (wlit (sm_usz cls))) (VL ActrB.TwinB.ActrB.K_FRAME)) as [h1|] eqn:H1; [|discriminate H].
  destruct (heap_add_window h1 (VP (PrimInt63.add (s_next (clobber st1)) 1%uint63) wzero) (VL (wlit (sm_tlen cls))) (VL ActrB.TwinB.ActrB.K_FTWIN)) as [h2|] eqn:H2; [|discriminate H].
  injection H as <-.
  exists r, hargs, st1, h1, h2. repeat (split; [reflexivity || assumption|]).
  unfold sm_post. reflexivity.
Qed.
End TwinB.
