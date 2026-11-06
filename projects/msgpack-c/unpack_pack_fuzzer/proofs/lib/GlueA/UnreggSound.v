(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame ITree Nodes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA NodesA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_iface2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op Adeq.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA GlueA CtrPre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import UnreggC UnreggPre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggAsan.
Unset Nia Cache. Unset Nra Cache.
Import CtrFX ActrA UnreggC.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.
Module UA := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.UnreggAsan.

Definition UNREGG_SYM : Z := 0x4ae40.

Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis OPS_holds_shmap : forall m mo, op_holds OPS (u_shmap CFG_ASAN) [] m mo -> shmap_holds m.
Variable OTHER : Model -> Model -> Prop.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable NMAXt : nat.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).

Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Hypothesis ACCT_rng_aimg_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG 0x7fffa000 0xc4000.
Definition acct_leaf_silent (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock)
    (r : unit) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo', mrel A' moc' mo' -> MP mo' /\ op_minv OPS mo' /\ OTHER mo0 mo' /\ ACCT aw L RNG' st LBa mo'.
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent mo aw L st LBa).

Lemma unregg_apply_shape : forall st sts, unregg_apply CFG_ASAN st = Some sts ->
  exists r hargs wnl st1, acall_pre ASTACK None st = Some (r, hargs, wnl, st1) /\ unregg_pre_b CFG_ASAN st = true
    /\ hull_views_ok CFG_ASAN st = true
    /\ sts = [setpc (setr (snd (fresh (clobber st1))) X10 (VP (fst (fresh (clobber st1))) wzero)) r].
Proof.
  intros st sts H. unfold unregg_apply in H.
  destruct (acall_pre ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:P; [|discriminate H].
  destruct (unregg_pre_b CFG_ASAN st) eqn:B; [|discriminate H].
  destruct (hull_views_ok CFG_ASAN st) eqn:HV; [|discriminate H]. cbn [andb] in H.
  exists r, hargs, wnl, st1. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  destruct (fresh (clobber st1)) as [x st3] eqn:F. injection H as <-. reflexivity.
Qed.

Definition unregg_leaf : Prop :=
  forall st sts (K : TSet) E ms mo r hargs wnl st1 (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word),
  st_ok asegs OPS E st ms mo -> PB (eb E) ->
  (forall st', In st' sts -> forall E' ms' mo', env_ext (s_next st) E E' -> MP mo' -> st_ok asegs OPS E' st' ms' mo' ->
               realizes asegs (mkCfg ms' mo') K) ->
  acall_pre ASTACK None st = Some (r, hargs, wnl, st1) -> unregg_pre_b CFG_ASAN st = true -> hull_views_ok CFG_ASAN st = true ->
  sts = [setpc (setr (snd (fresh (clobber st1))) X10 (VP (fst (fresh (clobber st1))) wzero)) r] ->
  call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) -> UA.unregg_pre (ms_mem ms) ->
  let R := ms_regs ms in
  ATOP + 4096 <= CtrPre.sp_lo E st -> CtrPre.sp_lo E st <= bv_unsigned (AP.getr R 2) - 4096 -> bv_unsigned (AP.getr R 2) < 2 ^ 47 ->
  forall ms' mo',
  UA.unregg_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
     (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
     (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (CtrPre.sp_lo E st) (ms_mem ms) ms' ->
  MP mo' -> op_minv OPS mo' -> OTHER mo mo' -> ACCT aw L RNG sta LBa mo' ->
  realizes asegs (mkCfg ms' mo') K.

Theorem unregg_sound_of_leaf : unregg_leaf ->
  forall pc, to_Z pc = UNREGG_SYM -> contract_sound asegs OPS MP PB (unregg_c CFG_ASAN pc).
Proof.
  intros LEAF pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc unregg_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = UNREGG_SYM) by (rewrite Hspc; exact Hpc).
  destruct (unregg_apply_shape st sts Happ) as (r & hargs & wnl & st1 & PRE & PREB & HVO & ESTS).
  destruct (CtrPre.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT.
  destruct (unregg_pre_facts OPS OPS_holds_shmap E st ms mo HS PREB RT (AI_relro AI _ _ _ _ _ AH)) as (UPRE & A0E & A1E).
  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (A0 & moc & MR & MINV & HH & TW).
  pose proof (ACCT_rng_aimg _ _ _ _ _ _ AC) as RIMG. pose proof (ACCT_rng_aimg_sh _ _ _ _ _ _ AC) as RISH.
  pose proof atop_range as ATR.
  set (R := ms_regs ms) in *.
  assert (EV := UA.unregg_proof RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31)
                (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) (CtrPre.sp_lo E st) UPRE ST).
  specialize (EV ltac:(unfold UA.MDTOR_DEPTH; lia) ltac:(unfold OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.KHIGH; lia) MI RSTK RIMG).
  specialize (EV ltac:(unfold UA.MDTOR_W; repeat (apply Forall_cons; [cbn [fst snd]|]); [ eapply rng_sub'; [exact RIMG| lia] | eapply rng_sub'; [exact RISH| lia] | eapply rng_sub'; [exact RISH| lia] | apply Forall_nil])).
  specialize (EV A0E A1E).
  rewrite Ems, HPC. apply (GlueA.realizes_to_mkRA asegs).
  eapply (implS_twfS_realizes_silent asegs NMAXt (Ret (Exc.Ok tt)) RNG A0
            (fun (_ : unit) (RNGq : footprint) ms' => RNGq = RNG /\ UA.unregg_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (CtrPre.sp_lo E st) (ms_mem ms) ms')
            _ _ moc mo K).
  - cbn [implF epostF]. eapply evtF_mono; [exact EV|]. intros ms' PO. split; [reflexivity| exact PO].
  - exact TW.
  - exact HH.
  - exact MINV.
  - exact MR.
  - intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV' MR'.
    destruct (HP' mo' MR') as (HMP' & HMI' & OTH & ACP). destruct HQ as [-> HQ].
    exact (LEAF st sts K E ms mo r hargs wnl st1 L RNG sta LBa aw HS HPB HK PRE PREB HVO ESTS CP FS CF AH UPRE BOT LO SPT ms' mo' HQ HMP' HMI' OTH ACP).
Qed.
End Sound.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.NodesA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB.
Import AMalloc_iface2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Ledger.TwinB Op.TwinB Adeq.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Import Actr.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import UnreggC.TwinB UnreggPre.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import CtrFX ActrA UnreggC.TwinB.UnreggC.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.
Module UA := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.UnreggAsan.TwinB.

Definition UNREGG_SYM : Z := 0x4b7d0.

Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis OPS_holds_shmap : forall m mo, op_holds OPS (u_shmap CFG_ASAN) [] m mo -> shmap_holds m.
Variable OTHER : Model -> Model -> Prop.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable NMAXt : nat.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).

Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Hypothesis ACCT_rng_aimg_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG 0x7fffa000 0xc5000.
Definition acct_leaf_silent (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock)
    (r : unit) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo', mrel A' moc' mo' -> MP mo' /\ op_minv OPS mo' /\ OTHER mo0 mo' /\ ACCT aw L RNG' st LBa mo'.
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent mo aw L st LBa).

Lemma unregg_apply_shape : forall st sts, unregg_apply CFG_ASAN st = Some sts ->
  exists r hargs wnl st1, acall_pre ASTACK None st = Some (r, hargs, wnl, st1) /\ unregg_pre_b CFG_ASAN st = true
    /\ hull_views_ok CFG_ASAN st = true
    /\ sts = [setpc (setr (snd (fresh (clobber st1))) X10 (VP (fst (fresh (clobber st1))) wzero)) r].
Proof.
  intros st sts H. unfold unregg_apply in H.
  destruct (acall_pre ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:P; [|discriminate H].
  destruct (unregg_pre_b CFG_ASAN st) eqn:B; [|discriminate H].
  destruct (hull_views_ok CFG_ASAN st) eqn:HV; [|discriminate H]. cbn [andb] in H.
  exists r, hargs, wnl, st1. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  destruct (fresh (clobber st1)) as [x st3] eqn:F. injection H as <-. reflexivity.
Qed.

Definition unregg_leaf : Prop :=
  forall st sts (K : TSet) E ms mo r hargs wnl st1 (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word),
  st_ok bsegs OPS E st ms mo -> PB (eb E) ->
  (forall st', In st' sts -> forall E' ms' mo', env_ext (s_next st) E E' -> MP mo' -> st_ok bsegs OPS E' st' ms' mo' ->
               realizes bsegs (mkCfg ms' mo') K) ->
  acall_pre ASTACK None st = Some (r, hargs, wnl, st1) -> unregg_pre_b CFG_ASAN st = true -> hull_views_ok CFG_ASAN st = true ->
  sts = [setpc (setr (snd (fresh (clobber st1))) X10 (VP (fst (fresh (clobber st1))) wzero)) r] ->
  call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) -> UA.unregg_pre (ms_mem ms) ->
  let R := ms_regs ms in
  ATOP + 4096 <= CtrPre.TwinB.sp_lo E st -> CtrPre.TwinB.sp_lo E st <= bv_unsigned (AP.getr R 2) - 4096 -> bv_unsigned (AP.getr R 2) < 2 ^ 47 ->
  forall ms' mo',
  UA.unregg_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
     (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
     (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (CtrPre.TwinB.sp_lo E st) (ms_mem ms) ms' ->
  MP mo' -> op_minv OPS mo' -> OTHER mo mo' -> ACCT aw L RNG sta LBa mo' ->
  realizes bsegs (mkCfg ms' mo') K.

Theorem unregg_sound_of_leaf : unregg_leaf ->
  forall pc, to_Z pc = UNREGG_SYM -> contract_sound bsegs OPS MP PB (unregg_c CFG_ASAN pc).
Proof.
  intros LEAF pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc unregg_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = UNREGG_SYM) by (rewrite Hspc; exact Hpc).
  destruct (unregg_apply_shape st sts Happ) as (r & hargs & wnl & st1 & PRE & PREB & HVO & ESTS).
  destruct (CtrPre.TwinB.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT.
  destruct (unregg_pre_facts OPS OPS_holds_shmap E st ms mo HS PREB RT (AI_relro AI _ _ _ _ _ AH)) as (UPRE & A0E & A1E).
  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (A0 & moc & MR & MINV & HH & TW).
  pose proof (ACCT_rng_aimg _ _ _ _ _ _ AC) as RIMG. pose proof (ACCT_rng_aimg_sh _ _ _ _ _ _ AC) as RISH.
  pose proof atop_range as ATR.
  set (R := ms_regs ms) in *.
  assert (EV := UA.unregg_proof RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31)
                (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) (CtrPre.TwinB.sp_lo E st) UPRE ST).
  specialize (EV ltac:(unfold UA.MDTOR_DEPTH; lia) ltac:(unfold OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.KHIGH; lia) MI RSTK RIMG).
  specialize (EV ltac:(unfold UA.MDTOR_W; repeat (apply Forall_cons; [cbn [fst snd]|]); [ eapply rng_sub'; [exact RIMG| lia] | eapply rng_sub'; [exact RISH| lia] | eapply rng_sub'; [exact RISH| lia] | apply Forall_nil])).
  specialize (EV A0E A1E).
  rewrite Ems, HPC. apply (GlueA.TwinB.realizes_to_mkRA bsegs).
  eapply (implS_twfS_realizes_silent bsegs NMAXt (Ret (Exc.Ok tt)) RNG A0
            (fun (_ : unit) (RNGq : footprint) ms' => RNGq = RNG /\ UA.unregg_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (CtrPre.TwinB.sp_lo E st) (ms_mem ms) ms')
            _ _ moc mo K).
  - cbn [implF epostF]. eapply evtF_mono; [exact EV|]. intros ms' PO. split; [reflexivity| exact PO].
  - exact TW.
  - exact HH.
  - exact MINV.
  - exact MR.
  - intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV' MR'.
    destruct (HP' mo' MR') as (HMP' & HMI' & OTH & ACP). destruct HQ as [-> HQ].
    exact (LEAF st sts K E ms mo r hargs wnl st1 L RNG sta LBa aw HS HPB HK PRE PREB HVO ESTS CP FS CF AH UPRE BOT LO SPT ms' mo' HQ HMP' HMI' OTH ACP).
Qed.
End Sound.
End TwinB.
