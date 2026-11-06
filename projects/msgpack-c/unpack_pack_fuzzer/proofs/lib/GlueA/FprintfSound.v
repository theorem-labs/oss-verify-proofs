(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame ITree Nodes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem ALib.Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA NodesA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_iface2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require I_printf_icpt I_printf_formats.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import RtCells.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib Defs DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op Adeq.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA GlueA CtrPre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import UnreggSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import HalfC VprintfC VprintfSound FprintfC.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggPre.
Unset Nia Cache. Unset Nra Cache.
Import CtrFX ActrA VprintfC FprintfC.
Module IPI := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_printf_icpt.
Module IPF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_printf_formats.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Definition FPRINTF_SYM : Z := 0x50cf0.

Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis OPS_holds_zro : forall m mo, op_holds OPS ZRO_ID [] m mo -> zro_holds m.
Variable OTHER : Model -> Model -> Prop.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable NMAXt : nat.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Hypothesis ACCT_rng_aimg_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG 0x7fffa000 0xc4000.
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent ACCT OPS OTHER MP mo aw L st LBa).

Lemma afprintf_apply_shape : forall FMT st sts, afprintf_pre_apply asegs FMT st = Some sts ->
  exists r hargs wnl st1 st3,
    acall_pre ASTACK None st = Some (r, hargs, wnl, st1) /\ getr st X11 = VL FMT /\ find_op ZRO_ID (s_ops st) = Some []
    /\ HalfC.push_cells asegs (setpc (setr (clobber st1) X10 (getr st X10)) r) (fp_sp st) (fp_cells st r) = Some st3
    /\ sts = [setpc (HalfC.set_regs st3 (fp_regs st)) REAL_VF].
Proof.
  intros FMT st sts H. unfold afprintf_pre_apply in H.
  destruct (acall_pre ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:P; [|discriminate H].
  match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:CND; [|discriminate H] end.
  apply andb_prop in CND as [IL FZ]. unfold CtrS.is_lit in IL. apply ValP.sv_eqb_eq in IL.
  destruct (find_op ZRO_ID (s_ops st)) as [[|? ?]|] eqn:FO; try discriminate FZ.
  cbv zeta in H.
  destruct (HalfC.push_cells asegs (setpc (setr (clobber st1) X10 (getr st X10)) r) (fp_sp st) (fp_cells st r)) as [st3|] eqn:PC; [|discriminate H].
  injection H as <-. exists r, hargs, wnl, st1, st3. repeat split; try assumption; reflexivity.
Qed.

Definition afprintf_leaf : Prop :=
  forall st (K : TSet) E ms mo r hargs wnl st1 st3 (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word),
  st_ok asegs OPS E st ms mo -> PB (eb E) ->
  (forall st', In st' [setpc (HalfC.set_regs st3 (fp_regs st)) REAL_VF] -> forall E' ms' mo', env_ext (s_next st) E E' -> MP mo' -> st_ok asegs OPS E' st' ms' mo' ->
               realizes asegs (mkCfg ms' mo') K) ->
  acall_pre ASTACK None st = Some (r, hargs, wnl, st1) ->
  HalfC.push_cells asegs (setpc (setr (clobber st1) X10 (getr st X10)) r) (fp_sp st) (fp_cells st r) = Some st3 ->
  call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) -> ALib.Mem.mem_inv asegs (ms_mem ms) ->
  let R := ms_regs ms in
  ATOP + 4096 <= CtrPre.sp_lo E st -> CtrPre.sp_lo E st <= bv_unsigned (AP.getr R 2) - 4096 -> bv_unsigned (AP.getr R 2) < 2 ^ 47 ->
  forall ms' mo',
  IPI.fprintf_i_mid (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9) (AP.getr R 10) (AP.getr R 11)
     (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16) (AP.getr R 17)
     (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
     (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (CtrPre.sp_lo E st) (ms_mem ms) ms' ->
  MP mo' -> op_minv OPS mo' -> OTHER mo mo' -> ACCT aw L RNG sta LBa mo' ->
  realizes asegs (mkCfg ms' mo') K.

Theorem afprintf_sound_of_leaf : afprintf_leaf ->
  forall pc, to_Z pc = FPRINTF_SYM -> contract_sound asegs OPS MP PB (afprintf_pre_c asegs FMT_TOOBIG pc).
Proof.
  intros LEAF pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc afprintf_pre_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = FPRINTF_SYM) by (rewrite Hspc; exact Hpc).
  destruct (afprintf_apply_shape _ st sts Happ) as (r & hargs & wnl & st1 & st3 & PRE & G11 & FZ & PUSH & ->).
  destruct (CtrPre.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT.
  set (R := ms_regs ms) in *.
  pose proof atop_range as ATR.

  pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (UnreggPre.find_op_In _ _ _ FZ)) as HO. cbn [op_id op_args map] in HO.
  pose proof (OPS_holds_zro _ _ HO) as ZRO.
  assert (EA0 : AP.getr R (reg_of_r5 X11) = Z_to_bv 64 IPF.FMT_TOOBIG).
  { unfold R. rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X11), G11. reflexivity. }
  assert (EA0' : AP.getr R 11 = Z_to_bv 64 IPF.FMT_TOOBIG) by exact EA0.
  idtac "FS-1".
  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  pose proof (ACCT_rng_aimg _ _ _ _ _ _ AC) as RIMG. pose proof (ACCT_rng_aimg_sh _ _ _ _ _ _ AC) as RSH.
  assert (EV : evtF asegs RNG
            (IPI.fprintf_i_mid (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9) (AP.getr R 10) (AP.getr R 11)
     (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16) (AP.getr R 17)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (CtrPre.sp_lo E st) (ms_mem ms))
            (MS (mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31))
                (ms_fregs ms) (Z_to_bv 64 FPRINTF_SYM) (ms_fcsr ms) None (ms_mem ms) (seg_rom asegs))).
  { unfold artcells in RT. decompose [and] RT. clear RT.
    eapply (IPI.fprintf_i_pre_toobig RNG).
    all: try lazymatch goal with
         | |- ALib.Mem.mem_inv _ _ => exact MI
         | |- stk _ _ _ _ => exact ST
         | |- ALib.Step.rw_cells _ _ _ _ => assumption
         | |- Shadow.shadow_bytes _ _ _ _ => apply (zro_shadow_bytes _ _ _ ZRO); unfold IPF.FMT_TOOBIG; lia
         | |- rng_aimg _ => exact RIMG
         | |- AP.getr _ _ = _ => exact EA0'
         | |- rng _ (shad _) _ => apply (rng_sub _ _ _ _ _ RSH); unfold IPF.FMT_TOOBIG, shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia
         | |- rng _ _ _ => exact RSTK
         end.
    all: try (unfold Shadow.KHIGH in *; lia).
    all: match goal with |- ?G => idtac "REMW" G end. }
  rewrite Ems, HPC. apply (GlueA.realizes_to_mkRA asegs).
  eapply (implS_twfS_realizes_silent asegs NMAXt (Ret (Exc.Ok tt)) RNG AL0
            (fun (_ : unit) (RNGq : footprint) ms' => RNGq = RNG /\ IPI.fprintf_i_mid (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9) (AP.getr R 10) (AP.getr R 11)
     (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16) (AP.getr R 17)
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
    exact (LEAF st K E ms mo r hargs wnl st1 st3 L RNG sta LBa aw HS HPB HK PRE PUSH CP FS CF AH MI BOT LO SPT ms' mo' HQ HMP' HMI' OTH ACP).
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
Import RtCells.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Defs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Ledger.TwinB Op.TwinB Adeq.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Import Actr.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import UnreggSound.TwinB.
Import HalfC.TwinB VprintfC.TwinB VprintfSound.TwinB FprintfC.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import CtrFX ActrA VprintfC.TwinB.VprintfC FprintfC.TwinB.FprintfC.
Module IPI := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_printf_icpt.TwinB.
Module IPF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_printf_formats.TwinB.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Definition FPRINTF_SYM : Z := 0x51680.

Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis OPS_holds_zro : forall m mo, op_holds OPS ZRO_ID [] m mo -> zro_holds m.
Variable OTHER : Model -> Model -> Prop.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable NMAXt : nat.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Hypothesis ACCT_rng_aimg_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG 0x7fffa000 0xc5000.
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent ACCT OPS OTHER MP mo aw L st LBa).

Lemma afprintf_apply_shape : forall FMT st sts, afprintf_pre_apply bsegs FMT st = Some sts ->
  exists r hargs wnl st1 st3,
    acall_pre ASTACK None st = Some (r, hargs, wnl, st1) /\ getr st X11 = VL FMT /\ find_op ZRO_ID (s_ops st) = Some []
    /\ HalfC.TwinB.HalfC.push_cells bsegs (setpc (setr (clobber st1) X10 (getr st X10)) r) (fp_sp st) (fp_cells st r) = Some st3
    /\ sts = [setpc (HalfC.TwinB.HalfC.set_regs st3 (fp_regs st)) REAL_VF].
Proof.
  intros FMT st sts H. unfold afprintf_pre_apply in H.
  destruct (acall_pre ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:P; [|discriminate H].
  match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:CND; [|discriminate H] end.
  apply andb_prop in CND as [IL FZ]. unfold CtrS.is_lit in IL. apply ValP.sv_eqb_eq in IL.
  destruct (find_op ZRO_ID (s_ops st)) as [[|? ?]|] eqn:FO; try discriminate FZ.
  cbv zeta in H.
  destruct (HalfC.TwinB.HalfC.push_cells bsegs (setpc (setr (clobber st1) X10 (getr st X10)) r) (fp_sp st) (fp_cells st r)) as [st3|] eqn:PC; [|discriminate H].
  injection H as <-. exists r, hargs, wnl, st1, st3. repeat split; try assumption; reflexivity.
Qed.

Definition afprintf_leaf : Prop :=
  forall st (K : TSet) E ms mo r hargs wnl st1 st3 (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word),
  st_ok bsegs OPS E st ms mo -> PB (eb E) ->
  (forall st', In st' [setpc (HalfC.TwinB.HalfC.set_regs st3 (fp_regs st)) REAL_VF] -> forall E' ms' mo', env_ext (s_next st) E E' -> MP mo' -> st_ok bsegs OPS E' st' ms' mo' ->
               realizes bsegs (mkCfg ms' mo') K) ->
  acall_pre ASTACK None st = Some (r, hargs, wnl, st1) ->
  HalfC.TwinB.HalfC.push_cells bsegs (setpc (setr (clobber st1) X10 (getr st X10)) r) (fp_sp st) (fp_cells st r) = Some st3 ->
  call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) -> ALib.Mem.mem_inv bsegs (ms_mem ms) ->
  let R := ms_regs ms in
  ATOP + 4096 <= CtrPre.TwinB.sp_lo E st -> CtrPre.TwinB.sp_lo E st <= bv_unsigned (AP.getr R 2) - 4096 -> bv_unsigned (AP.getr R 2) < 2 ^ 47 ->
  forall ms' mo',
  IPI.fprintf_i_mid (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9) (AP.getr R 10) (AP.getr R 11)
     (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16) (AP.getr R 17)
     (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
     (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (CtrPre.TwinB.sp_lo E st) (ms_mem ms) ms' ->
  MP mo' -> op_minv OPS mo' -> OTHER mo mo' -> ACCT aw L RNG sta LBa mo' ->
  realizes bsegs (mkCfg ms' mo') K.

Theorem afprintf_sound_of_leaf : afprintf_leaf ->
  forall pc, to_Z pc = FPRINTF_SYM -> contract_sound bsegs OPS MP PB (afprintf_pre_c bsegs FMT_TOOBIG pc).
Proof.
  intros LEAF pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc afprintf_pre_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = FPRINTF_SYM) by (rewrite Hspc; exact Hpc).
  destruct (afprintf_apply_shape _ st sts Happ) as (r & hargs & wnl & st1 & st3 & PRE & G11 & FZ & PUSH & ->).
  destruct (CtrPre.TwinB.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT.
  set (R := ms_regs ms) in *.
  pose proof atop_range as ATR.

  pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (UnreggPre.TwinB.find_op_In _ _ _ FZ)) as HO. cbn [op_id op_args map] in HO.
  pose proof (OPS_holds_zro _ _ HO) as ZRO.
  assert (EA0 : AP.getr R (reg_of_r5 X11) = Z_to_bv 64 IPF.FMT_TOOBIG).
  { unfold R. rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X11), G11. reflexivity. }
  assert (EA0' : AP.getr R 11 = Z_to_bv 64 IPF.FMT_TOOBIG) by exact EA0.
  idtac "FS-1".
  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  pose proof (ACCT_rng_aimg _ _ _ _ _ _ AC) as RIMG. pose proof (ACCT_rng_aimg_sh _ _ _ _ _ _ AC) as RSH.
  assert (EV : evtF bsegs RNG
            (IPI.fprintf_i_mid (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9) (AP.getr R 10) (AP.getr R 11)
     (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16) (AP.getr R 17)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (CtrPre.TwinB.sp_lo E st) (ms_mem ms))
            (MS (mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31))
                (ms_fregs ms) (Z_to_bv 64 FPRINTF_SYM) (ms_fcsr ms) None (ms_mem ms) (seg_rom bsegs))).
  { unfold artcells in RT. decompose [and] RT. clear RT.
    eapply (IPI.fprintf_i_pre_toobig RNG).
    all: try lazymatch goal with
         | |- ALib.Mem.mem_inv _ _ => exact MI
         | |- stk _ _ _ _ => exact ST
         | |- ALib.Step.rw_cells _ _ _ _ => assumption
         | |- Shadow.shadow_bytes _ _ _ _ => apply (zro_shadow_bytes _ _ _ ZRO); unfold IPF.FMT_TOOBIG; lia
         | |- rng_aimg _ => exact RIMG
         | |- AP.getr _ _ = _ => exact EA0'
         | |- rng _ (shad _) _ => apply (rng_sub _ _ _ _ _ RSH); unfold IPF.FMT_TOOBIG, shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia
         | |- rng _ _ _ => exact RSTK
         end.
    all: try (unfold Shadow.KHIGH in *; lia).
    all: match goal with |- ?G => idtac "REMW" G end. }
  rewrite Ems, HPC. apply (GlueA.TwinB.realizes_to_mkRA bsegs).
  eapply (implS_twfS_realizes_silent bsegs NMAXt (Ret (Exc.Ok tt)) RNG AL0
            (fun (_ : unit) (RNGq : footprint) ms' => RNGq = RNG /\ IPI.fprintf_i_mid (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9) (AP.getr R 10) (AP.getr R 11)
     (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16) (AP.getr R 17)
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
    exact (LEAF st K E ms mo r hargs wnl st1 st3 L RNG sta LBa aw HS HPB HK PRE PUSH CP FS CF AH MI BOT LO SPT ms' mo' HQ HMP' HMI' OTH ACP).
Qed.
End Sound.
End TwinB.
