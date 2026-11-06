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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require I_asan_memcpy.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import RtCells.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import StackSh RangeC MemsetC MemsetPre RangePre MemsetSound PubC PubImg MemsetPC.
Unset Nia Cache. Unset Nra Cache.
Import CtrFX ActrA MemsetC MemsetPC.
Module IM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy.I_memset.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis Cw_sub_ghost : forall md ca LB ws m w g a, cw_holds Cw md ca LB ws m -> In w ws -> In g ws ->
  K_SUB <= w_kind w < K_GHOST -> K_GHOST <= w_kind g -> in_iv (w_iv w) a -> in_iv (w_iv g) a -> False.
Hypothesis OPS_holds_ssh : forall m mo, op_holds OPS RangeC.SSH_ID [] m mo -> ssh_holds m.
Variable OTHER : Model -> Model -> Prop.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable NMAXt : nat.
Variable SYM : Z.
Hypothesis WALK : memset_walk_stmt SYM.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Hypothesis ACCT_rng_stk_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (shad ATOP) (Shadow.KHIGH - shad ATOP).
Hypothesis ACCT_frng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> FRNG AI AI_fake L RNG.
Hypothesis W_PAT : w_pat_ev_stmt AI ACCT UNIV Cw OPS.
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent ACCT OPS OTHER MP mo aw L st LBa).

Hypothesis ACCT_rng_aimg_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG 0x7fffa000 0xc4000.
Hypothesis OPS_holds_zpb : forall m mo, op_holds OPS PubC.ZPB_ID [] m mo -> zpb_holds m.

Lemma amemsetp_apply_shape : forall st sts, amemsetp_apply asegs st = Some sts ->
  exists r hargs wnl st1 a c n,
    acall_pre ASTACK None st = Some (r, hargs, wnl, st1) /\ getr st X10 = VL a /\ getr st X11 = VL c /\ getr st X12 = VL n
    /\ wt n = false /\ 1 <= to_Z (wl n) <= 4096 /\ PubC.lit_pub st a (wl n) = true
    /\ set_bytes_post_p asegs a (PrimInt63.land (wl c) 255%uint63) (wl n) (setpc (setr (clobber st1) X10 (VL a)) r) = Some sts.
Proof.
  intros st sts H. unfold amemsetp_apply in H.
  destruct (acall_pre ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:P; [|discriminate H].
  destruct (getr st X10) as [a| | | | | | | | | |] eqn:G10; try discriminate H.
  destruct (getr st X11) as [c| | | | | | | | | |] eqn:G11; try discriminate H.
  destruct (getr st X12) as [n| | | | | | | | | |] eqn:G12; try discriminate H.
  cbv zeta in H. match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:CND; [|discriminate H] end.
  repeat match type of CND with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in CND as [CND X] end.
  apply negb_true_iff in CND; apply Uint63.leb_spec in Q1; apply Uint63.leb_spec in Q0; change (to_Z 1%uint63) with 1 in Q1; change (to_Z MemsetC.NMAX) with 4096 in Q0.
  exists r, hargs, wnl, st1, a, c, n. repeat split; try reflexivity; try eassumption; lia.
Qed.

Definition amemsetp_leaf : Prop :=
  forall st sts (K : TSet) E ms mo r hargs wnl st1 a c n (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word),
  st_ok asegs OPS E st ms mo -> PB (eb E) ->
  (forall st', In st' sts -> forall E' ms' mo', env_ext (s_next st) E E' -> MP mo' -> st_ok asegs OPS E' st' ms' mo' ->
               realizes asegs (mkCfg ms' mo') K) ->
  acall_pre ASTACK None st = Some (r, hargs, wnl, st1) -> getr st X10 = VL a -> getr st X11 = VL c -> getr st X12 = VL n ->
  wt a = false -> wt n = false -> 1 <= to_Z (wl n) <= 4096 ->
  set_bytes_post_p asegs a (PrimInt63.land (wl c) 255%uint63) (wl n) (setpc (setr (clobber st1) X10 (VL a)) r) = Some sts ->
  call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) -> ALib.Mem.mem_inv asegs (ms_mem ms) ->
  let R := ms_regs ms in
  ATOP + 4096 <= CtrPre.sp_lo E st -> CtrPre.sp_lo E st <= bv_unsigned (AP.getr R 2) - 4096 -> bv_unsigned (AP.getr R 2) < 2 ^ 47 ->
  let A0 := to_Z (wl a) in
  in_pubw A0 (A0 + to_Z (wl n)) ->
  (forall x, A0 <= x < A0 + to_Z (wl n) -> ~ in_priv (s_priv st) x) ->
  bv_unsigned (AP.getr R 10) = A0 -> bv_unsigned (AP.getr R 12) = to_Z (wl n) -> AP.getr R 11 = wbv c ->
  forall ms' mo',
  IM.memset_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
     (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
     (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (CtrPre.sp_lo E st) (ms_mem ms) ms' ->
  MP mo' -> op_minv OPS mo' -> OTHER mo mo' -> ACCT aw L RNG sta LBa mo' ->
  realizes asegs (mkCfg ms' mo') K.

Theorem amemsetp_sound_of_leaf : amemsetp_leaf ->
  forall pc, to_Z pc = SYM -> contract_sound asegs OPS MP PB (amemsetp_c asegs pc).
Proof.
  intros LEAF pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc amemsetp_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = SYM) by (rewrite Hspc; exact Hpc).
  destruct (amemsetp_apply_shape st sts Happ) as (r & hargs & wnl & st1 & a & c & n & PRE & G10 & G11 & G12 & WTN & NR & LPUB & SB).
  destruct (CtrPre.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT.
  set (R := ms_regs ms) in *. set (len := to_Z (wl n)) in *.

  destruct (lit_pub_inv st a (wl n) LPUB ltac:(lia)) as (WTA & PW & NPRIV & FZP). fold len in PW, NPRIV.
  pose proof (in_pubw_bounds _ _ PW) as [PLO PHI].
  pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (UnreggPre.find_op_In _ _ _ FZP)) as HOP. cbn [op_id op_args map] in HOP.
  pose proof (OPS_holds_zpb _ _ HOP) as ZPB.
  set (A0 := to_Z (wl a)) in *.
  pose proof atop_range as ATR.
  destruct (pub_range_facts_ok RNG (ms_mem ms) A0 len ZPB (ACCT_rng_aimg _ _ _ _ _ _ AC) (ACCT_rng_aimg_sh _ _ _ _ _ _ AC) PW ltac:(lia))
    as (_ & (junk & DST) & APB & UNP & RNGD & RLO2 & RHI2 & HULL & WRH & RNGH).

  assert (EA0 : bv_unsigned (AP.getr R (reg_of_r5 X10)) = A0).
  { unfold R. rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X10), G10. cbn [den]. rewrite wbv_unsigned. unfold w2Z, A0. rewrite WTA. lia. }
  assert (EA2 : bv_unsigned (AP.getr R (reg_of_r5 X12)) = len).
  { unfold R. rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X12), G12. cbn [den]. rewrite wbv_unsigned. unfold w2Z. rewrite WTN. unfold len. lia. }
  assert (EA1 : AP.getr R (reg_of_r5 X11) = wbv c) by (unfold R; rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X11), G11; reflexivity).
  assert (EA0' : bv_unsigned (AP.getr R 10) = A0) by exact EA0. assert (EA2' : bv_unsigned (AP.getr R 12) = len) by exact EA2.
  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  pose proof (ACCT_rng_aimg _ _ _ _ _ _ AC) as RIMG.
  assert (POS0 : A0 + len <= CtrPre.sp_lo E st) by lia.
  assert (EV : evtF asegs RNG
            (IM.memset_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (CtrPre.sp_lo E st) (ms_mem ms))
            (MS (mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31))
                (ms_fregs ms) (Z_to_bv 64 SYM) (ms_fcsr ms) None (ms_mem ms) (seg_rom asegs))).
  { unfold artcells in RT. decompose [and] RT. clear RT.
    eapply (WALK RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_fregs ms) (ms_fcsr ms) (ms_mem ms)
              (CtrPre.sp_lo E st) junk RLO2 RHI2).
    all: rewrite ?EA0', ?EA2'.
    all: try lazymatch goal with
         | |- ALib.Mem.mem_inv _ _ => exact MI
         | |- stk _ _ _ _ => exact ST
         | |- ALib.Step.rw_cells _ _ _ [CB _ _] => exact DST
         | |- ALib.Step.rw_cells _ _ _ _ => assumption
         | |- Shadow.unpoisoned _ _ _ => exact UNP
         | |- Shadow.app_blk _ _ => exact APB
         | |- ALib.Mem.wr_at _ _ _ _ => exact WRH
         | |- rng_aimg _ => exact RIMG
         | |- rng _ _ _ => first [exact RSTK | exact RNGD | exact RNGH]
         | |- _ /\ _ => exact HULL
         end.
    all: try (unfold Shadow.KHIGH in *; lia).
    all: try (left; exact POS0).
    all: match goal with |- ?G => idtac "REMW" G end. }
  rewrite Ems, HPC. apply (GlueA.realizes_to_mkRA asegs).
  eapply (implS_twfS_realizes_silent asegs NMAXt (Ret (Exc.Ok tt)) RNG AL0
            (fun (_ : unit) (RNGq : footprint) ms' => RNGq = RNG /\ IM.memset_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (CtrPre.sp_lo E st) (ms_mem ms) ms')
            _ _ moc mo K).
  - cbn [implF epostF]. eapply evtF_mono; [exact EV|]. intros ms' PO. split; [reflexivity| exact PO].
  - exact TW.
  - exact HH.
  - exact MINV.
  - exact MR.
  - intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV' MR'.
    destruct (HP' mo' MR') as (HMP' & HMI' & OTH & ACP). destruct HQ as [-> HQ].
    exact (LEAF st sts K E ms mo r hargs wnl st1 a c n L RNG sta LBa aw HS HPB HK PRE G10 G11 G12 WTA WTN NR SB CP FS CF AH MI BOT LO SPT
             PW NPRIV EA0 EA2 EA1 ms' mo' HQ HMP' HMI' OTH ACP).
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
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Ledger.TwinB Op.TwinB Adeq.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Import Actr.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import UnreggSound.TwinB.
Import StackSh.TwinB RangeC.TwinB MemsetC.TwinB MemsetPre.TwinB RangePre.TwinB MemsetSound.TwinB PubC.TwinB PubImg.TwinB MemsetPC.TwinB.
Unset Nia Cache. Unset Nra Cache.
Import CtrFX ActrA MemsetC.TwinB.MemsetC MemsetPC.TwinB.MemsetPC.
Module IM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy.TwinB.I_memset.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis Cw_sub_ghost : forall md ca LB ws m w g a, cw_holds Cw md ca LB ws m -> In w ws -> In g ws ->
  K_SUB <= w_kind w < K_GHOST -> K_GHOST <= w_kind g -> in_iv (w_iv w) a -> in_iv (w_iv g) a -> False.
Hypothesis OPS_holds_ssh : forall m mo, op_holds OPS RangeC.TwinB.RangeC.SSH_ID [] m mo -> ssh_holds m.
Variable OTHER : Model -> Model -> Prop.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable NMAXt : nat.
Variable SYM : Z.
Hypothesis WALK : memset_walk_stmt SYM.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Hypothesis ACCT_rng_stk_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (shad ATOP) (Shadow.KHIGH - shad ATOP).
Hypothesis ACCT_frng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> FRNG AI AI_fake L RNG.
Hypothesis W_PAT : w_pat_ev_stmt AI ACCT UNIV Cw OPS.
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent ACCT OPS OTHER MP mo aw L st LBa).

Hypothesis ACCT_rng_aimg_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG 0x7fffa000 0xc5000.
Hypothesis OPS_holds_zpb : forall m mo, op_holds OPS PubC.TwinB.PubC.ZPB_ID [] m mo -> zpb_holds m.

Lemma amemsetp_apply_shape : forall st sts, amemsetp_apply bsegs st = Some sts ->
  exists r hargs wnl st1 a c n,
    acall_pre ASTACK None st = Some (r, hargs, wnl, st1) /\ getr st X10 = VL a /\ getr st X11 = VL c /\ getr st X12 = VL n
    /\ wt n = false /\ 1 <= to_Z (wl n) <= 4096 /\ PubC.TwinB.PubC.lit_pub st a (wl n) = true
    /\ set_bytes_post_p bsegs a (PrimInt63.land (wl c) 255%uint63) (wl n) (setpc (setr (clobber st1) X10 (VL a)) r) = Some sts.
Proof.
  intros st sts H. unfold amemsetp_apply in H.
  destruct (acall_pre ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:P; [|discriminate H].
  destruct (getr st X10) as [a| | | | | | | | | |] eqn:G10; try discriminate H.
  destruct (getr st X11) as [c| | | | | | | | | |] eqn:G11; try discriminate H.
  destruct (getr st X12) as [n| | | | | | | | | |] eqn:G12; try discriminate H.
  cbv zeta in H. match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:CND; [|discriminate H] end.
  repeat match type of CND with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in CND as [CND X] end.
  apply negb_true_iff in CND; apply Uint63.leb_spec in Q1; apply Uint63.leb_spec in Q0; change (to_Z 1%uint63) with 1 in Q1; change (to_Z MemsetC.TwinB.MemsetC.NMAX) with 4096 in Q0.
  exists r, hargs, wnl, st1, a, c, n. repeat split; try reflexivity; try eassumption; lia.
Qed.

Definition amemsetp_leaf : Prop :=
  forall st sts (K : TSet) E ms mo r hargs wnl st1 a c n (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word),
  st_ok bsegs OPS E st ms mo -> PB (eb E) ->
  (forall st', In st' sts -> forall E' ms' mo', env_ext (s_next st) E E' -> MP mo' -> st_ok bsegs OPS E' st' ms' mo' ->
               realizes bsegs (mkCfg ms' mo') K) ->
  acall_pre ASTACK None st = Some (r, hargs, wnl, st1) -> getr st X10 = VL a -> getr st X11 = VL c -> getr st X12 = VL n ->
  wt a = false -> wt n = false -> 1 <= to_Z (wl n) <= 4096 ->
  set_bytes_post_p bsegs a (PrimInt63.land (wl c) 255%uint63) (wl n) (setpc (setr (clobber st1) X10 (VL a)) r) = Some sts ->
  call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) -> ALib.Mem.mem_inv bsegs (ms_mem ms) ->
  let R := ms_regs ms in
  ATOP + 4096 <= CtrPre.TwinB.sp_lo E st -> CtrPre.TwinB.sp_lo E st <= bv_unsigned (AP.getr R 2) - 4096 -> bv_unsigned (AP.getr R 2) < 2 ^ 47 ->
  let A0 := to_Z (wl a) in
  in_pubw A0 (A0 + to_Z (wl n)) ->
  (forall x, A0 <= x < A0 + to_Z (wl n) -> ~ in_priv (s_priv st) x) ->
  bv_unsigned (AP.getr R 10) = A0 -> bv_unsigned (AP.getr R 12) = to_Z (wl n) -> AP.getr R 11 = wbv c ->
  forall ms' mo',
  IM.memset_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
     (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
     (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (CtrPre.TwinB.sp_lo E st) (ms_mem ms) ms' ->
  MP mo' -> op_minv OPS mo' -> OTHER mo mo' -> ACCT aw L RNG sta LBa mo' ->
  realizes bsegs (mkCfg ms' mo') K.

Theorem amemsetp_sound_of_leaf : amemsetp_leaf ->
  forall pc, to_Z pc = SYM -> contract_sound bsegs OPS MP PB (amemsetp_c bsegs pc).
Proof.
  intros LEAF pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc amemsetp_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = SYM) by (rewrite Hspc; exact Hpc).
  destruct (amemsetp_apply_shape st sts Happ) as (r & hargs & wnl & st1 & a & c & n & PRE & G10 & G11 & G12 & WTN & NR & LPUB & SB).
  destruct (CtrPre.TwinB.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT.
  set (R := ms_regs ms) in *. set (len := to_Z (wl n)) in *.

  destruct (lit_pub_inv st a (wl n) LPUB ltac:(lia)) as (WTA & PW & NPRIV & FZP). fold len in PW, NPRIV.
  pose proof (in_pubw_bounds _ _ PW) as [PLO PHI].
  pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (UnreggPre.TwinB.find_op_In _ _ _ FZP)) as HOP. cbn [op_id op_args map] in HOP.
  pose proof (OPS_holds_zpb _ _ HOP) as ZPB.
  set (A0 := to_Z (wl a)) in *.
  pose proof atop_range as ATR.
  destruct (pub_range_facts_ok RNG (ms_mem ms) A0 len ZPB (ACCT_rng_aimg _ _ _ _ _ _ AC) (ACCT_rng_aimg_sh _ _ _ _ _ _ AC) PW ltac:(lia))
    as (_ & (junk & DST) & APB & UNP & RNGD & RLO2 & RHI2 & HULL & WRH & RNGH).

  assert (EA0 : bv_unsigned (AP.getr R (reg_of_r5 X10)) = A0).
  { unfold R. rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X10), G10. cbn [den]. rewrite wbv_unsigned. unfold w2Z, A0. rewrite WTA. lia. }
  assert (EA2 : bv_unsigned (AP.getr R (reg_of_r5 X12)) = len).
  { unfold R. rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X12), G12. cbn [den]. rewrite wbv_unsigned. unfold w2Z. rewrite WTN. unfold len. lia. }
  assert (EA1 : AP.getr R (reg_of_r5 X11) = wbv c) by (unfold R; rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X11), G11; reflexivity).
  assert (EA0' : bv_unsigned (AP.getr R 10) = A0) by exact EA0. assert (EA2' : bv_unsigned (AP.getr R 12) = len) by exact EA2.
  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  pose proof (ACCT_rng_aimg _ _ _ _ _ _ AC) as RIMG.
  assert (POS0 : A0 + len <= CtrPre.TwinB.sp_lo E st) by lia.
  assert (EV : evtF bsegs RNG
            (IM.memset_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (CtrPre.TwinB.sp_lo E st) (ms_mem ms))
            (MS (mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31))
                (ms_fregs ms) (Z_to_bv 64 SYM) (ms_fcsr ms) None (ms_mem ms) (seg_rom bsegs))).
  { unfold artcells in RT. decompose [and] RT. clear RT.
    eapply (WALK RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_fregs ms) (ms_fcsr ms) (ms_mem ms)
              (CtrPre.TwinB.sp_lo E st) junk RLO2 RHI2).
    all: rewrite ?EA0', ?EA2'.
    all: try lazymatch goal with
         | |- ALib.Mem.mem_inv _ _ => exact MI
         | |- stk _ _ _ _ => exact ST
         | |- ALib.Step.rw_cells _ _ _ [CB _ _] => exact DST
         | |- ALib.Step.rw_cells _ _ _ _ => assumption
         | |- Shadow.unpoisoned _ _ _ => exact UNP
         | |- Shadow.app_blk _ _ => exact APB
         | |- ALib.Mem.wr_at _ _ _ _ => exact WRH
         | |- rng_aimg _ => exact RIMG
         | |- rng _ _ _ => first [exact RSTK | exact RNGD | exact RNGH]
         | |- _ /\ _ => exact HULL
         end.
    all: try (unfold Shadow.KHIGH in *; lia).
    all: try (left; exact POS0).
    all: match goal with |- ?G => idtac "REMW" G end. }
  rewrite Ems, HPC. apply (GlueA.TwinB.realizes_to_mkRA bsegs).
  eapply (implS_twfS_realizes_silent bsegs NMAXt (Ret (Exc.Ok tt)) RNG AL0
            (fun (_ : unit) (RNGq : footprint) ms' => RNGq = RNG /\ IM.memset_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (CtrPre.TwinB.sp_lo E st) (ms_mem ms) ms')
            _ _ moc mo K).
  - cbn [implF epostF]. eapply evtF_mono; [exact EV|]. intros ms' PO. split; [reflexivity| exact PO].
  - exact TW.
  - exact HH.
  - exact MINV.
  - exact MR.
  - intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV' MR'.
    destruct (HP' mo' MR') as (HMP' & HMI' & OTH & ACP). destruct HQ as [-> HQ].
    exact (LEAF st sts K E ms mo r hargs wnl st1 a c n L RNG sta LBa aw HS HPB HK PRE G10 G11 G12 WTA WTN NR SB CP FS CF AH MI BOT LO SPT
             PW NPRIV EA0 EA2 EA1 ms' mo' HQ HMP' HMI' OTH ACP).
Qed.
End Sound.
End TwinB.
