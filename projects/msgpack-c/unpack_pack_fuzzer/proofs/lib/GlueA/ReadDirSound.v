(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem ALib.Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA NodesA SysStepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_iface2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require I_asan_memcpy0.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib Defs DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Ops.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op Adeq.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA GlueA CtrPre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import UnreggSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import ReadC ReadDirC ReadPre ReadAdeq ReadSound.
Import ValP CtrFX ActrA ReadC ReadDirC.
Module IR := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy0.I_read.

Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis OPS_holds_zsh : forall m mo, op_holds OPS (r_zsh CFG_ASAN) [] m mo -> zsh_holds m.

Hypothesis OPS_holds_fd3dir : forall args m mo, op_holds OPS CtrS.FD3DIR_ID args m mo -> Ops.Ops.fd3dir_holds args mo.
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

Lemma aread_dir_pre_inv : forall st, aread_dir_pre CFG_ASAN st = true ->
  CtrS.is_lit (Step.getr st X10) (wlit 3%uint63) = true /\ CtrS.is_lit (Step.getr st X11) (wlit 6275344%uint63) = true
  /\ CtrS.priv_has st 6275344%uint63 CtrS.STAGE_LEN = true
  /\ (exists w, CtrS.want_ok (Step.getr st X12) = Some w)
  /\ CtrS.one_fd_op st = true /\ find_op CtrS.FD3DIR_ID (s_ops st) = Some [] /\ find_op 11%uint63 (s_ops st) = Some [].
Proof.
  intros st B. unfold aread_dir_pre in B. cbn [r_stage r_zsh CFG_ASAN] in B.
  repeat match type of B with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in B as [B X] end.
  split; [exact B|]. split; [exact Q4|]. split; [exact Q3|].
  split; [destruct (CtrS.want_ok (Step.getr st X12)) as [w|]; [exists w; reflexivity| discriminate Q2]|].
  split; [exact Q1|].
  destruct (find_op CtrS.FD3DIR_ID (s_ops st)) as [[|? ?]|] eqn:FD; try discriminate Q0.
  destruct (find_op 11%uint63 (s_ops st)) as [[|? ?]|] eqn:FZ; try discriminate Q.
  split; reflexivity.
Qed.

Lemma aread_dir_pre_facts : forall E st ms mo,
  st_ok asegs OPS E st ms mo -> aread_dir_pre CFG_ASAN st = true ->
  AP.getr (ms_regs ms) (reg_of_r5 X10) = Z_to_bv 64 3 /\ AP.getr (ms_regs ms) (reg_of_r5 X11) = Z_to_bv 64 STAGE /\ zsh_holds (ms_mem ms)
  /\ m_fds mo = (Ops.Ops.fd3, FdDir) :: Ops.Ops.FDS0.
Proof.
  intros E st ms mo HS H. destruct (aread_dir_pre_inv st H) as (A0 & A1 & _ & _ & _ & F4 & FZ).
  unfold CtrS.is_lit in A0, A1. apply sv_eqb_eq in A0. apply sv_eqb_eq in A1.
  split; [rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X10), A0; reflexivity|].
  split; [rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X11), A1; reflexivity|].
  pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (find_op_In _ _ _ FZ)) as HO. cbn [op_id op_args map] in HO.
  split; [exact (OPS_holds_zsh _ _ HO)|].
  pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (find_op_In _ _ _ F4)) as HO4. cbn [op_id op_args map] in HO4.
  apply OPS_holds_fd3dir in HO4. exact HO4.
Qed.

Lemma aread_dir_apply_shape : forall st sts, aread_dir_apply CFG_ASAN st = Some sts ->
  exists r hargs wnl st1 stE, acall_pre ASTACK None st = Some (r, hargs, wnl, st1) /\ aread_dir_pre CFG_ASAN st = true
    /\ errno_havoc (setr (clobber st1) X10 MINUS1) = Some stE /\ sts = [setpc stE r].
Proof.
  intros st sts H. unfold aread_dir_apply in H.
  destruct (acall_pre ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:P; [|discriminate H].
  destruct (aread_dir_pre CFG_ASAN st) eqn:B; [|discriminate H].
  destruct (errno_havoc (setr (clobber st1) X10 MINUS1)) as [stE|] eqn:HV; [|discriminate H].
  injection H as <-. exists r, hargs, wnl, st1, stE. split; [reflexivity|]. split; [reflexivity|]. split; [exact HV| reflexivity].
Qed.

Definition aread_dir_leaf : Prop :=
  forall st (K : TSet) E ms mo r hargs wnl st1 stE (cnt : Z) (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word)
         (junk : list byte) (errv : word),
  st_ok asegs OPS E st ms mo -> MP mo -> PB (eb E) ->
  (forall E' ms' mo', env_ext (s_next st) E E' -> MP mo' -> st_ok asegs OPS E' (setpc stE r) ms' mo' -> realizes asegs (mkCfg ms' mo') K) ->
  acall_pre ASTACK None st = Some (r, hargs, wnl, st1) -> aread_dir_pre CFG_ASAN st = true ->
  errno_havoc (setr (clobber st1) X10 MINUS1) = Some stE ->
  bv_unsigned (den E (Step.getr st X12)) = cnt -> 0 < cnt <= 65536 ->
  call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) ->
  let R := ms_regs ms in
  ATOP + 4096 <= CtrPre.sp_lo E st -> CtrPre.sp_lo E st <= bv_unsigned (AP.getr R 2) - 4096 -> bv_unsigned (AP.getr R 2) < 2 ^ 47 ->
  AP.getr R 4 = Z_to_bv 64 ATP -> ALib.Mem.mem_inv asegs (ms_mem ms) ->
  AS.rw_cells asegs (ms_mem ms) STAGE [CB (Z.to_nat cnt) junk] -> AS.rw_cells asegs (ms_mem ms) ERRNO [C4 errv] ->
  zsh_holds (ms_mem ms) ->
  forall ms' mo',
  IR.read_i_post RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
     (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
     (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) STAGE (Z.to_nat cnt) junk errv (CtrPre.sp_lo E st) (ms_mem ms)
     (RdErr EISDIR) RNG ms' ->
  MP mo' -> op_minv OPS mo' -> OTHER mo mo' -> ACCT aw L RNG sta LBa mo' ->
  realizes asegs (mkCfg ms' mo') K.

Theorem aread_dir_sound_of_leaf : aread_dir_leaf ->
  forall pc, to_Z pc = READ_SYM -> contract_sound asegs OPS MP PB (aread_dir_c CFG_ASAN pc).
Proof.
  intros LEAF pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc aread_dir_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = READ_SYM) by (rewrite Hspc; exact Hpc).
  destruct (aread_dir_apply_shape st sts Happ) as (r & hargs & wnl & st1 & stE & PRE & RPRE & HAV & ->).
  destruct (CtrPre.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT.
  destruct (aread_dir_pre_facts E st ms mo HS RPRE) as (A0E & A1E & ZSH & FDS).
  destruct (aread_dir_pre_inv st RPRE) as (_ & _ & _ & [w HW] & _ & F4 & _).

  set (R := ms_regs ms) in *. set (cnt := bv_unsigned (den E (Step.getr st X12))) in *.
  assert (WR : 0 < cnt <= 65536).
  { destruct (want_ok_inv _ _ HW) as [X12E WR0]. unfold cnt. rewrite X12E. cbn [den]. rewrite wbv_unsigned. exact WR0. }
  assert (A2E : AP.getr R (reg_of_r5 X12) = Z_to_bv 64 cnt).
  { unfold R. rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X12). unfold cnt. symmetry. apply Z_to_bv_bv_unsigned. }

  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (A0 & moc & MR & MINV & HH & TW).
  pose proof (ACCT_rng_aimg _ _ _ _ _ _ AC) as RIMG. pose proof (ACCT_rng_aimg_sh _ _ _ _ _ _ AC) as RISH.
  cbn [twfA] in TW. destruct TW as [ACC LEAFC].
  pose proof atop_range as ATR.

  destruct (stage_chunk (ms_mem ms) (Z.to_nat cnt) ltac:(lia)) as [junk STG].
  destruct (errno_chunk (ms_mem ms)) as [errv ERR].
  assert (EB : bv_unsigned (AP.getr R (reg_of_r5 X11)) = STAGE) by (rewrite A1E; vm_compute; reflexivity).
  assert (ETP : bv_unsigned (AP.getr R 4) + -164 = ERRNO) by (rewrite TP; vm_compute; reflexivity).
  assert (TPU : bv_unsigned (AP.getr R 4) = 0x60cc80) by (rewrite TP; vm_compute; reflexivity).
  assert (SH1 : shad RLO2 = ZSH_LO) by (vm_compute; reflexivity). assert (SH2 : shad RHI2 = ZSH_HI) by (vm_compute; reflexivity).
  assert (EV : implA asegs RNG (enode (NRead 3 (bv_unsigned (AP.getr R (reg_of_r5 X11))) cnt) (dec_read (bv_unsigned (AP.getr R (reg_of_r5 X11))) cnt))
            (epostF (IR.read_i_post RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (bv_unsigned (AP.getr R (reg_of_r5 X11))) (Z.to_nat cnt) junk errv
               (CtrPre.sp_lo E st) (ms_mem ms)))
            (MS (mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31))
                (ms_fregs ms) (Z_to_bv 64 0x4f1f8) (ms_fcsr ms) None (ms_mem ms) (seg_rom asegs))).
  { unfold artcells in RT. decompose [and] RT. clear RT.
    eapply (IR.read_i_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_fregs ms) (ms_fcsr ms) (ms_mem ms)
              (CtrPre.sp_lo E st) 3 cnt junk errv RLO2 RHI2).
    all: rewrite ?EB, ?ETP, ?SH1, ?SH2.
    all: try lazymatch goal with
         | |- ALib.Mem.mem_inv _ _ => exact MI
         | |- stk _ _ _ _ => exact ST
         | |- AS.rw_cells _ _ STAGE _ => exact STG
         | |- AS.rw_cells _ _ ERRNO _ => exact ERR
         | |- AS.rw_cells _ _ _ _ => assumption
         | |- Shadow.unpoisoned _ _ _ => apply (zsh_unpoisoned _ _ ZSH); lia
         | |- ALib.Mem.wr_at _ _ _ _ => rewrite <- SH1, <- SH2; exact (zsh_wr _ ZSH)
         | |- rng_aimg _ => exact RIMG
         | |- rng _ (CtrPre.sp_lo _ _) _ => exact RSTK
         | |- rng _ ZSH_LO _ => eapply rng_sub'; [exact RISH| unfold ZSH_LO, ZSH_HI; lia]
         | |- rng _ _ _ => eapply rng_sub'; [exact RIMG| unfold STAGE, ERRNO, AIMG_HI in *; lia]
         | |- @eq word _ _ => first [exact A0E | exact A2E]
         | |- Shadow.app_blk _ _ => unfold Shadow.app_blk, Shadow.KLOW, Shadow.KHIGH, Shadow.KEND, STAGE; lia
         end.
    all: try (unfold STAGE, ERRNO, RLO2, RHI2, Shadow.KHIGH, Shadow.KEND in *; lia).
    all: match goal with |- ?G => idtac "REMW" G end. }
  rewrite EB in EV.
  pose proof (mrel_fds _ _ _ MR) as FDE.
  rewrite Ems, HPC. apply (GlueA.realizes_to_mkRA asegs).
  eapply (implA_twfA_realizes_silent asegs NMAXt (enode (NRead 3 STAGE cnt) (dec_read STAGE cnt)) RNG A0
            (IR.read_i_post RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) STAGE (Z.to_nat cnt) junk errv (CtrPre.sp_lo E st) (ms_mem ms))
            (fun a RNG' A' moc' => a = RdErr EISDIR /\ RNG' = RNG /\ A' = A0 /\ moc' = moc)
            _ moc mo K).
  - exact EV.
  - apply (twfA_read_dir NMAXt RNG A0 moc 3 STAGE cnt).
    + exact ACC.
    + apply (NodesA.fd_inv_dir3 moc); rewrite <- FDE, FDS; reflexivity.
    + rewrite <- FDE, FDS. reflexivity.
    + subst cnt. lia.
    + repeat split; reflexivity.
  - exact HH.
  - exact MINV.
  - exact MR.
  - intros a RNG' A' ms' moc' mo' HQ (-> & -> & -> & ->) ACC' HH' MINV' MR'.
    destruct (LEAFC _ MR') as (MP' & MI' & OT' & AC').
    exact (LEAF st K E ms mo r hargs wnl st1 stE cnt L RNG sta LBa aw junk errv HS HMP HPB
             (fun E' ms'' mo'' EXT MP'' HS'' => HK _ (or_introl eq_refl) E' ms'' mo'' EXT MP'' HS'')
             PRE RPRE HAV eq_refl WR CP FS CF AH BOT LO SPT TP MI STG ERR ZSH ms' mo' HQ MP' MI' OT' AC').
Qed.
End Sound.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.NodesA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB.
Import AMalloc_iface2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Defs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Ledger.TwinB Op.TwinB Adeq.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import Actr.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import UnreggSound.TwinB.
Import ReadC.TwinB ReadDirC.TwinB ReadPre.TwinB ReadAdeq.TwinB ReadSound.TwinB.
Import ValP CtrFX ActrA ReadC.TwinB.ReadC ReadDirC.TwinB.ReadDirC.
Module IR := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy0.TwinB.I_read.

Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis OPS_holds_zsh : forall m mo, op_holds OPS (r_zsh CFG_ASAN) [] m mo -> zsh_holds m.

Hypothesis OPS_holds_fd3dir : forall args m mo, op_holds OPS CtrS.FD3DIR_ID args m mo -> Ops.Ops.fd3dir_holds args mo.
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

Lemma aread_dir_pre_inv : forall st, aread_dir_pre CFG_ASAN st = true ->
  CtrS.is_lit (Step.getr st X10) (wlit 3%uint63) = true /\ CtrS.is_lit (Step.getr st X11) (wlit 6283984%uint63) = true
  /\ CtrS.priv_has st 6283984%uint63 CtrS.STAGE_LEN = true
  /\ (exists w, CtrS.want_ok (Step.getr st X12) = Some w)
  /\ CtrS.one_fd_op st = true /\ find_op CtrS.FD3DIR_ID (s_ops st) = Some [] /\ find_op 11%uint63 (s_ops st) = Some [].
Proof.
  intros st B. unfold aread_dir_pre in B. cbn [r_stage r_zsh CFG_ASAN] in B.
  repeat match type of B with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in B as [B X] end.
  split; [exact B|]. split; [exact Q4|]. split; [exact Q3|].
  split; [destruct (CtrS.want_ok (Step.getr st X12)) as [w|]; [exists w; reflexivity| discriminate Q2]|].
  split; [exact Q1|].
  destruct (find_op CtrS.FD3DIR_ID (s_ops st)) as [[|? ?]|] eqn:FD; try discriminate Q0.
  destruct (find_op 11%uint63 (s_ops st)) as [[|? ?]|] eqn:FZ; try discriminate Q.
  split; reflexivity.
Qed.

Lemma aread_dir_pre_facts : forall E st ms mo,
  st_ok bsegs OPS E st ms mo -> aread_dir_pre CFG_ASAN st = true ->
  AP.getr (ms_regs ms) (reg_of_r5 X10) = Z_to_bv 64 3 /\ AP.getr (ms_regs ms) (reg_of_r5 X11) = Z_to_bv 64 STAGE /\ zsh_holds (ms_mem ms)
  /\ m_fds mo = (Ops.Ops.fd3, FdDir) :: Ops.Ops.FDS0.
Proof.
  intros E st ms mo HS H. destruct (aread_dir_pre_inv st H) as (A0 & A1 & _ & _ & _ & F4 & FZ).
  unfold CtrS.is_lit in A0, A1. apply sv_eqb_eq in A0. apply sv_eqb_eq in A1.
  split; [rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X10), A0; reflexivity|].
  split; [rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X11), A1; reflexivity|].
  pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (find_op_In _ _ _ FZ)) as HO. cbn [op_id op_args map] in HO.
  split; [exact (OPS_holds_zsh _ _ HO)|].
  pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (find_op_In _ _ _ F4)) as HO4. cbn [op_id op_args map] in HO4.
  apply OPS_holds_fd3dir in HO4. exact HO4.
Qed.

Lemma aread_dir_apply_shape : forall st sts, aread_dir_apply CFG_ASAN st = Some sts ->
  exists r hargs wnl st1 stE, acall_pre ASTACK None st = Some (r, hargs, wnl, st1) /\ aread_dir_pre CFG_ASAN st = true
    /\ errno_havoc (setr (clobber st1) X10 MINUS1) = Some stE /\ sts = [setpc stE r].
Proof.
  intros st sts H. unfold aread_dir_apply in H.
  destruct (acall_pre ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:P; [|discriminate H].
  destruct (aread_dir_pre CFG_ASAN st) eqn:B; [|discriminate H].
  destruct (errno_havoc (setr (clobber st1) X10 MINUS1)) as [stE|] eqn:HV; [|discriminate H].
  injection H as <-. exists r, hargs, wnl, st1, stE. split; [reflexivity|]. split; [reflexivity|]. split; [exact HV| reflexivity].
Qed.

Definition aread_dir_leaf : Prop :=
  forall st (K : TSet) E ms mo r hargs wnl st1 stE (cnt : Z) (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word)
         (junk : list byte) (errv : word),
  st_ok bsegs OPS E st ms mo -> MP mo -> PB (eb E) ->
  (forall E' ms' mo', env_ext (s_next st) E E' -> MP mo' -> st_ok bsegs OPS E' (setpc stE r) ms' mo' -> realizes bsegs (mkCfg ms' mo') K) ->
  acall_pre ASTACK None st = Some (r, hargs, wnl, st1) -> aread_dir_pre CFG_ASAN st = true ->
  errno_havoc (setr (clobber st1) X10 MINUS1) = Some stE ->
  bv_unsigned (den E (Step.getr st X12)) = cnt -> 0 < cnt <= 65536 ->
  call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) ->
  let R := ms_regs ms in
  ATOP + 4096 <= CtrPre.TwinB.sp_lo E st -> CtrPre.TwinB.sp_lo E st <= bv_unsigned (AP.getr R 2) - 4096 -> bv_unsigned (AP.getr R 2) < 2 ^ 47 ->
  AP.getr R 4 = Z_to_bv 64 ATP -> ALib.Mem.mem_inv bsegs (ms_mem ms) ->
  AS.rw_cells bsegs (ms_mem ms) STAGE [CB (Z.to_nat cnt) junk] -> AS.rw_cells bsegs (ms_mem ms) ERRNO [C4 errv] ->
  zsh_holds (ms_mem ms) ->
  forall ms' mo',
  IR.read_i_post RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
     (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
     (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) STAGE (Z.to_nat cnt) junk errv (CtrPre.TwinB.sp_lo E st) (ms_mem ms)
     (RdErr EISDIR) RNG ms' ->
  MP mo' -> op_minv OPS mo' -> OTHER mo mo' -> ACCT aw L RNG sta LBa mo' ->
  realizes bsegs (mkCfg ms' mo') K.

Theorem aread_dir_sound_of_leaf : aread_dir_leaf ->
  forall pc, to_Z pc = READ_SYM -> contract_sound bsegs OPS MP PB (aread_dir_c CFG_ASAN pc).
Proof.
  intros LEAF pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc aread_dir_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = READ_SYM) by (rewrite Hspc; exact Hpc).
  destruct (aread_dir_apply_shape st sts Happ) as (r & hargs & wnl & st1 & stE & PRE & RPRE & HAV & ->).
  destruct (CtrPre.TwinB.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT.
  destruct (aread_dir_pre_facts E st ms mo HS RPRE) as (A0E & A1E & ZSH & FDS).
  destruct (aread_dir_pre_inv st RPRE) as (_ & _ & _ & [w HW] & _ & F4 & _).

  set (R := ms_regs ms) in *. set (cnt := bv_unsigned (den E (Step.getr st X12))) in *.
  assert (WR : 0 < cnt <= 65536).
  { destruct (want_ok_inv _ _ HW) as [X12E WR0]. unfold cnt. rewrite X12E. cbn [den]. rewrite wbv_unsigned. exact WR0. }
  assert (A2E : AP.getr R (reg_of_r5 X12) = Z_to_bv 64 cnt).
  { unfold R. rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X12). unfold cnt. symmetry. apply Z_to_bv_bv_unsigned. }

  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (A0 & moc & MR & MINV & HH & TW).
  pose proof (ACCT_rng_aimg _ _ _ _ _ _ AC) as RIMG. pose proof (ACCT_rng_aimg_sh _ _ _ _ _ _ AC) as RISH.
  cbn [twfA] in TW. destruct TW as [ACC LEAFC].
  pose proof atop_range as ATR.

  destruct (stage_chunk (ms_mem ms) (Z.to_nat cnt) ltac:(lia)) as [junk STG].
  destruct (errno_chunk (ms_mem ms)) as [errv ERR].
  assert (EB : bv_unsigned (AP.getr R (reg_of_r5 X11)) = STAGE) by (rewrite A1E; vm_compute; reflexivity).
  assert (ETP : bv_unsigned (AP.getr R 4) + -164 = ERRNO) by (rewrite TP; vm_compute; reflexivity).
  assert (TPU : bv_unsigned (AP.getr R 4) = 0x60ee40) by (rewrite TP; vm_compute; reflexivity).
  assert (SH1 : shad RLO2 = ZSH_LO) by (vm_compute; reflexivity). assert (SH2 : shad RHI2 = ZSH_HI) by (vm_compute; reflexivity).
  assert (EV : implA bsegs RNG (enode (NRead 3 (bv_unsigned (AP.getr R (reg_of_r5 X11))) cnt) (dec_read (bv_unsigned (AP.getr R (reg_of_r5 X11))) cnt))
            (epostF (IR.read_i_post RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (bv_unsigned (AP.getr R (reg_of_r5 X11))) (Z.to_nat cnt) junk errv
               (CtrPre.TwinB.sp_lo E st) (ms_mem ms)))
            (MS (mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31))
                (ms_fregs ms) (Z_to_bv 64 0x4fb88) (ms_fcsr ms) None (ms_mem ms) (seg_rom bsegs))).
  { unfold artcells in RT. decompose [and] RT. clear RT.
    eapply (IR.read_i_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_fregs ms) (ms_fcsr ms) (ms_mem ms)
              (CtrPre.TwinB.sp_lo E st) 3 cnt junk errv RLO2 RHI2).
    all: rewrite ?EB, ?ETP, ?SH1, ?SH2.
    all: try lazymatch goal with
         | |- ALib.Mem.mem_inv _ _ => exact MI
         | |- stk _ _ _ _ => exact ST
         | |- AS.rw_cells _ _ STAGE _ => exact STG
         | |- AS.rw_cells _ _ ERRNO _ => exact ERR
         | |- AS.rw_cells _ _ _ _ => assumption
         | |- Shadow.unpoisoned _ _ _ => apply (zsh_unpoisoned _ _ ZSH); lia
         | |- ALib.Mem.wr_at _ _ _ _ => rewrite <- SH1, <- SH2; exact (zsh_wr _ ZSH)
         | |- rng_aimg _ => exact RIMG
         | |- rng _ (CtrPre.TwinB.sp_lo _ _) _ => exact RSTK
         | |- rng _ ZSH_LO _ => eapply rng_sub'; [exact RISH| unfold ZSH_LO, ZSH_HI; lia]
         | |- rng _ _ _ => eapply rng_sub'; [exact RIMG| unfold STAGE, ERRNO, AIMG_HI in *; lia]
         | |- @eq word _ _ => first [exact A0E | exact A2E]
         | |- Shadow.app_blk _ _ => unfold Shadow.app_blk, Shadow.KLOW, Shadow.KHIGH, Shadow.KEND, STAGE; lia
         end.
    all: try (unfold STAGE, ERRNO, RLO2, RHI2, Shadow.KHIGH, Shadow.KEND in *; lia).
    all: match goal with |- ?G => idtac "REMW" G end. }
  rewrite EB in EV.
  pose proof (mrel_fds _ _ _ MR) as FDE.
  rewrite Ems, HPC. apply (GlueA.TwinB.realizes_to_mkRA bsegs).
  eapply (implA_twfA_realizes_silent bsegs NMAXt (enode (NRead 3 STAGE cnt) (dec_read STAGE cnt)) RNG A0
            (IR.read_i_post RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) STAGE (Z.to_nat cnt) junk errv (CtrPre.TwinB.sp_lo E st) (ms_mem ms))
            (fun a RNG' A' moc' => a = RdErr EISDIR /\ RNG' = RNG /\ A' = A0 /\ moc' = moc)
            _ moc mo K).
  - exact EV.
  - apply (twfA_read_dir NMAXt RNG A0 moc 3 STAGE cnt).
    + exact ACC.
    + apply (NodesA.fd_inv_dir3 moc); rewrite <- FDE, FDS; reflexivity.
    + rewrite <- FDE, FDS. reflexivity.
    + subst cnt. lia.
    + repeat split; reflexivity.
  - exact HH.
  - exact MINV.
  - exact MR.
  - intros a RNG' A' ms' moc' mo' HQ (-> & -> & -> & ->) ACC' HH' MINV' MR'.
    destruct (LEAFC _ MR') as (MP' & MI' & OT' & AC').
    exact (LEAF st K E ms mo r hargs wnl st1 stE cnt L RNG sta LBa aw junk errv HS HMP HPB
             (fun E' ms'' mo'' EXT MP'' HS'' => HK _ (or_introl eq_refl) E' ms'' mo'' EXT MP'' HS'')
             PRE RPRE HAV eq_refl WR CP FS CF AH BOT LO SPT TP MI STG ERR ZSH ms' mo' HQ MP' MI' OT' AC').
Qed.
End Sound.
End TwinB.
