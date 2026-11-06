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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import StackSh RangeC MemsetC MemsetPre RangePre.
Unset Nia Cache. Unset Nra Cache.
Import CtrFX ActrA MemsetC.
Module IM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy.I_memset.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Definition MEMSET_SYM : Z := 0x5d2e0.
Definition ASAN_MEMSET_SYM : Z := 0x5d0a0.

Definition memset_walk_stmt {rc : runConstT} (SYM : Z) : Prop :=
  forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (junk : list byte) (RLO2 RHI2 : Z),
  ALib.Mem.mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2224)%Z -> (Shadow.KHIGH <= lo)%Z ->
  rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
  ALib.Step.rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  (bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  Shadow.app_blk (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
  Shadow.unpoisoned m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
  (bv_unsigned a2 <= 2^40)%Z ->
  (RLO2 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= Shadow.KEND)%Z ->
  ALib.Mem.wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (bv_unsigned a0) (bv_unsigned a2) ->
  rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
  evtF asegs RNG (IM.memset_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SYM) fc None m (seg_rom asegs)).

Lemma memset_walk_i {rc : runConstT} : memset_walk_stmt MEMSET_SYM.
Proof. exact IM.memset_i_spec. Qed.

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

Lemma amemset_apply_shape : forall st sts, amemset_apply asegs st = Some sts ->
  exists r hargs wnl st1 kd od c n cls,
    acall_pre ASTACK None st = Some (r, hargs, wnl, st1) /\ getr st X10 = VP kd od /\ getr st X11 = VL c /\ getr st X12 = VL n
    /\ wt n = false /\ 1 <= to_Z (wl n) <= 4096 /\ RangeC.range_class asegs st wnl kd od (wl n) true = Some cls
    /\ set_bytes_post asegs r kd od (PrimInt63.land (wl c) 255%uint63) (wl n) (setpc (setr (clobber st1) X10 (VP kd od)) r) = Some sts.
Proof.
  intros st sts H. unfold amemset_apply in H.
  destruct (acall_pre ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:P; [|discriminate H].
  destruct (getr st X10) as [| | | | | | | | | |] eqn:G10; try discriminate H.
  all: destruct (getr st X11) eqn:G11; try discriminate H.
  all: destruct (getr st X12) eqn:G12; try discriminate H.
  all: cbv zeta in H; match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:CND; [|discriminate H] end.
  all: repeat match type of CND with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in CND as [CND X] end.
  all: apply negb_true_iff in CND; apply Uint63.leb_spec in Q1; apply Uint63.leb_spec in Q0; change (to_Z 1%uint63) with 1 in Q1; change (to_Z NMAX) with 4096 in Q0.
  all: match type of Q with match ?rcx with _ => _ end = true => destruct rcx as [cls|] eqn:RC; [|discriminate Q] end.
  all: do 9 eexists; repeat split; try reflexivity; try eassumption; lia.
Qed.

Lemma known_leu_sound_s : forall E st ms model a b, st_ok asegs OPS E st ms model ->
  known_leu (s_facts st) a b = true -> bv_unsigned (den E a) <= bv_unsigned (den E b).
Proof.
  intros E st ms model a b HS H. unfold known_leu, dec_false in H.
  destruct (decide_ltu (s_facts st) b a) as [[|]|] eqn:Hd; try discriminate H.
  pose proof (ValP.decide_ltu_sound E (s_facts st) (so_facts _ _ _ _ _ _ HS) b a false Hd) as X.
  apply (proj1 (ValP.ltu_iff _ _ false)) in X. exact X.
Qed.

Definition amemset_leaf : Prop :=
  forall st sts (K : TSet) E ms mo r hargs wnl st1 kd od c n (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word),
  st_ok asegs OPS E st ms mo -> PB (eb E) ->
  (forall st', In st' sts -> forall E' ms' mo', env_ext (s_next st) E E' -> MP mo' -> st_ok asegs OPS E' st' ms' mo' ->
               realizes asegs (mkCfg ms' mo') K) ->
  acall_pre ASTACK None st = Some (r, hargs, wnl, st1) -> getr st X10 = VP kd od -> getr st X11 = VL c -> getr st X12 = VL n ->
  wt n = false -> 1 <= to_Z (wl n) <= 4096 ->
  set_bytes_post asegs r kd od (PrimInt63.land (wl c) 255%uint63) (wl n) (setpc (setr (clobber st1) X10 (VP kd od)) r) = Some sts ->
  call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) -> ALib.Mem.mem_inv asegs (ms_mem ms) ->
  let R := ms_regs ms in
  ATOP + 4096 <= CtrPre.sp_lo E st -> CtrPre.sp_lo E st <= bv_unsigned (AP.getr R 2) - 4096 -> bv_unsigned (AP.getr R 2) < 2 ^ 47 ->
  let A0 := bv_unsigned (ev E kd) + w2Zs od in
  AIMG_HI <= A0 -> A0 + to_Z (wl n) + 8 <= 2 ^ 47 -> (A0 + to_Z (wl n) <= ATOP \/ bv_unsigned (AP.getr R 2) <= A0) ->
  bv_unsigned (AP.getr R 10) = A0 -> bv_unsigned (AP.getr R 12) = to_Z (wl n) -> AP.getr R 11 = wbv c ->
  forall ms' mo',
  IM.memset_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
     (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
     (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (CtrPre.sp_lo E st) (ms_mem ms) ms' ->
  MP mo' -> op_minv OPS mo' -> OTHER mo mo' -> ACCT aw L RNG sta LBa mo' ->
  realizes asegs (mkCfg ms' mo') K.

Theorem amemset_sound_of_leaf : amemset_leaf ->
  forall pc, to_Z pc = SYM -> contract_sound asegs OPS MP PB (amemset_c asegs pc).
Proof.
  intros LEAF pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc amemset_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = SYM) by (rewrite Hspc; exact Hpc).
  destruct (amemset_apply_shape st sts Happ) as (r & hargs & wnl & st1 & kd & od & c & n & cls & PRE & G10 & G11 & G12 & WTN & NR & RCL & SB).
  destruct (CtrPre.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT.
  set (R := ms_regs ms) in *. set (len := to_Z (wl n)) in *.

  destruct (range_class_facts_ev AI ACCT UNIV Cw OPS AI_fake Cw_sub_ghost OPS_holds_ssh ACCT_rng ACCT_rng_stk_sh ACCT_frng W_PAT E st ms mo r hargs wnl L RNG sta LBa aw
              kd od (wl n) true cls HS CF AH AC BOT LO SPT RCL NR) as (DEN & LOWA & HI47 & POS & _ & DSTW & APB & UNP & RNGD & RLO2 & RHI2 & HULL & WRH & RNGH).
  destruct (DSTW eq_refl) as (junk & DST). fold len in HI47, POS, DST, APB, UNP, RNGD, HULL.
  set (A0 := bv_unsigned (ev E kd) + w2Zs od) in *.
  pose proof atop_range as ATR.

  assert (EA0 : bv_unsigned (AP.getr R (reg_of_r5 X10)) = A0).
  { unfold R. rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X10), G10. exact DEN. }
  assert (EA2 : bv_unsigned (AP.getr R (reg_of_r5 X12)) = len).
  { unfold R. rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X12), G12. cbn [den]. rewrite wbv_unsigned. unfold w2Z. rewrite WTN. unfold len. lia. }
  assert (EA1 : AP.getr R (reg_of_r5 X11) = wbv c) by (unfold R; rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X11), G11; reflexivity).
  idtac "MS-1".
  assert (EA0' : bv_unsigned (AP.getr R 10) = A0) by exact EA0. assert (EA2' : bv_unsigned (AP.getr R 12) = len) by exact EA2.
  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  pose proof (ACCT_rng_aimg _ _ _ _ _ _ AC) as RIMG.
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
    all: try (destruct POS as [P|P]; [left; lia | right; exact P]).
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
    exact (LEAF st sts K E ms mo r hargs wnl st1 kd od c n L RNG sta LBa aw HS HPB HK PRE G10 G11 G12 WTN NR SB CP FS CF AH MI BOT LO SPT
             LOWA HI47 POS EA0 EA2 EA1 ms' mo' HQ HMP' HMI' OTH ACP).
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
Import StackSh.TwinB RangeC.TwinB MemsetC.TwinB MemsetPre.TwinB RangePre.TwinB.
Unset Nia Cache. Unset Nra Cache.
Import CtrFX ActrA MemsetC.TwinB.MemsetC.
Module IM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy.TwinB.I_memset.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Definition MEMSET_SYM : Z := 0x5dc70.
Definition ASAN_MEMSET_SYM : Z := 0x5da30.

Definition memset_walk_stmt {rc : runConstT} (SYM : Z) : Prop :=
  forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (junk : list byte) (RLO2 RHI2 : Z),
  ALib.Mem.mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2224)%Z -> (Shadow.KHIGH <= lo)%Z ->
  rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
  ALib.Step.rw_cells bsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  (bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  Shadow.app_blk (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
  Shadow.unpoisoned m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
  (bv_unsigned a2 <= 2^40)%Z ->
  (RLO2 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= Shadow.KEND)%Z ->
  ALib.Mem.wr_at bsegs m (shad RLO2) (shad RHI2 - shad RLO2) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (bv_unsigned a0) (bv_unsigned a2) ->
  rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
  evtF bsegs RNG (IM.memset_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SYM) fc None m (seg_rom bsegs)).

Lemma memset_walk_i {rc : runConstT} : memset_walk_stmt MEMSET_SYM.
Proof. exact IM.memset_i_spec. Qed.

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

Lemma amemset_apply_shape : forall st sts, amemset_apply bsegs st = Some sts ->
  exists r hargs wnl st1 kd od c n cls,
    acall_pre ASTACK None st = Some (r, hargs, wnl, st1) /\ getr st X10 = VP kd od /\ getr st X11 = VL c /\ getr st X12 = VL n
    /\ wt n = false /\ 1 <= to_Z (wl n) <= 4096 /\ RangeC.TwinB.RangeC.range_class bsegs st wnl kd od (wl n) true = Some cls
    /\ set_bytes_post bsegs r kd od (PrimInt63.land (wl c) 255%uint63) (wl n) (setpc (setr (clobber st1) X10 (VP kd od)) r) = Some sts.
Proof.
  intros st sts H. unfold amemset_apply in H.
  destruct (acall_pre ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:P; [|discriminate H].
  destruct (getr st X10) as [| | | | | | | | | |] eqn:G10; try discriminate H.
  all: destruct (getr st X11) eqn:G11; try discriminate H.
  all: destruct (getr st X12) eqn:G12; try discriminate H.
  all: cbv zeta in H; match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:CND; [|discriminate H] end.
  all: repeat match type of CND with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in CND as [CND X] end.
  all: apply negb_true_iff in CND; apply Uint63.leb_spec in Q1; apply Uint63.leb_spec in Q0; change (to_Z 1%uint63) with 1 in Q1; change (to_Z NMAX) with 4096 in Q0.
  all: match type of Q with match ?rcx with _ => _ end = true => destruct rcx as [cls|] eqn:RC; [|discriminate Q] end.
  all: do 9 eexists; repeat split; try reflexivity; try eassumption; lia.
Qed.

Lemma known_leu_sound_s : forall E st ms model a b, st_ok bsegs OPS E st ms model ->
  known_leu (s_facts st) a b = true -> bv_unsigned (den E a) <= bv_unsigned (den E b).
Proof.
  intros E st ms model a b HS H. unfold known_leu, dec_false in H.
  destruct (decide_ltu (s_facts st) b a) as [[|]|] eqn:Hd; try discriminate H.
  pose proof (ValP.decide_ltu_sound E (s_facts st) (so_facts _ _ _ _ _ _ HS) b a false Hd) as X.
  apply (proj1 (ValP.ltu_iff _ _ false)) in X. exact X.
Qed.

Definition amemset_leaf : Prop :=
  forall st sts (K : TSet) E ms mo r hargs wnl st1 kd od c n (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word),
  st_ok bsegs OPS E st ms mo -> PB (eb E) ->
  (forall st', In st' sts -> forall E' ms' mo', env_ext (s_next st) E E' -> MP mo' -> st_ok bsegs OPS E' st' ms' mo' ->
               realizes bsegs (mkCfg ms' mo') K) ->
  acall_pre ASTACK None st = Some (r, hargs, wnl, st1) -> getr st X10 = VP kd od -> getr st X11 = VL c -> getr st X12 = VL n ->
  wt n = false -> 1 <= to_Z (wl n) <= 4096 ->
  set_bytes_post bsegs r kd od (PrimInt63.land (wl c) 255%uint63) (wl n) (setpc (setr (clobber st1) X10 (VP kd od)) r) = Some sts ->
  call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) -> ALib.Mem.mem_inv bsegs (ms_mem ms) ->
  let R := ms_regs ms in
  ATOP + 4096 <= CtrPre.TwinB.sp_lo E st -> CtrPre.TwinB.sp_lo E st <= bv_unsigned (AP.getr R 2) - 4096 -> bv_unsigned (AP.getr R 2) < 2 ^ 47 ->
  let A0 := bv_unsigned (ev E kd) + w2Zs od in
  AIMG_HI <= A0 -> A0 + to_Z (wl n) + 8 <= 2 ^ 47 -> (A0 + to_Z (wl n) <= ATOP \/ bv_unsigned (AP.getr R 2) <= A0) ->
  bv_unsigned (AP.getr R 10) = A0 -> bv_unsigned (AP.getr R 12) = to_Z (wl n) -> AP.getr R 11 = wbv c ->
  forall ms' mo',
  IM.memset_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
     (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
     (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (CtrPre.TwinB.sp_lo E st) (ms_mem ms) ms' ->
  MP mo' -> op_minv OPS mo' -> OTHER mo mo' -> ACCT aw L RNG sta LBa mo' ->
  realizes bsegs (mkCfg ms' mo') K.

Theorem amemset_sound_of_leaf : amemset_leaf ->
  forall pc, to_Z pc = SYM -> contract_sound bsegs OPS MP PB (amemset_c bsegs pc).
Proof.
  intros LEAF pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc amemset_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = SYM) by (rewrite Hspc; exact Hpc).
  destruct (amemset_apply_shape st sts Happ) as (r & hargs & wnl & st1 & kd & od & c & n & cls & PRE & G10 & G11 & G12 & WTN & NR & RCL & SB).
  destruct (CtrPre.TwinB.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT.
  set (R := ms_regs ms) in *. set (len := to_Z (wl n)) in *.

  destruct (range_class_facts_ev AI ACCT UNIV Cw OPS AI_fake Cw_sub_ghost OPS_holds_ssh ACCT_rng ACCT_rng_stk_sh ACCT_frng W_PAT E st ms mo r hargs wnl L RNG sta LBa aw
              kd od (wl n) true cls HS CF AH AC BOT LO SPT RCL NR) as (DEN & LOWA & HI47 & POS & _ & DSTW & APB & UNP & RNGD & RLO2 & RHI2 & HULL & WRH & RNGH).
  destruct (DSTW eq_refl) as (junk & DST). fold len in HI47, POS, DST, APB, UNP, RNGD, HULL.
  set (A0 := bv_unsigned (ev E kd) + w2Zs od) in *.
  pose proof atop_range as ATR.

  assert (EA0 : bv_unsigned (AP.getr R (reg_of_r5 X10)) = A0).
  { unfold R. rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X10), G10. exact DEN. }
  assert (EA2 : bv_unsigned (AP.getr R (reg_of_r5 X12)) = len).
  { unfold R. rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X12), G12. cbn [den]. rewrite wbv_unsigned. unfold w2Z. rewrite WTN. unfold len. lia. }
  assert (EA1 : AP.getr R (reg_of_r5 X11) = wbv c) by (unfold R; rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X11), G11; reflexivity).
  idtac "MS-1".
  assert (EA0' : bv_unsigned (AP.getr R 10) = A0) by exact EA0. assert (EA2' : bv_unsigned (AP.getr R 12) = len) by exact EA2.
  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  pose proof (ACCT_rng_aimg _ _ _ _ _ _ AC) as RIMG.
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
    all: try (destruct POS as [P|P]; [left; lia | right; exact P]).
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
    exact (LEAF st sts K E ms mo r hargs wnl st1 kd od c n L RNG sta LBa aw HS HPB HK PRE G10 G11 G12 WTN NR SB CP FS CF AH MI BOT LO SPT
             LOWA HI47 POS EA0 EA2 EA1 ms' mo' HQ HMP' HMI' OTH ACP).
Qed.
End Sound.
End TwinB.
