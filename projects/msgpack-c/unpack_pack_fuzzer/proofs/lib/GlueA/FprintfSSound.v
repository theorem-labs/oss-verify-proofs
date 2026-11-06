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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import StackSh HalfC VprintfC VprintfSound FprintfC FprintfSound StrRegC FprintfSC MemsetPre RangePre StrReg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require InitLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggPre.
Unset Nia Cache. Unset Nra Cache.
Import CtrFX ActrA VprintfC FprintfC StrRegC FprintfSC.
Module IPI := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_printf_icpt.
Module IPF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_printf_formats.
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
Hypothesis OPS_holds_zro : forall m mo, op_holds OPS ZRO_ID [] m mo -> zro_holds m.
Hypothesis OPS_holds_zarg : forall az m mo, op_holds OPS ZARG_ID [az] m mo -> zarg_holds az m.
Variable OTHER : Model -> Model -> Prop.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Hypothesis PB_str : forall b, PB b -> forall j js, legal_str j js ->
  exists s : list byte, b j = s ++ [Z_to_bv 8 0] /\ Forall (fun x : byte => bv_unsigned x <> 0) s
    /\ b js = Z_to_le_bytes 8 (Z.of_nat (length s) + 1) /\ Z.of_nat (length s) <= 131071.
Variable NMAXt : nat.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Hypothesis ACCT_rng_aimg_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG 0x7fffa000 0xc4000.
Hypothesis ACCT_rng_stk_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (shad ATOP) (Shadow.KHIGH - shad ATOP).
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent ACCT OPS OTHER MP mo aw L st LBa).

Lemma str_ok_facts_at : forall (x : r5) E st ms mo r hargs wnl (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word) j js,
  st_ok asegs OPS E st ms mo -> PB (eb E) -> legal_str j js ->
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw -> ACCT aw L RNG sta LBa mo ->
  let sp := bv_unsigned (AP.getr (ms_regs ms) 2) in
  ATOP + 4096 <= CtrPre.sp_lo E st -> CtrPre.sp_lo E st <= sp - 4096 -> sp < 2 ^ 47 ->
  str_ok_at x st wnl j js = true ->
  exists (k : int) (rr : region) (sstr : list byte) (RLO RHI : Z),
    let Sa := bv_unsigned (AP.getr (ms_regs ms) (reg_of_r5 x)) in let NS := Z.of_nat (length sstr) + 1 in
    (getr st x = VP k wzero /\ IMap.find k (s_regs st) = Some rr /\ str_region rr j js = true /\ k <> 0%uint63
     /\ eb E j = sstr ++ [Z_to_bv 8 0] /\ hiZ E rr = NS /\ Sa = bv_unsigned (ev E k))
    /\ ALib.Mem.bytes_at asegs (ms_mem ms) Sa (sstr ++ [Z_to_bv 8 0]) /\ Forall (fun b : byte => bv_unsigned b <> 0) sstr
    /\ sp <= Sa /\ Shadow.app_blk Sa (Sa + NS) /\ 0 < Sa /\ Shadow.unpoisoned (ms_mem ms) Sa (Sa + NS) /\ NS <= 2 ^ 40
    /\ (RLO <= Sa /\ Sa + NS <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= Shadow.KEND)
    /\ ALib.Mem.wr_at asegs (ms_mem ms) (shad RLO) (shad RHI - shad RLO)
    /\ rng RNG Sa NS /\ rng RNG (shad RLO) (shad RHI - shad RLO).
Proof.
  intros x E st ms mo r hargs wnl L RNG sta LBa aw j js HS HPB LEG CF AC sp BOT LO SPT H.
  unfold str_ok_at in H.
  destruct (getr st x) as [|k o| | | | | | | | |] eqn:G12; try discriminate H.
  destruct (IMap.find k (s_regs st)) as [rr|] eqn:Hk; [|discriminate H].
  apply andb_prop in H as [H SRO]. apply ValP.weqb_eq in H. subst o.
  destruct (str_reg_ok_shape st wnl k rr j js SRO) as (az & FZ & Q4 & SRG & Q3 & S2 & RH & RB & RC & WLK & _ & _ & _).

  destruct (PB_str (eb E) HPB j js LEG) as (s & Bj & NOZ & Bjs & LEN).
  assert (HIZ : hiZ E rr = Z.of_nat (length s) + 1).
  { unfold hiZ. rewrite RH. cbn [den]. rewrite Bjs. change (bv_unsigned (wbv wzero)) with 0. change (to_Z 8%uint63) with 8.
    rewrite InitLib.InitLib.bytes_val_le8 by lia. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). lia. }
  set (NS := Z.of_nat (length s) + 1) in *.
  destruct (str_reg_facts AI ACCT UNIV Cw OPS OPS_holds_zarg ACCT_rng ACCT_rng_stk_sh E st ms mo r hargs wnl L RNG sta LBa aw k rr j js 0 NS HS CF AC BOT LO SPT Hk SRO
              ltac:(lia) ltac:(unfold NS; lia) ltac:(rewrite HIZ; lia)) as (RLO & RHI & _ & BYT & REST).
  rewrite Z.add_0_r in BYT, REST.
  rewrite (slice_all (eb E j) (Z.to_nat NS) (Z_to_bv 8 0)) in BYT by (rewrite Bj, length_app; cbn [length]; unfold NS; lia).
  rewrite Bj in BYT.
  set (Sa := bv_unsigned (ev E k)) in *.
  assert (EA2 : bv_unsigned (AP.getr (ms_regs ms) (reg_of_r5 x)) = Sa).
  { rewrite (GlueA.getr_RA asegs OPS E st ms mo HS x), G12.
    rewrite ValP.den_VP. change (w2Zs wzero) with 0. rewrite Z.add_0_r. apply Z.mod_small. pose proof (bv_unsigned_in_range _ (ev E k)) as RR.
    unfold bv_modulus in RR. unfold two64. fold Sa in RR |- *. change (2 ^ Z.of_N 64) with (2 ^ 64) in RR. lia. }
  exists k, rr, s, RLO, RHI. cbv zeta. rewrite EA2.
  split; [split; [first [reflexivity| exact G12]|]; split; [first [reflexivity| exact Hk]|]; split; [exact SRG|]; split; [intros ->; discriminate Q4|]; split; [exact Bj|]; split; [exact HIZ| reflexivity]|].
  destruct REST as (SPA & APB & SPOS & UNP & HULL & WRH & RNGS & RNGH).
  split; [exact BYT|]. split; [exact NOZ|]. split; [exact SPA|]. split; [exact APB|]. split; [exact SPOS|]. split; [exact UNP|].
  split; [unfold NS; lia|]. split; [exact HULL|]. split; [exact WRH|]. split; [exact RNGS| exact RNGH].
Qed.

Lemma str_ok_facts : forall E st ms mo r hargs wnl (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word) j js,
  st_ok asegs OPS E st ms mo -> PB (eb E) -> legal_str j js ->
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw -> ACCT aw L RNG sta LBa mo ->
  let sp := bv_unsigned (AP.getr (ms_regs ms) 2) in
  ATOP + 4096 <= CtrPre.sp_lo E st -> CtrPre.sp_lo E st <= sp - 4096 -> sp < 2 ^ 47 ->
  str_ok st wnl j js = true ->
  exists (sstr : list byte) (RLO RHI : Z),
    let Sa := bv_unsigned (AP.getr (ms_regs ms) 12) in let NS := Z.of_nat (length sstr) + 1 in
    ALib.Mem.bytes_at asegs (ms_mem ms) Sa (sstr ++ [Z_to_bv 8 0]) /\ Forall (fun b : byte => bv_unsigned b <> 0) sstr
    /\ sp <= Sa /\ Shadow.app_blk Sa (Sa + NS) /\ 0 < Sa /\ Shadow.unpoisoned (ms_mem ms) Sa (Sa + NS) /\ NS <= 2 ^ 40
    /\ (RLO <= Sa /\ Sa + NS <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= Shadow.KEND)
    /\ ALib.Mem.wr_at asegs (ms_mem ms) (shad RLO) (shad RHI - shad RLO)
    /\ rng RNG Sa NS /\ rng RNG (shad RLO) (shad RHI - shad RLO).
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw j js HS HPB LEG CF AC sp BOT LO SPT H.
  destruct (str_ok_facts_at X12 E st ms mo r hargs wnl L RNG sta LBa aw j js HS HPB LEG CF AC BOT LO SPT H) as (k & rr & sstr & RLO & RHI & _ & REST).
  exists sstr, RLO, RHI. exact REST.
Qed.

Lemma afprintf_s_apply_shape : forall FMT j js st sts, afprintf_s_pre_apply asegs FMT j js st = Some sts ->
  exists r hargs wnl st1, acall_pre ASTACK None st = Some (r, hargs, wnl, st1) /\ str_ok st wnl j js = true
    /\ afprintf_pre_apply asegs FMT st = Some sts.
Proof.
  intros FMT j js st sts H. unfold afprintf_s_pre_apply in H.
  destruct (acall_pre ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:P; [|discriminate H].
  destruct (str_ok st wnl j js) eqn:SO; [|discriminate H]. exists r, hargs, wnl, st1. repeat split; assumption.
Qed.

Theorem afprintf_s_sound_of_leaf : forall (A n : Z) (FMT : w64) (j js : int),
  wbv FMT = Z_to_bv 64 A -> 0x10040 <= A -> 0 <= n -> A + n + 64 <= 0x22c60 -> legal_str j js ->
  IPI.fprintf_i_pre_s_stmt A n ->
  FprintfSound.afprintf_leaf AI ACCT UNIV Cw OPS OTHER MP PB ->
  forall pc, to_Z pc = FPRINTF_SYM -> contract_sound asegs OPS MP PB (afprintf_s_pre_c asegs FMT j js pc).
Proof.
  intros A n FMT j js HFMT A0 N0 AN LEG WALK LEAF pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc afprintf_s_pre_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = FPRINTF_SYM) by (rewrite Hspc; exact Hpc).
  destruct (afprintf_s_apply_shape _ _ _ st sts Happ) as (r0 & hargs0 & wnl0 & st10 & PRE0 & SOK & Happ').
  destruct (afprintf_apply_shape _ st sts Happ') as (r & hargs & wnl & st1 & st3 & PRE & G11 & FZ & PUSH & ->).
  rewrite PRE in PRE0. injection PRE0 as <- <- <- <-.
  destruct (CtrPre.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT.
  set (R := ms_regs ms) in *.
  pose proof atop_range as ATR.
  pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (UnreggPre.find_op_In _ _ _ FZ)) as HO. cbn [op_id op_args map] in HO.
  pose proof (OPS_holds_zro _ _ HO) as ZRO.
  assert (EA1 : AP.getr R 11 = Z_to_bv 64 A).
  { change (AP.getr R 11) with (AP.getr R (reg_of_r5 X11)). unfold R. rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X11), G11. exact HFMT. }
  destruct (str_ok_facts E st ms mo r hargs wnl L RNG sta LBa aw j js HS HPB LEG CF AC BOT LO SPT SOK)
    as (sstr & RLO & RHI & BYT & NOZ & SPA & APB & SPOS & UNP & NSB & HULL & WRH & RNGS & RNGH).
  fold R in BYT, SPA, APB, SPOS, UNP, HULL, RNGS.
  idtac "SS-1".
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
    eapply (WALK RNG) with (sstr := sstr) (RLO := RLO) (RHI := RHI).
    all: try lazymatch goal with
         | |- ALib.Mem.mem_inv _ _ => exact MI
         | |- stk _ _ _ _ => exact ST
         | |- ALib.Step.rw_cells _ _ _ _ => assumption
         | |- Shadow.shadow_bytes _ _ _ _ => apply (zro_shadow_bytes _ _ _ ZRO); lia
         | |- ALib.Mem.bytes_at _ _ _ _ => exact BYT
         | |- Forall _ _ => exact NOZ
         | |- Shadow.app_blk _ _ => exact APB
         | |- Shadow.unpoisoned _ _ _ => exact UNP
         | |- ALib.Mem.wr_at _ _ _ _ => exact WRH
         | |- rng_aimg _ => exact RIMG
         | |- AP.getr _ _ = _ => exact EA1
         | |- rng _ (shad _) _ => first [ exact RNGH | apply (rng_sub _ _ _ _ _ RSH); unfold shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia ]
         | |- rng _ _ _ => first [exact RNGS | exact RSTK]
         | |- _ <= _ /\ _ => exact HULL
         | |- _ \/ _ => right; exact SPA
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
Import StackSh.TwinB HalfC.TwinB VprintfC.TwinB VprintfSound.TwinB FprintfC.TwinB FprintfSound.TwinB StrRegC.TwinB FprintfSC.TwinB MemsetPre.TwinB RangePre.TwinB StrReg.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import CtrFX ActrA VprintfC.TwinB.VprintfC FprintfC.TwinB.FprintfC StrRegC.TwinB.StrRegC FprintfSC.TwinB.FprintfSC.
Module IPI := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_printf_icpt.TwinB.
Module IPF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_printf_formats.TwinB.
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
Hypothesis OPS_holds_zro : forall m mo, op_holds OPS ZRO_ID [] m mo -> zro_holds m.
Hypothesis OPS_holds_zarg : forall az m mo, op_holds OPS ZARG_ID [az] m mo -> zarg_holds az m.
Variable OTHER : Model -> Model -> Prop.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Hypothesis PB_str : forall b, PB b -> forall j js, legal_str j js ->
  exists s : list byte, b j = s ++ [Z_to_bv 8 0] /\ Forall (fun x : byte => bv_unsigned x <> 0) s
    /\ b js = Z_to_le_bytes 8 (Z.of_nat (length s) + 1) /\ Z.of_nat (length s) <= 131071.
Variable NMAXt : nat.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Hypothesis ACCT_rng_aimg_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG 0x7fffa000 0xc5000.
Hypothesis ACCT_rng_stk_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (shad ATOP) (Shadow.KHIGH - shad ATOP).
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent ACCT OPS OTHER MP mo aw L st LBa).

Lemma str_ok_facts_at : forall (x : r5) E st ms mo r hargs wnl (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word) j js,
  st_ok bsegs OPS E st ms mo -> PB (eb E) -> legal_str j js ->
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw -> ACCT aw L RNG sta LBa mo ->
  let sp := bv_unsigned (AP.getr (ms_regs ms) 2) in
  ATOP + 4096 <= CtrPre.TwinB.sp_lo E st -> CtrPre.TwinB.sp_lo E st <= sp - 4096 -> sp < 2 ^ 47 ->
  str_ok_at x st wnl j js = true ->
  exists (k : int) (rr : region) (sstr : list byte) (RLO RHI : Z),
    let Sa := bv_unsigned (AP.getr (ms_regs ms) (reg_of_r5 x)) in let NS := Z.of_nat (length sstr) + 1 in
    (getr st x = VP k wzero /\ IMap.find k (s_regs st) = Some rr /\ str_region rr j js = true /\ k <> 0%uint63
     /\ eb E j = sstr ++ [Z_to_bv 8 0] /\ hiZ E rr = NS /\ Sa = bv_unsigned (ev E k))
    /\ ALib.Mem.bytes_at bsegs (ms_mem ms) Sa (sstr ++ [Z_to_bv 8 0]) /\ Forall (fun b : byte => bv_unsigned b <> 0) sstr
    /\ sp <= Sa /\ Shadow.app_blk Sa (Sa + NS) /\ 0 < Sa /\ Shadow.unpoisoned (ms_mem ms) Sa (Sa + NS) /\ NS <= 2 ^ 40
    /\ (RLO <= Sa /\ Sa + NS <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= Shadow.KEND)
    /\ ALib.Mem.wr_at bsegs (ms_mem ms) (shad RLO) (shad RHI - shad RLO)
    /\ rng RNG Sa NS /\ rng RNG (shad RLO) (shad RHI - shad RLO).
Proof.
  intros x E st ms mo r hargs wnl L RNG sta LBa aw j js HS HPB LEG CF AC sp BOT LO SPT H.
  unfold str_ok_at in H.
  destruct (getr st x) as [|k o| | | | | | | | |] eqn:G12; try discriminate H.
  destruct (IMap.find k (s_regs st)) as [rr|] eqn:Hk; [|discriminate H].
  apply andb_prop in H as [H SRO]. apply ValP.weqb_eq in H. subst o.
  destruct (str_reg_ok_shape st wnl k rr j js SRO) as (az & FZ & Q4 & SRG & Q3 & S2 & RH & RB & RC & WLK & _ & _ & _).

  destruct (PB_str (eb E) HPB j js LEG) as (s & Bj & NOZ & Bjs & LEN).
  assert (HIZ : hiZ E rr = Z.of_nat (length s) + 1).
  { unfold hiZ. rewrite RH. cbn [den]. rewrite Bjs. change (bv_unsigned (wbv wzero)) with 0. change (to_Z 8%uint63) with 8.
    rewrite InitLib.InitLib.bytes_val_le8 by lia. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). lia. }
  set (NS := Z.of_nat (length s) + 1) in *.
  destruct (str_reg_facts AI ACCT UNIV Cw OPS OPS_holds_zarg ACCT_rng ACCT_rng_stk_sh E st ms mo r hargs wnl L RNG sta LBa aw k rr j js 0 NS HS CF AC BOT LO SPT Hk SRO
              ltac:(lia) ltac:(unfold NS; lia) ltac:(rewrite HIZ; lia)) as (RLO & RHI & _ & BYT & REST).
  rewrite Z.add_0_r in BYT, REST.
  rewrite (slice_all (eb E j) (Z.to_nat NS) (Z_to_bv 8 0)) in BYT by (rewrite Bj, length_app; cbn [length]; unfold NS; lia).
  rewrite Bj in BYT.
  set (Sa := bv_unsigned (ev E k)) in *.
  assert (EA2 : bv_unsigned (AP.getr (ms_regs ms) (reg_of_r5 x)) = Sa).
  { rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS x), G12.
    rewrite ValP.den_VP. change (w2Zs wzero) with 0. rewrite Z.add_0_r. apply Z.mod_small. pose proof (bv_unsigned_in_range _ (ev E k)) as RR.
    unfold bv_modulus in RR. unfold two64. fold Sa in RR |- *. change (2 ^ Z.of_N 64) with (2 ^ 64) in RR. lia. }
  exists k, rr, s, RLO, RHI. cbv zeta. rewrite EA2.
  split; [split; [first [reflexivity| exact G12]|]; split; [first [reflexivity| exact Hk]|]; split; [exact SRG|]; split; [intros ->; discriminate Q4|]; split; [exact Bj|]; split; [exact HIZ| reflexivity]|].
  destruct REST as (SPA & APB & SPOS & UNP & HULL & WRH & RNGS & RNGH).
  split; [exact BYT|]. split; [exact NOZ|]. split; [exact SPA|]. split; [exact APB|]. split; [exact SPOS|]. split; [exact UNP|].
  split; [unfold NS; lia|]. split; [exact HULL|]. split; [exact WRH|]. split; [exact RNGS| exact RNGH].
Qed.

Lemma str_ok_facts : forall E st ms mo r hargs wnl (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word) j js,
  st_ok bsegs OPS E st ms mo -> PB (eb E) -> legal_str j js ->
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw -> ACCT aw L RNG sta LBa mo ->
  let sp := bv_unsigned (AP.getr (ms_regs ms) 2) in
  ATOP + 4096 <= CtrPre.TwinB.sp_lo E st -> CtrPre.TwinB.sp_lo E st <= sp - 4096 -> sp < 2 ^ 47 ->
  str_ok st wnl j js = true ->
  exists (sstr : list byte) (RLO RHI : Z),
    let Sa := bv_unsigned (AP.getr (ms_regs ms) 12) in let NS := Z.of_nat (length sstr) + 1 in
    ALib.Mem.bytes_at bsegs (ms_mem ms) Sa (sstr ++ [Z_to_bv 8 0]) /\ Forall (fun b : byte => bv_unsigned b <> 0) sstr
    /\ sp <= Sa /\ Shadow.app_blk Sa (Sa + NS) /\ 0 < Sa /\ Shadow.unpoisoned (ms_mem ms) Sa (Sa + NS) /\ NS <= 2 ^ 40
    /\ (RLO <= Sa /\ Sa + NS <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= Shadow.KEND)
    /\ ALib.Mem.wr_at bsegs (ms_mem ms) (shad RLO) (shad RHI - shad RLO)
    /\ rng RNG Sa NS /\ rng RNG (shad RLO) (shad RHI - shad RLO).
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw j js HS HPB LEG CF AC sp BOT LO SPT H.
  destruct (str_ok_facts_at X12 E st ms mo r hargs wnl L RNG sta LBa aw j js HS HPB LEG CF AC BOT LO SPT H) as (k & rr & sstr & RLO & RHI & _ & REST).
  exists sstr, RLO, RHI. exact REST.
Qed.

Lemma afprintf_s_apply_shape : forall FMT j js st sts, afprintf_s_pre_apply bsegs FMT j js st = Some sts ->
  exists r hargs wnl st1, acall_pre ASTACK None st = Some (r, hargs, wnl, st1) /\ str_ok st wnl j js = true
    /\ afprintf_pre_apply bsegs FMT st = Some sts.
Proof.
  intros FMT j js st sts H. unfold afprintf_s_pre_apply in H.
  destruct (acall_pre ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:P; [|discriminate H].
  destruct (str_ok st wnl j js) eqn:SO; [|discriminate H]. exists r, hargs, wnl, st1. repeat split; assumption.
Qed.

Theorem afprintf_s_sound_of_leaf : forall (A n : Z) (FMT : w64) (j js : int),
  wbv FMT = Z_to_bv 64 A -> 0x10040 <= A -> 0 <= n -> A + n + 64 <= 0x22d00 -> legal_str j js ->
  IPI.fprintf_i_pre_s_stmt A n ->
  FprintfSound.TwinB.afprintf_leaf AI ACCT UNIV Cw OPS OTHER MP PB ->
  forall pc, to_Z pc = FPRINTF_SYM -> contract_sound bsegs OPS MP PB (afprintf_s_pre_c bsegs FMT j js pc).
Proof.
  intros A n FMT j js HFMT A0 N0 AN LEG WALK LEAF pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc afprintf_s_pre_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = FPRINTF_SYM) by (rewrite Hspc; exact Hpc).
  destruct (afprintf_s_apply_shape _ _ _ st sts Happ) as (r0 & hargs0 & wnl0 & st10 & PRE0 & SOK & Happ').
  destruct (afprintf_apply_shape _ st sts Happ') as (r & hargs & wnl & st1 & st3 & PRE & G11 & FZ & PUSH & ->).
  rewrite PRE in PRE0. injection PRE0 as <- <- <- <-.
  destruct (CtrPre.TwinB.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT.
  set (R := ms_regs ms) in *.
  pose proof atop_range as ATR.
  pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (UnreggPre.TwinB.find_op_In _ _ _ FZ)) as HO. cbn [op_id op_args map] in HO.
  pose proof (OPS_holds_zro _ _ HO) as ZRO.
  assert (EA1 : AP.getr R 11 = Z_to_bv 64 A).
  { change (AP.getr R 11) with (AP.getr R (reg_of_r5 X11)). unfold R. rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X11), G11. exact HFMT. }
  destruct (str_ok_facts E st ms mo r hargs wnl L RNG sta LBa aw j js HS HPB LEG CF AC BOT LO SPT SOK)
    as (sstr & RLO & RHI & BYT & NOZ & SPA & APB & SPOS & UNP & NSB & HULL & WRH & RNGS & RNGH).
  fold R in BYT, SPA, APB, SPOS, UNP, HULL, RNGS.
  idtac "SS-1".
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
    eapply (WALK RNG) with (sstr := sstr) (RLO := RLO) (RHI := RHI).
    all: try lazymatch goal with
         | |- ALib.Mem.mem_inv _ _ => exact MI
         | |- stk _ _ _ _ => exact ST
         | |- ALib.Step.rw_cells _ _ _ _ => assumption
         | |- Shadow.shadow_bytes _ _ _ _ => apply (zro_shadow_bytes _ _ _ ZRO); lia
         | |- ALib.Mem.bytes_at _ _ _ _ => exact BYT
         | |- Forall _ _ => exact NOZ
         | |- Shadow.app_blk _ _ => exact APB
         | |- Shadow.unpoisoned _ _ _ => exact UNP
         | |- ALib.Mem.wr_at _ _ _ _ => exact WRH
         | |- rng_aimg _ => exact RIMG
         | |- AP.getr _ _ = _ => exact EA1
         | |- rng _ (shad _) _ => first [ exact RNGH | apply (rng_sub _ _ _ _ _ RSH); unfold shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia ]
         | |- rng _ _ _ => first [exact RNGS | exact RSTK]
         | |- _ <= _ /\ _ => exact HULL
         | |- _ \/ _ => right; exact SPA
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
