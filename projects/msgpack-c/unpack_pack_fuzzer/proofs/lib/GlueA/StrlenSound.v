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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggLib UnreggPre UnreggC.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import StackSh MemsetPre RangePre GshC GshImg StrlenC.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require I_strlen.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require InitLib.
Unset Nia Cache. Unset Nra Cache.
Import CtrFX ActrA StrlenC.
Module IL := I_strlen.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Definition STRLEN_SYM : Z := 0x4d564.

Definition strlen_post (st1 : sstate) (r : int) (len : int) : sstate := setpc (setr (clobber st1) X10 (VL (wlit len))) r.

Lemma astrlen_apply_shape : forall segs C st sts, astrlen_apply segs C st = Some sts ->
  exists r hargs wnl st1 a len,
    acall_pre ASTACK None st = Some (r, hargs, wnl, st1)
    /\ getr st X10 = VL a /\ GshC.gstr segs C st a = Some len /\ slot_ok C st = true
    /\ sts = [strlen_post st1 r len].
Proof.
  intros segs C st sts H. unfold astrlen_apply in H.
  destruct (acall_pre ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:P; [|discriminate H].
  destruct (getr st X10) as [a| | | | | | | | | |] eqn:G10; try discriminate H.
  destruct (GshC.gstr segs C st a) as [len|] eqn:GS; [|discriminate H].
  destruct (slot_ok C st) eqn:SO; [|discriminate H]. injection H as <-.
  exists r, hargs, wnl, st1, a, len. repeat (split; [first [reflexivity | assumption]|]). reflexivity.
Qed.

Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis OPS_holds_gsh : forall m mo, op_holds OPS GshC.GSH_ID [] m mo -> gsh_holds GshC.GSH_TAB_ASAN m.
Hypothesis OPS_holds_shmap : forall m mo, op_holds OPS GshC.SHMAP_ID [] m mo -> UnreggPre.shmap_holds m.
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

Lemma slot_facts : forall E st ms mo, st_ok asegs OPS E st ms mo -> slot_ok GshC.CFG_ASAN st = true ->
  ALib.Step.rw_cells asegs (ms_mem ms) 0xd32b8 [C8 (Z_to_bv 64 0xc7af0)].
Proof.
  intros E st ms mo HS H. unfold slot_ok in H. change (GshC.g_slot GshC.CFG_ASAN) with 0xd32b8 in H.
  destruct (IMap.find 0%uint63 (s_regs st)) as [r0|] eqn:Hr0; [|discriminate H].
  apply andb_prop in H as [H Q3]. apply andb_prop in H as [Q1 Q2]. apply negb_true_iff in Q3.
  assert (BG : rg_bg r0 = BGImage) by (unfold UnreggC.UnreggC.is_bgimage in Q1; destruct (rg_bg r0); try discriminate Q1; reflexivity).
  assert (IMG : forall i, 0 <= i < 8 -> rb asegs (ms_mem ms) (0xd32b8 + i) = img_byte asegs (0xd32b8 + i)).
  { apply (UnreggLib.image_bytes_p asegs OPS E st ms mo r0 0xd32b8 8 HS Hr0 BG); [lia | lia | exact Q3 | exact Q2 | vm_compute; reflexivity]. }
  apply (UnreggLib.img_chunk_sound asegs); [vm_compute; reflexivity | lia |].
  intros i Hi. apply IMG. simpl in Hi. lia.
Qed.

Definition astrlen_leaf : Prop :=
  forall st (K : TSet) E ms mo r hargs wnl st1 (a : w64) (len : int) (str slack : list byte) (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word),
  st_ok asegs OPS E st ms mo -> PB (eb E) ->
  (forall st', In st' [strlen_post st1 r len] -> forall E' ms' mo', env_ext (s_next st) E E' -> MP mo' -> st_ok asegs OPS E' st' ms' mo' ->
               realizes asegs (mkCfg ms' mo') K) ->
  acall_pre ASTACK None st = Some (r, hargs, wnl, st1) ->
  getr st X10 = VL a -> Z.of_nat (length str) = to_Z len ->
  call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) -> ALib.Mem.mem_inv asegs (ms_mem ms) ->
  let R := ms_regs ms in
  ATOP + 4096 <= CtrPre.sp_lo E st -> CtrPre.sp_lo E st <= bv_unsigned (AP.getr R 2) - 4096 ->
  CtrPre.sp_lo E st <= bv_unsigned (AP.getr R 2) - 2160 -> bv_unsigned (AP.getr R 2) < 2 ^ 47 ->
  forall ms' mo',
  IL.strlen_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
     (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
     (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (bv_unsigned (AP.getr R 10)) str slack (CtrPre.sp_lo E st) (ms_mem ms) ms' ->
  MP mo' -> op_minv OPS mo' -> OTHER mo mo' -> ACCT aw L RNG sta LBa mo' ->
  realizes asegs (mkCfg ms' mo') K.

Theorem astrlen_sound_of_leaf : astrlen_leaf ->
  forall pc, to_Z pc = STRLEN_SYM -> contract_sound asegs OPS MP PB (astrlen_c asegs GshC.CFG_ASAN pc).
Proof.
  intros LEAF pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc astrlen_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = STRLEN_SYM) by (rewrite Hspc; exact Hpc).
  destruct (astrlen_apply_shape asegs GshC.CFG_ASAN st sts Happ) as (r & hargs & wnl & st1 & a & len & PRE & G10 & GS & SO & ->).
  destruct (CtrPre.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  change (to_Z ASTACK) with 8192 in LOR.
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT.
  set (R := ms_regs ms) in *.
  pose proof atop_range as ATR.

  destruct (gstr_ops GshC.CFG_ASAN st a len GS) as [FG FM].
  pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (UnreggPre.find_op_In _ _ _ FG)) as HG. cbn [op_id op_args map] in HG.
  pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (UnreggPre.find_op_In _ _ _ FM)) as HM. cbn [op_id op_args map] in HM.
  pose proof (ACCT_rng_aimg _ _ _ _ _ _ AC) as RIMG. pose proof (ACCT_rng_aimg_sh _ _ _ _ _ _ AC) as RISH.

  destruct (gstr_facts OPS E st ms mo a len RNG HS GS (OPS_holds_gsh _ _ HG) (OPS_holds_shmap _ _ HM) RIMG RISH)
    as (WT & SLO & L63 & str & slack & LSTR & BUF & NONUL & PAD & SHI & APB & UNP & RNGB & RLO & RHI & HULL & WRH & RNGH).
  assert (EA0' : bv_unsigned (AP.getr R 10) = to_Z (wl a)).
  { change (AP.getr R 10) with (AP.getr R (reg_of_r5 X10)). unfold R. rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X10), G10, unsigned_VL.
    unfold w2Z. rewrite WT. lia. }
  set (SA := to_Z (wl a)) in *. set (L0 := to_Z len) in *.
  pose proof (slot_facts E st ms mo HS SO) as RSL.
  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  assert (LFULL : Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) = L0 + 1 + Z.of_nat (length slack)) by (rewrite length_app; cbn [length]; lia).
  assert (EV : evtF asegs RNG
            (IL.strlen_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (bv_unsigned (AP.getr R 10)) str slack
               (CtrPre.sp_lo E st) (ms_mem ms))
            (MS (mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31))
                (ms_fregs ms) (Z_to_bv 64 STRLEN_SYM) (ms_fcsr ms) None (ms_mem ms) (seg_rom asegs))).
  { unfold artcells in RT. decompose [and] RT. clear RT.
    pose proof (IL.strlen_i_spec RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31)
                (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) (CtrPre.sp_lo E st) str slack RLO RHI) as W.
    cbv zeta in W. apply W.
    all: rewrite ?EA0', ?LSTR, ?LFULL.
    all: try lazymatch goal with
         | |- ALib.Mem.mem_inv _ _ => exact MI
         | |- stk _ _ _ _ => exact ST
         | |- ALib.Step.rw_cells _ _ _ _ => assumption
         | |- ALib.Mem.bytes_at _ _ _ _ => exact BUF
         | |- ~ In _ _ => exact NONUL
         | |- Shadow.app_blk _ _ => exact APB
         | |- Shadow.unpoisoned _ _ _ => exact UNP
         | |- ALib.Mem.wr_at _ _ _ _ => exact WRH
         | |- rng_aimg _ => exact RIMG
         | |- rng _ (shad _) _ => exact RNGH
         | |- rng _ _ _ => first [exact RSTK | exact RNGB | exact RIMG]
         | |- _ <= _ /\ _ => exact HULL
         end.
    all: try lazymatch goal with
         | |- _ mod 8 <= _ => exact PAD
         | |- _ \/ _ => left; unfold SA, L0 in *; lia
         end.
    all: try (unfold Shadow.KHIGH in *; unfold SA, L0 in *; lia).
    all: match goal with |- ?G => idtac "REMW" G end. }
  rewrite Ems, HPC. apply (GlueA.realizes_to_mkRA asegs).
  eapply (implS_twfS_realizes_silent asegs NMAXt (Ret (Exc.Ok tt)) RNG AL0
            (fun (_ : unit) (RNGq : footprint) ms' => RNGq = RNG /\ IL.strlen_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (bv_unsigned (AP.getr R 10)) str slack
               (CtrPre.sp_lo E st) (ms_mem ms) ms')
            _ _ moc mo K).
  - cbn [implF epostF]. eapply evtF_mono; [exact EV|]. intros ms' PO. split; [reflexivity| exact PO].
  - exact TW.
  - exact HH.
  - exact MINV.
  - exact MR.
  - intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV' MR'.
    destruct (HP' mo' MR') as (HMP' & HMI' & OTH & ACP). destruct HQ as [-> HQ].
    exact (LEAF st K E ms mo r hargs wnl st1 a len str slack L RNG sta LBa aw HS HPB HK PRE G10 LSTR CP FS CF AH MI BOT LO
             ltac:(fold R; lia) SPT ms' mo' HQ HMP' HMI' OTH ACP).
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

Import StackSh.TwinB MemsetPre.TwinB RangePre.TwinB GshC.TwinB GshImg.TwinB StrlenC.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import CtrFX ActrA StrlenC.TwinB.StrlenC.
Module IL := I_strlen.TwinB.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Definition STRLEN_SYM : Z := 0x4def4.

Definition strlen_post (st1 : sstate) (r : int) (len : int) : sstate := setpc (setr (clobber st1) X10 (VL (wlit len))) r.

Lemma astrlen_apply_shape : forall segs C st sts, astrlen_apply segs C st = Some sts ->
  exists r hargs wnl st1 a len,
    acall_pre ASTACK None st = Some (r, hargs, wnl, st1)
    /\ getr st X10 = VL a /\ GshC.TwinB.GshC.gstr segs C st a = Some len /\ slot_ok C st = true
    /\ sts = [strlen_post st1 r len].
Proof.
  intros segs C st sts H. unfold astrlen_apply in H.
  destruct (acall_pre ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:P; [|discriminate H].
  destruct (getr st X10) as [a| | | | | | | | | |] eqn:G10; try discriminate H.
  destruct (GshC.TwinB.GshC.gstr segs C st a) as [len|] eqn:GS; [|discriminate H].
  destruct (slot_ok C st) eqn:SO; [|discriminate H]. injection H as <-.
  exists r, hargs, wnl, st1, a, len. repeat (split; [first [reflexivity | assumption]|]). reflexivity.
Qed.

Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis OPS_holds_gsh : forall m mo, op_holds OPS GshC.TwinB.GshC.GSH_ID [] m mo -> gsh_holds GshC.TwinB.GshC.GSH_TAB_ASAN m.
Hypothesis OPS_holds_shmap : forall m mo, op_holds OPS GshC.TwinB.GshC.SHMAP_ID [] m mo -> UnreggPre.TwinB.shmap_holds m.
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

Lemma slot_facts : forall E st ms mo, st_ok bsegs OPS E st ms mo -> slot_ok GshC.TwinB.GshC.CFG_ASAN st = true ->
  ALib.Step.rw_cells bsegs (ms_mem ms) 0xd53d0 [C8 (Z_to_bv 64 0xc9c0c)].
Proof.
  intros E st ms mo HS H. unfold slot_ok in H. change (GshC.TwinB.GshC.g_slot GshC.TwinB.GshC.CFG_ASAN) with 0xd53d0 in H.
  destruct (IMap.find 0%uint63 (s_regs st)) as [r0|] eqn:Hr0; [|discriminate H].
  apply andb_prop in H as [H Q3]. apply andb_prop in H as [Q1 Q2]. apply negb_true_iff in Q3.
  assert (BG : rg_bg r0 = BGImage) by (unfold UnreggC.TwinB.UnreggC.is_bgimage in Q1; destruct (rg_bg r0); try discriminate Q1; reflexivity).
  assert (IMG : forall i, 0 <= i < 8 -> rb bsegs (ms_mem ms) (0xd53d0 + i) = img_byte bsegs (0xd53d0 + i)).
  { apply (UnreggLib.TwinB.image_bytes_p bsegs OPS E st ms mo r0 0xd53d0 8 HS Hr0 BG); [lia | lia | exact Q3 | exact Q2 | vm_compute; reflexivity]. }
  apply (UnreggLib.TwinB.img_chunk_sound bsegs); [vm_compute; reflexivity | lia |].
  intros i Hi. apply IMG. simpl in Hi. lia.
Qed.

Definition astrlen_leaf : Prop :=
  forall st (K : TSet) E ms mo r hargs wnl st1 (a : w64) (len : int) (str slack : list byte) (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word),
  st_ok bsegs OPS E st ms mo -> PB (eb E) ->
  (forall st', In st' [strlen_post st1 r len] -> forall E' ms' mo', env_ext (s_next st) E E' -> MP mo' -> st_ok bsegs OPS E' st' ms' mo' ->
               realizes bsegs (mkCfg ms' mo') K) ->
  acall_pre ASTACK None st = Some (r, hargs, wnl, st1) ->
  getr st X10 = VL a -> Z.of_nat (length str) = to_Z len ->
  call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) -> ALib.Mem.mem_inv bsegs (ms_mem ms) ->
  let R := ms_regs ms in
  ATOP + 4096 <= CtrPre.TwinB.sp_lo E st -> CtrPre.TwinB.sp_lo E st <= bv_unsigned (AP.getr R 2) - 4096 ->
  CtrPre.TwinB.sp_lo E st <= bv_unsigned (AP.getr R 2) - 2160 -> bv_unsigned (AP.getr R 2) < 2 ^ 47 ->
  forall ms' mo',
  IL.strlen_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
     (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
     (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (bv_unsigned (AP.getr R 10)) str slack (CtrPre.TwinB.sp_lo E st) (ms_mem ms) ms' ->
  MP mo' -> op_minv OPS mo' -> OTHER mo mo' -> ACCT aw L RNG sta LBa mo' ->
  realizes bsegs (mkCfg ms' mo') K.

Theorem astrlen_sound_of_leaf : astrlen_leaf ->
  forall pc, to_Z pc = STRLEN_SYM -> contract_sound bsegs OPS MP PB (astrlen_c bsegs GshC.TwinB.GshC.CFG_ASAN pc).
Proof.
  intros LEAF pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc astrlen_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = STRLEN_SYM) by (rewrite Hspc; exact Hpc).
  destruct (astrlen_apply_shape bsegs GshC.TwinB.GshC.CFG_ASAN st sts Happ) as (r & hargs & wnl & st1 & a & len & PRE & G10 & GS & SO & ->).
  destruct (CtrPre.TwinB.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  change (to_Z ASTACK) with 8192 in LOR.
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT.
  set (R := ms_regs ms) in *.
  pose proof atop_range as ATR.

  destruct (gstr_ops GshC.TwinB.GshC.CFG_ASAN st a len GS) as [FG FM].
  pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (UnreggPre.TwinB.find_op_In _ _ _ FG)) as HG. cbn [op_id op_args map] in HG.
  pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (UnreggPre.TwinB.find_op_In _ _ _ FM)) as HM. cbn [op_id op_args map] in HM.
  pose proof (ACCT_rng_aimg _ _ _ _ _ _ AC) as RIMG. pose proof (ACCT_rng_aimg_sh _ _ _ _ _ _ AC) as RISH.

  destruct (gstr_facts OPS E st ms mo a len RNG HS GS (OPS_holds_gsh _ _ HG) (OPS_holds_shmap _ _ HM) RIMG RISH)
    as (WT & SLO & L63 & str & slack & LSTR & BUF & NONUL & PAD & SHI & APB & UNP & RNGB & RLO & RHI & HULL & WRH & RNGH).
  assert (EA0' : bv_unsigned (AP.getr R 10) = to_Z (wl a)).
  { change (AP.getr R 10) with (AP.getr R (reg_of_r5 X10)). unfold R. rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X10), G10, unsigned_VL.
    unfold w2Z. rewrite WT. lia. }
  set (SA := to_Z (wl a)) in *. set (L0 := to_Z len) in *.
  pose proof (slot_facts E st ms mo HS SO) as RSL.
  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  assert (LFULL : Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) = L0 + 1 + Z.of_nat (length slack)) by (rewrite length_app; cbn [length]; lia).
  assert (EV : evtF bsegs RNG
            (IL.strlen_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (bv_unsigned (AP.getr R 10)) str slack
               (CtrPre.TwinB.sp_lo E st) (ms_mem ms))
            (MS (mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31))
                (ms_fregs ms) (Z_to_bv 64 STRLEN_SYM) (ms_fcsr ms) None (ms_mem ms) (seg_rom bsegs))).
  { unfold artcells in RT. decompose [and] RT. clear RT.
    pose proof (IL.strlen_i_spec RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31)
                (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) (CtrPre.TwinB.sp_lo E st) str slack RLO RHI) as W.
    cbv zeta in W. apply W.
    all: rewrite ?EA0', ?LSTR, ?LFULL.
    all: try lazymatch goal with
         | |- ALib.Mem.mem_inv _ _ => exact MI
         | |- stk _ _ _ _ => exact ST
         | |- ALib.Step.rw_cells _ _ _ _ => assumption
         | |- ALib.Mem.bytes_at _ _ _ _ => exact BUF
         | |- ~ In _ _ => exact NONUL
         | |- Shadow.app_blk _ _ => exact APB
         | |- Shadow.unpoisoned _ _ _ => exact UNP
         | |- ALib.Mem.wr_at _ _ _ _ => exact WRH
         | |- rng_aimg _ => exact RIMG
         | |- rng _ (shad _) _ => exact RNGH
         | |- rng _ _ _ => first [exact RSTK | exact RNGB | exact RIMG]
         | |- _ <= _ /\ _ => exact HULL
         end.
    all: try lazymatch goal with
         | |- _ mod 8 <= _ => exact PAD
         | |- _ \/ _ => left; unfold SA, L0 in *; lia
         end.
    all: try (unfold Shadow.KHIGH in *; unfold SA, L0 in *; lia).
    all: match goal with |- ?G => idtac "REMW" G end. }
  rewrite Ems, HPC. apply (GlueA.TwinB.realizes_to_mkRA bsegs).
  eapply (implS_twfS_realizes_silent bsegs NMAXt (Ret (Exc.Ok tt)) RNG AL0
            (fun (_ : unit) (RNGq : footprint) ms' => RNGq = RNG /\ IL.strlen_i_post (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (bv_unsigned (AP.getr R 10)) str slack
               (CtrPre.TwinB.sp_lo E st) (ms_mem ms) ms')
            _ _ moc mo K).
  - cbn [implF epostF]. eapply evtF_mono; [exact EV|]. intros ms' PO. split; [reflexivity| exact PO].
  - exact TW.
  - exact HH.
  - exact MINV.
  - exact MR.
  - intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV' MR'.
    destruct (HP' mo' MR') as (HMP' & HMI' & OTH & ACP). destruct HQ as [-> HQ].
    exact (LEAF st K E ms mo r hargs wnl st1 a len str slack L RNG sta LBa aw HS HPB HK PRE G10 LSTR CP FS CF AH MI BOT LO
             ltac:(fold R; lia) SPT ms' mo' HQ HMP' HMI' OTH ACP).
Qed.
End Sound.
End TwinB.
