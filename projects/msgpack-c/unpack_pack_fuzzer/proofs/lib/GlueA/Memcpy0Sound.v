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
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs StepSoundBase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB MemFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA GlueA CtrPre CtrFrame CtrNoDelta CtrFree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggGeo UnreggPre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import UnreggSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import MemOps MemsetFX RangePre MemsetPost MemcpySound Memcpy0C.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require I_asan_memcpy0. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require I_asan_memcpy0.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import RtCells.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require ReadPost.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP StepB CtrFX ActrA Memcpy0C.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Definition mc0_post {rc : runConstT} (FRM : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (MState.ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - FRM, bv_unsigned sp)]%Z m m'
    /\ wmono asegs m m' /\ AM.mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Definition memcpy0_walk_stmt {rc : runConstT} (SYM FRM : Z) : Prop :=
  forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  AM.mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FRM)%Z -> (Shadow.KHIGH <= lo)%Z ->
  rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (mc0_post FRM ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SYM) fc None m (seg_rom asegs)).

Lemma memcpy0_walk_i {rc : runConstT} : memcpy0_walk_stmt MEMCPY_SYM 2240.
Proof. exact OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy0.I_memcpy0.memcpy_i_spec0_any. Qed.
Lemma memcpy0_walk_asan {rc : runConstT} : memcpy0_walk_stmt ASAN_MEMCPY_SYM 2224.
Proof. exact OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy0.I_asan_memcpy0.asan_memcpy_spec0_any. Qed.

Definition mc0_state (st st1 : sstate) (r : int) : sstate := setpc (setr (clobber st1) X10 (getr st X10)) r.
Lemma amemcpy0_apply_shape : forall st sts, amemcpy0_apply st = Some sts ->
  exists r hargs wnl st1, acall_pre ASTACK None st = Some (r, hargs, wnl, st1) /\ getr st X12 = VL wzero /\ sts = [mc0_state st st1 r].
Proof.
  intros st sts H. unfold amemcpy0_apply in H.
  destruct (acall_pre ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:PRE; [|discriminate H].
  destruct (getr st X12) as [n| | | | | | | | | |] eqn:G12; try discriminate H.
  destruct (weqb n wzero) eqn:NZ; [|discriminate H]. apply weqb_eq in NZ. subst n.
  exists r, hargs, wnl, st1. split; [reflexivity|]. split; [reflexivity|]. unfold mc0_state. congruence.
Qed.

Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis OPS_fp1 : forall args, op_fp OPS HEAP_ID args = heap_fp IMGX args.
Hypothesis OPS_cov1 : forall args z, op_cov1 OPS HEAP_ID args z <-> Op.cov1 HEAP_ID args z.
Hypothesis OPS_frame_other : forall id args m m' mo, id <> HEAP_ID -> op_holds OPS id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) -> wb asegs m a = true -> wb asegs m' a = true) ->
  op_holds OPS id args m' mo.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Variable OTHER : Model -> Model -> Prop.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.
Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment asegs a 1 = Some seg) -> op_cov0 OPS a.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable NMAXt : nat.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent ACCT OPS OTHER MP mo aw L st LBa).

Lemma mc0_core : forall SYM FRM, 0 < FRM <= 8192 -> memcpy0_walk_stmt SYM FRM ->
  forall st (K : TSet) E ms mo r hargs wnl st1,
  st_ok asegs OPS E st ms mo -> MP mo -> to_Z (s_pc st) = SYM ->
  acall_pre ASTACK None st = Some (r, hargs, wnl, st1) ->
  AP.getr (ms_regs ms) 12 = Z_to_bv 64 0 ->
  (forall st', In st' [mc0_state st st1 r] -> forall E' ms' mo', env_ext (s_next st) E E' -> MP mo' -> st_ok asegs OPS E' st' ms' mo' ->
               realizes asegs (mkCfg ms' mo') K) ->
  realizes asegs (mkCfg ms mo) K.
Proof.
  intros SYM FRM FR WALK st K E ms mo r hargs wnl st1 HS HMP HPC PRE EA2 HK.
  destruct (CtrPre.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  change (to_Z ASTACK) with 8192 in LOR.
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT.
  set (R := ms_regs ms) in *. pose proof atop_range as ATR.
  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  pose proof (ACCT_rng_aimg _ _ _ _ _ _ AC) as RIMG.
  assert (EV : evtF asegs RNG
            (mc0_post FRM (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (AP.getr R 10) (CtrPre.sp_lo E st) (ms_mem ms))
            (MS (mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (Z_to_bv 64 0) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31))
                (ms_fregs ms) (Z_to_bv 64 SYM) (ms_fcsr ms) None (ms_mem ms) (seg_rom asegs))).
  { unfold artcells in RT. decompose [and] RT. clear RT.
    apply WALK.
    all: try lazymatch goal with
         | |- AM.mem_inv _ _ => exact MI
         | |- stk _ _ _ _ => exact ST
         | |- ALib.Step.rw_cells _ _ _ _ => assumption
         | |- rng_aimg _ => exact RIMG
         | |- rng _ _ _ => exact RSTK
         end.
    all: try (unfold Shadow.KHIGH in *; lia).
    all: match goal with |- ?G => idtac "REMW" G end. }
  rewrite Ems, HPC. apply (GlueA.realizes_to_mkRA asegs). unfold GlueA.mkR_ofA. fold R. rewrite EA2.
  eapply (implS_twfS_realizes_silent asegs NMAXt (Ret (Exc.Ok tt)) RNG AL0
            (fun (_ : unit) (RNGq : footprint) ms' => RNGq = RNG /\ mc0_post FRM (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (AP.getr R 10) (CtrPre.sp_lo E st) (ms_mem ms) ms')
            _ _ moc mo K).
  - cbn [implF epostF]. eapply evtF_mono; [exact EV|]. intros ms' PO. split; [reflexivity| exact PO].
  - exact TW.
  - exact HH.
  - exact MINV.
  - exact MR.
  -
    intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV'' MR'.
    destruct (HP' mo' MR') as (HMP' & HMI' & OTH & ACP). destruct HQ as [-> HQ].
    destruct HQ as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MU & WM & MINV' & STK').
    match type of EMS with ms' = MS ?RR _ _ _ _ _ _ => set (R' := RR) in * end.
    set (Fv := CtrFree.cfvF R'). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0). set (E' := CtrFrame.E' E st Fv Gv).
    destruct (HeapCtr.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WT0 & LT0 & ER).
    assert (RAEQ : AP.getr R 1%bv = Z_to_bv 64 (to_Z r)).
    { unfold R. rewrite <- HeapCtr.reg_of_X1, (GlueA.getr_RA asegs OPS E st ms mo HS X1), Hra0, ER.
      assert (ERA : ra0 = wlit (wl ra0)) by (destruct ra0 as [t l]; cbn in WT0 |- *; subst t; reflexivity). rewrite ERA at 1. apply HeapCtr.den_wlit. }
    assert (EMS' : ms' = CtrFrame.ms' ms r R' m').
    { rewrite EMS. unfold CtrFrame.ms'. f_equal. rewrite RAEQ. apply ret_pc_even.
      - pose proof (int_range r) as RRr. rewrite two63_eq in RRr. lia.
      - pose proof (HeapCtr.call_pre_even st r CP) as EVn.
        pose proof (land_mk r 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
        change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EVn in LM. change (to_Z 0%uint63) with 0 in LM.
        change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }
    destruct (clobber_fields st1) as (_ & FF & RV & RG & FS0 & OP & PV & NXc).
    destruct (CtrFrame.st1_fields st st1 FS) as (_ & _ & FF1 & RV1 & FS1 & OP1 & PV1 & NX1).
    destruct (CtrFrame.SVB_parts st FOK) as (RFB & _).
    assert (VB10 : sv_vars_below (s_next st) (getr st X10) = true) by exact (PlanS.rf_allb_get _ _ _ RFB X10).
    assert (DVP : den E' (getr st X10) = AP.getr R' 10%bv).
    { unfold E'. rewrite (CtrFrame.den_E' E st Fv Gv _ VB10). symmetry. exact (GlueA.getr_RA asegs OPS E st ms mo HS X10). }
    assert (MU0 : munch [(bv_unsigned (AP.getr R 2) - FRM, bv_unsigned (AP.getr R 2)); (0, 0 + 0)]%Z (ms_mem ms) m').
    { intros x OUT. apply MU. cbn [outside] in OUT |- *. tauto. }
    pose proof (phaseA_ms_g AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
                  st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' 0 0 FRM (getr st X10) (s_next (clobber st1)) HS CP FS CF AH BOT LO SPT
                  ltac:(lia) ltac:(left; lia) ltac:(split; [lia| fold R; lia]) MU0 WM MI MINV' STK'
                  ltac:(intros rg Hrg; unfold CtrFrame.kept_regsA in Hrg; cbn [In] in Hrg; repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]); destruct Hrg)
                  DVP OTH HMI' ACP) as HSA.
    fold Fv Gv E' in HSA.
    assert (PW0 : forall x, m' x = ms_mem (CtrFrame.ms' ms r R' (mjoinR 0 (0 + 0) (ms_mem ms) m')) x).
    { intros x. change (ms_mem (CtrFrame.ms' ms r R' (mjoinR 0 (0 + 0) (ms_mem ms) m')) x) with (mjoinR 0 (0 + 0) (ms_mem ms) m' x).
      unfold mjoinR, in_rng. replace ((0 <=? bv_unsigned x) && (bv_unsigned x <? 0 + 0))%bool with false; [reflexivity|].
      symmetry. apply andb_false_iff. right. apply Z.ltb_ge. pose proof (bv_unsigned_in_range _ x). lia. }
    pose proof (st_ok_mem_ext_g OPS E' _ _ mo' m' PW0 HSA) as HS1.
    assert (SH2 : setpc (setr (clobber st1) X10 (getr st X10)) r
                = SS r (rf_set (s_rf (clobber st1)) X10 (getr st X10)) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) (s_ops st) (s_priv st) (s_next (clobber st1))).
    { rewrite <- FF1, <- RV1, <- FS1, <- OP1, <- PV1, <- FF, <- RV, <- RG, <- FS0, <- OP, <- PV. destruct (clobber st1); reflexivity. }
    apply (HK _ (or_introl eq_refl) E' ms' mo' (CtrFrame.EXT E st Fv Gv) HMP').
    rewrite EMS'. unfold mc0_state. rewrite SH2. exact HS1.
Qed.

Theorem amemcpy0_sound_at : forall SYM FRM, 0 < FRM <= 8192 -> memcpy0_walk_stmt SYM FRM ->
  forall pc, to_Z pc = SYM -> contract_sound asegs OPS MP PB (amemcpy0_c pc).
Proof.
  intros SYM FRM FR WALK pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc amemcpy0_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = SYM) by (rewrite Hspc; exact Hpc).
  destruct (amemcpy0_apply_shape st sts Happ) as (r & hargs & wnl & st1 & PRE & G12 & ->).
  apply (mc0_core SYM FRM FR WALK st K E ms mo r hargs wnl st1 HS HMP HPC PRE); [| exact HK].
  change (AP.getr (ms_regs ms) 12) with (AP.getr (ms_regs ms) (reg_of_r5 X12)). rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X12), G12. reflexivity.
Qed.

Theorem amemcpy0_sound : forall pc, to_Z pc = MEMCPY_SYM -> contract_sound asegs OPS MP PB (amemcpy0_c pc).
Proof. exact (amemcpy0_sound_at MEMCPY_SYM 2240 ltac:(lia) memcpy0_walk_i). Qed.
Theorem aasan_memcpy0_sound : forall pc, to_Z pc = ASAN_MEMCPY_SYM -> contract_sound asegs OPS MP PB (amemcpy0_c pc).
Proof. exact (amemcpy0_sound_at ASAN_MEMCPY_SYM 2224 ltac:(lia) memcpy0_walk_asan). Qed.
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
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Import Actr.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import UnreggSound.TwinB.
Import MemOps.TwinB MemsetFX.TwinB RangePre.TwinB MemsetPost.TwinB MemcpySound.TwinB Memcpy0C.TwinB.

Import RtCells.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ValP MemP StepB CtrFX ActrA Memcpy0C.TwinB.Memcpy0C.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Definition mc0_post {rc : runConstT} (FRM : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (MState.ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - FRM, bv_unsigned sp)]%Z m m'
    /\ wmono bsegs m m' /\ AM.mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Definition memcpy0_walk_stmt {rc : runConstT} (SYM FRM : Z) : Prop :=
  forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  AM.mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FRM)%Z -> (Shadow.KHIGH <= lo)%Z ->
  rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (mc0_post FRM ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SYM) fc None m (seg_rom bsegs)).

Lemma memcpy0_walk_i {rc : runConstT} : memcpy0_walk_stmt MEMCPY_SYM 2240.
Proof. exact OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy0.TwinB.I_memcpy0.memcpy_i_spec0_any. Qed.
Lemma memcpy0_walk_asan {rc : runConstT} : memcpy0_walk_stmt ASAN_MEMCPY_SYM 2224.
Proof. exact OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy0.TwinB.I_asan_memcpy0.asan_memcpy_spec0_any. Qed.

Definition mc0_state (st st1 : sstate) (r : int) : sstate := setpc (setr (clobber st1) X10 (getr st X10)) r.
Lemma amemcpy0_apply_shape : forall st sts, amemcpy0_apply st = Some sts ->
  exists r hargs wnl st1, acall_pre ASTACK None st = Some (r, hargs, wnl, st1) /\ getr st X12 = VL wzero /\ sts = [mc0_state st st1 r].
Proof.
  intros st sts H. unfold amemcpy0_apply in H.
  destruct (acall_pre ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:PRE; [|discriminate H].
  destruct (getr st X12) as [n| | | | | | | | | |] eqn:G12; try discriminate H.
  destruct (weqb n wzero) eqn:NZ; [|discriminate H]. apply weqb_eq in NZ. subst n.
  exists r, hargs, wnl, st1. split; [reflexivity|]. split; [reflexivity|]. unfold mc0_state. congruence.
Qed.

Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis OPS_fp1 : forall args, op_fp OPS HEAP_ID args = heap_fp IMGX args.
Hypothesis OPS_cov1 : forall args z, op_cov1 OPS HEAP_ID args z <-> Op.TwinB.cov1 HEAP_ID args z.
Hypothesis OPS_frame_other : forall id args m m' mo, id <> HEAP_ID -> op_holds OPS id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) -> wb bsegs m a = true -> wb bsegs m' a = true) ->
  op_holds OPS id args m' mo.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Variable OTHER : Model -> Model -> Prop.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.
Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment bsegs a 1 = Some seg) -> op_cov0 OPS a.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable NMAXt : nat.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent ACCT OPS OTHER MP mo aw L st LBa).

Lemma mc0_core : forall SYM FRM, 0 < FRM <= 8192 -> memcpy0_walk_stmt SYM FRM ->
  forall st (K : TSet) E ms mo r hargs wnl st1,
  st_ok bsegs OPS E st ms mo -> MP mo -> to_Z (s_pc st) = SYM ->
  acall_pre ASTACK None st = Some (r, hargs, wnl, st1) ->
  AP.getr (ms_regs ms) 12 = Z_to_bv 64 0 ->
  (forall st', In st' [mc0_state st st1 r] -> forall E' ms' mo', env_ext (s_next st) E E' -> MP mo' -> st_ok bsegs OPS E' st' ms' mo' ->
               realizes bsegs (mkCfg ms' mo') K) ->
  realizes bsegs (mkCfg ms mo) K.
Proof.
  intros SYM FRM FR WALK st K E ms mo r hargs wnl st1 HS HMP HPC PRE EA2 HK.
  destruct (CtrPre.TwinB.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  change (to_Z ASTACK) with 8192 in LOR.
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT.
  set (R := ms_regs ms) in *. pose proof atop_range as ATR.
  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  pose proof (ACCT_rng_aimg _ _ _ _ _ _ AC) as RIMG.
  assert (EV : evtF bsegs RNG
            (mc0_post FRM (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (AP.getr R 10) (CtrPre.TwinB.sp_lo E st) (ms_mem ms))
            (MS (mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (Z_to_bv 64 0) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31))
                (ms_fregs ms) (Z_to_bv 64 SYM) (ms_fcsr ms) None (ms_mem ms) (seg_rom bsegs))).
  { unfold artcells in RT. decompose [and] RT. clear RT.
    apply WALK.
    all: try lazymatch goal with
         | |- AM.mem_inv _ _ => exact MI
         | |- stk _ _ _ _ => exact ST
         | |- ALib.Step.rw_cells _ _ _ _ => assumption
         | |- rng_aimg _ => exact RIMG
         | |- rng _ _ _ => exact RSTK
         end.
    all: try (unfold Shadow.KHIGH in *; lia).
    all: match goal with |- ?G => idtac "REMW" G end. }
  rewrite Ems, HPC. apply (GlueA.TwinB.realizes_to_mkRA bsegs). unfold GlueA.TwinB.mkR_ofA. fold R. rewrite EA2.
  eapply (implS_twfS_realizes_silent bsegs NMAXt (Ret (Exc.Ok tt)) RNG AL0
            (fun (_ : unit) (RNGq : footprint) ms' => RNGq = RNG /\ mc0_post FRM (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) (AP.getr R 10) (CtrPre.TwinB.sp_lo E st) (ms_mem ms) ms')
            _ _ moc mo K).
  - cbn [implF epostF]. eapply evtF_mono; [exact EV|]. intros ms' PO. split; [reflexivity| exact PO].
  - exact TW.
  - exact HH.
  - exact MINV.
  - exact MR.
  -
    intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV'' MR'.
    destruct (HP' mo' MR') as (HMP' & HMI' & OTH & ACP). destruct HQ as [-> HQ].
    destruct HQ as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MU & WM & MINV' & STK').
    match type of EMS with ms' = MS ?RR _ _ _ _ _ _ => set (R' := RR) in * end.
    set (Fv := CtrFree.TwinB.cfvF R'). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0). set (E' := CtrFrame.TwinB.E' E st Fv Gv).
    destruct (HeapCtr.TwinB.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WT0 & LT0 & ER).
    assert (RAEQ : AP.getr R 1%bv = Z_to_bv 64 (to_Z r)).
    { unfold R. rewrite <- HeapCtr.TwinB.reg_of_X1, (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X1), Hra0, ER.
      assert (ERA : ra0 = wlit (wl ra0)) by (destruct ra0 as [t l]; cbn in WT0 |- *; subst t; reflexivity). rewrite ERA at 1. apply HeapCtr.TwinB.den_wlit. }
    assert (EMS' : ms' = CtrFrame.TwinB.ms' ms r R' m').
    { rewrite EMS. unfold CtrFrame.TwinB.ms'. f_equal. rewrite RAEQ. apply ret_pc_even.
      - pose proof (int_range r) as RRr. rewrite two63_eq in RRr. lia.
      - pose proof (HeapCtr.TwinB.call_pre_even st r CP) as EVn.
        pose proof (land_mk r 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
        change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EVn in LM. change (to_Z 0%uint63) with 0 in LM.
        change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }
    destruct (clobber_fields st1) as (_ & FF & RV & RG & FS0 & OP & PV & NXc).
    destruct (CtrFrame.TwinB.st1_fields st st1 FS) as (_ & _ & FF1 & RV1 & FS1 & OP1 & PV1 & NX1).
    destruct (CtrFrame.TwinB.SVB_parts st FOK) as (RFB & _).
    assert (VB10 : sv_vars_below (s_next st) (getr st X10) = true) by exact (PlanS.rf_allb_get _ _ _ RFB X10).
    assert (DVP : den E' (getr st X10) = AP.getr R' 10%bv).
    { unfold E'. rewrite (CtrFrame.TwinB.den_E' E st Fv Gv _ VB10). symmetry. exact (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X10). }
    assert (MU0 : munch [(bv_unsigned (AP.getr R 2) - FRM, bv_unsigned (AP.getr R 2)); (0, 0 + 0)]%Z (ms_mem ms) m').
    { intros x OUT. apply MU. cbn [outside] in OUT |- *. tauto. }
    pose proof (phaseA_ms_g AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
                  st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' 0 0 FRM (getr st X10) (s_next (clobber st1)) HS CP FS CF AH BOT LO SPT
                  ltac:(lia) ltac:(left; lia) ltac:(split; [lia| fold R; lia]) MU0 WM MI MINV' STK'
                  ltac:(intros rg Hrg; unfold CtrFrame.TwinB.kept_regsA in Hrg; cbn [In] in Hrg; repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]); destruct Hrg)
                  DVP OTH HMI' ACP) as HSA.
    fold Fv Gv E' in HSA.
    assert (PW0 : forall x, m' x = ms_mem (CtrFrame.TwinB.ms' ms r R' (mjoinR 0 (0 + 0) (ms_mem ms) m')) x).
    { intros x. change (ms_mem (CtrFrame.TwinB.ms' ms r R' (mjoinR 0 (0 + 0) (ms_mem ms) m')) x) with (mjoinR 0 (0 + 0) (ms_mem ms) m' x).
      unfold mjoinR, in_rng. replace ((0 <=? bv_unsigned x) && (bv_unsigned x <? 0 + 0))%bool with false; [reflexivity|].
      symmetry. apply andb_false_iff. right. apply Z.ltb_ge. pose proof (bv_unsigned_in_range _ x). lia. }
    pose proof (st_ok_mem_ext_g OPS E' _ _ mo' m' PW0 HSA) as HS1.
    assert (SH2 : setpc (setr (clobber st1) X10 (getr st X10)) r
                = SS r (rf_set (s_rf (clobber st1)) X10 (getr st X10)) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) (s_ops st) (s_priv st) (s_next (clobber st1))).
    { rewrite <- FF1, <- RV1, <- FS1, <- OP1, <- PV1, <- FF, <- RV, <- RG, <- FS0, <- OP, <- PV. destruct (clobber st1); reflexivity. }
    apply (HK _ (or_introl eq_refl) E' ms' mo' (CtrFrame.TwinB.EXT E st Fv Gv) HMP').
    rewrite EMS'. unfold mc0_state. rewrite SH2. exact HS1.
Qed.

Theorem amemcpy0_sound_at : forall SYM FRM, 0 < FRM <= 8192 -> memcpy0_walk_stmt SYM FRM ->
  forall pc, to_Z pc = SYM -> contract_sound bsegs OPS MP PB (amemcpy0_c pc).
Proof.
  intros SYM FRM FR WALK pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc amemcpy0_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = SYM) by (rewrite Hspc; exact Hpc).
  destruct (amemcpy0_apply_shape st sts Happ) as (r & hargs & wnl & st1 & PRE & G12 & ->).
  apply (mc0_core SYM FRM FR WALK st K E ms mo r hargs wnl st1 HS HMP HPC PRE); [| exact HK].
  change (AP.getr (ms_regs ms) 12) with (AP.getr (ms_regs ms) (reg_of_r5 X12)). rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X12), G12. reflexivity.
Qed.

Theorem amemcpy0_sound : forall pc, to_Z pc = MEMCPY_SYM -> contract_sound bsegs OPS MP PB (amemcpy0_c pc).
Proof. exact (amemcpy0_sound_at MEMCPY_SYM 2240 ltac:(lia) memcpy0_walk_i). Qed.
Theorem aasan_memcpy0_sound : forall pc, to_Z pc = ASAN_MEMCPY_SYM -> contract_sound bsegs OPS MP PB (amemcpy0_c pc).
Proof. exact (amemcpy0_sound_at ASAN_MEMCPY_SYM 2224 ltac:(lia) memcpy0_walk_asan). Qed.
End Sound.

End TwinB.
