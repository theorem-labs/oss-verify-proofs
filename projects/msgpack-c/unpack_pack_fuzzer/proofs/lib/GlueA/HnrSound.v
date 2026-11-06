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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_hnrP.
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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA CallV GlueA CtrPre FrameV CtrFrame CtrFree CtrNoDelta.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require StackSh.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require RangePre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require SmLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import ActrB SmShape.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.
Module HN := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_hnrP.

Definition hnr_postA {rc : runConstT} (AI : AMallocIface2) (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (MState.ret_pc ra) fc None m' (seg_rom asegs)
    /\ AM.mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ AHEAP AI L RNG st LB m'
    /\ twins_pres LB m m'
    /\ (forall a, 0 <= a < 2^64 -> aclient_addr (aci AI) LB (bv_unsigned sp) a ->
          ~ (shad (HN.hnr_bottom sp) <= a < shad (al_top L)) ->
          m' (AM.wa a) = m (AM.wa a) /\ (wview asegs m (AM.wa a) <> None -> wview asegs m' (AM.wa a) <> None))
    /\ AS.rw_cells asegs m' (shad (HN.hnr_bottom sp))
         [CB (Z.to_nat (shlen (al_top L - HN.hnr_bottom sp))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (al_top L - HN.hnr_bottom sp))))].

Definition hnr_walk_stmt {rc : runConstT} (AI : AMallocIface2) (AI_fake : AI_fake_law AI) (entry : Z) : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z) (junk : list byte),
  AHEAP AI L RNG st LB m ->
  AM.mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - 12288 ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  AS.rw_cells asegs m (shad (HN.hnr_bottom sp)) [CB (Z.to_nat (shlen (al_top L - HN.hnr_bottom sp))) junk] ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> FRNG AI AI_fake L RNG ->
  rng RNG (shad (HN.hnr_bottom sp)) (shlen (al_top L - HN.hnr_bottom sp)) ->
  evtF asegs RNG (hnr_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Lemma hnr_apply_shape : forall TP st sts, ActrB.hnr_apply TP st = Some sts ->
  exists r hargs hargs0 st1, ActrB.ssh_present st = true /\ find_op HEAP_ID (s_ops st) = Some hargs0 /\ ActrA.sp_altop_ok st hargs0 = true
    /\ ActrB.acall_pre TP 12288%uint63 st = Some (r, hargs)
    /\ ActrA.forget_stack_below_sp_g st = Some st1
    /\ sts = [setpc (setr (snd (fresh (clobber st1))) X10 (VP (fst (fresh (clobber st1))) wzero)) r].
Proof.
  intros TP st sts H. unfold ActrB.hnr_apply in H. destruct (find_op HEAP_ID (s_ops st)) as [hargs0|] eqn:FO; [|discriminate H].
  destruct (ActrB.ssh_present st && ActrA.sp_altop_ok st hargs0)%bool eqn:CK; [|discriminate H]. apply andb_prop in CK as [SSH SAO].
  unfold ActrB.void_call_apply in H. destruct (ActrB.acall_pre TP 12288%uint63 st) as [[r hargs]|] eqn:PRE; [|discriminate H].
  unfold ActrB.forget_stack_below_sp_g in H. destruct (ActrA.forget_stack_below_sp_g st) as [st1|] eqn:FS; [|discriminate H].
  exists r, hargs, hargs0, st1. split; [exact SSH|]. split; [reflexivity|]. split; [exact SAO|]. split; [reflexivity|]. split; [reflexivity|].
  destruct (fresh (clobber st1)) as [v st3] eqn:F. injection H as <-. reflexivity.
Qed.

Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Hypothesis IMGSH_aci : forall v a, In v Op.SHLIT -> fst v <= a < snd v -> exists a', in_ranges (aci AI) a' /\ a = shad a'.
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

Hypothesis OPS_stk_sh_zero : forall id args m mo a, id <> HEAP_ID -> op_holds OPS id args m mo ->
  Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) -> (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a') -> m (ALib.Mem.wa a) = Some (Z_to_bv 8 0).
Variable OTHER : Model -> Model -> Prop.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.
Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment asegs a 1 = Some seg) -> op_cov0 OPS a.
Hypothesis OPS_holds_ssh : forall m mo, op_holds OPS ActrB.SSH_ID [] m mo -> StackSh.ssh_holds m.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable NMAXt : nat.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).
Variable ENTRY : Z.
Hypothesis WALK : hnr_walk_stmt AI AI_fake ENTRY.
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Hypothesis ACCT_rng_stk_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (shad ATOP) (Shadow.KHIGH - shad ATOP).
Hypothesis ACCT_frng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> FRNG AI AI_fake L RNG.
Definition acct_leaf_silent (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock)
    (r : unit) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo', mrel A' moc' mo' -> MP mo' /\ op_minv OPS mo' /\ OTHER mo0 mo' /\ ACCT aw L RNG' st LBa mo'.
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent mo aw L st LBa).

Theorem hnr_sound : forall pc, to_Z pc = ENTRY -> contract_sound asegs OPS MP PB (ActrB.hnr_c pc ActrA.ATPi).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc ActrB.hnr_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = ENTRY) by (rewrite Hspc; exact Hpc).
  destruct (hnr_apply_shape ActrA.ATPi st sts Happ) as (r & hargs & hargs0 & st1 & SSHP & FO0 & SAO & PREB & FS0 & ESTS).
  destruct (acall_pre_bridge 12288%uint63 st r hargs st1 PREB FS0) as [wnl PRE].
  destruct (CtrPre.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng 12288%uint63 None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  set (R := ms_regs ms) in *. set (spw := AP.getr R 2) in *. set (sp := bv_unsigned spw) in *.
  pose proof atop_range as ATR.

  assert (SPA : bv_unsigned (AP.getr (ms_regs ms) 2%bv) <= al_top L).
  { destruct (CtrPre.acall_pre_inv 12288%uint63 None st r hargs wnl st1 PRE) as (tp0 & _ & _ & HW0 & _ & _ & SFO & _).
    pose proof (aheap_windows_hargs st hargs wnl HW0) as FH. rewrite FO0 in FH. injection FH as ->.
    exact (CtrPre.acall_sp_altop AI ACCT UNIV Cw OPS E st ms mo r hargs wnl L RNG sta LBa aw HS CF AH SPT SFO SAO). }
  fold R in SPA. fold spw in SPA. fold sp in SPA.
  destruct (AI_layout AI _ _ _ _ _ AH) as (_ & _ & TOP47 & _).
  change (to_Z 12288%uint63) with 12288 in LOR.
  destruct (AI_layout AI _ _ _ _ _ AH) as (_ & T4096 & _).
  set (bot := HN.hnr_bottom spw) in *.
  assert (BOTB : sp - 8256 < bot <= sp - 4160 /\ bot mod 4096 = 0).
  { unfold bot, HN.hnr_bottom. fold sp. split; [Z.div_mod_to_equations; lia| apply Z.mod_mul; lia]. }
  destruct BOTB as [BOTB B4096].
  set (len := shlen (al_top L - bot)) in *.
  assert (SHE : forall x, shad x = ASHOFF + x / 8) by (intros x; unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (LENE : len = (al_top L - bot) / 8) by (unfold len, shlen; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHTOP : shad bot + len = shad (al_top L)) by (rewrite LENE, !SHE; clear - T4096 B4096; Z.div_mod_to_equations; lia).
  assert (SHB : shad ATOP <= shad bot /\ shad (al_top L) <= Shadow.KHIGH /\ 0x100000000000 <= shad ATOP /\ 0 <= len).
  { unfold Shadow.KHIGH. rewrite LENE, !SHE. unfold ASHOFF. clear - BOTB BOT LOR TOP47 ATR SPA. Z.div_mod_to_equations. lia. }
  destruct SHB as (SHB1 & SHB2 & SHB3 & LEN0).

  assert (SSH : StackSh.ssh_holds (ms_mem ms)).
  { unfold ActrB.ssh_present in SSHP. destruct (find_op ActrB.SSH_ID (s_ops st)) as [[|? ?]|] eqn:FZ; try discriminate SSHP.
    pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (find_op_In _ _ _ FZ)) as HO. cbn [op_id op_args map] in HO.
    exact (OPS_holds_ssh _ _ HO). }
  destruct (UnreggLib.mapped_chunk asegs (ms_mem ms) (Z.to_nat len) (shad bot) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; unfold Shadow.KHIGH in SHB2; lia)) as [junk CHUNK].
  { intros i Hi. rewrite Z2Nat.id in Hi by lia.
    assert (WBI : wb asegs (ms_mem ms) (shad bot + i) = true) by (apply SSH; lia).
    split; [exact WBI| apply SmLib.shmap_rb; [unfold Shadow.KHIGH in SHB2; lia| exact WBI]]. }
  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  assert (RNG1 : rng RNG (CtrPre.sp_lo E st) (al_top L - CtrPre.sp_lo E st)) by (eapply rng_sub'; [exact (ACCT_rng _ _ _ _ _ _ AC)| lia]).
  assert (RNG2 : rng RNG (shad bot) len) by (eapply rng_sub'; [exact (ACCT_rng_stk_sh _ _ _ _ _ _ AC)| lia]).
  pose proof (WALK L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31)
                (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) sta LBa (CtrPre.sp_lo E st) junk AH MI ST BOT LOR SPA TP CHUNK
                RNG1 (ACCT_rng_aimg _ _ _ _ _ _ AC) (ACCT_frng _ _ _ _ _ _ AC) RNG2) as EV.
  rewrite Ems, HPC. apply (GlueA.realizes_to_mkRA asegs).
  eapply (implS_twfS_realizes_silent asegs NMAXt (Ret (Exc.Ok tt)) RNG AL0
            (fun (_ : unit) (RNGq : footprint) ms' => RNGq = RNG /\ hnr_postA AI L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) sta LBa (CtrPre.sp_lo E st) (ms_mem ms) ms')
            _ _ moc mo K).
  - cbn [implF epostF]. eapply evtF_mono; [exact EV|]. intros ms' PO. split; [reflexivity| exact PO].
  - exact TW.
  - exact HH.
  - exact MINV.
  - exact MR.
  - intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV' MR'.
    destruct (HP' mo' MR') as (HMP' & HMI' & OTH & ACP). destruct HQ as [-> HQ].
    destruct HQ as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MINV'' & STK' & AH' & TWP & PRESX & ZCHK).
    fold spw in PRESX, ZCHK. fold sp in PRESX. fold bot in PRESX, ZCHK. fold len in ZCHK.
    match type of EMS with ms' = MS ?RR _ _ _ _ _ _ => set (R' := RR) in * end.
    set (m := ms_mem ms) in *.
    set (Fv := CtrFree.cfvF R'). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0).
    destruct (HeapCtr.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WT0 & LT0 & ER).
    assert (EMS' : ms' = CtrFrame.ms' ms r R' m').
    { rewrite EMS. unfold CtrFrame.ms'. f_equal. fold R. rewrite RA. apply MState.ret_pc_even.
      - lia.
      - pose proof (HeapCtr.call_pre_even st r CP) as EV0.
        pose proof (land_mk r 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
        change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EV0 in LM. change (to_Z 0%uint63) with 0 in LM.
        change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }

    pose proof CF as CF0.
    destruct CF0 as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                    & NW & AN & AJ & TS & WF & HC & AWden & (Wt & WOF & ARW & TI)).
    destruct (clobber_fields st1) as (_ & FF & RV & RG & FS0' & OP & PV & NXc).
    destruct (CtrFrame.st1_fields st st1 FS) as (_ & _ & FF1 & RV1 & FS1 & OP1 & PV1 & NX1).
    assert (XE : s_next (clobber st1) = addn (s_next st) 15).
    { rewrite NXc, NX1. symmetry. destruct (CtrFrame.NX st FOK) as (_ & _ & B). pose proof (int_range (s_next st)) as RRn. rewrite two63_eq in RRn.
      apply addn_lit; [reflexivity| rewrite wB_two63, two63_eq; lia]. }
    assert (SHAPE : sts = [SS r (rf_set (s_rf (clobber st1)) X10 (VP (addn (s_next st) 15) wzero)) (s_ff st) (s_resv st) (s_regs st1) (s_facts st)
                              (s_ops st) (s_priv st) (PrimInt63.add (addn (s_next st) 15) 1%uint63)]).
    { rewrite ESTS. unfold fresh. cbn [fst snd]. rewrite XE. f_equal.
      assert (G : forall (S : sstate) nx1 v, setpc (setr (set_next S nx1) X10 v) r
                  = SS r (rf_set (s_rf S) X10 v) (s_ff S) (s_resv S) (s_regs S) (s_facts S) (s_ops S) (s_priv S) nx1) by (intros [] ? ?; reflexivity).
      rewrite G, FF, RV, RG, FS0', OP, PV, FF1, RV1, FS1, OP1, PV1. reflexivity. }
    apply (HK _ ltac:(rewrite SHAPE; left; reflexivity) (CtrFrame.E' E st Fv Gv) ms' mo' (CtrFrame.EXT E st Fv Gv) HMP').
    rewrite EMS'.

    set (X := fun a : Z => shad bot <= a < shad (al_top L)).
    assert (XB : forall a, X a -> shad ATOP <= a < shad (2 ^ 47)) by (intros a [X1 X2]; unfold Shadow.KHIGH in SHB2; change (shad (2 ^ 47)) with 0x10007fff8000; lia).
    assert (ZRB : forall a, X a -> rb asegs m' a = Some (Z_to_bv 8 0) /\ wb asegs m' a = true).
    { intros a [X1 X2]. destruct ZCHK as [[_ BY] (_ & _ & WV)]. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. destruct BY as (_ & _ & BY).
      cbn [cells_size csize Nat.add] in WV. rewrite Nat.add_0_r, Z2Nat.id in WV by lia.
      split.
      - specialize (BY (Z.to_nat (a - shad bot)) ltac:(rewrite repeat_length; lia)). rewrite Z2Nat.id in BY by lia. rewrite nth_error_repeat in BY by lia.
        replace (shad bot + (a - shad bot)) with a in BY by lia. exact BY.
      - apply (GlueA.wb_wviewA asegs). replace a with (shad bot + (a - shad bot)) by lia. apply WV. lia. }
    assert (STBx : forall LB0, aw_real AI ACCT UNIV aw LB0 m mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> CtrFrame.stableA AI ms LB0 a ->
              m' (AM.wa a) = m (AM.wa a)).
    { intros LB0 (W0 & (E1 & E2 & E3 & E4) & ARW0) a Ha ST0. pose proof ARW0 as [HW0 _]. pose proof HW0 as (_ & HT0 & _).
      destruct (LB_classify AI ACCT UNIV AI_fake W0 aw LB0 m mo HW0) as (KU & KT).
      apply (aw_real_stable_x AI ACCT UNIV AI_fake aw LB0 m mo W0 RNG sta LBa m' LBa LB0 sp X LBa TWP ltac:(intros b0 Hb0 _ _; rewrite <- E4; exact Hb0) ARW0).
      - rewrite E1. exact AH'.
      - intros a1' Ha1 CA NX. exact (proj1 (PRESX a1' Ha1 CA NX)).
      - exact XB.
      - lia.
      - intros v Hv. exact Hv.
      - intros v Hv UB P. destruct (KU v Hv UB P) as (b & Vb & ->). exists b. split; [rewrite <- E4; exact (proj1 Vb)| reflexivity].
      - intros v Hv NUB. destruct (KT v Hv NUB) as [(b & Hb & ->)|(b & Vb & ->)].
        + left. exists b. destruct (HT0 b Hb) as [HbL HH0]. split; [exact HbL|]. split; [rewrite <- E4; exact HbL|]. split; [exact HH0| reflexivity].
        + right. exists b. split; [exact (proj1 (proj1 Vb))|]. split; [rewrite <- E4; exact (proj1 (proj1 Vb))|]. split; [exact (proj2 Vb)| reflexivity].
      - exact Ha.
      - exact ST0. }
    assert (RAWV : forall a, m' (AM.wa a) = m (AM.wa a) -> rb asegs m' a = rb asegs m a /\ (wb asegs m a = true -> wb asegs m' a = true)).
    { intros a EQ. split; [unfold rb; unfold AM.wa in EQ; rewrite EQ; reflexivity|].
      intros Wb. apply (GlueA.wb_wviewA asegs). apply (GlueA.wb_wviewA asegs) in Wb. rewrite (wview_ext1 m' m _ EQ). exact Wb. }

    assert (CLX : forall a, 0 <= a < 2 ^ 64 -> aclient_addr (aci AI) LBa sp a -> ~ X a ->
              rb asegs m' a = rb asegs m a /\ (wb asegs m a = true -> wb asegs m' a = true)).
    { intros a Ha CA NX. apply RAWV. exact (proj1 (PRESX a Ha CA NX)). }
    assert (ACIX : forall a, in_ranges (aci AI) a -> ~ X (shad a) /\ ~ X a).
    { intros a (iv0 & Hi & RRa). pose proof (AI_aci_img AI iv0 Hi) as HIa. pose proof (AI_aci_lo AI iv0 Hi) as LOa.
      assert (SA : shad a < shad ATOP) by (rewrite !SHE; unfold AIMG_HI in HIa; clear - HIa RRa LOa ATR; Z.div_mod_to_equations; lia).
      unfold X. unfold AIMG_HI in HIa. split; lia. }

    assert (UNX : forall a, in_user LB a -> ~ X a).
    { intros a IU XA. destruct (XB a XA) as [XA1 XA2]. change (shad (2 ^ 47)) with 0x10007fff8000 in XA2.
      pose proof ARW as [HWW _]. pose proof HWW as (AHw & HTw & _).
      apply in_ivs_In in IU as (v & Hv & Hin). unfold in_iv in Hin.
      destruct (LB_cases AI ACCT UNIV Wt aw LB m mo v HWW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]]; cbn [fst snd user_iv twin_iv fsh_iv] in Hin.
      - destruct (blk_facts AI AI_fake _ _ _ _ _ b AHw (proj1 Vb)) as (NP & BK & TOPb & _). pose proof (usz_le b) as UL. unfold ablk, AIMG_HI, KLS in BK. lia.
      - destruct (HTw b Hb) as [HbL HbH]. destruct (blk_facts AI AI_fake _ _ _ _ _ b AHw HbL) as (NP & BK & TOPb & _).
        destruct (shadow_tight _ _ BK TOPb NP) as [T1 T2]. lia.
      - destruct (blk_facts AI AI_fake _ _ _ _ _ b AHw (proj1 (proj1 Vb))) as (NP & BK & TOPb & _).
        destruct (shadow_tight _ _ BK TOPb NP) as [T1 T2].
        assert (SL : shlen (ab_size b) <= shlen (ab_size b + 7)) by (unfold shlen; rewrite !Z.shiftr_div_pow2 by lia; apply Z.div_le_mono; lia). lia. }
    apply (CtrNoDelta.nodelta_st_ok AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other
             OPS_cov0_img E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' m' mo' RNG sta _ _ HS CP FS CF).
    --
      intros rg Hrg. unfold CtrFrame.kept_regsA in Hrg. cbn [In] in Hrg. repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]). destruct Hrg.
    -- intros x i Hx. exact (CtrFree.cfvF_clob R' x i Hx).
    -- rewrite HeapCtr.den_VPz. rewrite (CtrFrame.ev_E'_fresh E st FOK Fv Gv 15 ltac:(lia)). reflexivity.
    -- exact MINV''.
    -- exact STK'.
    --   intros LB0 AR0 a Ha STB. apply RAWV. exact (STBx LB0 AR0 a Ha STB).
    --   intros LB0 AR0 a Ha IU. apply (STBx LB0 AR0 a Ha). right; right. exact IU.
    --
      intros o a Ho NI Ha FP. unfold not_id in NI. apply Uint63.eqb_false_spec in NI.
      destruct (OPS_fp_other _ _ a NI FP) as [INA|[(a' & INA & ->)|(a' & STK & ->)]].
      + pose proof (proj1 (PRESX a ltac:(unfold two64 in Ha; lia) ltac:(right; left; exact INA) (proj2 (ACIX a INA)))) as E0. unfold AM.wa in E0. exact E0.
      + pose proof (proj1 (PRESX (shad a') ltac:(unfold two64 in Ha; lia) ltac:(right; right; right; exists a'; split; [right; left; exact INA| reflexivity]) (proj1 (ACIX a' INA)))) as E0.
        unfold AM.wa in E0. exact E0.
      +
        destruct (Z_lt_le_dec (shad a') (shad bot)) as [Q1|Q1]; [| destruct (Z_lt_le_dec (shad a') (shad (al_top L))) as [Q2|Q2]].
        * pose proof (proj1 (PRESX (shad a') ltac:(unfold two64 in Ha; lia) ltac:(right; right; right; exists a'; split; [left; exact STK| reflexivity]) ltac:(unfold X; lia))) as E0.
          unfold AM.wa in E0. exact E0.
        * assert (XA : X (shad a')) by (unfold X; lia). destruct (ZRB (shad a') XA) as [Z1 _].
          pose proof (XB (shad a') XA) as XR. change (shad (2 ^ 47)) with 0x10007fff8000 in XR.
          assert (R1 : m' (Z_to_bv 64 (shad a')) = Some (Z_to_bv 8 0)).
          { apply (RangePre.raw_of_view m' (shad a') _); [| exact Z1]. rewrite (SHE ATOP), (SHE a') in XR. rewrite (SHE a'). unfold ASHOFF in *. clear - XR ATR. Z.div_mod_to_equations; lia. }
          destruct (CtrFrame.SVB_parts st FOK) as (_ & _ & _ & _ & _ & OPB).
          rewrite (CtrFrame.map_den_E' E st Fv Gv _ (proj1 (forallb_forall _ _) OPB o Ho)) in FP.
          pose proof (OPS_stk_sh_zero (op_id o) (map (den E) (op_args o)) m mo (shad a') NI (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) o Ho) FP
                        (ex_intro _ a' (conj STK eq_refl))) as R0.
          unfold AM.wa in R0. rewrite R1. symmetry. exact R0.
        * pose proof (proj1 (PRESX (shad a') ltac:(unfold two64 in Ha; lia) ltac:(right; right; right; exists a'; split; [left; exact STK| reflexivity]) ltac:(unfold X; lia))) as E0.
          unfold AM.wa in E0. exact E0.
    --
      intros a Ha CC Wb.
      destruct (Z_lt_le_dec a (shad bot)) as [Q1|Q1]; [| destruct (Z_lt_le_dec a (shad (al_top L))) as [Q2|Q2]].
      + apply (CLX a ltac:(unfold two64 in Ha; lia)); [| unfold X; lia| exact Wb].
        destruct CC as [CC|[(a' & CC & ->)|(a' & CC & ->)]]; [right; left; exact CC| |]; right; right; right; exists a'; (split; [| reflexivity]); [right; left; exact CC| left; exact CC].
      + exact (proj2 (ZRB a (conj Q1 Q2))).
      + apply (CLX a ltac:(unfold two64 in Ha; lia)); [| unfold X; lia| exact Wb].
        destruct CC as [CC|[(a' & CC & ->)|(a' & CC & ->)]]; [right; left; exact CC| |]; right; right; right; exists a'; (split; [| reflexivity]); [right; left; exact CC| left; exact CC].
    --
      intros a Ha SC IB.
      assert (CA : aclient_addr (aci AI) LBa sp a).
      { destruct SC as [(a' & RRa & ->)|(vv & Hv & RRa)].
        - right; right; right. exists a'. split; [left; exact RRa| reflexivity].
        - destruct (IMGSH_aci vv a Hv RRa) as (a' & INA & ->). right; right; right. exists a'. split; [right; left; exact INA| reflexivity]. }
      destruct (Z_lt_le_dec a (shad bot)) as [Q1|Q1]; [apply (CLX a Ha CA); unfold X; lia|].
      destruct (Z_lt_le_dec a (shad (al_top L))) as [Q2|Q2]; [| apply (CLX a Ha CA); unfold X; lia].

      assert (XA : X a) by (split; assumption). destruct (ZRB a XA) as [ZR ZW]. split; [| intros _; exact ZW]. rewrite ZR.
      destruct (XB a XA) as [XA1 XA2]. change (shad (2 ^ 47)) with 0x10007fff8000 in XA2.
      destruct IB as (k & rgk & Hk & KZ & RNGa).
      assert (KN0 : k <> 0%uint63) by (intros ->; discriminate KZ).
      assert (INWIN : forall k0 len0 kd, CtrA.win_lookup wnl k0 = Some (len0, kd) ->
                bv_unsigned (ev E k0) <= a < bv_unsigned (ev E k0) + bv_unsigned (den E len0) -> False).
      { intros k0 len0 kd WL Hin.
        destruct (HeapCtrB.nonstack_windows_In E nn rest wnl k0 len0 kd NW (HeapCtrB.win_lookup_In _ _ _ _ WL)) as (_ & _ & KD & INW).
        apply (UNX a); [| exact XA].
        pose proof (proj1 (Forall_forall _ _) WF _ INW) as (W1' & W2' & W3' & [[KS0 _]|[[KB B]|[KS2 (b & Hb & SUB)]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *.
        - exfalso. exact (KD KS0).
        - apply in_ivs_In. eexists. split; [exact B|]. unfold in_iv. cbn [fst snd]. lia.
        - apply in_ivs_In. exists b. split; [exact Hb|]. apply SUB. unfold in_iv. cbn [fst snd]. lia. }
      pose proof (CallA.aregion_just_sound asegs OPS E st ms mo wnl ks offs rss k rgk HS SPR AJ Hk KN0) as JU.
      destruct (CallA.sp_region_inv st ks offs rss SPR) as (_ & Hrs & _).
      assert (ZV0 : forall hs, zero_view rgk = Some hs -> Some (Z_to_bv 8 0) = rb asegs m a).
      { intros hs ZV. pose proof (so_reg _ _ _ _ _ _ HS k rgk Hk) as RO.
        assert (ZVI : rg_bg rgk = BGZero /\ rg_cells rgk = IMap.Leaf).
        { unfold zero_view in ZV. destruct (rg_hi rgk); try discriminate ZV. destruct (rg_bg rgk); try discriminate ZV. destruct (rg_cells rgk); try discriminate ZV. auto. }
        destruct ZVI as [BGZ RCL].
        pose proof (ro_bg _ _ _ _ _ _ RO (a - bv_unsigned (ev E k)) ltac:(intros _; lia) ltac:(intros KK; rewrite KK in KZ; discriminate KZ)) as BG.
        assert (UNC : uncovered rgk (a - bv_unsigned (ev E k))) by (intros g gr _ FF0; rewrite RCL in FF0; discriminate FF0).
        specialize (BG UNC). unfold bg_byte in BG. rewrite BGZ in BG. replace (bv_unsigned (ev E k) + (a - bv_unsigned (ev E k))) with a in BG by lia.
        symmetry. exact BG. }
      destruct JU as [[EQ TOPk]|[NE [(len0 & kd0 & WLS & LZ & HZ)|[[J1 J2]|VJ]]]].
      + exfalso. subst k. rewrite Hrs in Hk. injection Hk as <-. lia.
      + exfalso. apply (INWIN k len0 kd0 WLS). rewrite LZ in RNGa. lia.
      + exfalso. rewrite (CtrFrame.SP_den OPS E st ms mo HS) in J1. fold R in J1. fold spw in J1. fold sp in J1. lia.
      +
        destruct VJ as [VJ|SL]; [| exfalso; pose proof (CtrPre.sliver_low OPS E st ms mo ks offs rss k rgk hargs nn md A nw rest LB a HS SPR Hk KN0 NE SL Hf Eh Tnw Nn Ln WF RNGa) as SLO; lia].
        pose proof (CallV.view_just_sound asegs OPS E st ms mo wnl ks offs rss k rgk HS SPR Hk KN0 VJ) as VS. unfold CallV.view_sem in VS. cbv zeta in VS.
        destruct VS as [((hs & ZV) & _)|[(hs & n0 & sh & len1 & ZV & _)|[(VI & v & Hv & V1 & V2)|(shD & kbD & nD & lenD & WLD & BTD & WLkD & STD & TND & ROD & LOD & HID)]]].
        * exact (ZV0 hs ZV).
        * exact (ZV0 hs ZV).
        * exfalso. unfold ActrA.IMGSH in Hv. cbn [In] in Hv. destruct Hv as [<-|[]]. cbn [fst snd] in V1, V2. clear - V1 V2 RNGa XA1 SHB3. lia.
        *   exfalso. apply (INWIN shD lenD ActrA.K_TWIN WLD). lia.
    -- exact AH'.
    -- exact ACP.
    --
      intros b x Hb FK Hx. pose proof (Op.blk_band AI AI_fake L RNG sta LBa m b x AH Hb Hx) as BB.
      assert (NX : ~ X x).
      { intros XA. destruct (XB x XA) as [XA1 XA2]. change (shad (2 ^ 47)) with 0x10007fff8000 in XA2. unfold AIMG_HI, KLS in BB. lia. }
      exact (proj1 (PRESX x ltac:(unfold AIMG_HI, KLS in BB; lia) ltac:(right; right; left; exists b; split; [exact Hb| exact Hx]) NX)).
    -- exact TWP.
    -- exact OTH.
    -- exact HMI'.
    -- exact (fun P => P).
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
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Import Actr.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import ActrB.TwinB SmShape.TwinB.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.
Module HN := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_hnrP.TwinB.

Definition hnr_postA {rc : runConstT} (AI : AMallocIface2) (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (MState.ret_pc ra) fc None m' (seg_rom bsegs)
    /\ AM.mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ AHEAP AI L RNG st LB m'
    /\ twins_pres LB m m'
    /\ (forall a, 0 <= a < 2^64 -> aclient_addr (aci AI) LB (bv_unsigned sp) a ->
          ~ (shad (HN.hnr_bottom sp) <= a < shad (al_top L)) ->
          m' (AM.wa a) = m (AM.wa a) /\ (wview bsegs m (AM.wa a) <> None -> wview bsegs m' (AM.wa a) <> None))
    /\ AS.rw_cells bsegs m' (shad (HN.hnr_bottom sp))
         [CB (Z.to_nat (shlen (al_top L - HN.hnr_bottom sp))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (al_top L - HN.hnr_bottom sp))))].

Definition hnr_walk_stmt {rc : runConstT} (AI : AMallocIface2) (AI_fake : AI_fake_law AI) (entry : Z) : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z) (junk : list byte),
  AHEAP AI L RNG st LB m ->
  AM.mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - 12288 ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  AS.rw_cells bsegs m (shad (HN.hnr_bottom sp)) [CB (Z.to_nat (shlen (al_top L - HN.hnr_bottom sp))) junk] ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> FRNG AI AI_fake L RNG ->
  rng RNG (shad (HN.hnr_bottom sp)) (shlen (al_top L - HN.hnr_bottom sp)) ->
  evtF bsegs RNG (hnr_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 entry) fc None m (seg_rom bsegs)).

Lemma hnr_apply_shape : forall TP st sts, ActrB.TwinB.ActrB.hnr_apply TP st = Some sts ->
  exists r hargs hargs0 st1, ActrB.TwinB.ActrB.ssh_present st = true /\ find_op HEAP_ID (s_ops st) = Some hargs0 /\ ActrA.sp_altop_ok st hargs0 = true
    /\ ActrB.TwinB.ActrB.acall_pre TP 12288%uint63 st = Some (r, hargs)
    /\ ActrA.forget_stack_below_sp_g st = Some st1
    /\ sts = [setpc (setr (snd (fresh (clobber st1))) X10 (VP (fst (fresh (clobber st1))) wzero)) r].
Proof.
  intros TP st sts H. unfold ActrB.TwinB.ActrB.hnr_apply in H. destruct (find_op HEAP_ID (s_ops st)) as [hargs0|] eqn:FO; [|discriminate H].
  destruct (ActrB.TwinB.ActrB.ssh_present st && ActrA.sp_altop_ok st hargs0)%bool eqn:CK; [|discriminate H]. apply andb_prop in CK as [SSH SAO].
  unfold ActrB.TwinB.ActrB.void_call_apply in H. destruct (ActrB.TwinB.ActrB.acall_pre TP 12288%uint63 st) as [[r hargs]|] eqn:PRE; [|discriminate H].
  unfold ActrB.TwinB.ActrB.forget_stack_below_sp_g in H. destruct (ActrA.forget_stack_below_sp_g st) as [st1|] eqn:FS; [|discriminate H].
  exists r, hargs, hargs0, st1. split; [exact SSH|]. split; [reflexivity|]. split; [exact SAO|]. split; [reflexivity|]. split; [reflexivity|].
  destruct (fresh (clobber st1)) as [v st3] eqn:F. injection H as <-. reflexivity.
Qed.

Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Hypothesis IMGSH_aci : forall v a, In v Op.TwinB.SHLIT -> fst v <= a < snd v -> exists a', in_ranges (aci AI) a' /\ a = shad a'.
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

Hypothesis OPS_stk_sh_zero : forall id args m mo a, id <> HEAP_ID -> op_holds OPS id args m mo ->
  Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) -> (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a') -> m (ALib.Mem.wa a) = Some (Z_to_bv 8 0).
Variable OTHER : Model -> Model -> Prop.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.
Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment bsegs a 1 = Some seg) -> op_cov0 OPS a.
Hypothesis OPS_holds_ssh : forall m mo, op_holds OPS ActrB.TwinB.ActrB.SSH_ID [] m mo -> StackSh.TwinB.ssh_holds m.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable NMAXt : nat.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).
Variable ENTRY : Z.
Hypothesis WALK : hnr_walk_stmt AI AI_fake ENTRY.
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Hypothesis ACCT_rng_stk_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (shad ATOP) (Shadow.KHIGH - shad ATOP).
Hypothesis ACCT_frng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> FRNG AI AI_fake L RNG.
Definition acct_leaf_silent (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock)
    (r : unit) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo', mrel A' moc' mo' -> MP mo' /\ op_minv OPS mo' /\ OTHER mo0 mo' /\ ACCT aw L RNG' st LBa mo'.
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent mo aw L st LBa).

Theorem hnr_sound : forall pc, to_Z pc = ENTRY -> contract_sound bsegs OPS MP PB (ActrB.TwinB.ActrB.hnr_c pc ActrA.ATPi).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc ActrB.TwinB.ActrB.hnr_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = ENTRY) by (rewrite Hspc; exact Hpc).
  destruct (hnr_apply_shape ActrA.ATPi st sts Happ) as (r & hargs & hargs0 & st1 & SSHP & FO0 & SAO & PREB & FS0 & ESTS).
  destruct (acall_pre_bridge 12288%uint63 st r hargs st1 PREB FS0) as [wnl PRE].
  destruct (CtrPre.TwinB.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng 12288%uint63 None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  set (R := ms_regs ms) in *. set (spw := AP.getr R 2) in *. set (sp := bv_unsigned spw) in *.
  pose proof atop_range as ATR.

  assert (SPA : bv_unsigned (AP.getr (ms_regs ms) 2%bv) <= al_top L).
  { destruct (CtrPre.TwinB.acall_pre_inv 12288%uint63 None st r hargs wnl st1 PRE) as (tp0 & _ & _ & HW0 & _ & _ & SFO & _).
    pose proof (aheap_windows_hargs st hargs wnl HW0) as FH. rewrite FO0 in FH. injection FH as ->.
    exact (CtrPre.TwinB.acall_sp_altop AI ACCT UNIV Cw OPS E st ms mo r hargs wnl L RNG sta LBa aw HS CF AH SPT SFO SAO). }
  fold R in SPA. fold spw in SPA. fold sp in SPA.
  destruct (AI_layout AI _ _ _ _ _ AH) as (_ & _ & TOP47 & _).
  change (to_Z 12288%uint63) with 12288 in LOR.
  destruct (AI_layout AI _ _ _ _ _ AH) as (_ & T4096 & _).
  set (bot := HN.hnr_bottom spw) in *.
  assert (BOTB : sp - 8256 < bot <= sp - 4160 /\ bot mod 4096 = 0).
  { unfold bot, HN.hnr_bottom. fold sp. split; [Z.div_mod_to_equations; lia| apply Z.mod_mul; lia]. }
  destruct BOTB as [BOTB B4096].
  set (len := shlen (al_top L - bot)) in *.
  assert (SHE : forall x, shad x = ASHOFF + x / 8) by (intros x; unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (LENE : len = (al_top L - bot) / 8) by (unfold len, shlen; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHTOP : shad bot + len = shad (al_top L)) by (rewrite LENE, !SHE; clear - T4096 B4096; Z.div_mod_to_equations; lia).
  assert (SHB : shad ATOP <= shad bot /\ shad (al_top L) <= Shadow.KHIGH /\ 0x100000000000 <= shad ATOP /\ 0 <= len).
  { unfold Shadow.KHIGH. rewrite LENE, !SHE. unfold ASHOFF. clear - BOTB BOT LOR TOP47 ATR SPA. Z.div_mod_to_equations. lia. }
  destruct SHB as (SHB1 & SHB2 & SHB3 & LEN0).

  assert (SSH : StackSh.TwinB.ssh_holds (ms_mem ms)).
  { unfold ActrB.TwinB.ActrB.ssh_present in SSHP. destruct (find_op ActrB.TwinB.ActrB.SSH_ID (s_ops st)) as [[|? ?]|] eqn:FZ; try discriminate SSHP.
    pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (find_op_In _ _ _ FZ)) as HO. cbn [op_id op_args map] in HO.
    exact (OPS_holds_ssh _ _ HO). }
  destruct (UnreggLib.TwinB.mapped_chunk bsegs (ms_mem ms) (Z.to_nat len) (shad bot) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; unfold Shadow.KHIGH in SHB2; lia)) as [junk CHUNK].
  { intros i Hi. rewrite Z2Nat.id in Hi by lia.
    assert (WBI : wb bsegs (ms_mem ms) (shad bot + i) = true) by (apply SSH; lia).
    split; [exact WBI| apply SmLib.TwinB.shmap_rb; [unfold Shadow.KHIGH in SHB2; lia| exact WBI]]. }
  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  assert (RNG1 : rng RNG (CtrPre.TwinB.sp_lo E st) (al_top L - CtrPre.TwinB.sp_lo E st)) by (eapply rng_sub'; [exact (ACCT_rng _ _ _ _ _ _ AC)| lia]).
  assert (RNG2 : rng RNG (shad bot) len) by (eapply rng_sub'; [exact (ACCT_rng_stk_sh _ _ _ _ _ _ AC)| lia]).
  pose proof (WALK L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31)
                (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) sta LBa (CtrPre.TwinB.sp_lo E st) junk AH MI ST BOT LOR SPA TP CHUNK
                RNG1 (ACCT_rng_aimg _ _ _ _ _ _ AC) (ACCT_frng _ _ _ _ _ _ AC) RNG2) as EV.
  rewrite Ems, HPC. apply (GlueA.TwinB.realizes_to_mkRA bsegs).
  eapply (implS_twfS_realizes_silent bsegs NMAXt (Ret (Exc.Ok tt)) RNG AL0
            (fun (_ : unit) (RNGq : footprint) ms' => RNGq = RNG /\ hnr_postA AI L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) sta LBa (CtrPre.TwinB.sp_lo E st) (ms_mem ms) ms')
            _ _ moc mo K).
  - cbn [implF epostF]. eapply evtF_mono; [exact EV|]. intros ms' PO. split; [reflexivity| exact PO].
  - exact TW.
  - exact HH.
  - exact MINV.
  - exact MR.
  - intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV' MR'.
    destruct (HP' mo' MR') as (HMP' & HMI' & OTH & ACP). destruct HQ as [-> HQ].
    destruct HQ as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MINV'' & STK' & AH' & TWP & PRESX & ZCHK).
    fold spw in PRESX, ZCHK. fold sp in PRESX. fold bot in PRESX, ZCHK. fold len in ZCHK.
    match type of EMS with ms' = MS ?RR _ _ _ _ _ _ => set (R' := RR) in * end.
    set (m := ms_mem ms) in *.
    set (Fv := CtrFree.TwinB.cfvF R'). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0).
    destruct (HeapCtr.TwinB.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WT0 & LT0 & ER).
    assert (EMS' : ms' = CtrFrame.TwinB.ms' ms r R' m').
    { rewrite EMS. unfold CtrFrame.TwinB.ms'. f_equal. fold R. rewrite RA. apply MState.ret_pc_even.
      - lia.
      - pose proof (HeapCtr.TwinB.call_pre_even st r CP) as EV0.
        pose proof (land_mk r 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
        change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EV0 in LM. change (to_Z 0%uint63) with 0 in LM.
        change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }

    pose proof CF as CF0.
    destruct CF0 as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                    & NW & AN & AJ & TS & WF & HC & AWden & (Wt & WOF & ARW & TI)).
    destruct (clobber_fields st1) as (_ & FF & RV & RG & FS0' & OP & PV & NXc).
    destruct (CtrFrame.TwinB.st1_fields st st1 FS) as (_ & _ & FF1 & RV1 & FS1 & OP1 & PV1 & NX1).
    assert (XE : s_next (clobber st1) = addn (s_next st) 15).
    { rewrite NXc, NX1. symmetry. destruct (CtrFrame.TwinB.NX st FOK) as (_ & _ & B). pose proof (int_range (s_next st)) as RRn. rewrite two63_eq in RRn.
      apply addn_lit; [reflexivity| rewrite wB_two63, two63_eq; lia]. }
    assert (SHAPE : sts = [SS r (rf_set (s_rf (clobber st1)) X10 (VP (addn (s_next st) 15) wzero)) (s_ff st) (s_resv st) (s_regs st1) (s_facts st)
                              (s_ops st) (s_priv st) (PrimInt63.add (addn (s_next st) 15) 1%uint63)]).
    { rewrite ESTS. unfold fresh. cbn [fst snd]. rewrite XE. f_equal.
      assert (G : forall (S : sstate) nx1 v, setpc (setr (set_next S nx1) X10 v) r
                  = SS r (rf_set (s_rf S) X10 v) (s_ff S) (s_resv S) (s_regs S) (s_facts S) (s_ops S) (s_priv S) nx1) by (intros [] ? ?; reflexivity).
      rewrite G, FF, RV, RG, FS0', OP, PV, FF1, RV1, FS1, OP1, PV1. reflexivity. }
    apply (HK _ ltac:(rewrite SHAPE; left; reflexivity) (CtrFrame.TwinB.E' E st Fv Gv) ms' mo' (CtrFrame.TwinB.EXT E st Fv Gv) HMP').
    rewrite EMS'.

    set (X := fun a : Z => shad bot <= a < shad (al_top L)).
    assert (XB : forall a, X a -> shad ATOP <= a < shad (2 ^ 47)) by (intros a [X1 X2]; unfold Shadow.KHIGH in SHB2; change (shad (2 ^ 47)) with 0x10007fff8000; lia).
    assert (ZRB : forall a, X a -> rb bsegs m' a = Some (Z_to_bv 8 0) /\ wb bsegs m' a = true).
    { intros a [X1 X2]. destruct ZCHK as [[_ BY] (_ & _ & WV)]. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. destruct BY as (_ & _ & BY).
      cbn [cells_size csize Nat.add] in WV. rewrite Nat.add_0_r, Z2Nat.id in WV by lia.
      split.
      - specialize (BY (Z.to_nat (a - shad bot)) ltac:(rewrite repeat_length; lia)). rewrite Z2Nat.id in BY by lia. rewrite nth_error_repeat in BY by lia.
        replace (shad bot + (a - shad bot)) with a in BY by lia. exact BY.
      - apply (GlueA.TwinB.wb_wviewA bsegs). replace a with (shad bot + (a - shad bot)) by lia. apply WV. lia. }
    assert (STBx : forall LB0, aw_real AI ACCT UNIV aw LB0 m mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> CtrFrame.TwinB.stableA AI ms LB0 a ->
              m' (AM.wa a) = m (AM.wa a)).
    { intros LB0 (W0 & (E1 & E2 & E3 & E4) & ARW0) a Ha ST0. pose proof ARW0 as [HW0 _]. pose proof HW0 as (_ & HT0 & _).
      destruct (LB_classify AI ACCT UNIV AI_fake W0 aw LB0 m mo HW0) as (KU & KT).
      apply (aw_real_stable_x AI ACCT UNIV AI_fake aw LB0 m mo W0 RNG sta LBa m' LBa LB0 sp X LBa TWP ltac:(intros b0 Hb0 _ _; rewrite <- E4; exact Hb0) ARW0).
      - rewrite E1. exact AH'.
      - intros a1' Ha1 CA NX. exact (proj1 (PRESX a1' Ha1 CA NX)).
      - exact XB.
      - lia.
      - intros v Hv. exact Hv.
      - intros v Hv UB P. destruct (KU v Hv UB P) as (b & Vb & ->). exists b. split; [rewrite <- E4; exact (proj1 Vb)| reflexivity].
      - intros v Hv NUB. destruct (KT v Hv NUB) as [(b & Hb & ->)|(b & Vb & ->)].
        + left. exists b. destruct (HT0 b Hb) as [HbL HH0]. split; [exact HbL|]. split; [rewrite <- E4; exact HbL|]. split; [exact HH0| reflexivity].
        + right. exists b. split; [exact (proj1 (proj1 Vb))|]. split; [rewrite <- E4; exact (proj1 (proj1 Vb))|]. split; [exact (proj2 Vb)| reflexivity].
      - exact Ha.
      - exact ST0. }
    assert (RAWV : forall a, m' (AM.wa a) = m (AM.wa a) -> rb bsegs m' a = rb bsegs m a /\ (wb bsegs m a = true -> wb bsegs m' a = true)).
    { intros a EQ. split; [unfold rb; unfold AM.wa in EQ; rewrite EQ; reflexivity|].
      intros Wb. apply (GlueA.TwinB.wb_wviewA bsegs). apply (GlueA.TwinB.wb_wviewA bsegs) in Wb. rewrite (wview_ext1 m' m _ EQ). exact Wb. }

    assert (CLX : forall a, 0 <= a < 2 ^ 64 -> aclient_addr (aci AI) LBa sp a -> ~ X a ->
              rb bsegs m' a = rb bsegs m a /\ (wb bsegs m a = true -> wb bsegs m' a = true)).
    { intros a Ha CA NX. apply RAWV. exact (proj1 (PRESX a Ha CA NX)). }
    assert (ACIX : forall a, in_ranges (aci AI) a -> ~ X (shad a) /\ ~ X a).
    { intros a (iv0 & Hi & RRa). pose proof (AI_aci_img AI iv0 Hi) as HIa. pose proof (AI_aci_lo AI iv0 Hi) as LOa.
      assert (SA : shad a < shad ATOP) by (rewrite !SHE; unfold AIMG_HI in HIa; clear - HIa RRa LOa ATR; Z.div_mod_to_equations; lia).
      unfold X. unfold AIMG_HI in HIa. split; lia. }

    assert (UNX : forall a, in_user LB a -> ~ X a).
    { intros a IU XA. destruct (XB a XA) as [XA1 XA2]. change (shad (2 ^ 47)) with 0x10007fff8000 in XA2.
      pose proof ARW as [HWW _]. pose proof HWW as (AHw & HTw & _).
      apply in_ivs_In in IU as (v & Hv & Hin). unfold in_iv in Hin.
      destruct (LB_cases AI ACCT UNIV Wt aw LB m mo v HWW Hv) as [(b & Vb & ->)|[(b & Hb & ->)|(b & Vb & ->)]]; cbn [fst snd user_iv twin_iv fsh_iv] in Hin.
      - destruct (blk_facts AI AI_fake _ _ _ _ _ b AHw (proj1 Vb)) as (NP & BK & TOPb & _). pose proof (usz_le b) as UL. unfold ablk, AIMG_HI, KLS in BK. lia.
      - destruct (HTw b Hb) as [HbL HbH]. destruct (blk_facts AI AI_fake _ _ _ _ _ b AHw HbL) as (NP & BK & TOPb & _).
        destruct (shadow_tight _ _ BK TOPb NP) as [T1 T2]. lia.
      - destruct (blk_facts AI AI_fake _ _ _ _ _ b AHw (proj1 (proj1 Vb))) as (NP & BK & TOPb & _).
        destruct (shadow_tight _ _ BK TOPb NP) as [T1 T2].
        assert (SL : shlen (ab_size b) <= shlen (ab_size b + 7)) by (unfold shlen; rewrite !Z.shiftr_div_pow2 by lia; apply Z.div_le_mono; lia). lia. }
    apply (CtrNoDelta.TwinB.nodelta_st_ok AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other
             OPS_cov0_img E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' m' mo' RNG sta _ _ HS CP FS CF).
    --
      intros rg Hrg. unfold CtrFrame.TwinB.kept_regsA in Hrg. cbn [In] in Hrg. repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]). destruct Hrg.
    -- intros x i Hx. exact (CtrFree.TwinB.cfvF_clob R' x i Hx).
    -- rewrite HeapCtr.TwinB.den_VPz. rewrite (CtrFrame.TwinB.ev_E'_fresh E st FOK Fv Gv 15 ltac:(lia)). reflexivity.
    -- exact MINV''.
    -- exact STK'.
    --   intros LB0 AR0 a Ha STB. apply RAWV. exact (STBx LB0 AR0 a Ha STB).
    --   intros LB0 AR0 a Ha IU. apply (STBx LB0 AR0 a Ha). right; right. exact IU.
    --
      intros o a Ho NI Ha FP. unfold not_id in NI. apply Uint63.eqb_false_spec in NI.
      destruct (OPS_fp_other _ _ a NI FP) as [INA|[(a' & INA & ->)|(a' & STK & ->)]].
      + pose proof (proj1 (PRESX a ltac:(unfold two64 in Ha; lia) ltac:(right; left; exact INA) (proj2 (ACIX a INA)))) as E0. unfold AM.wa in E0. exact E0.
      + pose proof (proj1 (PRESX (shad a') ltac:(unfold two64 in Ha; lia) ltac:(right; right; right; exists a'; split; [right; left; exact INA| reflexivity]) (proj1 (ACIX a' INA)))) as E0.
        unfold AM.wa in E0. exact E0.
      +
        destruct (Z_lt_le_dec (shad a') (shad bot)) as [Q1|Q1]; [| destruct (Z_lt_le_dec (shad a') (shad (al_top L))) as [Q2|Q2]].
        * pose proof (proj1 (PRESX (shad a') ltac:(unfold two64 in Ha; lia) ltac:(right; right; right; exists a'; split; [left; exact STK| reflexivity]) ltac:(unfold X; lia))) as E0.
          unfold AM.wa in E0. exact E0.
        * assert (XA : X (shad a')) by (unfold X; lia). destruct (ZRB (shad a') XA) as [Z1 _].
          pose proof (XB (shad a') XA) as XR. change (shad (2 ^ 47)) with 0x10007fff8000 in XR.
          assert (R1 : m' (Z_to_bv 64 (shad a')) = Some (Z_to_bv 8 0)).
          { apply (RangePre.TwinB.raw_of_view m' (shad a') _); [| exact Z1]. rewrite (SHE ATOP), (SHE a') in XR. rewrite (SHE a'). unfold ASHOFF in *. clear - XR ATR. Z.div_mod_to_equations; lia. }
          destruct (CtrFrame.TwinB.SVB_parts st FOK) as (_ & _ & _ & _ & _ & OPB).
          rewrite (CtrFrame.TwinB.map_den_E' E st Fv Gv _ (proj1 (forallb_forall _ _) OPB o Ho)) in FP.
          pose proof (OPS_stk_sh_zero (op_id o) (map (den E) (op_args o)) m mo (shad a') NI (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) o Ho) FP
                        (ex_intro _ a' (conj STK eq_refl))) as R0.
          unfold AM.wa in R0. rewrite R1. symmetry. exact R0.
        * pose proof (proj1 (PRESX (shad a') ltac:(unfold two64 in Ha; lia) ltac:(right; right; right; exists a'; split; [left; exact STK| reflexivity]) ltac:(unfold X; lia))) as E0.
          unfold AM.wa in E0. exact E0.
    --
      intros a Ha CC Wb.
      destruct (Z_lt_le_dec a (shad bot)) as [Q1|Q1]; [| destruct (Z_lt_le_dec a (shad (al_top L))) as [Q2|Q2]].
      + apply (CLX a ltac:(unfold two64 in Ha; lia)); [| unfold X; lia| exact Wb].
        destruct CC as [CC|[(a' & CC & ->)|(a' & CC & ->)]]; [right; left; exact CC| |]; right; right; right; exists a'; (split; [| reflexivity]); [right; left; exact CC| left; exact CC].
      + exact (proj2 (ZRB a (conj Q1 Q2))).
      + apply (CLX a ltac:(unfold two64 in Ha; lia)); [| unfold X; lia| exact Wb].
        destruct CC as [CC|[(a' & CC & ->)|(a' & CC & ->)]]; [right; left; exact CC| |]; right; right; right; exists a'; (split; [| reflexivity]); [right; left; exact CC| left; exact CC].
    --
      intros a Ha SC IB.
      assert (CA : aclient_addr (aci AI) LBa sp a).
      { destruct SC as [(a' & RRa & ->)|(vv & Hv & RRa)].
        - right; right; right. exists a'. split; [left; exact RRa| reflexivity].
        - destruct (IMGSH_aci vv a Hv RRa) as (a' & INA & ->). right; right; right. exists a'. split; [right; left; exact INA| reflexivity]. }
      destruct (Z_lt_le_dec a (shad bot)) as [Q1|Q1]; [apply (CLX a Ha CA); unfold X; lia|].
      destruct (Z_lt_le_dec a (shad (al_top L))) as [Q2|Q2]; [| apply (CLX a Ha CA); unfold X; lia].

      assert (XA : X a) by (split; assumption). destruct (ZRB a XA) as [ZR ZW]. split; [| intros _; exact ZW]. rewrite ZR.
      destruct (XB a XA) as [XA1 XA2]. change (shad (2 ^ 47)) with 0x10007fff8000 in XA2.
      destruct IB as (k & rgk & Hk & KZ & RNGa).
      assert (KN0 : k <> 0%uint63) by (intros ->; discriminate KZ).
      assert (INWIN : forall k0 len0 kd, CtrA.win_lookup wnl k0 = Some (len0, kd) ->
                bv_unsigned (ev E k0) <= a < bv_unsigned (ev E k0) + bv_unsigned (den E len0) -> False).
      { intros k0 len0 kd WL Hin.
        destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl k0 len0 kd NW (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WL)) as (_ & _ & KD & INW).
        apply (UNX a); [| exact XA].
        pose proof (proj1 (Forall_forall _ _) WF _ INW) as (W1' & W2' & W3' & [[KS0 _]|[[KB B]|[KS2 (b & Hb & SUB)]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *.
        - exfalso. exact (KD KS0).
        - apply in_ivs_In. eexists. split; [exact B|]. unfold in_iv. cbn [fst snd]. lia.
        - apply in_ivs_In. exists b. split; [exact Hb|]. apply SUB. unfold in_iv. cbn [fst snd]. lia. }
      pose proof (CallA.TwinB.aregion_just_sound bsegs OPS E st ms mo wnl ks offs rss k rgk HS SPR AJ Hk KN0) as JU.
      destruct (CallA.TwinB.sp_region_inv st ks offs rss SPR) as (_ & Hrs & _).
      assert (ZV0 : forall hs, zero_view rgk = Some hs -> Some (Z_to_bv 8 0) = rb bsegs m a).
      { intros hs ZV. pose proof (so_reg _ _ _ _ _ _ HS k rgk Hk) as RO.
        assert (ZVI : rg_bg rgk = BGZero /\ rg_cells rgk = IMap.Leaf).
        { unfold zero_view in ZV. destruct (rg_hi rgk); try discriminate ZV. destruct (rg_bg rgk); try discriminate ZV. destruct (rg_cells rgk); try discriminate ZV. auto. }
        destruct ZVI as [BGZ RCL].
        pose proof (ro_bg _ _ _ _ _ _ RO (a - bv_unsigned (ev E k)) ltac:(intros _; lia) ltac:(intros KK; rewrite KK in KZ; discriminate KZ)) as BG.
        assert (UNC : uncovered rgk (a - bv_unsigned (ev E k))) by (intros g gr _ FF0; rewrite RCL in FF0; discriminate FF0).
        specialize (BG UNC). unfold bg_byte in BG. rewrite BGZ in BG. replace (bv_unsigned (ev E k) + (a - bv_unsigned (ev E k))) with a in BG by lia.
        symmetry. exact BG. }
      destruct JU as [[EQ TOPk]|[NE [(len0 & kd0 & WLS & LZ & HZ)|[[J1 J2]|VJ]]]].
      + exfalso. subst k. rewrite Hrs in Hk. injection Hk as <-. lia.
      + exfalso. apply (INWIN k len0 kd0 WLS). rewrite LZ in RNGa. lia.
      + exfalso. rewrite (CtrFrame.TwinB.SP_den OPS E st ms mo HS) in J1. fold R in J1. fold spw in J1. fold sp in J1. lia.
      +
        destruct VJ as [VJ|SL]; [| exfalso; pose proof (CtrPre.TwinB.sliver_low OPS E st ms mo ks offs rss k rgk hargs nn md A nw rest LB a HS SPR Hk KN0 NE SL Hf Eh Tnw Nn Ln WF RNGa) as SLO; lia].
        pose proof (CallV.TwinB.view_just_sound bsegs OPS E st ms mo wnl ks offs rss k rgk HS SPR Hk KN0 VJ) as VS. unfold CallV.TwinB.view_sem in VS. cbv zeta in VS.
        destruct VS as [((hs & ZV) & _)|[(hs & n0 & sh & len1 & ZV & _)|[(VI & v & Hv & V1 & V2)|(shD & kbD & nD & lenD & WLD & BTD & WLkD & STD & TND & ROD & LOD & HID)]]].
        * exact (ZV0 hs ZV).
        * exact (ZV0 hs ZV).
        * exfalso. unfold ActrA.IMGSH in Hv. cbn [In] in Hv. destruct Hv as [<-|[]]. cbn [fst snd] in V1, V2. clear - V1 V2 RNGa XA1 SHB3. lia.
        *   exfalso. apply (INWIN shD lenD ActrA.K_TWIN WLD). lia.
    -- exact AH'.
    -- exact ACP.
    --
      intros b x Hb FK Hx. pose proof (Op.TwinB.blk_band AI AI_fake L RNG sta LBa m b x AH Hb Hx) as BB.
      assert (NX : ~ X x).
      { intros XA. destruct (XB x XA) as [XA1 XA2]. change (shad (2 ^ 47)) with 0x10007fff8000 in XA2. unfold AIMG_HI, KLS in BB. lia. }
      exact (proj1 (PRESX x ltac:(unfold AIMG_HI, KLS in BB; lia) ltac:(right; right; left; exists b; split; [exact Hb| exact Hx]) NX)).
    -- exact TWP.
    -- exact OTH.
    -- exact HMI'.
    -- exact (fun P => P).
Qed.
End Sound.
End TwinB.
