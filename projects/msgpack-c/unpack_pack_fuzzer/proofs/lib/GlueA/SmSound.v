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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_cnt AInstanceUF.
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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA GlueA CtrPre CtrFrame FakeLaw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require SmLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import ActrB SmShape SmWorld SmPost SmLive.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX ActrA.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.
Module UF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AInstanceUF.
Module FC := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_cnt.

Definition sm_postA {rc : runConstT} (AI : AMallocIface2) (AI_fake : AI_fake_law AI) (c n : Z) (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (LBk : list ablock) (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (MState.ret_pc ra) fc None m' (seg_rom asegs)
    /\ AM.mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres (aci AI) LBk (bv_unsigned sp) m m'
    /\ twins_pres LB m m'
    /\ AHEAP AI L RNG st (mkABlock (ABFake c) F n :: LBk) m'
    /\ (forall b, In b LBk -> In b LB) /\ (forall b, In b LB -> UF.fk_live L m sp b -> In b LBk)
    /\ F mod 64 = 0 /\ ablk F (F + n) /\ F + n <= ATOP
    /\ AS.rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB (Z.to_nat (n - 32)) junk; C8 (Z_to_bv 64 (FLG AI AI_fake L (mkABlock (ABFake c) F n)))]
    /\ AS.rw_cells asegs m' (shad F) (repeat (C8 (Z_to_bv 64 0)) (Z.to_nat (n / 64)))
    /\ rng RNG F n /\ rng RNG (shad F) (n / 8)
    /\ AS.rw_cells asegs m' (F + 24) [C8 sp].

Definition sm_walk_stmt {rc : runConstT} (AI : AMallocIface2) (AI_fake : AI_fake_law AI) (c n nfr entry : Z) : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP AI L RNG st LB m ->
  Z.of_nat (FC.fk_count c LB) < nfr ->
  (forall c' F n', In (mkABlock (ABFake c') F n') LB -> c' <= 2) ->
  AM.mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - 4096 ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> FRNG AI AI_fake L RNG ->
  evtF asegs RNG (sm_postA AI AI_fake c n L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Lemma fk_count_fakeb : forall c LB, (FC.fk_count c LB <= length (List.filter fakeb LB))%nat.
Proof.
  intros c LB. unfold FC.fk_count. induction LB as [|b LB IH]; [cbn; lia|]. cbn [List.filter].
  set (X := List.filter (FC.isfk c) LB) in *. set (Y := List.filter fakeb LB) in *.
  destruct b as [[p|c'] A n]; unfold FC.isfk, fakeb; cbn [ab_kind]; [exact IH|]. destruct (c' =? c); cbn [length]; lia.
Qed.
Lemma wins_of_length : forall E n ws, (length (wins_of E n ws) <= n)%nat.
Proof. intros E n. induction n as [|n IH]; intros ws; [cbn; lia|]. destruct ws as [|a [|b [|c ws']]]; cbn [wins_of length]; try lia. specialize (IH ws'). lia. Qed.

Lemma zero_cells_bytes : forall k, cells_bytes (repeat (C8 (Z_to_bv 64 0)) k) = repeat (Z_to_bv 8 0) (8 * k).
Proof.
  induction k as [|k IH]; [reflexivity|]. cbn [repeat cells_bytes]. rewrite IH. replace (8 * S k)%nat with (8 + 8 * k)%nat by lia.
  rewrite repeat_app. f_equal.
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
Variable OTHER : Model -> Model -> Prop.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.
Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment asegs a 1 = Some seg) -> op_cov0 OPS a.
Hypothesis Cw_ghost_grow_f : forall kd md ca LB ws m b n, kd = K_FRAMEz \/ kd = K_FTWINz -> cw_holds Cw md ca LB ws m ->
  (forall a, in_iv (b, n) a -> ~ in_user LB a) -> cw_holds Cw md ca ((b, n) :: LB) (ws ++ [Win b n kd]) m.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable NMAXt : nat.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).

Variable cls : int.
Hypothesis CLS2 : PrimInt63.leb cls 2%uint63 = true.
Variables (NFR ENTRY : Z).
Hypothesis NFR_big : 4096 <= NFR.
Hypothesis WALK : sm_walk_stmt AI AI_fake (to_Z cls) (fsize (to_Z cls)) NFR ENTRY.

Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Hypothesis ACCT_frng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> FRNG AI AI_fake L RNG.
Definition acct_leaf_frame_in (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock)
    (r : unit) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo', mrel A' moc' mo' -> MP mo' /\ op_minv OPS mo' /\ OTHER mo0 mo' /\
    forall c F n LBk, (forall id A sz, In (HB id A sz) LBa -> In (HB id A sz) LBk) -> ACCT aw L RNG' st (mkABlock (ABFake c) F n :: LBk) mo'.

Hypothesis ACCT_frame_in : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_frame_in mo aw L st LBa).
Theorem stack_malloc_sound : forall pc, to_Z pc = ENTRY -> contract_sound asegs OPS MP PB (ActrB.stack_malloc_c asegs pc ActrA.ATPi cls).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc ActrB.stack_malloc_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = ENTRY) by (rewrite Hspc; exact Hpc).
  destruct (sm_apply_shape asegs ActrA.ATPi cls st sts Happ) as (r & hargs & st1 & h1 & h2 & PREB & _ & FP & SAO & FS0 & H1 & H2 & ->).
  destruct (acall_pre_bridge 4096%uint63 st r hargs st1 PREB FS0) as [wnl PRE].
  destruct (CtrPre.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng 4096%uint63 None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  set (R := ms_regs ms) in *. set (c := to_Z cls) in *. set (n := fsize c) in *.
  pose proof atop_range as ATR.

  assert (SPA : bv_unsigned (AP.getr (ms_regs ms) 2%bv) <= al_top L).
  { destruct (CtrPre.acall_pre_inv 4096%uint63 None st r hargs wnl st1 PRE) as (tp0 & _ & _ & _ & _ & _ & SFO & _).
    exact (CtrPre.acall_sp_altop AI ACCT UNIV Cw OPS E st ms mo r hargs wnl L RNG sta LBa aw HS CF AH SPT SFO SAO). }
  fold R in SPA.
  destruct (AI_layout AI _ _ _ _ _ AH) as (_ & _ & TOP47 & _).

  pose proof CF as CF0.
  destruct CF0 as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
  destruct WOF as (E1 & E2 & E3 & E4).
  assert (NOTFULL : Z.of_nat (FC.fk_count c LBa) < NFR).
  { pose proof (aw_real_fake_count AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo W _ ARW TI) as FCN. rewrite E4 in FCN.
    pose proof (fk_count_fakeb c LBa) as X1. pose proof (wins_of_length E nn rest) as X2. unfold ZTOTAL in FCN. lia. }
  assert (CLSW : forall c' F n', In (mkABlock (ABFake c') F n') LBa -> c' <= 2).
  { intros c' F n' Hb. apply (aw_real_cls AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo W c' F n' ARW). rewrite E4. exact Hb. }
  destruct (ACCT_frame_in aw L RNG sta LBa mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  pose proof (WALK L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31)
                (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) sta LBa (CtrPre.sp_lo E st) AH NOTFULL CLSW MI ST BOT LO SPA TP
                ltac:(eapply rng_sub'; [exact (ACCT_rng _ _ _ _ _ _ AC)| lia]) (ACCT_rng_aimg _ _ _ _ _ _ AC) (ACCT_frng _ _ _ _ _ _ AC)) as EV.
  rewrite Ems, HPC. apply (GlueA.realizes_to_mkRA asegs).
  eapply (implS_twfS_realizes_silent asegs NMAXt (Ret (Exc.Ok tt)) RNG AL0
            (fun (_ : unit) (RNGq : footprint) ms' => RNGq = RNG /\ sm_postA AI AI_fake c n L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
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
    destruct HQ as (F & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & LBk & j0 & j1 & j2 & junk
                    & EMS & MINV'' & STK' & PRES & TWP & AH' & KEEP1 & KEEP2d & F64 & BKF & TOPF & FRM & SHD & RG1 & RG2 & RSW).
    match type of EMS with ms' = MS ?RR _ _ _ _ _ _ => set (R' := RR) in * end.
    destruct (HeapCtr.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WT0 & LT0 & ER).
    assert (EMS' : ms' = CtrFrame.ms' ms r R' m').
    { rewrite EMS. unfold CtrFrame.ms'. f_equal. fold R. rewrite RA. apply MState.ret_pc_even.
      - lia.
      - pose proof (HeapCtr.call_pre_even st r CP) as EV0.
        pose proof (land_mk r 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
        change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EV0 in LM. change (to_Z 0%uint63) with 0 in LM.
        change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }
    destruct (cls_lits cls CLS2) as (_ & _ & _ & NCASES). fold c in NCASES. fold n in NCASES.
    assert (LOWF : 0x62f000 <= F /\ F + n < 2 ^ 47) by (unfold ablk, AIMG_HI, KLS in BKF; lia).

    assert (ZSH : forall g, 0 <= g < n / 8 -> m' (AM.wa (shad F + g)) = Some (Z_to_bv 8 0)).
    { intros g Hg. destruct SHD as [[_ BY] _]. rewrite zero_cells_bytes in BY. destruct BY as (_ & _ & BY).
      assert (N8 : (8 * Z.to_nat (n / 64))%nat = Z.to_nat (n / 8)) by (destruct NCASES as [->|[->| ->]]; reflexivity).
      rewrite repeat_length, N8 in BY. specialize (BY (Z.to_nat g) ltac:(lia)). rewrite Z2Nat.id in BY by lia.
      rewrite nth_error_repeat in BY by lia.
      assert (SHLO : 0x62f000 <= shad F + g < 2 ^ 64).
      { unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. destruct NCASES as [Q|[Q|Q]]; rewrite Q in *; Z.div_mod_to_equations; lia. }
      apply (SmLib.raw_of_view m' (shad F + g) _ SHLO). exact BY. }
    assert (FLW : exists flg, AM.bytes_at asegs m' (F + n - 8) (AM.le8 (Z_to_bv 64 flg)) /\ flag_law AI L (mkABlock (ABFake c) F n) flg).
    { exists (FLG AI AI_fake L (mkABlock (ABFake c) F n)). split; [| exact (fk_law AI AI_fake L (mkABlock (ABFake c) F n) ltac:(exists c; reflexivity))].
      pose proof (FakeLaw.last_cell_bytes m' F j0 j1 j2 _ _ junk FRM) as BA. rewrite Z2Nat.id in BA by (destruct NCASES as [Q|[Q|Q]]; rewrite Q; lia).
      replace (F + n - 8) with (F + 24 + (n - 32)) by lia. exact BA. }
    pose proof (frames_live AI ACCT UNIV OPS AI_fake E st ms mo cls hargs L RNG sta LBa LBk HS Hf FP KEEP2d) as LIVE.
    destruct (sm_post_ok AI IMGX IMGX_aci IMGSH_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img Cw_ghost_grow_f
                st E ms mo cls r hargs wnl st1 h1 h2 L RNG sta LBa aw F R' m' mo' LBk HS CP FS CF CLS2 H1 H2
                ltac:(intros rg Hrg; unfold CtrFrame.kept_regsA in Hrg; cbn [In] in Hrg; repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]); destruct Hrg)
                eq_refl MINV'' STK' PRES TWP AH' (ACP c F n LBk (fun id A sz Hin => KEEP2d _ Hin (UF.fk_live_heap L (ms_mem ms) (AP.getr (ms_regs ms) 2%bv) id A sz))) KEEP1 LIVE F64 RSW ZSH FLW HMI' OTH) as (E1' & EXT & HSP).
    apply (HK _ ltac:(left; reflexivity) E1' ms' mo' EXT HMP'). rewrite EMS'. exact HSP.
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
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import ActrB.TwinB SmShape.TwinB SmWorld.TwinB SmPost.TwinB SmLive.TwinB.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX ActrA.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.
Module UF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AInstanceUF.TwinB.
Module FC := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_cnt.TwinB.

Definition sm_postA {rc : runConstT} (AI : AMallocIface2) (AI_fake : AI_fake_law AI) (c n : Z) (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (LBk : list ablock) (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (MState.ret_pc ra) fc None m' (seg_rom bsegs)
    /\ AM.mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres (aci AI) LBk (bv_unsigned sp) m m'
    /\ twins_pres LB m m'
    /\ AHEAP AI L RNG st (mkABlock (ABFake c) F n :: LBk) m'
    /\ (forall b, In b LBk -> In b LB) /\ (forall b, In b LB -> UF.fk_live L m sp b -> In b LBk)
    /\ F mod 64 = 0 /\ ablk F (F + n) /\ F + n <= ATOP
    /\ AS.rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB (Z.to_nat (n - 32)) junk; C8 (Z_to_bv 64 (FLG AI AI_fake L (mkABlock (ABFake c) F n)))]
    /\ AS.rw_cells bsegs m' (shad F) (repeat (C8 (Z_to_bv 64 0)) (Z.to_nat (n / 64)))
    /\ rng RNG F n /\ rng RNG (shad F) (n / 8)
    /\ AS.rw_cells bsegs m' (F + 24) [C8 sp].

Definition sm_walk_stmt {rc : runConstT} (AI : AMallocIface2) (AI_fake : AI_fake_law AI) (c n nfr entry : Z) : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP AI L RNG st LB m ->
  Z.of_nat (FC.fk_count c LB) < nfr ->
  (forall c' F n', In (mkABlock (ABFake c') F n') LB -> c' <= 2) ->
  AM.mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - 4096 ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> FRNG AI AI_fake L RNG ->
  evtF bsegs RNG (sm_postA AI AI_fake c n L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 entry) fc None m (seg_rom bsegs)).

Lemma fk_count_fakeb : forall c LB, (FC.fk_count c LB <= length (List.filter fakeb LB))%nat.
Proof.
  intros c LB. unfold FC.fk_count. induction LB as [|b LB IH]; [cbn; lia|]. cbn [List.filter].
  set (X := List.filter (FC.isfk c) LB) in *. set (Y := List.filter fakeb LB) in *.
  destruct b as [[p|c'] A n]; unfold FC.isfk, fakeb; cbn [ab_kind]; [exact IH|]. destruct (c' =? c); cbn [length]; lia.
Qed.
Lemma wins_of_length : forall E n ws, (length (wins_of E n ws) <= n)%nat.
Proof. intros E n. induction n as [|n IH]; intros ws; [cbn; lia|]. destruct ws as [|a [|b [|c ws']]]; cbn [wins_of length]; try lia. specialize (IH ws'). lia. Qed.

Lemma zero_cells_bytes : forall k, cells_bytes (repeat (C8 (Z_to_bv 64 0)) k) = repeat (Z_to_bv 8 0) (8 * k).
Proof.
  induction k as [|k IH]; [reflexivity|]. cbn [repeat cells_bytes]. rewrite IH. replace (8 * S k)%nat with (8 + 8 * k)%nat by lia.
  rewrite repeat_app. f_equal.
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
Variable OTHER : Model -> Model -> Prop.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.
Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment bsegs a 1 = Some seg) -> op_cov0 OPS a.
Hypothesis Cw_ghost_grow_f : forall kd md ca LB ws m b n, kd = K_FRAMEz \/ kd = K_FTWINz -> cw_holds Cw md ca LB ws m ->
  (forall a, in_iv (b, n) a -> ~ in_user LB a) -> cw_holds Cw md ca ((b, n) :: LB) (ws ++ [Win b n kd]) m.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable NMAXt : nat.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).

Variable cls : int.
Hypothesis CLS2 : PrimInt63.leb cls 2%uint63 = true.
Variables (NFR ENTRY : Z).
Hypothesis NFR_big : 4096 <= NFR.
Hypothesis WALK : sm_walk_stmt AI AI_fake (to_Z cls) (fsize (to_Z cls)) NFR ENTRY.

Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Hypothesis ACCT_frng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> FRNG AI AI_fake L RNG.
Definition acct_leaf_frame_in (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock)
    (r : unit) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo', mrel A' moc' mo' -> MP mo' /\ op_minv OPS mo' /\ OTHER mo0 mo' /\
    forall c F n LBk, (forall id A sz, In (HB id A sz) LBa -> In (HB id A sz) LBk) -> ACCT aw L RNG' st (mkABlock (ABFake c) F n :: LBk) mo'.

Hypothesis ACCT_frame_in : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_frame_in mo aw L st LBa).
Theorem stack_malloc_sound : forall pc, to_Z pc = ENTRY -> contract_sound bsegs OPS MP PB (ActrB.TwinB.ActrB.stack_malloc_c bsegs pc ActrA.ATPi cls).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc ActrB.TwinB.ActrB.stack_malloc_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = ENTRY) by (rewrite Hspc; exact Hpc).
  destruct (sm_apply_shape bsegs ActrA.ATPi cls st sts Happ) as (r & hargs & st1 & h1 & h2 & PREB & _ & FP & SAO & FS0 & H1 & H2 & ->).
  destruct (acall_pre_bridge 4096%uint63 st r hargs st1 PREB FS0) as [wnl PRE].
  destruct (CtrPre.TwinB.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng 4096%uint63 None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  set (R := ms_regs ms) in *. set (c := to_Z cls) in *. set (n := fsize c) in *.
  pose proof atop_range as ATR.

  assert (SPA : bv_unsigned (AP.getr (ms_regs ms) 2%bv) <= al_top L).
  { destruct (CtrPre.TwinB.acall_pre_inv 4096%uint63 None st r hargs wnl st1 PRE) as (tp0 & _ & _ & _ & _ & _ & SFO & _).
    exact (CtrPre.TwinB.acall_sp_altop AI ACCT UNIV Cw OPS E st ms mo r hargs wnl L RNG sta LBa aw HS CF AH SPT SFO SAO). }
  fold R in SPA.
  destruct (AI_layout AI _ _ _ _ _ AH) as (_ & _ & TOP47 & _).

  pose proof CF as CF0.
  destruct CF0 as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
  destruct WOF as (E1 & E2 & E3 & E4).
  assert (NOTFULL : Z.of_nat (FC.fk_count c LBa) < NFR).
  { pose proof (aw_real_fake_count AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo W _ ARW TI) as FCN. rewrite E4 in FCN.
    pose proof (fk_count_fakeb c LBa) as X1. pose proof (wins_of_length E nn rest) as X2. unfold ZTOTAL in FCN. lia. }
  assert (CLSW : forall c' F n', In (mkABlock (ABFake c') F n') LBa -> c' <= 2).
  { intros c' F n' Hb. apply (aw_real_cls AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo W c' F n' ARW). rewrite E4. exact Hb. }
  destruct (ACCT_frame_in aw L RNG sta LBa mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  pose proof (WALK L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31)
                (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) sta LBa (CtrPre.TwinB.sp_lo E st) AH NOTFULL CLSW MI ST BOT LO SPA TP
                ltac:(eapply rng_sub'; [exact (ACCT_rng _ _ _ _ _ _ AC)| lia]) (ACCT_rng_aimg _ _ _ _ _ _ AC) (ACCT_frng _ _ _ _ _ _ AC)) as EV.
  rewrite Ems, HPC. apply (GlueA.TwinB.realizes_to_mkRA bsegs).
  eapply (implS_twfS_realizes_silent bsegs NMAXt (Ret (Exc.Ok tt)) RNG AL0
            (fun (_ : unit) (RNGq : footprint) ms' => RNGq = RNG /\ sm_postA AI AI_fake c n L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
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
    destruct HQ as (F & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & LBk & j0 & j1 & j2 & junk
                    & EMS & MINV'' & STK' & PRES & TWP & AH' & KEEP1 & KEEP2d & F64 & BKF & TOPF & FRM & SHD & RG1 & RG2 & RSW).
    match type of EMS with ms' = MS ?RR _ _ _ _ _ _ => set (R' := RR) in * end.
    destruct (HeapCtr.TwinB.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WT0 & LT0 & ER).
    assert (EMS' : ms' = CtrFrame.TwinB.ms' ms r R' m').
    { rewrite EMS. unfold CtrFrame.TwinB.ms'. f_equal. fold R. rewrite RA. apply MState.ret_pc_even.
      - lia.
      - pose proof (HeapCtr.TwinB.call_pre_even st r CP) as EV0.
        pose proof (land_mk r 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
        change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EV0 in LM. change (to_Z 0%uint63) with 0 in LM.
        change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }
    destruct (cls_lits cls CLS2) as (_ & _ & _ & NCASES). fold c in NCASES. fold n in NCASES.
    assert (LOWF : 0x631000 <= F /\ F + n < 2 ^ 47) by (unfold ablk, AIMG_HI, KLS in BKF; lia).

    assert (ZSH : forall g, 0 <= g < n / 8 -> m' (AM.wa (shad F + g)) = Some (Z_to_bv 8 0)).
    { intros g Hg. destruct SHD as [[_ BY] _]. rewrite zero_cells_bytes in BY. destruct BY as (_ & _ & BY).
      assert (N8 : (8 * Z.to_nat (n / 64))%nat = Z.to_nat (n / 8)) by (destruct NCASES as [->|[->| ->]]; reflexivity).
      rewrite repeat_length, N8 in BY. specialize (BY (Z.to_nat g) ltac:(lia)). rewrite Z2Nat.id in BY by lia.
      rewrite nth_error_repeat in BY by lia.
      assert (SHLO : 0x631000 <= shad F + g < 2 ^ 64).
      { unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. destruct NCASES as [Q|[Q|Q]]; rewrite Q in *; Z.div_mod_to_equations; lia. }
      apply (SmLib.TwinB.raw_of_view m' (shad F + g) _ SHLO). exact BY. }
    assert (FLW : exists flg, AM.bytes_at bsegs m' (F + n - 8) (AM.le8 (Z_to_bv 64 flg)) /\ flag_law AI L (mkABlock (ABFake c) F n) flg).
    { exists (FLG AI AI_fake L (mkABlock (ABFake c) F n)). split; [| exact (fk_law AI AI_fake L (mkABlock (ABFake c) F n) ltac:(exists c; reflexivity))].
      pose proof (FakeLaw.TwinB.last_cell_bytes m' F j0 j1 j2 _ _ junk FRM) as BA. rewrite Z2Nat.id in BA by (destruct NCASES as [Q|[Q|Q]]; rewrite Q; lia).
      replace (F + n - 8) with (F + 24 + (n - 32)) by lia. exact BA. }
    pose proof (frames_live AI ACCT UNIV OPS AI_fake E st ms mo cls hargs L RNG sta LBa LBk HS Hf FP KEEP2d) as LIVE.
    destruct (sm_post_ok AI IMGX IMGX_aci IMGSH_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img Cw_ghost_grow_f
                st E ms mo cls r hargs wnl st1 h1 h2 L RNG sta LBa aw F R' m' mo' LBk HS CP FS CF CLS2 H1 H2
                ltac:(intros rg Hrg; unfold CtrFrame.TwinB.kept_regsA in Hrg; cbn [In] in Hrg; repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]); destruct Hrg)
                eq_refl MINV'' STK' PRES TWP AH' (ACP c F n LBk (fun id A sz Hin => KEEP2d _ Hin (UF.fk_live_heap L (ms_mem ms) (AP.getr (ms_regs ms) 2%bv) id A sz))) KEEP1 LIVE F64 RSW ZSH FLW HMI' OTH) as (E1' & EXT & HSP).
    apply (HK _ ltac:(left; reflexivity) E1' ms' mo' EXT HMP'). rewrite EMS'. exact HSP.
Qed.
End Sound.
End TwinB.
