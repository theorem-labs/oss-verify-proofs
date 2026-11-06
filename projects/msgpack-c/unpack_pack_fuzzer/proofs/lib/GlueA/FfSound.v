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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_ffepi.
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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA CallV GlueA CtrPre FrameV CtrDelta CtrFree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import ActrB FfShape FfWalk FfPost.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.

Lemma reg_of_r5_unsigned : forall (r : reg) (x : r5), bv_unsigned r = r5_to_Z x -> r = reg_of_r5 x.
Proof.
  intros r x H. unfold reg_of_r5. rewrite <- H. symmetry. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma ff_regs {rc : runConstT} : forall OPS E st ms mo (HS : st_ok asegs OPS E st ms mo) (FOK : fresh_ok st = true) (Fv : Z -> word) (Gv : Z -> Z -> byte)
    (RT : r5) (flgw pcw : word),
  r5_eqb RT X0 = false -> Fv 0 = flgw ->
  forall x, rget (Core (AP.regupd (ms_regs ms) (reg_of_r5 RT) flgw) (ms_fregs ms) pcw (ms_fcsr ms) None) (reg_of_r5 x)
          = den (CtrDelta.E' E st Fv Gv) (rf_get (rf_set (s_rf st) RT (VP (s_next st) wzero)) x).
Proof.
  intros OPS E st ms mo HS FOK Fv Gv RT flgw pcw RTNZ F0 x. unfold rget. cbn [c_regs]. unfold AP.regupd. rewrite StepB.is_x0_reg_of_r5.
  destruct (r5_eqb x RT) eqn:Q.
  - apply r5_eqb_spec in Q. subst x. rewrite RTNZ, StepB.reg_get_set, StepB.r5_eqb_refl, rf_get_set_same, HeapCtr.den_VPz.
    pose proof (CtrDelta.ev_E'_fresh E st FOK Fv Gv 0 (Nat.le_0_l 200)) as EV. cbn [addn Z.of_nat] in EV. rewrite EV. symmetry. exact F0.
  - assert (NE : RT <> x) by (intros ->; rewrite StepB.r5_eqb_refl in Q; discriminate Q).
    rewrite StepB.reg_get_set, Q, (rf_get_set_other _ _ RT x _ NE).
    pose proof (CtrDelta.den_E' E st Fv Gv _ (CtrDelta.reg_below st FOK x)) as DE. unfold getr in DE. rewrite DE.
    pose proof (so_regs _ _ _ _ _ _ HS x) as R0. unfold rget in R0. cbn [c_regs] in R0. rewrite StepB.is_x0_reg_of_r5 in R0. exact R0.
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
Hypothesis Cw_ghost_free_f : forall kd md ca LB ws m b n ws', kd = K_FRAMEz \/ kd = K_FTWINz -> cw_holds Cw md ca LB ws m -> In (Win b n kd) ws ->
  (forall w, In w ws' <-> In w ws /\ w <> Win b n kd) -> cw_holds Cw md ca (remove iv_eq_dec (b, n) LB) ws' m.
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

Hypothesis ACCT_frng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> FRNG AI AI_fake L RNG.
Definition acct_leaf_frame_out (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock)
    (r : unit) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo', mrel A' moc' mo' -> MP mo' /\ op_minv OPS mo' /\ OTHER mo0 mo' /\
    forall fb, In fb LBa -> is_fake fb -> ACCT aw L RNG' st (lb_del fb LBa) mo'.
Hypothesis ACCT_frame_out : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_frame_out mo aw L st LBa).

Theorem fake_free_sound : forall pc RF RT OFF,
  F_ffepi.ffepi_shape (to_Z pc) (r5_to_Z RT) (r5_to_Z RF) (to_Z OFF) = true -> to_Z pc + 8 < 2 ^ 62 ->
  contract_sound asegs OPS MP PB (ActrB.fake_free_c pc RF RT OFF).
Proof.
  intros pc RF RT OFF SHP PCB st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc ActrB.fake_free_c] in Happ, Hspc.
  destruct (ff_apply_shape RF RT OFF st sts Happ)
    as (kf & shf & hargs & wnl & i0 & rsh & h1 & h2 & RVN & GR & AW & FT & FW & FRS & FOK & RTNZ & FOKk & SRG & SFO & LO0s & (lent0 & kdt & WLT0 & KEQ) & H1 & H2 & ->).

  destruct (CtrPre.aheap_call_facts AI ACCT UNIV Cw OPS AI_fake OPS_holds1 E st ms mo hargs wnl HS AW)
    as (r1 & n & md & A & nw & rest & LB & Hr1 & Hf & Hc & Hn & Eh & T & N & Ln & N255 & SW & NW & AN & JU & HA & WF & HC & W & ARW & TI).
  destruct (CallA.aheap_windows_inv st hargs wnl AW) as (_ & _ & r1' & n' & md2 & A2 & nw2 & rest2 & _ & _ & Eh2 & _ & N2 & _ & _ & _ & NW2 & _ & _ & TS).

  destruct (CallA.stack_sound_g asegs OPS E st ms mo 0%uint63 HS ltac:(change (to_Z 0%uint63) with 0; lia) SRG)
    as (ks & offs & rss & ksp & HX2 & Hrs & K0 & Hksp & K16 & A16 & Esp & LOX & HI64 & STK & SPR & LOR & LOZ0).
  destruct (CallA.sp_floor_sound asegs OPS E st ms mo hargs n md A nw rest ks offs rss HS SFO Hn Eh SPR LOZ0) as (wlo & len & INw & FLOOR0).
  pose proof (proj1 (Forall_forall _ _) WF _ INw) as (_ & _ & _ & KDs). cbn [w_kind w_lo] in KDs.
  assert (CE : ATOP + 4096 <= bv_unsigned (den E (VP STACK_ID wlo))).
  { destruct KDs as [[_ C]|[[K1 _]|[K1 _]]]; [exact C| unfold K_BLOCK, K_STACK in K1; lia| unfold K_SUB, K_STACK in K1; lia]. }
  change (to_Z 0%uint63) with 0 in LOR.
  set (R := ms_regs ms) in *. set (m := ms_mem ms) in *.
  assert (SP2 : bv_unsigned (AP.getr R 2%bv) = bv_unsigned (ev E ks) + keyZ ksp).
  { unfold R. rewrite <- HeapCtr.reg_of_X2, (GlueA.getr_RA asegs OPS E st ms mo HS X2). exact Esp. }

  destruct (CtrFree.afree_ok_k_inv OPS ActrB.K_FRAME ActrB.K_FTWIN E st ms mo wnl kf shf HS FOKk)
    as (rf & lenf & lent & Frf & WLf & WLt & BTs & LO0 & POSf & LEf & OTHERS).
  rewrite WLt in WLT0. injection WLT0 as <- <-.
  assert (FULLs : hiZ E rsh = bv_unsigned (den E lent)).
  { unfold hiZ. rewrite (HeapCtr.known_eq_sound E _ _ _ (so_facts _ _ _ _ _ _ HS) KEQ). reflexivity. }
  assert (ELF : lenf = VL (wlit OFF)).
  { assert (FW' : find_window n rest (VP kf wzero) = Some (i0, VL (wlit OFF), VL ActrB.K_FRAME)).
    { unfold heap_find_window in FW. rewrite Hn, Eh in FW. exact FW. }
    pose proof (find_window_In n rest kf i0 (VL (wlit OFF)) ActrB.K_FRAME wnl FW' eq_refl NW) as IN1.
    destruct (HeapCtrB.windows_anchored_nodup _ _ kf _ _ _ _ AN IN1 (HeapCtrB.win_lookup_In _ _ _ _ WLf)) as [EQ _]. symmetry. exact EQ. }
  destruct (owner_f AI ACCT UNIV OPS AI_fake E st ms mo HS wnl n rest LB (den E A) NW WF W ARW TI kf shf lenf lent WLf WLt BTs)
    as (fb & VF & EAf & ENf & ESH & ELT & INU & INS & UIV & SIV).
  set (Af := bv_unsigned (ev E kf)) in *.
  assert (NFE : bv_unsigned (den E lenf) = to_Z OFF) by (rewrite ELF; cbn [den]; rewrite wbv_unsigned; apply wlit_ok).

  destruct (aw_real_flag_rng AI ACCT UNIV AI_fake (den E A) LB m mo W fb ARW VF) as (flg & BA & FL & FLG64 & FRNGflg).
  destruct (aw_realW_AHEAP AI ACCT UNIV (den E A) LB m mo W ARW) as (AH & AC & HU).
  pose proof (ACCT_frng _ _ _ _ _ _ AC) as FRG.
  destruct (fk_rng AI AI_fake _ _ _ _ _ fb AH (proj1 (proj1 VF)) (proj2 VF) FRG) as (RNGb & _ & _).
  destruct (fk_facts AI AI_fake _ _ _ _ _ fb AH (proj1 (proj1 VF)) (proj2 VF)) as (BKb & HIb & A8b & N8b & N64b & WRb & _).
  destruct (FL (w_RNG W) (w_st W) (w_LBa W) m AH (proj1 (proj1 VF))) as (_ & WRflg & _).
  set (RNG := w_RNG W) in *.

  destruct (ffepi_shape_inv _ _ _ _ SHP) as (w1 & w2 & sg & RTr & RFr & R2 & imm & imm2 & F1 & E1 & D1 & F2 & E2 & D2 & X2 & I2 & NX & URT & URF & UOFF).
  pose proof (reg_of_r5_unsigned RTr RT URT) as ERT. pose proof (reg_of_r5_unsigned RFr RF URF) as ERF.
  assert (GRF : AP.getr R RFr = Z_to_bv 64 Af).
  { rewrite ERF. unfold R. rewrite (GlueA.getr_RA asegs OPS E st ms mo HS RF), GR, HeapCtr.den_VPz. unfold Af. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (IM : sext 64 imm = Z_to_bv 64 (to_Z OFF)) by (rewrite <- UOFF; symmetry; apply Z_to_bv_bv_unsigned).
  assert (BA' : AM.bytes_at asegs m (Af + to_Z OFF) (AM.le8 (Z_to_bv 64 flg))).
  { replace (Af + to_Z OFF) with (ab_addr fb + ab_size fb - 8) by (rewrite EAf; lia). exact BA. }
  assert (RG1 : rng RNG (Af + to_Z OFF) 8) by (eapply rng_sub'; [exact RNGb| rewrite EAf; lia]).
  pose proof (FRNGflg RNG FRG) as RG2.
  pose proof (F_ffepi.ffepi_walk_off asegs RNG R (ms_fregs ms) (Z_to_bv 64 (to_Z pc)) (ms_fcsr ms) m w1 w2 sg RTr RFr R2 imm imm2 Af (to_Z OFF) flg
                F1 E1 D1 F2 E2 D2 X2 I2 NX GRF IM BA' WRflg FLG64 RG1 RG2) as EV.
  destruct (ACCT_frame_out _ _ _ _ _ mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  rewrite (GlueA.ms_formA asegs OPS E st ms mo HS RVN). rewrite Hspc. fold R m.
  eapply (implS_twfS_realizes_silent asegs NMAXt (Ret (Exc.Ok tt)) RNG AL0
            (fun (_ : unit) (RNGq : footprint) ms' => RNGq = RNG /\
               ms' = MS (AP.regupd R RTr (Z_to_bv 64 flg)) (ms_fregs ms) (bv_add (Z_to_bv 64 (to_Z pc)) (Z_to_bv 64 8)) (ms_fcsr ms) None
                           (write_to_mem m (AM.wa flg) [Z_to_bv 8 0]) (seg_rom asegs))
            _ _ moc mo K).
  - cbn [implF epostF]. eapply evtF_mono; [exact EV|]. intros ms' PO. split; [reflexivity| exact PO].
  - exact TW.
  - exact HH.
  - exact MINV.
  - exact MR.
  - intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV'' MR'.
    destruct (HP' mo' MR') as (HMP' & HMI' & OTH & ACP). destruct HQ as [-> ->].
    specialize (ACP fb (proj1 (proj1 VF)) (proj2 VF)).
    set (Fv := fun _ : Z => Z_to_bv 64 flg). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0).
    apply (HK _ (or_introl eq_refl) (CtrDelta.E' E st Fv Gv) _ mo' (CtrDelta.EXT E st Fv Gv) HMP').
    assert (PC8 : bv_add (Z_to_bv 64 (to_Z pc)) (Z_to_bv 64 8) = Z_to_bv 64 (to_Z (PrimInt63.add (s_pc st) 8%uint63))).
    { rewrite Hspc. pose proof (to_Z_bounded pc) as PB0. rewrite add_spec. change (to_Z 8%uint63) with 8. rewrite Z.mod_small by (rewrite wB_two63, two63_eq; lia).
      apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. change (bv_wrap 64 8) with 8. rewrite (bv_wrap_small 64 (to_Z pc)) by (unfold bv_modulus; change (Z.of_N 64) with 64; lia). reflexivity. }
    rewrite PC8, ERT. unfold ff_post. rewrite RVN.
    assert (MI : AM.mem_inv asegs m).
    { intros a b Hm. unfold AM.ro_addr. destruct (find_segment asegs (bv_unsigned a) 1) as [seg|] eqn:Fs; [|reflexivity].
      rewrite (so_minv _ _ _ _ _ _ HS a b Hm seg Fs). reflexivity. }
    assert (MI' : AM.mem_inv asegs (write_to_mem m (AM.wa flg) [Z_to_bv 8 0])).
    { apply (AM.mem_inv_store asegs m _ _ MI). cbn [length]. replace (AM.wa flg) with (AM.wa (flg + 0)) by (f_equal; lia).
      apply (AM.wr_at_store_ok asegs m flg 1 0 1 WRflg); lia. }
    apply (ff_post_ok AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 Cw_ghost_free_f OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
             E st ms mo HS wnl n rest LB (den E A) NW AN WF W ARW TI kf shf rf rsh lenf lent Frf FRS WLf WLt LO0 POSf LO0s FULLs OTHERS
             fb VF EAf ENf ESH ELT INU INS UIV SIV flg mo' FL ACP ltac:(fold R; lia) hargs md A nw Hf Eh T N Ln FOK Fv Gv h1 h2 H1 H2 eq_refl HC
             (AP.regupd R (reg_of_r5 RT) (Z_to_bv 64 flg)) MI' ks offs rss ksp SPR SP2 JU ltac:(lia) ltac:(lia) Hc OTH HMI').
    + exact RVN.
    + rewrite rf_get_set_other; [exact (so_x0 _ _ _ _ _ _ HS)|]. intros ->. discriminate RTNZ.
    + exact (ff_regs OPS E st ms mo HS FOK Fv Gv RT (Z_to_bv 64 flg) _ RTNZ eq_refl).
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

Import ActrB.TwinB FfShape.TwinB FfWalk.TwinB FfPost.TwinB.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.

Lemma reg_of_r5_unsigned : forall (r : reg) (x : r5), bv_unsigned r = r5_to_Z x -> r = reg_of_r5 x.
Proof.
  intros r x H. unfold reg_of_r5. rewrite <- H. symmetry. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma ff_regs {rc : runConstT} : forall OPS E st ms mo (HS : st_ok bsegs OPS E st ms mo) (FOK : fresh_ok st = true) (Fv : Z -> word) (Gv : Z -> Z -> byte)
    (RT : r5) (flgw pcw : word),
  r5_eqb RT X0 = false -> Fv 0 = flgw ->
  forall x, rget (Core (AP.regupd (ms_regs ms) (reg_of_r5 RT) flgw) (ms_fregs ms) pcw (ms_fcsr ms) None) (reg_of_r5 x)
          = den (CtrDelta.TwinB.E' E st Fv Gv) (rf_get (rf_set (s_rf st) RT (VP (s_next st) wzero)) x).
Proof.
  intros OPS E st ms mo HS FOK Fv Gv RT flgw pcw RTNZ F0 x. unfold rget. cbn [c_regs]. unfold AP.regupd. rewrite StepB.is_x0_reg_of_r5.
  destruct (r5_eqb x RT) eqn:Q.
  - apply r5_eqb_spec in Q. subst x. rewrite RTNZ, StepB.reg_get_set, StepB.r5_eqb_refl, rf_get_set_same, HeapCtr.TwinB.den_VPz.
    pose proof (CtrDelta.TwinB.ev_E'_fresh E st FOK Fv Gv 0 (Nat.le_0_l 200)) as EV. cbn [addn Z.of_nat] in EV. rewrite EV. symmetry. exact F0.
  - assert (NE : RT <> x) by (intros ->; rewrite StepB.r5_eqb_refl in Q; discriminate Q).
    rewrite StepB.reg_get_set, Q, (rf_get_set_other _ _ RT x _ NE).
    pose proof (CtrDelta.TwinB.den_E' E st Fv Gv _ (CtrDelta.TwinB.reg_below st FOK x)) as DE. unfold getr in DE. rewrite DE.
    pose proof (so_regs _ _ _ _ _ _ HS x) as R0. unfold rget in R0. cbn [c_regs] in R0. rewrite StepB.is_x0_reg_of_r5 in R0. exact R0.
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
Hypothesis Cw_ghost_free_f : forall kd md ca LB ws m b n ws', kd = K_FRAMEz \/ kd = K_FTWINz -> cw_holds Cw md ca LB ws m -> In (Win b n kd) ws ->
  (forall w, In w ws' <-> In w ws /\ w <> Win b n kd) -> cw_holds Cw md ca (remove iv_eq_dec (b, n) LB) ws' m.
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

Hypothesis ACCT_frng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> FRNG AI AI_fake L RNG.
Definition acct_leaf_frame_out (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock)
    (r : unit) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo', mrel A' moc' mo' -> MP mo' /\ op_minv OPS mo' /\ OTHER mo0 mo' /\
    forall fb, In fb LBa -> is_fake fb -> ACCT aw L RNG' st (lb_del fb LBa) mo'.
Hypothesis ACCT_frame_out : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_frame_out mo aw L st LBa).

Theorem fake_free_sound : forall pc RF RT OFF,
  F_ffepi.TwinB.ffepi_shape (to_Z pc) (r5_to_Z RT) (r5_to_Z RF) (to_Z OFF) = true -> to_Z pc + 8 < 2 ^ 62 ->
  contract_sound bsegs OPS MP PB (ActrB.TwinB.ActrB.fake_free_c pc RF RT OFF).
Proof.
  intros pc RF RT OFF SHP PCB st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc ActrB.TwinB.ActrB.fake_free_c] in Happ, Hspc.
  destruct (ff_apply_shape RF RT OFF st sts Happ)
    as (kf & shf & hargs & wnl & i0 & rsh & h1 & h2 & RVN & GR & AW & FT & FW & FRS & FOK & RTNZ & FOKk & SRG & SFO & LO0s & (lent0 & kdt & WLT0 & KEQ) & H1 & H2 & ->).

  destruct (CtrPre.TwinB.aheap_call_facts AI ACCT UNIV Cw OPS AI_fake OPS_holds1 E st ms mo hargs wnl HS AW)
    as (r1 & n & md & A & nw & rest & LB & Hr1 & Hf & Hc & Hn & Eh & T & N & Ln & N255 & SW & NW & AN & JU & HA & WF & HC & W & ARW & TI).
  destruct (CallA.TwinB.aheap_windows_inv st hargs wnl AW) as (_ & _ & r1' & n' & md2 & A2 & nw2 & rest2 & _ & _ & Eh2 & _ & N2 & _ & _ & _ & NW2 & _ & _ & TS).

  destruct (CallA.TwinB.stack_sound_g bsegs OPS E st ms mo 0%uint63 HS ltac:(change (to_Z 0%uint63) with 0; lia) SRG)
    as (ks & offs & rss & ksp & HX2 & Hrs & K0 & Hksp & K16 & A16 & Esp & LOX & HI64 & STK & SPR & LOR & LOZ0).
  destruct (CallA.TwinB.sp_floor_sound bsegs OPS E st ms mo hargs n md A nw rest ks offs rss HS SFO Hn Eh SPR LOZ0) as (wlo & len & INw & FLOOR0).
  pose proof (proj1 (Forall_forall _ _) WF _ INw) as (_ & _ & _ & KDs). cbn [w_kind w_lo] in KDs.
  assert (CE : ATOP + 4096 <= bv_unsigned (den E (VP STACK_ID wlo))).
  { destruct KDs as [[_ C]|[[K1 _]|[K1 _]]]; [exact C| unfold K_BLOCK, K_STACK in K1; lia| unfold K_SUB, K_STACK in K1; lia]. }
  change (to_Z 0%uint63) with 0 in LOR.
  set (R := ms_regs ms) in *. set (m := ms_mem ms) in *.
  assert (SP2 : bv_unsigned (AP.getr R 2%bv) = bv_unsigned (ev E ks) + keyZ ksp).
  { unfold R. rewrite <- HeapCtr.TwinB.reg_of_X2, (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X2). exact Esp. }

  destruct (CtrFree.TwinB.afree_ok_k_inv OPS ActrB.TwinB.ActrB.K_FRAME ActrB.TwinB.ActrB.K_FTWIN E st ms mo wnl kf shf HS FOKk)
    as (rf & lenf & lent & Frf & WLf & WLt & BTs & LO0 & POSf & LEf & OTHERS).
  rewrite WLt in WLT0. injection WLT0 as <- <-.
  assert (FULLs : hiZ E rsh = bv_unsigned (den E lent)).
  { unfold hiZ. rewrite (HeapCtr.TwinB.known_eq_sound E _ _ _ (so_facts _ _ _ _ _ _ HS) KEQ). reflexivity. }
  assert (ELF : lenf = VL (wlit OFF)).
  { assert (FW' : find_window n rest (VP kf wzero) = Some (i0, VL (wlit OFF), VL ActrB.TwinB.ActrB.K_FRAME)).
    { unfold heap_find_window in FW. rewrite Hn, Eh in FW. exact FW. }
    pose proof (find_window_In n rest kf i0 (VL (wlit OFF)) ActrB.TwinB.ActrB.K_FRAME wnl FW' eq_refl NW) as IN1.
    destruct (HeapCtrB.TwinB.windows_anchored_nodup _ _ kf _ _ _ _ AN IN1 (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLf)) as [EQ _]. symmetry. exact EQ. }
  destruct (owner_f AI ACCT UNIV OPS AI_fake E st ms mo HS wnl n rest LB (den E A) NW WF W ARW TI kf shf lenf lent WLf WLt BTs)
    as (fb & VF & EAf & ENf & ESH & ELT & INU & INS & UIV & SIV).
  set (Af := bv_unsigned (ev E kf)) in *.
  assert (NFE : bv_unsigned (den E lenf) = to_Z OFF) by (rewrite ELF; cbn [den]; rewrite wbv_unsigned; apply wlit_ok).

  destruct (aw_real_flag_rng AI ACCT UNIV AI_fake (den E A) LB m mo W fb ARW VF) as (flg & BA & FL & FLG64 & FRNGflg).
  destruct (aw_realW_AHEAP AI ACCT UNIV (den E A) LB m mo W ARW) as (AH & AC & HU).
  pose proof (ACCT_frng _ _ _ _ _ _ AC) as FRG.
  destruct (fk_rng AI AI_fake _ _ _ _ _ fb AH (proj1 (proj1 VF)) (proj2 VF) FRG) as (RNGb & _ & _).
  destruct (fk_facts AI AI_fake _ _ _ _ _ fb AH (proj1 (proj1 VF)) (proj2 VF)) as (BKb & HIb & A8b & N8b & N64b & WRb & _).
  destruct (FL (w_RNG W) (w_st W) (w_LBa W) m AH (proj1 (proj1 VF))) as (_ & WRflg & _).
  set (RNG := w_RNG W) in *.

  destruct (ffepi_shape_inv _ _ _ _ SHP) as (w1 & w2 & sg & RTr & RFr & R2 & imm & imm2 & F1 & E1 & D1 & F2 & E2 & D2 & X2 & I2 & NX & URT & URF & UOFF).
  pose proof (reg_of_r5_unsigned RTr RT URT) as ERT. pose proof (reg_of_r5_unsigned RFr RF URF) as ERF.
  assert (GRF : AP.getr R RFr = Z_to_bv 64 Af).
  { rewrite ERF. unfold R. rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS RF), GR, HeapCtr.TwinB.den_VPz. unfold Af. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (IM : sext 64 imm = Z_to_bv 64 (to_Z OFF)) by (rewrite <- UOFF; symmetry; apply Z_to_bv_bv_unsigned).
  assert (BA' : AM.bytes_at bsegs m (Af + to_Z OFF) (AM.le8 (Z_to_bv 64 flg))).
  { replace (Af + to_Z OFF) with (ab_addr fb + ab_size fb - 8) by (rewrite EAf; lia). exact BA. }
  assert (RG1 : rng RNG (Af + to_Z OFF) 8) by (eapply rng_sub'; [exact RNGb| rewrite EAf; lia]).
  pose proof (FRNGflg RNG FRG) as RG2.
  pose proof (F_ffepi.TwinB.ffepi_walk_off bsegs RNG R (ms_fregs ms) (Z_to_bv 64 (to_Z pc)) (ms_fcsr ms) m w1 w2 sg RTr RFr R2 imm imm2 Af (to_Z OFF) flg
                F1 E1 D1 F2 E2 D2 X2 I2 NX GRF IM BA' WRflg FLG64 RG1 RG2) as EV.
  destruct (ACCT_frame_out _ _ _ _ _ mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  rewrite (GlueA.TwinB.ms_formA bsegs OPS E st ms mo HS RVN). rewrite Hspc. fold R m.
  eapply (implS_twfS_realizes_silent bsegs NMAXt (Ret (Exc.Ok tt)) RNG AL0
            (fun (_ : unit) (RNGq : footprint) ms' => RNGq = RNG /\
               ms' = MS (AP.regupd R RTr (Z_to_bv 64 flg)) (ms_fregs ms) (bv_add (Z_to_bv 64 (to_Z pc)) (Z_to_bv 64 8)) (ms_fcsr ms) None
                           (write_to_mem m (AM.wa flg) [Z_to_bv 8 0]) (seg_rom bsegs))
            _ _ moc mo K).
  - cbn [implF epostF]. eapply evtF_mono; [exact EV|]. intros ms' PO. split; [reflexivity| exact PO].
  - exact TW.
  - exact HH.
  - exact MINV.
  - exact MR.
  - intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV'' MR'.
    destruct (HP' mo' MR') as (HMP' & HMI' & OTH & ACP). destruct HQ as [-> ->].
    specialize (ACP fb (proj1 (proj1 VF)) (proj2 VF)).
    set (Fv := fun _ : Z => Z_to_bv 64 flg). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0).
    apply (HK _ (or_introl eq_refl) (CtrDelta.TwinB.E' E st Fv Gv) _ mo' (CtrDelta.TwinB.EXT E st Fv Gv) HMP').
    assert (PC8 : bv_add (Z_to_bv 64 (to_Z pc)) (Z_to_bv 64 8) = Z_to_bv 64 (to_Z (PrimInt63.add (s_pc st) 8%uint63))).
    { rewrite Hspc. pose proof (to_Z_bounded pc) as PB0. rewrite add_spec. change (to_Z 8%uint63) with 8. rewrite Z.mod_small by (rewrite wB_two63, two63_eq; lia).
      apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. change (bv_wrap 64 8) with 8. rewrite (bv_wrap_small 64 (to_Z pc)) by (unfold bv_modulus; change (Z.of_N 64) with 64; lia). reflexivity. }
    rewrite PC8, ERT. unfold ff_post. rewrite RVN.
    assert (MI : AM.mem_inv bsegs m).
    { intros a b Hm. unfold AM.ro_addr. destruct (find_segment bsegs (bv_unsigned a) 1) as [seg|] eqn:Fs; [|reflexivity].
      rewrite (so_minv _ _ _ _ _ _ HS a b Hm seg Fs). reflexivity. }
    assert (MI' : AM.mem_inv bsegs (write_to_mem m (AM.wa flg) [Z_to_bv 8 0])).
    { apply (AM.mem_inv_store bsegs m _ _ MI). cbn [length]. replace (AM.wa flg) with (AM.wa (flg + 0)) by (f_equal; lia).
      apply (AM.wr_at_store_ok bsegs m flg 1 0 1 WRflg); lia. }
    apply (ff_post_ok AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 Cw_ghost_free_f OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
             E st ms mo HS wnl n rest LB (den E A) NW AN WF W ARW TI kf shf rf rsh lenf lent Frf FRS WLf WLt LO0 POSf LO0s FULLs OTHERS
             fb VF EAf ENf ESH ELT INU INS UIV SIV flg mo' FL ACP ltac:(fold R; lia) hargs md A nw Hf Eh T N Ln FOK Fv Gv h1 h2 H1 H2 eq_refl HC
             (AP.regupd R (reg_of_r5 RT) (Z_to_bv 64 flg)) MI' ks offs rss ksp SPR SP2 JU ltac:(lia) ltac:(lia) Hc OTH HMI').
    + exact RVN.
    + rewrite rf_get_set_other; [exact (so_x0 _ _ _ _ _ _ HS)|]. intros ->. discriminate RTNZ.
    + exact (ff_regs OPS E st ms mo HS FOK Fv Gv RT (Z_to_bv 64 flg) _ RTNZ eq_refl).
Qed.
End Sound.
End TwinB.
