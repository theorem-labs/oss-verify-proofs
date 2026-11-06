From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec RcIdentModel SlotModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import put_dec_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import put_dec_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uab1 UTac_uab3.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.

Lemma b22_EV2_len : forall idb, 0 <= zlen (EV2 idb) <= 33.
Proof.
  intros idb. destruct (v2_mmp idb) as (H1 & H2 & _).
  pose proof (v1_DEC_len _ 1 H1 ltac:(lia)). pose proof (v1_DEC_len _ 1 H2 ltac:(lia)).
  unfold zlen, EV2, EV1. rewrite !length_app. cbn [length]. lia.
Qed.

Section S.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis PUTDEC : put_dec_contract.

Lemma seg_B22 : forall i,
  Hrec B APIf ra (Inv_U13508_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U134f4_at B APIf ra empty) i.
Proof.
  intros i HX g c (pl & HC).
  apply (tb_seg B APIf ra empty FF g 0x134f4 0x13508 _ _ _
    (fun regs m => RB12 g i pl regs m /\ S6A g i regs /\ FALL g i regs /\ RRr g i regs /\ VB g i /\
       q64 m (spk g 184) (zlen (EV (idS g i))) /\ bytes_at rsegs m (spk g 192) (EV (idS g i))) c HC).
  2: { intros c' HC'. apply HX. exists pl. exact HC'. }
  intros L A regs mem md HF HP HPE.
  destruct HPE as ((HREC & E20 & E26 & E21 & HPL & HID & HAG & HBF & HLP) & E22 & ((E23 & E18 & E25 & E19 & E27) & E8) &
    E24 & HVB & HEN & HEV).
  pose proof HREC as (Hi & E9 & HNR & HG24 & HHW & HEVb).
  pose proof HF as (HGV & E2 & E3 & E4 & _ & _ & _ & _ & HM & _).
  pose proof HGV as (_ & _ & _ & HS16 & HSc & HS47 & _).
  pose proof alloc_ceiling_value as Hac.
  destruct (tb_norm_frame B APIf ra empty FF g _ _ _ _ _ _ _ HF) as (HRO & MIn & WRn & STn).
  assert (Hin : In (pl, rec_k (g_in g) i) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  destruct (t_block_range B APIf ra empty FF L A mem md _ _ HM Hin) as [Hpl1 Hpl2].
  assert (HPLl : Z.of_nat (length (rec_pl (g_in g) i)) = rec_k (g_in g) i).
  { rewrite rec_pl_length. pose proof (rec_k_range (g_in g) i). lia. }
  pose proof (rec_id_length (g_in g) (S i)) as LID1. pose proof (rec_id_length (g_in g) i) as LID0.
  unfold ID_SIZE in LID1, LID0. pose proof (tb_hwb_len (g_in g) i) as HWL.
  pose proof (v2_mmp (idS g i)) as (Hma & Hmi & Hpa).
  pose proof (b22_EV2_len (idS g i)) as HE2.
  pose proof (v1_DEC_len _ 2 Hpa ltac:(lia)) as HDl.
  remember (zlen (EV2 (idS g i))) as EN2 eqn:HE2d.
  remember (dec_len (patch (idS g i)) 2) as D eqn:HDd.
  assert (HD0 : 0 <= D <= 16) by (rewrite HDd; unfold dec_len; lia).
  assert (EEV : zlen (EV (idS g i)) = EN2 + D) by (rewrite HE2d, HDd; unfold EV, zlen, dec_len; rewrite length_app; lia).
  exists [(g_S g - 384 - 16, g_S g - 384); (g_S g - 384 + 184, g_S g - 384 + 184 + 8);
          (g_S g - 384 + 192 + EN2, g_S g - 384 + 192 + EN2 + D)],
    ([(9%bv, Z_to_bv 64 (Z.of_nat i)); (20%bv, Z_to_bv 64 (rec_k (g_in g) i));
    (26%bv, Z_to_bv 64 (g_p g + rec_c (g_in g) (S i))); (21%bv, Z_to_bv 64 pl); (22%bv, Z_to_bv 64 (rec_addr (g_in g) i));
    (23%bv, Z_to_bv 64 (fw_milli (idS g i))); (18%bv, Z_to_bv 64 (has_fw (idS g i)));
    (25%bv, Z_to_bv 64 (major (idS g i))); (19%bv, Z_to_bv 64 (minor (idS g i)));
    (27%bv, Z_to_bv 64 (patch (idS g i))); (8%bv, Z_to_bv 64 (has_model_name (idS g i)));
    (24%bv, Z_to_bv 64 (rec_r (g_in g) i))] : list (reg * word)),
    [(spk g 184, le8 (Z_to_bv 64 (zlen (EV (idS g i))))); (spk g 192, EV (idS g i))].
  split.
  { intros x Hx. cbn [outside] in Hx. unfold SLOT_K, SLOT_STACK. lia. }
  split.
  - pose proof (bytes_at_normalize rsegs mem _ _ HRO HEN) as HENn.
    pose proof (bytes_at_normalize rsegs mem _ _ HRO HEV) as HEVn.
    pose proof (bytes_at_normalize rsegs mem _ _ HRO HID) as HIDn.
    unfold q64, IDb, spk, fsp, SLOT_FRAME in HENn, HEVn, HIDn.
    unfold rmk. rewrite E2, E3, E4, E9, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27, E8.
    unfold spk, fsp, SLOT_FRAME in *. unfold SLOT_K, SLOT_STACK in *.
    pose proof (bytes_at_read rsegs _ _ _ 26 2 HIDn ltac:(lia) ltac:(lia)) as RI26.
    replace (g_S g - 384 + 146 + 26) with (g_S g - 384 + 172) in RI26 by lia.
    step.
    assert (EM : zext 64 (bv_extract 0 16 (le_bytes_to_word (firstn 2 (skipn (Z.to_nat 26) (rec_id (g_in g) (S i)))))) =
      Z_to_bv 64 (patch (idS g i))).
    { change (Z.to_nat 26) with 26%nat. rewrite (ua_lhu _ 26) by (rewrite LID1; lia). reflexivity. }
    rewrite EM.
    step. step. step. step.
    eapply Exec.evt_cut.
    { eapply PUTDEC with (b := g_S g - 384 + 192) (p := g_S g - 384 + 184) (v := patch (idS g i)) (mn := 2)
        (lo := g_S g - 65536) (N := Z_to_bv 64 EN2).
      - reflexivity.
      - lia.
      - reflexivity.
      - rewrite MState.unsigned_lit by lia. apply Z.mod_small. lia.
      - left. rewrite MState.unsigned_lit by lia. lia.
      - reflexivity.
      - lia.
      - exact HENn.
      - apply (v2_wr_sub _ _ _ _ _ WRn); lia.
      - Z.div_mod_to_equations. lia.
      - rewrite MState.unsigned_lit by lia. rewrite <- HDd. apply (v2_wr_sub _ _ _ _ _ WRn); lia.
      - exact MIn.
      - rewrite MState.unsigned_lit by lia. apply (v1_stk_sub _ _ _ _ _ _ STn); lia.
      - rewrite MState.unsigned_lit by lia. unfold PUT_DEC_FRAME. lia.
      - rewrite MState.unsigned_lit by lia. rewrite <- HDd. lia.
      - rewrite MState.unsigned_lit by lia. unfold PUT_DEC_FRAME. lia.
      - rewrite !MState.unsigned_lit by lia. rewrite <- HDd. unfold PUT_DEC_FRAME. lia. }
    intros ms' PO. destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' &
      t6' & m' & -> & MU2 & WM' & _ & _ & HDB & HP8).
    pose proof (MState.unsigned_lit EN2 ltac:(lia)) as UN.
    rewrite !MState.unsigned_lit in MU2, HDB, HP8 by lia. rewrite ?UN in MU2, HDB, HP8.
    rewrite <- HDd in MU2, HP8. unfold PUT_DEC_FRAME in MU2.
    rewrite (MState.ret_pc_even 0x13508) by (lia || reflexivity).
    apply Exec.evt_done. eexists _, _. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [repeat (apply Forall_cons; [reflexivity|]); apply Forall_nil|].
    split.
    { eapply munch_weaken; [|exact MU2]. intros x Hx. cbn [outside] in Hx |- *. repeat split; try exact I; lia. }
    split; [exact WM'|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
    + rewrite EEV. exact HP8.
    + unfold EV. apply bytes_at_app. split.
      * apply (tb_bytes_keep _ _ _ _ _ HEVn MU2). intros j Hj.
        assert (Z.of_nat (length (EV2 (idS g i))) = EN2) by (rewrite HE2d; reflexivity).
        cbn [outside]. repeat split; try exact I; lia.
      * assert (EL : Z.of_nat (length (EV2 (idS g i))) = EN2) by (rewrite HE2d; reflexivity).
        rewrite EL. exact HDB.
  - intros regs' mem' HRL MU HBL. tb_regs HRL. tb_regs HBL.
    unfold RB12, REC, S6A, FALL, FNM, F7, F2, F9, F3, F11, F0, RRr.
    unfold NRb, G24, HWb, EVb, PLB, IDb, AGN, BEF, LPm in *. unfold q64, u32 in *.
    destruct HHW as (HW1 & HW2 & HW3). unfold SLOT_K, SLOT_STACK in *.
    tb_psplit; try assumption; tb_keep MU.
Qed.

End S.
