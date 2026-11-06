From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec RcIdentModel SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import put_dec_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sb1 Tac_sb3.
Import ListNotations.
Open Scope Z_scope.

Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis PUTDEC : put_dec_contract.

Lemma seg_B21 : forall i,
  Hrec B APIf ra (Inv_K1337c_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K1334c_at B APIf ra empty) i.
Proof.
  intros i HX g c (pl & HC).
  apply (tb_seg B APIf ra empty FF g 0x1334c 0x1337c _ _ _
    (fun regs m => RB12 g i pl regs m /\ S7A g i regs /\ FALL g i regs /\
       getr regs 9 = Z_to_bv 64 (spk g 176) /\ VB g i /\
       q64 m (spk g 168) (zlen (EV2 (idS g i))) /\ bytes_at rsegs m (spk g 176) (EV2 (idS g i))) c HC).
  2: { intros c' HC'. apply HX. exists pl. exact HC'. }
  intros L A regs mem md HF HP HPE.
  destruct HPE as ((HREC & E21 & E20 & E22 & HPL & HID & HAG & HBF & HLP) & E23 & (E27 & E8 & E18 & E24 & E25 & E26) &
    E9 & HVB & HEN & HEV).
  pose proof HREC as (Hi & E19 & HNR & HG16 & HHW).
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
  unfold ID_SIZE in LID1, LID0. pose proof (t_hwb_len (g_in g) i) as HWL.
  pose proof (v2_mmp (idS g i)) as (Hma & Hmi & Hpa).
  pose proof (v1_DEC_len _ 1 Hma ltac:(lia)) as HD1.
  pose proof (v1_DEC_len _ 1 Hmi ltac:(lia)) as HDl.
  assert (HE1l : Z.of_nat (length (EV1 (idS g i))) = zlen (EV1 (idS g i))) by reflexivity.
  assert (HE1 : 0 <= zlen (EV1 (idS g i)) <= 16) by (unfold zlen, EV1; lia).
  remember (zlen (EV1 (idS g i))) as EN1 eqn:HE1d.
  remember (dec_len (minor (idS g i)) 1) as D eqn:HDd.
  assert (HD0 : 0 <= D <= 16) by (rewrite HDd; unfold dec_len; lia).
  assert (EEV : zlen (EV2 (idS g i)) = EN1 + 1 + D).
  { rewrite HE1d, HDd. unfold EV2, zlen, dec_len. rewrite !length_app. cbn [length]. lia. }
  exists [(g_S g - 368 - 64, g_S g - 368); (g_S g - 368 + 168, g_S g - 368 + 226)],
    ([(19%bv, Z_to_bv 64 (Z.of_nat i)); (21%bv, Z_to_bv 64 (rec_k (g_in g) i));
    (20%bv, Z_to_bv 64 (g_p g + rec_body (g_in g) i)); (22%bv, Z_to_bv 64 pl); (23%bv, Z_to_bv 64 (rec_addr (g_in g) i));
    (27%bv, Z_to_bv 64 (fw_milli (idS g i))); (8%bv, Z_to_bv 64 (has_fw (idS g i)));
    (18%bv, Z_to_bv 64 (has_model_name (idS g i))); (24%bv, Z_to_bv 64 (major (idS g i)));
    (25%bv, Z_to_bv 64 (minor (idS g i))); (26%bv, Z_to_bv 64 (patch (idS g i)));
    (9%bv, Z_to_bv 64 (spk g 176))] : list (reg * word)),
    [(spk g 168, le8 (Z_to_bv 64 (zlen (EV2 (idS g i))))); (spk g 176, EV2 (idS g i))].
  split.
  { intros x Hx. cbn [outside] in Hx. unfold SLOT_K, SLOT_STACK. lia. }
  split.
  - pose proof (bytes_at_normalize rsegs mem _ _ HRO HEN) as HENn.
    pose proof (bytes_at_normalize rsegs mem _ _ HRO HEV) as HEVn.
    unfold q64, spk, fsp, SLOT_FRAME in HENn, HEVn.
    pose proof (tb_rd8 _ _ _ HENn) as RD168. clear HENn.
    pose proof (munch_refl [(g_S g - 368 - 64, g_S g - 368); (g_S g - 368 + 168, g_S g - 368 + 226)]
      (normalize rsegs mem)) as MU0.
    pose proof (wmono_refl rsegs (normalize rsegs mem)) as WM0.
    unfold SLOT_K, SLOT_STACK in *.
    pose proof (v2_sok _ _ _ (g_S g - 368 + 168) 8%nat WRn ltac:(lia) ltac:(lia)) as HS1.
    unfold rmk. rewrite E2, E3, E4, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27, E8.
    unfold spk, fsp, SLOT_FRAME in *.
    step. step. step. step. step.
    v3_st HS1. rename NW into NW1.
    pose proof (v2_sok _ _ _ (g_S g - 368 + 176 + EN1) 1%nat WRn ltac:(lia) ltac:(lia)) as HS2.
    step. step.
    v3_st HS2. rename NW into NW2.
    match type of NW2 with bytes_at rsegs ?mm ?aa _ =>
      assert (NWd : bytes_at rsegs mm aa [dot]) by (eapply bytes_at_ext; [exact NW2 | vm_compute; reflexivity]) end.
    step. step. step. step. step.
    eapply Exec.evt_cut.
    { eapply PUTDEC with (b := g_S g - 368 + 176) (p := g_S g - 368 + 168) (v := minor (idS g i)) (mn := 1)
        (lo := g_S g - 65536) (N := Z_to_bv 64 (EN1 + 1)).
      - reflexivity.
      - reflexivity.
      - rewrite MState.unsigned_lit by lia. apply Z.mod_small. lia.
      - left. rewrite MState.unsigned_lit by lia. lia.
      - reflexivity.
      - lia.
      - first [exact NW1 | eapply bytes_at_ext; [exact NW1 | f_equal; unfold v_addi;
          rewrite MState.unsigned_lit by lia; reflexivity]].
      - apply (v2_wr_sub _ _ _ _ _ WRn); lia.
      - Z.div_mod_to_equations. lia.
      - rewrite MState.unsigned_lit by lia. rewrite <- HDd. apply (v2_wr_sub _ _ _ _ _ WRn); lia.
      - assumption.
      - rewrite MState.unsigned_lit by lia. apply (v1_stk_sub _ _ _ _ _ _ STn); lia.
      - rewrite MState.unsigned_lit by lia. unfold PUT_DEC_FRAME. lia.
      - rewrite MState.unsigned_lit by lia. rewrite <- HDd. lia.
      - rewrite MState.unsigned_lit by lia. unfold PUT_DEC_FRAME. lia.
      - rewrite !MState.unsigned_lit by lia. rewrite <- HDd. unfold PUT_DEC_FRAME. lia. }
    intros ms' PO. destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' &
      t6' & m' & -> & MU2 & WM' & _ & _ & HDB & HP8).
    pose proof (MState.unsigned_lit (EN1 + 1) ltac:(lia)) as UN.
    rewrite !MState.unsigned_lit in MU2, HDB, HP8 by lia. rewrite ?UN in MU2, HDB, HP8.
    rewrite <- HDd in MU2, HP8. unfold PUT_DEC_FRAME in MU2.
    rewrite (MState.ret_pc_even 0x1337c) by (lia || reflexivity).
    apply Exec.evt_done. eexists _, _. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [repeat (apply Forall_cons; [reflexivity|]); apply Forall_nil|].
    split.
    { eapply munch_trans; [exact MU0|]. eapply munch_weaken; [|exact MU2].
      intros x Hx. cbn [outside] in Hx |- *. repeat split; try exact I; lia. }
    split; [eapply wmono_trans; [exact WM0 | exact WM']|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
    + rewrite EEV. exact HP8.
    + unfold EV2. apply bytes_at_app. split.
      * apply (tb_bytes_keep _ _ _ _ _ HEVn MU2). intros j Hj. rewrite HE1l in Hj.
        cbn [outside]. repeat split; try exact I; lia.
      * rewrite HE1l. apply bytes_at_app. split.
        -- apply (tb_bytes_keep _ _ _ _ _ NWd MU2).
           intros j Hj. cbn [length] in Hj. cbn [outside]. repeat split; try exact I; lia.
        -- replace (g_S g - 368 + 176 + EN1 + Z.of_nat (length [dot])) with (g_S g - 368 + 176 + (EN1 + 1))
             by (cbn [length]; lia).
           exact HDB.
  - intros regs' mem' HRL MU HBL. tb_regs HRL. tb_regs HBL.
    unfold RB12, REC, S7A, FALL, F11, F0, F2, F8, F9, F10.
    unfold NRb, G16, HWb, PLB, IDb, AGN, BEF, LPm in *. unfold q64, u32 in *.
    destruct HHW as (HW1 & HW2 & HW3). unfold SLOT_K, SLOT_STACK in *.
    tb_psplit; try assumption; tb_keep MU.
Qed.

End S.
