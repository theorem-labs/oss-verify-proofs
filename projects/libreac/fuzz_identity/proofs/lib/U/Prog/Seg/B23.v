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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import reac_identity_reac_ver_str_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import reac_identity_reac_ver_str_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uab1 UTac_uab3.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.

Definition WB23 (S0 EN LV : Z) : list (Z * Z) :=
  [(S0 + 192 + EN, S0 + 192 + EN + 1); (S0 - 64, S0); (S0 + 216, S0 + 216 + LV + 1)].

Ltac ubr := let H := fresh "HU" in if_cases H; zify_cond H; try (exfalso; lia);
  try (exfalso; rewrite Z.mod_small in H by lia; lia).

Section S.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis VERC : lib.U.Prog.reac_identity_reac_ver_str_c.reac_identity_reac_ver_str_contract.

Lemma seg_B23 : forall i,
  Hrec B APIf ra (Inv_U13540_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U13508_at B APIf ra empty) i.
Proof.
  intros i HX g c (pl & HC).
  apply (tb_seg B APIf ra empty FF g 0x13508 0x13540 _ _ _
    (fun regs m => V540 g i pl regs m /\ getr regs 10 = Z_to_bv 64 (VER_LV g i)) c HC).
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
  pose proof (v2_LV (major (idS g i)) (minor (idS g i)) (patch (idS g i))) as HLV.
  pose proof (v2_EV_len (idS g i)) as HEQ.
  pose proof (v2_mmp (idS g i)) as (Hma & Hmi & Hpa).
  remember (lib.Prog.reac_identity_reac_ver_str_c.reac_ver_str_LV (major (idS g i)) (minor (idS g i)) (patch (idS g i)))
    as LV eqn:HLVd.
  remember (zlen (EV (idS g i))) as EN eqn:HENd.
  assert (HENl : Z.of_nat (length (EV (idS g i))) = EN) by (rewrite HENd; reflexivity).
  exists (WB23 (g_S g - 384) EN LV),
    ([(8%bv, Z_to_bv 64 EN); (10%bv, Z_to_bv 64 LV); (9%bv, Z_to_bv 64 (Z.of_nat i));
    (20%bv, Z_to_bv 64 (rec_k (g_in g) i)); (26%bv, Z_to_bv 64 (g_p g + rec_c (g_in g) (S i)));
    (21%bv, Z_to_bv 64 pl); (22%bv, Z_to_bv 64 (rec_addr (g_in g) i));
    (23%bv, Z_to_bv 64 (fw_milli (idS g i))); (18%bv, Z_to_bv 64 (has_fw (idS g i)));
    (25%bv, Z_to_bv 64 (major (idS g i))); (19%bv, Z_to_bv 64 (minor (idS g i)));
    (27%bv, Z_to_bv 64 (patch (idS g i))); (24%bv, Z_to_bv 64 (rec_r (g_in g) i))] : list (reg * word)),
    [(spk g 192, EV (idS g i) ++ [z8]); (spk g 216, id_VER (idS g i) ++ [z8])].
  split.
  { intros x Hx. unfold WB23 in Hx. cbn [outside] in Hx. unfold SLOT_K, SLOT_STACK. lia. }
  split.
  - pose proof (bytes_at_normalize rsegs mem _ _ HRO HEN) as HENn.
    pose proof (bytes_at_normalize rsegs mem _ _ HRO HEV) as HEVn.
    pose proof (bytes_at_normalize rsegs mem _ _ HRO HEVb) as H40n.
    pose proof (bytes_at_normalize rsegs mem _ _ HRO HID) as HIDn.
    unfold q64, EVb, EVN, IDb, spk, fsp, SLOT_FRAME in HENn, HEVn, H40n, HIDn.
    pose proof (tb_rd8 _ _ _ HENn) as RD184. clear HENn.
    pose proof (tb_rd8 _ _ _ H40n) as RD40.
    pose proof (bytes_at_read rsegs _ _ _ 22 2 HIDn ltac:(lia) ltac:(lia)) as RI22.
    replace (g_S g - 384 + 146 + 22) with (g_S g - 384 + 168) in RI22 by lia.
    pose proof (bytes_at_read rsegs _ _ _ 24 2 HIDn ltac:(lia) ltac:(lia)) as RI24.
    replace (g_S g - 384 + 146 + 24) with (g_S g - 384 + 170) in RI24 by lia.
    pose proof (bytes_at_read rsegs _ _ _ 26 2 HIDn ltac:(lia) ltac:(lia)) as RI26.
    replace (g_S g - 384 + 146 + 26) with (g_S g - 384 + 172) in RI26 by lia.
    pose proof (munch_refl (WB23 (g_S g - 384) EN LV) (normalize rsegs mem)) as MU0.
    pose proof (wmono_refl rsegs (normalize rsegs mem)) as WM0.
    unfold WB23 in MU0.
    unfold SLOT_K, SLOT_STACK in *.
    pose proof (v2_sok _ _ _ (g_S g - 384 + 192 + EN) 1%nat WRn ltac:(lia) ltac:(lia)) as HS.
    unfold rmk. rewrite E2, E3, E4, E9, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27.
    unfold spk, fsp, SLOT_FRAME in *.
    step. step. step. ubr.
    step. step. ubr.
    step. step. step.
    assert (EMa : zext 64 (bv_extract 0 16 (le_bytes_to_word (firstn 2 (skipn (Z.to_nat 22) (rec_id (g_in g) (S i)))))) =
      Z_to_bv 64 (major (idS g i))).
    { change (Z.to_nat 22) with 22%nat. rewrite (ua_lhu _ 22) by (rewrite LID1; lia). reflexivity. }
    assert (EMi : zext 64 (bv_extract 0 16 (le_bytes_to_word (firstn 2 (skipn (Z.to_nat 24) (rec_id (g_in g) (S i)))))) =
      Z_to_bv 64 (minor (idS g i))).
    { change (Z.to_nat 24) with 24%nat. rewrite (ua_lhu _ 24) by (rewrite LID1; lia). reflexivity. }
    assert (EMp : zext 64 (bv_extract 0 16 (le_bytes_to_word (firstn 2 (skipn (Z.to_nat 26) (rec_id (g_in g) (S i)))))) =
      Z_to_bv 64 (patch (idS g i))).
    { change (Z.to_nat 26) with 26%nat. rewrite (ua_lhu _ 26) by (rewrite LID1; lia). reflexivity. }
    rewrite EMa, EMi, EMp.
    step. step. step.
    v2_after_st.
    lazymatch goal with |- Exec.evt _ _ (MState.MS _ _ _ _ _ ?m1 _) =>
      assert (H192 : bytes_at rsegs m1 (g_S g - 384 + 192) (EV (idS g i) ++ [z8])) end.
    { apply bytes_at_app. split; [exact HEVn|]. rewrite HENl.
      match type of NW with bytes_at _ _ ?a _ => replace (g_S g - 384 + 192 + EN) with a by lia end.
      eapply bytes_at_ext; [exact NW | vm_compute; reflexivity]. }
    clear HEVn NW.
    lazymatch goal with |- Exec.evt _ _ (MState.MS _ _ _ _ _ ?m1 _) =>
      destruct (stk_split rsegs m1 _ (g_S g - 384) _ STn ltac:(lia)) as [ST1 _] end.
    step. step. step.
    eapply Exec.evt_cut.
    { eapply VERC with (ma := major (idS g i)) (mi := minor (idS g i)) (pa := patch (idS g i))
        (o := g_S g - 384 + 216) (c := 20) (lo := g_S g - 65536).
      all: first [ reflexivity | (f_equal; lia) | lia
                 | (rewrite MState.unsigned_lit by lia; first [exact ST1 | lia])
                 | (intros _ _; split; [apply (v2_wr_sub _ _ _ _ _ WRn); lia
                                       | right; rewrite MState.unsigned_lit by lia; lia]) ]. }
    intros ms' PO. destruct PO as (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & m' &
      -> & WM' & _ & HIF).
    assert (EO : ((g_S g - 384 + 216 =? 0) || (20 <? 20)) = false).
    { apply orb_false_iff. split; [apply Z.eqb_neq; lia | reflexivity]. }
    rewrite EO in HIF. cbv iota in HIF. rewrite <- HLVd in HIF.
    destruct HIF as (-> & MU2 & HVER).
    rewrite MState.unsigned_lit in MU2 by lia.
    rewrite (MState.ret_pc_even 0x13540) by (lia || reflexivity).
    apply Exec.evt_done. eexists _, _. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [repeat (apply Forall_cons; [reflexivity|]); apply Forall_nil|].
    split.
    { eapply munch_trans; [exact MU0|]. eapply munch_weaken; [|exact MU2].
      intros x Hx. unfold WB23 in Hx |- *. cbn [outside] in Hx |- *. repeat split; try exact I; lia. }
    split; [eapply wmono_trans; [exact WM0 | exact WM']|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
    + apply (tb_bytes_keep _ _ _ _ _ H192 MU2). intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
      cbn [outside]. repeat split; try exact I; lia.
    + exact HVER.
  - intros regs' mem' HRL MU HBL. tb_regs HRL. tb_regs HBL.
    unfold WB23 in MU.
    unfold V540, VER_LV, RB12, REC, S6A, FNM, F7, F2, F9, F3, F11, RRr. rewrite <- HLVd, <- HENd.
    unfold NRb, G24, HWb, EVb, PLB, IDb, AGN, BEF, LPm, cstr in *. unfold q64, u32 in *.
    destruct HHW as (HW1 & HW2 & HW3). unfold SLOT_K, SLOT_STACK in *.
    tb_psplit; try assumption; tb_keep MU.
Qed.

End S.
