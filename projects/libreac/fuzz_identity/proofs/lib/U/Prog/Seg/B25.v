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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uab1 UTac_uab3.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.

Lemma b25_val : forall b0 b1 b2 b3 : byte,
  bv_unsigned (Z_to_bv 64 (Z.lor
    (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b3)) 24)))
                                     (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b2)) 16))))))
    (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b1)) 8)))
                                     (bv_unsigned (zxb b0))))))) =
  bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3.
Proof.
  intros b0 b1 b2 b3. pose proof (tb_byte_range b0). pose proof (tb_byte_range b1).
  pose proof (tb_byte_range b2). pose proof (tb_byte_range b3). unfold zxb.
  rewrite (MState.unsigned_lit (bv_unsigned b0)) by lia. rewrite (MState.unsigned_lit (bv_unsigned b1)) by lia.
  rewrite (MState.unsigned_lit (bv_unsigned b2)) by lia. rewrite (MState.unsigned_lit (bv_unsigned b3)) by lia.
  rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. change (2 ^ 16) with 65536. change (2 ^ 24) with 16777216.
  rewrite (MState.unsigned_lit (bv_unsigned b3 * 16777216)) by lia.
  rewrite (MState.unsigned_lit (bv_unsigned b2 * 65536)) by lia.
  rewrite (MState.unsigned_lit (bv_unsigned b1 * 256)) by lia.
  rewrite (kb_lor_low (bv_unsigned b3 * 16777216) (bv_unsigned b2 * 65536) 24);
    [| lia | lia | change (2 ^ 24) with 16777216; lia | change (2 ^ 24) with 16777216; apply Z_mod_mult].
  rewrite (kb_lor_low (bv_unsigned b1 * 256) (bv_unsigned b0) 8);
    [| lia | lia | change (2 ^ 8) with 256; lia | change (2 ^ 8) with 256; apply Z_mod_mult].
  rewrite (MState.unsigned_lit (bv_unsigned b3 * 16777216 + bv_unsigned b2 * 65536)) by lia.
  rewrite (MState.unsigned_lit (bv_unsigned b1 * 256 + bv_unsigned b0)) by lia.
  rewrite (kb_lor_low (bv_unsigned b3 * 16777216 + bv_unsigned b2 * 65536) (bv_unsigned b1 * 256 + bv_unsigned b0) 16);
    [| lia | lia | change (2 ^ 16) with 65536; lia |].
  2: { change (2 ^ 16) with 65536.
       replace (bv_unsigned b3 * 16777216 + bv_unsigned b2 * 65536) with ((bv_unsigned b3 * 256 + bv_unsigned b2) * 65536)
         by ring. apply Z_mod_mult. }
  rewrite MState.unsigned_lit by lia. ring.
Qed.

Lemma b25_le4 : forall b0 b1 b2 b3 : byte,
  le4 (Z_to_bv 64 (Z.lor
    (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b3)) 24)))
                                     (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b2)) 16))))))
    (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b1)) 8)))
                                     (bv_unsigned (zxb b0))))))) = [b0; b1; b2; b3].
Proof.
  intros b0 b1 b2 b3. unfold le4. rewrite b25_val.
  pose proof (tb_byte_range b0). pose proof (tb_byte_range b1).
  pose proof (tb_byte_range b2). pose proof (tb_byte_range b3).
  cbn [Z_to_le_bytes]. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  f_equal; [|f_equal; [|f_equal; [|f_equal]]];
    apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 8) with 256;
    Z.div_mod_to_equations; lia.
Qed.

Lemma b25_first8 : forall l : list byte, (8 <= length l)%nat ->
  firstn 8 l = [nthb l 0; nthb l 1; nthb l 2; nthb l 3] ++ [nthb l 4; nthb l 5; nthb l 6; nthb l 7].
Proof.
  intros l H. do 8 (destruct l as [|? l]; [cbn in H; lia|]). reflexivity.
Qed.

Section S.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.

Lemma seg_B25 : forall i,
  Hrec B APIf ra (Inv_U13660_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U13558_at B APIf ra empty) i.
Proof.
  intros i HX g c (pl & HC).
  apply (tb_seg B APIf ra empty FF g 0x13558 0x13660 _ _ _
    (fun regs m => Z.of_nat i < NR g /\ getr regs 9 = Z_to_bv 64 (Z.of_nat i) /\ NRb g m /\ G24 g m /\
       HWb g (S i) 0 m /\ EVb g m /\ IDb g (S i) m /\
       getr regs 26 = Z_to_bv 64 (g_p g + rec_c (g_in g) (S i)) /\
       getr regs 20 = Z_to_bv 64 (rec_k (g_in g) i) /\ LPm g i m /\ getr regs 21 = Z_to_bv 64 pl) c HC).
  2: { intros c' HC'. apply HX. exists pl. exact HC'. }
  intros L A regs mem md HF HP HPE.
  destruct HPE as (((HREC & E20 & E26 & E21 & HPL & HID & HAG & HBF & HLP) & E22 & (E23 & E18 & E25 & E19 & E27) &
    E24 & HVB & HEN & HEV & E8 & HVR) & E10).
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
  pose proof (rec_id_length (g_in g) (S i)) as LID1. unfold ID_SIZE in LID1.
  destruct (v1_vb (g_in g) i (proj1 HVB) (proj2 HVB)) as (K8 & _ & _ & _ & _ & _).
  assert (HWS : rec_hw (g_in g) (S i) = Some (firstn 8 (rec_pl (g_in g) i))).
  { cbn [rec_hw]. rewrite (proj2 HVB), Z.eqb_refl.
    replace (8 <=? rec_k (g_in g) i) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
  exists [(g_S g - 384 + 32, g_S g - 384 + 40); (g_S g - 384 + 132, g_S g - 384 + 140)],
    ([(9%bv, Z_to_bv 64 (Z.of_nat i)); (26%bv, Z_to_bv 64 (g_p g + rec_c (g_in g) (S i)));
      (20%bv, Z_to_bv 64 (rec_k (g_in g) i)); (21%bv, Z_to_bv 64 pl)] : list (reg * word)),
    [(spk g 32, le8 (Z_to_bv 64 1)); (spk g 132, firstn 8 (rec_pl (g_in g) i))].
  split.
  { intros x Hx. cbn [outside] in Hx. unfold SLOT_K, SLOT_STACK. lia. }
  split.
  - pose proof (bytes_at_normalize rsegs mem _ _ HRO HPL) as HPLn. unfold PLB in HPLn.
    pose proof (tb_rd1 _ _ _ 0 HPLn ltac:(lia) ltac:(lia)) as RD0.
    pose proof (tb_rd1 _ _ _ 1 HPLn ltac:(lia) ltac:(lia)) as RD1.
    pose proof (tb_rd1 _ _ _ 2 HPLn ltac:(lia) ltac:(lia)) as RD2.
    pose proof (tb_rd1 _ _ _ 3 HPLn ltac:(lia) ltac:(lia)) as RD3.
    pose proof (tb_rd1 _ _ _ 4 HPLn ltac:(lia) ltac:(lia)) as RD4.
    pose proof (tb_rd1 _ _ _ 5 HPLn ltac:(lia) ltac:(lia)) as RD5.
    pose proof (tb_rd1 _ _ _ 6 HPLn ltac:(lia) ltac:(lia)) as RD6.
    pose proof (tb_rd1 _ _ _ 7 HPLn ltac:(lia) ltac:(lia)) as RD7.
    change (Z.to_nat 0) with 0%nat in RD0. change (Z.to_nat 1) with 1%nat in RD1.
    change (Z.to_nat 2) with 2%nat in RD2. change (Z.to_nat 3) with 3%nat in RD3.
    change (Z.to_nat 4) with 4%nat in RD4. change (Z.to_nat 5) with 5%nat in RD5.
    change (Z.to_nat 6) with 6%nat in RD6. change (Z.to_nat 7) with 7%nat in RD7.
    clear HPLn.
    pose proof (munch_refl [(g_S g - 384 + 32, g_S g - 384 + 40); (g_S g - 384 + 132, g_S g - 384 + 140)]
      (normalize rsegs mem)) as MU0.
    pose proof (wmono_refl rsegs (normalize rsegs mem)) as WM0.
    unfold SLOT_K, SLOT_STACK in *.
    pose proof (v2_sok _ _ _ (g_S g - 384 + 132) 4%nat WRn ltac:(lia) ltac:(lia)) as HS3.
    unfold rmk. rewrite E2, E3, E4, E10, E9, E26, E20, E21.
    unfold spk, fsp, SLOT_FRAME in *.
    step. if_false.
    do 20 step.
    step. v3_st HS3. rename NW into NW3.
    pose proof (v2_sok _ _ _ (g_S g - 384 + 136) 4%nat WRn ltac:(lia) ltac:(lia)) as HS4.
    step. v3_st HS4. rename NW into NW4.
    pose proof (v2_sok _ _ _ (g_S g - 384 + 32) 8%nat WRn ltac:(lia) ltac:(lia)) as HS1.
    step. step. v3_st HS1. rename NW into NW1.
    step.
    rewrite b25_le4 in NW3, NW4.
    apply Exec.evt_done. eexists _, _. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [repeat (apply Forall_cons; [reflexivity|]); apply Forall_nil|].
    split; [exact MU0|]. split; [exact WM0|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
    + exact NW1.
    + rewrite (b25_first8 _ K8). apply bytes_at_app. split; [exact NW3|]. cbn [length].
      replace (g_S g - 384 + 132 + Z.of_nat 4) with (g_S g - 384 + 136) by lia. exact NW4.
  - intros regs' mem' HRL MU HBL. tb_regs HRL. tb_regs HBL.
    unfold NRb, G24, HWb, EVb, IDb, LPm in *. unfold q64, u32 in *.
    destruct HHW as (HW1 & HW2 & HW3).
    unfold rec_have, rec_hwb. rewrite HWS.
    unfold SLOT_K, SLOT_STACK in *.
    tb_psplit; try assumption; tb_keep MU.
Qed.

End S.
