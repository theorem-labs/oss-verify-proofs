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

Lemma b20_be : forall b2 b3 : byte,
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b2)) 8))) (bv_unsigned (zxb b3)) = be16 b2 b3.
Proof.
  intros b2 b3. pose proof (tb_byte_range b2) as R2. pose proof (tb_byte_range b3) as R3. unfold zxb.
  rewrite (MState.unsigned_lit (bv_unsigned b2)) by lia. rewrite (MState.unsigned_lit (bv_unsigned b3)) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite (MState.unsigned_lit (bv_unsigned b2 * 256)) by lia.
  rewrite (kb_lor_low (bv_unsigned b2 * 256) (bv_unsigned b3) 8);
    [| lia | lia | change (2 ^ 8) with 256; lia | change (2 ^ 8) with 256; apply Z_mod_mult].
  unfold be16, bz. ring.
Qed.

Ltac b20_br H := lazymatch goal with |- context [if ?c then _ else _] =>
  replace c with false; [cbv iota | symmetry; rewrite b20_be, H; unfold bv_eqb; rewrite Z.eqb_refl; reflexivity] end.

Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis PUTDEC : put_dec_contract.

Lemma seg_B20 : forall i,
  Hrec B APIf ra (Inv_K1334c_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K132f4_at B APIf ra empty) i.
Proof.
  intros i HX g c (pl & HC).
  apply (tb_seg B APIf ra empty FF g 0x132f4 0x1334c _ _ _
    (fun regs m => RB12 g i pl regs m /\ S7A g i regs /\ FALL g i regs /\ RRr g i regs /\ VB g i /\
       q64 m (spk g 168) (zlen (EV1 (idS g i))) /\ bytes_at rsegs m (spk g 176) (EV1 (idS g i))) c HC).
  2: { intros c' HC'. apply HX. exists pl. exact HC'. }
  intros L A regs mem md HF HP HPE.
  destruct HPE as ((HREC & E21 & E20 & E22 & HPL & HID & HAG & HBF & HLP) & E23 & (E27 & E8 & E18 & E24 & E25 & E26) &
    E9 & HVB & E10).
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
  destruct (v1_vb (g_in g) i (proj1 HVB) (proj2 HVB)) as (K8 & _ & _ & HMA & HMI & HPA).
  change (rec_id (g_in g) (S i)) with (idS g i) in HMA, HMI, HPA.
  symmetry in HMA, HMI, HPA.
  pose proof (v2_mmp (idS g i)) as (Hma & Hmi & Hpa).
  pose proof (v1_DEC_len _ 1 Hma ltac:(lia)) as HD1.
  assert (HE1 : 0 + dec_len (major (idS g i)) 1 = zlen (EV1 (idS g i))) by (unfold dec_len, zlen, EV1; lia).
  exists [(g_S g - 368 - 64, g_S g - 368); (g_S g - 368 + 168, g_S g - 368 + 226)],
    ([(19%bv, Z_to_bv 64 (Z.of_nat i)); (21%bv, Z_to_bv 64 (rec_k (g_in g) i));
    (20%bv, Z_to_bv 64 (g_p g + rec_body (g_in g) i)); (22%bv, Z_to_bv 64 pl); (23%bv, Z_to_bv 64 (rec_addr (g_in g) i));
    (27%bv, Z_to_bv 64 (fw_milli (idS g i))); (8%bv, Z_to_bv 64 (has_fw (idS g i)));
    (18%bv, Z_to_bv 64 (has_model_name (idS g i))); (24%bv, Z_to_bv 64 (major (idS g i)));
    (25%bv, Z_to_bv 64 (minor (idS g i))); (26%bv, Z_to_bv 64 (patch (idS g i)));
    (9%bv, Z_to_bv 64 (rec_r (g_in g) i))] : list (reg * word)),
    [(spk g 168, le8 (Z_to_bv 64 (zlen (EV1 (idS g i))))); (spk g 176, EV1 (idS g i))].
  split.
  { intros x Hx. cbn [outside] in Hx. unfold SLOT_K, SLOT_STACK. lia. }
  split.
  - pose proof (bytes_at_normalize rsegs mem _ _ HRO HPL) as HPLn. unfold PLB in HPLn.
    pose proof (tb_rd1 _ _ _ 2 HPLn ltac:(lia) ltac:(lia)) as RD2.
    pose proof (tb_rd1 _ _ _ 3 HPLn ltac:(lia) ltac:(lia)) as RD3.
    pose proof (tb_rd1 _ _ _ 4 HPLn ltac:(lia) ltac:(lia)) as RD4.
    pose proof (tb_rd1 _ _ _ 5 HPLn ltac:(lia) ltac:(lia)) as RD5.
    pose proof (tb_rd1 _ _ _ 6 HPLn ltac:(lia) ltac:(lia)) as RD6.
    pose proof (tb_rd1 _ _ _ 7 HPLn ltac:(lia) ltac:(lia)) as RD7.
    change (Z.to_nat 2) with 2%nat in RD2. change (Z.to_nat 3) with 3%nat in RD3.
    change (Z.to_nat 4) with 4%nat in RD4. change (Z.to_nat 5) with 5%nat in RD5.
    change (Z.to_nat 6) with 6%nat in RD6. change (Z.to_nat 7) with 7%nat in RD7.
    clear HPLn.
    pose proof (munch_refl [(g_S g - 368 - 64, g_S g - 368); (g_S g - 368 + 168, g_S g - 368 + 226)]
      (normalize rsegs mem)) as MU0.
    pose proof (wmono_refl rsegs (normalize rsegs mem)) as WM0.
    unfold SLOT_K, SLOT_STACK in *.
    pose proof (v2_sok _ _ _ (g_S g - 368 + 168) 8%nat WRn ltac:(lia) ltac:(lia)) as HS1.
    unfold rmk. rewrite E2, E3, E4, E9, E10, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27, E8.
    unfold spk, fsp, SLOT_FRAME in *.
    step. if_false.
    step. step. step. step. step. b20_br HMA.
    step. step. step. step. step. b20_br HMI.
    step. step. step. step. step. b20_br HPA.
    step.
    v3_st HS1. rename NW into NW1.
    step. step. step. step. step.
    eapply Exec.evt_cut.
    { eapply PUTDEC with (b := g_S g - 368 + 176) (p := g_S g - 368 + 168) (v := major (idS g i)) (mn := 1)
        (lo := g_S g - 65536) (N := Z_to_bv 64 0).
      - reflexivity.
      - reflexivity.
      - rewrite MState.unsigned_lit by lia. apply Z.mod_small. lia.
      - left. rewrite MState.unsigned_lit by lia. lia.
      - reflexivity.
      - lia.
      - first [exact NW1 | eapply bytes_at_ext; [exact NW1 | vm_compute; reflexivity]].
      - apply (v2_wr_sub _ _ _ _ _ WRn); lia.
      - Z.div_mod_to_equations. lia.
      - change (bv_unsigned (Z_to_bv 64 0)) with 0. apply (v2_wr_sub _ _ _ _ _ WRn); unfold dec_len; lia.
      - assumption.
      - rewrite MState.unsigned_lit by lia. apply (v1_stk_sub _ _ _ _ _ _ STn); lia.
      - rewrite MState.unsigned_lit by lia. unfold PUT_DEC_FRAME. lia.
      - change (bv_unsigned (Z_to_bv 64 0)) with 0. unfold dec_len. lia.
      - rewrite MState.unsigned_lit by lia. unfold PUT_DEC_FRAME. lia.
      - change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite MState.unsigned_lit by lia. unfold dec_len, PUT_DEC_FRAME.
        lia. }
    intros ms' PO. destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' &
      t6' & m' & -> & MU2 & WM' & _ & _ & HDB & HP8).
    change (bv_unsigned (Z_to_bv 64 0)) with 0 in MU2, HDB, HP8.
    rewrite ?MState.unsigned_lit in MU2 by lia. unfold PUT_DEC_FRAME, dec_len in MU2.
    rewrite HE1 in HP8. rewrite Z.add_0_r in HDB.
    rewrite (MState.ret_pc_even 0x1334c) by (lia || reflexivity).
    apply Exec.evt_done. eexists _, _. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [repeat (apply Forall_cons; [reflexivity|]); apply Forall_nil|].
    split.
    { eapply munch_trans; [exact MU0|]. eapply munch_weaken; [|exact MU2].
      intros x Hx. cbn [outside] in Hx |- *. repeat split; try exact I; lia. }
    split; [eapply wmono_trans; [exact WM0 | exact WM']|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
    + exact HP8.
    + exact HDB.
  - intros regs' mem' HRL MU HBL. tb_regs HRL. tb_regs HBL.
    unfold RB12, REC, S7A, FALL, F11, F0, F2, F8, F9, F10, RRr.
    unfold NRb, G16, HWb, PLB, IDb, AGN, BEF, LPm in *. unfold q64, u32 in *.
    destruct HHW as (HW1 & HW2 & HW3). unfold SLOT_K, SLOT_STACK in *.
    tb_psplit; try assumption; tb_keep MU.
Qed.

End S.
