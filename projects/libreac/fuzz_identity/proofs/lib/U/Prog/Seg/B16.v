From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac ZBridge
Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec RcIdentModel SlotModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require reac_identity_fw_str_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uab1 UTac_uab2.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.

Ltac sb2_br b rw :=
  lazymatch goal with
  | |- Exec.evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b; [cbv iota | symmetry; rw; solve_cond]
  end.

Lemma sb2_dg_unsigned : forall x, 0 <= x <= 9 -> bv_unsigned (dg x) = 48 + x.
Proof.
  intros x Hx. unfold dg. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  apply Z.mod_small. lia.
Qed.

Ltac xtrap := match goal with H : Z.lxor (Z.b2z (?a <? ?b)) (Z.b2z (?c <? ?d)) = 0 |- _ =>
  rewrite (proj2 (Z.ltb_lt a b)) in H by lia; rewrite (proj2 (Z.ltb_ge c d)) in H by lia; discriminate H end.
Ltac ubr := let H := fresh "HU" in if_cases H; zify_cond H; try (exfalso; lia); try xtrap;
  try (exfalso; rewrite Z.mod_small in H by lia; lia).

Section Seg.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.

Lemma seg_B16 : forall i,
  Hrec B APIf ra (Inv_U13660_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U13314_at B APIf ra empty) i.
Proof.
  intros i H g c (pl & L & A & regs & mem & md & -> & HFR & HPERM & HP).
  destruct HP as (HRB & HFALL & HRR & H22 & HFWA & HV & HS).
  pose proof HFR as HFR'. unfold FR in HFR'. cbv zeta in HFR'.
  destruct HFR' as (HGV & H2s & _ & _ & _ & _ & _ & _ & HMR & _).
  pose proof (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hlz & _).
  pose proof HRB as (HREC & H20 & H26 & H21 & HPLB & HID & HAGN & HBEF & HLPm).
  assert (Hpl : In (pl, rec_k (g_in g) i) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HPERM)); left; reflexivity).
  destruct (t_block_range B APIf ra empty FF L A mem md _ _ HMR Hpl) as [PL1 PL2].
  pose proof alloc_ceiling_value as AC.
  destruct (sb2_FR_basics B APIf ra empty FF g _ _ L A regs mem md HFR)
    as (HAC & HSK & HS47 & HSm & Efsp & _ & _ & _ & _ & _ & _).
  destruct HFWA as [FR1 FA0].
  destruct (sb2_rec_fw (g_in g) i FR1) as (_ & K4 & DIG & _ & FWM & FWR);
    [rewrite FA0; unfold ADDR_FIRMWARE, ADDR_MODEL_NAME; lia | rewrite FA0; unfold ADDR_FIRMWARE, ADDR_REAC_VERSION; lia |].
  pose proof (rec_pl_length (g_in g) i) as PLL.
  pose proof (rec_k_range (g_in g) i) as KR.
  assert (PL4 : (4 <= length (rec_pl (g_in g) i))%nat) by lia.
  assert (ALLD : all_digits (firstn 4 (rec_pl (g_in g) i)) = true).
  { unfold all_digits. apply forallb_forall. intros b Hb.
    apply In_nth with (d := zb 0) in Hb. destruct Hb as (j & Hj & <-).
    rewrite length_firstn in Hj. rewrite nth_first by lia. apply Z.leb_le. apply DIG. lia. }
  unfold idS in HS. rewrite FWM, (sb2_FW_digits _ PL4 ALLD) in HS.
  unfold cstr in HS. cbn [app] in HS.
  unfold bz, nthb in DIG, HS.
  set (p0 := nth 0 (rec_pl (g_in g) i) (zb 0)) in *.
  set (p1 := nth 1 (rec_pl (g_in g) i) (zb 0)) in *.
  set (p2 := nth 2 (rec_pl (g_in g) i) (zb 0)) in *.
  set (p3 := nth 3 (rec_pl (g_in g) i) (zb 0)) in *.
  pose proof (DIG 0%nat ltac:(lia)) as D0. pose proof (DIG 1%nat ltac:(lia)) as D1.
  pose proof (DIG 2%nat ltac:(lia)) as D2. pose proof (DIG 3%nat ltac:(lia)) as D3.
  fold p0 in D0. fold p1 in D1. fold p2 in D2. fold p3 in D3.
  pose proof (bv_unsigned_in_range 8 p0) as B0. pose proof (bv_unsigned_in_range 8 p1) as B1.
  pose proof (bv_unsigned_in_range 8 p2) as B2. pose proof (bv_unsigned_in_range 8 p3) as B3.
  change (bv_modulus 8) with 256 in B0, B1, B2, B3.
  assert (U0 : bv_unsigned (dg (bv_unsigned p0)) = 48 + bv_unsigned p0) by (apply sb2_dg_unsigned; lia).
  assert (U1 : bv_unsigned (dg (bv_unsigned p1)) = 48 + bv_unsigned p1) by (apply sb2_dg_unsigned; lia).
  assert (U2 : bv_unsigned (dg (bv_unsigned p2)) = 48 + bv_unsigned p2) by (apply sb2_dg_unsigned; lia).
  assert (U3 : bv_unsigned (dg (bv_unsigned p3)) = 48 + bv_unsigned p3) by (apply sb2_dg_unsigned; lia).
  assert (RP0 : ov_read_bytes rsegs mem (wa pl) 1 = Some [p0]).
  { apply (sb2_bytes_at_rd1' rsegs mem pl _ 0 _ HPLB); [lia | lia]. }
  assert (RP1 : ov_read_bytes rsegs mem (wa (pl + 1)) 1 = Some [p1]).
  { apply (sb2_bytes_at_rd1' rsegs mem pl _ 1 _ HPLB); [lia | lia]. }
  assert (RP2 : ov_read_bytes rsegs mem (wa (pl + 2)) 1 = Some [p2]).
  { apply (sb2_bytes_at_rd1' rsegs mem pl _ 2 _ HPLB); [lia | lia]. }
  assert (RP3 : ov_read_bytes rsegs mem (wa (pl + 3)) 1 = Some [p3]).
  { apply (sb2_bytes_at_rd1' rsegs mem pl _ 3 _ HPLB); [lia | lia]. }
  assert (RS0 : ov_read_bytes rsegs mem (wa (fsp g + 192)) 1 = Some [dg (bv_unsigned p0)]).
  { apply (sb2_bytes_at_rd1' rsegs mem (spk g 192) _ 0 _ HS); [cbn; lia | unfold spk; lia]. }
  assert (RS1 : ov_read_bytes rsegs mem (wa (fsp g + 193)) 1 = Some [Z_to_bv 8 0x2e]).
  { apply (sb2_bytes_at_rd1' rsegs mem (spk g 192) _ 1 _ HS); [cbn; lia | unfold spk; lia]. }
  assert (RS2 : ov_read_bytes rsegs mem (wa (fsp g + 194)) 1 = Some [dg (bv_unsigned p1)]).
  { apply (sb2_bytes_at_rd1' rsegs mem (spk g 192) _ 2 _ HS); [cbn; lia | unfold spk; lia]. }
  assert (RS3 : ov_read_bytes rsegs mem (wa (fsp g + 195)) 1 = Some [dg (bv_unsigned p2)]).
  { apply (sb2_bytes_at_rd1' rsegs mem (spk g 192) _ 3 _ HS); [cbn; lia | unfold spk; lia]. }
  assert (RS4 : ov_read_bytes rsegs mem (wa (fsp g + 196)) 1 = Some [dg (bv_unsigned p3)]).
  { apply (sb2_bytes_at_rd1' rsegs mem (spk g 192) _ 4 _ HS); [cbn; lia | unfold spk; lia]. }
  assert (G2 : reg_get regs 2 = Z_to_bv 64 (fsp g)) by exact H2s.
  assert (G22 : reg_get regs 22 = Z_to_bv 64 5) by exact H22.
  assert (G21 : reg_get regs 21 = Z_to_bv 64 pl) by exact H21.
  eapply (sb2_seg_run B APIf ra empty FF regs 0x13314 mem md _
    (fun R pc' m' => pc' = 0x13660 /\ m' = mem /\
       sb2_agree regs R [2; 3; 4; 9; 20; 21; 22; 26]) Hh Hlz).
  - unfold Regs6ss.mkR_of. rewrite G2, G22, G21.
    step. step. sb2_br false idtac.
    step. step. step. step. sb2_br false ltac:(unfold bv_eqb, zxb; rewrite U0, (MState.unsigned_lit (bv_unsigned p0)) by lia; rewrite !MState.unsigned_lit by lia).
    step. step. step. ubr.
    step. step. step. sb2_br false idtac.
    step. step. step. ubr.
    step. step. step. step. sb2_br false ltac:(unfold bv_eqb, zxb; rewrite U1, (MState.unsigned_lit (bv_unsigned p1)) by lia; rewrite !MState.unsigned_lit by lia).
    step. step. step. ubr.
    step. step. ubr.
    step. step. step. step. sb2_br false ltac:(unfold bv_eqb, zxb; rewrite U2, (MState.unsigned_lit (bv_unsigned p2)) by lia; rewrite !MState.unsigned_lit by lia).
    step. step. step. ubr.
    step. step. ubr.
    step. step. step. step. sb2_br false ltac:(unfold bv_eqb, zxb; rewrite U3, (MState.unsigned_lit (bv_unsigned p3)) by lia; rewrite !MState.unsigned_lit by lia).
    step.
    apply evt_done. do 3 eexists. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    intros k Hk. cbn [In] in Hk. repeat destruct Hk as [<-|Hk]; try contradiction;
      first [reflexivity | rewrite <- G2; reflexivity | rewrite <- G21; reflexivity | rewrite <- G22; reflexivity].
  - intros R R' pc' m' (-> & -> & AG) XR.
    assert (AG' : sb2_agree regs R' [2; 3; 4; 9; 20; 21; 22; 26])
      by (apply (sb2_agree_eqv regs R R' _ AG XR); intros k Hk; cbn [In] in Hk;
          repeat destruct Hk as [<-|Hk]; try contradiction; lia).
    pose proof HREC as (HNR & H9 & HNRb & HG24 & HHW & HEV).
    apply H. exists pl, L, A, R', mem, md. split; [reflexivity|].
    split; [apply (sb2_FR_regs B APIf ra empty FF g _ _ L A regs mem md R' HFR HPERM);
            apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
    split; [exact HPERM|].
    split; [exact HNR|].
    split; [sb2_ag AG' 9; exact H9|].
    split; [exact HNRb|]. split; [exact HG24|].
    split.
    { unfold HWb, rec_have, rec_hwb in *. rewrite sb2_rec_hw_keep; [exact HHW|].
      rewrite FA0. unfold ADDR_FIRMWARE, ADDR_REAC_VERSION. lia. }
    split; [exact HEV|].
    split; [exact HID|].
    split; [sb2_ag AG' 26; exact H26|].
    split; [sb2_ag AG' 20; exact H20|].
    split; [exact HLPm|].
    sb2_ag AG' 21. exact H21.
Qed.

End Seg.
