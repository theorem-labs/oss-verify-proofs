From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require RcIdentModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Tac_si.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Exec Step Tac.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0 Contract FrameAPI KindBGlue MemNorm.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU strlen_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uhj UTac_uhj_i.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.


Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Section I10.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.

Lemma step10 : forall g q,
  Hcut B APIf ra (Inv_U13e54 B APIf ra empty) ->
  (forall c, Inv_U13e08_at B APIf ra empty g (S q) c -> Rz (ms_segs B) c (Post B APIf ra g)) ->
  forall c, Inv_U13e08_at B APIf ra empty g q c -> Rz (ms_segs B) c (Post B APIf ra g).
Proof.
  intros g q HE0 HN c (nm & tk & dp & HC).
  eapply (seg_go2 B APIf ra empty FF (fun g' c => g' = g /\ Inv_U13e08_at B APIf ra empty g (S q) c)
    (Inv_U13e54 B APIf ra empty)).
  { intros g' c' (-> & H). exact (HN c' H). }
  { exact HE0. }
  { intros c' HC'. split; [reflexivity|]. exists nm, tk, dp. exact HC'. }
  { intros c' HC'. exists nm, tk, dp. exact HC'. }
  { exact HC. }
  intros L A regs mem md HFR HPM HP.
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct HP as ((HI & R0) & Hq & E10 & E11 & E12 & E13 & E14 & E15 & E16).
  pose proof HI as (HID & E9 & HQ56 & HQ48 & E20 & E21 & E22 & E23 & E24 & E25 & E19 & HO & HE).
  destruct (HO R0) as (C1 & C2 & C3).
  destruct (Tac_si.n_r0 _ R0) as [Wk _].
  pose proof (n_ln_le (g_in g) Wk) as LN. unfold n_ln in LN.
  pose proof (Tac_si.nzb_EXP_NM _ Wk) as NZE.
  pose proof (Tac_si.dropped_range (n_EXP_NM (g_in g)) q) as DR.
  pose proof (Tac_si.dropped_le (n_EXP_NM (g_in g)) q) as DL.
  destruct (nmb_in _ _ _ _ _ _ HPM) as (N1 & N2 & N3).
  destruct (FR_parts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (_ & _ & _ & _ & HMR & _).
  pose proof (blk_range B APIf _ _ _ _ _ _ HMR N1) as [BN1 BN2].
  pose proof (blk_range B APIf _ _ _ _ _ _ HMR N2) as [BT1 BT2].
  pose proof YM05.alloc_ceiling_value as [AC1 AC2].
  pose proof (Tac_si.caps_range (g_in g)) as CRg. unfold bsz in BN2, BT2.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO C1) as C1n.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO C2) as C2n.
  pose proof (cstr_byte _ _ _ q C1n Hq) as RN.
  assert (KMm : forall m', mem_rel rsegs m' (normalize rsegs mem) -> KM [] mem m').
  { intros m' HREL. exact (KM_of [] mem (normalize rsegs mem) m' HRO (Frame.munch_refl _ _) HREL). }
  assert (HOk : forall m', mem_rel rsegs m' (normalize rsegs mem) -> OUTS g nm tk dp m').
  { intros m' HREL. exact (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md (normalize rsegs mem) m' HFR HPM
      (munch_SWIN g [] _ _ (Frame.munch_refl _ _) (Forall_nil _)) HREL HO). }
  assert (HIR : forall R' m', mem_rel rsegs m' (normalize rsegs mem) ->
    getr R' 9 = getr regs 9 -> getr R' 20 = getr regs 20 -> getr R' 21 = getr regs 21 ->
    getr R' 22 = getr regs 22 -> getr R' 23 = getr regs 23 -> getr R' 24 = getr regs 24 ->
    getr R' 25 = getr regs 25 -> getr R' 19 = getr regs 19 -> IR g nm tk dp R' m').
  { intros R' m' HREL F9 F20 F21 F22 F23 F24 F25 F19. split; [|exact R0].
    exact (IRb_keep g nm tk dp regs mem R' m' [] HI (KMm m' HREL) (HOk m' HREL) I I I I I
      F9 F20 F21 F22 F23 F24 F25 F19). }
  assert (TL : Z.of_nat (length (n_TK (g_in g))) =
    Z.of_nat (length (n_EXP_NM (g_in g))) - dropped (n_EXP_NM (g_in g)) (length (n_EXP_NM (g_in g)))).
  { unfold n_TK. apply Tac_si.tok_len_full. }
  unfold rmk, Frame.mkR. rewrite E2, E10, E11, E12, E13, E14, E15, E16, E21.
  destruct (Nat.eq_dec q (length (n_EXP_NM (g_in g)))) as [EQ|LT].
  - rewrite EQ, Tac_si.nthb_snoc_eq in RN.
    step. change (zxb z8) with (Z_to_bv 64 0).
    step. br_if.
    apply (fin_r g mem regs _ _ _ _ _ (normalize rsegs mem) (Frame.munch_refl _ _) (Frame.wmono_refl _ _) HSTK0);
      [rewrite E2; reflexivity | reflexivity | reflexivity |].
    intros R' m' HG HREL. split; [apply (HIR R' m' HREL); kr HG|].
    split; [|kr HG].
    rewrite HG. greg2. f_equal. unfold zlen. rewrite TL, <- EQ. lia.
  - assert (Lq : (q < length (n_EXP_NM (g_in g)))%nat) by lia.
    rewrite Tac_si.nthb_snoc_lt in RN by exact Lq.
    pose proof (Tac_si.nzb_nth _ _ NZE Lq) as NZ.
    pose proof (bz_range (RcIdentModel.nthb (n_EXP_NM (g_in g)) q)) as BR.
    step. rewrite Tac_si.zxb_bz.
    step. rewrite bv_eqb_lit by lia.
    replace (RcIdentModel.bz (RcIdentModel.nthb (n_EXP_NM (g_in g)) q) =? 0) with false
      by (symmetry; apply Z.eqb_neq; exact NZ).
    br_if.
    destruct (Z.eq_dec (RcIdentModel.bz (RcIdentModel.nthb (n_EXP_NM (g_in g)) q)) 45) as [E45|N45];
      [destruct (Z.eq_dec (dropped (n_EXP_NM (g_in g)) q) 0) as [D0|D1]|].
    + pose proof (Tac_si.tok_dash_drop _ _ Lq E45 D0) as DS.
      step. rewrite bv_eqb_lit by lia.
      replace (RcIdentModel.bz (RcIdentModel.nthb (n_EXP_NM (g_in g)) q) =? 45) with true
        by (rewrite E45; reflexivity).
      br_if.
      step. rewrite bv_eqb_lit by lia.
      replace (dropped (n_EXP_NM (g_in g)) q =? 0) with true by (rewrite D0; reflexivity).
      br_if.
      step. step. step. step. step. brz.
      apply (fin_l g mem regs _ _ _ _ _ (normalize rsegs mem) (Frame.munch_refl _ _) (Frame.wmono_refl _ _) HSTK0);
        [rewrite E2; reflexivity | reflexivity | reflexivity |].
      intros R' m' HG HREL. split; [apply (HIR R' m' HREL); kr HG|].
      split; [lia|].
      split; [rg HG; rewrite DS, D0; lia|]. split; [rg HG|]. split; [rewrite HG; greg2; rewrite DS; reflexivity|].
      split; [kr HG|]. split; [kr HG|]. split; [kr HG|]. rg HG.
    + assert (D1' : dropped (n_EXP_NM (g_in g)) q = 1) by lia.
      assert (HnA : ~ (RcIdentModel.bz (RcIdentModel.nthb (n_EXP_NM (g_in g)) q) = 45 /\
        dropped (n_EXP_NM (g_in g)) q = 0)) by lia.
      pose proof (Tac_si.tok_other_keep _ _ Lq HnA) as DK.
      destruct (Tac_si.tok_at _ _ Lq HnA) as [TI TV].
      pose proof (cstr_byte _ _ _ (Z.to_nat (Z.of_nat q - dropped (n_EXP_NM (g_in g)) q)) C2n
        ltac:(unfold n_TK; lia)) as RT.
      rewrite Z2Nat.id in RT by lia.
      change (n_TK (g_in g)) with (TOK (n_EXP_NM (g_in g))) in RT.
      rewrite Tac_si.nthb_snoc_lt in RT by exact TI. rewrite TV in RT.
      step. rewrite bv_eqb_lit by lia.
      replace (RcIdentModel.bz (RcIdentModel.nthb (n_EXP_NM (g_in g)) q) =? 45) with true
        by (rewrite E45; reflexivity).
      br_if.
      step. rewrite bv_eqb_lit by lia.
      replace (dropped (n_EXP_NM (g_in g)) q =? 0) with false by (rewrite D1'; reflexivity).
      br_if.
      step. brz.
      step. step. step. rewrite Tac_si.zxb_bz, Tac_si.lower_lw.
      step. step. step. rewrite Tac_si.lower_or_bv by lia.
      step. rewrite Tac_si.neg_eqb_same. br_if.
      step. step. step. step. brz.
      apply (fin_l g mem regs _ _ _ _ _ (normalize rsegs mem) (Frame.munch_refl _ _) (Frame.wmono_refl _ _) HSTK0);
        [rewrite E2; reflexivity | reflexivity | reflexivity |].
      intros R' m' HG HREL. split; [apply (HIR R' m' HREL); kr HG|].
      split; [lia|].
      split; [rg HG; rewrite DK; lia|]. split; [rg HG|]. split; [rewrite HG; greg2; rewrite DK; reflexivity|].
      split; [kr HG|]. split; [kr HG|]. split; [kr HG|]. rg HG.
    + assert (HnA : ~ (RcIdentModel.bz (RcIdentModel.nthb (n_EXP_NM (g_in g)) q) = 45 /\
        dropped (n_EXP_NM (g_in g)) q = 0)) by tauto.
      pose proof (Tac_si.tok_other_keep _ _ Lq HnA) as DK.
      destruct (Tac_si.tok_at _ _ Lq HnA) as [TI TV].
      pose proof (cstr_byte _ _ _ (Z.to_nat (Z.of_nat q - dropped (n_EXP_NM (g_in g)) q)) C2n
        ltac:(unfold n_TK; lia)) as RT.
      rewrite Z2Nat.id in RT by lia.
      change (n_TK (g_in g)) with (TOK (n_EXP_NM (g_in g))) in RT.
      rewrite Tac_si.nthb_snoc_lt in RT by exact TI. rewrite TV in RT.
      step. rewrite bv_eqb_lit by lia.
      replace (RcIdentModel.bz (RcIdentModel.nthb (n_EXP_NM (g_in g)) q) =? 45) with false
        by (symmetry; apply Z.eqb_neq; exact N45).
      br_if.
      step. brz.
      step. step. step. rewrite Tac_si.zxb_bz, Tac_si.lower_lw.
      step. step. step. rewrite Tac_si.lower_or_bv by lia.
      step. rewrite Tac_si.neg_eqb_same. br_if.
      step. step. step. step. brz.
      apply (fin_l g mem regs _ _ _ _ _ (normalize rsegs mem) (Frame.munch_refl _ _) (Frame.wmono_refl _ _) HSTK0);
        [rewrite E2; reflexivity | reflexivity | reflexivity |].
      intros R' m' HG HREL. split; [apply (HIR R' m' HREL); kr HG|].
      split; [lia|].
      split; [rg HG; rewrite DK; lia|]. split; [rg HG|]. split; [rewrite HG; greg2; rewrite DK; reflexivity|].
      split; [kr HG|]. split; [kr HG|]. split; [kr HG|]. rg HG.
Qed.

Lemma seg_I10 : Hcut B APIf ra (Inv_U13e54 B APIf ra empty) -> Hcut B APIf ra (Inv_U13e08 B APIf ra empty).
Proof.
  intros HE0.
  assert (IND : forall n g q c, (length (n_EXP_NM (g_in g)) - q < n)%nat ->
    Inv_U13e08_at B APIf ra empty g q c -> Rz (ms_segs B) c (Post B APIf ra g)).
  { induction n as [|n IH]; intros g q c Hn HC; [lia|].
    apply (step10 g q HE0); [|exact HC]. intros c' HC'.
    assert (Hq' : (S q <= length (n_EXP_NM (g_in g)))%nat)
      by (destruct HC' as (nm & tk & dp & L & A & regs & mem & md & _ & _ & _ & _ & Hq & _); exact Hq).
    apply (IH g (S q) c'); [lia | exact HC']. }
  intros g c (q & HC). exact (IND _ g q c (Nat.lt_succ_diag_r _) HC).
Qed.

End I10.
