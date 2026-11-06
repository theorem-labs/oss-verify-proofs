From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Exec Step Tac.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI KindBGlue MemNorm.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sh2.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Tac_si.
Import ListNotations.
Open Scope Z_scope.

Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Section I10.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Ltac ir_close HIR HG HREL R' m' :=
  apply (HIR R' m' HREL); rewrite HG;
  first [reflexivity | match goal with H : YK11.getr _ 21 = _ |- _ => rewrite H; reflexivity end].

Lemma step10 : forall g q,
  Hcut B APIf ra (Inv_K13be0 B APIf ra empty) ->
  (forall c, Inv_K13b9c_at B APIf ra empty g (S q) c -> Rz (ms_segs B) c (Post B APIf ra g)) ->
  forall c, Inv_K13b9c_at B APIf ra empty g q c -> Rz (ms_segs B) c (Post B APIf ra g).
Proof.
  intros g q HE0 HN c (nm & tk & dp & HC).
  eapply (seg_go2 B APIf ra empty FF (fun g' c => g' = g /\ Inv_K13b9c_at B APIf ra empty g (S q) c)
    (Inv_K13be0 B APIf ra empty)).
  { intros g' c' (-> & H). exact (HN c' H). }
  { exact HE0. }
  { intros c' HC'. split; [reflexivity|]. exists nm, tk, dp. exact HC'. }
  { intros c' HC'. exists nm, tk, dp. exact HC'. }
  { exact HC. }
  intros L A regs mem md HFR HPM HP.
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct HP as ((HI & R0) & Hq & E13 & E14 & E11 & E12 & E10).
  pose proof HI as (HID & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R27 & HO & HE).
  destruct (HO R0) as (C1 & C2 & C3).
  destruct (Tac_si.n_r0 _ R0) as [Wk _].
  pose proof (n_ln_le (g_in g) Wk) as LN. unfold n_ln in LN.
  pose proof (Tac_si.nzb_EXP_NM _ Wk) as NZE.
  pose proof (Tac_si.dropped_range (n_EXP_NM (g_in g)) q) as DR.
  pose proof (Tac_si.dropped_le (n_EXP_NM (g_in g)) q) as DL.
  pose proof (bz_range (RcIdentModel.nthb (n_EXP_NM (g_in g)) q)) as BR.
  destruct (Tac_si.nmb_in _ _ _ _ _ _ HPM) as (N1 & N2 & N3).
  destruct (Tac_si.FR_parts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (_ & _ & _ & _ & HMR & _).
  pose proof (Tac_si.blk_range B APIf _ _ _ _ _ _ HMR N1) as [BN1 BN2].
  pose proof (Tac_si.blk_range B APIf _ _ _ _ _ _ HMR N2) as [BT1 BT2].
  pose proof YM05.alloc_ceiling_value as [AC1 AC2].
  pose proof (bytes_at_normalize rsegs mem _ _ HRO C1) as C1n.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO C2) as C2n.
  pose proof (Tac_si.cstr_byte _ _ _ (S q) C1n ltac:(lia)) as RN.
  assert (KMm : forall m', mem_rel rsegs m' (normalize rsegs mem) -> KM [] mem m').
  { intros m' HREL. exact (KM_of [] mem (normalize rsegs mem) m' HRO (Frame.munch_refl _ _) HREL). }
  assert (HOk : forall m', mem_rel rsegs m' (normalize rsegs mem) -> OUTS g nm tk dp m').
  { intros m' HREL. exact (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md (normalize rsegs mem) m' HFR HPM
      (munch_SWIN g [] _ _ (Frame.munch_refl _ _) (Forall_nil _)) HREL HO). }
  assert (HIR : forall R' m', mem_rel rsegs m' (normalize rsegs mem) ->
    YK11.getr R' 9 = YK11.getr regs 9 -> YK11.getr R' 18 = YK11.getr regs 18 ->
    YK11.getr R' 19 = YK11.getr regs 19 -> YK11.getr R' 20 = YK11.getr regs 20 ->
    YK11.getr R' 21 = YK11.getr regs 21 -> YK11.getr R' 22 = YK11.getr regs 22 ->
    YK11.getr R' 23 = YK11.getr regs 23 -> YK11.getr R' 24 = YK11.getr regs 24 ->
    YK11.getr R' 25 = YK11.getr regs 25 -> YK11.getr R' 27 = YK11.getr regs 27 -> IR g nm tk dp R' m').
  { intros R' m' HREL F9 F18 F19 F20 F21 F22 F23 F24 F25 F27. split; [|exact R0].
    exact (IRb_keep g nm tk dp regs mem R' m' [] HI (KMm m' HREL) (HOk m' HREL) I I I
      F9 F18 F19 F20 F21 F22 F23 F24 F25 F27). }
  assert (TL : Z.of_nat (length (n_TK (g_in g))) =
    Z.of_nat (length (n_EXP_NM (g_in g))) - dropped (n_EXP_NM (g_in g)) (length (n_EXP_NM (g_in g)))).
  { unfold n_TK. apply Tac_si.tok_len_full. }
  assert (RNX : forall (EQ : S q = length (n_EXP_NM (g_in g))),
    ov_read_bytes rsegs (normalize rsegs mem) (wa (nm + Z.of_nat (S q))) 1 = Some [z8]).
  { intros EQ. rewrite RN. f_equal. f_equal. rewrite EQ. apply Tac_si.nthb_snoc_eq. }
  unfold rmk, Frame.mkR. rewrite E2, E13, E14, E11, E12, E10, R21.
  destruct (Z.eq_dec (RcIdentModel.bz (RcIdentModel.nthb (n_EXP_NM (g_in g)) q)) 45) as [E45|N45];
    [destruct (Z.eq_dec (dropped (n_EXP_NM (g_in g)) q) 0) as [D0|D1]|].
  - pose proof (Tac_si.tok_dash_drop _ _ Hq E45 D0) as DS.
    step. rewrite bv_eqb_lit by lia.
    replace (RcIdentModel.bz (RcIdentModel.nthb (n_EXP_NM (g_in g)) q) =? 45) with true
      by (rewrite E45; reflexivity).
    br_if.
    step. rewrite bv_eqb_lit by lia.
    replace (dropped (n_EXP_NM (g_in g)) q =? 0) with true by (rewrite D0; reflexivity).
    br_if.
    step. step.
    destruct (Nat.eq_dec (S q) (length (n_EXP_NM (g_in g)))) as [EQ|LT].
    + pose proof (RNX EQ) as RZ. clear RN.
      step. change (zxb z8) with (Z_to_bv 64 0).
      step. step. br_if.
      apply (fin_r g mem regs _ _ _ _ _ (normalize rsegs mem) (Frame.munch_refl _ _) (Frame.wmono_refl _ _) HSTK0);
        [rewrite E2; reflexivity | reflexivity | reflexivity |].
      intros R' m' HG HREL. split; [ir_close HIR HG HREL R' m'|].
      rewrite HG. greg2. f_equal. unfold zlen. rewrite TL, <- EQ, DS. rewrite D0. lia.
    + assert (Lq : (S q < length (n_EXP_NM (g_in g)))%nat) by lia.
      rewrite Tac_si.nthb_snoc_lt in RN by exact Lq.
      pose proof (Tac_si.nzb_nth _ _ NZE Lq) as NZ.
      pose proof (bz_range (RcIdentModel.nthb (n_EXP_NM (g_in g)) (S q))) as BR1.
      step. rewrite Tac_si.zxb_bz.
      step. step. rewrite bv_eqb_lit by lia.
      replace (RcIdentModel.bz (RcIdentModel.nthb (n_EXP_NM (g_in g)) (S q)) =? 0) with false
        by (symmetry; apply Z.eqb_neq; exact NZ).
      br_if. step.
      apply (fin_l g mem regs _ _ _ _ _ (normalize rsegs mem) (Frame.munch_refl _ _) (Frame.wmono_refl _ _) HSTK0);
        [rewrite E2; reflexivity | reflexivity | reflexivity |].
      intros R' m' HG HREL. split; [ir_close HIR HG HREL R' m'|].
      split; [exact Lq|].
      split; [rewrite HG; reflexivity|]. split; [rewrite HG; greg2; reflexivity|].
      split; [rewrite HG; greg2; f_equal; lia|]. split; [rewrite HG; greg2; rewrite DS; reflexivity|].
      rewrite HG. greg2. f_equal. rewrite DS, D0. lia.
  - assert (D1' : dropped (n_EXP_NM (g_in g)) q = 1) by lia.
    assert (HnA : ~ (RcIdentModel.bz (RcIdentModel.nthb (n_EXP_NM (g_in g)) q) = 45 /\
      dropped (n_EXP_NM (g_in g)) q = 0)) by lia.
    pose proof (Tac_si.tok_other_keep _ _ Hq HnA) as DK.
    destruct (Tac_si.tok_at _ _ Hq HnA) as [TI TV].
    pose proof (Tac_si.cstr_byte _ _ _ (Z.to_nat (Z.of_nat q - dropped (n_EXP_NM (g_in g)) q)) C2n
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
    step. step. step. rewrite Tac_si.zxb_bz, Tac_si.lower_lw.
    step. step. step. rewrite Tac_si.lower_or_bv by lia.
    step. rewrite Tac_si.neg_eqb_same. br_if.
    step.
    destruct (Nat.eq_dec (S q) (length (n_EXP_NM (g_in g)))) as [EQ|LT].
    + pose proof (RNX EQ) as RZ. clear RN.
      step. change (zxb z8) with (Z_to_bv 64 0).
      step. step. br_if.
      apply (fin_r g mem regs _ _ _ _ _ (normalize rsegs mem) (Frame.munch_refl _ _) (Frame.wmono_refl _ _) HSTK0);
        [rewrite E2; reflexivity | reflexivity | reflexivity |].
      intros R' m' HG HREL. split; [ir_close HIR HG HREL R' m'|].
      rewrite HG. greg2. f_equal. unfold zlen. rewrite TL, <- EQ, DK. lia.
    + assert (Lq : (S q < length (n_EXP_NM (g_in g)))%nat) by lia.
      rewrite Tac_si.nthb_snoc_lt in RN by exact Lq.
      pose proof (Tac_si.nzb_nth _ _ NZE Lq) as NZ.
      pose proof (bz_range (RcIdentModel.nthb (n_EXP_NM (g_in g)) (S q))) as BR1.
      step. rewrite Tac_si.zxb_bz.
      step. step. rewrite bv_eqb_lit by lia.
      replace (RcIdentModel.bz (RcIdentModel.nthb (n_EXP_NM (g_in g)) (S q)) =? 0) with false
        by (symmetry; apply Z.eqb_neq; exact NZ).
      br_if. step.
      apply (fin_l g mem regs _ _ _ _ _ (normalize rsegs mem) (Frame.munch_refl _ _) (Frame.wmono_refl _ _) HSTK0);
        [rewrite E2; reflexivity | reflexivity | reflexivity |].
      intros R' m' HG HREL. split; [ir_close HIR HG HREL R' m'|].
      split; [exact Lq|].
      split; [rewrite HG; reflexivity|]. split; [rewrite HG; greg2; reflexivity|].
      split; [rewrite HG; greg2; f_equal; lia|]. split; [rewrite HG; greg2; rewrite DK; reflexivity|].
      rewrite HG. greg2. f_equal. rewrite DK. lia.
  - assert (HnA : ~ (RcIdentModel.bz (RcIdentModel.nthb (n_EXP_NM (g_in g)) q) = 45 /\
      dropped (n_EXP_NM (g_in g)) q = 0)) by tauto.
    pose proof (Tac_si.tok_other_keep _ _ Hq HnA) as DK.
    destruct (Tac_si.tok_at _ _ Hq HnA) as [TI TV].
    pose proof (Tac_si.cstr_byte _ _ _ (Z.to_nat (Z.of_nat q - dropped (n_EXP_NM (g_in g)) q)) C2n
      ltac:(unfold n_TK; lia)) as RT.
    rewrite Z2Nat.id in RT by lia.
    change (n_TK (g_in g)) with (TOK (n_EXP_NM (g_in g))) in RT.
    rewrite Tac_si.nthb_snoc_lt in RT by exact TI. rewrite TV in RT.
    step. rewrite bv_eqb_lit by lia.
    replace (RcIdentModel.bz (RcIdentModel.nthb (n_EXP_NM (g_in g)) q) =? 45) with false
      by (symmetry; apply Z.eqb_neq; exact N45).
    br_if.
    step. step. step. rewrite Tac_si.zxb_bz, Tac_si.lower_lw.
    step. step. step. rewrite Tac_si.lower_or_bv by lia.
    step. rewrite Tac_si.neg_eqb_same. br_if.
    step.
    destruct (Nat.eq_dec (S q) (length (n_EXP_NM (g_in g)))) as [EQ|LT].
    + pose proof (RNX EQ) as RZ. clear RN.
      step. change (zxb z8) with (Z_to_bv 64 0).
      step. step. br_if.
      apply (fin_r g mem regs _ _ _ _ _ (normalize rsegs mem) (Frame.munch_refl _ _) (Frame.wmono_refl _ _) HSTK0);
        [rewrite E2; reflexivity | reflexivity | reflexivity |].
      intros R' m' HG HREL. split; [ir_close HIR HG HREL R' m'|].
      rewrite HG. greg2. f_equal. unfold zlen. rewrite TL, <- EQ, DK. lia.
    + assert (Lq : (S q < length (n_EXP_NM (g_in g)))%nat) by lia.
      rewrite Tac_si.nthb_snoc_lt in RN by exact Lq.
      pose proof (Tac_si.nzb_nth _ _ NZE Lq) as NZ.
      pose proof (bz_range (RcIdentModel.nthb (n_EXP_NM (g_in g)) (S q))) as BR1.
      step. rewrite Tac_si.zxb_bz.
      step. step. rewrite bv_eqb_lit by lia.
      replace (RcIdentModel.bz (RcIdentModel.nthb (n_EXP_NM (g_in g)) (S q)) =? 0) with false
        by (symmetry; apply Z.eqb_neq; exact NZ).
      br_if. step.
      apply (fin_l g mem regs _ _ _ _ _ (normalize rsegs mem) (Frame.munch_refl _ _) (Frame.wmono_refl _ _) HSTK0);
        [rewrite E2; reflexivity | reflexivity | reflexivity |].
      intros R' m' HG HREL. split; [ir_close HIR HG HREL R' m'|].
      split; [exact Lq|].
      split; [rewrite HG; reflexivity|]. split; [rewrite HG; greg2; reflexivity|].
      split; [rewrite HG; greg2; f_equal; lia|]. split; [rewrite HG; greg2; rewrite DK; reflexivity|].
      rewrite HG. greg2. f_equal. rewrite DK. lia.
Qed.

Lemma seg_I10 : Hcut B APIf ra (Inv_K13be0 B APIf ra empty) -> Hcut B APIf ra (Inv_K13b9c B APIf ra empty).
Proof.
  intros HE0.
  assert (IND : forall n g q c, (length (n_EXP_NM (g_in g)) - q <= n)%nat ->
    Inv_K13b9c_at B APIf ra empty g q c -> Rz (ms_segs B) c (Post B APIf ra g)).
  { induction n as [|n IH]; intros g q c Hn HC.
    - exfalso. destruct HC as (nm & tk & dp & L & A & regs & mem & md & _ & _ & _ & _ & Hq & _). lia.
    - apply (step10 g q HE0); [|exact HC]. intros c' HC'. apply (IH g (S q) c'); [lia | exact HC']. }
  intros g c (q & HC). exact (IND _ g q c (le_n _) HC).
Qed.

End I10.
