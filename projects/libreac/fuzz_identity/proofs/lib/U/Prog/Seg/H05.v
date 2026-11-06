From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require RcIdentModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Tac_si.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require H05.
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uhj.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.

Module PH05 := OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg.H05.

Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Ltac bveq := apply bv_eq; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64;
  unfold spk, fsp, SLOT_FRAME in *; Z.div_mod_to_equations; lia.

Ltac ltu_off := lazymatch goal with |- context [bv_ltu ?a ?b] =>
  replace (bv_ltu a b) with false by (symmetry; unfold bv_ltu, notw; apply Z.ltb_ge; rewrite ?Z_to_bv_unsigned;
    unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64; unfold spk, fsp, SLOT_FRAME in *;
    Z.div_mod_to_equations; lia) end; br_if.

Ltac rg HG := rewrite HG; greg2; first [reflexivity | f_equal; unfold spk, fsp, SLOT_FRAME in *; lia | bveq].

Section H05.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.

Lemma H05_b08 : Hcut B APIf ra (Inv_U13b98 B APIf ra empty) -> Hcut B APIf ra (Inv_U13bf4 B APIf ra empty) ->
  Hcut B APIf ra (Inv_U13b08 B APIf ra empty).
Proof.
  intros H98 Hf4 g c (nm & tk & dp & HC).
  eapply (seg_go2 B APIf ra empty FF); [exact H98 | exact Hf4 | | | exact HC | ].
  { intros c' HC'. unfold Inv_U13b98. exists nm, tk, dp. exact HC'. }
  { intros c' HC'. unfold Inv_U13bf4. exists nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM HP.
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct HP as (HN1 & E8 & E12 & E10 & HB).
  pose proof HN1 as (HNB & E27 & HSTP & HQ216 & HW4).
  pose proof HNB as (HID & HW & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOU).
  pose proof (n_stem_len (g_in g)) as L16.
  destruct (nzb_W4 _ HW) as [NZW LW].
  pose proof E10 as E10'. unfold spk, fsp, SLOT_FRAME in E10'.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HB) as HBn. unfold spk, fsp, SLOT_FRAME in HBn.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HW4) as HW4n. unfold spk, fsp, SLOT_FRAME in HW4n.
  assert (KMm : forall m', mem_rel rsegs m' (normalize rsegs mem) -> KM [] mem m').
  { intros m' HREL. exact (KM_of [] mem (normalize rsegs mem) m' HRO (Frame.munch_refl _ _) HREL). }
  assert (HOk : forall m', mem_rel rsegs m' (normalize rsegs mem) -> OUTS g nm tk dp m').
  { intros m' HREL. exact (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md (normalize rsegs mem) m' HFR HPM
      (munch_SWIN g [] _ _ (Frame.munch_refl _ _) (Forall_nil _)) HREL HOU). }
  unfold rmk, Frame.mkR. rewrite E2, E12, E10'.
  step. step. step. step. step.
  rewrite not_lit by lia.
  lazymatch goal with |- context [bv_ltu ?s (Z_to_bv 64 4)] =>
    replace s with (Z_to_bv 64 (Z.of_nat (length (n_stem (g_in g))))) by (unfold zlen; bveq) end.
  rewrite bv_ltu_lit by lia.
  destruct (Z.ltb_spec (Z.of_nat (length (n_stem (g_in g)))) 4) as [HL|HL]; br_if.
  - apply (fin_l g mem regs _ _ _ _ _ (normalize rsegs mem) (Frame.munch_refl _ _) (Frame.wmono_refl _ _) HSTK0);
      [rewrite E2; reflexivity | reflexivity | reflexivity |].
    intros R' m' HG HREL. cbv beta.
    split; [|split; [|split; [|split]]].
    + apply (N1_keep g nm tk dp regs mem R' m' [] HN1 (KMm m' HREL) (HOk m' HREL)); try exact I; kr HG.
    + rg HG.
    + rg HG.
    + apply (fin_bytes m' (normalize rsegs mem) _ _ HREL). exact (bytes_at_normalize rsegs mem _ _ HRO HB).
    + unfold n_ends_w4. replace (4 <=? length (n_stem (g_in g)))%nat with false
        by (symmetry; apply Nat.leb_gt; lia). reflexivity.
  - pose proof (fun k (Hk : (k < length (n_stem (g_in g)))%nat) => rd1 _ _ _ (bytes_at_one _ _ _ k HBn Hk)) as RS.
    pose proof (RS (length (n_stem (g_in g)) - 4)%nat ltac:(lia)) as RS0.
    pose proof (RS (length (n_stem (g_in g)) - 3)%nat ltac:(lia)) as RS1.
    pose proof (RS (length (n_stem (g_in g)) - 2)%nat ltac:(lia)) as RS2.
    pose proof (RS (length (n_stem (g_in g)) - 1)%nat ltac:(lia)) as RS3.
    clear RS.
    pose proof (cstr_byte _ _ _ 0 HW4n ltac:(lia)) as RW0.
    pose proof (cstr_byte _ _ _ 1 HW4n ltac:(lia)) as RW1.
    pose proof (cstr_byte _ _ _ 2 HW4n ltac:(lia)) as RW2.
    pose proof (cstr_byte _ _ _ 3 HW4n ltac:(lia)) as RW3.
    rewrite Tac_si.nthb_snoc_lt in RW0, RW1, RW2, RW3 by lia.
    step. step. ltu_off.
    step. ltu_off.
    step. step. step. step. ltu_off.
    step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step.
    step. step. step.
    rewrite PH05.w4_eqb.
    assert (EW : n_ends_w4 (g_in g) = bytes_eqb
      [nth (length (n_stem (g_in g)) - 4) (n_stem (g_in g)) (Z_to_bv 8 0);
       nth (length (n_stem (g_in g)) - 3) (n_stem (g_in g)) (Z_to_bv 8 0);
       nth (length (n_stem (g_in g)) - 2) (n_stem (g_in g)) (Z_to_bv 8 0);
       nth (length (n_stem (g_in g)) - 1) (n_stem (g_in g)) (Z_to_bv 8 0)]
      [RcIdentModel.nthb (n_W4 (g_in g)) 0; RcIdentModel.nthb (n_W4 (g_in g)) 1;
       RcIdentModel.nthb (n_W4 (g_in g)) 2; RcIdentModel.nthb (n_W4 (g_in g)) 3]).
    { unfold n_ends_w4. replace (4 <=? length (n_stem (g_in g)))%nat with true
        by (symmetry; apply Nat.leb_le; lia).
      rewrite PH05.skipn4 by lia. rewrite PH05.firstn4 by exact LW. reflexivity. }
    rewrite <- EW.
    destruct (n_ends_w4 (g_in g)) eqn:EE; br_if.
    + apply (fin_r g mem regs _ _ _ _ _ (normalize rsegs mem) (Frame.munch_refl _ _) (Frame.wmono_refl _ _) HSTK0);
        [rewrite E2; reflexivity | reflexivity | reflexivity |].
      intros R' m' HG HREL. cbv beta.
      split; [|split; [|split]].
      * apply (N1_keep g nm tk dp regs mem R' m' [] HN1 (KMm m' HREL) (HOk m' HREL)); try exact I; kr HG.
      * rewrite HG. greg2. unfold n_ln, n_EXP_NM, zlen. rewrite EE. reflexivity.
      * rg HG.
      * unfold n_EXP_NM. rewrite EE. apply (fin_bytes m' (normalize rsegs mem) _ _ HREL).
        exact (bytes_at_normalize rsegs mem _ _ HRO HB).
    + step. step. rewrite bv_eqb_lit by lia.
      replace (Z.of_nat (length (n_stem (g_in g))) =? 32) with false by (symmetry; apply Z.eqb_neq; lia).
      br_if.
      apply (fin_l g mem regs _ _ _ _ _ (normalize rsegs mem) (Frame.munch_refl _ _) (Frame.wmono_refl _ _) HSTK0);
        [rewrite E2; reflexivity | reflexivity | reflexivity |].
      intros R' m' HG HREL. cbv beta.
      split; [|split; [|split; [|split]]].
      * apply (N1_keep g nm tk dp regs mem R' m' [] HN1 (KMm m' HREL) (HOk m' HREL)); try exact I; kr HG.
      * rg HG.
      * rg HG.
      * apply (fin_bytes m' (normalize rsegs mem) _ _ HREL). exact (bytes_at_normalize rsegs mem _ _ HRO HB).
      * reflexivity.
Qed.

Lemma H05_b10 : Hcut B APIf ra (Inv_U13b98 B APIf ra empty) -> Hcut B APIf ra (Inv_U13b10 B APIf ra empty).
Proof.
  intros H98 g c (nm & tk & dp & HC).
  eapply (seg_go B APIf ra empty FF); [exact H98 | | exact HC | ].
  { intros c' HC'. unfold Inv_U13b98. exists nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM HP.
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct HP as (HN1 & E8 & E10 & Z0).
  pose proof HN1 as (HNB & E27 & HSTP & HQ216 & HW4).
  pose proof HNB as (HID & HW & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOU).
  pose proof (Tac_si.nzb_stem (g_in g)) as NZS.
  assert (ES : n_stem (g_in g) = []).
  { destruct (n_stem (g_in g)) as [|b s] eqn:E; [reflexivity|]. exfalso.
    unfold Tac_si.nzb in NZS. cbn [forallb] in NZS. apply andb_prop in NZS as [NB _].
    unfold RcIdentModel.nthb in Z0. cbn in Z0. rewrite Z0 in NB. discriminate. }
  pose proof E10 as E10'. unfold spk, fsp, SLOT_FRAME in E10'.
  assert (KMm : forall m', mem_rel rsegs m' (normalize rsegs mem) -> KM [] mem m').
  { intros m' HREL. exact (KM_of [] mem (normalize rsegs mem) m' HRO (Frame.munch_refl _ _) HREL). }
  assert (HOk : forall m', mem_rel rsegs m' (normalize rsegs mem) -> OUTS g nm tk dp m').
  { intros m' HREL. exact (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md (normalize rsegs mem) m' HFR HPM
      (munch_SWIN g [] _ _ (Frame.munch_refl _ _) (Forall_nil _)) HREL HOU). }
  unfold rmk, Frame.mkR. rewrite E2, E10'.
  step. step. step. step.
  rewrite not_lit by lia.
  try (rewrite bv_ltu_lit by lia); try (replace (0 <? 4) with true by reflexivity); br_if.
  apply fin_nomem; [exact HSTK0 | rewrite E2; reflexivity | reflexivity | reflexivity |].
  intros R' m' HG HREL. cbv beta.
  split; [|split; [|split; [|split]]].
  - apply (N1_keep g nm tk dp regs mem R' m' [] HN1 (KMm m' HREL) (HOk m' HREL)); try exact I; kr HG.
  - rewrite HG. greg2. rewrite ES. reflexivity.
  - rg HG.
  - rewrite ES. apply bytes_at_nil. unfold spk, fsp, SLOT_FRAME. lia.
  - unfold n_ends_w4. rewrite ES. reflexivity.
Qed.

Lemma seg_H05 : Hcut B APIf ra (Inv_U13b98 B APIf ra empty) -> Hcut B APIf ra (Inv_U13bf4 B APIf ra empty) ->
  Hcut B APIf ra (Inv_U13b08 B APIf ra empty) /\ Hcut B APIf ra (Inv_U13b10 B APIf ra empty).
Proof. intros H98 Hf4. split; [exact (H05_b08 H98 Hf4) | exact (H05_b10 H98)]. Qed.

End H05.
