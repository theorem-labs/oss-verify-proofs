(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.IConj.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import
  ZIface InflateState Inftrees InftreesCoverage ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I8U Require Import Base.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK Require Import ZTac ZArr ZArr4 IDefs ISpecs ITac.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S Require Import S_It0.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I8U Require Import T_It1.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.

Section U8IT2.
Context {RCa1 : RunCtx}.
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 208 zc.

#[local] Abbreviation PR := (pregs p lens_ofs codes pb sp vgp vtp (cty ty)).
#[local] Abbreviation cA := (arr_get (cntA lf lens_ofs codes)).
#[local] Abbreviation cntAr := (cntA lf lens_ofs codes).
#[local] Abbreviation mx := (mxA lf lens_ofs codes).
#[local] Abbreviation mn := (mnA lf lens_ofs codes).
#[local] Abbreviation rt := (rootA lf lens_ofs codes bits).
#[local] Abbreviation L k := (LZ (cntA lf lens_ofs codes) k).
#[local] Abbreviation KLEFT := (Kleft ty lf lens_ofs codes bits p pb sp vgp vtp).
#[local] Abbreviation offsAr := (offsA lf lens_ofs codes).
#[local] Abbreviation work1Ar := (work1A lf lens_ofs codes wf).
#[local] Abbreviation SKo i := (fst (itm_sort_k (lensA lf) lens_ofs i (offsA lf lens_ofs codes) (workA wf))).
#[local] Abbreviation SKw i := (snd (itm_sort_k (lensA lf) lens_ofs i (offsA lf lens_ofs codes) (workA wf))).

Lemma cty_codes : (cty ty =? 0) = codetype_eqb ty CODES.
Proof. destruct ty; reflexivity. Qed.

Definition Kneg (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', PR R' [] -> zget_l R' [] kA6 = -1 ->
    itm_reject ty mx (it_left_check cntAr) = true -> 1 <= mx ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 101316 (zupd R' []) M MD) T.

Definition Koffs (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', PR R' [] -> zget_l R' [] kT0 = mx -> zget_l R' [] kT1 = mn -> zget_l R' [] kA7 = rt ->
    zget_l R' [] kT3 = cA 1 -> zget_l R' [] kT5 = cA 2 -> zget_l R' [] kT6 = cA 3 -> zget_l R' [] kS0 = cA 4 ->
    zget_l R' [] kS1 = cA 5 -> zget_l R' [] kS2 = cA 6 -> zget_l R' [] kS3 = cA 7 -> zget_l R' [] kS4 = cA 8 ->
    zget_l R' [] kS5 = cA 9 -> zget_l R' [] kS6 = cA 10 -> zget_l R' [] kS7 = cA 11 -> zget_l R' [] kS8 = cA 12 ->
    zget_l R' [] kS9 = cA 13 -> zget_l R' [] kS10 = cA 14 ->
    1 <= mx -> itm_reject ty mx (it_left_check cntAr) = false ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 99904 (zupd R' []) M MD) T.


Definition pregs6_t (R : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l R l kSP = sp + -208 /\ zget_l R l kGP = vgp /\ zget_l R l kTP = vtp /\ zget_l R l kA0 = cty ty /\
  zget_l R l kA1 = p + 168 + 2 * lens_ofs /\
  zget_l R l kA3 = p + 160 /\ zget_l R l kA4 = pb /\ zget_l R l kA5 = p + 808.
Ltac open_pregs6_t H := unfold pregs6_t in H;
  let a := fresh "LSP" in let b := fresh "LGP" in let c := fresh "LTP" in let d := fresh "LA0" in
  let e := fresh "LA1" in let g := fresh "LA3" in let h := fresh "LA4" in
  let i := fresh "LA5" in dand H as (a & b & c & d & e & g & h & i).
Ltac close_pregs6_t := unfold pregs6_t; split_conj; zreg.
Lemma left_t : forall M MD T,
  m_halted MD = None -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -136) 16 cA -> Kneg M MD T -> Koffs M MD T -> KLEFT M MD T.
Proof.
  intros M MD T Hh Hcnt KN KO. unfold Kleft. intros Rb HP LT0 LT1 LA7 LT3 LT4 LT2 Hmx.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range _ _ _ _ _ _ _ _ _ _ _ _ _ C j); lia).
  assert (HRa : forall j, 0 <= cA j <= codes) by (intros j; apply (cA_range _ _ _ _ _ _ _ _ _ _ _ _ _ C j)).
  assert (LB : forall j, 0 <= j <= 15 -> -18874368 <= L j <= 32768).
  { intros j Hj. pose proof (LZ_bound cntAr j codes ltac:(lia) HRa Hj). lia. }
  assert (PP0 : forall j, 1 <= j <= 0 -> 0 <= L j) by (intros; lia).
  pose proof (HRa 1) as HR1. pose proof (HRa 15) as HR15.
  zrebase.
  zstep Rfd. zstep Rfd.
  destruct (Z.ltb_spec 2 (cA 1)) as [F1|P1].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite (left_check_none cntAr 1); [reflexivity | lia | intros; lia | rewrite LZ_1; lia]. }
  zbr Rfd false.
  assert (PP1 : forall j, 1 <= j <= 1 -> 0 <= L j) by (intros j Hj; replace j with 1 by lia; rewrite LZ_1; lia). clear PP0.
  pose proof (LB 1 ltac:(lia)) as LB1. pose proof (LB 2 ltac:(lia)) as LB2. pose proof (HRa 2) as HR2.
  zstep Rfd. zsetreg (L 1) ltac:(rewrite LZ_1; lia).
  zstep Rfd. zsetreg 0 ltac:(rewrite LZ_1; symmetry; rewrite srliw_small by lia; apply Z.div_small; change (2 ^ 30) with 1073741824; lia).
  zbr Rfd false.
  tstep Rfd.
  zstep Rfd. zsetreg (2 * L 1) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd. zsetreg (L 2) ltac:(rewrite (LZ_S' cntAr 2) by lia; reflexivity).
  destruct (Z.ltb_spec (L 2) 0) as [F2|P2].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite (left_check_none cntAr 2); [reflexivity | lia | intros; apply PP1; lia | exact F2]. }
  zbr Rfd false.
  assert (PP2 : forall j, 1 <= j <= 2 -> 0 <= L j) by (intros j Hj; destruct (Z.eq_dec j 2) as [->|]; [exact P2 | apply PP1; lia]). clear PP1 P1.

  pose proof (LB 3 ltac:(lia)) as LB3. pose proof (HRa 3) as HR3. clear LB1.
  tstep Rfd.
  zstep Rfd. zsetreg (2 * L 2) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd. zsetreg (L 3) ltac:(rewrite (LZ_S' cntAr 3) by lia; reflexivity).
  destruct (Z.ltb_spec (L 3) 0) as [F3|P3].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite (left_check_none cntAr 3); [reflexivity | lia | intros; apply PP2; lia | exact F3]. }
  zbr Rfd false.
  assert (PP3 : forall j, 1 <= j <= 3 -> 0 <= L j) by (intros j Hj; destruct (Z.eq_dec j 3) as [->|]; [exact P3 | apply PP2; lia]). clear PP2 P2.
  pose proof (LB 4 ltac:(lia)) as LB4. pose proof (HRa 4) as HR4. clear LB2.
  tstep Rfd.
  zstep Rfd. zsetreg (2 * L 3) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd. zsetreg (L 4) ltac:(rewrite (LZ_S' cntAr 4) by lia; reflexivity).
  destruct (Z.ltb_spec (L 4) 0) as [F4|P4].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite (left_check_none cntAr 4); [reflexivity | lia | intros; apply PP3; lia | exact F4]. }
  zbr Rfd false.
  assert (PP4 : forall j, 1 <= j <= 4 -> 0 <= L j) by (intros j Hj; destruct (Z.eq_dec j 4) as [->|]; [exact P4 | apply PP3; lia]). clear PP3 P3.
  pose proof (LB 5 ltac:(lia)) as LB5. pose proof (HRa 5) as HR5. clear LB3.
  tstep Rfd.
  zstep Rfd. zsetreg (2 * L 4) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd. zsetreg (L 5) ltac:(rewrite (LZ_S' cntAr 5) by lia; reflexivity).
  destruct (Z.ltb_spec (L 5) 0) as [F5|P5].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite (left_check_none cntAr 5); [reflexivity | lia | intros; apply PP4; lia | exact F5]. }
  zbr Rfd false.
  assert (PP5 : forall j, 1 <= j <= 5 -> 0 <= L j) by (intros j Hj; destruct (Z.eq_dec j 5) as [->|]; [exact P5 | apply PP4; lia]). clear PP4 P4.
  pose proof (LB 6 ltac:(lia)) as LB6. pose proof (HRa 6) as HR6. clear LB4.
  tstep Rfd.
  zstep Rfd. zsetreg (2 * L 5) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd. zsetreg (L 6) ltac:(rewrite (LZ_S' cntAr 6) by lia; reflexivity).
  destruct (Z.ltb_spec (L 6) 0) as [F6|P6].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite (left_check_none cntAr 6); [reflexivity | lia | intros; apply PP5; lia | exact F6]. }
  zbr Rfd false.
  assert (PP6 : forall j, 1 <= j <= 6 -> 0 <= L j) by (intros j Hj; destruct (Z.eq_dec j 6) as [->|]; [exact P6 | apply PP5; lia]). clear PP5 P5.
  pose proof (LB 7 ltac:(lia)) as LB7. pose proof (HRa 7) as HR7. clear LB5.
  tstep Rfd.
  zstep Rfd. zsetreg (2 * L 6) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd. zsetreg (L 7) ltac:(rewrite (LZ_S' cntAr 7) by lia; reflexivity).
  destruct (Z.ltb_spec (L 7) 0) as [F7|P7].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite (left_check_none cntAr 7); [reflexivity | lia | intros; apply PP6; lia | exact F7]. }
  zbr Rfd false.
  assert (PP7 : forall j, 1 <= j <= 7 -> 0 <= L j) by (intros j Hj; destruct (Z.eq_dec j 7) as [->|]; [exact P7 | apply PP6; lia]). clear PP6 P6.
  pose proof (LB 8 ltac:(lia)) as LB8. pose proof (HRa 8) as HR8. clear LB6.
  tstep Rfd.
  zstep Rfd. zsetreg (2 * L 7) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd. zsetreg (L 8) ltac:(rewrite (LZ_S' cntAr 8) by lia; reflexivity).
  destruct (Z.ltb_spec (L 8) 0) as [F8|P8].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite (left_check_none cntAr 8); [reflexivity | lia | intros; apply PP7; lia | exact F8]. }
  zbr Rfd false.
  assert (PP8 : forall j, 1 <= j <= 8 -> 0 <= L j) by (intros j Hj; destruct (Z.eq_dec j 8) as [->|]; [exact P8 | apply PP7; lia]). clear PP7 P7.
  pose proof (LB 9 ltac:(lia)) as LB9. pose proof (HRa 9) as HR9. clear LB7.
  tstep Rfd.
  zstep Rfd. zsetreg (2 * L 8) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd. zsetreg (L 9) ltac:(rewrite (LZ_S' cntAr 9) by lia; change (9 - 1) with 8; symmetry; apply swrap32_small; lia).
  destruct (Z.ltb_spec (L 9) 0) as [F9|P9].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite (left_check_none cntAr 9); [reflexivity | lia | intros; apply PP8; lia | exact F9]. }
  zbr Rfd false.
  assert (PP9 : forall j, 1 <= j <= 9 -> 0 <= L j) by (intros j Hj; destruct (Z.eq_dec j 9) as [->|]; [exact P9 | apply PP8; lia]). clear PP8 P8.
  pose proof (LB 10 ltac:(lia)) as LB10. pose proof (HRa 10) as HR10. clear LB8.
  tstep Rfd.
  zstep Rfd. zsetreg (2 * L 9) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd. zsetreg (L 10) ltac:(rewrite (LZ_S' cntAr 10) by lia; change (10 - 1) with 9; symmetry; apply swrap32_small; lia).
  destruct (Z.ltb_spec (L 10) 0) as [F10|P10].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite (left_check_none cntAr 10); [reflexivity | lia | intros; apply PP9; lia | exact F10]. }
  zbr Rfd false.
  assert (PP10 : forall j, 1 <= j <= 10 -> 0 <= L j) by (intros j Hj; destruct (Z.eq_dec j 10) as [->|]; [exact P10 | apply PP9; lia]). clear PP9 P9.
  pose proof (LB 11 ltac:(lia)) as LB11. pose proof (HRa 11) as HR11. clear LB9.
  tstep Rfd.
  zstep Rfd. zsetreg (2 * L 10) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd. zsetreg (L 11) ltac:(rewrite (LZ_S' cntAr 11) by lia; change (11 - 1) with 10; symmetry; apply swrap32_small; lia).
  destruct (Z.ltb_spec (L 11) 0) as [F11|P11].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite (left_check_none cntAr 11); [reflexivity | lia | intros; apply PP10; lia | exact F11]. }
  zbr Rfd false.
  assert (PP11 : forall j, 1 <= j <= 11 -> 0 <= L j) by (intros j Hj; destruct (Z.eq_dec j 11) as [->|]; [exact P11 | apply PP10; lia]). clear PP10 P10.
  pose proof (LB 12 ltac:(lia)) as LB12. pose proof (HRa 12) as HR12. clear LB10.
  tstep Rfd.
  zstep Rfd. zsetreg (2 * L 11) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd. zsetreg (L 12) ltac:(rewrite (LZ_S' cntAr 12) by lia; change (12 - 1) with 11; symmetry; apply swrap32_small; lia).
  destruct (Z.ltb_spec (L 12) 0) as [F12|P12].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite (left_check_none cntAr 12); [reflexivity | lia | intros; apply PP11; lia | exact F12]. }
  zbr Rfd false.
  assert (PP12 : forall j, 1 <= j <= 12 -> 0 <= L j) by (intros j Hj; destruct (Z.eq_dec j 12) as [->|]; [exact P12 | apply PP11; lia]). clear PP11 P11.
  pose proof (LB 13 ltac:(lia)) as LB13. pose proof (HRa 13) as HR13. clear LB11.
  tstep Rfd.
  zstep Rfd. zsetreg (2 * L 12) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd. zsetreg (L 13) ltac:(rewrite (LZ_S' cntAr 13) by lia; change (13 - 1) with 12; symmetry; apply swrap32_small; lia).
  destruct (Z.ltb_spec (L 13) 0) as [F13|P13].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite (left_check_none cntAr 13); [reflexivity | lia | intros; apply PP12; lia | exact F13]. }
  zbr Rfd false.
  assert (PP13 : forall j, 1 <= j <= 13 -> 0 <= L j) by (intros j Hj; destruct (Z.eq_dec j 13) as [->|]; [exact P13 | apply PP12; lia]). clear PP12 P12.
  pose proof (LB 14 ltac:(lia)) as LB14. pose proof (HRa 14) as HR14. clear LB12.
  tstep Rfd.
  zstep Rfd. zsetreg (2 * L 13) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd. zsetreg (L 14) ltac:(rewrite (LZ_S' cntAr 14) by lia; change (14 - 1) with 13; symmetry; apply swrap32_small; lia).
  destruct (Z.ltb_spec (L 14) 0) as [F14|P14].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite (left_check_none cntAr 14); [reflexivity | lia | intros; apply PP13; lia | exact F14]. }
  zbr Rfd false.
  assert (PP14 : forall j, 1 <= j <= 14 -> 0 <= L j) by (intros j Hj; destruct (Z.eq_dec j 14) as [->|]; [exact P14 | apply PP13; lia]). clear PP13 P13.
  pose proof (LB 15 ltac:(lia)) as LB15. clear LB13.
  zstep Rfd. zsetreg (2 * L 14) ltac:(rewrite swrap32_small by (rewrite Z.shiftl_mul_pow2 by lia; lia); rewrite Z.shiftl_mul_pow2 by lia; lia).
  assert (E15 : L 15 = 2 * L 14 - cA 15) by (rewrite (LZ_S' cntAr 15) by lia; change (15 - 1) with 14; reflexivity).
  destruct (Z.ltb_spec (2 * L 14) (cA 15)) as [F15|P15].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite (left_check_none cntAr 15); [reflexivity | lia | intros; apply PP14; lia | lia]. }
  zbr Rfd false.
  assert (PP15 : forall j, 1 <= j <= 15 -> 0 <= L j) by (intros j Hj; destruct (Z.eq_dec j 15) as [->|]; [lia | apply PP14; lia]). clear PP14 P14.
  assert (HLC : it_left_check cntAr = Some (L 15)) by (apply left_check_some; exact PP15).
  destruct (Z.eq_dec (2 * L 14) (cA 15)) as [Z15|NZ15].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KO Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite HLC. replace (0 <? L 15) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  zbr Rfd false.
  assert (L15P : 0 < L 15) by lia.
  assert (CTR : 0 <= cty ty <= 2) by (clear; destruct ty; cbn; lia_std).
  zstep Rfd. zsetreg (Z.b2z (cty ty =? 0)) ltac:(rewrite (Z.mod_small (cty ty)) by lia_std; destruct (Z.eqb_spec (cty ty) 0); destruct (Z.ltb_spec (cty ty) 1); cbn [Z.b2z]; lia_std).
  zstep Rfd. zsetreg (Z.b2z ((cty ty =? 0) || negb (mx =? 1))) ltac:(destruct (cty ty =? 0); destruct (mx =? 1); reflexivity).
  destruct ((cty ty =? 0) || negb (mx =? 1)) eqn:RJ.
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite HLC, <- cty_codes, RJ. replace (0 <? L 15) with true by (symmetry; apply Z.ltb_lt; lia_std). reflexivity.
  - zbr Rfd false.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KO Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite HLC, <- cty_codes, RJ. apply Bool.andb_false_r.
Qed.

Lemma offs_t : forall M MD T,
  m_halted MD = None -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (sp - 208) 208 ->
  (forall R' M', PR R' [] -> zget_l R' [] kT0 = mx -> zget_l R' [] kT1 = mn -> zget_l R' [] kA7 = rt -> zget_l R' [] kT2 = sp + -168 ->
     mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' (sp + -166) (sp + -136) 0 0 ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp + -166) 15 (fun j => arr_get offsAr (j + 1)) ->
     1 <= mx -> itm_reject ty mx (it_left_check cntAr) = false ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 100028 (zupd R' []) M' MD) T) ->
  Koffs M MD T.
Proof.
  intros M MD T Hh Wf K. unfold Koffs.
  intros Rb HP LT0 LT1 LA7 LT3 LT5 LT6 LS0 LS1 LS2 LS3 LS4 LS5 LS6 LS7 LS8 LS9 LS10 Hmx HRJ.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HRa : forall j, 0 <= cA j <= 288) by (intros j; pose proof (cA_range _ _ _ _ _ _ _ _ _ _ _ _ _ C j); lia).
  pose proof (mpost_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -166) (sp + -136) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost (run_segments R_segs rc_inp rc_sp rc_mb) M X (sp + -166) (sp + -136) 0 0) M) by (apply mpost_refl).
  zrebase.
  zstep Rfd.
  zstep Rfd.
  zbr Rfd false.
  zstep Rfd. zsetreg (OZ cntAr 3) ltac:(rewrite (OZ_S' cntAr 3) by lia; change (3 - 1) with 2; rewrite (OZ_S' cntAr 2) by lia; change (2 - 1) with 1; rewrite OZ_1; lia).
  zstep Rfd. zsetreg (OZ cntAr 4) ltac:(rewrite (OZ_S' cntAr 4) by lia; change (4 - 1) with 3; lia).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zsetreg (OZ cntAr 5) ltac:(rewrite (OZ_S' cntAr 5) by lia; change (5 - 1) with 4; lia).
  zstep Rfd. zsetreg (OZ cntAr 6) ltac:(rewrite (OZ_S' cntAr 6) by lia; change (6 - 1) with 5; lia).
  zstep Rfd. zsetreg (OZ cntAr 7) ltac:(rewrite (OZ_S' cntAr 7) by lia; change (7 - 1) with 6; lia).
  zstep Rfd. zsetreg (OZ cntAr 8) ltac:(rewrite (OZ_S' cntAr 8) by lia; change (8 - 1) with 7; lia).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zsetreg (OZ cntAr 9) ltac:(rewrite (OZ_S' cntAr 9) by lia; change (9 - 1) with 8; lia).
  zstep Rfd. zsetreg (OZ cntAr 10) ltac:(rewrite (OZ_S' cntAr 10) by lia; change (10 - 1) with 9; lia).
  zstep Rfd. zsetreg (OZ cntAr 11) ltac:(rewrite (OZ_S' cntAr 11) by lia; change (11 - 1) with 10; lia).
  zstep Rfd. zsetreg (OZ cntAr 12) ltac:(rewrite (OZ_S' cntAr 12) by lia; change (12 - 1) with 11; lia).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zsetreg (OZ cntAr 13) ltac:(rewrite (OZ_S' cntAr 13) by lia; change (13 - 1) with 12; lia).
  zstep Rfd. zsetreg (OZ cntAr 14) ltac:(rewrite (OZ_S' cntAr 14) by lia; change (14 - 1) with 13; lia).
  zstep Rfd. zsetreg (OZ cntAr 15) ltac:(rewrite (OZ_S' cntAr 15) by lia; change (15 - 1) with 14; lia).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx) end.
  all: try first [assumption | close_pregs | zreg].
  unfold mem_u16 in *.
  apply mem_arr_of_elems; [lia | lia | lia | rewrite two64_eq; lia |].
  intros i Hi. change (Z.to_nat 2) with 2%nat. cbn beta.
  assert (CS : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14) by lia.
  unfold offsA. rewrite (offs_spec cntAr HRa) by lia.
  destruct CS as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]]; rewrite E; clear E Hi.
  - replace (sp + -166 + 2 * 0) with (sp + -166) by lia. change (0 + 1) with 1. replace (OZ cntAr 1) with 0 by reflexivity. assumption.
  - replace (sp + -166 + 2 * 1) with (sp + -164) by lia. change (1 + 1) with 2. replace (OZ cntAr 2) with (cA 1) by (rewrite (OZ_S' cntAr 2) by lia; change (2 - 1) with 1; rewrite OZ_1; lia). assumption.
  - replace (sp + -166 + 2 * 2) with (sp + -162) by lia. change (2 + 1) with 3. idtac. assumption.
  - replace (sp + -166 + 2 * 3) with (sp + -160) by lia. change (3 + 1) with 4. idtac. assumption.
  - replace (sp + -166 + 2 * 4) with (sp + -158) by lia. change (4 + 1) with 5. idtac. assumption.
  - replace (sp + -166 + 2 * 5) with (sp + -156) by lia. change (5 + 1) with 6. idtac. assumption.
  - replace (sp + -166 + 2 * 6) with (sp + -154) by lia. change (6 + 1) with 7. idtac. assumption.
  - replace (sp + -166 + 2 * 7) with (sp + -152) by lia. change (7 + 1) with 8. idtac. assumption.
  - replace (sp + -166 + 2 * 8) with (sp + -150) by lia. change (8 + 1) with 9. idtac. assumption.
  - replace (sp + -166 + 2 * 9) with (sp + -148) by lia. change (9 + 1) with 10. idtac. assumption.
  - replace (sp + -166 + 2 * 10) with (sp + -146) by lia. change (10 + 1) with 11. idtac. assumption.
  - replace (sp + -166 + 2 * 11) with (sp + -144) by lia. change (11 + 1) with 12. idtac. assumption.
  - replace (sp + -166 + 2 * 12) with (sp + -142) by lia. change (12 + 1) with 13. idtac. assumption.
  - replace (sp + -166 + 2 * 13) with (sp + -140) by lia. change (13 + 1) with 14. idtac. assumption.
  - replace (sp + -166 + 2 * 14) with (sp + -138) by lia. change (14 + 1) with 15. idtac. assumption.
Qed.
Lemma sort_loop_t : forall fuel i Rb l M MD T,
  (Z.to_nat (codes - i) <= fuel)%nat -> 0 <= i < codes ->
  m_halted MD = None -> pregs6_t Rb l ->
  zget_l Rb l kA6 = i -> zget_l Rb l kT6 = codes -> zget_l Rb l kT2 = sp + -168 ->
  zget_l Rb l kA2 = - (p + 168 + 2 * lens_ofs) + -1 -> zget_l Rb l kT5 = - (sp + -168) + -1 ->
  zget_l Rb l kT3 = 0 -> zget_l Rb l kT4 = 16 -> zget_l Rb l kS0 = 1 ->
  zget_l Rb l kT0 = mx -> zget_l Rb l kT1 = mn -> zget_l Rb l kA7 = rt ->
  it_sort_ok (lensA lf) lens_ofs codes offsAr 288 = true ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (sp - 208) 208 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 168) 320 lf ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -166) 15 (fun j => arr_get (SKo i) (j + 1)) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 808) 288 (arr_get (SKw i)) ->
  (forall R' M', pregs6_t R' [] -> zget_l R' [] kT0 = mx -> zget_l R' [] kT1 = mn -> zget_l R' [] kA7 = rt ->
     mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' (sp + -166) (sp + -136) (p + 808) (p + 1384) ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp - 208) 208 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 808) 288 (arr_get (SKw codes)) ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 100176 (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 100080 (zupd Rb l) M MD) T.
Proof.
  induction fuel as [|fuel IH]; intros i Rb l M MD T Hfuel Hi Hh HP LA6 LT6 LT2 LA2 LT5 LT3 LT4 LS0 LT0 LT1 LA7 SOK Wf Wp Hlens Hoffs Hwork K.
  { exfalso. lia. }
  pose proof C as C'. open_itc C'. open_pregs6_t HP. zkeys. clear HtyC HtyD Hprom Hpb.
  pose proof (Hlens15 i ltac:(lia)) as Hl15. pose proof (Hlf (lens_ofs + i) ltac:(lia)) as Hl16.
  assert (HOr : forall j, 0 <= j < 16 -> 0 <= arr_get (SKo i) j < 65536) by (intros j _; unfold offsA; apply itm_sort_k_offs_range).
  pose proof (mpost_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -166) (sp + -136) (p + 808) (p + 1384) ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost (run_segments R_segs rc_inp rc_sp rc_mb) M X (sp + -166) (sp + -136) (p + 808) (p + 1384)) M) by (apply mpost_refl).
  pose proof (lnot_val_mod' (p + 168 + 2 * lens_ofs) ltac:(lia)) as Hn1.
  pose proof (lnot_val_mod' (sp + -168) ltac:(lia)) as Hn2.
  assert (J : forall RJ MJ, pregs6_t RJ [] ->
    zget_l RJ [] kA6 = i -> zget_l RJ [] kT6 = codes -> zget_l RJ [] kT2 = sp + -168 ->
    zget_l RJ [] kA2 = - (p + 168 + 2 * lens_ofs) + -1 -> zget_l RJ [] kT5 = - (sp + -168) + -1 ->
    zget_l RJ [] kT3 = 0 -> zget_l RJ [] kT4 = 16 -> zget_l RJ [] kS0 = 1 ->
    zget_l RJ [] kT0 = mx -> zget_l RJ [] kT1 = mn -> zget_l RJ [] kA7 = rt ->
    mpost (run_segments R_segs rc_inp rc_sp rc_mb) M MJ (sp + -166) (sp + -136) (p + 808) (p + 1384) ->
    mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) MJ (sp - 208) 208 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) MJ p 7176 ->
    mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) MJ (p + 168) 320 lf ->
    mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) MJ (sp + -166) 15 (fun j => arr_get (SKo (i + 1)) (j + 1)) ->
    mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) MJ (p + 808) 288 (arr_get (SKw (i + 1))) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 100072 (zupd RJ []) MJ MD) T).
  { intros RJ MJ HPJ JA6 JT6 JT2 JA2 JT5 JT3 JT4 JS0 JT0 JT1 JA7 HPO WfJ WpJ HlensJ HoffsJ HworkJ.
    clear HAG Hoffs Hwork Wf Wp Hlens.
    open_pregs6_t HPJ. zkeys. zrebase.
    zstep Rfd.
    destruct (Z.eq_dec (i + 1) codes) as [Hend|Hmore].
    - zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx MJ) end.
      all: try first [assumption | close_pregs6_t | zreg].
      rewrite Hend in HworkJ. exact HworkJ.
    - zbr Rfd false.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (IH (i + 1) Rx [] MJ MD T) end.
      all: try first [lia | assumption | close_pregs6_t | zreg].
      intros R' M'. intros. eapply K; try eassumption.
      eapply mpost_trans; [exact HPO | assumption]. }
  zrebase.
  zstep Rfd. zsetreg (2 * i) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zbr Rfd false.
  zbr Rfd false.
  zstep Rfd.
  tstep Rfd.
  destruct (Z.eq_dec (lf (lens_ofs + i)) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J Rx M) end.
    all: try first [assumption | close_pregs6_t | zreg].
    + rewrite sort_k_skip; [exact Hoffs | lia | rewrite lensA_get; exact Z0].
    + rewrite sort_k_skip; [exact Hwork | lia | rewrite lensA_get; exact Z0].
  - zbr Rfd false.
    pose proof (sort_ok_at (lensA lf) lens_ofs codes offsAr (workA wf) 288 i SOK ltac:(lia) ltac:(rewrite lensA_get; exact NZ)) as HO.
    rewrite lensA_get in HO.
    zbr Rfd false.
    zstep Rfd. zsetreg (2 * lf (lens_ofs + i)) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
    zbr Rfd false.
    zstep Rfd.
    tstep Rfd.
    zsetreg (arr_get (SKo i) (lf (lens_ofs + i))) ltac:(f_equal; lia).
    zstep Rfd.
    zstep Rfd. zsetreg (2 * arr_get (SKo i) (lf (lens_ofs + i))) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep Rfd.
    tstore_arr Rfd Hoffs (lf (lens_ofs + i) - 1).
    zbr Rfd false.
    zstep Rfd. zstep Rfd.
    zsetreg 1 ltac:(rewrite Z.mod_small by lia; destruct (Z.ltb_spec (p + 808 + 2 * arr_get (SKo i) (lf (lens_ofs + i))) 1); [lia | reflexivity]).
    zbr Rfd false.
    zbr Rfd false.
    zstep Rfd. zalign.
    zbr Rfd false.
    tstore_arr Rfd Hwork (arr_get (SKo i) (lf (lens_ofs + i))).
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (J Rx Mx) end.
    all: try first [assumption | close_pregs6_t | zreg].
    + eapply mem_arr_ext; [exact Hoffs|]. intros j Hj. cbn beta.
      rewrite sort_k_take by (try lia; rewrite lensA_get; exact NZ). cbv zeta. rewrite lensA_get. cbn [fst].
      unfold zfupd. rewrite arr_get_set. unfold arr_inb. rewrite (proj1 (sort_k_len _ _ _ _ _)), offsA_len.
      rewrite wrap16_small by lia.
      destruct (Z.eqb_spec j (lf (lens_ofs + i) - 1)); destruct (Z.eqb_spec (lf (lens_ofs + i)) (j + 1)); cbn [andb]; try lia.
      destruct (Z.leb_spec 0 (lf (lens_ofs + i))); destruct (Z.ltb_spec (lf (lens_ofs + i)) 16); cbn [andb]; lia.
    + apply mem_arr_arr_set in Hwork; [| rewrite (proj2 (sort_k_len _ _ _ _ _)), workA_len; lia].
      eapply mem_arr_ext; [exact Hwork|]. intros j Hj. cbn beta.
      rewrite sort_k_take by (try lia; rewrite lensA_get; exact NZ). cbv zeta. rewrite lensA_get. cbn [snd].
      rewrite (wrap16_small i) by lia. reflexivity.
Qed.

Lemma sort_phase_t : forall Rb l M MD T,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kT0 = mx -> zget_l Rb l kT1 = mn -> zget_l Rb l kA7 = rt -> zget_l Rb l kT2 = sp + -168 ->
  1 <= mx -> it_sort_ok (lensA lf) lens_ofs codes offsAr 288 = true ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (sp - 208) 208 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 168) 320 lf ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -166) 15 (fun j => arr_get offsAr (j + 1)) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 808) 288 wf ->
  (forall R' M', pregs6_t R' [] -> zget_l R' [] kT0 = mx -> zget_l R' [] kT1 = mn -> zget_l R' [] kA7 = rt ->
     mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' (sp + -166) (sp + -136) (p + 808) (p + 1384) ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' (sp - 208) 208 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 808) 288 (arr_get work1Ar) ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 100176 (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 100028 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T Hh HP LT0 LT1 LA7 LT2 Hmx SOK Wf Wp Hlens Hoffs Hwork K.
  pose proof C as C'. open_itc C'. clear HtyC HtyD Hprom Hpb.
  assert (Hc0 : 0 < codes).
  { destruct (Z.eq_dec codes 0) as [E|]; [|lia]. exfalso. enough (mx = 0) by lia. unfold mxA. apply mx_zero.
    intros j _. rewrite cntA_eq, E. unfold cntK. rewrite itm_count_k_0 by lia. apply it_zero_count_spec. }
  assert (Hoffs0 : mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (sp + -166) 15 (fun j => arr_get (SKo 0) (j + 1))).
  { rewrite itm_sort_k_0 by lia. cbn [fst]. exact Hoffs. }
  assert (Hwork0 : mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 808) 288 (arr_get (SKw 0))).
  { rewrite itm_sort_k_0 by lia. cbn [snd]. eapply mem_arr_ext; [exact Hwork|]. intros j _. symmetry. apply workA_get. }
  clear Hoffs Hwork. open_pregs HP. zkeys. zrebase.
  zbr Rfd false.
  zbr Rfd false.
  zstep Rfd.
  zstep Rfd. zalign.
  zstep Rfd.
  zstep Rfd. znot.
  zstep Rfd.
  zstep Rfd. znot.
  zstep Rfd. zsetreg codes ltac:(symmetry; apply zext32_id; lia).
  zstep Rfd. zbool.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (sort_loop_t (Z.to_nat codes) 0 Rx [] M MD T) end.
  all: try first [lia | assumption | close_pregs6_t | zreg].
Qed.
End U8IT2.
