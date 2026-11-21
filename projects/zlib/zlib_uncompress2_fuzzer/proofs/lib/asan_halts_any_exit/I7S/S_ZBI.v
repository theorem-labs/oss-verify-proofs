(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.IK Require IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.I7S Require S_U2C.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit Require Frame Hoare.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit Require RefMemcpyLib FuzzMem S7MemcpyBase S7Memcpy S7AdlerBase S7AdlerIface S7Adler.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit Require S7LibStmt.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Inftrees InftreesCoverage ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.I7S Require Base.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.IK Require ZTac ZMem ZCall ZCallL ZArr ZArr4 IDefs ISpecs ITac.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.I7S Require S_It0 S_It3.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.I7S Require S_It4 S_It5 S_It6.

Module S_It2.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.zspec.zmodel.ItableModel.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.I7S.Base.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.IK.ZTac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.IK.ZArr OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.IK.ZArr4 OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.IK.IDefs OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.IK.ISpecs OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.IK.ITac.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.I7S.S_It0 OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.I7S.S_It3.S_It1.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.PropExec.FPState}.

Section S7IT2.
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 192 zc.

#[local] Abbreviation PR := (pregs p lens_ofs codes pb sp vgp vtp (cty ty)).
#[local] Abbreviation cA := (arr_get (cntA lf lens_ofs codes)).
#[local] Abbreviation cntAr := (cntA lf lens_ofs codes).
#[local] Abbreviation mx := (mxA lf lens_ofs codes).
#[local] Abbreviation mn := (mnA lf lens_ofs codes).
#[local] Abbreviation rt := (rootA lf lens_ofs codes bits).
#[local] Abbreviation L k := (LZ (cntA lf lens_ofs codes) k).
#[local] Abbreviation KLEFT := (Kleft ty lf lens_ofs codes bits p pb sp vgp vtp).
#[local] Abbreviation offsAr := (offsA lf lens_ofs codes).
#[local] Abbreviation SKo i := (fst (itm_sort_k (lensA lf) lens_ofs i (offsA lf lens_ofs codes) (workA wf))).
#[local] Abbreviation work1Ar := (work1A lf lens_ofs codes wf).
#[local] Abbreviation SKw i := (snd (itm_sort_k (lensA lf) lens_ofs i (offsA lf lens_ofs codes) (workA wf))).

Lemma cty_codes : (cty ty =? 0) = codetype_eqb ty CODES.
Proof using C zc ret sp pb p wf cf bits nx codes lens_ofs lf. destruct ty; reflexivity. Qed.

Definition Kneg (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', PR R' [] -> zget_l R' [] kA6 = -1 ->
    itm_reject ty mx (it_left_check cntAr) = true -> 1 <= mx ->
    realizes R_segs (zcfg R_segs 97396 (zupd R' []) M MD) T.

Definition Koffs (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', PR R' [] -> zget_l R' [] kT0 = mx -> zget_l R' [] kT1 = mn -> zget_l R' [] kA7 = rt ->
    zget_l R' [] kT4 = cA 1 -> zget_l R' [] kT5 = cA 2 -> zget_l R' [] kT6 = cA 3 -> zget_l R' [] kS0 = cA 4 ->
    zget_l R' [] kS1 = cA 5 -> zget_l R' [] kS2 = cA 6 -> zget_l R' [] kS3 = cA 7 -> zget_l R' [] kS4 = cA 8 ->
    zget_l R' [] kS5 = cA 9 -> zget_l R' [] kS6 = cA 10 -> zget_l R' [] kS7 = cA 11 -> zget_l R' [] kS8 = cA 12 ->
    zget_l R' [] kS9 = cA 13 -> zget_l R' [] kS10 = cA 14 ->
    1 <= mx -> itm_reject ty mx (it_left_check cntAr) = false ->
    realizes R_segs (zcfg R_segs 96476 (zupd R' []) M MD) T.

Lemma left_s : forall M MD T,
  m_halted MD = None -> mem_arr 2 R_segs M (sp + -136) 16 cA -> Kneg M MD T -> Koffs M MD T -> KLEFT M MD T.
Proof using C zc ret wf cf nx.
  intros M MD T Hh Hcnt KN KO. unfold Kleft. intros Rb HP LT0 LT1 LA7 LT3 LT2 Hmx.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range _ _ _ _ _ _ _ _ _ _ _ _ _ C j); lia).
  assert (HRa : forall j, 0 <= cA j <= codes) by (intros j; apply (cA_range _ _ _ _ _ _ _ _ _ _ _ _ _ C j)).
  assert (LB : forall j, 0 <= j <= 15 -> -18874368 <= L j <= 32768).
  { intros j Hj. pose proof (LZ_bound cntAr j codes ltac:(lia) HRa Hj). lia. }
  assert (PP0 : forall j, 1 <= j <= 0 -> 0 <= L j) by (intros; lia).
  pose proof (HRa 1) as HR1. pose proof (HRa 15) as HR15.
  zrebase.
  tstep Rfd. zstep Rfd. zstep Rfd.
  destruct (Z.ltb_spec 2 (cA 1)) as [F1|P1].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite (left_check_none cntAr 1); [reflexivity | lia | intros; lia | rewrite LZ_1; lia]. }
  zbr Rfd false.
  assert (PP1 : forall j, 1 <= j <= 1 -> 0 <= L j) by (intros j Hj; replace j with 1 by lia; rewrite LZ_1; lia). clear PP0.
  pose proof (LB 1 ltac:(lia)) as LB1. pose proof (LB 2 ltac:(lia)) as LB2. pose proof (HRa 2) as HR2.
  zstep Rfd. zsetreg (2 * cA 1) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd. tstep Rfd.
  zstep Rfd. zsetreg (2 * L 1) ltac:(rewrite swrap32_small by lia; rewrite LZ_1; lia).
  zstep Rfd. zstep Rfd. zsetreg (2 * L 1) ltac:(symmetry; apply zext16_id; rewrite LZ_1; lia).
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
  zstep Rfd. zsetreg (L 9) ltac:(rewrite (LZ_S' cntAr 9) by lia; reflexivity).
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

Lemma offs_s : forall M MD T,
  m_halted MD = None -> mem_wr R_segs M (sp - 192) 192 ->
  (forall R' M', PR R' [] -> zget_l R' [] kT0 = mx -> zget_l R' [] kT1 = mn -> zget_l R' [] kA7 = rt ->
     mpost R_segs M M' (sp + -166) (sp + -136) 0 0 ->
     mem_arr 2 R_segs M' (sp + -166) 15 (fun j => arr_get offsAr (j + 1)) ->
     1 <= mx -> itm_reject ty mx (it_left_check cntAr) = false ->
     realizes R_segs (zcfg R_segs 96588 (zupd R' []) M' MD) T) ->
  Koffs M MD T.
Proof using C zc ret wf cf nx.
  intros M MD T Hh Wf K. unfold Koffs.
  intros Rb HP LT0 LT1 LA7 LT4 LT5 LT6 LS0 LS1 LS2 LS3 LS4 LS5 LS6 LS7 LS8 LS9 LS10 Hmx HRJ.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys.
  assert (HRa : forall j, 0 <= cA j <= 288) by (intros j; pose proof (cA_range _ _ _ _ _ _ _ _ _ _ _ _ _ C j); lia).
  pose proof (mpost_stable R_segs M (sp + -166) (sp + -136) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X (sp + -166) (sp + -136) 0 0) M) by (apply mpost_refl).
  zrebase.
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
Lemma sort_loop_s : forall fuel i Rb l M MD T,
  (Z.to_nat (codes - i) <= fuel)%nat -> 0 <= i < codes ->
  m_halted MD = None -> PR Rb l ->
  zget_l Rb l kA6 = i -> zget_l Rb l kT3 = p + 168 + 2 * lens_ofs + 2 * i -> zget_l Rb l kT2 = sp + -168 ->
  zget_l Rb l kT0 = mx -> zget_l Rb l kT1 = mn -> zget_l Rb l kA7 = rt ->
  it_sort_ok (lensA lf) lens_ofs codes offsAr 288 = true ->
  mem_wr R_segs M (sp - 192) 192 -> mem_wr R_segs M p 7176 ->
  mem_arr 2 R_segs M (p + 168) 320 lf ->
  mem_arr 2 R_segs M (sp + -166) 15 (fun j => arr_get (SKo i) (j + 1)) ->
  mem_arr 2 R_segs M (p + 808) 288 (arr_get (SKw i)) ->
  (forall R' M', PR R' [] -> zget_l R' [] kT0 = mx -> zget_l R' [] kT1 = mn -> zget_l R' [] kA7 = rt ->
     mpost R_segs M M' (sp + -166) (sp + -136) (p + 808) (p + 1384) ->
     mem_wr R_segs M' (sp - 192) 192 -> mem_wr R_segs M' p 7176 ->
     mem_arr 2 R_segs M' (p + 168) 320 lf ->
     mem_arr 2 R_segs M' (p + 808) 288 (arr_get (SKw codes)) ->
     realizes R_segs (zcfg R_segs 96672 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 96628 (zupd Rb l) M MD) T.
Proof using C zc ret cf nx.
  induction fuel as [|fuel IH]; intros i Rb l M MD T Hfuel Hi Hh HP LA6 LT3 LT2 LT0 LT1 LA7 SOK Wf Wp Hlens Hoffs Hwork K.
  { exfalso. lia. }
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys.
  pose proof (Hlens15 i ltac:(lia)) as Hl15. pose proof (Hlf (lens_ofs + i) ltac:(lia)) as Hl16.
  assert (HOr : forall j, 0 <= j < 16 -> 0 <= arr_get (SKo i) j < 65536) by (intros j _; unfold offsA; apply itm_sort_k_offs_range).
  pose proof (mpost_stable R_segs M (sp + -166) (sp + -136) (p + 808) (p + 1384) ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X (sp + -166) (sp + -136) (p + 808) (p + 1384)) M) by (apply mpost_refl).
  assert (J : forall RJ MJ, PR RJ [] ->
    zget_l RJ [] kA6 = i -> zget_l RJ [] kT3 = p + 168 + 2 * lens_ofs + 2 * i -> zget_l RJ [] kT2 = sp + -168 ->
    zget_l RJ [] kT0 = mx -> zget_l RJ [] kT1 = mn -> zget_l RJ [] kA7 = rt ->
    mpost R_segs M MJ (sp + -166) (sp + -136) (p + 808) (p + 1384) ->
    mem_wr R_segs MJ (sp - 192) 192 -> mem_wr R_segs MJ p 7176 ->
    mem_arr 2 R_segs MJ (p + 168) 320 lf ->
    mem_arr 2 R_segs MJ (sp + -166) 15 (fun j => arr_get (SKo (i + 1)) (j + 1)) ->
    mem_arr 2 R_segs MJ (p + 808) 288 (arr_get (SKw (i + 1))) ->
    realizes R_segs (zcfg R_segs 96616 (zupd RJ []) MJ MD) T).
  { intros RJ MJ HPJ JA6 JT3 JT2 JT0 JT1 JA7 HPO WfJ WpJ HlensJ HoffsJ HworkJ.
    clear HAG Hoffs Hwork Wf Wp Hlens.
    open_pregs HPJ. zkeys. zrebase.
    zstep Rfd. zstep Rfd.
    destruct (Z.eq_dec (i + 1) codes) as [Hend|Hmore].
    - zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx MJ) end.
      all: try first [assumption | close_pregs | zreg].
      rewrite Hend in HworkJ. exact HworkJ.
    - zbr Rfd false.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (IH (i + 1) Rx [] MJ MD T) end.
      all: try first [lia | assumption | close_pregs | zreg].
      intros R' M'. intros. eapply K; try eassumption.
      eapply mpost_trans; [exact HPO | assumption]. }
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (lf (lens_ofs + i)) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J Rx M) end.
    all: try first [assumption | close_pregs | zreg].
    + rewrite sort_k_skip; [exact Hoffs | lia | rewrite lensA_get; exact Z0].
    + rewrite sort_k_skip; [exact Hwork | lia | rewrite lensA_get; exact Z0].
  - zbr Rfd false.
    pose proof (sort_ok_at (lensA lf) lens_ofs codes offsAr (workA wf) 288 i SOK ltac:(lia) ltac:(rewrite lensA_get; exact NZ)) as HO.
    rewrite lensA_get in HO.
    zstep Rfd. zsetreg (2 * lf (lens_ofs + i)) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep Rfd.
    tstep Rfd.
    zsetreg (arr_get (SKo i) (lf (lens_ofs + i))) ltac:(f_equal; lia).
    zstep Rfd.
    zstep Rfd. zsetreg (2 * arr_get (SKo i) (lf (lens_ofs + i))) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
    tstore_arr Rfd Hoffs (lf (lens_ofs + i) - 1).
    zstep Rfd.
    tstore_arr Rfd Hwork (arr_get (SKo i) (lf (lens_ofs + i))).
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (J Rx Mx) end.
    all: try first [assumption | close_pregs | zreg].
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

Lemma sort_phase_s : forall Rb l M MD T,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kT0 = mx -> zget_l Rb l kT1 = mn -> zget_l Rb l kA7 = rt ->
  1 <= mx -> it_sort_ok (lensA lf) lens_ofs codes offsAr 288 = true ->
  mem_wr R_segs M (sp - 192) 192 -> mem_wr R_segs M p 7176 ->
  mem_arr 2 R_segs M (p + 168) 320 lf ->
  mem_arr 2 R_segs M (sp + -166) 15 (fun j => arr_get offsAr (j + 1)) ->
  mem_arr 2 R_segs M (p + 808) 288 wf ->
  (forall R' M', PR R' [] -> zget_l R' [] kT0 = mx -> zget_l R' [] kT1 = mn -> zget_l R' [] kA7 = rt ->
     mpost R_segs M M' (sp + -166) (sp + -136) (p + 808) (p + 1384) ->
     mem_wr R_segs M' (sp - 192) 192 -> mem_wr R_segs M' p 7176 ->
     mem_arr 2 R_segs M' (p + 168) 320 lf ->
     mem_arr 2 R_segs M' (p + 808) 288 (arr_get work1Ar) ->
     realizes R_segs (zcfg R_segs 96672 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 96588 (zupd Rb l) M MD) T.
Proof using C zc ret cf nx.
  intros Rb l M MD T Hh HP LT0 LT1 LA7 Hmx SOK Wf Wp Hlens Hoffs Hwork K.
  pose proof C as C'. open_itc C'.
  assert (Hc0 : 0 < codes).
  { destruct (Z.eq_dec codes 0) as [E|]; [|lia]. exfalso. enough (mx = 0) by lia. unfold mxA. apply mx_zero.
    intros j _. rewrite cntA_eq, E. unfold cntK. rewrite itm_count_k_0 by lia. apply it_zero_count_spec. }
  assert (Hoffs0 : mem_arr 2 R_segs M (sp + -166) 15 (fun j => arr_get (SKo 0) (j + 1))).
  { rewrite itm_sort_k_0 by lia. cbn [fst]. exact Hoffs. }
  assert (Hwork0 : mem_arr 2 R_segs M (p + 808) 288 (arr_get (SKw 0))).
  { rewrite itm_sort_k_0 by lia. cbn [snd]. eapply mem_arr_ext; [exact Hwork|]. intros j _. symmetry. apply workA_get. }
  clear Hoffs Hwork. open_pregs HP. zkeys. zrebase.
  zbr Rfd false.
  zstep Rfd.
  zstep Rfd. zstep Rfd. zsetreg codes ltac:(symmetry; apply zext32_id; lia).
  zstep Rfd. zstep Rfd. zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (sort_loop_s (Z.to_nat codes) 0 Rx [] M MD T) end.
  all: try first [lia | assumption | close_pregs | zreg].
Qed.

End S7IT2.
End FXG.
End S_It2.

Module S_It7.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.zspec.zmodel.ItableModel.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.I7S.Base.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.IK.ZTac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.IK.ZMem OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.IK.ZCall OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.IK.ZCallL OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.IK.ZArr OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.IK.ZArr4 OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.IK.IDefs OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.IK.ISpecs OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.IK.ITac.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.I7S.S_It0 OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.I7S.S_It3.S_It1 S_It2 OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.I7S.S_It3 OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.I7S.S_It4 OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.I7S.S_It5 OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.I7S.S_It6.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.PropExec.FPState}.

Section S7IT7.
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 192 zc.

#[local] Abbreviation PR := (pregs p lens_ofs codes pb sp vgp vtp (cty ty)).
#[local] Abbreviation cA := (arr_get (cntA lf lens_ofs codes)).
#[local] Abbreviation cntAr := (cntA lf lens_ofs codes).
#[local] Abbreviation mx := (mxA lf lens_ofs codes).
#[local] Abbreviation mn := (mnA lf lens_ofs codes).
#[local] Abbreviation rt := (rootA lf lens_ofs codes bits).
#[local] Abbreviation offsAr := (offsA lf lens_ofs codes).
#[local] Abbreviation work1Ar := (work1A lf lens_ofs codes wf).
#[local] Abbreviation X := (itm_ctx ty (lensA lf) lens_ofs nx (rootA lf lens_ofs codes bits) (mxA lf lens_ofs codes)).
#[local] Abbreviation st0 := (itm_st0 (mnA lf lens_ofs codes) nx (rootA lf lens_ofs codes bits) (cntA lf lens_ofs codes) (tblA cf) (work1A lf lens_ofs codes wf)).

Definition FP : list (Z * Z) := [(sp - 192, 192); (p + 160, 8); (pb, 4); (p + 808, 576); (p + 1384, 5776)].
Definition FPS : list (Z * Z) := [(sp + -192, 88); (p + 160, 8); (pb, 4); (p + 808, 576); (p + 1384, 5776)].

Definition pf (M : mem) : Prop :=
  mem_wr R_segs M p 7176 /\ mem_arr 2 R_segs M (p + 168) 320 lf /\ mem_arr 4 R_segs M (p + 1384) 1444 cf /\
  mem_arr 2 R_segs M (p + 808) 288 wf /\ mem_u64 R_segs M (p + 160) (p + 1384 + 4 * nx) /\ mem_u32 R_segs M pb bits /\
  mem_arr 2 R_segs M 67170 31 (arr_get lbase_a) /\ mem_arr 2 R_segs M 67232 31 (arr_get lext_a) /\
  mem_arr 2 R_segs M 67294 32 (arr_get dbase_a) /\ mem_arr 2 R_segs M 67358 32 (arr_get dext_a).
Ltac open_pf H :=
  unfold pf in H;
  let a := fresh "Wp" in let b := fresh "Hlens" in let c := fresh "Htabl" in let d := fresh "Hwork" in
  let e := fresh "Hnext" in let f := fresh "Hbcell" in let g := fresh "Hlb" in let h := fresh "Hle" in
  let i := fresh "Hdb" in let j := fresh "Hde" in
  dand H as (a & b & c & d & e & f & g & h & i & j).

Lemma pf_frame : forall M M' lo hi, pf M -> mpost R_segs M M' lo hi 0 0 -> zc <= lo -> pf M'.
Proof using C ret sp codes lens_ofs ty.
  intros M M' lo hi HP [HA HW] Hlo. pose proof C as C'. open_itc C'. unfold ZSEP in Hpb. open_pf HP. unfold pf. split_conj.
  - apply HW. exact Wp.
  - eapply mem_arr_magree; [exact HA | exact Hlens | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Htabl | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hwork | lia_std | lia_std].
  - eapply mem_u64_magree; [exact HA | exact Hnext | lia_std | rewrite two64_eq; lia_std | lia_std | lia_std].
  - eapply mem_u32_magree; [exact HA | exact Hbcell | lia_std | rewrite two64_eq; lia_std | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hlb | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hle | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hdb | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hde | lia_std | lia_std].
Qed.

Lemma slots_fps : forall M M' v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27,
  slots sp M v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 -> mpostL R_segs M M' FPS ->
  slots sp M' v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27.
Proof using C zc ret wf cf bits nx codes lens_ofs lf ty.
  intros M M' v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 HS [HA HW]. pose proof C as C'. open_itc C'. unfold ZSEP in Hpb.
  unfold slots in *. destr_conj HS. split_conj.
  all: eapply mem_u64_magreeL; [exact HA | eassumption | lia_std | rewrite two64_eq; lia_std | cbn; lia_std].
Qed.


Lemma acc2 : forall M0 M M' a1 b1 a2 b2,
  framed (fun X => mpostL R_segs M0 X FPS) M -> mpost R_segs M M' a1 b1 a2 b2 ->
  in_some a1 (b1 - a1) FPS \/ b1 <= a1 -> in_some a2 (b2 - a2) FPS \/ b2 <= a2 ->
  framed (fun X => mpostL R_segs M0 X FPS) M'.
Proof using. intros. eapply framed_mpostL_trans2; eassumption. Qed.
Lemma accL : forall M0 M M', framed (fun X => mpostL R_segs M0 X FPS) M -> mpostL R_segs M M' (rsL p sp) ->
  framed (fun X => mpostL R_segs M0 X FPS) M'.
Proof using.
  intros M0 M M' HF HP. eapply framed_mpostL_trans; [exact HF | exact HP |].
  intros x Hx. cbn in *. lia_std.
Qed.
Lemma accT : forall M0 M M', framed (fun X => mpostL R_segs M0 X FPS) M -> mpostL R_segs M M' (rsT p pb) ->
  framed (fun X => mpostL R_segs M0 X FPS) M'.
Proof using.
  intros M0 M M' HF HP. eapply framed_mpostL_trans; [exact HF | exact HP |].
  intros x Hx. cbn in *. lia_std.
Qed.

Lemma safe_sort : mx <> 0 -> itm_reject ty mx (it_left_check cntAr) = false ->
  it_sort_ok (lensA lf) lens_ofs codes offsAr 288 = true /\
  (it_not_enough ty (itm_used rt) = false -> it_loop_ok (Z.to_nat (codes + 1)) X 288 320 1444 st0 = true).
Proof using C zc ret sp pb p.
  intros Hmx Hrj.
  pose proof (it_safe_sort ty (lensA lf) lens_ofs codes (tblA cf) nx bits (workA wf) (it_safe_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ C)) as S.
  cbv zeta in S. unfold mxA, cntA, rootA, mnA, mxA, cntA, offsA, work1A, offsA, cntA in *.
  specialize (S Hmx Hrj). destruct S as [S1 S2].
  unfold workA, lensA, tblA in S1, S2 |- *. rewrite !arr_len_init in S1, S2. cbv [N_WORK N_LENS N_CODES] in S1, S2 |- *.
  split; [exact S1 | intros Hne; exact (proj2 (proj2 (S2 Hne)))].
Qed.

Lemma fin_fp : forall M M1 M', mpost R_segs M M1 (sp + -192) sp 0 0 -> mpostL R_segs M1 M' FPS -> mpostL R_segs M M' FP.
Proof using C zc ret wf cf bits nx codes lens_ofs lf ty.
  intros M M1 M' HP [HA HW]. pose proof C as C'. open_itc C'.
  pose proof (framed_mpostL_trans2 R_segs M M M1 FP _ _ _ _ (mpostL_refl R_segs M FP) HP ltac:(left; cbn; left; lia_std) ltac:(right; lia_std)) as [A1 W1].
  split; [| intros a n Hw; apply HW; apply W1; exact Hw].
  intros x Hx. rewrite (HA x); [apply A1; exact Hx|]. cbn in Hx |- *. lia_std.
Qed.

Lemma cA_zero : codes = 0 -> forall j, arr_get cntAr j = 0.
Proof using. intros Hc j. rewrite cntA_eq, Hc. unfold cntK. rewrite itm_count_k_0 by lia_std. apply it_zero_count_spec. Qed.

Lemma tbl_max0_range : forall j, 0 <= j < 1444 ->
  0 <= arr_get (arr_set (arr_set (tblA cf) nx (code_pack 64 1 0)) (nx + 1) (code_pack 64 1 0)) j < 4294967296.
Proof using C zc ret sp pb p wf bits codes lens_ofs lf ty.
  intros j Hj. pose proof C as C'. open_itc C'.
  rewrite !arr_get_set. destruct (_ && _); [apply code_pack_range|]. destruct (_ && _); [apply code_pack_range|].
  rewrite tblA_get. apply Hcf. exact Hj.
Qed.
Lemma tbl_brk_range : forall st, (forall j, 0 <= j < 1444 -> 0 <= arr_get (t_tbl st) j < 4294967296) ->
  forall j, 0 <= j < 1444 ->
  0 <= arr_get (if negb (t_huff st =? 0) then arr_set (t_tbl st) (t_next st + t_huff st) (code_pack 64 (t_len st - t_drop st) 0) else t_tbl st) j < 4294967296.
Proof using.
  intros st H j Hj. destruct (negb _); [|apply H; exact Hj]. rewrite arr_get_set. destruct (_ && _); [apply code_pack_range | apply H; exact Hj].
Qed.
Lemma tblA_range : forall j, 0 <= j < 1444 -> 0 <= arr_get (tblA cf) j < 4294967296.
Proof using C zc ret sp pb p wf bits nx codes lens_ofs lf ty. intros j Hj. pose proof C as C'. open_itc C'. rewrite tblA_get. apply Hcf. exact Hj. Qed.
Lemma workA_range : forall j, 0 <= j < 288 -> 0 <= arr_get (workA wf) j < 65536.
Proof using C zc ret sp pb p cf bits nx codes lens_ofs lf ty. intros j Hj. pose proof C as C'. open_itc C'. rewrite workA_get. apply Hwf. exact Hj. Qed.
End S7IT7.

End FXG.
Ltac open_pf H :=
  unfold pf in H;
  let a := fresh "Wp" in let b := fresh "Hlens" in let c := fresh "Htabl" in let d := fresh "Hwork" in
  let e := fresh "Hnext" in let f := fresh "Hbcell" in let g := fresh "Hlb" in let h := fresh "Hle" in
  let i := fresh "Hdb" in let j := fresh "Hde" in
  dand H as (a & b & c & d & e & f & g & h & i & j).
Ltac zkeys_all := cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS0 kS1 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS2 kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS10 kS11 kT3 kT4 kT5 kT6] in *.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.PropExec.FPState}.

Theorem itable_s : itable_spec_at R_segs A_ITABLE 192.
Proof.
  unfold itable_spec_at, A_ITABLE.
  intros Rb l M MD T ty p lens_ofs codes nx bits pb sp ret zc lf cf wf.
  intros Hh LA0 LA1 LA2 LA3 LA4 LA5 LSP LRA Hret Hret2 Hpb Hpal Hp0 Hpceil Hsp Hzrom Hsp2 Hspal Hprom
         Wf0 Wp0 Hlens0 Htab0 Hwork0 Hnext0 Hbits0 Hlb0 Hle0 Hdb0 Hde0 Rlf Rcf Rwf
         Hofs Hofs2 Hc0 Hc288 Hl15 HtyC HtyD Hb1 Hb15 Hnx Hroom K.
  cbv [o_lens o_next o_work o_codes N_LENS N_CODES N_WORK STATE_SIZE LBASE_ADDR LEXT_ADDR DBASE_ADDR DEXT_ADDR
       o_lenbits o_distbits ROM_LO_ALL it_fp] in *.
  set (vgp := zget_l Rb l kGP). set (vtp := zget_l Rb l kTP).
  assert (C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 192 zc).
  { constructor; cbv [N_LENS N_CODES N_WORK STATE_SIZE o_lenbits o_distbits ROM_LO_ALL DEXT_ADDR]; try assumption; try lia_std. }
  assert (PF0 : pf lf nx bits cf wf p pb M) by (unfold pf; split_conj; assumption).
  assert (FIN : forall R' M' rv (T' W' : arr) tab' b',
    resA ty lf lens_ofs codes nx bits cf wf = (rv, T', tab', b', W') ->
    zget_l R' [] kSP = sp + -192 -> zget_l R' [] kGP = vgp -> zget_l R' [] kTP = vtp -> zget_l R' [] kA6 = rv ->
    slots sp M' ret (zget_l Rb l kS0) (zget_l Rb l kS1) (zget_l Rb l kS2) (zget_l Rb l kS3) (zget_l Rb l kS4)
          (zget_l Rb l kS5) (zget_l Rb l kS6) (zget_l Rb l kS7) (zget_l Rb l kS8) (zget_l Rb l kS9)
          (zget_l Rb l kS10) (zget_l Rb l kS11) ->
    mpostL R_segs M M' (FP p pb sp) ->
    mem_arr 2 R_segs M' (p + 168) 320 lf -> mem_arr 4 R_segs M' (p + 1384) 1444 (arr_get T') -> mem_arr 2 R_segs M' (p + 808) 288 (arr_get W') ->
    (forall i, 0 <= i < 1444 -> 0 <= arr_get T' i < 4294967296) -> (forall i, 0 <= i < 288 -> 0 <= arr_get W' i < 65536) ->
    mem_u64 R_segs M' (p + 160) (p + 1384 + 4 * tab') -> mem_u32 R_segs M' pb b' ->
    realizes R_segs (zcfg R_segs 97396 (zupd R' []) M' MD) T).
  { intros R' M' rv T' W' tab' b' ER LSP' LGP' LTP' LA6' HSL HPL Hlens' Htab' Hwork' RT RW Hnext' Hbits'.
    eapply (epilogue_s ty lf lens_ofs codes nx bits cf wf p pb sp ret zc C R' [] M' MD T rv ret); try eassumption.
    intros R'' FA0 FSP FRA FS0 FS1 FS2 FS3 FS4 FS5 FS6 FS7 FS8 FS9 FS10 FS11 FGP FTP.
    assert (RES : it_ret (resA ty lf lens_ofs codes nx bits cf wf) = rv /\ it_tbl (resA ty lf lens_ofs codes nx bits cf wf) = T' /\
                  it_table (resA ty lf lens_ofs codes nx bits cf wf) = tab' /\ it_bits (resA ty lf lens_ofs codes nx bits cf wf) = b' /\
                  it_work (resA ty lf lens_ofs codes nx bits cf wf) = W').
    { rewrite ER. repeat split; reflexivity. }
    unfold resA, lensA, tblA, workA in RES. cbv [N_LENS N_CODES N_WORK] in RES. dand RES as (E1 & E2 & E3 & E4 & E5).
    assert (RV3 : rv = 0 \/ rv = 1 \/ rv = -1).
    { pose proof (res_phases ty lf lens_ofs codes nx bits cf wf) as PH. rewrite ER in PH.
      destruct (mxA lf lens_ofs codes =? 0); [injection PH; intros; lia_std|].
      destruct (itm_reject _ _ _); [injection PH; intros; lia_std|].
      destruct (it_not_enough _ _); [injection PH; intros; lia_std|].
      destruct (it_loop _ _ _); injection PH; intros; lia_std. }
    eapply (K R'' M' (arr_get T') (arr_get W')); cbv zeta; rewrite ?E1, ?E2, ?E3, ?E4, ?E5; try assumption.
    all: try (intros; reflexivity).
    unfold kept_eq. cbv [zget_l alookup] in FSP, FS0, FS1, FS2, FS3, FS4, FS5, FS6, FS7, FS8, FS9, FS10, FS11, FGP, FTP.
    rewrite FSP, FGP, FTP, FS0, FS1, FS2, FS3, FS4, FS5, FS6, FS7, FS8, FS9, FS10, FS11. subst vgp vtp.
    repeat split; first [reflexivity | symmetry; assumption | assumption]. }
  pose proof (it_safe_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as SAFE.
  eapply (it_prologue_s Rb l M MD T sp ret vgp vtp (zget_l Rb l kS0) (zget_l Rb l kS1) (cty ty) (p + 168 + 2 * lens_ofs) codes (p + 160) pb (p + 808)
            (zget_l Rb l kS2) (zget_l Rb l kS3) (zget_l Rb l kS4) (zget_l Rb l kS5) (zget_l Rb l kS6) (zget_l Rb l kS7)
            (zget_l Rb l kS8) (zget_l Rb l kS9) (zget_l Rb l kS10) (zget_l Rb l kS11) Hh); try assumption; try reflexivity; try lia.
  intros R1 M1 QSP QGP QTP QA0 QA1 QA2 QA3 QA4 QA5 HPO1 Wf1 S1 S8 S9 S18 S19 S20 S21 S22 S23 S24 S25 S26 S27 Hcnt0.
  assert (HSL1 : slots sp M1 ret (zget_l Rb l kS0) (zget_l Rb l kS1) (zget_l Rb l kS2) (zget_l Rb l kS3) (zget_l Rb l kS4)
          (zget_l Rb l kS5) (zget_l Rb l kS6) (zget_l Rb l kS7) (zget_l Rb l kS8) (zget_l Rb l kS9) (zget_l Rb l kS10) (zget_l Rb l kS11))
    by (unfold slots; split_conj; assumption).
  clear S1 S8 S9 S18 S19 S20 S21 S22 S23 S24 S25 S26 S27.
  pose proof (pf_frame _ _ _ _ _ _ _ _ _ _ _ _ _ C M M1 _ _ PF0 HPO1 ltac:(lia)) as PF1.
  assert (HAGS1 : framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) M1) by (apply mpostL_refl).
  assert (PR1 : pregs p lens_ofs codes pb sp vgp vtp (cty ty) R1 []) by (unfold pregs; split_conj; assumption).
  assert (KC : forall Mc, pf lf nx bits cf wf p pb Mc -> mem_wr R_segs Mc (sp - 192) 192 -> mem_arr 2 R_segs Mc (sp + -136) 16 (arr_get (cntA lf lens_ofs codes)) ->
            framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) Mc ->
            Kleft ty lf lens_ofs codes bits p pb sp vgp vtp Mc MD T /\ Kmax0 ty lf lens_ofs codes p pb sp vgp vtp Mc MD T).
  { intros Mc PFc Wfc Hcntc HAGc. pose proof PFc as PFc'. unfold pf in PFc'.
    dand PFc' as (Wpc & Hlens1 & Htabl0 & Hwork1 & Hnext1 & Hbcell0 & Hlb1 & Hle1 & Hdb1 & Hde1). split.
    -
      apply (left_s ty lf lens_ofs codes nx bits cf wf p pb sp ret vgp vtp zc C Mc MD T Hh Hcntc).
      +
        unfold Kneg. intros R' HP' LA6 Hrj Hmx1. open_pregs HP'.
        eapply (FIN R' Mc (-1) (tblA cf) (workA wf) nx bits); try eassumption.
        * rewrite res_phases. destruct (Z.eqb_spec (mxA lf lens_ofs codes) 0); [lia|]. rewrite Hrj. reflexivity.
        * eapply slots_fps; [exact C | exact HSL1 | exact HAGc].
        * eapply fin_fp; [exact C | exact HPO1 | exact HAGc].
        * eapply mem_arr_ext; [exact Htabl0|]. intros; symmetry; apply tblA_get.
        * eapply mem_arr_ext; [exact Hwork1|]. intros; symmetry; apply workA_get.
        * apply (tblA_range _ _ _ _ _ _ _ _ _ _ _ _ _ C).
        * apply (workA_range _ _ _ _ _ _ _ _ _ _ _ _ _ C).
      +
        apply (offs_s ty lf lens_ofs codes nx bits cf wf p pb sp ret vgp vtp zc C Mc MD T Hh Wfc).
        intros R3 M3 HP3 LT0 LT1 LA7 HPO3 Hoffs Hmx1 Hrj.
        assert (Hmx0 : mxA lf lens_ofs codes <> 0) by lia.
        destruct (safe_sort _ _ _ _ _ _ _ _ _ _ _ _ _ C Hmx0 Hrj) as [SOK LOOPOK].
        pose proof (pf_frame _ _ _ _ _ _ _ _ _ _ _ _ _ C Mc M3 _ _ PFc HPO3 ltac:(lia)) as PF3.
        dand PF3 as (Wp3 & Hlens3 & Htab3 & Hwork3 & Hnext3 & Hbits3 & Hlb3 & Hle3 & Hdb3 & Hde3).
        assert (HAG3 : framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) M3) by (eapply acc2; [exact HAGc | exact HPO3 | left; cbn; left; lia | right; lia]).
        assert (Wf3 : mem_wr R_segs M3 (sp - 192) 192) by (destruct HPO3 as [_ HW]; apply HW; exact Wfc).
        eapply (sort_phase_s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R3 [] M3 MD T Hh HP3 LT0 LT1 LA7 Hmx1 SOK Wf3 Wp3 Hlens3 Hoffs Hwork3).
        intros R4 M4 HP4 LT0' LT1' LA7' HPO4 Wf4 Wp4 Hlens4 Hwork4.
        destruct HPO4 as [HA4 HW4]. unfold ZSEP in Hprom, Hpb.
        assert (HAG4 : framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) M4) by (eapply acc2; [exact HAG3 | exact (conj HA4 HW4) | left; cbn; left; lia | left; cbn; right; right; right; left; lia]).
        assert (Htab4 : mem_arr 4 R_segs M4 (p + 1384) 1444 cf) by (eapply mem_arr_magree; [exact HA4 | exact Htab3 | lia | lia]).
        assert (Hnext4 : mem_u64 R_segs M4 (p + 160) (p + 1384 + 4 * nx)) by (eapply mem_u64_magree; [exact HA4 | exact Hnext3 | lia | rewrite two64_eq; lia | lia | lia]).
        assert (Hbits4 : mem_u32 R_segs M4 pb bits) by (eapply mem_u32_magree; [exact HA4 | exact Hbits3 | lia | rewrite two64_eq; lia | lia | lia]).
        assert (Hlb4 : mem_arr 2 R_segs M4 67170 31 (arr_get lbase_a)) by (eapply mem_arr_magree; [exact HA4 | exact Hlb3 | lia | lia]).
        assert (Hle4 : mem_arr 2 R_segs M4 67232 31 (arr_get lext_a)) by (eapply mem_arr_magree; [exact HA4 | exact Hle3 | lia | lia]).
        assert (Hdb4 : mem_arr 2 R_segs M4 67294 32 (arr_get dbase_a)) by (eapply mem_arr_magree; [exact HA4 | exact Hdb3 | lia | lia]).
        assert (Hde4 : mem_arr 2 R_segs M4 67358 32 (arr_get dext_a)) by (eapply mem_arr_magree; [exact HA4 | exact Hde3 | lia | lia]).
        assert (Hcnt4 : mem_arr 2 R_segs M4 (sp + -136) 16 (arr_get (cntA lf lens_ofs codes))).
        { eapply mem_arr_magree; [exact HA4 | | lia | lia]. destruct HPO3 as [HA3 _]. eapply mem_arr_magree; [exact HA3 | exact Hcntc | lia | lia]. }
        clear HA4 HW4 Htab3 Hnext3 Hbits3 Hlb3 Hle3 Hdb3 Hde3 Hwork3 Hlens3 Wp3 Htabl0 Hnext1 Hbcell0 Hlb1 Hle1 Hdb1 Hde1 Hwork1 Hlens1 Wpc.
        eapply (switch_s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R4 [] M4 MD T Hh HP4 LT0' LT1' LA7' Hmx1 Wf4 Wp4 Hlens4 Hwork4 Hcnt4 Htab4 Hnext4 Hlb4 Hle4 Hdb4 Hde4).
        *
          intros R5 M5 HC5 HS5 HPO5 HM5 HSM5 HSP5 Hne.
          assert (HAG5 : framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) M5) by (eapply acc2; [exact HAG4 | exact HPO5 | left; cbn; left; lia | right; lia]).
          assert (Hbits5 : mem_u32 R_segs M5 pb bits).
          { destruct HPO5 as [HA5 _]. eapply mem_u32_magree; [exact HA5 | exact Hbits4 | lia | rewrite two64_eq; lia | lia | lia]. }
          specialize (LOOPOK Hne).
          assert (PHc : 0 <= codes <= 288) by lia.
          assert (PHl : forall s, 0 <= s < codes -> 0 <= arr_get (lensA lf) (lens_ofs + s) <= 15).
          { intros s Hs. rewrite lensA_get. pose proof (Rlf (lens_ofs + s) ltac:(lia)). pose proof (Hl15 s Hs). lia. }
          assert (PHt : ty = CODES -> codes <= 19 /\ bits = 7 /\ forall s, 0 <= s < codes -> arr_get (lensA lf) (lens_ofs + s) <= 7).
          { intros E. destruct (HtyC E) as (A & B & D). repeat split; try assumption. intros s Hs. rewrite lensA_get. apply D. exact Hs. }
          assert (PHb : 1 <= bits <= 15) by lia.
          assert (PHI1 : forall st, PIc_mod.PIc ty lf lens_ofs codes nx bits st -> ty = CODES -> tr_w st < it_match ty).
          { intros st0 HPI Ety. unfold tr_w. assert (EM : it_match ty = 20) by (rewrite Ety; reflexivity). rewrite EM. exact (PIc_mod.pic_w ty lf lens_ofs codes nx bits PHc PHl PHt PHb Hmx1 Hrj st0 HPI Ety). }
          eapply (main_loop_s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C (PIc_mod.PIc ty lf lens_ofs codes nx bits) PHI1
                    (PIc_mod.pic_step ty lf lens_ofs codes nx bits PHc PHl PHt PHb Hmx1 Hrj)
                    (Z.to_nat (codes + 1)) _ R5 [] M5 M5 MD T LOOPOK Hmx1
                    (PIc_mod.pic_init ty lf lens_ofs codes nx bits cf wf PHc PHl PHt PHb Hmx1 Hrj Hne)
                    Hh HC5 HS5 HM5 HSM5 HSP5 (mpostL_refl _ _ _)).
          --
             intros st' R6 M6 HL HC6 HS6 L8 HPL6 HM6 HSM6 HSP6 Hfit B1 B2 B3.
             assert (HAG6 : framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) M6) by (eapply accL; [exact HAG5 | exact HPL6]).
             eapply (break_tail_s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C st' R6 [] M6 MD T Hh HC6 HS6 L8 HM6 HSM6 HSP6 B1 B2 B3 Hfit).
             intros R7 M7 HP7 LA6 HPT7 Htbl7 Hnext7 Hbits7 Wf7 Wp7 Hlens7 Hwork7.
             assert (HAG7 : framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) M7) by (eapply accT; [exact HAG6 | exact HPT7]).
             unfold pregs3 in HP7. dand HP7 as (P1 & P2 & P3).
             pose proof HSP6 as HSP6'. unfold spure in HSP6'. dand HSP6' as (WK6 & _ & _ & _ & _ & _ & HTR6 & _ & _).
             eapply (FIN R7 M7 0 _ (t_work st') (nx + t_used st') (rootA lf lens_ofs codes bits)); try eassumption.
             ++ rewrite res_phases. destruct (Z.eqb_spec (mxA lf lens_ofs codes) 0); [lia|]. rewrite Hrj, Hne.
                rewrite it_loop_is_n. replace (codes + 1) with (Z.of_nat (Z.to_nat (codes + 1))) by lia. rewrite HL. reflexivity.
             ++ eapply slots_fps; [exact C | exact HSL1 | exact HAG7].
             ++ eapply fin_fp; [exact C | exact HPO1 | exact HAG7].
             ++ rewrite WK6. exact Hwork7.
             ++ apply tbl_brk_range. exact HTR6.
             ++ rewrite WK6. apply (work1_range _ _ _ _ _ _ _ _ _ _ _ _ _ C).
          --
             intros st' R6 M6 HL HC6 LA6 HPL6 HM6 HSM6 HW6 HTR6.
             assert (HAG6 : framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) M6) by (eapply accL; [exact HAG5 | exact HPL6]).
             unfold cregsN in HC6. dand HC6 as (HP6 & _). unfold pregs6 in HP6. dand HP6 as (P1 & P2 & P3 & _).
             unfold cmem in HM6. dand HM6 as (Wf6 & Wp6 & Hlens6 & Hwork6 & Hnext6 & _).
             unfold smem in HSM6. dand HSM6 as (Hcnt6 & Htbl6).
             assert (Hbits6 : mem_u32 R_segs M6 pb bits).
             { destruct HPL6 as [HA6 _]. eapply mem_u32_magreeL; [exact HA6 | exact Hbits5 | lia | rewrite two64_eq; lia | cbn; lia]. }
             eapply (FIN R6 M6 1 (t_tbl st') (t_work st') nx bits); try eassumption.
             ++ rewrite res_phases. destruct (Z.eqb_spec (mxA lf lens_ofs codes) 0); [lia|]. rewrite Hrj, Hne.
                rewrite it_loop_is_n. replace (codes + 1) with (Z.of_nat (Z.to_nat (codes + 1))) by lia. rewrite HL. reflexivity.
             ++ eapply slots_fps; [exact C | exact HSL1 | exact HAG6].
             ++ eapply fin_fp; [exact C | exact HPO1 | exact HAG6].
             ++ rewrite HW6. exact Hwork6.
             ++ rewrite HW6. apply (work1_range _ _ _ _ _ _ _ _ _ _ _ _ _ C).
        *
          intros R5 M5 HP5 LA6 HPO5 Hne.
          assert (HAG5 : framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) M5) by (eapply acc2; [exact HAG4 | exact HPO5 | left; cbn; left; lia | right; lia]).
          destruct HPO5 as [HA5 HW5].
          unfold pregs6 in HP5. dand HP5 as (P1 & P2 & P3 & _).
          eapply (FIN R5 M5 1 (tblA cf) (work1A lf lens_ofs codes wf) nx bits); try eassumption.
          -- rewrite res_phases. destruct (Z.eqb_spec (mxA lf lens_ofs codes) 0); [lia|]. rewrite Hrj, Hne. reflexivity.
          -- eapply slots_fps; [exact C | exact HSL1 | exact HAG5].
          -- eapply fin_fp; [exact C | exact HPO1 | exact HAG5].
          -- eapply mem_arr_magree; [exact HA5 | exact Hlens4 | lia | lia].
          -- eapply mem_arr_magree; [exact HA5 | | lia | lia]. eapply mem_arr_ext; [exact Htab4|]. intros; symmetry; apply tblA_get.
          -- eapply mem_arr_magree; [exact HA5 | exact Hwork4 | lia | lia].
          -- apply (tblA_range _ _ _ _ _ _ _ _ _ _ _ _ _ C).
          -- apply (work1_range _ _ _ _ _ _ _ _ _ _ _ _ _ C).
          -- eapply mem_u64_magree; [exact HA5 | exact Hnext4 | lia | rewrite two64_eq; lia | lia | lia].
          -- eapply mem_u32_magree; [exact HA5 | exact Hbits4 | lia | rewrite two64_eq; lia | lia | lia].
    -
      unfold Kmax0. intros R' HP' Hmx0.
      eapply (max0_s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R' [] Mc MD T Hh HP' Hmx0 Wpc Htabl0 Hnext1 Wfc Hlens1 Hwork1).
      intros R2 M2 HP2 LA6 HPT2 Htbl2 Hnext2 Hbits2 Wf2 Wp2 Hlens2 Hwork2.
      assert (HAG2 : framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) M2) by (eapply accT; [exact HAGc | exact HPT2]).
      unfold pregs3 in HP2. dand HP2 as (P1 & P2 & P3).
      eapply (FIN R2 M2 0 _ (workA wf) (nx + 2) 1); try eassumption.
      + rewrite res_phases. rewrite Hmx0. reflexivity.
      + eapply slots_fps; [exact C | exact HSL1 | exact HAG2].
      + eapply fin_fp; [exact C | exact HPO1 | exact HAG2].
      + eapply mem_arr_ext; [exact Hwork2|]. intros; symmetry; apply workA_get.
      + apply (tbl_max0_range _ _ _ _ _ _ _ _ _ _ _ _ _ C).
      + apply (workA_range _ _ _ _ _ _ _ _ _ _ _ _ _ C). }
  pose proof PF1 as PF1'. unfold pf in PF1'. dand PF1' as (Wp1 & HlensM1 & HtabM1 & HworkM1 & HnextM1 & HbitsM1 & _).
  destruct (Z.eq_dec codes 0) as [Cz|Cnz].
  -
    assert (HcntA : mem_arr 2 R_segs M1 (sp + -136) 16 (arr_get (cntA lf lens_ofs codes))).
    { eapply mem_arr_ext; [exact Hcnt0|]. intros; symmetry; apply cA_zero; exact Cz. }
    destruct (KC M1 PF1 Wf1 HcntA HAGS1) as [_ KM0].
    eapply (count_phase0_s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R1 [] M1 MD T _ Cz Hh PR1 eq_refl Hcnt0 HbitsM1 KM0).
  - eapply (count_phase_s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R1 [] M1 MD T ltac:(lia) Hh PR1 Wf1 HlensM1 Hcnt0).
    intros R2 M2 PR2 QA7 HPO2 Wf2 Hlens2 Hcnt2.
    pose proof (pf_frame _ _ _ _ _ _ _ _ _ _ _ _ _ C M1 M2 _ _ PF1 HPO2 ltac:(lia)) as PF2.
    assert (HAG2 : framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) M2) by (eapply acc2; [exact HAGS1 | exact HPO2 | left; cbn; left; lia | right; lia]).
    destruct (KC M2 PF2 Wf2 Hcnt2 HAG2) as [KL KM0].
    pose proof PF2 as PF2'. unfold pf in PF2'. dand PF2' as (_ & _ & _ & _ & _ & HbitsM2 & _).
    eapply (max_entry_s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R2 [] M2 MD T _ Hh PR2 QA7 Hcnt2 HbitsM2).
    + unfold Kmax. intros R3 HP3 LA7 LT0 LT2 Hmx2.
      eapply (rootmin_s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R3 [] M2 MD T Hh HP3 LA7 LT0 LT2 Hmx2 Hcnt2 KL).
    + unfold Klow. intros R3 HP3 LA7 HZ.
      eapply (maxlow_s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R3 [] M2 MD T Hh HP3 LA7 HZ Hcnt2 KL KM0).
Qed.
End FXG.
End S_It7.


