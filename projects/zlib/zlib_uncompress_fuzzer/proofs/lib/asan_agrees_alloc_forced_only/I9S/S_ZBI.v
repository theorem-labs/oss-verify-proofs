(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.I9S Require SBase S_Entry. (* 1.4: was S_ZA, of which nothing is used; this keeps S_ZA's own Requires and frees inflate_table from S_ZA / S_ZAw (inflateInit_) *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only Require Frame Hoare.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only Require RefMemcpyLib FuzzMem S9MemcpyBase S9Memcpy S9AdlerBase S9AdlerIface S9Adler.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only Require S9LibStmt.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Inftrees InftreesCoverage ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.I9S Require Base.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require ZTac ZMem ZCall ZCallL ZArr ZArr4 IDefs ISpecs ITac.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.I9S Require S_It3.

Module S_It2.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel.ItableModel.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.I9S.Base.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ZTac OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ZArr OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ZArr4 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.IDefs OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ISpecs OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ITac.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.I9S.S_It3.S_It0 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.I9S.S_It3.S_It1.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

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
    realizes R_segs (zcfg R_segs 97368 (zupd R' []) M MD) T.

Definition Koffs (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', PR R' [] -> zget_l R' [] kT0 = mx -> zget_l R' [] kT1 = mn -> zget_l R' [] kA7 = rt ->
    zget_l R' [] kT4 = cA 1 -> zget_l R' [] kT5 = cA 2 -> zget_l R' [] kT6 = cA 3 -> zget_l R' [] kS0 = cA 4 ->
    zget_l R' [] kS1 = cA 5 -> zget_l R' [] kS2 = cA 6 -> zget_l R' [] kS3 = cA 7 -> zget_l R' [] kS4 = cA 8 ->
    zget_l R' [] kS5 = cA 9 -> zget_l R' [] kS6 = cA 10 -> zget_l R' [] kS7 = cA 11 -> zget_l R' [] kS8 = cA 12 ->
    zget_l R' [] kS9 = cA 13 -> zget_l R' [] kS10 = cA 14 ->
    1 <= mx -> itm_reject ty mx (it_left_check cntAr) = false ->
    realizes R_segs (zcfg R_segs 96448 (zupd R' []) M MD) T.

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
     realizes R_segs (zcfg R_segs 96560 (zupd R' []) M' MD) T) ->
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
     realizes R_segs (zcfg R_segs 96644 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 96600 (zupd Rb l) M MD) T.
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
    realizes R_segs (zcfg R_segs 96588 (zupd RJ []) MJ MD) T).
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
     realizes R_segs (zcfg R_segs 96644 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 96560 (zupd Rb l) M MD) T.
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

Module S_It4.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel.ItableModel.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.I9S.Base.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ZTac OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ZArr OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ZArr4 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.IDefs OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ISpecs OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ITac.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.I9S.S_It3.S_It0 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.I9S.S_It3.S_It1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.I9S.S_It3.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

Section S7IT4.
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 192 zc.

#[local] Abbreviation cA := (arr_get (cntA lf lens_ofs codes)).
#[local] Abbreviation cntAr := (cntA lf lens_ofs codes).
#[local] Abbreviation mx := (mxA lf lens_ofs codes).
#[local] Abbreviation mn := (mnA lf lens_ofs codes).
#[local] Abbreviation rt := (rootA lf lens_ofs codes bits).
#[local] Abbreviation work1Ar := (work1A lf lens_ofs codes wf).
#[local] Abbreviation X := (itm_ctx ty (lensA lf) lens_ofs nx (rootA lf lens_ofs codes bits) (mxA lf lens_ofs codes)).
#[local] Abbreviation CR := (cregsN ty lf lens_ofs codes bits p pb sp vgp vtp).
#[local] Abbreviation CRB := (cregsB ty lf lens_ofs codes bits p pb sp vgp vtp).
#[local] Abbreviation SR := (sregs p).
#[local] Abbreviation CM := (cmem ty lf lens_ofs codes nx wf p sp).
#[local] Abbreviation SM := (smem p sp).
#[local] Abbreviation SP := (spure lf lens_ofs codes nx bits wf).

Definition uregs (st : ItSt) (R : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l R l kT6 = tr_sym st /\ zget_l R l kT1 = tr_len X st /\
  zget_l R l kS1 = tr_huff st /\ zget_l R l kS0 = p + 1384 + 4 * t_next st /\ zget_l R l kA2 = 2 ^ t_curr st /\
  zget_l R l kS8 = tr_low X st.
Ltac open_uregs H :=
  unfold uregs in H;
  let a := fresh "LT6" in let b := fresh "LT1" in let d := fresh "LS1" in
  let e := fresh "LS0" in let f := fresh "LT2" in let g := fresh "LS8" in
  dand H as (a & b & d & e & f & g).
Ltac close_uregs := unfold uregs; split_conj; zreg.
Ltac kauto4 := first
  [ assumption
  | lazymatch goal with
    | |- uregs _ _ _ => close_uregs
    | |- _ => kauto
    end ].
Ltac xaddr := pose proof (xaddr_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C) as (XS1 & XS2 & XA1 & XA2 & XB1 & XB2 & XN).

Lemma curr_loop_s : forall m curr lft n (cnt : arr) st Rb l M MD T,
  mx - (curr + rt) <= Z.of_nat m -> Z.of_nat m < n -> 1 <= mx ->
  1 <= curr -> curr + rt < mx -> 0 < lft <= 2 ^ curr ->
  (forall j, 0 <= j < 16 -> 0 <= arr_get cnt j < 65536) ->
  m_halted MD = None -> CR Rb l -> uregs st Rb l -> zget_l Rb l kT5 = t_used st -> zget_l Rb l kS9 = rt ->
  zget_l Rb l kS10 = curr + rt -> zget_l Rb l kA6 = lft -> zget_l Rb l kS7 = mx - rt ->
  mem_arr 2 R_segs M (sp + -136) 16 (arr_get cnt) ->
  (forall R', CR R' [] -> uregs st R' [] -> zget_l R' [] kT5 = t_used st -> zget_l R' [] kS9 = rt ->
     zget_l R' [] kS7 = fst (loopZ n (curr_body cnt rt mx) (curr, lft)) ->
     zget_l R' [] kA6 = 2 ^ fst (loopZ n (curr_body cnt rt mx) (curr, lft)) ->
     realizes R_segs (zcfg R_segs 97208 (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs 97160 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf.
  induction m as [|m IH]; intros curr lft n cnt st Rb l M MD T Hm Hn Hmx Hc1 Hcm Hl HCR Hh HC HUr LT5 LS9 LS10 LA6 LS7 Hcnt K.
  { exfalso. lia. }
  pose proof C as C'. open_itc C'. open_cregs HC. open_uregs HUr. zkeys. clear Hprom HtyC HtyD Hpb Hlf Hcf Hwf Hlens15.
  pose proof (mx15 lf lens_ofs codes) as MXR. pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C ltac:(lia)) as (RT1 & RT2 & RT3).
  assert (P14 : 2 ^ curr <= 2 ^ 13) by (apply Z.pow_le_mono_r; lia). change (2 ^ 13) with 8192 in P14.
  pose proof (HCR (curr + rt) ltac:(lia)) as HCc.
  zrebase.
  zstep Rfd. zstep Rfd. zsetreg (2 * (curr + rt)) ltac:(symmetry; apply zext32_x2; lia).
  zstep Rfd.
  tstep Rfd.
  zstep Rfd. zsetreg (lft - arr_get cnt (curr + rt)) ltac:(symmetry; apply swrap32_small; lia).
  destruct (Z_lt_le_dec 0 (lft - arr_get cnt (curr + rt))) as [GT|LE].
  - zbr Rfd false.
    zstep Rfd. zsetreg (curr + rt + 1) ltac:(symmetry; apply swrap32_small; lia).
    zstep Rfd. zsetreg (2 * (lft - arr_get cnt (curr + rt))) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
    destruct (Z_lt_le_dec (curr + rt + 1) mx) as [MORE|DONE].
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
        eapply (IH (curr + 1) (2 * (lft - arr_get cnt (curr + rt))) (n - 1) cnt st Rx [] M MD T) end.
      all: try kauto4.
      all: try lia.
      * rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. lia.
      * intros R' HC' HU' L5 L9 L7 L6. eapply K; try eassumption.
        all: rewrite curr_more by lia; rewrite Z.shiftl_mul_pow2, Z.pow_1_r by lia;
             replace ((lft - arr_get cnt (curr + rt)) * 2) with (2 * (lft - arr_get cnt (curr + rt))) by lia; assumption.
    + zbr Rfd false.
      zstep Rfd.
      zstep Rfd. zsetreg (2 ^ (mx - rt)) ltac:(symmetry; apply sllw_1; lia).
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
      all: try kauto4.
      * zregv. rewrite curr_more by lia. rewrite curr_stop_ge by lia. cbn [fst]. lia.
      * zregv. rewrite curr_more by lia. rewrite curr_stop_ge by lia. cbn [fst]. f_equal. lia.
  - zbr Rfd true.
    zstep Rfd. zsetreg curr ltac:(rewrite swrap32_small by lia; lia).
    zstep Rfd. zsetreg (2 ^ curr) ltac:(symmetry; apply sllw_1; lia).
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
    all: try kauto4.
    * zregv. rewrite curr_stop_le by lia. reflexivity.
    * zregv. rewrite curr_stop_le by lia. reflexivity.
Qed.

Lemma ne_facts : (isL ty = 0 \/ isL ty = 1) /\ (isD ty = 0 \/ isD ty = 1) /\ isL ty + isD ty <= 1 /\
  (forall u, it_not_enough ty u = (if isL ty =? 1 then 852 <? u else if isD ty =? 1 then 592 <? u else false)).
Proof using C zc ret sp pb p wf cf bits nx codes lens_ofs lf. destruct ty; cbn; repeat split; try lia_std; intros; reflexivity. Qed.
Lemma lxor1_b2z : forall b, Z.lxor (Z.b2z b) 1 = Z.b2z (negb b).
Proof using. destruct b; reflexivity. Qed.
Lemma land1_b2z : forall b, Z.land 1 (Z.b2z b) = Z.b2z b.
Proof using. destruct b; reflexivity. Qed.
Lemma lowS_small : forall z, 0 <= z < 4294967295 -> lowS z = z.
Proof using. intros z Hz. unfold lowS. destruct (Z.eqb_spec z 4294967295); [lia_std | reflexivity]. Qed.

Definition Kbody3 (st : ItSt) (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R' M', CR R' [] -> SR (tr_st3 X st) R' [] ->
     mpost R_segs M M' (p + 1384) (p + 7160) 0 0 -> CM M' -> SM (tr_st3 X st) M' ->
     tr_sub X st = true -> it_not_enough ty (tr_used X st) = false ->
     1 <= tr_curr X st <= 15 -> 0 <= tr_low X st < 32768 -> tr_drop X st = rt -> t_next st <= tr_next st ->
     realizes R_segs (zcfg R_segs 96852 (zupd R' []) M' MD) T.
Definition Kfail (st : ItSt) (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', CR R' [] -> zget_l R' [] kA6 = 1 -> tr_sub X st = true -> it_not_enough ty (tr_used X st) = true ->
     realizes R_segs (zcfg R_segs 97368 (zupd R' []) M MD) T.

Lemma link_s : forall st Rb l M MD T,
  m_halted MD = None -> CR Rb l -> uregs st Rb l -> zget_l Rb l kS9 = rt -> zget_l Rb l kS7 = tr_curr X st ->
  zget_l Rb l kT5 = tr_used X st ->
  CM M -> SM (tr_st1 X st) M -> SP st -> it_trip_ok X 288 320 1444 st = true ->
  tr_brk X st = false -> tr_sub X st = true -> it_not_enough ty (tr_used X st) = false -> 1 <= mx ->
  0 <= tr_low X st < 32768 -> tr_drop X st = rt ->
  Kbody3 st M MD T ->
  realizes R_segs (zcfg R_segs 97256 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HU LS9 LS7 LT5 HM HSM HP TOK Hbrk Hsub Hne Hmx HLOW HDR K3.
  pose proof C as C'. open_itc C'. open_cregs HC. open_uregs HU. open_cmem HM. open_smem HSM. open_spure HP. zkeys. xaddr.
  cbn [t_count t_tbl tr_st1] in Hcnt, Htbl.
  trip_facts TOK. clear Flook Fwm LOWR DROPR Hprom HtyC HtyD Hcf Hwf Hlens15.
  pose proof (mx15 lf lens_ofs codes) as MXR. pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C Hmx) as (RT1 & RT2 & RT3).
  assert (HST3 : it_step X st = ItCont (tr_st3 X st)).
  { rewrite it_step_eq. rewrite Hbrk, Hsub. cbn [x_ty itm_ctx]. rewrite Hne. reflexivity. }
  unbox Fcont. dand (Fcont (tr_st3 X st) HST3) as (Flow3 & Fcurr3 & Fnext3).
  { right. cbn [t_next tr_st3]. unfold tr_next, tr_fill. rewrite shl32_1 by lia. pose proof (pow2_le15 (t_curr st) ltac:(lia)). lia. }
  cbn [t_low t_curr t_next tr_st3] in Flow3, Fcurr3, Fnext3. clear Fcont HST3.
  assert (ENX : tr_next st = t_next st + 2 ^ t_curr st) by (unfold tr_next, tr_fill; rewrite shl32_1 by lia; reflexivity).
  pose proof (pow2_le15 (t_curr st) ltac:(lia)) as PC. pose proof (pow2_le15 (tr_curr X st) ltac:(lia)) as PC3.
  assert (Hroom3 : t_next st < 1444).
  { pose proof (pow2_le15 (t_len st - t_drop st) ltac:(lia)).
    assert (2 ^ (t_len st - t_drop st) <= 2 ^ t_curr st) by (apply Z.pow_le_mono_r; lia).
    assert (0 <= Z.shiftr (t_huff st) (t_drop st)) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]). lia. }
  destruct (arr4_hole R_segs M (p + 1384) 1444 (arr_get (tr_tbl1 X st)) (nx + tr_low X st) Htbl ltac:(lia)) as [HT1 HT2]. clear Htbl.
  pose proof (mpost_stable R_segs M (p + 1384) (p + 7160) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X (p + 1384) (p + 7160) 0 0) M) by (apply mpost_refl).
  zrebase.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zsetreg (4 * 2 ^ t_curr st) ltac:(symmetry; apply zext32_x4; lia).
  zstep Rfd. zsetreg (p + 1384 + 4 * tr_next st) ltac:(rewrite ENX; lia).
  zstep Rfd. zsetreg (4 * tr_low X st) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd.
  zstep Rfd. zsetreg (4 * (tr_next st - nx)) ltac:(rewrite swrap32_small by lia; lia).
  zstep Rfd. zsetreg (tr_next st - nx) ltac:(rewrite srli_small by lia; change (2 ^ 2) with 4; rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  match goal with
  | Ho : mem_u8 _ ?Mc _ (tr_curr X st), Hb : mem_u8 _ _ _ rt, Hv : mem_u16 _ _ _ (tr_next st - nx) |- _ =>
    pose proof (entry_write Mc (p + 1384) 1444 (arr_get (tr_tbl1 X st)) (nx + tr_low X st) _ _ _ _ _ _ HT1 HT2 Ho Hb Hv
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Htbl;
    clear Ho Hb Hv HT1 HT2
  end.
  apply mem_arr_arr_set in Htbl; [| rewrite it_fill_len_tr; lia].
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zsetreg (2 ^ tr_curr X st) ltac:(symmetry; apply sllw_1; lia).
  zstep Rfd. zsetreg (tr_low X st) ltac:(rewrite swrap32_small by lia; lia).
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K3 Rx Mx) end.
  all: try kauto4.
  all: lazymatch goal with
       | |- sregs _ _ _ _ => unfold sregs; cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st3]; rewrite HDR;
                             rewrite (lowS_small (tr_low X st)) by lia; split_conj; zreg
       | |- cmem _ _ _ _ _ _ _ _ _ => close_cmem
       | |- smem _ _ _ _ => unfold smem; cbn [t_count t_tbl tr_st3]; split; [exact Hcnt|]; unfold tr_tbl2; cbn [x_table x_root itm_ctx]; exact Htbl
       | |- _ => lia
       end.
Qed.

Lemma enough_s : forall st Rb l M MD T,
  m_halted MD = None -> CR Rb l -> uregs st Rb l -> zget_l Rb l kS9 = rt -> zget_l Rb l kT5 = t_used st ->
  zget_l Rb l kS7 = tr_curr X st -> zget_l Rb l kA6 = 2 ^ tr_curr X st ->
  CM M -> SM (tr_st1 X st) M -> SP st -> it_trip_ok X 288 320 1444 st = true ->
  tr_brk X st = false -> tr_sub X st = true -> 1 <= mx ->
  0 <= tr_low X st < 32768 -> tr_drop X st = rt -> 1 <= tr_curr X st <= 15 ->
  Kbody3 st M MD T -> Kfail st M MD T ->
  realizes R_segs (zcfg R_segs 97208 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HU LS9 LT5 LS7 LA6 HM HSM HP TOK Hbrk Hsub Hmx HLOW HDR HCU K3 KF.
  pose proof C as C'. open_itc C'. open_cmem HM. open_spure HP. zkeys.
  trip_facts TOK. clear Flook Fwm Fcont Hprom HtyC HtyD Hcf Hwf Hlens15.
  pose proof (pow2_le15 (tr_curr X st) ltac:(lia)) as PC3.
  assert (EU : tr_used X st = t_used st + 2 ^ tr_curr X st).
  { unfold tr_used. rewrite Z.shiftl_1_l. apply wrap32_small. lia. }
  pose proof ne_facts as (IL & ID & ILD & NE').
  assert (JD : forall RJ, CR RJ [] -> uregs st RJ [] -> zget_l RJ [] kS9 = rt -> zget_l RJ [] kT5 = tr_used X st ->
            zget_l RJ [] kS7 = tr_curr X st -> zget_l RJ [] kA6 = 1 -> (isL ty = 1 -> tr_used X st < 853) ->
            realizes R_segs (zcfg R_segs 97236 (zupd RJ []) M MD) T).
  { intros RJ HCJ HUJ J9 J5 J7 J6 HL. open_cregs HCJ. open_uregs HUJ. zkeys. zrebase.
    zstep Rfd. zsetreg (Z.b2z (tr_used X st <? 593)) ltac:(rewrite (Z.mod_small (tr_used X st)) by lia; reflexivity).
    zstep Rfd. zsetreg (Z.b2z (593 <=? tr_used X st)) ltac:(rewrite lxor1_b2z, <- Z.leb_antisym; reflexivity).
    zstep Rfd.
    destruct ID as [ID0|ID1].
    - zstep Rfd. zsetreg 0 ltac:(rewrite ID0; symmetry; apply Z.land_0_l).
      zbr Rfd false.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (link_s st Rx [] M MD T) end.
      all: try kauto4. all: try assumption. all: try lia.
      + unfold cmem; split_conj; assumption.
      + unfold spure; split_conj; assumption.
      + rewrite NE'. destruct (Z.eqb_spec (isL ty) 1); [apply Z.ltb_ge; lia|]. rewrite ID0. reflexivity.
    - zstep Rfd. zsetreg (Z.b2z (593 <=? tr_used X st)) ltac:(rewrite ID1; symmetry; apply land1_b2z).
      destruct (Z.leb_spec 593 (tr_used X st)) as [GE|LT].
      + zbr Rfd true.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
        all: try kauto4. rewrite NE'. destruct (Z.eqb_spec (isL ty) 1); [destruct IL; lia|]. rewrite ID1. cbn [Z.eqb]. apply Z.ltb_lt. lia.
      + zbr Rfd false.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (link_s st Rx [] M MD T) end.
        all: try kauto4. all: try assumption. all: try lia.
        * unfold cmem; split_conj; assumption.
        * unfold spure; split_conj; assumption.
        * rewrite NE'. destruct (Z.eqb_spec (isL ty) 1); [apply Z.ltb_ge; lia|]. rewrite ID1. cbn [Z.eqb]. apply Z.ltb_ge. lia. }
  open_cregs HC. open_uregs HU. zkeys. zrebase.
  zstep Rfd. zsetreg (tr_used X st) ltac:(rewrite EU, swrap32_small by lia; lia).
  zstep Rfd. zsetreg (Z.b2z (tr_used X st <? 853)) ltac:(rewrite (Z.mod_small (tr_used X st)) by lia; reflexivity).
  zstep Rfd. zsetreg (Z.b2z (853 <=? tr_used X st)) ltac:(rewrite lxor1_b2z, <- Z.leb_antisym; reflexivity).
  zstep Rfd.
  destruct IL as [IL0|IL1].
  - zstep Rfd. zsetreg 0 ltac:(rewrite IL0; symmetry; apply Z.land_0_l).
    zstep Rfd.
    zbr Rfd false.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (JD Rx) end.
    all: try kauto4. intros; lia.
  - zstep Rfd. zsetreg (Z.b2z (853 <=? tr_used X st)) ltac:(rewrite IL1; symmetry; apply land1_b2z).
    zstep Rfd.
    destruct (Z.leb_spec 853 (tr_used X st)) as [GE|LT].
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
      all: try kauto4. rewrite NE', IL1. cbn [Z.eqb]. apply Z.ltb_lt. lia.
    + zbr Rfd false.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (JD Rx) end.
      all: try kauto4. intros; lia.
Qed.

Ltac zbr_by bv tac :=
  let pc := zpc in Rfd pc ltac:(fun F E D => eapply (zu_branch_b bv); [exact F | exact E | exact D | zhalted | znorm; tac | ]; cbv iota; znorm).

Lemma tr_count_range : forall st, (forall j, 0 <= j < 16 -> 0 <= arr_get (t_count st) j < 65536) ->
  forall j, 0 <= j < 16 -> 0 <= arr_get (tr_count st) j < 65536.
Proof using.
  intros st H j Hj. unfold tr_count. rewrite arr_get_set. destruct (_ && _); [|apply H; exact Hj].
  pose proof (wrap16_range (arr_get (t_count st) (t_len st) - 1)) as W. change (2 ^ 16) with 65536 in W. unfold tr_c. lia_std.
Qed.

Lemma currsz_s : forall st Rb l M MD T,
  m_halted MD = None -> CR Rb l -> uregs st Rb l -> zget_l Rb l kS9 = rt -> zget_l Rb l kT5 = t_used st ->
  CM M -> SM (tr_st1 X st) M -> SP st -> it_trip_ok X 288 320 1444 st = true ->
  tr_brk X st = false -> tr_sub X st = true -> 1 <= mx ->
  1 <= tr_len X st <= 15 -> rt < tr_len X st -> 0 <= tr_low X st < 32768 -> tr_drop X st = rt ->
  Kbody3 st M MD T -> Kfail st M MD T ->
  realizes R_segs (zcfg R_segs 97140 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HU LS9 LT5 HM HSM HP TOK Hbrk Hsub Hmx TLR RTL HLOW HDR K3 KF.
  pose proof C as C'. open_itc C'. open_smem HSM. open_spure HP. zkeys.
  cbn [t_count t_tbl tr_st1] in Hcnt, Htbl.
  clear Hprom HtyC HtyD Hcf Hwf Hlens15.
  pose proof (mx15 lf lens_ofs codes) as MXR. pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C Hmx) as (RT1 & RT2 & RT3).
  pose proof (tr_count_range st HCr) as HCr1.
  set (c0 := tr_len X st - rt). assert (Ec0 : c0 = tr_len X st - rt) by reflexivity.
  pose proof (pow2_le15 c0 ltac:(lia)) as PC0.
  assert (ETC : tr_curr X st = fst (loopZ 16 (curr_body (tr_count st) rt mx) (c0, 2 ^ c0))).
  { unfold tr_curr. rewrite HDR. cbn [x_max itm_ctx]. rewrite it_subtable_curr_eq. rewrite (wrap32_small (tr_len X st - rt)) by lia.
    fold c0. rewrite Z.shiftl_1_l, swrap32_id by lia. reflexivity. }
  pose proof (curr_result_range (tr_count st) rt mx 16 c0 (2 ^ c0) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (CR1 & CR2 & CR3).
  rewrite <- ETC in CR1, CR2, CR3.
  open_cregs HC. open_uregs HU. zkeys. zrebase.
  zstep Rfd. zsetreg c0 ltac:(rewrite swrap32_small by lia; lia).
  zstep Rfd. zsetreg (2 ^ c0) ltac:(symmetry; apply sllw_1; lia).
  destruct (Z_lt_le_dec (tr_len X st) mx) as [LT|GE].
  - zbr Rfd false.
    zstep Rfd. zsetreg (mx - rt) ltac:(rewrite swrap32_small by lia; lia).
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
      eapply (curr_loop_s 15%nat c0 (2 ^ c0) 16 (tr_count st) st Rx [] M MD T) end.
    all: try kauto4. all: try lia.
    intros R' HC' HU' L5 L9 L7 L6. rewrite <- ETC in L7, L6. specialize (CR2 ltac:(lia)).
    eapply enough_s; try eassumption; try lia.
    + unfold smem. cbn [t_count t_tbl tr_st1]. split; assumption.
    + unfold spure. split_conj; assumption.
  - zbr Rfd true.
    assert (ETC0 : tr_curr X st = c0) by (apply CR3; lia).
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (enough_s st Rx [] M MD T) end.
    all: try kauto4. all: try (rewrite ETC0; zreg). all: try lia.
    + unfold smem. cbn [t_count t_tbl tr_st1]. split; assumption.
    + unfold spure. split_conj; assumption.
Qed.

Lemma sub_s : forall st Rb l M MD T,
  m_halted MD = None -> CR Rb l -> SR (tr_st1 X st) Rb l ->
  CM M -> SM (tr_st1 X st) M -> SP st -> it_trip_ok X 288 320 1444 st = true ->
  tr_brk X st = false -> 1 <= mx ->
  (forall R', CR R' [] -> SR (tr_st1 X st) R' [] -> tr_sub X st = false ->
     realizes R_segs (zcfg R_segs 96852 (zupd R' []) M MD) T) ->
  Kbody3 st M MD T -> Kfail st M MD T ->
  realizes R_segs (zcfg R_segs 97116 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HS HM HSM HP TOK Hbrk Hmx K1 K3 KF.
  pose proof C as C'. open_itc C'. open_spure HP. zkeys.
  clear Hprom HtyC HtyD Hcf Hwf Hlens15.
  pose proof (mx15 lf lens_ofs codes) as MXR. pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C Hmx) as (RT1 & RT2 & RT3).
  trip_facts TOK. clear Fwm Fcont.
  pose proof (pow2_le15 rt ltac:(lia)) as PRT.
  assert (TLR : 1 <= tr_len X st <= 15).
  { unfold tr_len. cbn [x_max x_lens x_lens_ofs itm_ctx].
    destruct (Z.eqb_spec (tr_c st) 0) as [E0|NE0]; [|cbn [andb]; lia].
    destruct (Z.eqb_spec (t_len st) mx) as [EM|NEM]; cbn [andb negb]; [lia|].
    unbox Flook. dand (Flook E0 NEM) as (W1 & W2 & W3 & W4).
    replace (tr_sym st) with (t_sym st + 1) by (unfold tr_sym; symmetry; apply wrap32_small; lia). exact W4. }
  clear Flook.
  assert (HHF : 0 <= tr_huff st).
  { unfold tr_huff. pose proof (pow2_le15 (t_len st - 1) ltac:(lia)) as PL1.
    pose proof (incr_range (t_huff st) 32 (shl32 1 (t_len st - 1)) ltac:(rewrite shl32_1 by lia; lia)) as IR.
    rewrite <- it_incr_back_eq in IR. fold (tr_incr2 st) in IR. rewrite shl32_1 in IR by lia.
    destruct (Z.eqb_spec (tr_incr2 st) 0); cbn [negb]; [lia|].
    assert (0 <= Z.land (t_huff st) (tr_incr2 st - 1)) by (apply Z.land_nonneg; lia). lia. }
  assert (HLOW : 0 <= tr_low X st < 32768).
  { unfold tr_low. cbn [x_mask itm_ctx]. rewrite itm_used_pow2 by lia.
    split; [apply Z.land_nonneg; lia|]. eapply Z.le_lt_trans; [apply land_le_r; lia | lia]. }
  assert (ELOW : Z.land (tr_huff st) (2 ^ rt - 1) = tr_low X st).
  { unfold tr_low. cbn [x_mask itm_ctx]. rewrite itm_used_pow2 by lia. reflexivity. }
  assert (HDR : tr_drop X st = rt).
  { unfold tr_drop. cbn [x_root itm_ctx]. unbox DROPR. destruct DROPR as [D0|D1]; rewrite D0 || rewrite D1; [reflexivity|].
    destruct (Z.eqb_spec rt 0); lia. }
  assert (J68 : forall RJ, CR RJ [] -> uregs st RJ [] -> zget_l RJ [] kA6 = t_drop st -> zget_l RJ [] kT5 = t_used st ->
            tr_sub X st = true -> realizes R_segs (zcfg R_segs 97128 (zupd RJ []) M MD) T).
  { intros RJ HCJ HUJ JA6 JT5 Hsub.
    assert (RTL : rt < tr_len X st).
    { unfold tr_sub in Hsub. apply andb_prop in Hsub as [H1 _]. cbn [x_root itm_ctx] in H1. apply Z.ltb_lt in H1. exact H1. }
    open_cregs HCJ. open_uregs HUJ. zkeys. zrebase.
    zstep Rfd.
    unbox DROPR. destruct DROPR as [D0|D1].
    - zbr Rfd true.
      eapply currsz_s; try eassumption; try lia. all: try kauto4.
      + unfold spure; split_conj; try assumption. unfold ZSEP. lia.
    - zbr Rfd false.
      zstep Rfd.
      eapply currsz_s; try eassumption; try lia. all: try kauto4.
      + unfold spure; split_conj; try assumption. unfold ZSEP. lia. }
  open_cregs HC. open_sregs HS. cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st1] in LT6, LT1, LA6, LT5, LS1, LS0, LT2, LS7.
  zkeys. zrebase.
  destruct (Z_lt_le_dec rt (tr_len X st)) as [SUB1|NOSUB1].
  - zbr Rfd false.
    zstep Rfd. zsetreg (tr_low X st) ltac:(exact (eq_sym ELOW)).
    unbox LOWR. destruct LOWR as [LM|LSM].
    +
      unfold lowS in LS7. rewrite LM in LS7. cbn in LS7.
      zbr_by false ltac:(cbv beta iota delta [zcond]; rewrite (mod_small_u64 (tr_low X st)) by lia;
                         try change ((-1) mod 18446744073709551616) with 18446744073709551615; apply Z.eqb_neq; lia).
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J68 Rx) end.
      all: try kauto4.
      unfold tr_sub. cbn [x_root x_mask itm_ctx]. rewrite itm_used_pow2 by lia. rewrite ELOW, LM.
      replace (rt <? tr_len X st) with true by (symmetry; apply Z.ltb_lt; lia).
      destruct (Z.eqb_spec (tr_low X st) 4294967295); [lia | reflexivity].
    + rewrite (lowS_small (t_low st)) in LS7 by lia.
      destruct (Z.eq_dec (tr_low X st) (t_low st)) as [EQL|NEL].
      * zbr Rfd true.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K1 Rx) end.
        all: try kauto4.
        -- unfold sregs. cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st1]. rewrite (lowS_small (t_low st)) by lia. split_conj; zreg.
        -- unfold tr_sub. cbn [x_root x_mask itm_ctx]. rewrite itm_used_pow2 by lia. rewrite ELOW, EQL, Z.eqb_refl. cbn [negb]. apply Bool.andb_false_r.
      * zbr Rfd false.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J68 Rx) end.
        all: try kauto4.
        unfold tr_sub. cbn [x_root x_mask itm_ctx]. rewrite itm_used_pow2 by lia. rewrite ELOW.
        replace (rt <? tr_len X st) with true by (symmetry; apply Z.ltb_lt; lia).
        destruct (Z.eqb_spec (tr_low X st) (t_low st)); [lia | reflexivity].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K1 Rx) end.
    all: try kauto4.
    + unfold sregs. cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st1]. split_conj; zreg.
    + unfold tr_sub. cbn [x_root itm_ctx]. replace (rt <? tr_len X st) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
End S7IT4.
End FXG.
End S_It4.

Module S_It5.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel.ItableModel.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.I9S.Base.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ZTac OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ZMem OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ZCall OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ZCallL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ZArr OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ZArr4 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.IDefs OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ISpecs OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ITac.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.I9S.S_It3.S_It0 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.I9S.S_It3.S_It1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.I9S.S_It3 S_It4.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

Section S7IT5.
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 192 zc.

#[local] Abbreviation cntAr := (cntA lf lens_ofs codes).
#[local] Abbreviation mx := (mxA lf lens_ofs codes).
#[local] Abbreviation mn := (mnA lf lens_ofs codes).
#[local] Abbreviation rt := (rootA lf lens_ofs codes bits).
#[local] Abbreviation work1Ar := (work1A lf lens_ofs codes wf).
#[local] Abbreviation X := (itm_ctx ty (lensA lf) lens_ofs nx (rootA lf lens_ofs codes bits) (mxA lf lens_ofs codes)).
#[local] Abbreviation CR := (cregsN ty lf lens_ofs codes bits p pb sp vgp vtp).
#[local] Abbreviation CRB := (cregsB ty lf lens_ofs codes bits p pb sp vgp vtp).
#[local] Abbreviation SR := (sregs p).
#[local] Abbreviation CM := (cmem ty lf lens_ofs codes nx wf p sp).
#[local] Abbreviation SM := (smem p sp).
#[local] Abbreviation SP := (spure lf lens_ofs codes nx bits wf).

Definition rsL : list (Z * Z) := [(sp + -136, 32); (p + 1384, 5776)].

Ltac xaddr := pose proof (xaddr_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C) as (XS1 & XS2 & XA1 & XA2 & XB1 & XB2 & XN).

Lemma cmem_mpost : forall M M' lo hi,
  CM M -> mpost R_segs M M' lo hi 0 0 ->
  ((lo = p + 1384 /\ hi = p + 7160) \/ (lo = sp + -136 /\ hi = sp + -104)) -> CM M'.
Proof using C zc ret pb cf bits.
  intros M M' lo hi HM [HA HW] Hr. pose proof C as C'. open_itc C'. xaddr. unfold ZSEP in *. open_cmem HM.
  unfold cmem. split_conj.
  - apply HW. exact Wf.
  - apply HW. exact Wp.
  - eapply mem_arr_magree; [exact HA | exact Hlens | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hwork | lia_std | lia_std].
  - eapply mem_u64_magree; [exact HA | exact Hnext | lia_std | rewrite two64_eq; lia_std | lia_std | lia_std].
  - eapply mem_u64_magree; [exact HA | exact HslD | lia_std | rewrite two64_eq; lia_std | lia_std | lia_std].
  - eapply mem_u64_magree; [exact HA | exact HslL | lia_std | rewrite two64_eq; lia_std | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hext | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hbase | lia_std | lia_std].
Qed.

Lemma cnt_mpost : forall M M' f, mem_arr 2 R_segs M (sp + -136) 16 f -> mpost R_segs M M' (p + 1384) (p + 7160) 0 0 ->
  mem_arr 2 R_segs M' (sp + -136) 16 f.
Proof using C zc ret pb wf cf bits nx codes lens_ofs lf ty.
  intros M M' f H [HA HW]. pose proof C as C'. open_itc C'.
  eapply mem_arr_magree; [exact HA | exact H | lia_std | lia_std].
Qed.

Lemma mpostL_of_tbl : forall M M', mpost R_segs M M' (p + 1384) (p + 7160) 0 0 -> mpostL R_segs M M' rsL.
Proof using.
  intros M M' HP. pose proof (framed_mpostL_trans2 R_segs M M M' rsL _ _ _ _ (mpostL_refl R_segs M rsL) HP) as H.
  apply H; [left | right; lia]. cbn. right. left. lia.
Qed.
Lemma mpostL_of_cnt : forall M M', mpost R_segs M M' (sp + -136) (sp + -104) 0 0 -> mpostL R_segs M M' rsL.
Proof using.
  intros M M' HP. pose proof (framed_mpostL_trans2 R_segs M M M' rsL _ _ _ _ (mpostL_refl R_segs M rsL) HP) as H.
  apply H; [left | right; lia]. cbn. left. lia.
Qed.

Lemma spure_st1 : forall st, SP st -> SP (tr_st1 X st).
Proof using.
  intros st HP. open_spure HP. unfold spure. cbn [t_work t_low t_drop t_next t_count t_tbl tr_st1]. split_conj; try assumption.
  - apply tr_count_range0. exact HCr.
  - apply tr_tbl1_range. exact HTr.
  - unfold tr_count. rewrite arr_len_set. exact CL.
  - rewrite it_fill_len_tr. exact TL.
Qed.
Lemma spure_st3 : forall st, SP st -> 0 <= tr_low X st < 32768 -> tr_drop X st = rt -> t_next st <= tr_next st -> SP (tr_st3 X st).
Proof using.
  intros st HP HL HD HN. open_spure HP. unfold spure. cbn [t_work t_low t_drop t_next t_count t_tbl tr_st3]. split_conj; try assumption.
  - unfold ZSEP. right. exact HL.
  - unfold ZSEP. right. exact HD.
  - lia_std.
  - lia_std.
  - apply tr_count_range0. exact HCr.
  - apply tr_tbl2_range. exact HTr.
  - unfold tr_count. rewrite arr_len_set. exact CL.
  - unfold tr_tbl2. rewrite arr_len_set. rewrite it_fill_len_tr. exact TL.
Qed.

Lemma trip_s : forall st Rb l M MD T,
  m_halted MD = None -> CR Rb l -> SR st Rb l -> CM M -> SM st M -> SP st ->
  it_trip_ok X 288 320 1444 st = true -> 1 <= mx ->
  (ty = CODES -> tr_w st < it_match ty) ->
  (forall st' R' M', it_step X st = ItCont st' -> CR R' [] -> SR st' R' [] ->
      mpostL R_segs M M' rsL -> CM M' -> SM st' M' -> SP st' ->
      realizes R_segs (zcfg R_segs 96852 (zupd R' []) M' MD) T) ->
  (forall st' R' M', it_step X st = ItBreak st' -> CR R' [] -> SR st' R' [] -> zget_l R' [] kS8 = t_len st' - t_drop st' ->
      mpostL R_segs M M' rsL -> CM M' -> SM st' M' -> SP st' ->
      0 <= t_len st' - t_drop st' <= 15 -> 0 <= t_used st' < 65536 -> 0 <= t_huff st' ->
      realizes R_segs (zcfg R_segs 97308 (zupd R' []) M' MD) T) ->
  (forall st' R' M', it_step X st = ItFail st' -> CR R' [] -> zget_l R' [] kA6 = 1 ->
      mpostL R_segs M M' rsL -> CM M' -> SM st' M' -> t_work st' = work1Ar ->
      (forall j, 0 <= j < 1444 -> 0 <= arr_get (t_tbl st') j < 4294967296) ->
      realizes R_segs (zcfg R_segs 97368 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 96852 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HS HM HSM HP TOK Hmx HcB KC KB KF.
  pose proof HP as HP'. open_spure HP'. open_smem HSM.
  pose proof TOK as TOK'. trip_facts TOK'. unbox Fwm.
  eapply here_s; try eassumption; try lia.
  intros R1 HC1 HS1 L10 L9.
  eapply fill_s; try eassumption.
  { open_cmem HM. assumption. }
  intros R2 M2 HC2 HS2 L8 HPO1 Wp2 Htbl2.
  pose proof (cmem_mpost M M2 _ _ HM HPO1 ltac:(left; split; reflexivity)) as HM2.
  pose proof (cnt_mpost M M2 _ Hcnt HPO1) as Hcnt2.
  eapply count_s; try eassumption.
  -
    intros R3 M3 HC3 HS3 L8' HPO2 HM3 HSM3 Hbrk.
    eapply sub_s; try eassumption.
    +
      intros R4 HC4 HS4 Hsub. eapply (KC (tr_st1 X st) R4 M3); try assumption.
      * rewrite it_step_eq, Hbrk, Hsub. reflexivity.
      * eapply mpostL_trans; [apply mpostL_of_tbl; exact HPO1 | apply mpostL_of_cnt; exact HPO2].
      * apply spure_st1. exact HP.
    +
      intros R4 M4 HC4 HS4 HPO3 HM4 HSM4 Hsub Hne HCU HLOW HDR HNX. eapply (KC (tr_st3 X st) R4 M4); try assumption.
      * rewrite it_step_eq, Hbrk, Hsub. cbn [x_ty itm_ctx]. rewrite Hne. reflexivity.
      * eapply mpostL_trans; [apply mpostL_of_tbl; exact HPO1 |].
        eapply mpostL_trans; [apply mpostL_of_cnt; exact HPO2 | apply mpostL_of_tbl; exact HPO3].
      * apply spure_st3; assumption.
    +
      intros R4 HC4 LA6 Hsub Hne. eapply (KF (tr_st2 X st) R4 M3); try assumption.
      * rewrite it_step_eq, Hbrk, Hsub. cbn [x_ty itm_ctx]. rewrite Hne. reflexivity.
      * eapply mpostL_trans; [apply mpostL_of_tbl; exact HPO1 | apply mpostL_of_cnt; exact HPO2].
      * cbn [t_tbl tr_st2]. apply tr_tbl1_range. exact HTr.
  -
    intros R3 M3 HC3 HS3 L8' HPO2 HM3 HSM3 Hbrk.
    assert (EL : tr_len X st = t_len st).
    { unfold tr_brk in Hbrk. apply andb_prop in Hbrk as [B1 B2]. unfold tr_len. rewrite B1.
      cbn [x_max itm_ctx] in *. rewrite B2. reflexivity. }
    assert (HHF : 0 <= tr_huff st).
    { unfold tr_huff. pose proof (pow2_le15 (t_len st - 1) ltac:(lia)) as PL1.
      pose proof (incr_range (t_huff st) 32 (shl32 1 (t_len st - 1)) ltac:(rewrite shl32_1 by lia; lia)) as IR.
      rewrite <- it_incr_back_eq in IR. fold (tr_incr2 st) in IR. rewrite shl32_1 in IR by lia.
      destruct (Z.eqb_spec (tr_incr2 st) 0); cbn [negb]; [lia|].
      assert (0 <= Z.land (t_huff st) (tr_incr2 st - 1)) by (apply Z.land_nonneg; lia). lia. }
    eapply (KB (tr_st1 X st) R3 M3); try assumption.
    all: try (rewrite it_step_eq, Hbrk; reflexivity).
    all: try (cbn [t_len t_drop tr_st1]; rewrite EL; first [exact L8' | lia]).
    all: try (eapply mpostL_trans; [apply mpostL_of_tbl; exact HPO1 | apply mpostL_of_cnt; exact HPO2]).
    all: try (apply spure_st1; exact HP).
    all: cbn [t_used t_huff tr_st1]; first [exact HHF | lia].
Qed.

Lemma main_loop_s : forall (PI : ItSt -> Prop),
  (forall st, PI st -> ty = CODES -> tr_w st < it_match ty) ->
  (forall st st', PI st -> it_step X st = ItCont st' -> PI st') ->
  forall k st Rb l M0 M MD T,
  it_loop_ok k X 288 320 1444 st = true -> 1 <= mx -> PI st ->
  m_halted MD = None -> CR Rb l -> SR st Rb l -> CM M -> SM st M -> SP st ->
  mpostL R_segs M0 M rsL ->
  (forall st' R' M', it_loop_n X (Z.of_nat k) st = inl st' ->
      CR R' [] -> SR st' R' [] -> zget_l R' [] kS8 = t_len st' - t_drop st' ->
      mpostL R_segs M0 M' rsL -> CM M' -> SM st' M' -> SP st' ->
      (t_huff st' <> 0 -> 0 <= t_next st' + t_huff st' < 1444) ->
      0 <= t_len st' - t_drop st' <= 15 -> 0 <= t_used st' < 65536 -> 0 <= t_huff st' ->
      realizes R_segs (zcfg R_segs 97308 (zupd R' []) M' MD) T) ->
  (forall st' R' M', it_loop_n X (Z.of_nat k) st = inr st' ->
      CR R' [] -> zget_l R' [] kA6 = 1 ->
      mpostL R_segs M0 M' rsL -> CM M' -> SM st' M' -> t_work st' = work1Ar ->
      (forall j, 0 <= j < 1444 -> 0 <= arr_get (t_tbl st') j < 4294967296) ->
      realizes R_segs (zcfg R_segs 97368 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 96852 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros PI HI1 HI2. induction k as [|k IH]; intros st Rb l M0 M MD T HOK Hmx PIs Hh HC HS HM HSM HP HPL KB KF.
  { cbn [it_loop_ok] in HOK. discriminate. }
  rewrite it_loop_ok_S in HOK. apply andb_prop in HOK as [TOK REST].
  eapply trip_s; try eassumption.
  - exact (HI1 _ PIs).
  - intros st' R' M' Hstep HC' HS' HPO HM' HSM' HP'. rewrite Hstep in REST.
    eapply (IH st' R' [] M0 M' MD T); try eassumption.
    + eapply HI2; eassumption.
    + eapply mpostL_trans; eassumption.
    + intros st'' R'' M'' Hl. eapply KB. rewrite it_loop_n_step by lia. rewrite Hstep.
      replace (Z.of_nat (S k) - 1) with (Z.of_nat k) by lia. exact Hl.
    + intros st'' R'' M'' Hl. eapply KF. rewrite it_loop_n_step by lia. rewrite Hstep.
      replace (Z.of_nat (S k) - 1) with (Z.of_nat k) by lia. exact Hl.
  - intros st' R' M' Hstep HC' HS' L8 HPO HM' HSM' HP' B1 B2 B3. rewrite Hstep in REST.
    eapply KB; try eassumption.
    + rewrite it_loop_n_step by lia. rewrite Hstep. reflexivity.
    + eapply mpostL_trans; eassumption.
    + intros Hne. destruct (Z.eqb_spec (t_huff st') 0); [lia_std|]. cbn [negb] in REST.
      apply andb_prop in REST as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. lia_std.
  - intros st' R' M' Hstep HC' LA6 HPO HM' HSM' HW HTR. eapply KF; try eassumption.
    + rewrite it_loop_n_step by lia. rewrite Hstep. reflexivity.
    + eapply mpostL_trans; eassumption.
Qed.
End S7IT5.
End FXG.
End S_It5.

Module S_It6.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel.ItableModel.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.I9S.Base.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ZTac OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ZMem OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ZCall OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ZCallL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ZArr OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ZArr4 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.IDefs OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ISpecs OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ITac.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.I9S.S_It3.S_It0 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.I9S.S_It3.S_It1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.I9S.S_It3.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

Section S7IT6.
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 192 zc.

#[local] Abbreviation PR := (pregs p lens_ofs codes pb sp vgp vtp (cty ty)).
#[local] Abbreviation PR6 := (pregs6 lens_ofs p pb sp vgp vtp).
#[local] Abbreviation cA := (arr_get (cntA lf lens_ofs codes)).
#[local] Abbreviation cntAr := (cntA lf lens_ofs codes).
#[local] Abbreviation mx := (mxA lf lens_ofs codes).
#[local] Abbreviation mn := (mnA lf lens_ofs codes).
#[local] Abbreviation rt := (rootA lf lens_ofs codes bits).
#[local] Abbreviation work1Ar := (work1A lf lens_ofs codes wf).
#[local] Abbreviation X := (itm_ctx ty (lensA lf) lens_ofs nx (rootA lf lens_ofs codes bits) (mxA lf lens_ofs codes)).
#[local] Abbreviation CR := (cregsN ty lf lens_ofs codes bits p pb sp vgp vtp).
#[local] Abbreviation CRB := (cregsB ty lf lens_ofs codes bits p pb sp vgp vtp).
#[local] Abbreviation SR := (sregs p).
#[local] Abbreviation CM := (cmem ty lf lens_ofs codes nx wf p sp).
#[local] Abbreviation SM := (smem p sp).
#[local] Abbreviation SP := (spure lf lens_ofs codes nx bits wf).
#[local] Abbreviation st0 := (itm_st0 (mnA lf lens_ofs codes) nx (rootA lf lens_ofs codes bits) (cntA lf lens_ofs codes) (tblA cf) (work1A lf lens_ofs codes wf)).

Ltac xaddr := pose proof (xaddr_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C) as (XS1 & XS2 & XA1 & XA2 & XB1 & XB2 & XN).

Definition pregs3 (R : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l R l kSP = sp + -192 /\ zget_l R l kGP = vgp /\ zget_l R l kTP = vtp.
Ltac close_pregs3 := unfold pregs3; split_conj; zreg.

Lemma ne_pow : forall k, 1 <= k <= 15 ->
  it_not_enough ty (itm_used k) = match ty with CODES => false | _ => negb (k <=? 9) end.
Proof using C zc ret sp pb p wf cf bits nx codes lens_ofs lf.
  intros k Hk. rewrite itm_used_pow2 by lia_std. unfold it_not_enough, ENOUGH_LENS, ENOUGH_DISTS.
  assert (E : forall b : bool, (if b then true else false) = b) by (destruct b; reflexivity).
  destruct ty; [reflexivity| |].
  - destruct (Z.leb_spec k 9); cbn [negb].
    + apply Z.ltb_ge. assert (2 ^ k <= 2 ^ 9) by (apply Z.pow_le_mono_r; lia_std). change (2 ^ 9) with 512 in *. lia_std.
    + apply Z.ltb_lt. assert (2 ^ 10 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia_std). change (2 ^ 10) with 1024 in *. lia_std.
  - destruct (Z.leb_spec k 9); cbn [negb].
    + apply Z.ltb_ge. assert (2 ^ k <= 2 ^ 9) by (apply Z.pow_le_mono_r; lia_std). change (2 ^ 9) with 512 in *. lia_std.
    + apply Z.ltb_lt. assert (2 ^ 10 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia_std). change (2 ^ 10) with 1024 in *. lia_std.
Qed.

Lemma init_s : forall Rb l M MD T,
  m_halted MD = None -> PR6 Rb l -> zget_l Rb l kT0 = mx -> zget_l Rb l kT1 = mn -> zget_l Rb l kA7 = rt ->
  zget_l Rb l kA0 = it_match ty -> zget_l Rb l kT3 = EXAn ty p -> zget_l Rb l kT2 = BSAn ty p ->
  1 <= mx -> CM M -> SM st0 M ->
  (forall R', CR R' [] -> SR st0 R' [] -> realizes R_segs (zcfg R_segs 96852 (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs 96800 (zupd Rb l) M MD) T.
Proof using C zc ret.
  intros Rb l M MD T Hh HP LT0 LT1 LA7 LA2 LT3 LT4 Hmx HM HSM K.
  pose proof C as C'. open_itc C'. open_pregs6 HP. open_cmem HM. zkeys. clear Hprom HtyC HtyD Hpb.
  pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C Hmx) as (RT1 & RT2 & RT3). pose proof (pow2_le15 rt ltac:(lia)) as PRT.
  zrebase.
  zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zsetreg (2 ^ rt) ltac:(symmetry; apply sllw_1; lia).
  zstep Rfd. zsetreg (2 ^ rt - 1) ltac:(rewrite swrap32_small by lia; lia).
  zstep Rfd. zstep Rfd. zstep Rfd.
  zstep Rfd. zsetreg (2 ^ rt) ltac:(symmetry; apply sllw_1; lia).
  zstep Rfd. zsetreg (-1) ltac:(reflexivity).
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
  - close_cregs.
  - unfold sregs. cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low itm_st0]. rewrite itm_used_pow2 by lia.
    unfold lowS. cbn [Z.eqb Pos.eqb]. split_conj; zreg.
Qed.

Ltac kfix := unfold EXAn, BSAn, EXA, BSA; match goal with H : ty = _ |- _ => rewrite H end; cbv iota; kauto.
Lemma ty_cases :
  (ty = CODES /\ cty ty = 0 /\ it_match ty = 20 /\ EXA ty p = p + 808 /\ BSA ty p = p + 808 /\ NE ty = 288 /\ isL ty = 0 /\ isD ty = 0)
  \/ (ty = LENS /\ cty ty = 1 /\ it_match ty = 257 /\ EXA ty p = 67232 /\ BSA ty p = 67170 /\ NE ty = 31 /\ isL ty = 1 /\ isD ty = 0)
  \/ (ty = DISTS /\ cty ty = 2 /\ it_match ty = 0 /\ EXA ty p = 67358 /\ BSA ty p = 67294 /\ NE ty = 32 /\ isL ty = 0 /\ isD ty = 1).
Proof using C zc ret sp pb wf cf bits nx codes lens_ofs lf. destruct ty; [left | right; left | right; right]; repeat split; reflexivity. Qed.

Lemma spure_st0 : 1 <= mx -> SP st0.
Proof using C zc ret sp pb p ty.
  intros Hmx. pose proof C as C'. open_itc C'. unfold spure. cbn [t_work t_low t_drop t_next t_count t_tbl itm_st0]. split_conj.
  - reflexivity.
  - unfold ZSEP. left. reflexivity.
  - unfold ZSEP. left. reflexivity.
  - lia_std.
  - lia_std.
  - intros j Hj. pose proof (cA_range _ _ _ _ _ _ _ _ _ _ _ _ _ C j). lia_std.
  - intros j Hj. rewrite tblA_get. apply Hcf. exact Hj.
  - rewrite cntA_eq. apply cntK_len.
  - unfold tblA. apply arr_len_init.
Qed.

Lemma switch_s : forall Rb l M MD T,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kT0 = mx -> zget_l Rb l kT1 = mn -> zget_l Rb l kA7 = rt -> 1 <= mx ->
  mem_wr R_segs M (sp - 192) 192 -> mem_wr R_segs M p 7176 ->
  mem_arr 2 R_segs M (p + 168) 320 lf -> mem_arr 2 R_segs M (p + 808) 288 (arr_get work1Ar) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA -> mem_arr 4 R_segs M (p + 1384) 1444 cf ->
  mem_u64 R_segs M (p + 160) (p + 1384 + 4 * nx) ->
  mem_arr 2 R_segs M 67170 31 (arr_get lbase_a) -> mem_arr 2 R_segs M 67232 31 (arr_get lext_a) ->
  mem_arr 2 R_segs M 67294 32 (arr_get dbase_a) -> mem_arr 2 R_segs M 67358 32 (arr_get dext_a) ->
  (forall R' M', CR R' [] -> SR st0 R' [] -> mpost R_segs M M' (sp + -184) (sp + -168) 0 0 ->
     CM M' -> SM st0 M' -> SP st0 -> it_not_enough ty (itm_used rt) = false ->
     realizes R_segs (zcfg R_segs 96852 (zupd R' []) M' MD) T) ->
  (forall R' M', PR6 R' [] -> zget_l R' [] kA6 = 1 -> mpost R_segs M M' (sp + -184) (sp + -168) 0 0 ->
     it_not_enough ty (itm_used rt) = true ->
     realizes R_segs (zcfg R_segs 97368 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 96644 (zupd Rb l) M MD) T.
Proof using C zc ret.
  intros Rb l M MD T Hh HP LT0 LT1 LA7 Hmx Wf Wp Hlens Hwork Hcnt Htbl Hnext Hlb Hle Hdb Hde KBODY KFAIL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. xaddr. clear HtyC HtyD.
  pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C Hmx) as (RT1 & RT2 & RT3).
  pose proof (spure_st0 Hmx) as HSP.
  assert (HSM : forall Mq, mem_arr 2 R_segs Mq (sp + -136) 16 cA -> mem_arr 4 R_segs Mq (p + 1384) 1444 cf -> SM st0 Mq).
  { intros Mq A B. unfold smem. cbn [t_count t_tbl itm_st0]. split; [exact A|].
    eapply mem_arr_ext; [exact B|]. intros j _. symmetry. apply tblA_get. }
  pose proof (ne_pow rt ltac:(lia)) as NE.
  pose proof (mpost_stable R_segs M (sp + -184) (sp + -168) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X (sp + -184) (sp + -168) 0 0) M) by (apply mpost_refl).
  zrebase.
  destruct ty_cases as [(Ety & E0 & EM & EX & EB & EN & EL & ED) | [(Ety & E0 & EM & EX & EB & EN & EL & ED) | (Ety & E0 & EM & EX & EB & EN & EL & ED)]];
    rewrite E0 in LA0.
  -
    zstep Rfd. zbr Rfd false. zstep Rfd. zbr Rfd false. zbr Rfd false.
    zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.
    eapply init_s; try eassumption; try lia.
    all: try kfix.
    all: try kauto.
    all: lazymatch goal with
         | |- cmem _ _ _ _ _ _ _ _ _ => unfold cmem; rewrite EX, EB, EN, EL, ED, Ety; split_conj; assumption
         | |- smem _ _ _ _ => apply HSM; assumption
         | |- _ => idtac
         end.
    intros R' HC' HS'. eapply KBODY; try assumption.
    + unfold cmem. rewrite EX, EB, EN, EL, ED, Ety. split_conj; assumption.
    + apply HSM; assumption.
    + rewrite NE, Ety. reflexivity.
  -
    zstep Rfd. zbr Rfd false. zstep Rfd. zbr Rfd true. zstep Rfd.
    destruct (Z_lt_le_dec 9 rt) as [BIG|OK].
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KFAIL Rx M) end.
      all: try kauto. all: try exact HAG.
      rewrite NE, Ety. destruct (Z.leb_spec rt 9); [lia | reflexivity].
    + zbr Rfd false.
      zstep Rfd.
      zstep Rfd.
      zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.
      zstep Rfd. zstep Rfd.
      zstep Rfd.
      eapply init_s; try eassumption; try lia.
      all: try kfix.
      all: try kauto.
      all: lazymatch goal with
           | |- cmem _ _ _ _ _ _ _ _ _ => unfold cmem; rewrite EX, EB, EN, EL, ED, Ety; split_conj; assumption
           | |- smem _ _ _ _ => apply HSM; assumption
           | |- _ => idtac
           end.
      intros R' HC' HS'. eapply KBODY; try assumption.
      * unfold cmem. rewrite EX, EB, EN, EL, ED, Ety. split_conj; assumption.
      * apply HSM; assumption.
      * rewrite NE, Ety. destruct (Z.leb_spec rt 9); [reflexivity | lia].
  -
    zstep Rfd. zbr Rfd true. zstep Rfd. zstep Rfd.
    destruct (Z_lt_le_dec 9 rt) as [BIG|OK].
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KFAIL Rx Mx) end.
      all: try kauto. all: try exact HAG.
      rewrite NE, Ety. destruct (Z.leb_spec rt 9); [lia | reflexivity].
    + zbr Rfd false.
      zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.
      eapply init_s; try eassumption; try lia.
      all: try kfix.
      all: try kauto.
      all: lazymatch goal with
           | |- cmem _ _ _ _ _ _ _ _ _ => unfold cmem; rewrite EX, EB, EN, EL, ED, Ety; split_conj; assumption
           | |- smem _ _ _ _ => apply HSM; assumption
           | |- _ => idtac
           end.
      intros R' HC' HS'. eapply KBODY; try assumption.
      * unfold cmem. rewrite EX, EB, EN, EL, ED, Ety. split_conj; assumption.
      * apply HSM; assumption.
      * rewrite NE, Ety. destruct (Z.leb_spec rt 9); [reflexivity | lia].
Qed.

Lemma entry_write2 : forall M base n f i lo a0 a2,
  mem_arr 4 R_segs M base i f ->
  mem_arr 4 R_segs M (base + 4 * (i + 1)) (n - (i + 1)) (fun j => f (i + 1 + j)) ->
  mem_u16 R_segs M a0 lo -> mem_u16 R_segs M a2 0 ->
  a0 = base + 4 * i -> a2 = a0 + 2 -> 0 <= i < n -> base + 4 * n <= two64 -> 0 <= base -> 0 <= lo < 65536 ->
  mem_arr 4 R_segs M base n (zfupd f i lo).
Proof using.
  intros M base n f i lo a0 a2 H1 H2 Hlo Hhi -> -> Hi Hn Hb Rlo.
  eapply mem_arr4_fill; [exact H1 | | exact H2 | lia | lia].
  change 4%nat with (2 + 2)%nat. rewrite Z_to_le_bytes_add. unfold mem_u16 in *.
  apply mem_is_app; [exact Hlo | | rewrite two64_eq in *; lia | rewrite !length_Z_to_le_bytes; cbn; rewrite two64_eq in *; lia].
  rewrite length_Z_to_le_bytes. change (Z.of_nat 2) with 2.
  replace (Z.shiftr lo (8 * 2)) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia). exact Hhi.
Qed.

Definition slots (M : mem) (v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : Z) : Prop :=
  mem_u64 R_segs M (sp + -8) v1 /\ mem_u64 R_segs M (sp + -16) v8 /\ mem_u64 R_segs M (sp + -24) v9 /\
  mem_u64 R_segs M (sp + -32) v18 /\ mem_u64 R_segs M (sp + -40) v19 /\ mem_u64 R_segs M (sp + -48) v20 /\
  mem_u64 R_segs M (sp + -56) v21 /\ mem_u64 R_segs M (sp + -64) v22 /\ mem_u64 R_segs M (sp + -72) v23 /\
  mem_u64 R_segs M (sp + -80) v24 /\ mem_u64 R_segs M (sp + -88) v25 /\ mem_u64 R_segs M (sp + -96) v26 /\
  mem_u64 R_segs M (sp + -104) v27.

Lemma epilogue_s : forall Rb l M MD T v v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27,
  m_halted MD = None -> zget_l Rb l kSP = sp + -192 -> zget_l Rb l kA6 = v ->
  slots M v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 -> Z.land v1 (-2) = v1 -> 0 <= v1 < two64 ->
  (forall R', zget_l R' [] kA0 = v -> zget_l R' [] kSP = sp -> zget_l R' [] kRA = v1 ->
     zget_l R' [] kS0 = v8 -> zget_l R' [] kS1 = v9 -> zget_l R' [] kS2 = v18 -> zget_l R' [] kS3 = v19 ->
     zget_l R' [] kS4 = v20 -> zget_l R' [] kS5 = v21 -> zget_l R' [] kS6 = v22 -> zget_l R' [] kS7 = v23 ->
     zget_l R' [] kS8 = v24 -> zget_l R' [] kS9 = v25 -> zget_l R' [] kS10 = v26 -> zget_l R' [] kS11 = v27 ->
     zget_l R' [] kGP = zget_l Rb l kGP -> zget_l R' [] kTP = zget_l Rb l kTP ->
     realizes R_segs (zcfg R_segs v1 (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs 97368 (zupd Rb l) M MD) T.
Proof using C zc ret pb p wf cf bits nx codes lens_ofs lf ty.
  intros Rb l M MD T v v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 Hh LSP LA6 HSL Hev Hv1 K.
  remember (zget_l Rb l kGP) as vgp' eqn:EG. remember (zget_l Rb l kTP) as vtp' eqn:ET. symmetry in EG, ET.
  pose proof C as C'. open_itc C'. zkeys. clear Hprom HtyC HtyD Hpb Hlf Hcf Hwf Hlens15.
  unfold slots in HSL. dand HSL as (M1 & M8 & M9 & M18 & M19 & M20 & M21 & M22 & M23 & M24 & M25 & M26 & M27).
  zrebase.
  zstep Rfd.
  do 13 (zstep Rfd).
  zstep Rfd.
  zret Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
  all: zreg.
Qed.

Lemma setbits_s : forall Rb l M MD T rv,
  m_halted MD = None -> pregs3 Rb l -> zget_l Rb l kA4 = pb -> zget_l Rb l kA7 = rv -> mem_wr R_segs M p 7176 ->
  (forall R' M', pregs3 R' [] -> zget_l R' [] kA6 = 0 -> mpost R_segs M M' pb (pb + 4) 0 0 -> mem_u32 R_segs M' pb rv ->
     realizes R_segs (zcfg R_segs 97368 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 97360 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx codes lens_ofs lf ty.
  intros Rb l M MD T rv Hh HP LA4 LA7 Wp K.
  pose proof C as C'. open_itc C'. unfold pregs3 in HP. dand HP as (LSP & LGP & LTP). zkeys. clear Hprom HtyC HtyD Hlf Hcf Hwf Hlens15. unfold ZSEP in Hpb.
  pose proof (mpost_stable R_segs M pb (pb + 4) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X pb (pb + 4) 0 0) M) by (apply mpost_refl).
  zrebase.
  zstep Rfd.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx) end.
  all: try kauto. all: try close_pregs3. all: exact HAG.
Qed.

Lemma it_room_ge : 128 <= it_room ty.
Proof using C zc ret sp pb p wf cf bits nx codes lens_ofs lf. destruct ty; cbn; unfold ENOUGH_LENS, ENOUGH_DISTS; lia_std. Qed.

Definition rsT : list (Z * Z) := [(p + 1384, 5776); (p + 160, 8); (pb, 4)].

Lemma break_tail_s : forall st Rb l M MD T,
  m_halted MD = None -> CR Rb l -> SR st Rb l -> zget_l Rb l kS8 = t_len st - t_drop st ->
  CM M -> SM st M -> SP st ->
  0 <= t_len st - t_drop st <= 15 -> 0 <= t_used st < 65536 -> 0 <= t_huff st ->
  (t_huff st <> 0 -> 0 <= t_next st + t_huff st < 1444) ->
  (forall R' M', pregs3 R' [] -> zget_l R' [] kA6 = 0 -> mpostL R_segs M M' rsT ->
     mem_arr 4 R_segs M' (p + 1384) 1444
       (arr_get (if negb (t_huff st =? 0) then arr_set (t_tbl st) (t_next st + t_huff st) (code_pack 64 (t_len st - t_drop st) 0)
                 else t_tbl st)) ->
     mem_u64 R_segs M' (p + 160) (p + 1384 + 4 * (nx + t_used st)) -> mem_u32 R_segs M' pb rt ->
     mem_wr R_segs M' (sp - 192) 192 -> mem_wr R_segs M' p 7176 ->
     mem_arr 2 R_segs M' (p + 168) 320 lf -> mem_arr 2 R_segs M' (p + 808) 288 (arr_get work1Ar) ->
     realizes R_segs (zcfg R_segs 97368 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 97308 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HS LS8 HM HSM HP Hhb Hused Hhuff Hfit K.
  pose proof C as C'. open_itc C'. open_cmem HM. open_smem HSM. open_spure HP. zkeys. xaddr.
  clear Hprom HtyC HtyD Hlf Hcf Hwf Hlens15 LOWR DROPR.
  assert (J80 : forall RJ MJ, CRB RJ [] -> zget_l RJ [] kT5 = t_used st ->
            mpost R_segs M MJ (p + 1384) (p + 7160) 0 0 ->
            mem_arr 4 R_segs MJ (p + 1384) 1444
              (arr_get (if negb (t_huff st =? 0) then arr_set (t_tbl st) (t_next st + t_huff st) (code_pack 64 (t_len st - t_drop st) 0)
                        else t_tbl st)) ->
            mem_wr R_segs MJ (sp - 192) 192 -> mem_wr R_segs MJ p 7176 ->
            mem_arr 2 R_segs MJ (p + 168) 320 lf -> mem_arr 2 R_segs MJ (p + 808) 288 (arr_get work1Ar) ->
            mem_u64 R_segs MJ (p + 160) (p + 1384 + 4 * nx) ->
            realizes R_segs (zcfg R_segs 97340 (zupd RJ []) MJ MD) T).
  { intros RJ MJ HCJ JT5 HPO HtblJ WfJ WpJ HlensJ HworkJ HnextJ.
    clear Hcnt Htbl Wf Wp Hlens Hwork Hnext HslD HslL Hext Hbase. open_cregsB HCJ. zkeys.
    pose proof (mpost_stable R_segs MJ (p + 160) (p + 168) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
    assert (HAG : framed (fun X => mpost R_segs MJ X (p + 160) (p + 168) 0 0) MJ) by (apply mpost_refl).
    zrebase.
    zstep Rfd.
    zstep Rfd. zstep Rfd. zsetreg (4 * t_used st) ltac:(symmetry; apply zext32_x4; lia).
    zstep Rfd. zsetreg (p + 1384 + 4 * (nx + t_used st)) ltac:(lia).
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (setbits_s Rx [] Mx MD T rt Hh) end.
    all: try kauto. all: try close_pregs3.
    intros R' M' HP' LA6 HPO2 Hbits'.
    destruct HPO2 as [HA2 HW2].
    eapply K; try eassumption.
    -
      pose proof (framed_mpostL_trans2 R_segs M M MJ rsT _ _ _ _ (mpostL_refl R_segs M rsT) HPO ltac:(left; cbn; left; lia) ltac:(right; lia)) as F1.
      pose proof (framed_mpostL_trans2 R_segs M MJ _ rsT _ _ _ _ F1 HAG ltac:(left; cbn; right; left; lia) ltac:(right; lia)) as F2.
      exact (framed_mpostL_trans2 R_segs M _ M' rsT _ _ _ _ F2 (conj HA2 HW2) ltac:(left; cbn; right; right; left; lia) ltac:(right; lia)).
    - eapply mem_arr_magree; [exact HA2 | eassumption | unfold ZSEP in Hpb; lia | lia].
    - eapply mem_u64_magree; [exact HA2 | eassumption | lia | rewrite two64_eq; lia | unfold ZSEP in Hpb; lia | lia].
    - apply HW2. assumption.
    - apply HW2. assumption.
    - eapply mem_arr_magree; [exact HA2 | eassumption | unfold ZSEP in Hpb; lia | lia].
    - eapply mem_arr_magree; [exact HA2 | eassumption | unfold ZSEP in Hpb; lia | lia]. }
  pose proof (mpost_stable R_segs M (p + 1384) (p + 7160) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X (p + 1384) (p + 7160) 0 0) M) by (apply mpost_refl).
  open_cregs HC. open_sregs HS. zkeys. zrebase.
  destruct (Z.eq_dec (t_huff st) 0) as [H0|HN0].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J80 Rx M) end.
    all: try kauto. all: try assumption.
    rewrite H0. cbn [Z.eqb negb]. exact Htbl.
  - zbr Rfd false.
    specialize (Hfit HN0).
    destruct (arr4_hole R_segs M (p + 1384) 1444 (arr_get (t_tbl st)) (t_next st + t_huff st) Htbl ltac:(lia)) as [HT1 HT2]. clear Htbl.
    zstep Rfd. zstep Rfd. zsetreg (4 * t_huff st) ltac:(symmetry; apply zext32_x4; lia).
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    match goal with
    | Ho : mem_u8 _ ?Mc _ 64, Hb : mem_u8 _ _ _ (t_len st - t_drop st), Hv : mem_u16 _ _ _ 0 |- _ =>
      pose proof (entry_write Mc (p + 1384) 1444 (arr_get (t_tbl st)) (t_next st + t_huff st) _ _ _ _ _ _ HT1 HT2 Ho Hb Hv
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Htbl;
      clear Ho Hb Hv HT1 HT2
    end.
    apply mem_arr_arr_set in Htbl; [| rewrite TL; lia].
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (J80 Rx Mx) end.
    all: try kauto. all: try assumption.
    destruct (Z.eqb_spec (t_huff st) 0); [lia|]. cbn [negb]. exact Htbl.
Qed.

Lemma max0_s : forall Rb l M MD T,
  m_halted MD = None -> PR Rb l -> mx = 0 ->
  mem_wr R_segs M p 7176 -> mem_arr 4 R_segs M (p + 1384) 1444 cf -> mem_u64 R_segs M (p + 160) (p + 1384 + 4 * nx) ->
  mem_wr R_segs M (sp - 192) 192 -> mem_arr 2 R_segs M (p + 168) 320 lf -> mem_arr 2 R_segs M (p + 808) 288 wf ->
  (forall R' M', pregs3 R' [] -> zget_l R' [] kA6 = 0 -> mpostL R_segs M M' rsT ->
     mem_arr 4 R_segs M' (p + 1384) 1444 (arr_get (arr_set (arr_set (tblA cf) nx (code_pack 64 1 0)) (nx + 1) (code_pack 64 1 0))) ->
     mem_u64 R_segs M' (p + 160) (p + 1384 + 4 * (nx + 2)) -> mem_u32 R_segs M' pb 1 ->
     mem_wr R_segs M' (sp - 192) 192 -> mem_wr R_segs M' p 7176 ->
     mem_arr 2 R_segs M' (p + 168) 320 lf -> mem_arr 2 R_segs M' (p + 808) 288 wf ->
     realizes R_segs (zcfg R_segs 97368 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 97468 (zupd Rb l) M MD) T.
Proof using C zc ret bits.
  intros Rb l M MD T Hh HP Hmx0 Wp Htbl Hnext Wf Hlens Hwork K.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear Hprom HtyC HtyD Hlf Hwf Hlens15.
  pose proof it_room_ge as HRG.
  assert (Htbl' : mem_arr 4 R_segs M (p + 1384) 1444 (arr_get (tblA cf))).
  { eapply mem_arr_ext; [exact Htbl|]. intros j _. symmetry. apply tblA_get. }
  clear Htbl.
  pose proof (mpostL_stable R_segs M rsT ltac:(cbn; unfold ZSEP in Hpb; rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpostL R_segs M X rsT) M) by (apply mpostL_refl).
  destruct (arr4_hole R_segs M (p + 1384) 1444 (arr_get (tblA cf)) nx Htbl' ltac:(lia)) as [HT1 HT2]. clear Htbl'.
  zrebase.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  match goal with
  | Hlo : mem_u16 _ ?Mc _ 320, Hhi : mem_u16 _ _ _ 0 |- _ =>
    pose proof (entry_write2 Mc (p + 1384) 1444 (arr_get (tblA cf)) nx 320 _ _ HT1 HT2 Hlo Hhi
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(lia)) as Htbl;
    clear Hlo Hhi HT1 HT2
  end.
  apply mem_arr_arr_set in Htbl; [| unfold tblA; rewrite arr_len_init; cbv [N_CODES]; lia].
  destruct (arr4_hole R_segs _ (p + 1384) 1444 _ (nx + 1) Htbl ltac:(lia)) as [HT1 HT2]. clear Htbl.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  match goal with
  | Hlo : mem_u16 _ ?Mc _ 320, Hhi : mem_u16 _ _ _ 0 |- _ =>
    pose proof (entry_write2 Mc (p + 1384) 1444 _ (nx + 1) 320 _ _ HT1 HT2 Hlo Hhi
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(lia)) as Htbl;
    clear Hlo Hhi HT1 HT2
  end.
  apply mem_arr_arr_set in Htbl; [| rewrite arr_len_set; unfold tblA; rewrite arr_len_init; cbv [N_CODES]; lia].
  zstep Rfd.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (setbits_s Rx [] Mx MD T 1 Hh) end.
  all: try kauto. all: try close_pregs3.
  intros R' M' HP' LA6 HPO2 Hbits'. destruct HPO2 as [HA2 HW2].
  eapply K; try eassumption.
  - exact (framed_mpostL_trans2 R_segs M _ M' rsT _ _ _ _ HAG (conj HA2 HW2) ltac:(left; cbn; right; right; left; lia) ltac:(right; lia)).
  - eapply mem_arr_magree; [exact HA2 | | unfold ZSEP in Hpb; lia | lia].
    change (code_pack 64 1 0) with 320. exact Htbl.
  - eapply mem_u64_magree; [exact HA2 | | lia | rewrite two64_eq; lia | unfold ZSEP in Hpb; lia | lia].
    match goal with H : mem_u64 _ _ (p + 160) ?v |- _ => replace (p + 1384 + 4 * (nx + 2)) with v by lia; exact H end.
  - apply HW2. assumption.
  - apply HW2. assumption.
  - eapply mem_arr_magree; [exact HA2 | eassumption | unfold ZSEP in Hpb; lia | lia].
  - eapply mem_arr_magree; [exact HA2 | eassumption | unfold ZSEP in Hpb; lia | lia].
Qed.
End S7IT6.
End FXG.
End S_It6.

Module S_It7.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel.ItableModel.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.I9S.Base.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ZTac OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ZMem OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ZCall OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ZCallL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ZArr OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ZArr4 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.IDefs OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ISpecs OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.ITac.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.I9S.S_It3.S_It0 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.I9S.S_It3.S_It1 S_It2 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.I9S.S_It3 S_It4 S_It5 S_It6.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

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
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

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
    realizes R_segs (zcfg R_segs 97368 (zupd R' []) M' MD) T).
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


