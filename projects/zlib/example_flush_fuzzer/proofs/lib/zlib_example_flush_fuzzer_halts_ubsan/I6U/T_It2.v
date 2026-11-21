(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  ZIface InflateState Inftrees InftreesCoverage ItableModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.I6U Require Import Base.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.IK Require Import ZTac ZArr ZArr4. From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.IK6 Require Import IDefs ISpecs ITac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.I6S Require Import S_It0.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.I6U Require Import T_It1.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
(* itc at 1.4: lenbits/distbits at p+120/p+124 *)
Record itc (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z)
           (p pb sp ret FR zc : Z) : Prop := ITC {
  C_lf    : forall i, 0 <= i < N_LENS -> 0 <= lf i < 65536;
  C_cf    : forall i, 0 <= i < N_CODES -> 0 <= cf i < two32;
  C_wf    : forall i, 0 <= i < N_WORK -> 0 <= wf i < 65536;
  C_ofs   : 0 <= lens_ofs;
  C_ofs2  : lens_ofs + codes <= N_LENS;
  C_codes : 0 <= codes;
  C_codes2 : codes <= 288;
  C_lens15 : forall s, 0 <= s < codes -> lf (lens_ofs + s) <= 15;
  C_tyC   : ty = CODES -> codes <= 19 /\ bits = 7 /\ (forall s, 0 <= s < codes -> lf (lens_ofs + s) <= 7);
  C_tyD   : ty = DISTS -> codes <= 32;
  C_bits  : 1 <= bits;
  C_bits2 : bits <= 15;
  C_nx    : 0 <= nx;
  C_room  : nx + it_room ty <= N_CODES;
  C_pb    : pb = p + 120 \/ pb = p + 124;
  C_pal   : p mod 16 = 0;
  C_p0    : 0 < p;
  C_pceil : p + STATE_SIZE <= zc;
  C_sp    : zc + FR <= sp;
  C_zrom  : DEXT_ADDR + 64 <= zc;
  C_sp2   : sp <= 140737488355328;
  C_spal  : sp mod 16 = 0;
  C_prom  : p + STATE_SIZE <= ROM_LO_ALL \/ DEXT_ADDR + 64 <= p;
  C_ret   : Z.land ret (-2) = ret;
  C_ret2  : 0 <= ret < two64 }.

Lemma itc_old : forall ty lf lens_ofs codes nx bits cf wf p pb sp ret FR zc,
  itc ty lf lens_ofs codes nx bits cf wf p pb sp ret FR zc ->
  S_It0.itc ty lf lens_ofs codes nx bits cf wf p (p + 136) sp ret FR zc.
Proof. intros * H. destruct H; constructor; try assumption. left; reflexivity. Qed.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Section U7IT.
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 208 zc.

#[local] Abbreviation PR := (pregs p lens_ofs codes pb sp vgp vtp (cty ty)).
#[local] Abbreviation cnt i := (arr_get (cntK lf lens_ofs i)).
#[local] Abbreviation cA := (arr_get (cntA lf lens_ofs codes)).
#[local] Abbreviation mx := (mxA lf lens_ofs codes).

Lemma cA_range : forall j, 0 <= cA j <= codes.
Proof. intros j. pose proof C as C'. destruct C'. rewrite cntA_eq. pose proof (cntK_le lf lens_ofs codes j ltac:(lia_std) ltac:(lia_std)). lia_std. Qed.


Lemma count_loop_t : forall fuel i Rb l M MD T,
  (Z.to_nat (codes - i) <= fuel)%nat -> 0 <= i < codes ->
  m_halted MD = None -> PR Rb l ->
  zget_l Rb l kA6 = 2 * i -> zget_l Rb l kT5 = p + 152 + 2 * lens_ofs + 2 * i -> zget_l Rb l kT3 = 2 * codes ->
  zget_l Rb l kA7 = sp + -136 -> zget_l Rb l kT0 = 0 -> zget_l Rb l kT1 = - (p + 152 + 2 * lens_ofs) + -1 ->
  zget_l Rb l kT2 = - (sp + -136) + -1 -> zget_l Rb l kT4 = 16 ->
  mem_wr R_segs M (sp - 208) 208 ->
  mem_arr 2 R_segs M (p + 152) 320 lf ->
  mem_arr 2 R_segs M (sp + -136) 16 (cnt i) ->
  (forall R' M',
     PR R' [] -> zget_l R' [] kA7 = sp + -136 ->
     mpost R_segs M M' (sp + -136) (sp + -104) 0 0 ->
     mem_wr R_segs M' (sp - 208) 208 ->
     mem_arr 2 R_segs M' (p + 152) 320 lf ->
     mem_arr 2 R_segs M' (sp + -136) 16 (cnt codes) ->
     realizes R_segs (zcfg R_segs 138588 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 138536 (zupd Rb l) M MD) T.
Proof.
  induction fuel as [|fuel IH]; intros i Rb l M MD T Hfuel Hi Hh HP LA6 LT5 LT3 LA7 LT0 LT1 LT2 LT4 Wf Hlens Hcnt K.
  { exfalso. lia. }
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom.
  pose proof (Hlens15 i ltac:(lia)) as Hl15. pose proof (Hlf (lens_ofs + i) ltac:(lia)) as Hl16.
  assert (HCr1 : forall j, 0 <= j < 16 -> -32768 <= cnt i j < 32768).
  { intros j _. pose proof (cntK_le lf lens_ofs i j ltac:(lia) ltac:(lia)). lia. }
  pose proof (mpost_stable R_segs M (sp + -136) (sp + -104) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X (sp + -136) (sp + -104) 0 0) M) by (apply mpost_refl).
  pose proof (lnot_val_mod' (p + 152 + 2 * lens_ofs) ltac:(lia)) as Hn1.
  pose proof (lnot_val_mod' (sp + -136) ltac:(lia)) as Hn2.
  zrebase.
  zbr Rfd false.
  zbr Rfd false.
  tstep Rfd.
  zbr Rfd false.
  tstep Rfd. zsetreg (2 * lf (lens_ofs + i)) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zbr Rfd false.
  tstep Rfd.
  tstep Rfd.
  tstep Rfd.
  tstep Rfd.
  tstore_arr Rfd Hcnt (lf (lens_ofs + i)).
  apply mem_arr_arr_set in Hcnt; [|rewrite cntK_len; lia].
  rewrite <- (cntK_step lf lens_ofs i) in Hcnt by lia.
  zstep Rfd.
  destruct (Z.eq_dec (i + 1) codes) as [Hend|Hmore].
  - zbr Rfd false.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R ?Mx _) _ => eapply (K R Mx) end.
    all: try first [close_pregs | zreg | assumption].
    rewrite <- Hend. exact Hcnt.
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (IH (i + 1) Rx [] Mx MD T) end.
    all: try first [lia | assumption | close_pregs | zreg].
    intros R' M'. intros. eapply K; try eassumption.
    eapply mpost_trans; [exact HAG | assumption].
Qed.

Lemma count_phase_t : forall Rb l M MD T,
  0 < codes -> m_halted MD = None -> PR Rb l ->
  mem_wr R_segs M (sp - 208) 208 ->
  mem_arr 2 R_segs M (p + 152) 320 lf ->
  mem_arr 2 R_segs M (sp + -136) 16 (fun _ => 0) ->
  (forall R' M',
     PR R' [] -> zget_l R' [] kA7 = sp + -136 ->
     mpost R_segs M M' (sp + -136) (sp + -104) 0 0 ->
     mem_wr R_segs M' (sp - 208) 208 ->
     mem_arr 2 R_segs M' (p + 152) 320 lf ->
     mem_arr 2 R_segs M' (sp + -136) 16 cA ->
     realizes R_segs (zcfg R_segs 138588 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 138492 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T Hc0 Hh HP Wf Hlens Hcnt K.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom.
  assert (Hcnt0 : mem_arr 2 R_segs M (sp + -136) 16 (cnt 0)).
  { eapply mem_arr_ext; [exact Hcnt|]. intros j Hj. cbn beta. unfold cntK. rewrite itm_count_k_0 by lia.
    rewrite it_zero_count_spec. reflexivity. }
  clear Hcnt. zrebase.
  zbr Rfd false.
  zbr Rfd false.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zalign.
  zstep Rfd. znot.
  zstep Rfd.
  zstep Rfd. znot.
  zstep Rfd. zsetreg (2 * codes) ltac:(symmetry; apply zext32_x2; lia).
  zstep Rfd.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
    eapply (count_loop_t (Z.to_nat codes) 0 Rx [] Mx MD T) end.
  all: try first [lia | assumption | close_pregs | zreg].
  all: intros; rewrite cntA_eq in K; eapply K; eassumption.
Qed.

Definition Kmax (bitsv : Z) (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', PR R' [] -> zget_l R' [] kA7 = bitsv -> zget_l R' [] kT0 = mx -> zget_l R' [] kT2 = cA 15 ->
    2 <= mx -> realizes R_segs (zcfg R_segs 138824 (zupd R' []) M MD) T.
Definition Klow (bitsv : Z) (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', PR R' [] -> zget_l R' [] kA7 = bitsv -> zget_l R' [] kT2 = cA 15 -> (forall j, 2 <= j <= 15 -> cA j = 0) ->
    realizes R_segs (zcfg R_segs 140620 (zupd R' []) M MD) T.

Lemma max_stage_2 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv -> zget_l Rb l kT2 = cA 15 ->
  (forall j, 2 < j <= 15 -> cA j = 0) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes R_segs (zcfg R_segs 138812 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T bitsv Hh HP LA7 LT2 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 2) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 2) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KL Rx) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 2) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 2); [lia | exact Hz | exact NZ].
    + unfold mxA. rewrite (mx_found _ 2); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_3 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv -> zget_l Rb l kT2 = cA 15 ->
  (forall j, 3 < j <= 15 -> cA j = 0) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes R_segs (zcfg R_segs 138796 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T bitsv Hh HP LA7 LT2 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 3) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 3) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_2 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 3) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 3); [lia | exact Hz | exact NZ].
    + unfold mxA. rewrite (mx_found _ 3); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_4 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv -> zget_l Rb l kT2 = cA 15 ->
  (forall j, 4 < j <= 15 -> cA j = 0) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes R_segs (zcfg R_segs 138780 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T bitsv Hh HP LA7 LT2 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 4) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 4) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_3 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 4) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 4); [lia | exact Hz | exact NZ].
    + unfold mxA. rewrite (mx_found _ 4); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_5 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv -> zget_l Rb l kT2 = cA 15 ->
  (forall j, 5 < j <= 15 -> cA j = 0) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes R_segs (zcfg R_segs 138764 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T bitsv Hh HP LA7 LT2 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 5) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 5) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_4 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 5) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 5); [lia | exact Hz | exact NZ].
    + unfold mxA. rewrite (mx_found _ 5); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_6 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv -> zget_l Rb l kT2 = cA 15 ->
  (forall j, 6 < j <= 15 -> cA j = 0) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes R_segs (zcfg R_segs 138748 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T bitsv Hh HP LA7 LT2 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 6) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 6) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_5 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 6) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 6); [lia | exact Hz | exact NZ].
    + unfold mxA. rewrite (mx_found _ 6); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_7 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv -> zget_l Rb l kT2 = cA 15 ->
  (forall j, 7 < j <= 15 -> cA j = 0) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes R_segs (zcfg R_segs 138732 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T bitsv Hh HP LA7 LT2 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 7) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 7) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_6 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 7) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 7); [lia | exact Hz | exact NZ].
    + unfold mxA. rewrite (mx_found _ 7); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_8 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv -> zget_l Rb l kT2 = cA 15 ->
  (forall j, 8 < j <= 15 -> cA j = 0) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes R_segs (zcfg R_segs 138716 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T bitsv Hh HP LA7 LT2 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 8) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 8) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_7 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 8) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 8); [lia | exact Hz | exact NZ].
    + unfold mxA. rewrite (mx_found _ 8); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_9 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv -> zget_l Rb l kT2 = cA 15 ->
  (forall j, 9 < j <= 15 -> cA j = 0) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes R_segs (zcfg R_segs 138700 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T bitsv Hh HP LA7 LT2 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 9) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 9) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_8 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 9) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 9); [lia | exact Hz | exact NZ].
    + unfold mxA. rewrite (mx_found _ 9); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_10 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv -> zget_l Rb l kT2 = cA 15 ->
  (forall j, 10 < j <= 15 -> cA j = 0) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes R_segs (zcfg R_segs 138684 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T bitsv Hh HP LA7 LT2 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 10) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 10) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_9 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 10) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 10); [lia | exact Hz | exact NZ].
    + unfold mxA. rewrite (mx_found _ 10); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_11 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv -> zget_l Rb l kT2 = cA 15 ->
  (forall j, 11 < j <= 15 -> cA j = 0) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes R_segs (zcfg R_segs 138668 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T bitsv Hh HP LA7 LT2 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 11) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 11) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_10 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 11) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 11); [lia | exact Hz | exact NZ].
    + unfold mxA. rewrite (mx_found _ 11); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_12 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv -> zget_l Rb l kT2 = cA 15 ->
  (forall j, 12 < j <= 15 -> cA j = 0) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes R_segs (zcfg R_segs 138652 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T bitsv Hh HP LA7 LT2 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 12) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 12) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_11 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 12) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 12); [lia | exact Hz | exact NZ].
    + unfold mxA. rewrite (mx_found _ 12); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_13 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv -> zget_l Rb l kT2 = cA 15 ->
  (forall j, 13 < j <= 15 -> cA j = 0) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes R_segs (zcfg R_segs 138636 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T bitsv Hh HP LA7 LT2 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 13) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 13) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_12 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 13) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 13); [lia | exact Hz | exact NZ].
    + unfold mxA. rewrite (mx_found _ 13); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_14 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv -> zget_l Rb l kT2 = cA 15 ->
  (forall j, 14 < j <= 15 -> cA j = 0) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes R_segs (zcfg R_segs 138620 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T bitsv Hh HP LA7 LT2 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 14) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 14) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_13 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 14) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 14); [lia | exact Hz | exact NZ].
    + unfold mxA. rewrite (mx_found _ 14); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma pb_al : pb mod 2 ^ 2 = 0 /\ 0 < pb /\ pb + 4 <= p + 144 /\ p + 120 <= pb.
Proof.
  pose proof C as C'. open_itc C'. unfold ZSEP in Hpb.
  assert (D : exists q, p = 16 * q). { apply Z.mod_divide in Hpal; [|lia_std]. destruct Hpal as [q Hq]. exists q. lia_std. }
  destruct D as [q Hq]. change (2 ^ 2) with 4.
  destruct Hpb as [E|E]; rewrite E; (split; [rewrite Hq | lia_std]).
  - replace (16 * q + 120) with ((4 * q + 30) * 4) by lia_std. apply Z_mod_mult.
  - replace (16 * q + 124) with ((4 * q + 31) * 4) by lia_std. apply Z_mod_mult.
Qed.

Lemma max_entry_t : forall Rb l M MD T av,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = av ->
  mem_arr 2 R_segs M (sp + -136) 16 cA -> mem_u32 R_segs M pb bits ->
  Kmax bits M MD T -> Klow bits M MD T ->
  realizes R_segs (zcfg R_segs 138588 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T av Hh HP LA7 Hcnt HB32 KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  pose proof pb_al as (PB4 & PB0 & PB1 & PB2).
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 15) as HRk.
  zrebase.
  zbr Rfd false.
  zstep Rfd. zsetreg 0 ltac:(symmetry; apply (land_mask0 pb 2); [lia_std | exact PB4]).
  zbr Rfd false.
  tstep Rfd.
  zstep Rfd. zsetreg bits ltac:(symmetry; apply swrap32_small; lia).
  destruct (Z.eq_dec (cA 15) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_14 Rx [] M MD T bits) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. replace jj with 15 by lia. exact Z0.
  - zbr Rfd false. zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 15); [lia | intros; lia | exact NZ].
    + unfold mxA. rewrite (mx_found _ 15); [lia | lia | intros; lia | exact NZ].
Qed.

#[local] Abbreviation mn := (mnA lf lens_ofs codes).
#[local] Abbreviation rt := (rootA lf lens_ofs codes bits).

Definition Kleft (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', PR R' [] -> zget_l R' [] kT0 = mx -> zget_l R' [] kT1 = mn -> zget_l R' [] kA7 = rt ->
    zget_l R' [] kT3 = cA 1 -> zget_l R' [] kT4 = (if mx =? 1 then 0 else 1) -> zget_l R' [] kT2 = cA 15 -> 1 <= mx ->
    realizes R_segs (zcfg R_segs 138888 (zupd R' []) M MD) T.
Definition Kmax0 (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', PR R' [] -> mx = 0 -> realizes R_segs (zcfg R_segs 140652 (zupd R' []) M MD) T.

Lemma mxmn_facts : 1 <= mx -> 1 <= mn <= mx /\ mx <= 15 /\ 1 <= rt <= 15 /\ mn <= rt /\
  rt = (let r := (if bits <? mx then bits else mx) in if mn <? r then r else mn).
Proof.
  intros H1. pose proof C as C'. open_itc C'. pose proof (mx_range (cntA lf lens_ofs codes)) as MR.
  pose proof (mn_range (cntA lf lens_ofs codes) mx ltac:(unfold mxA in *; lia_std)) as NR.
  unfold rootA, itm_root. unfold mnA in *. unfold mxA in *.
  set (mxv := itm_max (cntA lf lens_ofs codes)) in *. set (mnv := itm_min (cntA lf lens_ofs codes) mxv) in *.
  destruct (Z.ltb_spec mxv bits); destruct (Z.ltb_spec bits mxv); try lia_std;
    destruct (Z.ltb_spec mxv mnv); destruct (Z.ltb_spec bits mnv); destruct (Z.ltb_spec mnv mxv); destruct (Z.ltb_spec mnv bits); cbv zeta; lia_std.
Qed.

Lemma min_loop_t : forall fuel m Rb l M MD T r7,
  (Z.to_nat (mx - m) <= fuel)%nat -> 1 <= m < mx -> 2 <= mx <= 15 ->
  (forall jj, 1 <= jj < m -> cA jj = 0) ->
  m_halted MD = None -> PR Rb l ->
  zget_l Rb l kT1 = m -> zget_l Rb l kA6 = sp + -136 + 2 * m -> zget_l Rb l kT3 = mx - m ->
  zget_l Rb l kT0 = mx -> zget_l Rb l kA7 = r7 -> zget_l Rb l kT2 = cA 15 ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  (forall R', PR R' [] -> zget_l R' [] kT1 = mn -> zget_l R' [] kT0 = mx -> zget_l R' [] kA7 = r7 ->
     zget_l R' [] kT2 = cA 15 ->
     realizes R_segs (zcfg R_segs 138872 (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs 138844 (zupd Rb l) M MD) T.
Proof.
  induction fuel as [|fuel IH]; intros m Rb l M MD T r7 Hfuel Hm Hmx2 Hz Hh HP LT1 LA6 LT3 LT0 LA7 LT2 Hcnt K.
  { exfalso. lia. }
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range m) as HRm.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA m) 0) as [Z0|NZ].
  - zbr Rfd false.
    zstep Rfd. zsetreg (m + 1) ltac:(symmetry; apply swrap32_small; lia).
    zstep Rfd. zstep Rfd.
    destruct (Z.eq_dec (m + 1) mx) as [Hlast|Hmore].
    + zbr Rfd false.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
      all: try first [assumption | close_pregs | zreg].
      zregv. symmetry. unfold mnA. apply mn_all; [lia|].
      intros jj Hjj. destruct (Z.eq_dec jj m) as [->|]; [exact Z0 | apply Hz; lia].
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (IH (m + 1) Rx [] M MD T r7) end.
      all: try first [lia | assumption | close_pregs | zreg].
      intros jj Hjj. destruct (Z.eq_dec jj m) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
    all: try first [assumption | close_pregs | zreg].
    zregv. symmetry. unfold mnA. apply mn_found; [lia | lia | exact Hz | exact NZ].
Qed.

Lemma rootmin_t : forall Rb l M MD T,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bits -> zget_l Rb l kT0 = mx -> zget_l Rb l kT2 = cA 15 ->
  2 <= mx ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  Kleft M MD T ->
  realizes R_segs (zcfg R_segs 138824 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T Hh HP LA7 LT0 LT2 Hmx2 Hcnt KL.
  pose proof C as C'. open_itc C'. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 1) as HR1.
  pose proof (mxmn_facts ltac:(lia)) as (MN1 & MX15 & RT & MNRT & RTEQ).
  assert (STEP : forall r7, r7 = (if bits <? mx then bits else mx) -> 1 <= r7 <= 15 ->
    forall Rx lx, m_halted MD = None -> PR Rx lx -> zget_l Rx lx kA7 = r7 -> zget_l Rx lx kT0 = mx -> zget_l Rx lx kT2 = cA 15 ->
    realizes R_segs (zcfg R_segs 138832 (zupd Rx lx) M MD) T).
  { intros r7 Hr7 Hr7b Rx lx Hh' HP' XA7 XT0 XT2. open_pregs HP'. zkeys. zrebase.
    zstep Rfd. zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx' _ _) _ => eapply (min_loop_t (Z.to_nat mx) 1 Rx' [] M MD T r7) end.
    all: try first [lia | assumption | close_pregs | zreg].
    intros R' HP2 YT1 YT0 YA7 YT2. open_pregs HP2. zkeys. zrebase.
    tstep Rfd.
    zstep Rfd.
    destruct (Z.ltb_spec mn r7).
    - zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Ry _ _) _ => eapply (KL Ry) end.
      all: try first [assumption | close_pregs | zreg].
      + zregv. rewrite RTEQ. cbv zeta. subst r7. destruct (Z.ltb_spec mn (if bits <? mx then bits else mx)); lia.
      + zregv. destruct (Z.eqb_spec mx 1); lia.
    - zbr Rfd false. zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Ry _ _) _ => eapply (KL Ry) end.
      all: try first [assumption | close_pregs | zreg].
      + zregv. rewrite RTEQ. cbv zeta. subst r7. destruct (Z.ltb_spec mn (if bits <? mx then bits else mx)); lia.
      + zregv. destruct (Z.eqb_spec mx 1); lia. }
  open_pregs HP. zkeys. zrebase.
  destruct (Z.ltb_spec bits mx).
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (STEP bits _ _ Rx []) end.
    all: try first [assumption | close_pregs | zreg].
    all: destruct (Z.ltb_spec bits mx); lia.
  - zbr Rfd false. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (STEP mx _ _ Rx []) end.
    all: try first [assumption | close_pregs | zreg].
    all: destruct (Z.ltb_spec bits mx); lia.
  Unshelve. all: lia.
Qed.

Lemma maxlow_t : forall Rb l M MD T,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bits -> zget_l Rb l kT2 = cA 15 ->
  (forall jj, 2 <= jj <= 15 -> cA jj = 0) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  Kleft M MD T -> Kmax0 M MD T ->
  realizes R_segs (zcfg R_segs 140620 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T Hh HP LA7 LT2 Hz Hcnt KL K0.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 1) as HR1. pose proof (Hz 15 ltac:(lia)) as Z15.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 1) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K0 Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold mxA. apply mx_zero. intros jj Hjj. destruct (Z.eq_dec jj 1) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    assert (MX1 : mx = 1) by (unfold mxA; apply (mx_found _ 1); [lia | intros jj Hjj; apply Hz; lia | exact NZ]).
    pose proof (mxmn_facts ltac:(lia)) as (MN1 & MX15 & RT & MNRT & RTEQ).
    zstep Rfd.
    zstep Rfd. zbool.
    zstep Rfd. zstep Rfd.
    zbr Rfd true.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KL Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. rewrite RTEQ, MX1. cbv zeta. destruct (Z.ltb_spec bits 1); destruct (Z.ltb_spec mn 1); destruct (Z.ltb_spec mn bits); lia.
    + zregv. rewrite MX1. reflexivity.
Qed.

Lemma count_phase0_t : forall Rb l M MD T av,
  codes = 0 -> m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = av ->
  mem_arr 2 R_segs M (sp + -136) 16 (fun _ => 0) -> mem_u32 R_segs M pb bits ->
  Kmax0 M MD T ->
  realizes R_segs (zcfg R_segs 138492 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T av Hc0 Hh HP LA7 Hcnt HB32 K0.
  pose proof C as C'. open_itc C'. clear HtyC HtyD Hprom Hpb.
  assert (ZALL : forall jj, cA jj = 0).
  { intros jj. rewrite cntA_eq, Hc0. unfold cntK. rewrite itm_count_k_0 by lia. apply it_zero_count_spec. }
  assert (MX0 : mx = 0) by (unfold mxA; apply mx_zero; intros; apply ZALL).
  assert (Hcnt' : mem_arr 2 R_segs M (sp + -136) 16 cA).
  { eapply mem_arr_ext; [exact Hcnt|]. intros jj Hjj. cbn beta. symmetry. apply ZALL. }
  open_pregs HP. zkeys. zrebase.
  zbr Rfd true.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_entry_t Rx [] M MD T av) end.
  all: try first [assumption | close_pregs | zreg].
  - intros R' _ _ _ _ Hmx. exfalso. lia.
  - intros R' HP' XA7 XT2 _. eapply maxlow_t; try eassumption.
    + intros; apply ZALL.
    + intros R'' _ _ _ _ _ _ _ Hmx. exfalso. lia.
Qed.
End U7IT.
End FXG.

Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Section U7IT2.
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
Proof using C zc ret sp pb p wf cf bits nx codes lens_ofs lf. destruct ty; reflexivity. Qed.

Definition Kneg (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', PR R' [] -> zget_l R' [] kA6 = -1 ->
    itm_reject ty mx (it_left_check cntAr) = true -> 1 <= mx ->
    realizes R_segs (zcfg R_segs 140556 (zupd R' []) M MD) T.

Definition Koffs (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', PR R' [] -> zget_l R' [] kT0 = mx -> zget_l R' [] kT1 = mn -> zget_l R' [] kA7 = rt ->
    zget_l R' [] kT3 = cA 1 -> zget_l R' [] kT5 = cA 2 -> zget_l R' [] kT6 = cA 3 -> zget_l R' [] kS0 = cA 4 ->
    zget_l R' [] kS1 = cA 5 -> zget_l R' [] kS2 = cA 6 -> zget_l R' [] kS3 = cA 7 -> zget_l R' [] kS4 = cA 8 ->
    zget_l R' [] kS5 = cA 9 -> zget_l R' [] kS6 = cA 10 -> zget_l R' [] kS7 = cA 11 -> zget_l R' [] kS8 = cA 12 ->
    zget_l R' [] kS9 = cA 13 -> zget_l R' [] kS10 = cA 14 ->
    1 <= mx -> itm_reject ty mx (it_left_check cntAr) = false ->
    realizes R_segs (zcfg R_segs 139144 (zupd R' []) M MD) T.


Definition pregs6_t (R : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l R l kSP = sp + -208 /\ zget_l R l kGP = vgp /\ zget_l R l kTP = vtp /\ zget_l R l kA0 = cty ty /\
  zget_l R l kA1 = p + 152 + 2 * lens_ofs /\
  zget_l R l kA3 = p + 144 /\ zget_l R l kA4 = pb /\ zget_l R l kA5 = p + 792.
Ltac open_pregs6_t H := unfold pregs6_t in H;
  let a := fresh "LSP" in let b := fresh "LGP" in let c := fresh "LTP" in let d := fresh "LA0" in
  let e := fresh "LA1" in let g := fresh "LA3" in let h := fresh "LA4" in
  let i := fresh "LA5" in destruct H as (a & b & c & d & e & g & h & i).
Ltac close_pregs6_t := unfold pregs6_t; split_conj; zreg.
Lemma left_t : forall M MD T,
  m_halted MD = None -> mem_arr 2 R_segs M (sp + -136) 16 cA -> Kneg M MD T -> Koffs M MD T -> KLEFT M MD T.
Proof using C zc ret wf cf nx.
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
  m_halted MD = None -> mem_wr R_segs M (sp - 208) 208 ->
  (forall R' M', PR R' [] -> zget_l R' [] kT0 = mx -> zget_l R' [] kT1 = mn -> zget_l R' [] kA7 = rt -> zget_l R' [] kT2 = sp + -168 ->
     mpost R_segs M M' (sp + -166) (sp + -136) 0 0 ->
     mem_arr 2 R_segs M' (sp + -166) 15 (fun j => arr_get offsAr (j + 1)) ->
     1 <= mx -> itm_reject ty mx (it_left_check cntAr) = false ->
     realizes R_segs (zcfg R_segs 139268 (zupd R' []) M' MD) T) ->
  Koffs M MD T.
Proof using C zc ret wf cf nx.
  intros M MD T Hh Wf K. unfold Koffs.
  intros Rb HP LT0 LT1 LA7 LT3 LT5 LT6 LS0 LS1 LS2 LS3 LS4 LS5 LS6 LS7 LS8 LS9 LS10 Hmx HRJ.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear HtyC HtyD Hprom Hpb.
  assert (HRa : forall j, 0 <= cA j <= 288) by (intros j; pose proof (cA_range _ _ _ _ _ _ _ _ _ _ _ _ _ C j); lia).
  pose proof (mpost_stable R_segs M (sp + -166) (sp + -136) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X (sp + -166) (sp + -136) 0 0) M) by (apply mpost_refl).
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
  zget_l Rb l kA2 = - (p + 152 + 2 * lens_ofs) + -1 -> zget_l Rb l kT5 = - (sp + -168) + -1 ->
  zget_l Rb l kT3 = 0 -> zget_l Rb l kT4 = 16 -> zget_l Rb l kS0 = 1 ->
  zget_l Rb l kT0 = mx -> zget_l Rb l kT1 = mn -> zget_l Rb l kA7 = rt ->
  it_sort_ok (lensA lf) lens_ofs codes offsAr 288 = true ->
  mem_wr R_segs M (sp - 208) 208 -> mem_wr R_segs M p 7160 ->
  mem_arr 2 R_segs M (p + 152) 320 lf ->
  mem_arr 2 R_segs M (sp + -166) 15 (fun j => arr_get (SKo i) (j + 1)) ->
  mem_arr 2 R_segs M (p + 792) 288 (arr_get (SKw i)) ->
  (forall R' M', pregs6_t R' [] -> zget_l R' [] kT0 = mx -> zget_l R' [] kT1 = mn -> zget_l R' [] kA7 = rt ->
     mpost R_segs M M' (sp + -166) (sp + -136) (p + 792) (p + 1368) ->
     mem_wr R_segs M' (sp - 208) 208 -> mem_wr R_segs M' p 7160 ->
     mem_arr 2 R_segs M' (p + 152) 320 lf ->
     mem_arr 2 R_segs M' (p + 792) 288 (arr_get (SKw codes)) ->
     realizes R_segs (zcfg R_segs 139416 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 139320 (zupd Rb l) M MD) T.
Proof using C zc ret cf nx.
  induction fuel as [|fuel IH]; intros i Rb l M MD T Hfuel Hi Hh HP LA6 LT6 LT2 LA2 LT5 LT3 LT4 LS0 LT0 LT1 LA7 SOK Wf Wp Hlens Hoffs Hwork K.
  { exfalso. lia. }
  pose proof C as C'. open_itc C'. open_pregs6_t HP. zkeys. clear HtyC HtyD Hprom Hpb.
  pose proof (Hlens15 i ltac:(lia)) as Hl15. pose proof (Hlf (lens_ofs + i) ltac:(lia)) as Hl16.
  assert (HOr : forall j, 0 <= j < 16 -> 0 <= arr_get (SKo i) j < 65536) by (intros j _; unfold offsA; apply itm_sort_k_offs_range).
  pose proof (mpost_stable R_segs M (sp + -166) (sp + -136) (p + 792) (p + 1368) ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X (sp + -166) (sp + -136) (p + 792) (p + 1368)) M) by (apply mpost_refl).
  pose proof (lnot_val_mod' (p + 152 + 2 * lens_ofs) ltac:(lia)) as Hn1.
  pose proof (lnot_val_mod' (sp + -168) ltac:(lia)) as Hn2.
  assert (J : forall RJ MJ, pregs6_t RJ [] ->
    zget_l RJ [] kA6 = i -> zget_l RJ [] kT6 = codes -> zget_l RJ [] kT2 = sp + -168 ->
    zget_l RJ [] kA2 = - (p + 152 + 2 * lens_ofs) + -1 -> zget_l RJ [] kT5 = - (sp + -168) + -1 ->
    zget_l RJ [] kT3 = 0 -> zget_l RJ [] kT4 = 16 -> zget_l RJ [] kS0 = 1 ->
    zget_l RJ [] kT0 = mx -> zget_l RJ [] kT1 = mn -> zget_l RJ [] kA7 = rt ->
    mpost R_segs M MJ (sp + -166) (sp + -136) (p + 792) (p + 1368) ->
    mem_wr R_segs MJ (sp - 208) 208 -> mem_wr R_segs MJ p 7160 ->
    mem_arr 2 R_segs MJ (p + 152) 320 lf ->
    mem_arr 2 R_segs MJ (sp + -166) 15 (fun j => arr_get (SKo (i + 1)) (j + 1)) ->
    mem_arr 2 R_segs MJ (p + 792) 288 (arr_get (SKw (i + 1))) ->
    realizes R_segs (zcfg R_segs 139312 (zupd RJ []) MJ MD) T).
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
    zsetreg 1 ltac:(rewrite Z.mod_small by lia; destruct (Z.ltb_spec (p + 792 + 2 * arr_get (SKo i) (lf (lens_ofs + i))) 1); [lia | reflexivity]).
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
  mem_wr R_segs M (sp - 208) 208 -> mem_wr R_segs M p 7160 ->
  mem_arr 2 R_segs M (p + 152) 320 lf ->
  mem_arr 2 R_segs M (sp + -166) 15 (fun j => arr_get offsAr (j + 1)) ->
  mem_arr 2 R_segs M (p + 792) 288 wf ->
  (forall R' M', pregs6_t R' [] -> zget_l R' [] kT0 = mx -> zget_l R' [] kT1 = mn -> zget_l R' [] kA7 = rt ->
     mpost R_segs M M' (sp + -166) (sp + -136) (p + 792) (p + 1368) ->
     mem_wr R_segs M' (sp - 208) 208 -> mem_wr R_segs M' p 7160 ->
     mem_arr 2 R_segs M' (p + 152) 320 lf ->
     mem_arr 2 R_segs M' (p + 792) 288 (arr_get work1Ar) ->
     realizes R_segs (zcfg R_segs 139416 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 139268 (zupd Rb l) M MD) T.
Proof using C zc ret cf nx.
  intros Rb l M MD T Hh HP LT0 LT1 LA7 LT2 Hmx SOK Wf Wp Hlens Hoffs Hwork K.
  pose proof C as C'. open_itc C'. clear HtyC HtyD Hprom Hpb.
  assert (Hc0 : 0 < codes).
  { destruct (Z.eq_dec codes 0) as [E|]; [|lia]. exfalso. enough (mx = 0) by lia. unfold mxA. apply mx_zero.
    intros j _. rewrite cntA_eq, E. unfold cntK. rewrite itm_count_k_0 by lia. apply it_zero_count_spec. }
  assert (Hoffs0 : mem_arr 2 R_segs M (sp + -166) 15 (fun j => arr_get (SKo 0) (j + 1))).
  { rewrite itm_sort_k_0 by lia. cbn [fst]. exact Hoffs. }
  assert (Hwork0 : mem_arr 2 R_segs M (p + 792) 288 (arr_get (SKw 0))).
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
End U7IT2.
End FXG.
