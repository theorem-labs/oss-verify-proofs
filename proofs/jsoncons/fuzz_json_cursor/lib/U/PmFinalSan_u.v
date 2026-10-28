(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import ShapeAlg DivergeSim SpinAlg SpinAlgX ShapeEF Spec BigintSpec HeapIface LibIface LibIfaceFp KillFree VmLimitFrame.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Bridge Require PmHeapInst10_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Pm10DrvLibL_u Pm10HeapBridge_u PmFinal_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require PropExec.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation IMG_csrc :=
  (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc
           Ubsan.M.phdrs).

Definition half_ok (scfg : SpuriousCfg) (img : Image) (lim : Z) (en : ExecEntry) (inp : ProcInput) (T : TSet) : Prop :=
  error_free_unkilled (run_scfg scfg img lim en inp)
  /\ forall tr, bh_traces (run_scfg scfg img lim en inp) tr <-> T tr.

Lemma base_abort_of_halves : forall scfg lim_s lim_t src tgt en_s en_t inp T,
  half_ok scfg src lim_s en_s inp T -> half_ok scfg tgt lim_t en_t inp T ->
  strong_equiv_error_free_budgets_scfg_abort scfg lim_s lim_t src tgt en_s en_t inp.
Proof.
  intros scfg lim_s lim_t src tgt en_s en_t inp T [HsE HsT] [HtE HtT].
  split; [exact HsE | split; [exact HtE |]].
  intro tr. rewrite (HsT tr), (HtT tr). reflexivity.
Qed.

Lemma half_ok_of_srealizes : forall scfg segs pc ph sp brk0 mb rnd lim inp T,
  srealizes segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  Safe segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) ->
  kill_free T ->
  half_ok scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp T.
Proof.
  intros scfg segs pc ph sp brk0 mb rnd lim inp T Hs Hsafe HK. split.
  - exact (srealizes_error_free_unkilled scfg segs pc ph sp brk0 mb rnd lim inp T Hs Hsafe HK).
  - intro tr. exact (srealizes_traces_iff scfg segs pc ph sp brk0 mb rnd lim inp T tr Hs Hsafe).
Qed.

Section FPX_1.
#[local] Existing Instance PropExec.fx0.

Section Src.

  Variable Lay0F : word -> lib_layout.
  Variable LS0F : word -> lib_statics.
  Hypothesis DLL0 : forall sp, valid_sp sp -> Pm10DrvLibL_u.drv_lib_layout (Lay0F sp) (PmHeapInst10_u.L0 (bv_unsigned sp)).
  Hypothesis LIB0 : forall sp, valid_sp sp -> lib_iface_ok_fp (Lay0F sp) PmFinal_u.cfg0 (PmHeapInst10_u.HI0 (bv_unsigned sp)) (LS0F sp).
  Hypothesis LX0 : forall sp, valid_sp sp -> Pm10DrvLibL_u.lib_exit_ok (LS0F sp).
  Hypothesis BUD0 : PmFinal_u.budget0_ok Lay0F.

  Lemma src11_srealizes_lim : forall lim sp brk mb rnd inp,
    valid_entry IMG_csrc (mkEntry sp brk mb rnd) inp -> valid_input_abort inp ->
    srealizes Ubsan.M.loaded_segments PmFinal_u.cfg0
      (init_config Ubsan.M.loaded_segments Ubsan.M.init_pc
                   Ubsan.M.phdrs sp brk mb rnd lim inp)
      (spec (in_argv inp) (in_fs inp)).
  Proof.
    intros lim sp brk mb rnd inp Hen Hvalid.
    pose proof (Pm10HeapBridge_u.src0_realizes_spec_heap_lim PmFinal_u.cfg0 eq_refl eq_refl Lay0F LS0F DLL0 LIB0 LX0 BUD0 lim) as SRC.
    pose proof (valid_input_abort_va_size _ Hvalid) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
    destruct Hen as [Hrsp [Hrbrk [Hrmb Hrfit]]].
    destruct Hvalid as (Hargv & Henvp & Hfs & _ & Hcreds & _).
    exact (SRC sp brk mb rnd inp Hrsp Hrbrk Hrmb Hrfit Hargv Henvp Hfs Hcreds).
  Qed.

  Theorem src11_half_wb : forall lim en inp,
    valid_entry IMG_csrc en inp -> valid_input_abort inp ->
    source_within_budget_scfg PmFinal_u.cfg0 lim IMG_csrc en inp ->
    half_ok PmFinal_u.cfg0 IMG_csrc lim en inp (spec (in_argv inp) (in_fs inp)).
  Proof.
    intros lim [sp brk mb rnd] inp Hen Hvalid Hwb.
    apply half_ok_of_srealizes.
    - exact (src11_srealizes_lim lim sp brk mb rnd inp Hen Hvalid).
    - apply Safe_init_within_budget. exact Hwb.
    - apply kill_free_spec.
  Qed.

  Theorem src11_half_big : forall lim en inp,
    valid_entry IMG_csrc en inp -> valid_input_abort inp ->
    nbr_limit <= lim ->
    half_ok PmFinal_u.cfg0 IMG_csrc lim en inp (spec (in_argv inp) (in_fs inp)).
  Proof.
    intros lim [sp brk mb rnd] inp Hen Hvalid Hbig.
    apply half_ok_of_srealizes.
    - exact (src11_srealizes_lim lim sp brk mb rnd inp Hen Hvalid).
    - apply Safe_init_big. exact Hbig.
    - apply kill_free_spec.
  Qed.

  Theorem san_base_of_target_half : forall (tgt : Image),
    (forall en_t inp, valid_entry tgt en_t inp -> valid_input_abort inp ->
       half_ok PmFinal_u.cfg0 tgt SanitizerBudgets.lim_target en_t inp (spec (in_argv inp) (in_fs inp))) ->
    strong_universal_error_free_T_scfg_budgets_abort PmFinal_u.cfg0 SanitizerBudgets.lim_source SanitizerBudgets.lim_target IMG_csrc tgt.
  Proof.
    intros tgt HT en_s en_t inp Hens Hent Hvalid Hwb.
    exact (base_abort_of_halves _ _ _ _ _ _ _ _ _ (src11_half_wb _ en_s inp Hens Hvalid Hwb) (HT en_t inp Hent Hvalid)).
  Qed.

  Theorem shipped_base_of_target_half : forall (tgt : Image),
    (forall en_t inp, valid_entry tgt en_t inp -> valid_input_abort inp ->
       half_ok PmFinal_u.cfg0 tgt ShippedBudgets.lim_target en_t inp (spec (in_argv inp) (in_fs inp))) ->
    strong_universal_error_free_T_scfg_budgets_abort PmFinal_u.cfg0 ShippedBudgets.lim_source ShippedBudgets.lim_target IMG_csrc tgt.
  Proof.
    intros tgt HT en_s en_t inp Hens Hent Hvalid _.
    exact (base_abort_of_halves _ _ _ _ _ _ _ _ _ (src11_half_big _ en_s inp Hens Hvalid nbr_limit_source) (HT en_t inp Hent Hvalid)).
  Qed.
End Src.
End FPX_1.
