(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* ubsan_agrees from its two halves (rename of PmXasanBaseW): the source half xsrc_half16 at ShippedBudgets.lim_source
   and the target half, the Section hypothesis TGTU : pm_xubsan_tgt_stmt cfgU PHI0U. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import ShapeAlg SpinAlg ShapeEF KillFree VmLimitFrame Spec BigintSpec HalfOk SpecG.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require PropExec Pm6DrvD.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmXubsanStmt PmXsrcHalf16.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require PmPhiX_s34.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PmXubsanBaseW.
Import PmXubsanStmt.
Abbreviation IMG_xsrc := (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs).

Lemma cfg_src_eq : PmPhiX_s34.PmPhiX16.cfg0 = cfgU.  Proof. reflexivity. Qed.

Lemma payload_eq : forall data, Pm6DrvD.payload data = payloadU data.
Proof. intros data. reflexivity. Qed.

Section FPX_1.
#[local] Existing Instance PropExec.fx0.
Section Glue.
  Hypothesis TGTU : pm_xubsan_tgt_stmt cfgU PHI0U.

  Theorem xubsan_half : forall en_s en_t inp,
    valid_entry IMG_xsrc en_s inp -> valid_entry IMG_xubsan en_t inp -> valid_input_abort inp ->
    ~ run_scfg_budget_refused cfgU IMG_xsrc ShippedBudgets.lim_source en_s inp ->
    half_ok cfgU IMG_xubsan ShippedBudgets.lim_target en_t inp (spec (in_argv inp) (in_fs inp)).
  Proof.
    intros [ssp sbrk smb srnd] [sp brk mb rnd] inp Hens Hent Hvalid Hwb.
    pose proof (valid_input_abort_va_size _ Hvalid) as Hsv48.
    pose proof Hent as Hent'. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent'. destruct Hent' as [Hsp [Hbrk [Hmb Hfit]]].
    pose proof Hvalid as (Hargv & Henvp & Hfs & _ & Hcreds & _ & _ & Hhw & _).
    apply half_ok_of_srealizes.
    - apply (TGTU sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hargv Henvp Hfs Hcreds Hhw Hsv48).
      intros a0s path Hinargv. unfold phi_okU. intros Hlen Hne Hnd data Hlk Hhdr.
      rewrite <- payload_eq.
      exact (PmXsrcHalf16.phi_of_premise16 ssp sbrk smb srnd inp Hens Hvalid Hwb a0s path data Hinargv Hlen Hne Hnd Hlk Hhdr).
    - apply Safe_init_big. exact nbr_limit_target.
    - apply kill_free_spec.
  Qed.

  Theorem xubsan_base :
    strong_universal_error_free_T_scfg_budgets_abort cfgU ShippedBudgets.lim_source ShippedBudgets.lim_target IMG_xsrc IMG_xubsan.
  Proof.
    apply (base_abort_of_halves_dep cfgU _ _ IMG_xsrc IMG_xubsan (fun inp => spec (in_argv inp) (in_fs inp))).
    - exact PmXsrcHalf16.xsrc_half16.
    - exact xubsan_half.
  Qed.
End Glue.
End FPX_1.
End PmXubsanBaseW.
