(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Cfg. 
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
From OSSVerify.Proofs.openssl.bignum.lib Require Import TopE TopSides TopRows TopBignumPlain.
From OSSVerify.Proofs.openssl.bignum.lib.Common Require Import ClassifierRows.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require BnTree BgExp.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import RT_iface RT_rep RT_closed RT_io D_defs D_libiface I_iodefs X_xdefs TopA_io.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import LibaBg.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require ARun UnwindA EdgesInstA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require ExpKitA ExpKitAF W_fuzzA FuzzTopA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require ExpClosedF.
From OSSVerify.Proofs.openssl.bignum.lib.BgHXB Require HxbClosed.
From OSSVerify.Proofs.openssl.bignum.lib.BgAxBdB Require Import BdBParams.
From OSSVerify.Proofs.openssl.bignum.lib.BgAxB Require Import TargetB.

Require OSSVerify.openssl.bignum.images.Plain.
Require OSSVerify.openssl.bignum.images.AsanUbsan.




Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation imgP := (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs) (only parsing).
Notation imgB := (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs) (only parsing).





Lemma FUZZ_closed : fuzz_one_cps' RTA (LIBA RTA).
Proof.
  apply (FuzzTopA.fuzz_one_cps_RTA_of_exp ExpClosedF.EXPC_STACK ExpClosedF.EXPC_COST ExpClosedF.SIMPLEC_STACK ExpClosedF.SIMPLEC_COST 4 2).
  - exact ExpClosedF.EXPC_STACK_ok.
  - exact ExpClosedF.SIMPLEC_STACK_ok.
  - exact ExpClosedF.EXPC_COST_ok.
  - exact ExpClosedF.SIMPLEC_COST_ok.
  - lia.
  - lia.
  - apply FuzzTopA.FUZZ_TOTAL_le. exact ExpClosedF.EXPC_TOTAL_ok.
  - exact (@ExpClosedF.BN_mod_exp_closedA EdgesInstA.UK_A EdgesInstA.BE_A).
  - exact (@ExpClosedF.BN_mod_exp_simple_closed2A EdgesInstA.UK_A EdgesInstA.BE_A).
Qed.

Section Debt.

  Let FUZZ : fuzz_one_cps' RTA (LIBA RTA) := FUZZ_closed.

  Let INIT : init_cps RTA (LIBA RTA) := HxbClosed.init_cps_RTA.

  Lemma main_both : forall (argv : list (list byte)) (fs : Fs.Fs) c, valid_argv argv ->
    START RTA OUT_repA ERR_repA XENVA lib_startA argv fs c -> AS.ShapeAlg.realizes bgbsegs c (Canon.canonT (Prog.argv_Z argv) fs).
  Proof.
    intros argv fs c Hva HS.
    exact (main_rta rta_contracts_all rta_io (LIBA RTA) INIT FUZZ (liba_frameA RTA) (liba_exitA RTA) argv fs Hva c HS).
  Qed.

  Lemma side_both : side_canon_off ncfg Tc imgB target_alloc_limit.
  Proof. intros en inp He Hi. exact (target_canon_B_main main_both en inp He Hi). Qed.

  Theorem base_bignum_both :
    strong_universal_error_free_T_scfg_budgets (mkSpuriousCfg false true true true true true)
      SanitizerBudgets.lim_source SanitizerBudgets.lim_target imgP imgB.
  Proof. exact (glue_scfg_budgets_lim ncfg Tc _ _ _ _ side_plain_bg_san side_both). Qed.

  Section Rows.




  End Rows.

  Check (base_bignum_both :
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
      (mkSpuriousCfg false true true true true true)
      LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
      LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
      (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.bignum.images.Plain.M.loaded_segments OSSVerify.openssl.bignum.images.Plain.M.init_pc OSSVerify.openssl.bignum.images.Plain.M.phdrs)
      (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.bignum.images.AsanUbsan.M.loaded_segments OSSVerify.openssl.bignum.images.AsanUbsan.M.init_pc OSSVerify.openssl.bignum.images.AsanUbsan.M.phdrs)).
End Debt.


