(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Cfg ImageA.
From OSSVerify.Proofs.openssl.bndiv.lib Require Import TopE TopSides TopRows TopBndivPlain.  (* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bndiv.lib.Common Require Import ClassifierRows.
From OSSVerify.Proofs.openssl.bndiv.lib.A Require Import RT_iface RT_rep RT_closed RT_io D_defs D_libiface I_iodefs X_xdefs TopA_io.
From OSSVerify.Proofs.openssl.bndiv.lib.BnAsan Require Import LibaA.
From OSSVerify.Proofs.openssl.bndiv.lib.BnAsan Require FuzzOneRTA.   (* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bndiv.lib.HXA Require HxaClosed.
From OSSVerify.Proofs.openssl.bndiv.lib.AxBdA Require Import BdAParams.
From OSSVerify.Proofs.openssl.bndiv.lib.AxA Require Import TargetA.
Require OSSVerify.openssl.bndiv.images.Plain.
Require OSSVerify.openssl.bndiv.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Notation imgP := (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs) (only parsing).
Notation imgA := (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs) (only parsing).

Section Debt.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Let INIT : init_cps RTA (LIBA RTA) := HxaClosed.init_cps_RTA.
  Let FUZZ : fuzz_one_cps' RTA (LIBA RTA) := FuzzOneRTA.fuzz_one_cps_RTA.   (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma main_asan : forall (argv : list (list byte)) (fs : Fs.Fs) c, valid_argv argv ->
    START RTA OUT_repA ERR_repA XENVA lib_startA argv fs c -> AS.ShapeAlg.realizes asegs c (Canon.canonT (Prog.argv_Z argv) fs).
  Proof.
    intros argv fs c Hva HS.
    exact (main_rta rta_contracts_all rta_io (LIBA RTA) INIT FUZZ (liba_frameA RTA) (liba_exitA RTA) argv fs Hva c HS).
  Qed.

  (* [comment removed for export] *)
  Lemma side_asan : side_canon_off ncfg Tc imgA target_alloc_limit.
  Proof. intros en inp He Hi. exact (target_canon_A_main main_asan en inp He Hi). Qed.

  (* [comment removed for export] *)
  Theorem base_bndiv_asan :
    strong_universal_error_free_T_scfg_budgets (mkSpuriousCfg false true true true true true)
      SanitizerBudgets.lim_source SanitizerBudgets.lim_target imgP imgA.
  Proof. exact (glue_scfg_budgets_lim ncfg Tc _ _ _ _ side_plain_san side_asan). Qed.  (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End Debt.

(* [comment removed for export] *)
Check (base_bndiv_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    (mkSpuriousCfg false true true true true true)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.bndiv.images.Plain.M.loaded_segments OSSVerify.openssl.bndiv.images.Plain.M.init_pc OSSVerify.openssl.bndiv.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.bndiv.images.Asan.M.loaded_segments OSSVerify.openssl.bndiv.images.Asan.M.init_pc OSSVerify.openssl.bndiv.images.Asan.M.phdrs)).
(* [comment removed for export] *)
