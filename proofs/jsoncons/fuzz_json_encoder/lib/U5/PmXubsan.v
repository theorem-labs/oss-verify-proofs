(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Root of ubsan_agrees: the statement of Proof.v's ubsan theorem, from the ubsan target half
   (PmXubsanTgtLay.pm_xubsan_tgt0 over the library instance PmLibInstU.lib_iface0U). *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require PropExec.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmXubsanStmt PmXubsanBaseW.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require PmXubsanTgtLay.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmInteg Require PmLibInstU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PmXubsan.
Section S.
#[local] Existing Instance PropExec.fx0.

Theorem xubsan_top :
  strong_universal_error_free_T_scfg_budgets_abort (mkSpuriousCfg false true true true true true) ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
  exact (PmXubsanBaseW.xubsan_base
           (PmXubsanTgtLay.PmXubsanTgtLay.pm_xubsan_tgt0 PmLibInstU.PmLibInstU.lib_iface0U)).
Qed.
End S.
End PmXubsan.
