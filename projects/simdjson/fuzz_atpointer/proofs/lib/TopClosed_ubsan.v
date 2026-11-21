(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (comments brought up to date with the port). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Ceiling Cfg.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib Require Import TopLevel Obligations ProofBase TopFinal_plain TopFinal_ubsan.
From OSSVerify.simdjson.fuzz_atpointer.images Require Import Plain.
From OSSVerify.simdjson.fuzz_atpointer.images Require Import Ubsan.
Require OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P.Rnd OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P.Z41 OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.U.Z41.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma client_P_closed : client_P_stmt.
Proof. intros CE RN. exact (@OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P.Z41.rfuzz_one_closed CE RN). Qed.
Lemma client_U_closed : client_U_stmt.
Proof. intros CE RN. exact (@OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.U.Z41.rfuzz_one_closed CE RN). Qed.


(* SUPERSEDED 2026-11-06.  The old text here read:

     (* The kernel pin (Main's ruling, 2026-11-04; TopLevel.v): until the model's retarget
        proves [kernel_pinned] from [valid_input_either], it is this section's hypothesis. *)
     Section Pinned.
     Hypothesis Hkernel : kernel_pinned.
     ... Theorem off_ubsan ... Theorem base_ubsan ...
     End Pinned.

   The 11-04 ruling predates the measurement that at 75d69e00 the published
   statement quantifies over the five FREE kernel fields, so [kernel_pinned]
   cannot be discharged at the top at all -- it is not that the retarget had
   not landed yet, it is that the pin is false.  The section therefore shipped
   [base_ubsan : kernel_pinned -> ...], which [Theorems.v:38] applies BARE; that
   mismatch was the visible symptom.  No section and no hypothesis now: nothing
   below [Theorems.v] carries a kernel premise. *)
Theorem off_ubsan : strong_universal_error_free_T_scfg (mkSpuriousCfg false true true true true true)
  (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
  (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof. exact (TopFinal_ubsan.off_ubsan_cfg client_P_closed client_U_closed). Qed.
Theorem base_ubsan :
  strong_universal_error_free_T_scfg_budgets_abort (mkSpuriousCfg false true true true true true) ShippedBudgets.lim_source ShippedBudgets.lim_target
  (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
  (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof. exact (TopFinal_ubsan.base_ubsan_cfg client_P_closed client_U_closed). Qed.
