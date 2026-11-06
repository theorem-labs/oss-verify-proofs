(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import HeapIface LibIface L5Defs
     L5DivSpecs L5DivSpecsU L5UnwindSpecs L5UnwindSpecsU L5Top L5TopU L5TopBind L5TopBindU BigintFinal BigintFinalA
     BigintBaseH.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Bridge Require Import HeapInst0 HeapInst1.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Theorem fuzz_bigint_ubsan_abort_modulo_divide :
  OPMOD1_src0 -> OPMOD2_src0 -> OPMOD1_ub0 -> OPMOD2_ub0 ->
  strong_universal_error_free_T_scfg_budgets_abort cfg0 ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc
             Plain.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
  intros O1 O2 O1U O2U.
  exact (fuzz_bigint_ubsan_final_abort (LIB0_of_divide O1 O2) (LIB1_of_divide O1U O2U)).
Qed.
