From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Plain.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib Require Import TopE TopSides.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib Require PSide USide.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1gm.

Notation imgS := (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs) (only parsing).
Notation imgU := (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs) (only parsing).

Theorem ubsan_agree : strong_universal_error_free_T_scfg_budgets_abort (alloc_only_cfg false)
  ShippedBudgets.lim_source ShippedBudgets.lim_target imgS imgU.
Proof.
exact (glue_budgets_abort_at Tc imgS imgU ShippedBudgets.lim_source ShippedBudgets.lim_target
  PSide.P_side_closed (U_side (USide.HU_proof U.X1gm.harness_proof_final)) Tc_nokill).
Qed.

