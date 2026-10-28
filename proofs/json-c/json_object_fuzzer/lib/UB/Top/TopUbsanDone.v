From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UHdY UTargetJoP.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require TopUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma target_lim_ge : (2 ^ 31 <= target_alloc_limit)%Z.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma tgt_ubsan_realizes_of_target : UHdY.target_P -> TopUbsan.TGT_UBSAN_REALIZES.
Proof. intros TGT. exact (UHdY.drv_realizes_P_lim target_alloc_limit target_lim_ge TGT). Qed.

Theorem json_object_ubsan_ba_closed :
LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_abort
(LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true)
LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
(LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.json_c.json_object_fuzzer.images.Plain.M.loaded_segments OssFuzzTheorems.json_c.json_object_fuzzer.images.Plain.M.init_pc OssFuzzTheorems.json_c.json_object_fuzzer.images.Plain.M.phdrs)
(LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.M.loaded_segments OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.M.init_pc OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.M.phdrs).
Proof. exact (TopUbsan.json_object_ubsan_ba (tgt_ubsan_realizes_of_target UTargetJoP.target_P2_proof)). Qed.
