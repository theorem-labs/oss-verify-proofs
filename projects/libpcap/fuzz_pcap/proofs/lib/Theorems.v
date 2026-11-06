(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: added the halting theorems of the ASan and ASan+UBSan builds, halts_allowed_libpcap_fuzz_pcap_halts_asan and halts_allowed_libpcap_fuzz_pcap_halts_both, with the Requires of their proofs. *)
(* The three equivalence theorems for libpcap, with their proofs.

   Each theorem states that the uninstrumented build (the Src_ image) and one
   sanitizer build (the Tgt_ image: ASan, UBSan, or both) are equivalent and
   error-free, at the statement that the checkers in ../Checker seal. Their
   names and types must not change.

   This file is the graded Proof.v reduced to these three theorems and the
   declarations of the graded Proof.v that they use. The other theorems of the
   graded run are removed, with the Requires that only they used. *)

(* [comment removed for export] *)

From Stdlib Require Import NArith List QArith.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require LinuxProcessSemantics.EquivalenceDefinition.MustExit.
Require LinuxProcessSemantics.EquivalenceDefinition.FinInput.
Require LinuxProcessSemantics.EquivalenceDefinition.Classifier.
Require LinuxProcessSemantics.EquivalenceDefinition.Measure.
Require LinuxProcessSemantics.EquivalenceDefinition.PatchClassifySpec.
Require LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.
Require OSSVerify.libpcap.fuzz_pcap.images.Plain.
Require OSSVerify.libpcap.fuzz_pcap.images.Asan.
Require OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Require OSSVerify.libpcap.fuzz_pcap.images.AsanUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top Require Final_ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top Require Final_asan_top.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top Require Final_both_top.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top Require Halts_plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top Require Halts_ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top Require Halts_asan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top Require Halts_both.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Module SpuriousCfgM <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true.
End SpuriousCfgM.

Module HaltsCfgForcedOnly <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.forced_only_cfg.
End HaltsCfgForcedOnly.

Module LibpcapFuzzBothHaltsPlainExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End LibpcapFuzzBothHaltsPlainExits.

Module LibpcapFuzzBothHaltsAsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End LibpcapFuzzBothHaltsAsanExits.

Module LibpcapFuzzBothHaltsUbsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End LibpcapFuzzBothHaltsUbsanExits.

Module LibpcapFuzzBothHaltsBothExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End LibpcapFuzzBothHaltsBothExits.

Module LibpcapFuzzFilterHaltsPlainExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End LibpcapFuzzFilterHaltsPlainExits.

Module LibpcapFuzzFilterHaltsAsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End LibpcapFuzzFilterHaltsAsanExits.

Module LibpcapFuzzFilterHaltsUbsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End LibpcapFuzzFilterHaltsUbsanExits.

Module LibpcapFuzzFilterHaltsBothExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End LibpcapFuzzFilterHaltsBothExits.

Module LibpcapFuzzPcapHaltsPlainExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End LibpcapFuzzPcapHaltsPlainExits.

Module LibpcapFuzzPcapHaltsAsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End LibpcapFuzzPcapHaltsAsanExits.

Module LibpcapFuzzPcapHaltsUbsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End LibpcapFuzzPcapHaltsUbsanExits.

Module LibpcapFuzzPcapHaltsBothExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End LibpcapFuzzPcapHaltsBothExits.

Theorem strong_universal_error_free_fuzz_pcap_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.libpcap.fuzz_pcap.images.Plain.M.loaded_segments OSSVerify.libpcap.fuzz_pcap.images.Plain.M.init_pc OSSVerify.libpcap.fuzz_pcap.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.libpcap.fuzz_pcap.images.Asan.M.loaded_segments OSSVerify.libpcap.fuzz_pcap.images.Asan.M.init_pc OSSVerify.libpcap.fuzz_pcap.images.Asan.M.phdrs).
Proof.
  exact OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top.Final_asan_top.fuzz_pcap_asan_main.
Qed.

Theorem strong_universal_error_free_fuzz_pcap_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.libpcap.fuzz_pcap.images.Plain.M.loaded_segments OSSVerify.libpcap.fuzz_pcap.images.Plain.M.init_pc OSSVerify.libpcap.fuzz_pcap.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.libpcap.fuzz_pcap.images.Ubsan.M.loaded_segments OSSVerify.libpcap.fuzz_pcap.images.Ubsan.M.init_pc OSSVerify.libpcap.fuzz_pcap.images.Ubsan.M.phdrs).
Proof.
  exact OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top.Final_ubsan.fuzz_pcap_ubsan_main.
Qed.

Theorem strong_universal_error_free_fuzz_pcap_both :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.libpcap.fuzz_pcap.images.Plain.M.loaded_segments OSSVerify.libpcap.fuzz_pcap.images.Plain.M.init_pc OSSVerify.libpcap.fuzz_pcap.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.libpcap.fuzz_pcap.images.AsanUbsan.M.loaded_segments OSSVerify.libpcap.fuzz_pcap.images.AsanUbsan.M.init_pc OSSVerify.libpcap.fuzz_pcap.images.AsanUbsan.M.phdrs).
Proof.
  exact OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top.Final_both_top.fuzz_pcap_both_main.
Qed.

Theorem halts_allowed_libpcap_fuzz_pcap_halts_plain :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LibpcapFuzzPcapHaltsPlainExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.libpcap.fuzz_pcap.images.Plain.M.loaded_segments OSSVerify.libpcap.fuzz_pcap.images.Plain.M.init_pc OSSVerify.libpcap.fuzz_pcap.images.Plain.M.phdrs).
Proof.
  exact OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top.Halts_plain.fuzz_pcap_halts_plain.
Qed.

Theorem halts_allowed_libpcap_fuzz_pcap_halts_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LibpcapFuzzPcapHaltsUbsanExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.libpcap.fuzz_pcap.images.Ubsan.M.loaded_segments OSSVerify.libpcap.fuzz_pcap.images.Ubsan.M.init_pc OSSVerify.libpcap.fuzz_pcap.images.Ubsan.M.phdrs).
Proof.
  exact OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top.Halts_ubsan.fuzz_pcap_halts_ubsan.
Qed.

Theorem halts_allowed_libpcap_fuzz_pcap_halts_asan :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LibpcapFuzzPcapHaltsAsanExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.libpcap.fuzz_pcap.images.Asan.M.loaded_segments OSSVerify.libpcap.fuzz_pcap.images.Asan.M.init_pc OSSVerify.libpcap.fuzz_pcap.images.Asan.M.phdrs).
Proof.
  exact OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top.Halts_asan.fuzz_pcap_halts_asan.
Qed.

Theorem halts_allowed_libpcap_fuzz_pcap_halts_both :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LibpcapFuzzPcapHaltsBothExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.libpcap.fuzz_pcap.images.AsanUbsan.M.loaded_segments OSSVerify.libpcap.fuzz_pcap.images.AsanUbsan.M.init_pc OSSVerify.libpcap.fuzz_pcap.images.AsanUbsan.M.phdrs).
Proof.
  exact OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top.Halts_both.fuzz_pcap_halts_both.
Qed.
