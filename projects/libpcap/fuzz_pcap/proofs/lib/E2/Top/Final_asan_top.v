(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.libpcap.fuzz_pcap.images Require Plain.
From OSSVerify.libpcap.fuzz_pcap.images Require Asan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require Final_asan__EquivA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require ImplTopA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

#[local] Notation IMG_S := (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs).
#[local] Notation IMG_T := (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).

Theorem fuzz_pcap_asan_scfg :
  strong_universal_error_free_T_scfg (mkSpuriousCfg false true true true true true) IMG_S IMG_T.
Proof. exact (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.Final_asan__EquivA.Final_asan.fuzz_pcap_asan_scfg ImplTopA.stkA_real ImplTopA.stkA_real_ok ImplTopA.IMPL_A_real). Qed.

Theorem fuzz_pcap_asan_main :
  strong_universal_error_free_T_scfg_budgets (mkSpuriousCfg false true true true true true)
    SanitizerBudgets.lim_source SanitizerBudgets.lim_target IMG_S IMG_T.   (* [comment removed for export] *)
Proof. exact (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.Final_asan__EquivA.Final_asan.fuzz_pcap_asan_main ImplTopA.stkA_real ImplTopA.stkA_real_ok ImplTopA.IMPL_A_real). Qed.
