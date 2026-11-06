(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.libpcap.fuzz_pcap.images Require Plain.
From OSSVerify.libpcap.fuzz_pcap.images Require AsanUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require Final_asan__EquivA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require ImplTopA. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

#[local] Notation IMG_S := (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs).
#[local] Notation IMG_T := (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).

Theorem fuzz_pcap_both_scfg :
  strong_universal_error_free_T_scfg (mkSpuriousCfg false true true true true true) IMG_S IMG_T.
Proof. exact (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.Final_asan__EquivA.Final_both.fuzz_pcap_both_scfg A3D.ImplTopA.TwB.stkA_real A3D.ImplTopA.TwB.stkA_real_ok A3D.ImplTopA.TwB.IMPL_A_real). Qed.

Theorem fuzz_pcap_both_main :
  strong_universal_error_free_T_scfg_budgets (mkSpuriousCfg false true true true true true)
    SanitizerBudgets.lim_source SanitizerBudgets.lim_target IMG_S IMG_T.   (* [comment removed for export] *)
Proof. exact (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.Final_asan__EquivA.Final_both.fuzz_pcap_both_main A3D.ImplTopA.TwB.stkA_real A3D.ImplTopA.TwB.stkA_real_ok A3D.ImplTopA.TwB.IMPL_A_real). Qed.
