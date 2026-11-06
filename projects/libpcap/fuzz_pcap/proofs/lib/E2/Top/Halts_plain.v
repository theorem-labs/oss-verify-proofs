(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence HaltsAllowed.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UNodes__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require HaltsFinal. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.EquivPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.HaltsFinal.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top Require Import Final_ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Theorem fuzz_pcap_halts_plain :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source [Z_to_bv 64 0; Z_to_bv 64 2]
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs).
Proof.
  apply (halts_final ssegs SRCM.init_pc SRCM.phdrs tbS stkS sec sec_range source_alloc_limit image_ok_src3).
  - intros en inp _. exact OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Compose.tls_in_image_ssegs.
  - intros en. destruct (spB_ok en) as [A B]. exact (sites_at_ok_S _ A B).
  - exact IMPL_S_final.
Qed.
