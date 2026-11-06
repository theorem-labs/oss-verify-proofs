(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: relocated from proofs/omx-clap-core/fuzz_preset/lib/A/RGcfS5_r.v (hub 96e1d2182ec6, blob 3b896c9cd196), stated at fuzz_preset's asan image (ELF sha256 bff8519bbe3e), to its asan-ubsan image (ELF sha256 c90d4fa54d43): module paths to the image-B twins, every image numeral by symbol + offset, image bounds by the image-B start-up facts; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YF0x YFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFeq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import FSRealloc_S1_tblB RGcfS5_uB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require FSRealloc_S1_rB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition R_IMN : YP09.region := YP09.mkRegion None 0xac908 0xac910 0 0 [YP09.mkChunk 0xac908 (CZero 8)].
Definition SS_L1N : sstate := Eval vm_compute in (FSRealloc_S1_rB.xrun_to 0x5f0a4 RGcfS5_uB.SS0).
Definition SS_AN : sstate := Eval vm_compute in
(FSRealloc_S1_rB.xrun_to 0x5b5c0 (FSRealloc_S1_rB.xpin 10 (SLit TFIB_IAL_LO)
  (FSRealloc_S1_rB.xadd R_IMN (FSRealloc_S1_rB.xadd FSRealloc_S1_rB.R_SCRR (FSRealloc_S1_rB.xafter 54 (-2144) 0x53c68 SS_L1N))))).
Definition SS_EN : sstate := Eval vm_compute in
(FSRealloc_S1_rB.xrun_to 0x326a4 (FSRealloc_S1_rB.xadd FSRealloc_S1_rB.R_OBJR
  (FSRealloc_S1_rB.xadd FSRealloc_S1_rB.R_SCRR (FSRealloc_S1_rB.xafterU 70 0x53dbc SS_AN)))).
Goal ss_pc SS_L1N = 0x5f0a4 /\ ss_pc SS_AN = 0x5b5c0 /\ ss_pc SS_EN = 0x326a4. Proof. repeat split; reflexivity. Qed.
