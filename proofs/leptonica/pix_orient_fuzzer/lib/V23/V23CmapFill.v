(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import StartupTac RefMemcpyLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica.VL Require CmapFill.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23Reloc V23RelocCode V23RelocSites V23RelocImg V23RelocVL.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section VPORT.
Context {fx : FPState}.
Definition CMAP_CLOB : list nat := [5; 10; 11; 12; 13; 14; 15; 16; 17; 23]%nat.
Theorem cmapfill_contract :
  SSP.sum_contract SEGS (SSP.spec_cmapfill 0x747f4 0x74718 19 18 0 8 [(23%nat, 0%Z); (9%nat, 4%Z); (22%nat, 4%Z)] CMAP_CLOB).
Proof. rl_tail (@VL.CmapFill.cmapfill_contract fx v23_reloc v23_code_vl). Qed.

End VPORT.
