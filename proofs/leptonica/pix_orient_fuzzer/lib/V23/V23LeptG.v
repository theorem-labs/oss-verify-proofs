(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import AllocIface.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptDefs.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica.VL Require LeptBase.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23Reloc V23RelocVL V23LeptBase.
(* [comment removed for export] *)

Lemma v23_LL : LLU16 = @LeptBase.LLG v23_reloc v23_lept.
Proof. reflexivity. Qed.

Definition v23_pinsG {AL : AllocLayout} {CL : CallocLayout} (PP : @V23Pins AL CL) : @LeptBase.PinsG v23_reloc AL CL :=
  @LeptBase.Build_PinsG v23_reloc AL CL (@p16_segs AL CL PP) (@p16_malloc AL CL PP) (@p16_free AL CL PP) (@p16_calloc AL CL PP) (@p16_tp AL CL PP).
