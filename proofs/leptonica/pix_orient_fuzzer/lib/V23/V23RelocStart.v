(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc RelocBlocks RelocImg.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require Import RelocStart.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23Reloc V23RelocImg.
Local Open Scope Z_scope.

Lemma v23_start_ok : start_ok (@rl_delta v23_reloc 8%positive) (@rl_data_lo v23_reloc v23_data) = true.
Proof.
vm_cast_no_check (@eq_refl bool true). Qed.
Definition v23_start : RelocStart v23_reloc v23_data := {| rl_start_ok := v23_start_ok |}.
