(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import MallocLayout RelocLayout.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23MallocLayout V23Reloc.

Lemma lv23_reloc : LU16 = reloc_layout v23_reloc.
Proof.
unfold LU16, reloc_layout. f_equal; first [ reflexivity | apply bv_eq; reflexivity ]. Qed.

(* [comment removed for export] *)
Ltac v23_ml_tail t := rewrite lv23_reloc; exact t.
