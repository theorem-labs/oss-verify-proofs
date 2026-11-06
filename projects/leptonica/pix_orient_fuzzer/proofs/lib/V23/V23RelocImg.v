(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec StreamSim.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc RelocImg CanonImg RelocSpan CanonSpans.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23Reloc.
Local Open Scope Z_scope.

Lemma v23_cells_ok : @cells_check v23_reloc canon_cells = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Definition v23_img : RelocImg v23_reloc := Build_RelocImg v23_reloc v23_cells_ok.

Lemma v23_data_wseg : wseg_ok (@rl_segs v23_reloc) (Z_to_bv 64 0x127000) (Z.to_nat (@rl_img_hi v23_reloc - 0x127000)) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma v23_data_ok : (0 <=? 0x127000) && (0x127000 <=? @rl_img_hi v23_reloc) && (@rl_img_hi v23_reloc <=? 2^32) = true.
Proof. exact (eq_refl true). Qed.

Definition v23_data : RelocData v23_reloc :=
  Build_RelocData v23_reloc 1208320 v23_data_ok v23_data_wseg.

Lemma v23_hull_ok : @hull_okb v23_reloc v23_data = true.
Proof. exact (eq_refl true). Qed.
Lemma v23_spans_ok : @spans_check v23_reloc v23_data canon_spans = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma v23_orders_ok : @orders_check v23_reloc canon_spans canon_order = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition v23_spans : RelocSpans v23_reloc v23_data :=
  Build_RelocSpans v23_reloc v23_data v23_hull_ok v23_spans_ok v23_orders_ok.
