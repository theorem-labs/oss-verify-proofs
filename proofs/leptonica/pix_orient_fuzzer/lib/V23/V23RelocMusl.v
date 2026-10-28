(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import PFLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc RelocBlocks RelocImg RelocSpan CanonSpans.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require Import RelocRW RelocPF.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23Reloc V23RelocImg.
Local Open Scope Z_scope.

Lemma v23_dwin_bounds : @dwin_bounds_chk v23_reloc v23_data = true.
Proof.
vm_cast_no_check (@eq_refl bool true). Qed.
Definition v23_rw : RelocRW v23_reloc v23_data := {| rl_dwin_bounds := v23_dwin_bounds; rl_rw_hull := v23_hull_ok; rl_rw_spans := v23_spans_ok; rl_rw_orders := v23_orders_ok |}.

Lemma v23_segs_lo : segs_lo (@rl_segs v23_reloc) = @rl_img_lo v23_reloc.
Proof.
vm_cast_no_check (@eq_refl Z (@rl_img_lo v23_reloc)). Qed.
Lemma v23_segs_hi : segs_hi (@rl_segs v23_reloc) = @rl_img_hi v23_reloc.
Proof.
vm_cast_no_check (@eq_refl Z (@rl_img_hi v23_reloc)). Qed.
Lemma v23_pf_bounds : @pf_bounds_chk v23_reloc = true.
Proof.
vm_cast_no_check (@eq_refl bool true). Qed.
Lemma v23_pf_prefix : pf_prefix_ok (@rl_segs v23_reloc) (0x102e7 + @rl_delta v23_reloc B_S_102e7) = true.
Proof.
vm_cast_no_check (@eq_refl bool true). Qed.
Definition v23_pf : RelocPF v23_reloc :=
  {| rl_segs_lo_val := v23_segs_lo; rl_segs_hi_val := v23_segs_hi; rl_pf_bounds := v23_pf_bounds; rl_pf_prefix := v23_pf_prefix |}.
