(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc RelocCode RelocSites RelocImg CanonCodeVL CanonSitesVL CanonImgVL.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23Reloc.

Lemma v23_code_vl_ok : code_check (@rl_segs v23_reloc) (@rl_delta v23_reloc) canon_code_VL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v23_code_vl : RelocCodeVL v23_reloc := {| rl_code_vl_ok := v23_code_vl_ok |}.

Lemma v23_sites_vl_ok : @sites_check v23_reloc canon_sites_VL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v23_sites_vl : RelocSitesVL v23_reloc := {| rl_sites_vl_ok := v23_sites_vl_ok |}.

Lemma v23_lept_ok : wr_readable_chk (@rl_segs v23_reloc) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v23_lept : RelocLept v23_reloc := {| rl_wr_readable_ok := v23_lept_ok; rl_pages_ok := eq_refl; rl_clr_extra := nil |}.

Lemma v23_strs_vl_ok : @strs_check v23_reloc canon_strs_VL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma v23_cells_vl_ok : @cells_check v23_reloc canon_cells_VL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma v23_spans_vl_ok : @RelocLept.spans_check v23_reloc canon_spans_VL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v23_img_vl : RelocImgVL v23_reloc := {| rl_strs_vl_ok := v23_strs_vl_ok; rl_cells_vl_ok := v23_cells_vl_ok; rl_spans_vl_ok := v23_spans_vl_ok |}.
