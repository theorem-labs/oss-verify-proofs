(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc RelocCode RelocSites RelocImg CanonCodeVL CanonSitesVL CanonImgVL.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2Reloc.

Lemma v2_code_vl_ok : code_check (@rl_segs v2_reloc) (@rl_delta v2_reloc) canon_code_VL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v2_code_vl : RelocCodeVL v2_reloc := {| rl_code_vl_ok := v2_code_vl_ok |}.

Lemma v2_sites_vl_ok : @sites_check v2_reloc canon_sites_VL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v2_sites_vl : RelocSitesVL v2_reloc := {| rl_sites_vl_ok := v2_sites_vl_ok |}.

Lemma v2_lept_ok : wr_readable_chk (@rl_segs v2_reloc) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v2_lept : RelocLept v2_reloc := {| rl_wr_readable_ok := v2_lept_ok; rl_pages_ok := eq_refl; rl_clr_extra := nil |}.

Lemma v2_strs_vl_ok : @strs_check v2_reloc canon_strs_VL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma v2_cells_vl_ok : @cells_check v2_reloc canon_cells_VL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma v2_spans_vl_ok : @RelocLept.spans_check v2_reloc canon_spans_VL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v2_img_vl : RelocImgVL v2_reloc := {| rl_strs_vl_ok := v2_strs_vl_ok; rl_cells_vl_ok := v2_cells_vl_ok; rl_spans_vl_ok := v2_spans_vl_ok |}.
