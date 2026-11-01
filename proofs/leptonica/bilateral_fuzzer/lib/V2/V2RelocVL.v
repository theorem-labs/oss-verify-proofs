(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc RelocCode RelocSites RelocImg CanonCodeVL CanonSitesVL CanonImgVL.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2Reloc.

Lemma v2_code_vl_ok : code_check (@rl_segs v2_reloc) (@rl_delta v2_reloc) canon_code_VL = true.
Proof. vm_compute. reflexivity. Qed.
Definition v2_code_vl : RelocCodeVL v2_reloc := Build_RelocCodeVL v2_reloc v2_code_vl_ok.

Lemma v2_sites_vl_ok : @sites_check v2_reloc canon_sites_VL = true.
Proof. exact (eq_refl true <: @sites_check v2_reloc canon_sites_VL = true). Qed.
Definition v2_sites_vl : RelocSitesVL v2_reloc := Build_RelocSitesVL v2_reloc v2_sites_vl_ok.

Lemma v2_lept_ok : wr_readable_chk (@rl_segs v2_reloc) = true.
Proof. lazy. reflexivity. Qed.
Definition v2_lept : RelocLept v2_reloc := Build_RelocLept v2_reloc v2_lept_ok (@eq_refl bool true) nil.

Lemma v2_strs_vl_ok : @strs_check v2_reloc canon_strs_VL = true.
Proof. apply Bool.Is_true_eq_true. vm_compute. exact I. Qed.
Lemma v2_cells_vl_ok : @cells_check v2_reloc canon_cells_VL = true.
Proof.
  unfold cells_check. apply forallb_forall.
  intros cell cell_listed. cbn [In canon_cells_VL] in cell_listed.
  repeat (destruct cell_listed as [<- | cell_listed]; [vm_compute; constructor |]).
  destruct cell_listed.
Qed.
Lemma v2_spans_vl_ok : @RelocLept.spans_check v2_reloc canon_spans_VL = true.
Proof.
  unfold spans_check, canon_spans_VL. cbn [forallb].
  repeat match goal with |- _ && _ = true => apply andb_true_intro; split end.
  all: reflexivity.
Qed.
Definition v2_img_vl : RelocImgVL v2_reloc :=
  Build_RelocImgVL v2_reloc v2_strs_vl_ok v2_cells_vl_ok v2_spans_vl_ok.
