From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require FrameProof.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import StatementUbsan slot_c slot ManifestLink.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require readings_scan_c readings_scan.
From OSSVerify.omx_clap_core.fuzz_manifest Require Statements.

Lemma kindb_callees_of : readings_scan_c.readings_scan_contract -> kindb_callees.
Proof.
  intros SCAN.
  split; [|split; [|split]]; intros B API LS SH SK ra empty FF rc fx.
  - exact (L_check_no_overread B API LS SH SK ra empty FF SCAN fx).
  - exact (L_names B API LS SH SK ra empty FF SCAN fx).
  - exact (L_check_reject_clean_starved B API LS SH SK ra empty FF SCAN fx).
  - exact (L_check_round_trip B API LS SH SK ra empty FF SCAN fx).
Qed.

Theorem slot_fill_of_scan : readings_scan_c.readings_scan_contract -> slot_fill.
Proof.
  intros SCAN. apply slot_fill_of.
  - first [exact L_memchr | exact L_memchr_ro].
  - exact L_memcpy.
  - exact L_fuzz_alloc_live.
  - exact L_fuzz_alloc_peak_reset.
  - exact L_fuzz_alloc_peak.
  - exact L_check_bounded_alloc.
  - exact L_check_as_written.
  - exact L_check_reject_clean.
  - exact (kindb_callees_of SCAN).
Qed.

Theorem ubsan_halts_of_scan : readings_scan_c.readings_scan_contract -> Statements.ubsan_halts.
Proof. intros SCAN. exact (ubsan_halts_of_frame (slot_fill_of_scan SCAN) FrameProof.frame_ubsan_holds). Qed.

Lemma readings_scan_closed : readings_scan_c.readings_scan_contract.
Proof.
  apply readings_scan.readings_scan_holds;
    [exact L_strlen | exact L_strncmp | exact L_strncasecmp | exact L_strchr | exact L_isalnum | exact L_has_prefixed].
Qed.

Theorem ubsan_halts_holds : Statements.ubsan_halts.
Proof. exact (ubsan_halts_of_scan readings_scan_closed). Qed.
