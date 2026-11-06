From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import StatementUbsanCg slot_c_cf slot_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require ManifestLink ManifestLinkCf.

(* The cut-free slot closed (mirroring ManifestEnd.v): the Kind B callees at every agreement frame from
   ManifestLinkCf.v, the Kind A callees from ManifestLink.v. *)
Lemma kindb_callees_cf_holds : kindb_callees_cf.
Proof.
  split; [|split; [|split]]; intros B API LS SH SK ra empty FF MCF FCF LIM rc fx.
  - exact (ManifestLinkCf.Lc_check_no_overread B API LS SH SK ra empty FF (MCF rc) (FCF rc) (LIM rc) fx).
  - exact (ManifestLinkCf.Lc_names B API LS SH SK ra empty FF (MCF rc) (FCF rc) (LIM rc) fx).
  - exact (ManifestLinkCf.Lc_check_reject_clean_starved B API LS SH SK ra empty FF (MCF rc) (FCF rc) (LIM rc) fx).
  - exact (ManifestLinkCf.Lc_check_round_trip B API LS SH SK ra empty FF (MCF rc) (FCF rc) (LIM rc) fx).
Qed.

Theorem slot_fill_cg_holds : slot_fill_cg.
Proof.
  apply slot_fill_cg_of.
  - first [exact ManifestLink.L_memchr | exact ManifestLink.L_memchr_ro].
  - exact ManifestLink.L_memcpy.
  - exact ManifestLink.L_fuzz_alloc_live.
  - exact ManifestLink.L_fuzz_alloc_peak_reset.
  - exact ManifestLink.L_fuzz_alloc_peak.
  - exact ManifestLink.L_check_bounded_alloc.
  - exact ManifestLink.L_check_as_written.
  - exact ManifestLink.L_check_reject_clean.
  - exact kindb_callees_cf_holds.
Qed.
