From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require FrameProof.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import StatementPlain slot_c slot ManifestLink.
From OSSVerify.omx_clap_core.fuzz_manifest Require Statements.

Lemma kindb_callees_holds : kindb_callees.
Proof.
  split; [|split; [|split]]; intros B API LS SH SK ra empty FF rc fx.
  - eapply L_check_no_overread. exact FF.
  - eapply L_names. exact FF.
  - eapply L_check_reject_clean_starved. exact FF.
  - eapply L_check_round_trip. exact FF.
Qed.

Theorem slot_fill_holds : slot_fill.
Proof.
  apply slot_fill_of.
  - first [exact L_memchr | exact L_memchr_ro].
  - exact L_memcpy.
  - exact L_fuzz_alloc_live.
  - exact L_fuzz_alloc_peak_reset.
  - exact L_fuzz_alloc_peak.
  - exact L_check_bounded_alloc.
  - exact L_check_as_written.
  - exact L_check_reject_clean.
  - exact kindb_callees_holds.
Qed.

Theorem plain_halts_holds : Statements.plain_halts.
Proof. exact (plain_halts_of_frame slot_fill_holds FrameProof.frame_plain_holds). Qed.
