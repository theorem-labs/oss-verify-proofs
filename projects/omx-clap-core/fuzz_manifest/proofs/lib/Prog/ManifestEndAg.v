From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import StatementPlain StatementPlainAg slot_c_ag
  slot_ag ManifestLinkAg.

(* ManifestEnd.v at the bounded-room frame facts (StatementPlainAg.frame_facts_ag), without plain_halts_holds. *)
Lemma kindb_callees_ag_holds : kindb_callees_ag.
Proof.
  split; [|split; [|split]]; intros B API LS SH SK ra empty FF rc fx.
  - eapply L_check_no_overread. exact FF.
  - eapply L_names. exact FF.
  - eapply L_check_reject_clean_starved. exact FF.
  - eapply L_check_round_trip. exact FF.
Qed.

Theorem slot_fill_ag_holds : slot_fill_ag.
Proof.
  apply slot_fill_ag_of.
  - first [exact L_memchr | exact L_memchr_ro].
  - exact L_memcpy.
  - exact L_fuzz_alloc_live.
  - exact L_fuzz_alloc_peak_reset.
  - exact L_fuzz_alloc_peak.
  - exact L_check_bounded_alloc.
  - exact L_check_as_written.
  - exact L_check_reject_clean.
  - exact kindb_callees_ag_holds.
Qed.
