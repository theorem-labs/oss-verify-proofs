(* fuzz_state, image A (fs.asan): the audit of the closing side lib/A/FSClose.v, kept apart from it (owner ruling
   2026-10-29 13:25Z). Print Assumptions walks the whole proof cone of each top (the walks and runtime proofs under
   them), which is the slow part of the build; FSClose.v itself only composes. The gates build this file on each S0
   head.
   - About: the named Section hypotheses each top still takes (its arguments).
   - Print Assumptions: the axioms of the global context the tops use.
   - Print Statements.asan_halts / asan_agrees: the statements of record the two tops prove
     (projects/omx-clap-core/fuzz_state/Statements.v:85-86, :110-111).
   rule 24: no function proved (an audit file: no definition, no proof). *)
From OSSVerify.omx_clap_core.fuzz_state Require Statements.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSClose.

About FSClose.fs_asan_agrees_closed.
Print Assumptions FSClose.fs_asan_agrees_closed.
About FSClose.fs_asan_halts_closed.
Print Assumptions FSClose.fs_asan_halts_closed.
Print Statements.asan_halts.
Print Statements.asan_agrees.
