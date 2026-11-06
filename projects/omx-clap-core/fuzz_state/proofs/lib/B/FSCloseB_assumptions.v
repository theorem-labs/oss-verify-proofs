(* fuzz_state, image B: the named premises and the axioms of the two asan_ubsan tops of lib/B/FSCloseB.v, printed for
   the gates and the fold record (rule 24: no function proved; output only, no definition, no proof). Kept out of
   FSCloseB.v so that the closing file's own build does not pay for traversing the whole cone. *)
From OSSVerify.omx_clap_core.fuzz_state Require Statements.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSCloseB.

(* the named parts are the tops' arguments (About); the global context adds only axioms (Print Assumptions) *)
About FSCloseB.fs_asan_ubsan_agrees_closed.
Print Assumptions FSCloseB.fs_asan_ubsan_agrees_closed.
About FSCloseB.fs_asan_ubsan_halts_closed.
Print Assumptions FSCloseB.fs_asan_ubsan_halts_closed.
(* the two route-1 realloc premises the tops name, as fs_arealloc_BU states them *)
Print FSCloseB.FS_ALLOCATE_RAW_B.
Print FSCloseB.FS_DEALLOCATE_RAW_B.
(* the statements of record the tops prove (projects/omx-clap-core/fuzz_state/Statements.v) *)
Print Statements.asan_ubsan_agrees.
Print Statements.asan_ubsan_halts.
