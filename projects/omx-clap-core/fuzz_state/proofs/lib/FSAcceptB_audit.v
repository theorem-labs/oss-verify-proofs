(* Acceptance audit of all four fuzz_state ASan statements (image B's record, on the final release sha). It holds only Check / Print Assumptions pairs and Print lines, in the form cbrec's parser
   reads (cbrec.sh:101-113; it refuses About). A lib file cannot Require a statement directory (each of those requires
   lib), so the pairs name the closed tops that each <statement>/Proof.v applies with `exact`. *)
From OSSVerify.omx_clap_core.fuzz_state Require Statements.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSClose.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSCloseB.

Print OSSVerify.omx_clap_core.fuzz_state.Statements.asan_halts.
Print OSSVerify.omx_clap_core.fuzz_state.Statements.asan_agrees.
Print OSSVerify.omx_clap_core.fuzz_state.Statements.asan_ubsan_halts.
Print OSSVerify.omx_clap_core.fuzz_state.Statements.asan_ubsan_agrees.

Check OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSClose.fs_asan_halts_closed.
Print Assumptions OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSClose.fs_asan_halts_closed.
Check OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSClose.fs_asan_agrees_closed.
Print Assumptions OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSClose.fs_asan_agrees_closed.
Check OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSCloseB.fs_asan_ubsan_halts_closed.
Print Assumptions OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSCloseB.fs_asan_ubsan_halts_closed.
Check OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSCloseB.fs_asan_ubsan_agrees_closed.
Print Assumptions OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSCloseB.fs_asan_ubsan_agrees_closed.
