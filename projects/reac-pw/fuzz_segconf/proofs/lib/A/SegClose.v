(* reac-pw/fuzz_segconf, image A: the two ASan statements of the unit, closed.
   - seg_asan_halts_closed: SegTop.seg_asan_halts_of_parts at HLTOI := SegProgClosed.seg_ltoi_all (the harness contract
     at SegB, every callee closed by its walk, every runtime row by its closing); the destructor-exit instance is the
     core's RtDtorExit.cmd_dtor_exit;
   - seg_asan_agrees_closed: SegAsanAgree.seg_asan_agrees_of_tfib_plain (SegAsanTop's plain side given by the plain
     tree) at SegTop.seg_TFIB_T_of_parts with the same part.
   Both take no argument.
   Proves no function (kind: merge; the closing of the two statements). *)
From OSSVerify.reac_pw.fuzz_segconf Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require SegTop SegAsanAgree.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtDtorExit.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegProgClosed.
#[local] Existing Instance OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt.RtDtorExit.cmd_dtor_exit.

Theorem seg_asan_halts_closed : Statements.asan_halts.
Proof.
  exact (lib.A.SegTop.seg_asan_halts_of_parts (fun rc => @lib.A.Prog.SegProgClosed.seg_ltoi_all rc)).
Qed.

Theorem seg_asan_agrees_closed : Statements.asan_agrees.
Proof.
  exact (lib.A.SegAsanAgree.seg_asan_agrees_of_tfib_plain
           (lib.A.SegTop.seg_TFIB_T_of_parts (fun rc => @lib.A.Prog.SegProgClosed.seg_ltoi_all rc))).
Qed.
