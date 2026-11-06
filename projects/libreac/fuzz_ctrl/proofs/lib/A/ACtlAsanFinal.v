(* lib/A/ACtlAsanFinal.v -- fuzz_ctrl image A's two CLOSED ASan theorems, the unit statements Statements.asan_agrees and
   Statements.asan_halts: lib/A/ACtlAsanFinalPre.v's ctrl_asan_agrees_of_a9 / ctrl_asan_halts_of_a9 applied to a Theorem Labs lane's
   walk theorem A.Prog.reac_box_model_block_thm.BmbThm.pb_reac_box_model_block (a working branch 85ce1e55661, Qed) at
   CtrlB, the list, the read-only span [0x9e380, 0xa07c8) and CtrlB's symbol table A.AD2l.CtrlB_syms.  The file defines exactly these two names (a Theorem Labs lane's cut rule).  proves no function (kind: merge;
   rule 24: no function proved here).  Writer: a Theorem Labs lane.  No Axiom, no Parameter, no Admitted, no admit. *)
From Coq Require Import ZArith.
From OSSVerify.libreac.fuzz_ctrl Require Statements.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AE2k AD2l ACtlTmb ACtlAsanFinalPre.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_box_model_block_thm.

Theorem ctrl_asan_agrees_closed : OSSVerify.libreac.fuzz_ctrl.Statements.asan_agrees.
Proof.
  exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlAsanFinalPre.ctrl_asan_agrees_of_a9
    (fun fx rc GLOBS => @OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_model_block_thm.BmbThm.pb_reac_box_model_block fx rc
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AE2k.tfib_sink_head OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AD2l.CtrlB
       GLOBS (0x9e380)%Z (0xa07c8)%Z OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AD2l.CtrlB_syms)).
Qed.

Theorem ctrl_asan_halts_closed : OSSVerify.libreac.fuzz_ctrl.Statements.asan_halts.
Proof.
  exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlAsanFinalPre.ctrl_asan_halts_of_a9
    (fun fx rc GLOBS => @OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_model_block_thm.BmbThm.pb_reac_box_model_block fx rc
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AE2k.tfib_sink_head OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AD2l.CtrlB
       GLOBS (0x9e380)%Z (0xa07c8)%Z OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AD2l.CtrlB_syms)).
Qed.
