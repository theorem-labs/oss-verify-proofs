(* lib/A/ACtlAsanFinalPre.v -- the open-premise forms of fuzz_ctrl image A's final ASan tops (lib/A/ACtlAsanFinal.v holds
   only the two closed theorems, a Theorem Labs lane's cut rule): the unit's two ASan statements
   (Statements.asan_agrees, Statements.asan_halts) from A/AsanTop.v's ctrl_asan_agrees_of_tfib / ctrl_asan_halts_of_tfib at
   TFIB := a Theorem Labs lane's A.CtrlClose.ctrl_TFIB_T_closed applied to the walk top of lib/A/ACtlAll.v.  proves no function (kind:
   merge; rule 24: no function proved here).  Writer: a Theorem Labs lane (scope addition a Theorem Labs lane 19:01Z via a Theorem Labs lane).

   ctrl_TFIB_T_closed (A/CtrlClose.v:187) takes the walk top as `forall fx rc, ctrl_lib_x_at fx rc` (CtrlClose.v:104-106:
   LS_LEAF -> the core's lib contract at CtrlB, ameter_triv, ctrl_XL0, 0x9e380 / 0xa07c8, at fuzz_ctrl's shape).
   ACtlAll.ctl_lib_x_CtrlB_all proves that contract at XL0 (= ctrl_XL0 = fun _ => 0) and the same bounds and shape, so it
   is passed by conversion.  a Theorem Labs lane's A.CtrlCloseLink.ctrl_lib_x_link (not in this delivery) is NOT used: it takes ctl_lib_x_CtrlB's open
   ARGUMENTS, which ACtlAll.v has already discharged inside its top theorem.
   No Section, no Hypothesis, no Variable here: the two premises ACtlAll.v still leaves open (its Section Hypotheses
   TMB and TMB_LAY) are the explicit leading binders of both theorems, typed by ACtlAll.v's NAMED statements TMB_stmt /
   TMB_LAY_stmt at every fx rc, so the statement and Print Assumptions both show them.  ctrl_asan_agrees_of_a9 / ctrl_asan_halts_of_a9
   discharge both binders from a Theorem Labs lane's walk statement (A.ACtlTmb.A9_stmt_all); lib/A/ACtlAsanFinal.v's closed
   theorems ctrl_asan_agrees_closed / ctrl_asan_halts_closed apply those to a Theorem Labs lane's walk theorem.
   No Axiom, no Parameter, no Admitted, no admit. *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
From OSSVerify.libreac.fuzz_ctrl Require Statements.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ACtlAll ACtlTmb CtrlClose CtrlTFIB AsanTop.

Theorem ctrl_asan_agrees_A :
  (forall (fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState)
          (rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil),
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlAll.TMB_stmt fx rc) ->
  (forall (fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState)
          (rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil),
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlAll.TMB_LAY_stmt fx rc) ->
  OSSVerify.libreac.fuzz_ctrl.Statements.asan_agrees.
Proof.
  intros TMB TMB_LAY.
  apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanTop.ctrl_asan_agrees_of_tfib.
  apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.CtrlClose.ctrl_TFIB_T_closed.
  intros fx rc _.
  exact (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlAll.ctl_lib_x_CtrlB_all fx rc (TMB fx rc) (TMB_LAY fx rc)).
Qed.

Theorem ctrl_asan_halts_A :
  (forall (fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState)
          (rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil),
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlAll.TMB_stmt fx rc) ->
  (forall (fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState)
          (rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil),
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlAll.TMB_LAY_stmt fx rc) ->
  OSSVerify.libreac.fuzz_ctrl.Statements.asan_halts.
Proof.
  intros TMB TMB_LAY.
  apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanTop.ctrl_asan_halts_of_tfib.
  apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.CtrlClose.ctrl_TFIB_T_closed.
  intros fx rc _.
  exact (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlAll.ctl_lib_x_CtrlB_all fx rc (TMB fx rc) (TMB_LAY fx rc)).
Qed.

Theorem ctrl_asan_agrees_of_a9 :
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlTmb.A9_stmt_all -> OSSVerify.libreac.fuzz_ctrl.Statements.asan_agrees.
Proof.
  intros A9.
  exact (ctrl_asan_agrees_A (fun fx rc => @OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlTmb.tmb_stmt_ok fx rc A9)
    (fun fx rc => @OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlTmb.tmb_lay_stmt_ok fx rc A9)).
Qed.

Theorem ctrl_asan_halts_of_a9 :
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlTmb.A9_stmt_all -> OSSVerify.libreac.fuzz_ctrl.Statements.asan_halts.
Proof.
  intros A9.
  exact (ctrl_asan_halts_A (fun fx rc => @OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlTmb.tmb_stmt_ok fx rc A9)
    (fun fx rc => @OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlTmb.tmb_lay_stmt_ok fx rc A9)).
Qed.
