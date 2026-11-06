(* lib/A/ACtlTmb.v -- the two premises lib/A/ACtlAll.v leaves open, DERIVED from a Theorem Labs lane's walk statement:
   ACtlAll.TMB_stmt (a Theorem Labs lane's reac_box_model_block spec at the catalogue singleton) and ACtlAll.TMB_LAY_stmt (the same
   at the image's globals list), each from A9_stmt_all (pb_reac_box_model_block_stmt, C_reac_box_model_block.v:184-221,
   at every fx rc and list, at CtrlB and the read-only span [0x9e380, 0xa07c8)) applied to its premises.  When a Theorem Labs lane's walk
   theorem lands, A9_stmt_all is discharged by it in ONE commit (ACtlAsanFinal.v's ctrl_asan_*_closed, over
   ACtlAsanFinalPre.v's ctrl_asan_*_of_a9).  proves no
   function (kind: merge; rule 24: no function proved here).  Writer: a Theorem Labs lane.
   The premises: RELRO := ACtl.relro_img_ctrl; ROFL := a Theorem Labs lane's ACtlTopLink.actl_RO; TL / TLF := its actl_PALib /
   actl_PALibF; LAWS := the core's AR_laws_ok; ML := model_laws_ok at CtrlTSyms' universe; AMEMSET / AMEMCPY :=
   a Theorem Labs lane's IntrinCpySetA.ctrlA_asan_memset_realizes / ctrlA_asan_memcpy_realizes; ASM0 := a Theorem Labs lane's
   StackMalloc0.ctrl_stack_malloc0; SMP := the core's stack_malloc_progress; ASF := astack_free_law_ok; FFL := a Theorem Labs lane's
   AFrameFlagLaw.frame_flag_law_ok; JE and the ten image facts := a Theorem Labs lane's ACtlTmbFacts (ctlall_JE, ctlall_HJT_rng ..
   ctlall_HZS_J14); HGM := a Theorem Labs lane's ctrl_globs_A_marked (at the image list) or its restriction to the catalogue row
   (ctrl_globs_A_cat); HIMGSH := a Theorem Labs lane's ctrl_img_shadow_vis.  No Axiom, no Parameter, no Admitted, no admit. *)
From Coq Require Import ZArith List Lia.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0d YG0f YCbq YG0q YG05 YG0t.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v AE2k AF0m AD2l ACtlCutC ACtl ACtlAll ACtlGlobs AFrameFlagLaw ACtlTopLink ACtlTmbFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Rt Require StackMalloc0 IntrinCpySetA.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require CtrlRo C_reac_box_catalogue_match C_reac_box_model_block.
Import ListNotations.
Local Open Scope Z_scope.

Local Notation segs := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AB1v.tfibsegs.
Local Notation CtrlB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AD2l.CtrlB.
Local Notation RLO := 0x9e380.
Local Notation RHI := 0xa07c8.
Local Notation SK0 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AE2k.tfib_sink_head.
Local Notation GLOBS_CM :=
  [(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_reac_box_catalogue_match.A_CM_TBL,
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_reac_box_catalogue_match.CM_ROWS)].
Local Notation GLOBS_A := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlGlobs.ctrl_globs_A.

(* a Theorem Labs lane's walk statement at CtrlB, the span and every list, at every fx rc. *)
Definition A9_stmt_all : Prop :=
  forall (fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState)
    (rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil) (GLOBS : list (Z * Z)),
  A.Prog.C_reac_box_model_block.pb_reac_box_model_block_stmt (fx := fx) (rc := rc) (SK := SK0) CtrlB GLOBS RLO RHI.

Section CtlTmb.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
  {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}.

Let TS : A.AF0m.CtrlTSyms CtrlB := A.AD2l.CtrlB_syms.
Let LAWS : Reusable.YG0d.AR_laws segs CtrlB := Reusable.YG0q.AR_laws_ok segs CtrlB.
Let ML : Reusable.YG0d.model_laws (Reusable.YG0f.as_universe CtrlB) :=
  Reusable.YG05.model_laws_ok (Reusable.YG0f.as_universe CtrlB) (A.AF0m.ts_universe CtrlB TS).
Let SMP : Reusable.YCbq.stack_malloc_progressP CtrlB := fun s cid HW Hc Hn0 => Reusable.YG05.stack_malloc_progress _ s cid HW Hc Hn0.
Let ASF := Reusable.YG0t.astack_free_law_ok segs CtrlB.
Let ASM0 := A.Rt.StackMalloc0.ctrl_stack_malloc0 fx CtrlB LAWS TS.
Let FFL := A.AFrameFlagLaw.frame_flag_law_ok CtrlB.
Let HIMGSH : A.Prog.CtrlRo.img_shadow_vis segs CtrlB := A.ACtlCutC.ctrl_img_shadow_vis CtrlB TS LAWS.
Let GLOBS_A_MARKED : A.Prog.CtrlRo.globs_marked segs CtrlB GLOBS_A := A.ACtlGlobs.ctrl_globs_A_marked.
Let GLOBS_CM_MARKED : A.Prog.CtrlRo.globs_marked segs CtrlB GLOBS_CM.
Proof.
  intros ly S W mem md q sz Hin HAR. apply (GLOBS_A_MARKED ly S W mem md q sz); [|exact HAR].
  destruct Hin as [E|[]]. rewrite <- E. exact A.ACtlGlobs.ctrl_globs_A_cat.
Qed.

Theorem tmb_stmt_ok (A9 : A9_stmt_all) : A.ACtlAll.TMB_stmt fx rc.
Proof.
  exact (A9 fx rc GLOBS_CM A.ACtl.relro_img_ctrl A.ACtlTopLink.actl_RO
    A.ACtlTopLink.actl_PALib LAWS ML A.Rt.IntrinCpySetA.ctrlA_asan_memset_realizes A.Rt.IntrinCpySetA.ctrlA_asan_memcpy_realizes
    ASM0 SMP ASF FFL A.ACtlTopLink.actl_PALibF A.ACtlTmbFacts.ctlall_JE
    A.ACtlTmbFacts.ctlall_HJT_rng A.ACtlTmbFacts.ctlall_HJT_pos A.ACtlTmbFacts.ctlall_HJT_eq A.ACtlTmbFacts.ctlall_HJT_e
    A.ACtlTmbFacts.ctlall_HJ13_rng A.ACtlTmbFacts.ctlall_HJ14_rng A.ACtlTmbFacts.ctlall_HJ13 A.ACtlTmbFacts.ctlall_HJ14
    GLOBS_CM_MARKED HIMGSH A.ACtlTmbFacts.ctlall_HZS_J13 A.ACtlTmbFacts.ctlall_HZS_J14).
Qed.

Theorem tmb_lay_stmt_ok (A9 : A9_stmt_all) : A.ACtlAll.TMB_LAY_stmt fx rc.
Proof.
  exact (A9 fx rc GLOBS_A A.ACtl.relro_img_ctrl A.ACtlTopLink.actl_RO
    A.ACtlTopLink.actl_PALib LAWS ML A.Rt.IntrinCpySetA.ctrlA_asan_memset_realizes A.Rt.IntrinCpySetA.ctrlA_asan_memcpy_realizes
    ASM0 SMP ASF FFL A.ACtlTopLink.actl_PALibF A.ACtlTmbFacts.ctlall_JE
    A.ACtlTmbFacts.ctlall_HJT_rng A.ACtlTmbFacts.ctlall_HJT_pos A.ACtlTmbFacts.ctlall_HJT_eq A.ACtlTmbFacts.ctlall_HJT_e
    A.ACtlTmbFacts.ctlall_HJ13_rng A.ACtlTmbFacts.ctlall_HJ14_rng A.ACtlTmbFacts.ctlall_HJ13 A.ACtlTmbFacts.ctlall_HJ14
    GLOBS_A_MARKED HIMGSH A.ACtlTmbFacts.ctlall_HZS_J13 A.ACtlTmbFacts.ctlall_HZS_J14).
Qed.

End CtlTmb.
