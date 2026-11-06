(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* reac_box_model_block (0x85b44) on fuzz_ctrl's ASan build, image A: the ro_agree and asan_cells conjuncts of the glue's
   rt_facts (lib/A/Prog/reac_box_model_block_glue.v (a version not in this delivery), Section Glue) WITHOUT A.ProgWorld.AR_states_vis0_shadow, for
   a Theorem Labs lane's glue lane.  rule 24: no function is proved here (a VIS0-free restatement of two conjuncts of
   an already-proved lemma, from two already-proved lemmas).
   Writer: a Theorem Labs lane; a working branch.

   bmb_rt_facts_on has rt_facts' binders without VIS0 (B LAWS TSY RLO RHI ly S W m md, then AR and arodata_okP) and
   its first two conjuncts, text for text, so a caller replaces `rt_facts B LAWS TSY VIS0` with
   `bmb_rt_facts_on B LAWS TSY`.  The proof:
     ro_agree    A.ProgWorldCtlRt.ro_agree_of_AR, at OWNED_RO := A.ProgWorldOwnedRo.AR_states_owned_ro_of_AR B TSY
                 (the glue's Let of the same name);
     asan_cells  A.ProgWorldCtlRt.asan_cells_of_AR, moved to the normalized memory by A.MemNormTr.asan_cells_normalize
                 (as rt_facts does).
   Both are the VIS0-free factors of ctlrt_of_AR (ProgWorldCtlRt.v, route (C)).  The shadow_rw conjunct is not here:
   it comes from reac_box_model_block_glue_sr.v (BmbGlueSR.reac_box_model_block_sr_on_img).  LAWS is not used by the
   proof; it is kept (Proof using) so that the binders are rt_facts' without VIS0.  This file does not Require the glue,
   so the glue itself can Require it.  The header is the glue's (as reac_box_model_block_glue_sr.v copies it), so
   every name of the statement resolves as it does in the glue. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* The six core modules that ctrl's lib/A/Reusable duplicates (YI04, YI16, YK11, YK1b, YM05, YO09) are Required, never
   Imported, and written lib.Reusable.X.n (porter 04:24Z / 04:33Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YI04 YI16 YM05 YK1b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK0h YK0i YK14 YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal CtrlSyms CtrlList CtrlAddr CtrlPa CtrlPaLib CtrlBase CtrlFrame
CtrlRo YC85.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import CtrlCallerJ.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require CtrlImg.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcBox RcSynth RcSynthLib.
(* the statement, qualified *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require C_reac_box_model_block.
#[local] Existing Instance CtrlImg.PI_ctrl.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope bv_scope.
Local Open Scope Z_scope.
(* The lib.Lib family is doubled under lib/A/Bz/Lib: Required from its own directory and named lib.Lib.X (a Theorem Labs lane 05:20Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require PropExec MState Mem Frame Cells Step ExecF StepF Regs6ss
  RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04R Reusable.YA0nR Reusable.YG0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Img0 A.AsanRT A.ProgBridge A.MemNorm A.MemNormF
  A.MemNormTr A.ProgWorld A.ProgWorld_Fs A.ProgWorldShadow A.ProgWorldAstack A.ProgWorldCtlRt A.ProgWorldOwnedRo
  A.ProgWorldVisFrame A.ProgWorldVisWin A.ProgWorldVisHeap A.Prog.CtrlRo.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.asan_stack_malloc_c A.Prog.RcAsanFP A.Prog.RcAsanFPLib
  A.Prog.reac_box_model_block_c A.Prog.reac_box_model_block_cF A.Prog.rng_asan A.Prog.reac_box_model_block_base
  A.Prog.asan_memsetF A.Prog.ImgBounds A.Prog.memset A.Prog.asan_memcpyF A.Prog.build_dt1_singleF
  A.Prog.reac_box_model_block_baseF A.Prog.reac_box_model_block_epi A.Prog.reac_box_model_block_epiF.

Module BmbGlueRT.
Import lib.Lib.PropExec lib.Lib.MState lib.Lib.Mem lib.Lib.Frame lib.Lib.Cells lib.Lib.Step.
Import A.Img0 A.AsanRT A.Prog.asan_stack_malloc_c A.Prog.RcAsanFP A.Prog.reac_box_model_block_c.
Import Reusable.YK04R Reusable.YA0nR A.ProgBridge A.MemNorm A.MemNormTr.
(* Last: StepF's step (evtF goals) shadows Step's (evt goals), as in the _F files. *)
Import lib.Lib.ExecF lib.Lib.StepF.
Import ListNotations.
Local Open Scope Z_scope.

(* The glue's Section Glue header (reac_box_model_block_glue.v:958-962, :1158), without VIS0 and without the
   hypotheses rt_facts does not take (TL TLF ML SMP ASM0). *)
Section Glue.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : asyms.

Hypothesis LAWS : AR_laws AB1v.tfibsegs B.
Hypothesis TSY : A.AF0m.CtrlTSyms B.                  (* the bundle's const table is ctrl's [core composition] *)

Lemma bmb_rt_facts_on : forall RLO RHI ly S (W : YA0n.world AB1v.tfibsegs) m md,
  AR AB1v.tfibsegs B ly S W m md ->
  A.Prog.CtrlBase.arodata_okP AB1v.tfibsegs RLO RHI B (aview AB1v.tfibsegs (YA0n.w_H W) m) ->
  ro_agree rsegs m /\ asan_cells (normalize rsegs m).
Proof using LAWS TSY.
  intros RLO RHI ly S W m md HAR HRO.
  pose proof (A.ProgWorldCtlRt.ro_agree_of_AR B TSY (A.ProgWorldOwnedRo.AR_states_owned_ro_of_AR B TSY)
                RLO RHI ly S W m md HAR HRO) as RO.
  pose proof (A.ProgWorldCtlRt.asan_cells_of_AR B TSY ly S W m md HAR) as AC.
  assert (Hro : ro_agree rsegs m) by exact RO.
  split; [exact Hro | exact (asan_cells_normalize m Hro AC)].
Qed.

End Glue.
End BmbGlueRT.
