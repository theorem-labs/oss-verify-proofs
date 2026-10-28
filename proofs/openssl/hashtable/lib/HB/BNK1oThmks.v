(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanNodesIO AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CertRefl CxRel CxPlan CxPlanSound CxGlue CxBatch CxOfAps CxReblob.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HBPlanImage HBAtable HBArg HBCheckG HBChain HBHop HBBatch HBFam2 HBParity HBBatchF9 HBOpSel2 HBUsageDefs BNK1oS0 BNK1oIT BNK1oDks BNK1oks_bA0 BNK1oks_bA1 BNK1oks_bB BNK1oks_bC1 BNK1oks_bC2 BNK1oks_bX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.
Lemma allA0 : allok true 400000 3000 NK1o_IT _ jA0 (a0s).
Proof. exact (hbatch_map true 400000 3000 _ jA0 NK1o_IT _ bA0). Qed.
Lemma allA1 : allok true 400000 3000 NK1o_IT _ jA1 (leaves).
Proof. exact (hbatch_map true 400000 3000 _ jA1 NK1o_IT _ bA1). Qed.
Lemma allB : allok true 400000 3000 NK1o_IT _ jB (ops).
Proof. exact (hbatch_map true 400000 3000 _ jB NK1o_IT _ bB). Qed.
Lemma allC1 : allok true 400000 3000 NK1o_IT _ jC1 (list_prod leaves (classes TCs)).
Proof. exact (hbatch_map true 400000 3000 _ jC1 NK1o_IT _ bC1). Qed.
Lemma allC2 : allok true 400000 3000 NK1o_IT _ jC2 (flat_map od_holes ops).
Proof. exact (hbatch_map true 400000 3000 _ jC2 NK1o_IT _ bC2). Qed.
Lemma allX : allok true 400000 3000 NK1o_IT _ jX (xjobs ops).
Proof. exact (hbatch_map true 400000 3000 _ jX NK1o_IT _ bX). Qed.
Lemma SIDE : side_ok N0 1200 1860 4800 5400 6000 1160 1760 4600 5200 5800 NK1o_cs TA1 TB TCs TDs FCs TFE TFEE a0s leaves ops opdom shapeB sC2s sXs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma OPSEL : forall E, Forall (pure_holds E) opdom -> exists o, In o ops /\ Forall (pure_holds E) (od_F o).
Proof. apply (opsel_of_cover 1680 ops opdom). vm_compute. reflexivity. Qed.
Section G.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variables argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variables uid hw : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Let c := content_of argv fs.
  #[local] Notation SV := (SINVm HAPH sp rdraw brk0 argv envp uid hw c).
  #[local] Notation argH := (argH0 HAPH sp rdraw argv envp uid hw).
  Let SVF := SINVm_frame HAPH sp rdraw brk0 argv envp uid hw c.
  Let SVA := SINVm_agree HAPH sp rdraw brk0 argv envp uid hw c.
  Let SV1 := SVm_to1 sp rdraw brk0 argv envp uid hw c.
  (* [comment removed for export] *)
  Hypothesis H_FE : fx_hole SV argH (bv_unsigned sp) fs TFE TFEE.
  Definition grp_sound := fam_sound sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit SV SV1 SVF SVA true 400000 3000 NK1o_IT NK1o_IT_ok
    N0 1200 1860 4800 5400 6000 1160 1760 4600 5200 5800 NK1o_cs TA1 TB TCs TDs FCs TFE TFEE a0s leaves ops opdom shapeB sC2s sXs allA0 allA1 allB allC1 allC2 allX SIDE OPSEL H_FE.
End G.
Check grp_sound.
