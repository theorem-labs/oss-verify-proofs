(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.MhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.DrvNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Sound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Glue OSSVerify.Proofs.glaze.binary_reflection.lib.GlzAllocPlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzClosurePlain. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs.RefImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImagePlain OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks.GpFuzzT OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.MhKInst OSSVerify.Proofs.glaze.binary_reflection.lib.MhFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks.DrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.DrvNodes OSSVerify.Proofs.glaze.binary_reflection.lib.DrvNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Plan.DrvHooksS OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound.DrvTPlan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound.DrvTSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound.DrvTInst OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound.DrvTGlue OSSVerify.Proofs.glaze.binary_reflection.lib.DrvSSound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Plan OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Sound OSSVerify.Proofs.glaze.binary_reflection.lib.DrvS2Glue OSSVerify.Proofs.glaze.binary_reflection.lib.GlzAllocPlain OSSVerify.Proofs.glaze.binary_reflection.lib.GlzClosurePlain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

#[local] Notation RSEGS := PSEGS.
(* [comment removed for export] *)
Ltac lia ::= Zify.zify; xlia zchecker.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition SRP : shape_rel RSEGS := SR_realizes RSEGS.
Lemma SRXP : sr_exactness RSEGS SRP.
Proof. exact (exact_realizes RSEGS). Qed.
Lemma SRP_rel : forall c T, sr_rel RSEGS SRP c T <-> realizes RSEGS c T.
Proof. intros c T. split; intros H; exact H. Qed.

(* [comment removed for export] *)
Lemma SWIN_T_img : forall lo hi, In (lo, hi) SWIN_T ->
  g_ro_hi GPLAIN <= lo /\ hi <= g_img_hi GPLAIN /\ (forall plo phi, In (plo, phi) (g_priv GPLAIN) -> hi <= plo \/ phi <= lo).
Proof.
  intros lo hi Hin. unfold SWIN_T, PERM_Tc, RSTAGE_W, DN.FILE1, DN.FILE2 in Hin. cbn in Hin.
  cbn [g_ro_hi g_img_hi g_priv GPLAIN].
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]; injection H as <- <-;
    (split; [lia | split; [lia | intros plo phi [X|[X|[X|[]]]]; injection X as <- <-; lia]]).
Qed.

Lemma BCAP_ok : 0 + BCAP <= GBUDGET. Proof. unfold BCAP. lia. Qed.
Lemma CCAP_ok : 0 + CCAP <= GCOUNT. Proof. unfold CCAP. lia. Qed.

Section InstP.
Context {RC : run_ceil}.
(* [comment removed for export] *)
Hypothesis HMW : forall fx : FPState, @MALLOC_KATW fx RC MSTK_M.
Hypothesis HMA : forall fx : FPState, @MALLOC_ALT_F fx RC MSTK_M.
Hypothesis HMB : forall fx : FPState, @MALLOC_BIG_R fx RC MSTK_M.

#[local] Notation RZ := (sr_rel RSEGS SRP).
#[local] Notation AINVcT TOP M0 := (AINV_f SWIN_T GPLAIN AINV PERM_Tc TOP [] M0 0 0).
#[local] Notation AINVcS TOP M0 := (AINV_f SWIN_T GPLAIN AINV_R PERM_Tc TOP [] M0 0 0).
#[local] Notation cs_okT TOP FS0 M0 := (GPS.cs_ok RSEGS PERM_Tc TOP FS0 fds_std (AINVcT TOP M0) fx_ok UTRUE).
#[local] Notation cs_okS TOP FS0 M0 := (GPS.cs_ok RSEGS PERM_Tc TOP FS0 fds_std (AINVcS TOP M0) fx_ok UTRUE).

(* [comment removed for export] *)
Lemma HFRP : forall fx : FPState, @FREE_R fx RC MSTK_M.
Proof. intros fx. exact (@free_r3 fx RC). Qed.

(* [comment removed for export] *)
Lemma GC_TP : forall TOP FS0 M0,
  gcontracts RSEGS ITD APLAIN NXD PERM_Tc TOP FS0 fds_std (AINVcT TOP M0) fx_ok UTRUE RZ GPLAIN BCAP CCAP.
Proof.
  intros TOP FS0 M0.
  exact (GC_ALL HMW SWIN_T swin_ok_T SWIN_T_img ITD NXD BCAP CCAP PERM_Tc TOP [] M0 0 0 FS0 fds_std UTRUE
           ITD_ok (Z.le_refl 0) (Z.le_refl 0) BCAP_ok CCAP_ok UTRUE_agree).
Qed.

(* [comment removed for export] *)
Lemma FZNP : callee_contract RSEGS SWIN_T GPLAIN fx_ok RZ AINV FuzzN.ce.
Proof. exact (fuzz_closed_N HMW). Qed.
Lemma FZEP : callee_contract RSEGS SWIN_T GPLAIN fx_ok RZ AINV FuzzE.ce.
Proof. exact (fuzz_closed_E HMW). Qed.





(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ReadLoop.
Variables (p : Fs.path) (data : list byte) (TOP : Z) (M0 : word -> option byte).
(* [comment removed for export] *)
Hypothesis REFP : forall len E fx R M model,
  GPS.cs_ok RSEGS PERM_Tc TOP (m_fs model) (FDSr p (len + (2 ^ 26 - len))) (AINVcS TOP M0) fx_ok (U_rd data len (2 ^ 26)) E tVRb fx R M model ->
  realizes RSEGS (cfgF RSEGS fx R (pc tVRb) M model) (t_die msg_refused (m_fs model)).

End ReadLoop.
End InstP.
