(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AsanNodesAux AsanStartLoops AsanNodesStartX AsanNodesStartXInit. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import Img_src13 Code_startx_src13.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Section StartX.
  Context {fx : FPState}.
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variable uid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Variable LIMIT : Z.
  (* [comment removed for export] *)
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 PH_src13 sp rdraw brk0 argv envp uid hw E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0 PH_src13 sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.
  #[local] Notation XSTMT x := (x_stmt SEGS_src13 AT_src13 NX0 LIMIT SINV (argH0 PH_src13 sp rdraw argv envp uid hw) FS0 x).

  Theorem src13_x_sound_XEnvScan : XSTMT XEnvScan.
  Proof.
    eapply (init_x_sound_envscan SEGS_src13 AT_src13 PH_src13 src13_wx src13_in_hull src13_hull_ok
              W_b29ac W_b29b0 W_b29b4
              ltac:(cbn [x_envscan x_envscan_k AT_src13]; lia)
              (fetch_lit _ _ _ _ eq_refl F_b29ac) (fetch_lit _ _ _ _ eq_refl F_b29b0) (fetch_lit _ _ _ _ eq_refl F_b29b4)
              ltac:(repeat split; reflexivity)
              D_b29ac D_b29b0 D_b29b4
              sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit LIMIT SINV SINV_SINV0 SINV_frame).
  Qed.

  Theorem src13_x_sound_XPnScan : XSTMT XPnScan.
  Proof.
    eapply (init_x_sound_pnscan SEGS_src13 AT_src13 PH_src13 src13_wx src13_in_hull src13_hull_ok
              W_b2a68 W_b2a6c W_b2a70 W_b2a74 W_b2a78
              ltac:(cbn [x_pnscan x_pnscan_k AT_src13]; lia)
              (fetch_lit _ _ _ _ eq_refl F_b2a68) (fetch_lit _ _ _ _ eq_refl F_b2a6c) (fetch_lit _ _ _ _ eq_refl F_b2a70)
              (fetch_lit _ _ _ _ eq_refl F_b2a74) (fetch_lit _ _ _ _ eq_refl F_b2a78)
              ltac:(repeat split; reflexivity)
              D_b2a68 D_b2a6c D_b2a70 D_b2a74 D_b2a78
              sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit LIMIT SINV SINV_SINV0 SINV_frame SINV_agree).
  Qed.

  Theorem src13_x_sound_XLayout : XSTMT XLayout.
  Proof. apply x_sound_layout. Qed.
End StartX.
