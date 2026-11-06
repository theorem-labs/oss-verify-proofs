(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AsanNodesAux AsanStartLoops AsanNodesStartX AsanNodesStartXInit. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import Img_utf8_ubsan Code_startx_utf8_ubsan.
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
  Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 PH_utf8_ubsan sp rdraw brk0 argv envp uid hw E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0 PH_utf8_ubsan sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.
  #[local] Notation XSTMT x := (x_stmt SEGS_utf8_ubsan AT_utf8_ubsan NX0 LIMIT SINV (argH0 PH_utf8_ubsan sp rdraw argv envp uid hw) FS0 x).

  Theorem utf8_ubsan_x_sound_XEnvScan : XSTMT XEnvScan.
  Proof.
    eapply (init_x_sound_envscan SEGS_utf8_ubsan AT_utf8_ubsan PH_utf8_ubsan utf8_ubsan_wx utf8_ubsan_in_hull utf8_ubsan_hull_ok
              W_bcb60 W_bcb64 W_bcb68
              ltac:(cbn [x_envscan x_envscan_k AT_utf8_ubsan]; lia)
              (fetch_lit _ _ _ _ eq_refl F_bcb60) (fetch_lit _ _ _ _ eq_refl F_bcb64) (fetch_lit _ _ _ _ eq_refl F_bcb68)
              ltac:(repeat split; reflexivity)
              D_bcb60 D_bcb64 D_bcb68
              sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit LIMIT SINV SINV_SINV0 SINV_frame).
  Qed.

  Theorem utf8_ubsan_x_sound_XPnScan : XSTMT XPnScan.
  Proof.
    eapply (init_x_sound_pnscan SEGS_utf8_ubsan AT_utf8_ubsan PH_utf8_ubsan utf8_ubsan_wx utf8_ubsan_in_hull utf8_ubsan_hull_ok
              W_bcc1c W_bcc20 W_bcc24 W_bcc28 W_bcc2c
              ltac:(cbn [x_pnscan x_pnscan_k AT_utf8_ubsan]; lia)
              (fetch_lit _ _ _ _ eq_refl F_bcc1c) (fetch_lit _ _ _ _ eq_refl F_bcc20) (fetch_lit _ _ _ _ eq_refl F_bcc24)
              (fetch_lit _ _ _ _ eq_refl F_bcc28) (fetch_lit _ _ _ _ eq_refl F_bcc2c)
              ltac:(repeat split; reflexivity)
              D_bcc1c D_bcc20 D_bcc24 D_bcc28 D_bcc2c
              sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit LIMIT SINV SINV_SINV0 SINV_frame SINV_agree).
  Qed.

  Theorem utf8_ubsan_x_sound_XLayout : XSTMT XLayout.
  Proof. apply x_sound_layout. Qed.
End StartX.
