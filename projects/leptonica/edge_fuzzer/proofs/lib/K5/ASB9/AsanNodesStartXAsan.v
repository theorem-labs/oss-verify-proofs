(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.leptonica.edge_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.ASB9 Require Import AsanAcctImages.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import PropExec.  (* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.ASB9 Require Import AsanPlanImages.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.ASB9 Require Import AsanTablesA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import AsanNodesAux AsanStartLoops AsanNodesStartX AsanNodesStartXInit.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.ASB9 Require Import Asan_code_startx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Section AsanInstance.
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variable uid : word.
  Variable hw : word.           (* [comment removed for export] *)
  Hypothesis Hfit : entry_stack_fits sp argv envp.   (* [comment removed for export] *)

  Section AnySINV.
    (* [comment removed for export] *)
    Variable SINV : env -> (word -> option byte) -> Prop.
    Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 APH sp rdraw brk0 argv envp uid hw E M.
    Hypothesis SINV_frame : forall E M M', (forall a, argH0 APH sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
    Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

    Theorem node_x_sound_XEnvScan_asan_gen : x_stmt ASEGS ASAN_A NX0 LIMIT SINV (argH0 APH sp rdraw argv envp uid hw) FS0 XEnvScan.
    Proof.
      eapply (init_x_sound_envscan ASEGS ASAN_A APH asan_wx asan_in_hull asan_hull_ok
                W_1b0bf0 W_1b0bf4 W_1b0bf8
                ltac:(cbn [x_envscan x_envscan_k ASAN_A]; lia)
                (fetch_lit _ _ _ _ eq_refl F_1b0bf0) (fetch_lit _ _ _ _ eq_refl F_1b0bf4) (fetch_lit _ _ _ _ eq_refl F_1b0bf8)
                ltac:(repeat split; reflexivity)
                D_1b0bf0 D_1b0bf4 D_1b0bf8
                sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV SINV_SINV0 SINV_frame).
    Qed.

    Theorem node_x_sound_XPnScan_asan_gen : x_stmt ASEGS ASAN_A NX0 LIMIT SINV (argH0 APH sp rdraw argv envp uid hw) FS0 XPnScan.
    Proof.
      eapply (init_x_sound_pnscan ASEGS ASAN_A APH asan_wx asan_in_hull asan_hull_ok
                W_1b0cac W_1b0cb0 W_1b0cb4 W_1b0cb8 W_1b0cbc
                ltac:(cbn [x_pnscan x_pnscan_k ASAN_A]; lia)
                (fetch_lit _ _ _ _ eq_refl F_1b0cac) (fetch_lit _ _ _ _ eq_refl F_1b0cb0) (fetch_lit _ _ _ _ eq_refl F_1b0cb4)
                (fetch_lit _ _ _ _ eq_refl F_1b0cb8) (fetch_lit _ _ _ _ eq_refl F_1b0cbc)
                ltac:(repeat split; reflexivity)
                D_1b0cac D_1b0cb0 D_1b0cb4 D_1b0cb8 D_1b0cbc
                sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV SINV_SINV0 SINV_frame SINV_agree).
    Qed.

    Theorem node_x_sound_XLayout_asan_gen : x_stmt ASEGS ASAN_A NX0 LIMIT SINV (argH0 APH sp rdraw argv envp uid hw) FS0 XLayout.
    Proof. apply x_sound_layout. Qed.
  End AnySINV.

  (* [comment removed for export] *)
  Theorem node_x_sound_XEnvScan_asan :
    x_stmt ASEGS ASAN_A NX0 LIMIT (SINV0 APH sp rdraw brk0 argv envp uid hw) (argH0 APH sp rdraw argv envp uid hw) FS0 XEnvScan.
  Proof. apply node_x_sound_XEnvScan_asan_gen; [auto | apply SINV0_frame]. Qed.

  Theorem node_x_sound_XPnScan_asan :
    x_stmt ASEGS ASAN_A NX0 LIMIT (SINV0 APH sp rdraw brk0 argv envp uid hw) (argH0 APH sp rdraw argv envp uid hw) FS0 XPnScan.
  Proof. apply node_x_sound_XPnScan_asan_gen; [auto | apply SINV0_frame | apply SINV0_agree]. Qed.

  Theorem node_x_sound_XLayout_asan :
    x_stmt ASEGS ASAN_A NX0 LIMIT (SINV0 APH sp rdraw brk0 argv envp uid hw) (argH0 APH sp rdraw argv envp uid hw) FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End AsanInstance.
