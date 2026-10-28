(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.simdjson.fuzz_implementations.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib
  AsanAcct AsanAcctShape AsanAcctImagesB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import PropExec.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsanPlanImagesB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AsanTablesB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AsanNodesAux AsanStartLoops AsanNodesStartX AsanNodesStartXInit Asan_code_startxB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Section AsanInstance.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variable uid : word.
  Variable hw : word.
  Hypothesis Hfit : entry_stack_fits sp argv envp.

  Section AnySINV.

    Variable SINV : env -> (word -> option byte) -> Prop.
    Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 APH sp rdraw brk0 argv envp uid hw E M.
    Hypothesis SINV_frame : forall E M M', (forall a, argH0 APH sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
    Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

    Theorem node_x_sound_XEnvScan_asan_gen : x_stmt ASEGS ASAN_B NX0 LIMIT SINV (argH0 APH sp rdraw argv envp uid hw) FS0 XEnvScan.
    Proof.
      eapply (init_x_sound_envscan ASEGS ASAN_B APH asan_wx asan_in_hull asan_hull_ok
                W_88d40 W_88d44 W_88d48
                ltac:(cbn [x_envscan x_envscan_k ASAN_B]; lia)
                (fetch_lit _ _ _ _ eq_refl F_88d40) (fetch_lit _ _ _ _ eq_refl F_88d44) (fetch_lit _ _ _ _ eq_refl F_88d48)
                ltac:(repeat split; reflexivity)
                D_88d40 D_88d44 D_88d48
                sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV SINV_SINV0 SINV_frame).
    Qed.

    Theorem node_x_sound_XPnScan_asan_gen : x_stmt ASEGS ASAN_B NX0 LIMIT SINV (argH0 APH sp rdraw argv envp uid hw) FS0 XPnScan.
    Proof.
      eapply (init_x_sound_pnscan ASEGS ASAN_B APH asan_wx asan_in_hull asan_hull_ok
                W_88dfc W_88e00 W_88e04 W_88e08 W_88e0c
                ltac:(cbn [x_pnscan x_pnscan_k ASAN_B]; lia)
                (fetch_lit _ _ _ _ eq_refl F_88dfc) (fetch_lit _ _ _ _ eq_refl F_88e00) (fetch_lit _ _ _ _ eq_refl F_88e04)
                (fetch_lit _ _ _ _ eq_refl F_88e08) (fetch_lit _ _ _ _ eq_refl F_88e0c)
                ltac:(repeat split; reflexivity)
                D_88dfc D_88e00 D_88e04 D_88e08 D_88e0c
                sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV SINV_SINV0 SINV_frame SINV_agree).
    Qed.

    Theorem node_x_sound_XLayout_asan_gen : x_stmt ASEGS ASAN_B NX0 LIMIT SINV (argH0 APH sp rdraw argv envp uid hw) FS0 XLayout.
    Proof. apply x_sound_layout. Qed.
  End AnySINV.

  Theorem node_x_sound_XEnvScan_asan :
    x_stmt ASEGS ASAN_B NX0 LIMIT (SINV0 APH sp rdraw brk0 argv envp uid hw) (argH0 APH sp rdraw argv envp uid hw) FS0 XEnvScan.
  Proof. apply node_x_sound_XEnvScan_asan_gen; [auto | apply SINV0_frame]. Qed.

  Theorem node_x_sound_XPnScan_asan :
    x_stmt ASEGS ASAN_B NX0 LIMIT (SINV0 APH sp rdraw brk0 argv envp uid hw) (argH0 APH sp rdraw argv envp uid hw) FS0 XPnScan.
  Proof. apply node_x_sound_XPnScan_asan_gen; [auto | apply SINV0_frame | apply SINV0_agree]. Qed.

  Theorem node_x_sound_XLayout_asan :
    x_stmt ASEGS ASAN_B NX0 LIMIT (SINV0 APH sp rdraw brk0 argv envp uid hw) (argH0 APH sp rdraw argv envp uid hw) FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End AsanInstance.
