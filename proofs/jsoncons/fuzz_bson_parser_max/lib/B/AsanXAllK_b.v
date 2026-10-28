(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec ShapeAlg SpinAlg AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanCoreK AsanPlanK AsanPlanSoundK
  AsanInitK. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DefsK_b Ba0PlanImagesK_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanNodesStartXK. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import AsanNodesStartXAsanK_b SumsAsanCloseK_b.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2K. Import AX2SK. Import APCK. Import APK. Import APSK.
Open Scope Z_scope.

Section XAll.
Variable scfg : SpuriousCfg.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variables argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.

  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).

  Theorem asan_X_ALL : forall x, x_stmt ASEGS0 scfg ASAN0 NX0 AsanInitK.LIMIT SINV argH fs x.
  Proof.
    pose proof (argH0_high APH0 sp rdraw argv envp uid hw Hsp Hva) as AH.
    pose proof (argH0_agree APH0 sp rdraw argv envp uid hw) as AA.
    pose proof (SINV0_frame APH0 sp rdraw brk0 argv envp uid hw) as SF.
    pose proof (SINV0_agree APH0 sp rdraw brk0 argv envp uid hw) as SA.
    pose proof e_sp0_init as EI.
    intros [ | | | | | | | | | | ].
    - eapply asan_node_x_sound_XIMemset; eassumption.
    - eapply asan_node_x_sound_XIMemcpy; eassumption.
    - eapply asan_node_x_sound_XMemset; eassumption.
    - eapply asan_node_x_sound_XMemcpy; eassumption.
    - eapply asan_node_x_sound_XMemIsZero; eassumption.
    - eapply node_x_sound_XEnvScan_asan; eassumption.
    - eapply node_x_sound_XPnScan_asan; eassumption.
    - apply x_sound_layout.
    - eapply asan_node_x_sound_XIStrncpy; eassumption.
    - eapply asan_node_x_sound_XPopFree; eassumption.
    - (* [comment removed for export] *) intros args cs cs' E R FULL model T HC HE H. cbn [node_x] in H. discriminate H.
  Qed.
End XAll.
