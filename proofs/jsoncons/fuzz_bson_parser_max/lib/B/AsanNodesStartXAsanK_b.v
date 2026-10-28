(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
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
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PlanImagesK_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanNodesAuxK AsanStartLoops AsanNodesStartXK AsanNodesStartXInitK. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Asan_code_startxK_b.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2K. Import AX2SK. Import APK. Import APSK.
Open Scope Z_scope.

Section AsanInstance.
Variable scfg : SpuriousCfg.
  Variable sp brk0 mbase : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
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
    Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 APH0 sp rdraw brk0 argv envp uid hw E M.
    Hypothesis SINV_frame : forall E M M', (forall a, argH0 APH0 sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
    Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

    Theorem node_x_sound_XEnvScan_asan_gen : x_stmt ASEGS0 scfg ASAN0 NX0 LIMIT SINV (argH0 APH0 sp rdraw argv envp uid hw) FS0 XEnvScan.
    Proof.
      eapply (init_x_sound_envscan ASEGS0 scfg ASAN0 APH0 Asan0_wx_nowrap asan0_in_hull asan0_hull_ok
                W_1157d0 W_1157d4 W_1157d8
                ltac:(cbn [x_envscan x_envscan_k ASAN0]; lia)
                (fetch_lit _ _ _ _ eq_refl F_1157d0) (fetch_lit _ _ _ _ eq_refl F_1157d4) (fetch_lit _ _ _ _ eq_refl F_1157d8)
                ltac:(repeat split; reflexivity)
                D_1157d0 D_1157d4 D_1157d8
                sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV SINV_SINV0 SINV_frame).
    Qed.

    Theorem node_x_sound_XPnScan_asan_gen : x_stmt ASEGS0 scfg ASAN0 NX0 LIMIT SINV (argH0 APH0 sp rdraw argv envp uid hw) FS0 XPnScan.
    Proof.
      eapply (init_x_sound_pnscan ASEGS0 scfg ASAN0 APH0 Asan0_wx_nowrap asan0_in_hull asan0_hull_ok
                W_11588c W_115890 W_115894 W_115898 W_11589c
                ltac:(cbn [x_pnscan x_pnscan_k ASAN0]; lia)
                (fetch_lit _ _ _ _ eq_refl F_11588c) (fetch_lit _ _ _ _ eq_refl F_115890) (fetch_lit _ _ _ _ eq_refl F_115894)
                (fetch_lit _ _ _ _ eq_refl F_115898) (fetch_lit _ _ _ _ eq_refl F_11589c)
                ltac:(repeat split; reflexivity)
                D_11588c D_115890 D_115894 D_115898 D_11589c
                sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV SINV_SINV0 SINV_frame SINV_agree).
    Qed.

    Theorem node_x_sound_XLayout_asan_gen : x_stmt ASEGS0 scfg ASAN0 NX0 LIMIT SINV (argH0 APH0 sp rdraw argv envp uid hw) FS0 XLayout.
    Proof. apply x_sound_layout. Qed.
  End AnySINV.

  (* [comment removed for export] *)
  Theorem node_x_sound_XEnvScan_asan :
    x_stmt ASEGS0 scfg ASAN0 NX0 LIMIT (SINV0 APH0 sp rdraw brk0 argv envp uid hw) (argH0 APH0 sp rdraw argv envp uid hw) FS0 XEnvScan.
  Proof. apply node_x_sound_XEnvScan_asan_gen; [auto | apply SINV0_frame]. Qed.

  Theorem node_x_sound_XPnScan_asan :
    x_stmt ASEGS0 scfg ASAN0 NX0 LIMIT (SINV0 APH0 sp rdraw brk0 argv envp uid hw) (argH0 APH0 sp rdraw argv envp uid hw) FS0 XPnScan.
  Proof. apply node_x_sound_XPnScan_asan_gen; [auto | apply SINV0_frame | apply SINV0_agree]. Qed.

  Theorem node_x_sound_XLayout_asan :
    x_stmt ASEGS0 scfg ASAN0 NX0 LIMIT (SINV0 APH0 sp rdraw brk0 argv envp uid hw) (argH0 APH0 sp rdraw argv envp uid hw) FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End AsanInstance.
