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

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.yajl_ruby.json_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec ShapeAlg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import StoreOk SpinAlg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import AgentLib AsanAcct AsanAcctShape.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.AS5 Require Import AsanAcctImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.AS5 Require Import AsanPlanImages5.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import AsanNodesAux AsanStartLoops AsanNodesStartX AsanNodesStartXInit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.AS5 Require Import Asan_code_startx5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Section AsanInstance.
  Variable SC : SpuriousCfg.                 (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : StackLayout.EntryDraw.     (* [comment removed for export] *)
  Variable brk0 mbase : word.
  Variable hw : word.                         (* [comment removed for export] *)
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variable uid : word.
  Hypothesis Hfit : entry_stack_fits sp argv envp.   (* [comment removed for export] *)

  Section AnySINV.
    (* [comment removed for export] *)
    Variable SINV : env -> (word -> option byte) -> Prop.
    Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 APH sp rdraw brk0 argv envp uid hw E M.
    Hypothesis SINV_frame : forall E M M', (forall a, argH0 APH sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
    (* [comment removed for export] *)
    Variable nx0 : nat.
    Hypothesis NX0_le : (NX0 <= nx0)%nat.
    Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

    Theorem node_x_sound_XEnvScan_asan_gen : x_stmt ASEGS SC ASAN5 nx0 LIMIT SINV (argH0 APH sp rdraw argv envp uid hw) FS0 XEnvScan.
    Proof.
      eapply (init_x_sound_envscan ASEGS SC ASAN5 APH asan_wx asan_in_hull asan_hull_ok
                W_910ec W_910f0 W_910f4
                ltac:(cbn [x_envscan x_envscan_k ASAN5]; lia)
                (fetch_lit _ _ _ _ eq_refl F_910ec) (fetch_lit _ _ _ _ eq_refl F_910f0) (fetch_lit _ _ _ _ eq_refl F_910f4)
                ltac:(repeat split; reflexivity)
                D_910ec D_910f0 D_910f4
                sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV SINV_SINV0 SINV_frame nx0 NX0_le).
    Qed.

    Theorem node_x_sound_XPnScan_asan_gen : x_stmt ASEGS SC ASAN5 nx0 LIMIT SINV (argH0 APH sp rdraw argv envp uid hw) FS0 XPnScan.
    Proof.
      eapply (init_x_sound_pnscan ASEGS SC ASAN5 APH asan_wx asan_in_hull asan_hull_ok
                W_911a8 W_911ac W_911b0 W_911b4 W_911b8
                ltac:(cbn [x_pnscan x_pnscan_k ASAN5]; lia)
                (fetch_lit _ _ _ _ eq_refl F_911a8) (fetch_lit _ _ _ _ eq_refl F_911ac) (fetch_lit _ _ _ _ eq_refl F_911b0)
                (fetch_lit _ _ _ _ eq_refl F_911b4) (fetch_lit _ _ _ _ eq_refl F_911b8)
                ltac:(repeat split; reflexivity)
                D_911a8 D_911ac D_911b0 D_911b4 D_911b8
                sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV SINV_SINV0 SINV_frame nx0 NX0_le SINV_agree).
    Qed.

    Theorem node_x_sound_XLayout_asan_gen : x_stmt ASEGS SC ASAN5 nx0 LIMIT SINV (argH0 APH sp rdraw argv envp uid hw) FS0 XLayout.
    Proof. apply x_sound_layout. Qed.

  End AnySINV.

  (* [comment removed for export] *)
  Theorem node_x_sound_XEnvScan_asan :
    x_stmt ASEGS SC ASAN5 NX0 LIMIT (SINV0 APH sp rdraw brk0 argv envp uid hw) (argH0 APH sp rdraw argv envp uid hw) FS0 XEnvScan.
  Proof. apply node_x_sound_XEnvScan_asan_gen; [auto | apply SINV0_frame | apply le_n]. Qed.

  Theorem node_x_sound_XPnScan_asan :
    x_stmt ASEGS SC ASAN5 NX0 LIMIT (SINV0 APH sp rdraw brk0 argv envp uid hw) (argH0 APH sp rdraw argv envp uid hw) FS0 XPnScan.
  Proof. apply node_x_sound_XPnScan_asan_gen; [auto | apply SINV0_frame | apply le_n | apply SINV0_agree]. Qed.

  Theorem node_x_sound_XLayout_asan :
    x_stmt ASEGS SC ASAN5 NX0 LIMIT (SINV0 APH sp rdraw brk0 argv envp uid hw) (argH0 APH sp rdraw argv envp uid hw) FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End AsanInstance.
