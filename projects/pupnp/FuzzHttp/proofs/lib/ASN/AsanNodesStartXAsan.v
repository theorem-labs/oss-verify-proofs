(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.pupnp.FuzzHttp.images Require Import Asan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib
  AsanAcct AsanAcctShape AsanAcctImages.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsanPlanImages.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AsanNodesAux AsanStartLoops AsanNodesStartX AsanNodesStartXInit Asan_code_startx.

Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
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

    Variable nx0 : nat.
    Hypothesis Hnx0 : (NX0 <= nx0)%nat.
    Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

    #[using="brk0 Hsp Hva Hve Hfit SINV_SINV0 SINV_frame Hnx0"] Theorem node_x_sound_XEnvScan_asan_gen : x_stmt ASEGS ASAN nx0 LIMIT SINV (argH0 APH sp rdraw argv envp uid hw) FS0 XEnvScan.
    Proof.
      eapply (init_x_sound_envscan ASEGS ASAN APH asan_wx asan_in_hull asan_hull_ok
                W_93d80 W_93d84 W_93d88
                ltac:(cbn [x_envscan x_envscan_k ASAN]; lia)
                (fetch_lit _ _ _ _ eq_refl F_93d80) (fetch_lit _ _ _ _ eq_refl F_93d84) (fetch_lit _ _ _ _ eq_refl F_93d88)
                ltac:(repeat split; reflexivity)
                D_93d80 D_93d84 D_93d88
                sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV SINV_SINV0 SINV_frame nx0 Hnx0).
    Qed.

    #[using="brk0 Hsp Hva Hve Hfit SINV_SINV0 SINV_frame Hnx0 SINV_agree"] Theorem node_x_sound_XPnScan_asan_gen : x_stmt ASEGS ASAN nx0 LIMIT SINV (argH0 APH sp rdraw argv envp uid hw) FS0 XPnScan.
    Proof.
      eapply (init_x_sound_pnscan ASEGS ASAN APH asan_wx asan_in_hull asan_hull_ok
                W_93e3c W_93e40 W_93e44 W_93e48 W_93e4c
                ltac:(cbn [x_pnscan x_pnscan_k ASAN]; lia)
                (fetch_lit _ _ _ _ eq_refl F_93e3c) (fetch_lit _ _ _ _ eq_refl F_93e40) (fetch_lit _ _ _ _ eq_refl F_93e44)
                (fetch_lit _ _ _ _ eq_refl F_93e48) (fetch_lit _ _ _ _ eq_refl F_93e4c)
                ltac:(repeat split; reflexivity)
                D_93e3c D_93e40 D_93e44 D_93e48 D_93e4c
                sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV SINV_SINV0 SINV_frame nx0 Hnx0 SINV_agree).
    Qed.

    #[using="Type"] Theorem node_x_sound_XLayout_asan_gen : x_stmt ASEGS ASAN nx0 LIMIT SINV (argH0 APH sp rdraw argv envp uid hw) FS0 XLayout.
    Proof. apply x_sound_layout. Qed.
  End AnySINV.

  #[using="Hsp Hva Hve Hfit"] Theorem node_x_sound_XEnvScan_asan :
    x_stmt ASEGS ASAN NX0 LIMIT (SINV0 APH sp rdraw brk0 argv envp uid hw) (argH0 APH sp rdraw argv envp uid hw) FS0 XEnvScan.
  Proof. apply node_x_sound_XEnvScan_asan_gen; [auto | apply SINV0_frame | apply le_n]. Qed.

  #[using="Hsp Hva Hve Hfit"] Theorem node_x_sound_XPnScan_asan :
    x_stmt ASEGS ASAN NX0 LIMIT (SINV0 APH sp rdraw brk0 argv envp uid hw) (argH0 APH sp rdraw argv envp uid hw) FS0 XPnScan.
  Proof. apply (node_x_sound_XPnScan_asan_gen _ (fun E M H => H) (SINV0_frame APH sp rdraw brk0 argv envp uid hw) NX0 (le_n NX0) (SINV0_agree APH sp rdraw brk0 argv envp uid hw)). Qed.

  #[using="Type"] Theorem node_x_sound_XLayout_asan :
    x_stmt ASEGS ASAN NX0 LIMIT (SINV0 APH sp rdraw brk0 argv envp uid hw) (argH0 APH sp rdraw argv envp uid hw) FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End AsanInstance.
