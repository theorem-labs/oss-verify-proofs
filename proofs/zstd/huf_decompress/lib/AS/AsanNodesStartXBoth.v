(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)








From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.zstd.huf_decompress.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.AS Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib
  AsanAcct AsanAcctShape AsanAcctImages.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit BothPlanImages.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.AS Require Import AsanNodesAux AsanStartLoops AsanNodesStartX AsanNodesStartXInit Both_code_startx.

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
  
  Variable LIMIT : Z.

  Section AnySINV.
    
    Variable SINV : env -> (word -> option byte) -> Prop.
    Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 APH sp rdraw brk0 argv envp uid hw E M.
    Hypothesis SINV_frame : forall E M M', (forall a, argH0 APH sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
    
    Variable nx0 : nat.
    Hypothesis Hnx0 : (NX0 <= nx0)%nat.
    Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

    Theorem node_x_sound_XEnvScan_asan_gen : x_stmt ASEGS BOTH nx0 LIMIT SINV (argH0 APH sp rdraw argv envp uid hw) FS0 XEnvScan.
Proof.
      eapply (init_x_sound_envscan ASEGS BOTH APH asan_wx asan_in_hull asan_hull_ok
                W_9e890 W_9e894 W_9e898
                ltac:(cbn [x_envscan x_envscan_k BOTH]; lia)
                (fetch_lit _ _ _ _ eq_refl F_9e890) (fetch_lit _ _ _ _ eq_refl F_9e894) (fetch_lit _ _ _ _ eq_refl F_9e898)
                ltac:(repeat split; reflexivity)
                D_9e890 D_9e894 D_9e898
                sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV SINV_SINV0 SINV_frame nx0 Hnx0).
    Qed.

    Theorem node_x_sound_XPnScan_asan_gen : x_stmt ASEGS BOTH nx0 LIMIT SINV (argH0 APH sp rdraw argv envp uid hw) FS0 XPnScan.
Proof.
      eapply (init_x_sound_pnscan ASEGS BOTH APH asan_wx asan_in_hull asan_hull_ok
                W_9e94c W_9e950 W_9e954 W_9e958 W_9e95c
                ltac:(cbn [x_pnscan x_pnscan_k BOTH]; lia)
                (fetch_lit _ _ _ _ eq_refl F_9e94c) (fetch_lit _ _ _ _ eq_refl F_9e950) (fetch_lit _ _ _ _ eq_refl F_9e954)
                (fetch_lit _ _ _ _ eq_refl F_9e958) (fetch_lit _ _ _ _ eq_refl F_9e95c)
                ltac:(repeat split; reflexivity)
                D_9e94c D_9e950 D_9e954 D_9e958 D_9e95c
                sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV SINV_SINV0 SINV_frame nx0 Hnx0 SINV_agree).
    Qed.

    Theorem node_x_sound_XLayout_asan_gen : x_stmt ASEGS BOTH nx0 LIMIT SINV (argH0 APH sp rdraw argv envp uid hw) FS0 XLayout.
Proof. apply x_sound_layout. Qed.
  End AnySINV.

  
  Theorem node_x_sound_XEnvScan_asan :
    x_stmt ASEGS BOTH NX0 LIMIT (SINV0 APH sp rdraw brk0 argv envp uid hw) (argH0 APH sp rdraw argv envp uid hw) FS0 XEnvScan.
Proof. apply node_x_sound_XEnvScan_asan_gen; [auto | apply SINV0_frame | apply le_n]. Qed.

  Theorem node_x_sound_XPnScan_asan :
    x_stmt ASEGS BOTH NX0 LIMIT (SINV0 APH sp rdraw brk0 argv envp uid hw) (argH0 APH sp rdraw argv envp uid hw) FS0 XPnScan.
Proof. apply (node_x_sound_XPnScan_asan_gen _ (fun E M H => H) (SINV0_frame APH sp rdraw brk0 argv envp uid hw) NX0 (le_n NX0) (SINV0_agree APH sp rdraw brk0 argv envp uid hw)). Qed.

  Theorem node_x_sound_XLayout_asan :
    x_stmt ASEGS BOTH NX0 LIMIT (SINV0 APH sp rdraw brk0 argv envp uid hw) (argH0 APH sp rdraw argv envp uid hw) FS0 XLayout.
Proof. apply x_sound_layout. Qed.
End AsanInstance.
