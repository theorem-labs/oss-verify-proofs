(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up nodes over the launch's ProcInput, kernel build, exec file name and SIGPIPE disposition, at the run's CONFIG_RSEQ flag). *)
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
From OSSVerify.zstd.simple_decompress.images Require Import Asan.
From OSSVerify.Proofs.zstd.simple_decompress.lib.AS Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib
  AsanAcct AsanAcctShape AsanAcctImages.
From OSSVerify.Proofs.zstd.simple_decompress.lib.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsanPlanImages.
From OSSVerify.Proofs.zstd.simple_decompress.lib.AS Require Import AsanNodesAux AsanStartLoops AsanNodesStartX AsanNodesStartXInit Asan_code_startx.
(* [comment removed for export] *)
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Section AsanInstance.
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variable FS0 : Fs.Fs.
  Variable uid gid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Variable groups : list word.
  Variable net : NetQueue.
  (* the input fields the start-up does not pin (AsanInit.inp); the kernel build, the exec file
     name and the SIGPIPE disposition are free as in AsanInit (LPS 727298f3) *)
  Variables nof sigm : word.
  Variable abt : bool.
  Variable urnd : InputStream.
  Variable tmp : Fs.Fs.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variable sdef : bool.
  Let INP := inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmp kb execfn sdef.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.   (* [comment removed for export] *)
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  (* the run's CONFIG_RSEQ flag as the plan's 0 or 1 (model commit 0c15dd4) *)
  #[local] Notation RZ := (rseq_z (kb_rseq kb)).

  Section AnySINV.
    (* [comment removed for export] *)
    Variable SINV : env -> (word -> option byte) -> Prop.
    Hypothesis SINV_SINV0 : forall E M, SINV E M ->
      SINV0 BPH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmp kb execfn sdef E M.
    Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw argv envp kb execfn E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
    (* [comment removed for export] *)
    Variable nx0 : nat.
    Hypothesis Hnx0 : (NX0 <= nx0)%nat.
    Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

    Theorem node_x_sound_XEnvScan_asan_gen : x_stmt BSEGS ASAN nx0 LIMIT RZ SINV (argH0 sp rdraw argv envp kb execfn) FS0 XEnvScan.
    Proof.
      eapply (init_x_sound_envscan BSEGS ASAN BPH both_wx both_in_hull both_hull_ok
                W_bacc4 W_bacc8 W_baccc
                ltac:(cbn [x_envscan x_envscan_k ASAN]; lia)
                (fetch_lit _ _ _ _ eq_refl F_bacc4) (fetch_lit _ _ _ _ eq_refl F_bacc8) (fetch_lit _ _ _ _ eq_refl F_baccc)
                ltac:(repeat split; reflexivity)
                D_bacc4 D_bacc8 D_baccc);
        eassumption.
    Qed.

    Theorem node_x_sound_XPnScan_asan_gen : x_stmt BSEGS ASAN nx0 LIMIT RZ SINV (argH0 sp rdraw argv envp kb execfn) FS0 XPnScan.
    Proof.
      eapply (init_x_sound_pnscan BSEGS ASAN BPH both_wx both_in_hull both_hull_ok
                W_bad80 W_bad84 W_bad88 W_bad8c W_bad90
                ltac:(cbn [x_pnscan x_pnscan_k ASAN]; lia)
                (fetch_lit _ _ _ _ eq_refl F_bad80) (fetch_lit _ _ _ _ eq_refl F_bad84) (fetch_lit _ _ _ _ eq_refl F_bad88)
                (fetch_lit _ _ _ _ eq_refl F_bad8c) (fetch_lit _ _ _ _ eq_refl F_bad90)
                ltac:(repeat split; reflexivity)
                D_bad80 D_bad84 D_bad88 D_bad8c D_bad90);
        eassumption.
    Qed.

    Theorem node_x_sound_XLayout_asan_gen : x_stmt BSEGS ASAN nx0 LIMIT RZ SINV (argH0 sp rdraw argv envp kb execfn) FS0 XLayout.
    Proof. apply x_sound_layout. Qed.
  End AnySINV.

  (* [comment removed for export] *)
  Theorem node_x_sound_XEnvScan_asan :
    x_stmt BSEGS ASAN NX0 LIMIT RZ (SINV0 BPH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmp kb execfn sdef)
      (argH0 sp rdraw argv envp kb execfn) FS0 XEnvScan.
  Proof.
    eapply node_x_sound_XEnvScan_asan_gen; [exact (fun E M H => H) | apply SINV0_frame | apply le_n].
  Qed.

  Theorem node_x_sound_XPnScan_asan :
    x_stmt BSEGS ASAN NX0 LIMIT RZ (SINV0 BPH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmp kb execfn sdef)
      (argH0 sp rdraw argv envp kb execfn) FS0 XPnScan.
  Proof.
    eapply node_x_sound_XPnScan_asan_gen; [exact (fun E M H => H) | apply SINV0_frame | apply le_n | apply SINV0_agree].
  Qed.

  Theorem node_x_sound_XLayout_asan :
    x_stmt BSEGS ASAN NX0 LIMIT RZ (SINV0 BPH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmp kb execfn sdef)
      (argH0 sp rdraw argv envp kb execfn) FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End AsanInstance.
