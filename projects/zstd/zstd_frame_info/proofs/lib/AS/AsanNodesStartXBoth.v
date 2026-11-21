(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (node_x_sound_XEnvScan_asan_gen, node_x_sound_XPnScan_asan_gen and node_x_sound_XLayout_asan_gen state their nodes at the run's CONFIG_RSEQ flag (RZ) over argH0's new arguments (kernel build, exec name), under the whole launch input (new section variables apc, gid, groups, net, nof, sigm, abt, urnd, kb, execfn and sdef) with valid_launch and entry_launch_ok_va hypotheses; SINV_SINV0 and SINV_frame restated for SINV0's and argH0's new arguments; #[using] lists of both scan theorems updated; node_x_sound_XEnvScan_asan, node_x_sound_XPnScan_asan and node_x_sound_XLayout_asan, stated over the old launch arguments and used by no file, removed). *)
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
From OSSVerify.zstd.zstd_frame_info.images Require Import AsanUbsan.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AS Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib
  AsanAcct AsanAcctShape AsanAcctImages.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit BothPlanImages.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AS Require Import AsanNodesAux AsanStartLoops AsanNodesStartX AsanNodesStartXInit Both_code_startx.
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
Variable hw : word.
Variable groups : list word.
Variable net : NetQueue.
Variables nof sigm : word.
Variable abt : bool.
Variable urnd : InputStream.
Variable kb : KernelBuild.
(* the exec file name and the SIGPIPE disposition, free as in AsanInit (LPS 727298f3) *)
Variable execfn : list byte.
Variable sdef : bool.
Let INP := inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb execfn sdef.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.   (* [comment removed for export] *)
Hypothesis Hlaunch : valid_launch INP.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  (* [comment removed for export] *)
  Variable LIMIT : Z.
(* the run's CONFIG_RSEQ flag as the plan's 0 or 1 (model commit 0c15dd4) *)
#[local] Notation RZ := (rseq_z (kb_rseq kb)).

  Section AnySINV.
    (* [comment removed for export] *)
    Variable SINV : env -> (word -> option byte) -> Prop.
Hypothesis SINV_SINV0 : forall E M, SINV E M ->
SINV0 BPH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb execfn sdef E M.
Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw argv envp kb execfn E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
    (* [comment removed for export] *)
    Variable nx0 : nat.
    Hypothesis Hnx0 : (NX0 <= nx0)%nat.
    Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

#[using="apc brk0 mbase fs stdin gid groups net nof sigm abt urnd Hsp Hva Hve Hfit Hlaunch Hlau SINV_SINV0 SINV_frame Hnx0"] Theorem node_x_sound_XEnvScan_asan_gen : x_stmt BSEGS BOTH nx0 LIMIT RZ SINV (argH0 sp rdraw argv envp kb execfn) FS0 XEnvScan.
    Proof.
      eapply (init_x_sound_envscan BSEGS BOTH BPH both_wx both_in_hull both_hull_ok
                W_88100 W_88104 W_88108
                ltac:(cbn [x_envscan x_envscan_k BOTH]; lia)
                (fetch_lit _ _ _ _ eq_refl F_88100) (fetch_lit _ _ _ _ eq_refl F_88104) (fetch_lit _ _ _ _ eq_refl F_88108)
                ltac:(repeat split; reflexivity)
                D_88100 D_88104 D_88108);
      eassumption.
    Qed.

#[using="apc brk0 mbase fs stdin gid groups net nof sigm abt urnd Hsp Hva Hve Hfit Hlaunch Hlau SINV_SINV0 SINV_frame Hnx0 SINV_agree"] Theorem node_x_sound_XPnScan_asan_gen : x_stmt BSEGS BOTH nx0 LIMIT RZ SINV (argH0 sp rdraw argv envp kb execfn) FS0 XPnScan.
    Proof.
      eapply (init_x_sound_pnscan BSEGS BOTH BPH both_wx both_in_hull both_hull_ok
                W_881bc W_881c0 W_881c4 W_881c8 W_881cc
                ltac:(cbn [x_pnscan x_pnscan_k BOTH]; lia)
                (fetch_lit _ _ _ _ eq_refl F_881bc) (fetch_lit _ _ _ _ eq_refl F_881c0) (fetch_lit _ _ _ _ eq_refl F_881c4)
                (fetch_lit _ _ _ _ eq_refl F_881c8) (fetch_lit _ _ _ _ eq_refl F_881cc)
                ltac:(repeat split; reflexivity)
                D_881bc D_881c0 D_881c4 D_881c8 D_881cc);
      eassumption.
    Qed.

    #[using="Type"] Theorem node_x_sound_XLayout_asan_gen : x_stmt BSEGS BOTH nx0 LIMIT RZ SINV (argH0 sp rdraw argv envp kb execfn) FS0 XLayout.
    Proof. apply x_sound_layout. Qed.
  End AnySINV.
End AsanInstance.
