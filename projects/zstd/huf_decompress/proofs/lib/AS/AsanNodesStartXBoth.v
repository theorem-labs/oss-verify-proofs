(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (node_x_sound_XEnvScan_asan_gen, node_x_sound_XPnScan_asan_gen and node_x_sound_XLayout_asan_gen state their nodes at the run's CONFIG_RSEQ flag (RZ) over argH0's new arguments (kernel build, exec name), under the whole launch input (new section variables apc, gid, groups, net, nof, sigm, abt, urnd, kb, execfn and sdef) with valid_launch and entry_launch_ok_va hypotheses; SINV_SINV0 and SINV_frame restated for SINV0's and argH0's new arguments; #[using] lists of both scan theorems updated; node_x_sound_XEnvScan_asan, node_x_sound_XPnScan_asan and node_x_sound_XLayout_asan, stated over the old launch arguments and used by no file, removed; node_x_sound_XEnvScan_asan, node_x_sound_XPnScan_asan, node_x_sound_XLayout_asan dropped; the port of zstd/zstd_frame_info's same file, naming this unit's scan-loop code facts and image lemmas). *)
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
From OSSVerify.zstd.huf_decompress.images Require Import AsanUbsan.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib
  AsanAcct AsanAcctShape AsanAcctImages.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit BothPlanImages.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import AsanNodesAux AsanStartLoops AsanNodesStartX AsanNodesStartXInit Both_code_startx.
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
SINV0 APH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb execfn sdef E M.
Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw argv envp kb execfn E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
    (* [comment removed for export] *)
    Variable nx0 : nat.
    Hypothesis Hnx0 : (NX0 <= nx0)%nat.
    Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

#[using="apc brk0 mbase fs stdin gid groups net nof sigm abt urnd Hsp Hva Hve Hfit Hlaunch Hlau SINV_SINV0 SINV_frame Hnx0"] Theorem node_x_sound_XEnvScan_asan_gen : x_stmt ASEGS BOTH nx0 LIMIT RZ SINV (argH0 sp rdraw argv envp kb execfn) FS0 XEnvScan.
    Proof.
      eapply (init_x_sound_envscan ASEGS BOTH APH asan_wx asan_in_hull asan_hull_ok
                W_9e890 W_9e894 W_9e898
                ltac:(cbn [x_envscan x_envscan_k BOTH]; lia)
                (fetch_lit _ _ _ _ eq_refl F_9e890) (fetch_lit _ _ _ _ eq_refl F_9e894) (fetch_lit _ _ _ _ eq_refl F_9e898)
                ltac:(repeat split; reflexivity)
                D_9e890 D_9e894 D_9e898);
      eassumption.
    Qed.

#[using="apc brk0 mbase fs stdin gid groups net nof sigm abt urnd Hsp Hva Hve Hfit Hlaunch Hlau SINV_SINV0 SINV_frame Hnx0 SINV_agree"] Theorem node_x_sound_XPnScan_asan_gen : x_stmt ASEGS BOTH nx0 LIMIT RZ SINV (argH0 sp rdraw argv envp kb execfn) FS0 XPnScan.
    Proof.
      eapply (init_x_sound_pnscan ASEGS BOTH APH asan_wx asan_in_hull asan_hull_ok
                W_9e94c W_9e950 W_9e954 W_9e958 W_9e95c
                ltac:(cbn [x_pnscan x_pnscan_k BOTH]; lia)
                (fetch_lit _ _ _ _ eq_refl F_9e94c) (fetch_lit _ _ _ _ eq_refl F_9e950) (fetch_lit _ _ _ _ eq_refl F_9e954)
                (fetch_lit _ _ _ _ eq_refl F_9e958) (fetch_lit _ _ _ _ eq_refl F_9e95c)
                ltac:(repeat split; reflexivity)
                D_9e94c D_9e950 D_9e954 D_9e958 D_9e95c);
      eassumption.
    Qed.

    #[using="Type"] Theorem node_x_sound_XLayout_asan_gen : x_stmt ASEGS BOTH nx0 LIMIT RZ SINV (argH0 sp rdraw argv envp kb execfn) FS0 XLayout.
    Proof. apply x_sound_layout. Qed.
  End AnySINV.
End AsanInstance.
