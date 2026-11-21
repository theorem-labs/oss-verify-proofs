(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.World Require Import Tgt_zlib_uncompress_fuzzer_both.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.AS Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib
  AsanAcct AsanAcctShape AsanAcctImages.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit BothPlanImages.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.AS Require Import AsanNodesAux AsanStartLoops AsanNodesStartX AsanNodesStartXInit Both_code_startx.
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
  (* the launch, as AsanInit takes it *)
  Variable apc : N.
  Variable gid : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variable kb : KernelBuild.
  Variables nof sigm : word.
  Variable abt : bool.
  Variable urnd : InputStream.
  Variable efn : list byte.
  Variable sigdef : bool.
  Let INP := AsanInit.inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb efn sigdef.
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  (* the run reads ASEGS ++ VSEGS (declared last, so callers append it after Hlau) *)
  Variable VSEGS : list Segment.
  Hypothesis VSEGS_nx : Forall (fun s => seg_executable s = false) VSEGS.

  #[local] Notation SINVA := (SINV0 BPH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb efn sigdef).
  #[local] Notation ARGH := (argH0 sp rdraw argv envp kb efn).
  #[local] Notation RZK := (rseq_z (kb_rseq kb)).

  Section AnySINV.
    Variable SINV : env -> (word -> option byte) -> Prop.
    Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINVA E M.
    Hypothesis SINV_frame : forall E M M', (forall a, ARGH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
    Variable nx0 : nat.
    Hypothesis Hnx0 : (NX0 <= nx0)%nat.
    Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

    Theorem node_x_sound_XEnvScan_asan_gen : x_stmt BSEGS VSEGS BOTH nx0 LIMIT RZK SINV ARGH FS0 XEnvScan.
    Proof.
      eapply (init_x_sound_envscan BSEGS VSEGS VSEGS_nx BOTH BPH both_wx both_in_hull both_hull_ok
                W_bcc74 W_bcc78 W_bcc7c
                ltac:(cbn [x_envscan x_envscan_k BOTH]; lia)
                (fetch_lit _ _ _ _ eq_refl F_bcc74) (fetch_lit _ _ _ _ eq_refl F_bcc78) (fetch_lit _ _ _ _ eq_refl F_bcc7c)
                ltac:(repeat split; reflexivity)
                D_bcc74 D_bcc78 D_bcc7c
                apc sp rdraw brk0 mbase argv envp fs stdin FS0 uid gid hw groups net kb nof sigm abt urnd efn sigdef
                Hsp Hva Hve Hfit Hlaunch Hlau SINV SINV_SINV0 SINV_frame nx0 Hnx0).
    Qed.

    Theorem node_x_sound_XPnScan_asan_gen : x_stmt BSEGS VSEGS BOTH nx0 LIMIT RZK SINV ARGH FS0 XPnScan.
    Proof.
      eapply (init_x_sound_pnscan BSEGS VSEGS VSEGS_nx BOTH BPH both_wx both_in_hull both_hull_ok
                W_bcd30 W_bcd34 W_bcd38 W_bcd3c W_bcd40
                ltac:(cbn [x_pnscan x_pnscan_k BOTH]; lia)
                (fetch_lit _ _ _ _ eq_refl F_bcd30) (fetch_lit _ _ _ _ eq_refl F_bcd34) (fetch_lit _ _ _ _ eq_refl F_bcd38)
                (fetch_lit _ _ _ _ eq_refl F_bcd3c) (fetch_lit _ _ _ _ eq_refl F_bcd40)
                ltac:(repeat split; reflexivity)
                D_bcd30 D_bcd34 D_bcd38 D_bcd3c D_bcd40
                apc sp rdraw brk0 mbase argv envp fs stdin FS0 uid gid hw groups net kb nof sigm abt urnd efn sigdef
                Hsp Hva Hve Hfit Hlau SINV SINV_SINV0 SINV_frame nx0 Hnx0 SINV_agree).
    Qed.

    Theorem node_x_sound_XLayout_asan_gen : x_stmt BSEGS VSEGS BOTH nx0 LIMIT RZK SINV ARGH FS0 XLayout.
    Proof. apply x_sound_layout. Qed.
  End AnySINV.

  Theorem node_x_sound_XEnvScan_asan :
    x_stmt BSEGS VSEGS BOTH NX0 LIMIT RZK SINVA ARGH FS0 XEnvScan.
  Proof. apply node_x_sound_XEnvScan_asan_gen; [auto | apply SINV0_frame | apply le_n]. Qed.

  Theorem node_x_sound_XPnScan_asan :
    x_stmt BSEGS VSEGS BOTH NX0 LIMIT RZK SINVA ARGH FS0 XPnScan.
  Proof.
    apply (node_x_sound_XPnScan_asan_gen _ (fun E M H => H)
             (SINV0_frame BPH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb efn sigdef)
             NX0 (le_n NX0)
             (SINV0_agree BPH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd kb efn sigdef)).
  Qed.

  Theorem node_x_sound_XLayout_asan :
    x_stmt BSEGS VSEGS BOTH NX0 LIMIT RZK SINVA ARGH FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End AsanInstance.
