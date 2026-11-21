(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's validity hypotheses; the process input's new fields; the SIGPIPE disposition). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgA.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanAcct AsanAcctShape AsanAcctImages.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsanPlanImages AsanPlanImagesInit.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanNodesAux AsanStartLoops AsanNodesStartX AsanNodesStartXInit .
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import Asan_code_10a000_10b000.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Section AsanInstance.
  Context {fx : PropExec.FPState}.
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variable uid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Variable LINV : (word -> option byte) -> Prop.
  Hypothesis LINV_frame : forall M M' : word -> option byte,
    (forall a : word, in_lfp ASAN (bv_unsigned a) = true -> M' a = M a) -> LINV M -> LINV M'.
  Variable apc : N.
  Variable gid : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variable ur : InputStream.
  Variable kern : KernelBuild.
  Variable execfn : list byte.
  Variable nofile : word.
  Variable sigmask : word.
  Variables abt sdf : bool.

  (* #38's AsanNodesStartXInit.GenericInit carries the three launch facts (that file's :87-:89),
     because the strings are no longer at a literal offset above sp and NOTHING BUT
     entry_launch_ok_va pins the arch_align_stack pad (CatExec.v:407-411).  They are stated here
     exactly as AsanNodesArgAsan.v:90-91 states them, over the same `inp` application, and they
     sit after `abt` so this Section's order matches GenericInit's. *)
  Hypothesis Hkernel : in_kernel (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf) = recorded_kernel (in_kernel (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf)).
  Hypothesis Hlaunch : valid_launch (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf).
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf).

  Section AnySINV.
    (* [comment removed for export] *)
    Variable SINV : env -> (word -> option byte) -> Prop.
    Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 APH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf E M.
    Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw argv envp kern execfn E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
    Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

    Theorem node_x_sound_XEnvScan_asan_gen : x_stmt ASEGS ASAN NX0 LIMIT SINV (argH0 sp rdraw argv envp kern execfn) LINV FS0 XEnvScan.
    Proof.
      eapply (init_x_sound_envscan ASEGS ASAN APH asan_wx asan_in_hull asan_hull_ok
                W_10b068 W_10b06c W_10b070
                ltac:(cbn [x_envscan x_envscan_k ASAN]; lia)
                (fetch_lit _ _ _ _ eq_refl F_10b068) (fetch_lit _ _ _ _ eq_refl F_10b06c) (fetch_lit _ _ _ _ eq_refl F_10b070)
                ltac:(repeat split; reflexivity)
                D_10b068 D_10b06c D_10b070
                apc sp rdraw brk0 mbase argv envp fs stdin FS0 uid gid hw groups net ur kern execfn nofile sigmask abt sdf
                Hsp Hva Hve Hfit Hlaunch Hlau SINV SINV_SINV0 SINV_frame LINV LINV_frame).
    Qed.

    Theorem node_x_sound_XPnScan_asan_gen : x_stmt ASEGS ASAN NX0 LIMIT SINV (argH0 sp rdraw argv envp kern execfn) LINV FS0 XPnScan.
    Proof.
      eapply (init_x_sound_pnscan ASEGS ASAN APH asan_wx asan_in_hull asan_hull_ok
                W_10b124 W_10b128 W_10b12c W_10b130 W_10b134
                ltac:(cbn [x_pnscan x_pnscan_k ASAN]; lia)
                (fetch_lit _ _ _ _ eq_refl F_10b124) (fetch_lit _ _ _ _ eq_refl F_10b128) (fetch_lit _ _ _ _ eq_refl F_10b12c)
                (fetch_lit _ _ _ _ eq_refl F_10b130) (fetch_lit _ _ _ _ eq_refl F_10b134)
                ltac:(repeat split; reflexivity)
                D_10b124 D_10b128 D_10b12c D_10b130 D_10b134
                apc sp rdraw brk0 mbase argv envp fs stdin FS0 uid gid hw groups net ur kern execfn nofile sigmask abt sdf
                Hsp Hva Hve Hfit Hlau SINV SINV_SINV0 SINV_frame SINV_agree LINV LINV_frame).
    Qed.

    Theorem node_x_sound_XLayout_asan_gen : x_stmt ASEGS ASAN NX0 LIMIT SINV (argH0 sp rdraw argv envp kern execfn) LINV FS0 XLayout.
    Proof. apply x_sound_layout. Qed.
  End AnySINV.

  (* [comment removed for export] *)
  Theorem node_x_sound_XEnvScan_asan :
    x_stmt ASEGS ASAN NX0 LIMIT (SINV0 APH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf) (argH0 sp rdraw argv envp kern execfn) LINV FS0 XEnvScan.
  Proof. apply node_x_sound_XEnvScan_asan_gen; [auto | apply SINV0_frame]. Qed.

  Theorem node_x_sound_XPnScan_asan :
    x_stmt ASEGS ASAN NX0 LIMIT (SINV0 APH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf) (argH0 sp rdraw argv envp kern execfn) LINV FS0 XPnScan.
  Proof. apply node_x_sound_XPnScan_asan_gen; [auto | apply SINV0_frame | apply SINV0_agree]. Qed.

  Theorem node_x_sound_XLayout_asan :
    x_stmt ASEGS ASAN NX0 LIMIT (SINV0 APH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf) (argH0 sp rdraw argv envp kern execfn) LINV FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End AsanInstance.
