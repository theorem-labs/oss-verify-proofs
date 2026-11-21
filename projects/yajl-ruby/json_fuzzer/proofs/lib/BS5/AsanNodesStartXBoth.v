(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the instance's envscan, pnscan and layout theorems take the launch's whole ProcInput (gid, kernel build kb, execfn and the rest), its entry, recorded kernel, valid_launch and entry_launch_ok_va, and pass x_stmt the CONFIG_RSEQ value of kb; the NX0 corollaries are dropped). *)
(* [comment removed for export] *)
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
From OSSVerify.yajl_ruby.json_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec ShapeAlg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import StoreOk SpinAlg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import AgentLib AsanAcct AsanAcctShape.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.BS5 Require Import BothAcctImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.BS5 Require Import AsanPlanImagesB.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import AsanNodesAux AsanStartLoops AsanNodesStartX AsanNodesStartXInit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.BS5 Require Import Asan_code_startxB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Section AsanInstance.
  Variable SC : SpuriousCfg.
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : StackLayout.EntryDraw.
  Variable brk0 mbase : word.
  Variable hw : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variable FS0 : Fs.Fs.
  Variables uid gid : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.
  Variable urnd : InputStream.
  Variable tmp : Fs.Fs.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variables rdr sgd sgt : bool.
  Let INP := AsanInit.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn rdr sgd sgt.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  (* the kernel build as Run.valid_input records it: kb_rseq stays free (LPS 727298f3) *)
  Hypothesis Hkernel : in_kernel INP = recorded_kernel (in_kernel INP).
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.

  #[local] Notation SINVx := (SINV0 BPH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn rdr sgd sgt).
  #[local] Notation argHx := (argH0 sp rdraw argv envp kb execfn).

  Section AnySINV.
    Variable SINV : env -> (word -> option byte) -> Prop.
    Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINVx E M.
    Hypothesis SINV_frame : forall E M M', (forall a, argHx E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
    Variable nx0 : nat.
    Hypothesis NX0_le : (NX0 <= nx0)%nat.
    Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

    Theorem node_x_sound_XEnvScan_asan_gen : x_stmt BSEGS SC BOTH5 nx0 LIMIT (rseq_z (kb_rseq kb)) SINV argHx FS0 XEnvScan.
    Proof.
      eapply init_x_sound_envscan.
      all: first [ exact (fetch_lit _ _ _ _ eq_refl F_91efc) | exact (fetch_lit _ _ _ _ eq_refl F_91f00) | exact (fetch_lit _ _ _ _ eq_refl F_91f04) | exact (fetch_lit _ _ _ _ eq_refl F_91fb8) | exact (fetch_lit _ _ _ _ eq_refl F_91fbc) | exact (fetch_lit _ _ _ _ eq_refl F_91fc0) | exact (fetch_lit _ _ _ _ eq_refl F_91fc4) | exact (fetch_lit _ _ _ _ eq_refl F_91fc8) | exact D_91efc | exact D_91f00 | exact D_91f04 | exact D_91fb8 | exact D_91fbc | exact D_91fc0 | exact D_91fc4 | exact D_91fc8 | exact both_wx | exact both_in_hull | exact both_hull_ok | eassumption
                 | (cbn [x_envscan x_envscan_k x_pnscan x_pnscan_k BOTH5]; lia)
                 | (repeat split; reflexivity) ].
    Qed.

    Theorem node_x_sound_XPnScan_asan_gen : x_stmt BSEGS SC BOTH5 nx0 LIMIT (rseq_z (kb_rseq kb)) SINV argHx FS0 XPnScan.
    Proof.
      eapply init_x_sound_pnscan.
      all: first [ exact (fetch_lit _ _ _ _ eq_refl F_91efc) | exact (fetch_lit _ _ _ _ eq_refl F_91f00) | exact (fetch_lit _ _ _ _ eq_refl F_91f04) | exact (fetch_lit _ _ _ _ eq_refl F_91fb8) | exact (fetch_lit _ _ _ _ eq_refl F_91fbc) | exact (fetch_lit _ _ _ _ eq_refl F_91fc0) | exact (fetch_lit _ _ _ _ eq_refl F_91fc4) | exact (fetch_lit _ _ _ _ eq_refl F_91fc8) | exact D_91efc | exact D_91f00 | exact D_91f04 | exact D_91fb8 | exact D_91fbc | exact D_91fc0 | exact D_91fc4 | exact D_91fc8 | exact both_wx | exact both_in_hull | exact both_hull_ok | eassumption
                 | (cbn [x_envscan x_envscan_k x_pnscan x_pnscan_k BOTH5]; lia)
                 | (repeat split; reflexivity) ].
    Qed.

    Theorem node_x_sound_XLayout_asan_gen : x_stmt BSEGS SC BOTH5 nx0 LIMIT (rseq_z (kb_rseq kb)) SINV argHx FS0 XLayout.
    Proof. apply x_sound_layout. Qed.
  End AnySINV.
End AsanInstance.
