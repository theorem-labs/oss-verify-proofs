(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's whole ProcInput and kernel build, the CONFIG_RSEQ flag the scan nodes are checked at, and the start-up summaries' new arguments). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib
  AsanAcct AsanAcctShape AsanAcctImages.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit BothPlanImages.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require Import AsanNodesAux AsanStartLoops AsanNodesStartX AsanNodesStartXInit Both_code_startx.
Unset Nia Cache. Unset Nra Cache.

Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Section AsanInstance.
  (** THE INPUT GROUP.  [AsanInit.SINV0] reads [wrap_mem inp ...] and [inp] is
      all twenty [State.ProcInput] fields, so this Section can no longer carry
      just [fs stdin uid hw]: without the rest it cannot build [inp] at all.
      Declared in [AsanInit]'s order, so every positional list below reads in
      that order. *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variable uid gid : word.
  Variable hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nof sigm : word.
  Variable abt : bool.
  Variable urnd : InputStream.
  Variable tmpf : Fs.Fs.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variables chrdr sigdef sigterm : bool.
  Variable FS0 : Fs.Fs.

  #[local] Notation INP := (inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmpf kb execfn chrdr sigdef sigterm).
  #[local] Notation RZ := (rseq_z (kb_rseq kb)).
  (** [argH0] LOST [ph], [uid] and [hw] — and [ph] was argument ONE, so a site
      that still passes [BPH] first shifts every later argument by one. *)
  #[local] Notation argH0a := (argH0 sp rdraw argv envp kb execfn).
  #[local] Notation SINV0a := (SINV0 BOTH BPH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmpf kb execfn chrdr sigdef sigterm).
  #[local] Notation SINV0a_frame := (SINV0_frame BOTH BPH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmpf kb execfn chrdr sigdef sigterm).
  #[local] Notation SINV0a_agree := (SINV0_agree BOTH BPH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd tmpf kb execfn chrdr sigdef sigterm).

  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  (** NEW PREMISES.  [Hlau] is [Run.valid_entry]'s fifth conjunct, so every
      caller that destructures [valid_entry] already holds it.  [Hlaunch] is a
      [valid_input] conjunct and is NOT in [valid_entry], so it travels up to
      whoever owns the [valid_input]. *)
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.

  Section AnySINV.

    Variable SINV : env -> (word -> option byte) -> Prop.
    Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0a E M.
    Hypothesis SINV_frame : forall E M M', (forall a, argH0a E a = true -> M' a = M a) -> SINV E M -> SINV E M'.

    Variable nx0 : nat.
    Hypothesis Hnx0 : (NX0 <= nx0)%nat.
    Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

    (** [AsanNodesStartXInit]'s three exports are pinned by [Proof using] to ONE
        discharge list, so it is spelled once here and the two theorems below
        differ only in the name they apply. *)
    Ltac asan_init_apply L :=
      exact (L BSEGS BOTH BPH both_wx both_in_hull both_hull_ok
               W_bf150 W_bf154 W_bf158 W_bf20c W_bf210 W_bf214 W_bf218 W_bf21c
               ltac:(cbn [x_envscan x_envscan_k BOTH]; lia)
               (fetch_lit _ _ _ _ eq_refl F_bf150) (fetch_lit _ _ _ _ eq_refl F_bf154) (fetch_lit _ _ _ _ eq_refl F_bf158)
               ltac:(repeat split; reflexivity)
               D_bf150 D_bf154 D_bf158
               ltac:(cbn [x_pnscan x_pnscan_k BOTH]; lia)
               (fetch_lit _ _ _ _ eq_refl F_bf20c) (fetch_lit _ _ _ _ eq_refl F_bf210) (fetch_lit _ _ _ _ eq_refl F_bf214)
               (fetch_lit _ _ _ _ eq_refl F_bf218) (fetch_lit _ _ _ _ eq_refl F_bf21c)
               ltac:(repeat split; reflexivity)
               D_bf20c D_bf210 D_bf214 D_bf218 D_bf21c
               sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net
               nof sigm abt urnd tmpf kb execfn chrdr sigdef sigterm FS0
               Hsp Hva Hve Hfit Hlaunch Hlau
               SINV SINV_SINV0 SINV_frame nx0 Hnx0 SINV_agree).

    Theorem node_x_sound_XEnvScan_asan_gen : x_stmt BSEGS BOTH nx0 LIMIT RZ SINV argH0a FS0 XEnvScan.
    Proof. asan_init_apply init_x_sound_envscan. Qed.

    Theorem node_x_sound_XPnScan_asan_gen : x_stmt BSEGS BOTH nx0 LIMIT RZ SINV argH0a FS0 XPnScan.
    Proof. asan_init_apply init_x_sound_pnscan. Qed.

    Theorem node_x_sound_XLayout_asan_gen : x_stmt BSEGS BOTH nx0 LIMIT RZ SINV argH0a FS0 XLayout.
    Proof. apply x_sound_layout. Qed.
  End AnySINV.

  Theorem node_x_sound_XEnvScan_asan :
    x_stmt BSEGS BOTH NX0 LIMIT RZ SINV0a argH0a FS0 XEnvScan.
  Proof.
    apply (node_x_sound_XEnvScan_asan_gen _ (fun E M H => H) SINV0a_frame NX0 (le_n NX0) SINV0a_agree).
  Qed.

  Theorem node_x_sound_XPnScan_asan :
    x_stmt BSEGS BOTH NX0 LIMIT RZ SINV0a argH0a FS0 XPnScan.
  Proof.
    apply (node_x_sound_XPnScan_asan_gen _ (fun E M H => H) SINV0a_frame NX0 (le_n NX0) SINV0a_agree).
  Qed.

  Theorem node_x_sound_XLayout_asan :
    x_stmt BSEGS BOTH NX0 LIMIT RZ SINV0a argH0a FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End AsanInstance.
