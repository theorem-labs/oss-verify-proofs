(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11 (LPS 08b1429): the [srealizes] half of the run-segments bridge, the
   counterpart of openssl/pem's [Common/Cfg/SRomStable.v] srealizes lemmas.

   In this tree [SpinAlg.srealizes] has the same three constructors as [ShapeAlg.realizes]
   ([srz_node] asks [node_ok] and [RomBase.sys_rob] as [rz_node] does), and SpinAlg proves the two
   equivalent ([srealizes_of_realizes], [realizes_of_srealizes]).  So each lemma here is its
   [realizes] counterpart in [RomStable], conjugated by that equivalence.

   Kept apart from [RomStable] so that the halts chain ([EchHalts], [BaseUbsan]) does not load
   SpinAlg. *)
From Stdlib Require Import List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Scfg ShapeAlg SpinAlg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import RomBase RomStable.

Theorem srealizes_wrom {SC : StepCfg} : forall segs, vdso_image segs = None ->
  forall c T, srealizes segs c T ->
  forall r, rom_ext (ms_rom (cfg_ms c)) r -> srealizes segs (cwrom c r) T.
Proof.
  intros segs Hvi c T H r Hr.
  apply srealizes_of_realizes.
  apply (realizes_wrom segs Hvi); [exact (realizes_of_srealizes segs c T H) | exact Hr].
Qed.

Theorem srealizes_app_tail {SC : StepCfg} : forall segs tail,
  (forall s, In s tail -> seg_executable s = false) ->
  (forall s, In s tail -> seg_writable s = false) ->
  vdso_image segs = None ->
  forall c T, srealizes segs c T -> srealizes (segs ++ tail) c T.
Proof.
  intros segs tail Hnx Hnw Hvi c T H.
  apply srealizes_of_realizes.
  apply (realizes_app_tail segs tail Hnx Hnw Hvi).
  exact (realizes_of_srealizes segs c T H).
Qed.

Theorem srealizes_run_segments {SC : StepCfg} : forall segs inp (sp mb : word) c T,
  vdso_image segs = None ->
  srealizes segs c T -> srealizes (run_segments segs inp sp mb) c T.
Proof.
  intros segs inp sp mb c T Hvi H.
  apply srealizes_of_realizes.
  apply (realizes_run_segments segs inp sp mb c T Hvi).
  exact (realizes_of_srealizes segs c T H).
Qed.

(** The bridge for [srealizes]: a walk over the binary's own segments, from the binary's start,
    is a walk over the run's segment list from the run's start. *)
Theorem srun_init {SC : StepCfg} : forall segs inp (sp mb : word) pc ph brk rnd lim T,
  vdso_image segs = None ->
  srealizes segs (init_config segs pc ph sp brk mb rnd lim inp) T ->
  srealizes (run_segments segs inp sp mb)
    (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp) T.
Proof.
  intros segs inp sp mb pc ph brk rnd lim T Hvi H.
  apply srealizes_of_realizes.
  apply (run_init segs inp sp mb pc ph brk rnd lim T Hvi).
  exact (realizes_of_srealizes segs _ T H).
Qed.
