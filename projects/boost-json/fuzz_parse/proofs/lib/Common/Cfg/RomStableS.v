(* SPDX-License-Identifier: MIT *)
(* Copied from boost-beast/http_request's lib/Common/Cfg/RomStableS.v for the LPS 727298f3 port of
   this tree's asan top statements; only the module paths changed.

   The [srealizes] half of the run-segments bridge.  In this tree [SpinAlg.srealizes] has the
   same three constructors as [ShapeAlg.realizes] ([srz_node] asks [node_ok] and
   [RomBase.sys_rob] as [rz_node] does), and SpinAlg proves the two equivalent
   ([srealizes_of_realizes], [realizes_of_srealizes]).  So each lemma here is its [realizes]
   counterpart in [RomStable], conjugated by that equivalence. *)
From Stdlib Require Import List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Scfg ShapeAlg.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SpinAlg.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Common.Cfg Require Import RomBase RomStable.

Theorem srealizes_wrom {SC : StepCfg} : forall segs, vdso_image segs = None ->
  forall c T, srealizes segs c T ->
  forall r, rom_ext (ms_rom (cfg_ms c)) r -> srealizes segs (cwrom c r) T.
Proof.
  intros segs Hvi c T H r Hr.
  apply srealizes_of_realizes.
  apply (realizes_wrom segs Hvi); [apply realizes_of_srealizes; exact H | exact Hr].
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
  apply realizes_of_srealizes. exact H.
Qed.

Theorem srealizes_run_segments {SC : StepCfg} : forall segs inp (sp mb : word) c T,
  vdso_image segs = None ->
  srealizes segs c T -> srealizes (run_segments segs inp sp mb) c T.
Proof.
  intros segs inp sp mb c T Hvi H.
  apply srealizes_of_realizes.
  apply (realizes_run_segments segs inp sp mb c T Hvi).
  apply realizes_of_srealizes. exact H.
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
  apply realizes_of_srealizes. exact H.
Qed.
