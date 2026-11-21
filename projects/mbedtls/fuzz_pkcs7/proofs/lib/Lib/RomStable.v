(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: its provenance comment names its source by unit and file. *)
(* Theorem Labs, 2026-11 (LPS 75d69e00): a [Lib.Shape.realizes] walk over a binary's own segments,
   lifted to the run's ([run_segments]) from the run's own start ([run_init]).

   Why it is needed: at the revision the run reads the image through
   ms_rom = seg_rom (run_segments ..), a larger backing than the binary's own segments, and
   [sys_input] reads memory through ms_rom; so a walk over [segs] lifts to the run only because
   each syscall node answers the same on the larger backing - [RomBase.sys_rob], node_ok's third
   conjunct.  The step-level facts are [Common/Cfg/RomStep.v].

   Donor (proof shape, per lemma): the double-conversion/string_to_double_fuzzer unit's
   RomStable.v:110-112 [node_rom],
   184-193 [node_wrom], 208-218 [realizes_wrom], 488-514 [node_ok_app_tail, realizes_app_tail],
   592-601 [realizes_run_segments], 642-653 [run_init]; adapted from that tree's separate
   [sys_rob] premise on [rz_node] to this tree's node_ok conjunct. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common.Cfg Require Import RomBase RomStep.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Shape.
Import ListNotations.

Section Seg.
Variable segs : list Segment.
Hypothesis Hvi : vdso_image segs = None.

Lemma node_rom : forall c I evs nx, node_ok segs c I evs nx ->
  forall i, ms_rom (cfg_ms (nx i)) = ms_rom (cfg_ms c).
Proof. intros c I evs nx [Hc _] i. exact (sstep_next_rom segs Hvi _ _ _ (Hc i)). Qed.

Lemma node_wrom : forall c I evs nx r,
  node_ok segs c I evs nx -> rom_ext (ms_rom (cfg_ms c)) r ->
  node_ok segs (cwrom c r) I evs (fun i => cwrom (nx i) r).
Proof.
  intros c I evs nx r [Hc [Hb Hrob]] Hr. split; [|split].
  - intros i. exact (sstep_wrom_fwd segs Hvi c (evs i) (nx i) r Hrob Hr (Hc i)).
  - intros e st Hst.
    destruct (sstep_wrom_back segs Hvi c e st r Hrob Hr Hst) as (st0 & H0 & ->).
    destruct (Hb e st0 H0) as (i & -> & ->). exists i. split; reflexivity.
  - exact (sys_rob_wrom segs c r Hrob Hr).
Qed.

Theorem realizes_wrom : forall c T, realizes segs c T ->
  forall r, rom_ext (ms_rom (cfg_ms c)) r -> realizes segs (cwrom c r) T.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hn Hc IH | c Hh | c T T' H IH Heq]; intros r Hr.
  - apply (rz_node segs (cwrom c r) I evs (fun i => cwrom (nx i) r) T i0).
    + exact (node_wrom c I evs nx r Hn Hr).
    + intros i. apply IH. rewrite (node_rom c I evs nx Hn i). exact Hr.
  - apply rz_halt. exact Hh.
  - eapply rz_conseq; [apply IH; exact Hr | exact Heq].
Qed.
End Seg.

Section AppTail.
  Variables segs tail : list Segment.
  Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
  Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.
  Hypothesis Hvi : vdso_image segs = None.

  Lemma node_ok_app_tail : forall c (I : Type) evs nx (i0 : I),
    node_ok segs c I evs nx -> node_ok (segs ++ tail) c I evs nx.
  Proof.
    intros [ms model] I evs nx i0 [Hc [Hs Hrob]]. split; [|split].
    - intros i. apply (sstep_app_next segs tail); first [assumption | exact (Hc i)].
    - intros e st Hb. apply Hs. apply (sstep_app_back segs tail); try assumption.
      eapply instr_ok_of_step; first [exact (Hc i0) | eassumption].
    - apply (sys_rob_app_tail segs tail); assumption.
  Qed.

  Theorem realizes_app_tail : forall c T, realizes segs c T -> realizes (segs ++ tail) c T.
  Proof.
    intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
    - exact (rz_node (segs ++ tail) c I evs nx T i0 (node_ok_app_tail c I evs nx i0 Hnode) IH).
    - exact (rz_halt (segs ++ tail) c Hh).
    - exact (rz_conseq (segs ++ tail) c T T' IH Heq).
  Qed.
End AppTail.

Theorem realizes_run_segments : forall segs inp (sp mb : word) c T,
  vdso_image segs = None ->
  realizes segs c T -> realizes (run_segments segs inp sp mb) c T.
Proof.
  intros segs inp sp mb c T Hvi H. unfold run_segments.
  apply realizes_app_tail;
    [ intros s Hs; exact (vdso_segments_nx _ _ _ s Hs)
    | intros s Hs; exact (vdso_segments_nw _ _ _ s Hs)
    | exact Hvi | exact H ].
Qed.

(** The supplier-walk bridge: a walk over the binary's own segments, from the binary's start, is
    a derivation of the run's statement from the run's start. *)
Theorem run_init : forall segs inp (sp mb : word) pc ph brk rnd lim T,
  vdso_image segs = None ->
  realizes segs (init_config segs pc ph sp brk mb rnd lim inp) T ->
  realizes (run_segments segs inp sp mb)
    (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp) T.
Proof.
  intros segs inp sp mb pc ph brk rnd lim T Hvi H.
  rewrite init_config_run_segments.
  apply realizes_run_segments; [exact Hvi|].
  apply (realizes_wrom segs Hvi); [exact H|].
  rewrite init_config_rom. apply rom_ext_run_segments.
Qed.
