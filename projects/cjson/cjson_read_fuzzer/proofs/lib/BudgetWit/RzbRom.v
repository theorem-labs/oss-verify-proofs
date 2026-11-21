(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11: the budget walk [BudgetWit.Rzb.rzb] over a binary's own segments, lifted to
   the run's segment list, as this tree's RomStable.v lifts [ShapeAlg.realizes]; the node transfers are
   that file's lemmas, used here, not copied.  The file follows
   projects/msgpack-c/unpack_pack_fuzzer/proofs/lib/BudgetWit/RzbRom.v over this tree's [rzb].

   At LPS 727298f3 [Run.run_scfg_budget_refused] reads the run against [run_segments segs inp sp mb]
   = [segs ++ vdso_segments ..], from [init_config (run_segments ..) ..], which is [init_config segs ..]
   with a larger read-only backing ([RomStable.init_config_run_segments]).  An [rzb] node carries three
   facts besides its successors: [node_ok] and [RomBase.sys_rob], which transfer by RomStable's
   [node_wrom] / [sys_rob_wrom] (a larger backing) and [node_ok_app_tail] / [sys_rob_app_tail] (the vDSO
   pair appended), and [Rzb.grant_ok], which reads the configuration only through its pending syscall
   number, so neither a larger backing nor a longer segment list changes it.  [rzb_cfg_wrom] and
   [rzb_app_tail] are the two transfers, [rzb_run_init] their composition at the run's start. *)
From Stdlib Require Import List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics StackLayout State Run.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import RomBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require RomStable.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.BudgetWit Require Import Rzb.
Import ListNotations.

(** The grant check reads only the pending syscall number, which [cwrom] keeps. *)
Lemma grant_ok_wrom : forall c r, grant_ok c -> grant_ok (cwrom c r).
Proof. intros [ms m] r Hg x8 Hx. exact (Hg x8 Hx). Qed.

(** * Part 1: a larger read-only backing *)
Section Wrom.
Variable segs : list Segment.
Hypothesis Hvi : vdso_image segs = None.

Theorem rzb_cfg_wrom : forall c T, rzb segs c T ->
  forall r, rom_ext (ms_rom (cfg_ms c)) r -> rzb segs (cwrom c r) T.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hn Hrob Hg Hc IH | c Hh | c T T' H IH Heq]; intros r Hr.
  - apply (rzb_node segs (cwrom c r) I evs (fun i => cwrom (nx i) r) T i0).
    + exact (RomStable.node_wrom segs Hvi c I evs nx r Hn Hrob Hr).
    + exact (RomStable.sys_rob_wrom segs c r Hrob Hr).
    + exact (grant_ok_wrom c r Hg).
    + intros i. apply IH. rewrite (RomStable.node_rom segs Hvi c I evs nx Hn i). exact Hr.
  - apply rzb_halt. exact Hh.
  - eapply rzb_conseq; [apply IH; exact Hr | exact Heq].
Qed.
End Wrom.

(** * Part 2: the vDSO pair appended to the segment list *)
Section AppTail.
Variables segs tail : list Segment.
Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.
Hypothesis Hvi : vdso_image segs = None.

Theorem rzb_app_tail : forall c T, rzb segs c T -> rzb (segs ++ tail) c T.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hn Hrob Hg Hc IH | c Hh | c T T' H IH Heq].
  - apply (rzb_node (segs ++ tail) c I evs nx T i0); [ | | exact Hg | exact IH ].
    + eapply RomStable.node_ok_app_tail; eassumption.
    + eapply RomStable.sys_rob_app_tail; eassumption.
  - exact (rzb_halt (segs ++ tail) c Hh).
  - exact (rzb_conseq (segs ++ tail) c T T' IH Heq).
Qed.
End AppTail.

Theorem rzb_run_segments : forall segs inp (sp mb : word) c T,
  vdso_image segs = None ->
  rzb segs c T -> rzb (run_segments segs inp sp mb) c T.
Proof.
  intros segs inp sp mb c T Hvi H. unfold run_segments.
  apply rzb_app_tail;
    [ intros s Hs; exact (RomStable.vdso_segments_nx _ _ _ s Hs)
    | intros s Hs; exact (RomStable.vdso_segments_nw _ _ _ s Hs)
    | exact Hvi | exact H ].
Qed.

(** * Part 3: the run's own start *)

(** A budget walk over the binary's own segments, from the binary's start, is one over the run's
    segment list from the run's start (the twin of [RomStable.run_init]). *)
Theorem rzb_run_init : forall segs inp (sp mb : word) pc ph brk rnd lim T,
  vdso_image segs = None ->
  rzb segs (init_config segs pc ph sp brk mb rnd lim inp) T ->
  rzb (run_segments segs inp sp mb)
    (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp) T.
Proof.
  intros segs inp sp mb pc ph brk rnd lim T Hvi H.
  rewrite RomStable.init_config_run_segments.
  apply rzb_run_segments; [exact Hvi|].
  apply (rzb_cfg_wrom segs Hvi); [exact H|].
  rewrite RomStable.init_config_rom. apply RomStable.rom_ext_run_segments.
Qed.
