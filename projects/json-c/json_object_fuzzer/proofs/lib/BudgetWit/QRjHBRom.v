(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11 (LPS 727298f3): the budget walk [BudgetWit.QRjHB.realizes] over the binary's own
   segments, lifted to the run's segment list and its start, and carried through the launch's vDSO layer.
   Parts 1-3 follow projects/msgpack-c/unpack_pack_fuzzer/proofs/lib/BudgetWit/RzbRom.v, over json-c's
   node facts: the node transfers are Cfg/RomStable.v's lemmas on [QRjH.node_ok], used here, not copied.
   Part 4 is the node case of Cfg/VdsoBridge.v's [realizes_with_vdso_mut] at [P := True] (as its
   [realizes_with_vdso_no_text]), over [QRjHB.realizes], with VdsoBridge's [wI] and [node_ok_vdso].

   At LPS 727298f3 [Run.run_scfg_budget_refused] reads the run against [run_segments segs inp sp mb]
   = [segs ++ vdso_segments ..], from [init_config (run_segments ..) ..], which is [init_config segs ..]
   with a larger read-only backing ([RomStable.init_config_run_segments]).  A [QRjHB.realizes] node carries
   three facts besides its successors: [QRjH.node_ok] and [RomBase.sys_rob], which transfer by RomStable's
   [node_wrom] / [sys_rob_wrom] (a larger backing) and [node_ok_app_tail'] / [sys_rob_app_tail] (the vDSO
   pair appended), and [QRjHB.budget_ok], which reads the configuration only through its pending syscall
   number: a change of backing, of segment list or of the model's vDSO layer leaves it as it is.
   [rz_cfg_wrom] and [rz_app_tail] are the two transfers, [rz_run_init] their composition at the run's
   start; [rz_with_vdso_no_text] drops the start's vDSO layer over a segment list with no vDSO text, as
   QHdY.drv_start_spec_lim does for [QRjH.realizes]. *)
From Stdlib Require Import List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics StackLayout State Vdso Run VdsoCommute VdsoCommuteSys VdsoCommuteCfg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Cfg Require Import RomBase.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Cfg Require RomStable VdsoBridge.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.BudgetWit Require QRjHB.
Import ListNotations.

(** * Part 1: a larger read-only backing *)

(** The budget check reads only the pending syscall, which [cwrom] keeps. *)
Lemma budget_ok_wrom : forall c r, QRjHB.budget_ok c -> QRjHB.budget_ok (cwrom c r).
Proof. intros c r Hb. exact Hb. Qed.

Theorem rz_cfg_wrom : forall segs, vdso_image segs = None ->
  forall c T, QRjHB.realizes segs c T ->
  forall r, rom_ext (ms_rom (cfg_ms c)) r -> QRjHB.realizes segs (cwrom c r) T.
Proof.
  intros segs Hvi c T H;
    induction H as [c I evs nx T i0 Hn Hrob Hb Hc IH | c Hh | c T T' H IH Heq]; intros r Hr.
  - apply (QRjHB.rz_node segs (cwrom c r) I evs (fun i => cwrom (nx i) r) T i0).
    + exact (RomStable.node_wrom segs Hvi c I evs nx r Hn Hrob Hr).
    + exact (RomStable.sys_rob_wrom segs c r Hrob Hr).
    + exact (budget_ok_wrom c r Hb).
    + intros i. apply IH. rewrite (RomStable.node_rom segs Hvi c I evs nx Hn i). exact Hr.
  - apply QRjHB.rz_halt. exact Hh.
  - eapply QRjHB.rz_conseq; [apply IH; exact Hr | exact Heq].
Qed.

(** * Part 2: the vDSO pair appended to the segment list *)

Theorem rz_app_tail : forall segs tail,
  (forall s, In s tail -> seg_executable s = false) ->
  (forall s, In s tail -> seg_writable s = false) ->
  vdso_image segs = None ->
  forall c T, QRjHB.realizes segs c T -> QRjHB.realizes (segs ++ tail) c T.
Proof.
  intros segs tail Hnx Hnw Hvi c T H;
    induction H as [c I evs nx T i0 Hn Hrob Hb Hc IH | c Hh | c T T' H IH Heq].
  - apply (QRjHB.rz_node (segs ++ tail) c I evs nx T i0); [ | | exact Hb | exact IH ].
    + eapply RomStable.node_ok_app_tail'; eassumption.
    + eapply RomStable.sys_rob_app_tail; eassumption.
  - exact (QRjHB.rz_halt (segs ++ tail) c Hh).
  - exact (QRjHB.rz_conseq (segs ++ tail) c T T' IH Heq).
Qed.

Theorem rz_run_segments : forall segs inp (sp mb : word) c T,
  vdso_image segs = None ->
  QRjHB.realizes segs c T -> QRjHB.realizes (run_segments segs inp sp mb) c T.
Proof.
  intros segs inp sp mb c T Hvi H. unfold run_segments.
  apply rz_app_tail;
    [ intros s Hs; exact (RomStable.vdso_segments_nx _ _ _ s Hs)
    | intros s Hs; exact (RomStable.vdso_segments_nw _ _ _ s Hs)
    | exact Hvi | exact H ].
Qed.

(** * Part 3: the run's own start *)

(** A budget walk over the binary's own segments, from the binary's start, is one over the run's
    segment list from the run's start (the twin of [RomStable.run_init]). *)
Theorem rz_run_init : forall segs inp (sp mb : word) pc ph brk rnd lim T,
  vdso_image segs = None ->
  QRjHB.realizes segs (init_config segs pc ph sp brk mb rnd lim inp) T ->
  QRjHB.realizes (run_segments segs inp sp mb)
    (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp) T.
Proof.
  intros segs inp sp mb pc ph brk rnd lim T Hvi H.
  rewrite RomStable.init_config_run_segments.
  apply rz_run_segments; [exact Hvi|].
  apply (rz_cfg_wrom segs Hvi); [exact H|].
  rewrite RomStable.init_config_rom. apply RomStable.rom_ext_run_segments.
Qed.

(** * Part 4: the launch's vDSO layer

    The run's start model is [with_vdso (vdso_run_init ..) (init_model ..)]; the usage walk is stated
    at [init_model ..].  Over a segment list with no vDSO text no pc is an exported entry, so each node
    is a node at [cfg_with_vdso v c], re-indexed over the transitions the wrapped state takes
    ([VdsoBridge.wI]), with its children under the layer each step leaves. *)

Lemma budget_ok_with_vdso : forall v c, QRjHB.budget_ok c -> QRjHB.budget_ok (cfg_with_vdso v c).
Proof. intros v c Hb. exact Hb. Qed.

Theorem rz_with_vdso_no_text : forall segs, vdso_text_seg segs = None ->
  forall c T, QRjHB.realizes segs c T -> forall v, QRjHB.realizes segs (cfg_with_vdso v c) T.
Proof.
  intros segs Hnt c T H;
    induction H as [c I evs nx T i0 Hnode Hrob Hb Hcont IH | c Hh | c T T' H IH Heq]; intros v.
  - pose proof (vdso_entry_fn_none_of_no_text segs (ms_pc (cfg_ms c)) Hnt) as Hnv.
    assert (W : forall i, sstep_cfg segs (alloc_only_cfg false) (cfg_with_vdso v c) (evs i)
                            (SNext (cfg_with_vdso v (nx i))))
      by (intros i; exact (sstep_cfg_vdso_frame_c segs (alloc_only_cfg false) v c (evs i) (SNext (nx i))
                             Hnv (proj1 Hnode i))).
    set (pick := fun i : I => (
           @existT I (fun i => {c'' : config | (exists w, c'' = cfg_with_vdso w (nx i))
                                  /\ sstep_cfg segs (alloc_only_cfg false) (cfg_with_vdso v c) (evs i) (SNext c'')})
             i (exist _ (cfg_with_vdso v (nx i)) (conj (ex_intro _ v eq_refl) (W i)))
           : VdsoBridge.wI segs c I evs nx v)).
    apply (QRjHB.rz_conseq segs _
             (QRjH.t_alt (fun i' : VdsoBridge.wI segs c I evs nx v =>
                            QRjH.t_emit (evs (projT1 i')) (T (projT1 i'))))).
    + apply (QRjHB.rz_node segs _ (VdsoBridge.wI segs c I evs nx v) (fun i' => evs (projT1 i'))
               (fun i' => proj1_sig (projT2 i')) (fun i' => T (projT1 i')) (pick i0)).
      * exact (VdsoBridge.node_ok_vdso segs c I evs nx v Hnode Hnv).
      * exact (RomBase.sys_rob_cfg_with_vdso segs v c Hrob).
      * exact (budget_ok_with_vdso v c Hb).
      * intros [i [c'' Hp]]. cbn [projT1 projT2 proj1_sig]. destruct (proj1 Hp) as [w Hw]. rewrite Hw.
        exact (IH i w).
    + intros tr. split.
      * intros [[i s] Hi]. exists i. exact Hi.
      * intros [i Hi]. exists (pick i). exact Hi.
  - apply QRjHB.rz_halt. unfold cfg_with_vdso. cbn [cfg_model].
    rewrite VdsoBridge.m_halted_with_vdso. exact Hh.
  - eapply QRjHB.rz_conseq; [exact (IH v) | exact Heq].
Qed.
