(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11: the budget walk [BudgetWit.Rzb.rzb] over a binary's own segments,
   lifted to the run's segment list, as projects/msgpack-c/unpack_pack_fuzzer/proofs/lib/AS/RomStable.v
   (a copy of projects/zstd/zstd_frame_info/proofs/lib/AS/RomStable.v) lifts [AS.ShapeAlg.realizes];
   the node transfers are that file's lemmas, used here, not copied.

   At LPS 727298f3 [Run.run_scfg_budget_refused] reads the run against [run_segments segs inp sp mb]
   = [segs ++ vdso_segments ..], from [init_config (run_segments ..) ..], which is
   [init_config segs ..] with a larger read-only backing ([RomStable.init_config_run_segments]).
   An [rzb] node carries three facts besides its successors: [node_ok] and [RomBase.sys_rob],
   which transfer by RomStable's [node_wrom]/[sys_rob_wrom] (a larger backing) and
   [node_ok_app_tail]/[sys_rob_app_tail] (the vDSO pair appended), and [Rzb.budget_ok].  Both
   halves of [budget_ok] read the configuration only through its pending syscall and that
   syscall's input:
   - [Rzb.grant_ok]: [Run.alloc_budget_refused_b] reads the input's number and arguments, never
     [in_mem] ([alloc_budget_refused_b_with_mem]); a larger backing changes only [in_mem]
     ([RomBase.sys_input_wrom]), and the appended pair changes nothing
     ([RomStable.sys_input_app_nw]);
   - [Fcfg.step_nonspur]: over a larger backing the specification is the same
     ([RomBase.sys_rob]) and so is the refusal filter ([RomStable.nspur_to_wrom]); the appended
     pair leaves the input as it is.
   [rzb_cfg_wrom] and [rzb_app_tail] are the two transfers, [rzb_run_init] their composition at
   the run's start. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Scfg Require Import Fcfg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require Import RomBase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require RomStable.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BudgetWit Require Import Rzb.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(** The budget mark reads the input's number and arguments, not its memory view. *)
Lemma alloc_budget_refused_b_with_mem : forall i mp m,
  alloc_budget_refused_b (with_mem i mp) m = alloc_budget_refused_b i m.
Proof. intros i mp m. reflexivity. Qed.

(** * Part 1: a larger read-only backing *)
Section Wrom.
Variable segs : list Segment.
Hypothesis Hvi : vdso_image segs = None.

Lemma grant_ok_wrom : forall c r, grant_ok segs c -> grant_ok segs (cwrom c r).
Proof.
  intros [ms m] r Hg x8 Hx. unfold cwrom in *. cbn [cfg_ms cfg_model] in *.
  change (ms_svc_pending (wrom ms r)) with (ms_svc_pending ms) in Hx.
  rewrite sys_input_wrom, alloc_budget_refused_b_with_mem. exact (Hg x8 Hx).
Qed.

Lemma step_nonspur_wrom : forall c r, sys_rob segs c -> rom_ext (ms_rom (cfg_ms c)) r ->
  step_nonspur segs c -> step_nonspur segs (cwrom c r).
Proof.
  intros [ms m] r Hrob Hr Hn x8 eff m' evs Hx Hs. unfold cwrom in *. cbn [cfg_ms cfg_model] in *.
  change (ms_svc_pending (wrom ms r)) with (ms_svc_pending ms) in Hx.
  assert (Hsp : forall o, syscall_spec (sys_input segs (wrom ms r) x8) m o
                          <-> syscall_spec (sys_input segs ms x8) m o)
    by (intros o; exact (Hrob r x8 Hr Hx o)).
  exact (RomStable.nspur_to_wrom segs ms r x8 m eff Hsp
           (Hn x8 eff m' evs Hx (proj1 (Hsp (Ok eff m' evs)) Hs))).
Qed.

Lemma budget_ok_wrom : forall c r, sys_rob segs c -> rom_ext (ms_rom (cfg_ms c)) r ->
  budget_ok segs c -> budget_ok segs (cwrom c r).
Proof.
  intros c r Hrob Hr [Hg Hn].
  split; [exact (grant_ok_wrom c r Hg) | exact (step_nonspur_wrom c r Hrob Hr Hn)].
Qed.

Theorem rzb_cfg_wrom : forall c T, rzb segs c T ->
  forall r, rom_ext (ms_rom (cfg_ms c)) r -> rzb segs (cwrom c r) T.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hn Hrob Hb Hc IH | c Hh | c T T' H IH Heq]; intros r Hr.
  - apply (rzb_node segs (cwrom c r) I evs (fun i => cwrom (nx i) r) T i0).
    + exact (RomStable.node_wrom segs Hvi c I evs nx r Hn Hrob Hr).
    + exact (RomStable.sys_rob_wrom segs c r Hrob Hr).
    + exact (budget_ok_wrom c r Hrob Hr Hb).
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

Lemma grant_ok_app_tail : forall c, grant_ok segs c -> grant_ok (segs ++ tail) c.
Proof.
  intros c Hg x8 Hx. rewrite (RomStable.sys_input_app_nw segs tail Hnw). exact (Hg x8 Hx).
Qed.

Lemma step_nonspur_app_tail : forall c, step_nonspur segs c -> step_nonspur (segs ++ tail) c.
Proof.
  intros c Hn x8 eff m' evs Hx Hs.
  rewrite (RomStable.sys_input_app_nw segs tail Hnw) in Hs |- *.
  exact (Hn x8 eff m' evs Hx Hs).
Qed.

Lemma budget_ok_app_tail : forall c, budget_ok segs c -> budget_ok (segs ++ tail) c.
Proof.
  intros c [Hg Hn]. split; [exact (grant_ok_app_tail c Hg) | exact (step_nonspur_app_tail c Hn)].
Qed.

Theorem rzb_app_tail : forall c T, rzb segs c T -> rzb (segs ++ tail) c T.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hn Hrob Hb Hc IH | c Hh | c T T' H IH Heq].
  - exact (rzb_node (segs ++ tail) c I evs nx T i0
             (RomStable.node_ok_app_tail segs tail Hnx Hnw Hvi c I evs nx i0 Hn)
             (RomStable.sys_rob_app_tail segs tail Hnw c Hrob)
             (budget_ok_app_tail c Hb) IH).
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
    segment list from the run's start. *)
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
