(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Lib/Nodes.v's node and at_node: the nodes that are not allocation calls, and what the budget mark and the spurious-failure filter answer on them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: munmap (215) counts as an allocation call, and the three vDSO step arms are handled; taken in part from projects/simdjson/fuzz_ondemand/proofs/lib/BudgetWit/Quiet.v, lines 13-16, 24-28, 79-81. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import ITree Nodes.
Import ListNotations.

(** * Nodes that are not allocation calls

    [nalloc n] holds for every node but [NBrk], [NMmap], [NMunmap] and [NMprotect].
    At such a node the pending system call is none of brk, munmap, mremap, mmap or
    mprotect (214, 215, 216, 222, 226: [Run.alloc_mark_sysnos]; LPS 727298f3 added
    munmap's 215 to that list), so the budget mark
    [Run.alloc_budget_refused_b] answers [false] on it; and its family is not the
    allocation family, the one family [ACFG] reads as forced-only, so no outcome
    of it is a spurious refusal under [ACFG], and the unfiltered step relation
    and the [ACFG] one agree there ([sstep_cfg_quiet]). *)

Definition nalloc (n : node) : Prop :=
  match n with
  | NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ => False
  | _ => True
  end.

(** The check on a system-call number: off the allocation numbers, and in a
    family [ACFG] lets fail. *)
Definition quiet_no (k : Z) : bool :=
  negb (existsb (Z.eqb k) alloc_mark_sysnos) &&
  match injected_arm k with
  | Some a => family_may_fail ACFG (ia_family a)
  | None => true
  end.

Lemma quiet_no_sound : forall segs ms mo x8,
  quiet_no (bv_unsigned x8) = true ->
  injected_family_off ACFG (sys_input segs ms x8) = false /\
  alloc_budget_refused_b (sys_input segs ms x8) mo = false.
Proof.
  intros segs ms mo x8 H. unfold quiet_no in H. apply andb_true_iff in H. destruct H as [H1 H2].
  split.
  - revert H2. unfold injected_family_off. rewrite in_sysno_si.
    destruct (injected_arm (bv_unsigned x8)) as [a|]; intros H2; [rewrite H2|]; reflexivity.
  - apply alloc_budget_refused_b_outside. rewrite in_sysno_si. intros Hin.
    apply negb_true_iff in H1.
    assert (Hex : existsb (Z.eqb (bv_unsigned x8)) alloc_mark_sysnos = true).
    { apply existsb_exists. exists (bv_unsigned x8). split; [exact Hin | apply Z.eqb_refl]. }
    congruence.
Qed.

(** At a node that is not an allocation call, both answers are [false]. *)
Lemma nalloc_quiet : forall segs n ms mo x8,
  nalloc n -> at_node segs n ms -> ms_svc_pending ms = Some x8 ->
  injected_family_off ACFG (sys_input segs ms x8) = false /\
  alloc_budget_refused_b (sys_input segs ms x8) mo = false.
Proof.
  intros segs n ms mo x8 Hn Hat Hx. apply quiet_no_sound.
  destruct n; cbn [nalloc] in Hn; try contradiction; cbn [at_node] in Hat.
  - destruct Hat as [Hs _]. rewrite Hx in Hs. injection Hs as ->. vm_compute. reflexivity.
  - destruct Hat as [Hs _]. rewrite Hx in Hs. injection Hs as ->. vm_compute. reflexivity.
  - destruct Hat as [Hs _]. rewrite Hx in Hs. injection Hs as ->. vm_compute. reflexivity.
  - destruct Hat as [Hs _]. rewrite Hx in Hs. injection Hs as ->. vm_compute. reflexivity.
  - destruct Hat as [Hs _]. rewrite Hx in Hs. injection Hs as ->. vm_compute. reflexivity.
  - rewrite Hx in Hat. injection Hat as ->. vm_compute. reflexivity.
  - destruct Hat as [[Hs|Hs] _]; rewrite Hx in Hs; injection Hs as ->; vm_compute; reflexivity.
Qed.

(** Where no pending call is in a family [cfg] reads as forced-only, a step is a
    [cfg] step: the filter removes nothing there. *)
Lemma sstep_cfg_quiet : forall segs cfg c evs X,
  (forall x8, ms_svc_pending (cfg_ms c) = Some x8 ->
     injected_family_off cfg (sys_input segs (cfg_ms c) x8) = false) ->
  sstep segs c evs X -> sstep_cfg segs cfg c evs X.
Proof.
  intros segs cfg c evs X Hoff H. revert Hoff. destruct H; intros Hoff; cbn [cfg_ms] in Hoff;
    [ eapply sstep_cfg_instr | eapply sstep_cfg_instr_fault | eapply sstep_cfg_instr_unmodeled
    (* LPS 727298f3: the three vDSO arms, which [sstep_cfg] mirrors with no filter premise. *)
    | eapply sstep_cfg_vdso_call | eapply sstep_cfg_vdso_materialization_fault
    | eapply sstep_cfg_vdso_unmodeled
    | eapply sstep_cfg_syscall | eapply sstep_cfg_syscall_materialization_fault
    | eapply sstep_cfg_exit | eapply sstep_cfg_killed | eapply sstep_cfg_syscall_unmodeled ];
    eauto using spurious_refusal_family_on.
Qed.
