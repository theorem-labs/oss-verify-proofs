(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: new for LPS 727298f3: the start-up invariant SINV0L, which binds the run's mmap base existentially by launch_base_ok and LAUNCH0, its lemmas, and cs_ok_SINV0L, which repacks AsanInit's SINV0 into it. *)
(** THE START-UP INVARIANT WITH THE RUN'S MMAP BASE CLOSED INSIDE IT.

    At #38 [AsanInit.SINV0] reads the run's mmap base: its memory conjunct is
    [wrap_mem inp mbase ...], because the auxv in the stack image carries the vDSO base
    [Run.launch_auxv] places from it. That base is [Run.ExecEntry]'s [en_mmap_base], an
    execve choice drawn by ASLR. [Run.valid_launch_base] quantifies it over a free [r]
    under [kb_aslr] and [mmap_rnd_bits], so no function of the input gives it. Binding it
    by a [Let] would pin the draw.

    Past start-up, a consumer has no base in scope and must not choose one. [SINV0L]
    binds the base EXISTENTIALLY, by the two facts [AsanInit]'s Section takes it under:
    [Hmb] ([valid_mmap_base]) and [Hlau] ([entry_launch_ok_va]). The producer has the
    run's own base and introduces the witness once ([cs_ok_SINV0L]). [cs_ok] reads its
    invariant only in [co_sinv], positively, so the repack is a field rebuild.

    [LAUNCH0] is the same binding for the lemmas about [argH0]. [argH0] itself reads no
    mmap base, but [AsanInit.argH0_high] is discharged over [Hlau], whose entry names
    one.

    Every [AsanInit] lemma is used below through [eapply ...; eassumption]. A Section
    lemma is generalised over exactly the variables and hypotheses its proof reads, so
    spelling out its arguments would hard-code that list. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec ShapeAlg AsanAcct Scfg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(** the run's mmap base, by its defining facts *)
Definition launch_base_ok (sp : word) (rdraw : EntryDraw) (brk0 : word) (inp : ProcInput) (mb : word) : Prop :=
  valid_mmap_base mb /\ entry_launch_ok_va Sv48 (mkEntry sp brk0 mb rdraw) inp.

(** some launch base exists: what a consumer of [argH0]'s facts may assume about it *)
Definition LAUNCH0 (sp : word) (rdraw : EntryDraw) (brk0 : word) (inp : ProcInput) : Prop :=
  exists mb, launch_base_ok sp rdraw brk0 inp mb.

(** [AsanInit.SINV0] at the run's mmap base, the base bound inside *)
Definition SINV0L (ph : PhdrInfo) (apc : N) (sp : word) (rdraw : EntryDraw) (brk0 : word) (inp : ProcInput)
    (E : env) (M : word -> option byte) : Prop :=
  exists mb, launch_base_ok sp rdraw brk0 inp mb /\ SINV0 ph apc sp rdraw brk0 mb inp E M.

Lemma LAUNCH0_intro : forall sp rdraw brk0 inp mb,
  valid_mmap_base mb -> entry_launch_ok_va Sv48 (mkEntry sp brk0 mb rdraw) inp -> LAUNCH0 sp rdraw brk0 inp.
Proof. intros sp rdraw brk0 inp mb H1 H2. exists mb. split; [exact H1|exact H2]. Qed.

Lemma SINV0L_intro : forall ph apc sp rdraw brk0 inp mb E M,
  valid_mmap_base mb -> entry_launch_ok_va Sv48 (mkEntry sp brk0 mb rdraw) inp ->
  SINV0 ph apc sp rdraw brk0 mb inp E M -> SINV0L ph apc sp rdraw brk0 inp E M.
Proof. intros ph apc sp rdraw brk0 inp mb E M H1 H2 H3. exists mb. split; [split; [exact H1|exact H2]|exact H3]. Qed.

(** the invariant's first conjunct reads no mmap base: it reads the launch variables below
    [V_EHDR] ([NX0 - 1], the last launch variable), and [E0] reads the base only at [V_EHDR],
    the vDSO text base the launch places there, which [cs_ok]'s [co_ehdr] ties to the model *)
Lemma SINV0L_ev : forall ph apc sp rdraw brk0 inp E M, SINV0L ph apc sp rdraw brk0 inp E M ->
  forall n, (n < NX0 - 1)%nat -> ev E n = ev (E0 sp rdraw brk0 (Z_to_bv 64 0) inp) n.
Proof.
  intros ph apc sp rdraw brk0 inp E M (mb & _ & H & _) n Hn. rewrite (H n) by (unfold NX0, V_EHDR in *; lia).
  unfold NX0 in Hn. do 14 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

Lemma SINV0L_launch : forall ph apc sp rdraw brk0 inp E M, SINV0L ph apc sp rdraw brk0 inp E M -> LAUNCH0 sp rdraw brk0 inp.
Proof. intros ph apc sp rdraw brk0 inp E M (mb & Hb & _). exists mb. exact Hb. Qed.

(** the two [AsanPlanSound] hypotheses about the invariant *)
Lemma SINV0L_frame : forall ph apc sp rdraw brk0 inp E M M',
  (forall a, argH0 sp rdraw inp E a = true -> M' a = M a) ->
  SINV0L ph apc sp rdraw brk0 inp E M -> SINV0L ph apc sp rdraw brk0 inp E M'.
Proof.
  intros ph apc sp rdraw brk0 inp E M M' Hf (mb & Hb & H). exists mb. split; [exact Hb|].
  eapply SINV0_frame; [exact Hf | exact H].
Qed.

(** [argH0] reads the valuation only through [e_sp0_early], whose variables are all
    below [NX0], so two valuations that agree there hide the same set.

    WHY THIS IS RE-PROVED HERE RATHER THAN TAKEN FROM [AsanInit.argH0_agree].  A
    Section lemma is generalised over exactly the variables its PROOF reads, and
    [AsanInit.SINV0_agree] reaches [argH0_agree] and so carries [segs : list Segment]
    as its first argument, which [SINV0L] deliberately does not have in scope: the
    whole point of the closed invariant is that a past-start-up consumer holds no
    image context.  Measured in a farm build,
    AsanInitL.v:79: "The term "Hag" has type "env_agree NX0 E E'" while it is expected
    to have type "list Segment"", with the whole environment printed and no [segs] in
    it.  [AsanNodesStartXInit.v:126] states the same fact and CAN use the donor,
    because its own Section declares [segs].  The proof below is
    [AsanInit.v:645-646]'s, verbatim, at top level. *)
Lemma E_SP0_L : AP.expr_vars_lt NX0 e_sp0_early = true.
Proof. reflexivity. Qed.

Lemma argH0_agree_L : forall sp rdraw inp E E' (a : word), env_agree NX0 E E' ->
  argH0 sp rdraw inp E a = argH0 sp rdraw inp E' a.
Proof.
  intros sp rdraw inp E E' a Hag. unfold argH0, uE.
  rewrite (edenot_agree NX0 E E' e_sp0_early Hag E_SP0_L). reflexivity.
Qed.

Lemma SINV0L_agree : forall ph apc sp rdraw brk0 inp E E' M, env_agree NX0 E E' ->
  SINV0L ph apc sp rdraw brk0 inp E M -> SINV0L ph apc sp rdraw brk0 inp E' M.
Proof.
  intros ph apc sp rdraw brk0 inp E E' M Hag (mb & Hb & H1 & H2). exists mb. split; [exact Hb|]. split.
  - intros n Hn. rewrite <- (proj1 Hag n) by (unfold NX0, V_EHDR in *; lia). apply H1. exact Hn.
  - intros a Ha. apply H2. rewrite (argH0_agree_L sp rdraw inp E E' a Hag). exact Ha.
Qed.

(** [argH0]'s facts, over some launch base.

    THE FOUR LEADING ARGUMENTS ARE SUPPLIED BY HAND, AND THEY ARE UNUSED.  Measured with
    an About probe (a one-target farm build): the discharged type is
      argH0_high : list Segment -> atable -> PhdrInfo -> N ->
        forall sp rdraw brk0 mbase inp, valid_sp sp -> valid_argv .. -> valid_envp .. ->
        entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp ->
        forall E a, argH0 sp rdraw inp E a = true -> CEIL <= bv_unsigned a
    The first four binders are ANONYMOUS in the type: AsanInit's proof mentions [segs],
    [A], [ph] and [apc] (through [argB0_high]'s layout chain) but the STATEMENT does not,
    so unification can never determine them and [eassumption] cannot invent them.  That is
    the whole content of "Error: No applicable tactic." at this line in
    an earlier build.  Any values do; [ASAN] (AsanPlanCore.v:4217) and a zero
    [PhdrInfo] are in scope here and carry no meaning in the result.  [CEIL] is a global,
    not a projection of [A], so the conclusion is unaffected. *)
Lemma argH0_high_L : forall sp rdraw brk0 inp,
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> LAUNCH0 sp rdraw brk0 inp ->
  forall E (a : word), argH0 sp rdraw inp E a = true -> CEIL <= bv_unsigned a.
Proof.
  intros sp rdraw brk0 inp Hsp Hva Hve (mb & Hmb & Hlau) E a Ha.
  eapply (argH0_high nil ASAN (mkPhdrInfo 0%N 0%N 0%N) 0%N); eassumption.
Qed.

(** under the invariant the hidden set is [argB0], the envp array and the string area.
    Same probe, same reason as above, but only TWO of the leading arguments are anonymous
    here - [ph] and [apc] are named in [argH0_SINV0]'s type and are determined by the
    [SINV0] premise:
      argH0_SINV0 : list Segment -> atable -> forall ph apc sp rdraw brk0 mbase inp,
        valid_sp sp -> valid_argv .. -> valid_envp .. -> entry_launch_ok_va Sv48 .. ->
        forall E M a, SINV0 ph apc sp rdraw brk0 mbase inp E M ->
                      argH0 sp rdraw inp E a = argB0 sp rdraw inp a *)
Lemma argH0_SINV0L : forall ph apc sp rdraw brk0 inp,
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  forall E M a, SINV0L ph apc sp rdraw brk0 inp E M -> argH0 sp rdraw inp E a = argB0 sp rdraw inp a.
Proof.
  intros ph apc sp rdraw brk0 inp Hsp Hva Hve E M a (mb & (Hmb & Hlau) & H).
  eapply (argH0_SINV0 nil ASAN); eassumption.
Qed.

(** the valuation's early stack pointer is the run's *)
Lemma SINV0L_sp0 : forall ph apc sp rdraw brk0 inp,
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  forall E M, SINV0L ph apc sp rdraw brk0 inp E M -> uE E e_sp0_early = bv_unsigned sp.
Proof.
  intros ph apc sp rdraw brk0 inp Hsp Hva Hve E M (mb & (Hmb & Hlau) & H).
  eapply SINV0_sp0_E0; eassumption.
Qed.

(** the memory the invariant pins, at its own base *)
Lemma SINV0L_mem : forall ph apc sp rdraw brk0 inp E M, SINV0L ph apc sp rdraw brk0 inp E M ->
  exists mb, launch_base_ok sp rdraw brk0 inp mb
    /\ forall a, argH0 sp rdraw inp E a = true -> M a = wrap_mem inp mb ph (Z_to_bv 64 (Z.of_N apc)) sp rdraw a.
Proof. intros ph apc sp rdraw brk0 inp E M (mb & Hb & _ & H). exists mb. split; [exact Hb|exact H]. Qed.

Section Repack.
  Context {SC : StepCfg}.

  (** THE ONE PLACE THE WITNESS IS INTRODUCED: a [cs_ok] at the run's own base is one at
      the closed invariant *)
  Lemma cs_ok_SINV0L : forall segs A LIMIT ph apc sp rdraw brk0 inp mb (argH : env -> word -> bool) fs E cs R FULL model,
    valid_mmap_base mb -> entry_launch_ok_va Sv48 (mkEntry sp brk0 mb rdraw) inp ->
    cs_ok segs A LIMIT (SINV0 ph apc sp rdraw brk0 mb inp) argH fs E cs R FULL model ->
    cs_ok segs A LIMIT (SINV0L ph apc sp rdraw brk0 inp) argH fs E cs R FULL model.
  Proof.
    intros segs A LIMIT ph apc sp rdraw brk0 inp mb argH fs E cs R FULL model Hmb Hlau HC.
    destruct HC. constructor; try assumption.
    eapply SINV0L_intro; eassumption.
  Qed.
End Repack.
