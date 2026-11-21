(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: new for LPS 727298f3: the start-up invariant with the run's mmap base bound inside it, made from this unit's As/AsanInit.v. *)
(** THE START-UP INVARIANT WITH THE RUN'S MMAP BASE BOUND INSIDE IT.

    At #38 [AsanInit.SINV0]'s memory conjunct is [wrap_mem inp mbase ...]: the stack
    image's auxv carries the vDSO base [Run.launch_auxv] places from the mmap base.
    That base is [Run.ExecEntry]'s [en_mmap_base], an execve choice: [Run.valid_launch_base]
    draws it from a free ASLR offset under [kb_aslr] and [mmap_rnd_bits], so no function
    of the input gives it, and a [Let] over [inp] would pin the draw.

    [AsanInit]'s Section takes the base under exactly two facts, [Hmb]
    ([valid_mmap_base]) and [Hlau] ([entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp],
    [Run.valid_entry]'s fifth conjunct).  [SINV0L] binds the base EXISTENTIALLY by those
    two facts, so a consumer past start-up has none in scope and cannot choose one.

    Why not the model's own [vm_mmap_base]: [AsanPlanSound]'s [SINV] is one Section
    variable for the whole step chain while [model] changes at every step, and [cs_ok]
    has no field relating the model's base to anything, so the identity would need a
    preservation fact [cs_ok] does not carry.  No consumer needs it: [argH0]'s set (the
    argv pointers from argv[2], the envp array, the string area) holds no auxv word.

    The producer has the run's own base and introduces the witness once
    ([cs_ok_SINV0L]); [cs_ok] reads its invariant only in [co_sinv].

    Every [AsanInit] lemma is used through [eapply ...; eassumption] inside a Section
    carrying [AsanInit]'s hypotheses: a Section lemma is generalised over exactly the
    variables and hypotheses its proof reads, so the lemmas below are too, and spelling
    out an [AsanInit] argument list would hard-code one. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim StepTac ShapeAlg AgentLib StartupAux RefLayout ArgvEnv AsanAcct AsanAcctShape AsanPlacement BackingAlgebra Scfg.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanCeil AsanInit.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(** the run's mmap base, by its two defining facts *)
Definition launch_base_ok (sp : word) (rdraw : EntryDraw) (brk0 : word) (inp : ProcInput) (mb : word) : Prop :=
  valid_mmap_base mb /\ entry_launch_ok_va Sv48 (mkEntry sp brk0 mb rdraw) inp.

(** some launch base exists *)
Definition LAUNCH0 (sp : word) (rdraw : EntryDraw) (brk0 : word) (inp : ProcInput) : Prop :=
  exists mb, launch_base_ok sp rdraw brk0 inp mb.

(** [AsanInit.SINV0] at the run's mmap base, the base bound inside *)
Definition SINV0L (ph : PhdrInfo) (apc : N) (sp : word) (rdraw : EntryDraw) (brk0 : word) (inp : ProcInput)
    (E : env) (M : word -> option byte) : Prop :=
  exists mb, launch_base_ok sp rdraw brk0 inp mb /\ SINV0 ph apc sp rdraw brk0 mb inp E M.

Lemma SINV0L_intro : forall ph apc sp rdraw brk0 inp mb E M,
  valid_mmap_base mb -> entry_launch_ok_va Sv48 (mkEntry sp brk0 mb rdraw) inp ->
  SINV0 ph apc sp rdraw brk0 mb inp E M -> SINV0L ph apc sp rdraw brk0 inp E M.
Proof. intros ph apc sp rdraw brk0 inp mb E M H1 H2 H3. exists mb. split; [split; [exact H1|exact H2]|exact H3]. Qed.

Lemma SINV0L_launch : forall ph apc sp rdraw brk0 inp E M,
  SINV0L ph apc sp rdraw brk0 inp E M -> LAUNCH0 sp rdraw brk0 inp.
Proof. intros ph apc sp rdraw brk0 inp E M (mb & Hb & _). exists mb. exact Hb. Qed.

(** the invariant's first conjunct reads no mmap base *)
Lemma SINV0L_ev : forall ph apc sp rdraw brk0 inp E M, SINV0L ph apc sp rdraw brk0 inp E M ->
  forall n, (n < NX0)%nat -> ev E n = ev (E0 sp rdraw brk0 inp) n.
Proof. intros ph apc sp rdraw brk0 inp E M (mb & _ & H & _). exact H. Qed.

(** the memory the invariant pins, at its own base *)
Lemma SINV0L_mem : forall ph apc sp rdraw brk0 inp E M, SINV0L ph apc sp rdraw brk0 inp E M ->
  exists mb, launch_base_ok sp rdraw brk0 inp mb
    /\ forall a, argH0 sp rdraw inp E a = true -> M a = wrap_mem inp mb ph (Z_to_bv 64 (Z.of_N apc)) sp rdraw a.
Proof. intros ph apc sp rdraw brk0 inp E M (mb & Hb & _ & H). exists mb. split; [exact Hb|exact H]. Qed.

Section InitL.
  (** [AsanInit]'s Section, less [mbase], [Hmb] and [Hlau] *)
  Variable segs : list Segment.
  Variable A : atable.
  Variable ph : PhdrInfo.
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variable inp : ProcInput.

  Hypothesis IMG : img_facts segs A ph.
  Hypothesis Hapc : Z.of_N apc = a_entry A.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk segs brk0.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hhw : valid_hwcap (in_hwcap inp).
  Hypothesis Hlaunch : valid_launch inp.

  #[local] Notation SINV := (SINV0L ph apc sp rdraw brk0 inp).
  #[local] Notation argH := (argH0 sp rdraw inp).

  (** the two [AsanPlanSound] hypotheses about the invariant *)
  Lemma SINV0L_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Proof.
    intros E M M' Hf (mb & Hb & H). exists mb. split; [exact Hb|].
    (* [AsanInit.SINV0_frame] is Section-generalised, so its leading explicit arguments
       are [AsanInit]'s own Section variables and a two-bullet split lands on [segs]
       (measured: ":108 ... expected to have
       type list Segment").  The goal determines [ph apc sp rdraw brk0 mb inp E M'];
       [segs] and [A] are the only [list Segment] and [atable] in scope, so
       [eassumption] places every argument without depending on the count. *)
    eapply SINV0_frame; eassumption.
  Qed.

  Lemma SINV0L_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.
  Proof.
    intros E E' M Hag (mb & Hb & H). exists mb. split; [exact Hb|].
    eapply SINV0_agree; eassumption.
  Qed.

  (** [argH0]'s own facts, over some launch base *)
  Lemma argH0_high_L : LAUNCH0 sp rdraw brk0 inp -> forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Proof. intros (mb & Hmb & Hlau) E a Ha. eapply argH0_high; [eassumption .. | exact Ha]. Qed.

  Lemma argH0_sp0_L : forall E (a : word), argH E a = true -> bv_unsigned (edenot E e_sp0_early) <= bv_unsigned a.
  Proof. intros E a Ha. unfold argH0 in Ha. apply andb_prop in Ha as [_ Ha]. apply Z.leb_le in Ha. exact Ha. Qed.

  Lemma argH0_agree_L : forall E E' (a : word), env_agree NX0 E E' -> argH E a = argH E' a.
  Proof. intros E E' a Hag. unfold argH0, uE. rewrite (edenot_agree NX0 E E' e_sp0_early Hag eq_refl). reflexivity. Qed.

  (** under the invariant the hidden set is [argB0] *)
  Lemma argH0_SINV0L : forall E M a, SINV E M -> argH E a = argB0 sp rdraw inp a.
  Proof. intros E M a (mb & (Hmb & Hlau) & H). eapply argH0_SINV0; [eassumption .. | exact H]. Qed.

  (** every hidden byte is present *)
  Lemma hidden_present_L : forall E M a, SINV E M -> argH E a = true -> exists b, M a = Some b.
  Proof. intros E M a (mb & (Hmb & Hlau) & H) Ha. eapply hidden_present; [eassumption .. | exact H | exact Ha]. Qed.

  (** the valuation's early stack pointer, page and argument pointers are the run's *)
  Lemma SINV0L_sp0 : forall E M, SINV E M -> uE E e_sp0_early = bv_unsigned sp.
  Proof. intros E M (mb & (Hmb & Hlau) & H). eapply SINV0_sp0_E0; [eassumption .. | exact H]. Qed.

  Lemma SINV0L_pg : forall E M, SINV E M -> uE E e_pg_early = pagedown (uE E e_sp0_early).
  Proof. intros E M (mb & (Hmb & Hlau) & H). eapply SINV0_pg_E0; [eassumption .. | exact H]. Qed.

  Lemma SINV0L_vals : forall E M, SINV E M ->
    uE E e_envp = bv_unsigned sp + 8 * Z.of_nat (length (in_argv inp)) + 16
    /\ ev E V_ENVC = Z_to_bv 64 (Z.of_nat (length (in_envp inp)))
    /\ uE E e_str0 = bv_unsigned sp
                     + Z.of_nat (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp)).
  Proof. intros E M (mb & (Hmb & Hlau) & H). eapply SINV0_vals_E0; [eassumption .. | exact H]. Qed.

  (** the envp array and argv[0] read through the image, at the invariant's base *)
  Lemma SINV0L_args : forall E M, SINV E M ->
    exists mb, launch_base_ok sp rdraw brk0 inp mb
    /\ (forall a : word,
          bv_unsigned sp + 8 * Z.of_nat (length (in_argv inp)) + 16 <= bv_unsigned a
            < bv_unsigned sp + 8 * Z.of_nat (length (in_argv inp)) + 16 + 8 * Z.of_nat (length (in_envp inp)) + 8 ->
          M a = wrap_mem inp mb ph (Z_to_bv 64 (Z.of_N apc)) sp rdraw a)
    /\ (forall a : word,
          bv_unsigned sp + Z.of_nat (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp))
            <= bv_unsigned a
            <= bv_unsigned sp + Z.of_nat (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp))
               + Z.of_nat (length (nth 0 (in_argv inp) [])) ->
          M a = wrap_mem inp mb ph (Z_to_bv 64 (Z.of_N apc)) sp rdraw a).
  Proof.
    intros E M (mb & (Hmb & Hlau) & H). exists mb. split; [split; assumption|]. split.
    - intros a Ha. eapply SINV0_envp_E0; [eassumption .. | exact H | exact Ha].
    - intros a Ha. eapply SINV0_str0_E0; [eassumption .. | exact H | exact Ha].
  Qed.
End InitL.

Section Repack.
  Context {SC : StepCfg}.

  (** THE ONE PLACE THE WITNESS IS INTRODUCED: a [cs_ok] at the run's own base is one at
      the bound invariant *)
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
