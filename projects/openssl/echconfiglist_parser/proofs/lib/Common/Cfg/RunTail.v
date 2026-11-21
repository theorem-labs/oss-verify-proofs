(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/echconfiglist_parser/lib/SymDrive.v, with rz_run restated over the run's segment list, and proofs/openssl/echconfiglist_parser/lib/RefPrintfFirst.v's rz_run_lf likewise; 202 of its 238 lines of code are new or changed and 124 lines of the source are left out. *)
(* Theorem Labs, 2026-11 (LPS 727298f3): walks that run over the binary's own segments up to a
   point and over the run's segment list after it.  At 727298f3 a run that calls time() reads the
   vDSO image and jumps into it ([Run.run_segments] = the binary's segments ++ the vDSO pair), so a
   walk that reaches such a call cannot be stated over the binary's segments alone, and a
   continuation-passing lemma cannot be lifted by its statement ([RomStable.realizes_app_tail]
   lifts a WHOLE walk).  This file is the generic part of the lift, for any binary and any tail
   that is neither executable nor writable (the vDSO pair is both, [RomStable.vdso_segments_nx/nw]):

   - machine steps over [segs] are machine steps over [segs ++ tail] ([step_app_tail],
     [msteps_app_tail], [exec_msteps_app_tail]) and with any read-only backing ([step_wrom],
     [exec_msteps_wrom]): no machine step reads [ms_rom];
   - [rz_run_tail] / [rz_run_lf_tail]: [SymDrive.rz_run] / [RefPrintfFirst.rz_run_lf] with the
     symbolic run computed over [segs] and the walk stated over [segs ++ tail], so a chain file
     keeps its computed runs;
   - [sreach_app_tail] / [sreach_wrom]: an [SReach.sreach] over [segs] (the heap instances' [hs_SR])
     is one over [segs ++ tail] from the state with the larger backing, as
     [RomStable.realizes_app_tail] / [realizes_wrom] are for [realizes];
   - [exec_evt_sreach_tail]: the [SR_laws] straight-line law over the larger backing.
   Copy this file whole into a unit with the same [ShapeAlg]/[SReach]/[SymRun] layer. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg SymExec Frame Scfg
  SymExec2 SymExec2Sound SymRun SReach SReachTree.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Exec.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import RomBase RomStable.
Import ListNotations.
Import SX2. Import SX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(** * Machine steps and the read-only backing *)

Lemma step_wrom : forall segs ms ms' r,
  RiscvSemantics.step segs ms = MachineOk ms' ->
  RiscvSemantics.step segs (wrom ms r) = MachineOk (wrom ms' r).
Proof.
  intros segs ms ms' r. unfold RiscvSemantics.step. rewrite (step_accesses_wrom segs).
  destruct (step_accesses segs ms) as [rep| |]; cbn; intro H; try discriminate H.
  injection H as <-. reflexivity.
Qed.

Lemma exec_msteps_wrom : forall segs ms ms' r,
  Exec.msteps segs ms ms' -> Exec.msteps segs (wrom ms r) (wrom ms' r).
Proof.
  intros segs ms ms' r H. induction H as [ms | ms ms1 ms2 [Hsvc Hstep] Hms IH].
  - apply Exec.msteps_refl.
  - eapply Exec.msteps_cons; [split; [exact Hsvc | exact (step_wrom segs ms ms1 r Hstep)] | exact IH].
Qed.

Section Tail.
  Variables segs tail : list Segment.
  Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
  Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.

  Lemma step_app_tail : forall ms ms',
    RiscvSemantics.step segs ms = MachineOk ms' -> RiscvSemantics.step (segs ++ tail) ms = MachineOk ms'.
  Proof.
    intros ms ms'. unfold RiscvSemantics.step.
    destruct (step_accesses segs ms) as [rep| |] eqn:E; cbn; intro H; try discriminate H.
    assert (E' : step_accesses (segs ++ tail) ms = MachineOk rep) by (eapply step_accesses_app_nx; eassumption).
    rewrite E'. exact H.
  Qed.

  Lemma msteps_app_tail : forall ms ms', msteps segs ms ms' -> msteps (segs ++ tail) ms ms'.
  Proof.
    intros ms ms' H. induction H as [ms | ms ms1 ms2 Hsvc Hstep Hms IH]; [apply mst_refl|].
    eapply mst_step; [exact Hsvc | exact (step_app_tail ms ms1 Hstep) | exact IH].
  Qed.

  Lemma exec_msteps_app_tail : forall ms ms', Exec.msteps segs ms ms' -> Exec.msteps (segs ++ tail) ms ms'.
  Proof.
    intros ms ms' H. induction H as [ms | ms ms1 ms2 [Hsvc Hstep] Hms IH]; [apply Exec.msteps_refl|].
    eapply Exec.msteps_cons; [split; [exact Hsvc | exact (step_app_tail ms ms1 Hstep)] | exact IH].
  Qed.

  (** The binary's read-only view is part of the larger list's. *)
  Lemma rom_ext_app_tail : rom_ext (seg_rom segs) (seg_rom (segs ++ tail)).
  Proof.
    intros a b. unfold seg_rom.
    destruct (memory_read segs a 1) as [bs|] eqn:E; [|intro H; discriminate H].
    rewrite (memory_read_app_nx segs tail a 1 bs E). intro H; exact H.
  Qed.

  Context {SC : StepCfg}.

  (** [SymDrive.rz_run], with the walk over [segs ++ tail]: the symbolic run and its facts are
      over [segs]; the read-only backing is any. *)
  Theorem rz_run_tail : forall fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2
                           E M rom R model T,
    sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
    carry (s_log ss') kn [] = (kn', scs2, hs2) ->
    regs_ok E sr R -> know_ok segs E M kn ->
    scs_denot segs M E scs -> scs_denot segs M E scs2 ->
    m_halted model = None ->
    m_vm_lazy model = [] ->
    (forall R' M', regs_ok E (s_regs ss') R' -> know_ok segs E M' kn' ->
       M' = mem_denot E M (s_log ss') ->
       realizes (segs ++ tail) (mkCfg (mkst R' (Z_to_bv 64 (s_pc ss')) M' rom) model) T) ->
    realizes (segs ++ tail) (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) T.
  Proof.
    intros fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R model T
           Hex Hc HR HK Hsc Hsc2 Hh Hlazy Hcont.
    destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E M rom R Hex HR HK Hsc)
      as (R' & HR' & Hlf & Hms).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact (msteps_app_tail _ _ Hms) |].
    apply (Hcont R' _ HR'); [|reflexivity].
    eapply carry_after; eassumption.
  Qed.

  (** [RefPrintfFirst.rz_run_lf] (the continuation also has the log's flatness), likewise. *)
  Theorem rz_run_lf_tail : forall fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2
                              E M rom R model T,
    sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
    carry (s_log ss') kn [] = (kn', scs2, hs2) ->
    regs_ok E sr R -> know_ok segs E M kn ->
    scs_denot segs M E scs -> scs_denot segs M E scs2 ->
    m_halted model = None ->
    m_vm_lazy model = [] ->
    (forall R' M', regs_ok E (s_regs ss') R' -> know_ok segs E M' kn' ->
       M' = mem_denot E M (s_log ss') -> log_flat E (s_log ss') ->
       realizes (segs ++ tail) (mkCfg (mkst R' (Z_to_bv 64 (s_pc ss')) M' rom) model) T) ->
    realizes (segs ++ tail) (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) T.
  Proof.
    intros fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R model T
           Hex Hc HR HK Hsc Hsc2 Hh Hlazy Hcont.
    destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E M rom R Hex HR HK Hsc)
      as (R' & HR' & Hlf & Hms).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact (msteps_app_tail _ _ Hms) |].
    apply (Hcont R' _ HR'); [| reflexivity | exact Hlf].
    eapply carry_after; eassumption.
  Qed.

  (** [SR_laws]' straight-line law over the larger list and any backing. *)
  Lemma exec_evt_sreach_tail : forall (P : machine_state -> Prop) ms model r,
    m_halted model = None -> m_vm_lazy model = [] ->
    Exec.evt segs P ms ->
    sreach (segs ++ tail) (fun c => exists c0, c = cwrom c0 r /\ (P (cfg_ms c0) /\ cfg_model c0 = model))
           (cwrom (mkCfg ms model) r).
  Proof.
    intros P ms model r Hh Hlazy (ms' & Hms & HP).
    change (cwrom (mkCfg ms model) r) with (mkCfg (wrom ms r) model).
    eapply sreach_mono.
    - apply (cj_evt_sreach (segs ++ tail) (fun x => x = wrom ms' r) (wrom ms r) model Hh Hlazy).
      exists (wrom ms' r). split; [|reflexivity].
      exact (exec_msteps_app_tail _ _ (exec_msteps_wrom segs ms ms' r Hms)).
    - intros [ms1 mo1] [E1 E2]. cbn [cfg_ms cfg_model] in E1, E2. subst ms1 mo1.
      exists (mkCfg ms' model). split; [reflexivity | split; [exact HP | reflexivity]].
  Qed.

  Hypothesis Hvi : vdso_image segs = None.

  Lemma vdso_fn_none_tail : forall pc, vdso_entry_fn segs pc = None.
  Proof. intros pc. unfold vdso_entry_fn. rewrite Hvi. reflexivity. Qed.

  (** A step from [c] over the larger list is one over [segs], given that [c] steps over [segs]. *)
  Lemma sstep_back_tail : forall c e0 c0 e st,
    sstep_cfg segs the_scfg c e0 (SNext c0) ->
    sstep_cfg (segs ++ tail) the_scfg c e st -> sstep_cfg segs the_scfg c e st.
  Proof.
    intros [ms model] e0 c0 e st H0 H.
    eapply sstep_cfg_app_back; try eassumption.
    intros Hsvc. inversion H0; subst;
      first [ eexists; eassumption
            | exfalso; rewrite vdso_fn_none_tail in *; discriminate
            | congruence ].
  Qed.

  Theorem sreach_app_tail : forall Q c, sreach segs Q c -> sreach (segs ++ tail) Q c.
  Proof.
    intros Q c H. induction H as [c Hc | c Hrob Hprog Hall Hk IH].
    - apply sr_done. exact Hc.
    - destruct Hprog as [c1 Hc1].
      apply sr_step.
      + eapply sys_rob_app_tail; eassumption.
      + exists c1. eapply sstep_cfg_app_next; eassumption.
      + intros evs X Hss. apply Hall. exact (sstep_back_tail c [] c1 evs X Hc1 Hss).
      + intros evs c' Hss. exact (IH evs c' (sstep_back_tail c [] c1 evs (SNext c') Hc1 Hss)).
  Qed.

  (** [RomStable.realizes_wrom] for [sreach]: the walk from the state with a larger backing
      reaches the targets with that backing. *)
  Theorem sreach_wrom : forall Q c, sreach segs Q c -> forall r, rom_ext (ms_rom (cfg_ms c)) r ->
    sreach segs (fun c' => exists c0, c' = cwrom c0 r /\ Q c0) (cwrom c r).
  Proof.
    intros Q c H. induction H as [c Hc | c Hrob Hprog Hall Hk IH]; intros r Hr.
    - apply sr_done. exists c. split; [reflexivity | exact Hc].
    - destruct Hprog as [c1 Hc1].
      apply sr_step.
      + eapply sys_rob_wrom; eassumption.
      + exists (cwrom c1 r). eapply sstep_wrom_fwd; eassumption.
      + intros evs X Hss.
        assert (Hb : exists st0, sstep_cfg segs the_scfg c evs st0
                     /\ X = match st0 with SNext c0 => SNext (cwrom c0 r) | SError => SError end)
          by (eapply sstep_wrom_back; eassumption).
        destruct Hb as (st0 & H0 & E0).
        destruct (Hall evs st0 H0) as [Hevs (c2 & ->)]. subst X. split; [exact Hevs | eexists; reflexivity].
      + intros evs c' Hss.
        assert (Hb : exists st0, sstep_cfg segs the_scfg c evs st0
                     /\ SNext c' = match st0 with SNext c0 => SNext (cwrom c0 r) | SError => SError end)
          by (eapply sstep_wrom_back; eassumption).
        destruct Hb as (st0 & H0 & E0).
        destruct st0 as [c2|]; cbv iota in E0; [| discriminate E0]. injection E0 as ->.
        apply (IH evs c2 H0 r).
        assert (Er : ms_rom (cfg_ms c2) = ms_rom (cfg_ms c)) by (eapply sstep_cfg_next_rom; eassumption).
        rewrite Er. exact Hr.
  Qed.

  (** The two composed: an [sreach] over [segs] from a state with the binary's backing is one over
      the larger list from the state with the larger list's backing. *)
  Theorem sreach_lift_tail : forall Q c, sreach segs Q c -> ms_rom (cfg_ms c) = seg_rom segs ->
    sreach (segs ++ tail) (fun c' => exists c0, c' = cwrom c0 (seg_rom (segs ++ tail)) /\ Q c0)
           (cwrom c (seg_rom (segs ++ tail))).
  Proof.
    intros Q c H Hr. apply sreach_app_tail. apply sreach_wrom; [exact H|].
    rewrite Hr. exact rom_ext_app_tail.
  Qed.
End Tail.

(** A whole walk over [segs] from the binary's backing is a walk over [segs ++ tail] from the
    larger list's backing ([RomStable.realizes_wrom], then [RomStable.realizes_app_tail]).  Every
    branch of a chain that never reaches the vDSO lifts this way. *)
Theorem realizes_lift_tail {SC : StepCfg} : forall segs tail,
  (forall s, In s tail -> seg_executable s = false) ->
  (forall s, In s tail -> seg_writable s = false) ->
  vdso_image segs = None ->
  forall regs pc mem mo T,
    realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) mo) T ->
    realizes (segs ++ tail) (mkCfg (mkst regs pc mem (seg_rom (segs ++ tail))) mo) T.
Proof.
  intros segs tail Hnx Hnw Hvi regs pc mem mo T H.
  apply (realizes_app_tail segs tail Hnx Hnw Hvi).
  exact (realizes_wrom segs Hvi _ T H (seg_rom (segs ++ tail)) (rom_ext_app_tail segs tail)).
Qed.

(** * The tail as a class

    A chain that reaches the vDSO is stated over [segs ++ rt_tail] with that list's read-only
    backing.  The tail and its two permission facts are a class, found by instance search as
    [HeapCeil] is, so a lemma that gains them keeps its positional arguments.  The instance is
    built where the launch fixes the tail ([Run.run_segments] = segs ++ [Run.vdso_segments ..],
    whose two facts are [RomStable.vdso_segments_nx] / [vdso_segments_nw]). *)
Class RunTail : Type := mkRunTail {
  rt_tail : list Segment;
  rt_nx : forall s, In s rt_tail -> seg_executable s = false;
  rt_nw : forall s, In s rt_tail -> seg_writable s = false }.

Definition run_tail_of (kb : KernelBuild) (sp mbase : word) : RunTail :=
  mkRunTail (vdso_segments kb sp mbase) (vdso_segments_nx kb sp mbase) (vdso_segments_nw kb sp mbase).

(** The tail lemmas with the class's tail and facts, so a chain file names no permission
    fact.  Each is the lemma above (or [RomStable]'s) at [rt_tail]. *)
Section WithRT.
  Context {RT : RunTail}.

  Lemma rt_fetch_word : forall segs a, fetch_word (segs ++ rt_tail) a = fetch_word segs a.
  Proof. intros segs a. apply fetch_word_app_nx; first [exact rt_nx | exact rt_nw]. Qed.

  Lemma rt_store_ok : forall segs n m a, store_ok (segs ++ rt_tail) m a n = store_ok segs m a n.
  Proof. intros segs n m a. apply store_ok_app_nw; first [exact rt_nx | exact rt_nw]. Qed.

  Lemma rt_ov_read : forall segs n m a bs,
    ov_read_bytes segs m a n = Some bs -> ov_read_bytes (segs ++ rt_tail) m a n = Some bs.
  Proof. intros segs n m a bs H. eapply ov_read_bytes_app_nx; first [exact rt_nx | exact rt_nw | exact H]. Qed.

  Lemma rt_memory_read : forall segs a n bs,
    memory_read segs a n = Some bs -> memory_read (segs ++ rt_tail) a n = Some bs.
  Proof. intros segs a n bs H. eapply memory_read_app_nx; first [exact rt_nx | exact rt_nw | exact H]. Qed.

  Lemma rt_msteps : forall segs ms ms', Exec.msteps segs ms ms' -> Exec.msteps (segs ++ rt_tail) ms ms'.
  Proof. intros segs ms ms' H. eapply exec_msteps_app_tail; first [exact rt_nx | exact rt_nw | exact H]. Qed.

  Lemma rt_msteps_sym : forall segs ms ms', msteps segs ms ms' -> msteps (segs ++ rt_tail) ms ms'.
  Proof. intros segs ms ms' H. eapply msteps_app_tail; first [exact rt_nx | exact rt_nw | exact H]. Qed.

  Context {SC : StepCfg}.

  Theorem rz_run_rt : forall segs fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R model T,
    sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
    carry (s_log ss') kn [] = (kn', scs2, hs2) ->
    regs_ok E sr R -> know_ok segs E M kn ->
    scs_denot segs M E scs -> scs_denot segs M E scs2 ->
    m_halted model = None -> m_vm_lazy model = [] ->
    (forall R' M', regs_ok E (s_regs ss') R' -> know_ok segs E M' kn' ->
       M' = mem_denot E M (s_log ss') ->
       realizes (segs ++ rt_tail) (mkCfg (mkst R' (Z_to_bv 64 (s_pc ss')) M' rom) model) T) ->
    realizes (segs ++ rt_tail) (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) T.
  Proof. intros. eapply (rz_run_tail segs rt_tail); first [exact rt_nx | exact rt_nw | eassumption]. Qed.

  Theorem rz_run_lf_rt : forall segs fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R model T,
    sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
    carry (s_log ss') kn [] = (kn', scs2, hs2) ->
    regs_ok E sr R -> know_ok segs E M kn ->
    scs_denot segs M E scs -> scs_denot segs M E scs2 ->
    m_halted model = None -> m_vm_lazy model = [] ->
    (forall R' M', regs_ok E (s_regs ss') R' -> know_ok segs E M' kn' ->
       M' = mem_denot E M (s_log ss') -> log_flat E (s_log ss') ->
       realizes (segs ++ rt_tail) (mkCfg (mkst R' (Z_to_bv 64 (s_pc ss')) M' rom) model) T) ->
    realizes (segs ++ rt_tail) (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) T.
  Proof. intros. eapply (rz_run_lf_tail segs rt_tail); first [exact rt_nx | exact rt_nw | eassumption]. Qed.

  Theorem realizes_lift_rt : forall segs, vdso_image segs = None ->
    forall regs pc mem mo T,
      realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) mo) T ->
      realizes (segs ++ rt_tail) (mkCfg (mkst regs pc mem (seg_rom (segs ++ rt_tail))) mo) T.
  Proof. intros segs Hvi. apply (realizes_lift_tail segs rt_tail rt_nx rt_nw Hvi). Qed.

  Theorem sreach_lift_rt : forall segs, vdso_image segs = None ->
    forall Q c, sreach segs Q c -> ms_rom (cfg_ms c) = seg_rom segs ->
      sreach (segs ++ rt_tail) (fun c' => exists c0, c' = cwrom c0 (seg_rom (segs ++ rt_tail)) /\ Q c0)
             (cwrom c (seg_rom (segs ++ rt_tail))).
  Proof. intros segs Hvi Q c H Hr. eapply (sreach_lift_tail segs rt_tail); first [exact rt_nx | exact rt_nw | exact Hvi | exact H | exact Hr]. Qed.
End WithRT.
