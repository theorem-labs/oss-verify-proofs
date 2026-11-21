(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Common/ShapeAlg.v: the relation realizes with a no-allocation-call check at each node (rzb), its soundness for the budget premise, and ShapeAlg's node lemmas on the usage path restated over rzb. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the read-only-backing premise RomBase.sys_rob of rzb_node, rzb_silent1 and rzb_emit1; the vDSO materialization fault of budget_refused_at; the new nalloc_ok_cwrom, rzb_wrom, rzb_app_tail, rzb_run_segments and rzb_run_init, which lift a walk to the run segment list; the RomBase and RomStable imports). *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import SimInv ExitSim CatSim MmapSim AllocSim AllocSim2 WallSim CfgStep.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import AllocRefusal ShapeAlg.

Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Cfg Require RomBase RomStable.
(** * [rzb]: [ShapeAlg.realizes] with a no-allocation-call check at each node

    [ShapeAlg.realizes segs c T] ties a trace set to the one-step families of
    the configurations a run reaches, for the filtered step
    [sstep_cfg segs kit_cfg] ([kit_cfg = alloc_only_cfg false]).  It has no
    cut, but a derivation records nothing about the configurations it passes,
    so no [realizes] proof says that a run is never refused by the budget.
    [rzb] has the same three constructors, and its node constructor asks,
    besides [node_ok], for [nalloc_ok c]: if a syscall is pending at [c], its
    number is none of 214, 216, 222 and 226, the RISC-V Linux numbers of brk,
    mremap, mmap and mprotect ([Run.alloc_mark_sysnos]).

    That one fact gives both things the budget premise needs.
    - The grant clause of [Run.budget_refused_at] is false: off those four
      numbers [Run.alloc_budget_refused_b] answers [false]
      ([Run.alloc_budget_refused_b_outside]).
    - Every step of the unfiltered relation [sstep] from [c] is a step of
      [sstep_cfg segs kit_cfg]: [kit_cfg] filters only the allocation family
      ([CfgStep.kit_pending_on_not_alloc], [CfgStep.sstep_cfg_of_sstep_on]).
      So the completeness half of [node_ok] covers the unfiltered run, which
      is the run [Run.reaches_budget_refused] reads, and it excludes an
      [SError] step; the two first-touch clauses of [Run.budget_refused_at]
      are premises of an [SError] step
      ([Run.budget_fault_instr_sstep_error],
      [Run.budget_fault_syscall_sstep_error]).

    [rzb_never_refused]: no configuration the unfiltered run reaches from an
    [rzb] configuration is budget-refused; [rzb_never_refused_cfg]: so under
    every spurious-failure configuration.

    The rest of the file is ShapeAlg's lemmas that build a [realizes] node on
    the usage path, restated over [rzb] with their proofs: [rz_] is written
    [rzb_], [realizes] is written [rzb].  A lemma that takes a [node_ok] also
    takes [nalloc_ok] for the same configuration; a lemma whose node is an
    instruction or an exit derives it. *)

(** If a syscall is pending, it is not an allocation call. *)
Definition nalloc_ok (c : config) : Prop := not_alloc_pending (cfg_ms c).

Lemma nalloc_ok_instr : forall ms model,
  ms_svc_pending ms = None -> nalloc_ok (mkCfg ms model).
Proof. intros ms model H. exact (not_alloc_pending_none ms H). Qed.

Lemma nalloc_ok_sysno : forall ms model x8 n,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = n -> alloc_no_b n = false ->
  nalloc_ok (mkCfg ms model).
Proof. intros ms model x8 n Hsvc Hn Hno. exact (not_alloc_pending_sysno ms x8 n Hsvc Hn Hno). Qed.

(** The exit (93 or 94) is off the four allocation numbers. *)
Lemma nalloc_ok_exit : forall ms model x8,
  ms_svc_pending ms = Some x8 -> is_exit_no x8 -> nalloc_ok (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc Hx8.
  destruct Hx8 as [E | E]; exact (nalloc_ok_sysno ms model x8 _ Hsvc E eq_refl).
Qed.

Section WithSegs.
Variable segs : list Segment.

Inductive rzb : config -> TSet -> Prop :=
| rzb_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                    (T : I -> TSet) (i0 : I),
    node_ok segs c I evs nx ->
    (* LPS 08b1429: the node's syscall reads the same over a larger read-only backing, so a
       walk over the binary's own segments lifts to the run's segment list
       ([Rzb.rzb_run_init]).  [ShapeAlg.rz_node] asks the same, in the same place. *)
    RomBase.sys_rob segs c ->
    nalloc_ok c ->
    (forall i, rzb (nx i) (T i)) ->
    rzb c (t_alt (fun i => t_emit (evs i) (T i)))
| rzb_halt : forall c,
    m_halted (cfg_model c) <> None ->
    rzb c t_nil
| rzb_conseq : forall c T T',
    rzb c T -> t_eq T T' -> rzb c T'.

(** ** Soundness for the budget premise *)

Lemma nalloc_ok_on : forall c, nalloc_ok c -> pending_on segs kit_cfg c.
Proof. intros [ms model] H. exact (kit_pending_on_not_alloc segs ms model H). Qed.

Lemma rzb_sstep_lift : forall c e st,
  nalloc_ok c -> sstep segs c e st -> sstep_cfg segs kit_cfg c e st.
Proof. intros c e st Hb H. exact (sstep_cfg_of_sstep_on segs kit_cfg c e st (nalloc_ok_on c Hb) H). Qed.

Lemma star_cases : forall c tr c', star segs c tr c' ->
  c' = c \/ exists e c2 tr2, sstep segs c e (SNext c2) /\ star segs c2 tr2 c'.
Proof.
  intros c tr c' H. destruct H as [c0 | c1 e c2 tr2 c3 Hss Hstar].
  - left. reflexivity.
  - right. exists e, c2, tr2. split; [exact Hss | exact Hstar].
Qed.

(** A node with the check is not budget-refused. *)
Lemma node_not_refused : forall c I evs nx,
  node_ok segs c I evs nx -> nalloc_ok c -> ~ budget_refused_at segs c.
Proof.
  intros [ms model] I evs nx [_ Hc] Hb [Hh Hr].
  assert (Herr : ~ sstep segs (mkCfg ms model) [] SError).
  { intros Hs.
    destruct (Hc [] SError (rzb_sstep_lift _ [] SError Hb Hs)) as (i & _ & Hbad).
    discriminate Hbad. }
  cbn [cfg_ms cfg_model] in Hh, Hr.
  (* LPS 727298f3: [Run.budget_refused_at]'s instruction half is TWO clauses now --
     the first-touch fault and the vDSO materialization fault -- and both are premises
     of an [SError] step ([Run.budget_fault_instr_sstep_error],
     [Run.budget_fault_vdso_sstep_error]), so both close the same way. *)
  destruct Hr as [(Hsvc & [ (report & Hstep & Hmat)
                          | (Hacct & fn & n & eff0 & model0 & evs0 & Hfn & Hsys & Hspec0 & Hret0 & Hh0 & Hmat0) ])
                 | (x8 & Hx8 & [Hgr | (eff & model' & evs' & Hspec & Hh' & Hmat)])].
  - exact (Herr (budget_fault_instr_sstep_error segs ms model report Hh Hsvc Hstep Hmat)).
  - exact (Herr (budget_fault_vdso_sstep_error segs ms model fn n eff0 model0 evs0
                   Hh Hsvc Hacct Hfn Hsys Hspec0 Hret0 Hh0 Hmat0)).
  - unfold nalloc_ok, not_alloc_pending in Hb. cbn [cfg_ms] in Hb.
    assert (Hout : ~ In (bv_unsigned (in_sysno (sys_input segs ms x8))) alloc_mark_sysnos).
    { rewrite in_sysno_sys_input_eq. intros Hin. apply alloc_no_b_true_iff in Hin.
      rewrite (Hb x8 Hx8) in Hin. discriminate Hin. }
    rewrite (alloc_budget_refused_b_outside _ model Hout) in Hgr. discriminate Hgr.
  - exact (Herr (budget_fault_syscall_sstep_error segs ms model x8 eff model' evs' Hh Hx8 Hspec Hh' Hmat)).
Qed.

Lemma rzb_star_not_refused : forall c T, rzb c T ->
  forall tr c', star segs c tr c' -> ~ budget_refused_at segs c'.
Proof.
  intros c T H;
  induction H as [c I evs nx T i0 Hnode Hrob Hb Hcont IH | c Hh | c T T' H IH Heq];
  intros tr c' Hstar.
  - destruct (star_cases _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + exact (node_not_refused c I evs nx Hnode Hb).
    + destruct (proj2 Hnode e (SNext c2) (rzb_sstep_lift c e (SNext c2) Hb Hss))
        as (i & _ & Heq2).
      injection Heq2 as ->. exact (IH i tr2 c' Hstar2).
  - destruct (star_cases _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + intros [Hn _]. exact (Hh Hn).
    + exfalso. exact (Hh (sstep_halted_none segs c e _ Hss)).
  - exact (IH tr c' Hstar).
Qed.

(** No configuration the unfiltered run reaches from an [rzb] configuration is
    budget-refused. *)
Theorem rzb_never_refused : forall c T, rzb c T -> ~ reaches_budget_refused segs c.
Proof.
  intros c T H (tr & c' & Hstar & Hb). exact (rzb_star_not_refused c T H tr c' Hstar Hb).
Qed.

(** ...and so under every spurious-failure configuration
    ([Run.reaches_budget_refused_cfg_sub]). *)
Theorem rzb_never_refused_cfg : forall cfg c T, rzb c T ->
  ~ reaches_budget_refused_cfg segs cfg c.
Proof.
  intros cfg c T H Hr. exact (rzb_never_refused c T H (reaches_budget_refused_cfg_sub segs cfg c Hr)).
Qed.

(** ** ShapeAlg's node lemmas over [rzb] *)

Lemma rzb_nonempty : forall c T, rzb c T -> T [].
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hrob Hb Hcont IH | c Hh | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

Lemma rzb_silent1 : forall c c' T,
  node_ok segs c unit (fun _ => []) (fun _ => c') ->
  RomBase.sys_rob segs c ->
  nalloc_ok c ->
  rzb c' T ->
  rzb c T.
Proof.
  intros c c' T Hnode Hrob Hb Hc.
  apply (rzb_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (rzb_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode Hrob Hb).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply rzb_nonempty; exact Hc ].
Qed.

Lemma rzb_emit1 : forall c c' e T,
  node_ok segs c unit (fun _ => e) (fun _ => c') ->
  RomBase.sys_rob segs c ->
  nalloc_ok c ->
  rzb c' T ->
  rzb c (t_emit e T).
Proof.
  intros c c' e T Hnode Hrob Hb Hc.
  apply (rzb_conseq c (t_alt (fun _ : unit => t_emit e T))).
  - apply (rzb_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode Hrob Hb).
    intros []; exact Hc.
  - apply t_alt_unit.
Qed.

Lemma rzb_step : forall ms model ms' T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  rzb (mkCfg ms' model) T ->
  rzb (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  eapply rzb_silent1;
    [ apply node_instr; eassumption
    | apply RomBase.sys_rob_instr; cbn [cfg_ms]; exact Hsvc
    | apply nalloc_ok_instr; exact Hsvc | exact Hc].
Qed.

Lemma rzb_msteps : forall ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  rzb (mkCfg ms' model) T ->
  rzb (mkCfg ms model) T.
Proof.
  intros ms ms' model T Hh Hlazy Hms;
    induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
    intro Hc; [exact Hc|].
  eapply rzb_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
                   | apply IH; exact Hc].
Qed.

Lemma rzb_exit : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  rzb (mkCfg ms model)
      (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros ms model x8 Hh Hsvc Hx8.
  set (code := bv_and (ms_gpr ms 0) (Z_to_bv 64 255)).
  unfold t_exit.
  eapply (rzb_emit1 (mkCfg ms model) (mkCfg ms (with_halted code model))).
  - apply node_ok_of_u.
    { apply (kit_pending_on_sysno segs ms model x8 (bv_unsigned x8) Hsvc eq_refl).
      destruct Hx8 as [E | E]; rewrite E; reflexivity. }
    split.
    + intros []. cbn.
      replace [ExitEv code (m_fs model)]
        with ([] ++ [ExitEv code (m_fs (with_halted code model))]) by reflexivity.
      apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted code model) [] code);
        [exact Hh | exact Hsvc
         | apply (exit_dispatch_ok (sys_input segs ms x8) model);
           rewrite in_sysno_sys_input; exact Hx8
         | reflexivity
         | apply m_killed_with_halted ].
    + intros e st Hss.
      destruct (sstep_exit_inv segs ms model x8 e st Hh Hsvc Hx8 Hss) as [-> ->].
      exists tt. split; reflexivity.
  - destruct Hx8 as [Hx8' | Hx8'];
      (eapply (RomBase.sys_rob_memfree segs); [exact Hsvc | rewrite Hx8'; first [exact RomBase.memfree_93 | exact RomBase.memfree_94]]).
  - exact (nalloc_ok_exit ms model x8 Hsvc Hx8).
  - apply rzb_halt. cbn. discriminate.
Qed.

End WithSegs.

(** ** The walk over the binary's own segments, lifted to the run

    LPS 08b1429: [Run.run_scfg_budget_refused] reads the run against
    [run_segments segs inp sp mbase] -- the binary's segments with the run's vDSO
    appended -- and from the start configuration over that list.  A walk is built
    over the binary's own segments, so it has to be lifted, exactly as
    [Common.Cfg.RomStable.run_init] lifts a [ShapeAlg.realizes] walk.  These are
    that file's three theorems over [rzb]; every node-level step is RomStable's
    own, and the only new part is that [nalloc_ok] -- which reads
    [ms_svc_pending] alone -- is untouched by a change of the read-only
    backing. *)

Lemma nalloc_ok_cwrom : forall c r, nalloc_ok c -> nalloc_ok (RomBase.cwrom c r).
Proof. intros [ms model] r H. exact H. Qed.

Section RzbWrom.
  Variable segs : list Segment.
  Hypothesis Hvi : vdso_image segs = None.

  Theorem rzb_wrom : forall c T, rzb segs c T ->
    forall r, RomBase.rom_ext (ms_rom (cfg_ms c)) r -> rzb segs (RomBase.cwrom c r) T.
  Proof.
    intros c T H;
    induction H as [c I evs nx T i0 Hn Hrob Hb Hc IH | c Hh | c T T' H IH Heq];
    intros r Hr.
    - apply (rzb_node segs (RomBase.cwrom c r) I evs (fun i => RomBase.cwrom (nx i) r) T i0).
      + eapply RomStable.node_wrom; eassumption.
      + eapply RomStable.sys_rob_wrom; eassumption.
      + apply nalloc_ok_cwrom; exact Hb.
      + intros i. apply IH.
        match goal with |- RomBase.rom_ext ?x _ => replace x with (ms_rom (cfg_ms c)) end;
          [exact Hr|].
        symmetry. eapply RomStable.node_rom; eassumption.
    - apply rzb_halt. exact Hh.
    - eapply rzb_conseq; [apply IH; exact Hr | exact Heq].
  Qed.
End RzbWrom.

Section RzbAppTail.
  Variables segs tail : list Segment.
  Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
  Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.
  Hypothesis Hvi : vdso_image segs = None.

  Theorem rzb_app_tail : forall c T, rzb segs c T -> rzb (segs ++ tail) c T.
  Proof.
    intros c T H;
    induction H as [c I evs nx T i0 Hn Hrob Hb Hc IH | c Hh | c T T' H IH Heq].
    - apply (rzb_node (segs ++ tail) c I evs nx T i0).
      + eapply RomStable.node_ok_app_tail; eassumption.
      + eapply RomStable.sys_rob_app_tail; eassumption.
      + exact Hb.
      + exact IH.
    - apply rzb_halt. exact Hh.
    - eapply rzb_conseq; [exact IH | exact Heq].
  Qed.
End RzbAppTail.

Theorem rzb_run_segments : forall segs inp (sp mb : word) c T,
  vdso_image segs = None ->
  rzb segs c T -> rzb (run_segments segs inp sp mb) c T.
Proof.
  intros segs inp sp mb c T Hvi H. unfold run_segments.
  apply (rzb_app_tail segs _
           (fun s Hs => RomStable.vdso_segments_nx _ _ _ s Hs)
           (fun s Hs => RomStable.vdso_segments_nw _ _ _ s Hs) Hvi).
  exact H.
Qed.

(** The supplier-walk bridge over [rzb]: a walk over the binary's own segments, from the
    binary's start, is a walk of the run's start over the run's segment list. *)
Theorem rzb_run_init : forall segs inp (sp mb : word) pc ph brk rnd lim T,
  vdso_image segs = None ->
  rzb segs (init_config segs pc ph sp brk mb rnd lim inp) T ->
  rzb (run_segments segs inp sp mb)
    (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp) T.
Proof.
  intros segs inp sp mb pc ph brk rnd lim T Hvi H.
  rewrite RomStable.init_config_run_segments.
  apply rzb_run_segments; [exact Hvi|].
  apply (rzb_wrom segs Hvi); [exact H|].
  rewrite RomStable.init_config_rom. apply RomStable.rom_ext_run_segments.
Qed.
