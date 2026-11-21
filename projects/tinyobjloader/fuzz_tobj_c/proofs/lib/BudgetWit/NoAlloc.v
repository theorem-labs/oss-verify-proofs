(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Fw3/SymCall.v (ok_pframe, ok_pframeJ, ok_pframeJ_of_tcons) and Fw3/SymExit.v (ok_frame_tgt_K, ok_pframe_tgt_K, ok_halted_tgt): the syscall-frame obligation asked only at a non-allocation call number, and the world predicate okB that adds the budget premise to the released target obligation. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (sstep_acfg_of_na covers the step relation's three vDSO cases, and instr_unmodeled's premise that the pc is no vDSO entry; okB_never_refused_run, the budget premise over the run's segment list and the run's start, where Run.run_budget_refused reads the binary, LPS 75d69e00, from okB and the read-only backing's robustness RunSeg.rob_reach). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymCall SymExit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import RomBase RunSeg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(** * The budget premise as a world predicate of the Fw safety framework

    The released walk of the plain build ([P/Top.v top_sound_P]) proves
    [safe segsP okT n (w0 c0)] for the target obligation [okT := ok_tgt segsP Spec],
    with every world predicate [ok] that meets three frame obligations
    ([ok_frame], [ok_pframe], [ok_halted]).  Those obligations are what the walk asks
    of [ok] at an instruction step, at a pending system call and at a halted process.

    The budget premise [~ run_scfg_budget_refused] says that no configuration the
    filtered run reaches is [budget_refused_at].  [okB] is [okT] together with two
    facts at each world: no budget refusal there, and a pending system call of a
    running process there is not an allocation call (brk 214, mremap 216, mmap 222,
    mprotect 226; [pending_na]).  At an instruction step and at a halted process both
    hold for every world ([okB_frame], [okB_halted]): a refusal is marked only at a
    pending system call of a running process, and the frame gives [m_vm_lazy = []].
    At a pending system call they hold when the call number is not an allocation
    call: then [alloc_budget_refused_b] is [false]
    ([Run.alloc_budget_refused_b_outside]), and [only_ok] leaves no lazy mapping
    behind ([okB_pframe]).  They do not hold at every pending call, so the released
    [ok_pframe], which asks for [ok] at every call number, is restated here as
    [ok_pframe_na], which asks for it only at a call number outside
    [alloc_mark_sysnos]; each syscall site of the copied walk discharges that from
    the number it pins (BudgetWit.SysNA, BudgetWit.StartB).

    The framework's step is the filtered [sstep_a = sstep_cfg segs ACFG]
    ([ACFG = Run.alloc_only_cfg false = Env.alloc_forced_only]), while the budget
    premise of an arbitrary configuration is implied by the one of the unfiltered
    run ([Run.run_scfg_budget_refused_sub]).  [pending_na] closes that gap: at a
    configuration whose pending call is not an allocation call no outcome is a
    spurious refusal ([Refusable.ns_not_alloc]), so every unfiltered step from it is
    an [ACFG] step ([sstep_acfg_of_na]), and the unfiltered run reaches only the
    configurations the filtered one does ([star_acfg_of_na], [okB_never_refused]). *)

Section WithSegs.
Variable segs : list Segment.

(** [SymCall.ok_pframe] and [SymCall.ok_pframeJ] with one premise more: the pending
    call number is not an allocation call. *)
Definition ok_pframe_na (ok : world -> Prop) (K : list event -> Model -> Prop) : Prop :=
  forall tr ms md x8, K tr md -> ms_svc_pending ms = Some x8 ->
    ~ In (bv_unsigned x8) alloc_mark_sysnos ->
    only_ok (sys_input segs ms x8) md -> ok (tr, mkCfg ms md).

Definition ok_pframeJ_na (ok : world -> Prop) (J : jpred) : Prop :=
  forall rho tr ms md x8, J rho tr md -> ms_svc_pending ms = Some x8 ->
    ~ In (bv_unsigned x8) alloc_mark_sysnos ->
    only_ok (sys_input segs ms x8) md -> ok (tr, mkCfg ms md).

Lemma ok_pframeJ_na_of_tcons : forall (ok : world -> Prop) (Spec : list event -> Prop) (J : jpred),
  ok_pframe_na ok (fun tr _ => tcons Spec tr) ->
  (forall rho tr md, J rho tr md -> tcons Spec tr) ->
  ok_pframeJ_na ok J.
Proof using . intros ok Spec J Hok HJ rho tr ms md x8 Hj. apply Hok. eapply HJ; eauto. Qed.

(** A call number pinned to a literal that is not on the list. *)
Lemma na_of : forall (x8 : bv 64) (n : Z), bv_unsigned x8 = n ->
  existsb (Z.eqb n) alloc_mark_sysnos = false -> ~ In (bv_unsigned x8) alloc_mark_sysnos.
Proof using .
  intros x8 n Hn Hb Hin. rewrite Hn in Hin.
  assert (E : existsb (Z.eqb n) alloc_mark_sysnos = true)
    by (apply existsb_exists; exists n; split; [exact Hin | apply Z.eqb_refl]).
  congruence.
Qed.

(** exit (93) or exit_group (94). *)
Lemma na_exit : forall (x8 : bv 64), bv_unsigned x8 = 93 \/ bv_unsigned x8 = 94 ->
  ~ In (bv_unsigned x8) alloc_mark_sysnos.
Proof using .
  intros x8 [H | H]; [exact (na_of x8 93 H eq_refl) | exact (na_of x8 94 H eq_refl)].
Qed.

(** A pending system call of a running process is not an allocation call. *)
Definition pending_na (c : config) : Prop :=
  forall x8, m_halted (cfg_model c) = None -> ms_svc_pending (cfg_ms c) = Some x8 ->
    ~ In (bv_unsigned x8) alloc_mark_sysnos.

(** The released target obligation, no budget refusal and [pending_na] at the world's
    configuration. *)
Definition okB (Spec : list event -> Prop) (w : world) : Prop :=
  ok_tgt segs Spec w /\ ~ budget_refused_at segs (w_cfg w) /\ pending_na (w_cfg w).

Lemma okB_frame : forall Spec K, K_tcons Spec K -> ok_frame segs (okB Spec) K.
Proof using .
  intros Spec K HK tr ms md ms' Hk Hidle Hp Hs. split; [| split].
  - exact (@ok_frame_tgt_K segs Spec K HK tr ms md ms' Hk Hidle Hp Hs).
  - exact (budget_refused_at_no_lazy_instr segs ms md (proj2 Hidle) Hp).
  - intros x8 _ Hx. cbn [w_cfg snd cfg_ms] in Hx. congruence.
Qed.

Lemma okB_pframe : forall Spec K, K_tcons Spec K -> ok_pframe_na (okB Spec) K.
Proof using .
  intros Spec K HK tr ms md x8 Hk Hp Hna Hok. split; [| split].
  - exact (@ok_tgt_pending segs Spec tr ms md x8 (HK tr md Hk) Hp Hok).
  - change (~ budget_refused_at segs (mkCfg ms md)).
    pose proof (alloc_budget_refused_b_outside (sys_input segs ms x8) md Hna) as Hout.
    destruct Hok as [_ Hlz].
    intros (_ & [(Hn & _) | (y8 & Hy & [Hb | (eff & m' & evs & Hsp & Hh' & Hmat)])]);
      cbn [cfg_ms cfg_model] in *.
    + congruence.
    + rewrite Hp in Hy. injection Hy as <-. congruence.
    + rewrite Hp in Hy. injection Hy as <-.
      rewrite (materialize_model_accesses_no_lazy m' _ (Hlz eff m' evs Hsp Hh')) in Hmat.
      discriminate Hmat.
  - intros y8 _ Hy. cbn [w_cfg snd cfg_ms] in Hy. rewrite Hp in Hy. injection Hy as <-. exact Hna.
Qed.

Lemma okB_halted : forall Spec, ok_halted (okB Spec) Spec.
Proof using .
  intros Spec tr ms md code Ht Hh. split; [| split].
  - exact (@ok_halted_tgt segs Spec tr ms md code Ht Hh).
  - change (~ budget_refused_at segs (mkCfg ms md)).
    intros (Hn & _). cbn [cfg_model] in Hn. congruence.
  - intros x8 Hn _. cbn [w_cfg snd cfg_model] in Hn. congruence.
Qed.

(** From a configuration whose pending call is not an allocation call, every
    unfiltered step is a step of the framework's filtered relation. *)
Lemma sstep_acfg_of_na : forall c evs r, pending_na c -> sstep segs c evs r -> sstep_a segs c evs r.
Proof using .
  intros c evs r Hna H. unfold sstep_a.
  (* LPS 727298f3: [sstep] has eleven constructors; the three vDSO arms (slots 4-6) have no
     pending call, and [sstep_cfg] mirrors them with no filter premise; [instr_unmodeled] now
     also says the pc is no vDSO entry ([Hv]). *)
  destruct H as [ms md ms' md' Hh Hp Hs | ms md Hh Hp Hs | ms md Hh Hp Hs Hv
                | ms md fn n eff md' md'' e0 Hh Hp Hs Hf Hn Hsp Hef Hh' Hm
                | ms md fn n eff md' e0 Hh Hp Hs Hf Hn Hsp Hef Hh' Hm
                | ms md fn Hh Hp Hs Hf Hu
                | ms md x8 eff md' md'' e0 Hh Hp Hs Hh' Hm
                | ms md x8 eff md' e0 Hh Hp Hs Hh' Hm
                | ms md x8 eff md' e0 code Hh Hp Hs Hh' Hk
                | ms md x8 eff md' e0 sig Hh Hp Hs Hk
                | ms md x8 Hh Hp Hs].
  - eapply sstep_cfg_instr; eassumption.
  - eapply sstep_cfg_instr_fault; eassumption.
  - eapply sstep_cfg_instr_unmodeled; eassumption.
  - eapply sstep_cfg_vdso_call; eassumption.
  - eapply sstep_cfg_vdso_materialization_fault; eassumption.
  - eapply sstep_cfg_vdso_unmodeled; eassumption.
  - eapply sstep_cfg_syscall; [exact Hh | exact Hp | exact Hs | | exact Hh' | exact Hm].
    apply ns_not_alloc. exact (Hna x8 Hh Hp).
  - eapply sstep_cfg_syscall_materialization_fault; [exact Hh | exact Hp | exact Hs | | exact Hh' | exact Hm].
    apply ns_not_alloc. exact (Hna x8 Hh Hp).
  - eapply sstep_cfg_exit; eassumption.
  - eapply sstep_cfg_killed; eassumption.
  - eapply sstep_cfg_syscall_unmodeled; eassumption.
Qed.

(** An unfiltered run from [c] whose every filtered-reachable configuration has
    [pending_na] is a filtered run. *)
Lemma star_acfg_of_na : forall c tr c',
  star segs c tr c' ->
  (forall tr0 c0, star_a segs c tr0 c0 -> pending_na c0) ->
  star_a segs c tr c'.
Proof using .
  intros c tr c' H. induction H as [c | c1 ev c2 tr1 c3 Hs Hst IH]; intros Hinv.
  - apply star_cfg_refl.
  - assert (Hs' : sstep_a segs c1 ev (SNext c2)).
    { apply sstep_acfg_of_na; [apply (Hinv []); apply star_cfg_refl | exact Hs]. }
    eapply star_cfg_step; [exact Hs' |]. apply IH.
    intros tr0 c0 H0. apply (Hinv (ev ++ tr0)). eapply star_cfg_step; [exact Hs' | exact H0].
Qed.

(** A run that is [safe] for [okB] reaches no budget-refused configuration, under the
    unfiltered step and so under every configuration ([Run.run_scfg_budget_refused_sub]). *)
Lemma okB_never_refused : forall (c0 : config) (Spec : list event -> Prop),
  (forall n, safe segs (okB Spec) n (w0 c0)) -> ~ reaches_budget_refused segs c0.
Proof using .
  intros c0 Spec Hs (tr & c & Hst & Hb).
  assert (Hinv : forall tr0 c1, star_a segs c0 tr0 c1 -> okB Spec ([] ++ tr0, c1)).
  { intros tr0 c1 H.
    exact (@safe_reachable_ok segs (okB Spec) (w0 c0) ([] ++ tr0, c1) Hs (@star_wsteps segs c0 tr0 c1 [] H)). }
  pose proof (star_acfg_of_na c0 tr c Hst (fun tr0 c1 H => proj2 (proj2 (Hinv tr0 c1 H)))) as Hst'.
  destruct (Hinv tr c Hst') as (_ & Hn & _).
  exact (Hn Hb).
Qed.

End WithSegs.

(** LPS 75d69e00: the budget premise reads the run over [run_segments segs inp sp mb] from
    [init_config (run_segments ..) ..] ([Run.run_budget_refused]).  A run safe for [okB] whose
    read-only backing is robust at every configuration it reaches ([RunSeg.rob_reach]) reaches
    no budget-refused configuration there either.  Every configuration the run's list reaches
    by the framework's step is one the binary reaches over its own segments, at the larger
    backing ([RunSeg.star_app_back], [RunSeg.star_wrom_back]), so it has [pending_na] and the
    unfiltered run is the framework's ([star_acfg_of_na]).  At the configuration reached, an
    instruction neither faults nor is unmodeled over the binary's own list, so neither over
    the run's; a pending call is no allocation call, and its outcomes are the binary's own
    ([RomBase.sys_rob]), of which [okB] says none is refused. *)
Lemma okB_never_refused_run : forall segs inp (sp brk mb : word) pc ph rnd lim (Spec : list event -> Prop),
  vdso_image segs = None ->
  rob_reach segs (init_config segs pc ph sp brk mb rnd lim inp) ->
  (forall n, safe segs (okB segs Spec) n (w0 (init_config segs pc ph sp brk mb rnd lim inp))) ->
  ~ reaches_budget_refused (run_segments segs inp sp mb)
      (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp).
Proof.
  intros segs inp sp brk mb pc ph rnd lim Spec Hvi Hrob Hs.
  assert (Hr : rom_ext (ms_rom (cfg_ms (init_config segs pc ph sp brk mb rnd lim inp)))
                       (seg_rom1 (run_segments segs inp sp mb)))
    by (rewrite init_config_rom; apply rom_ext_run_segments).
  rewrite init_config_run_segments.
  remember (init_config segs pc ph sp brk mb rnd lim inp) as c0 eqn:Ec0.
  remember (seg_rom1 (run_segments segs inp sp mb)) as r eqn:Er.
  assert (Hinv : forall tr c, star_a segs c0 tr c -> okB segs Spec ([] ++ tr, c)).
  { intros tr c H.
    exact (@safe_reachable_ok segs (okB segs Spec) (w0 c0) ([] ++ tr, c) Hs (@star_wsteps segs c0 tr c [] H)). }
  assert (Hne : ~ reaches_error_cfg segs ACFG c0).
  { intros (tr & c & evs & Hst & He).
    destruct (Hinv tr c Hst) as ((_ & Hn) & _). exact (Hn evs (sstep_cfg_sub _ _ _ _ _ He)). }
  assert (Hne2 : ~ reaches_error_cfg segs ACFG (cwrom c0 r)).
  { intros Hc. apply Hne. apply reaches_error_wrom_back with (r := r);
      first [exact Hvi | exact Hrob | exact Hr | exact Hc]. }
  assert (Hback : forall tr d, star_a (run_segments segs inp sp mb) (cwrom c0 r) tr d ->
                    exists c', d = cwrom c' r /\ star_a segs c0 tr c').
  { intros tr d H. unfold star_a, run_segments in H.
    assert (H' : star_cfg segs ACFG (cwrom c0 r) tr d).
    { apply star_app_back with (tail := vdso_segments (in_kernel inp) sp mb);
        try exact Hvi; try exact Hne2; try exact H;
        intros s Hs0; first [exact (vdso_segments_nx _ _ _ s Hs0) | exact (vdso_segments_nw _ _ _ s Hs0)]. }
    destruct (star_wrom_back segs ACFG Hvi r (cwrom c0 r) tr d H' c0 eq_refl Hrob Hr) as (c' & Hd & Hc').
    exists c'. split; [exact Hd | exact Hc']. }
  intros (tr & d & Hst & Hb).
  (* the unfiltered run is the framework's: no configuration it reaches has a pending allocation call *)
  assert (Hst' : star_a (run_segments segs inp sp mb) (cwrom c0 r) tr d).
  { apply (star_acfg_of_na (run_segments segs inp sp mb)); [exact Hst|].
    intros tr0 d0 H0. destruct (Hback tr0 d0 H0) as (c' & -> & H0').
    destruct (Hinv tr0 c' H0') as (_ & _ & Hna). exact Hna. }
  destruct (Hback tr d Hst') as (c' & -> & Hc').
  destruct (Hinv tr c' Hc') as ((_ & Hnoerr) & Hnb & Hna).
  cbn [w_cfg snd] in Hnoerr, Hnb, Hna.
  destruct c' as [ms md].
  destruct Hb as (Hh & [(Hsvc & Hins) | (x8 & Hx8 & Hsys)]);
    change (m_halted md = None) in Hh.
  - (* an instruction: it neither faults nor is unmodeled over the binary's own list, so its
       accesses over the run's list are the same and materialize *)
    change (ms_svc_pending ms = None) in Hsvc.
    destruct (mi_account_step segs ms md) as [[ms1 md1]| |] eqn:Em.
    + assert (Ep : mi_account_step (run_segments segs inp sp mb) ms md = MachineOk (ms1, md1)).
      { unfold run_segments. apply mi_account_step_app_nx; try exact Em;
          intros s Hs0; first [exact (vdso_segments_nx _ _ _ s Hs0) | exact (vdso_segments_nw _ _ _ s Hs0)]. }
      assert (Ew : mi_account_step (run_segments segs inp sp mb) (wrom ms r) md = MachineOk (wrom ms1 r, md1))
        by (rewrite mi_account_step_wrom, Ep; reflexivity).
      cbn [cwrom cfg_ms cfg_model] in Hins.
      destruct Hins as [(rep & Hrep & Hmat) | (Hun & _)].
      * assert (Ef : mi_account_step (run_segments segs inp sp mb) (wrom ms r) md = MachineFault)
          by (unfold mi_account_step; rewrite Hrep; cbv beta iota; rewrite Hmat; reflexivity).
        rewrite Ew in Ef. discriminate Ef.
      * rewrite Ew in Hun. discriminate Hun.
    + exfalso. apply (Hnoerr []). apply sstep_instr_fault; assumption.
    + exfalso. apply (Hnoerr []). apply sstep_instr_unmodeled; try assumption.
      unfold vdso_entry_fn. rewrite Hvi. reflexivity.
  - (* a pending call: no allocation call, and the binary's own outcomes *)
    cbn [cwrom cfg_ms cfg_model] in Hx8, Hsys.
    change (ms_svc_pending ms = Some x8) in Hx8.
    assert (Hnot : ~ In (bv_unsigned x8) alloc_mark_sysnos) by exact (Hna x8 Hh Hx8).
    destruct Hsys as [Hal | (eff & m' & evs & Hspec & Hh' & Hmat)].
    + pose proof (alloc_budget_refused_b_outside (sys_input (run_segments segs inp sp mb) (wrom ms r) x8) md Hnot) as Hout.
      congruence.
    + apply Hnb. split; [exact Hh|]. right. exists x8. split; [exact Hx8|]. right.
      exists eff, m', evs. split; [|split; [exact Hh' | exact Hmat]].
      assert (Ei : sys_input (run_segments segs inp sp mb) (wrom ms r) x8 = sys_input segs (wrom ms r) x8).
      { unfold run_segments. apply sys_input_app_nw;
          intros s Hs0; first [exact (vdso_segments_nx _ _ _ s Hs0) | exact (vdso_segments_nw _ _ _ s Hs0)]. }
      rewrite Ei in Hspec.
      pose proof (star_cfg_rom segs ACFG Hvi c0 tr (mkCfg ms md) Hc') as Erom. cbn [cfg_ms] in Erom.
      assert (Hr' : rom_ext (ms_rom ms) r) by (rewrite Erom; exact Hr).
      exact (proj1 (Hrob tr (mkCfg ms md) Hc' Hh r x8 Hr' Hx8 _) Hspec).
Qed.
