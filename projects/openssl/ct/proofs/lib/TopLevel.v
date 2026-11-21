(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3; internal commit ids in comments replaced by public commits or removed. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
(* The tree-local [Lib] import MUST come last.  [Lib/ITree.v:95] defines
   [Fixpoint impl {R} (t : itree R) (Q : ...) (ms : machine_state)], which
   section-discharges to the [impl segs at_node t Q ms] this file and
   [Spec/Monad.v:52] call; re-importing the LinuxProcessSem modules AFTER
   it shadows that with a [Prop -> Prop -> Prop] [impl], and [tree_ok]'s
   [impl segs ...] then reports [segs] "expected to have type Prop"
   (TopLevel.v:136).  [Vdso] is folded into
   this line, which is the donor's single LinuxProcessSem line
   (projects/openssl/bignum/proofs/lib/TopLevel.v:8); the
   duplicate that used to sit after [Lib] carried nothing else. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv FP.
From OSSVerify.Proofs.openssl.ct.lib.Common Require Import RsLift.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition prog_tree (R : Type) : Type := ProcInput -> ExecEntry -> itree node R.

(* [comment removed for export] *)
Definition ms0 (segs : list Segment) (pc : N) (ph : PhdrInfo)
    (en : ExecEntry) (inp : ProcInput) : machine_state :=
  init_ms segs pc ph (en_sp en) (en_mmap_base en) (en_draw en) inp.

Lemma ms0_eq : forall segs pc ph en inp,
  ms0 segs pc ph en inp =
  MS (mkR_init (en_sp en)) bvmap_empty (Z_to_bv 64 (Z.of_N pc)) (Z_to_bv 32 0) None
     (wrap_mem inp (en_mmap_base en) ph (Z_to_bv 64 (Z.of_N pc)) (en_sp en) (en_draw en)) (seg_rom segs).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition mo0 (segs : list Segment) (lim : Z) (en : ExecEntry) (inp : ProcInput) : Model :=
  with_vdso (vdso_run_init (ed_vdso (en_draw en)))
    (init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp).

(* The bare-[segs] [init_config_eq] the old shape carried is gone: at the
   revision [Run.init_machine_state] (75d69e00 theories/LinuxProcessSem/Run.v:1384,
   discharged out of [Section WithMemImage] at Run.v:339 into
   [init_machine_state segs pc ph sp mbase draw inp]) takes the mmap base
   where the old shape passed the draw, and the run's configuration is
   [init_config_run] below, over [Run.run_segments].  It had no consumer in
   this tree and the donor does not carry it (the donor's
   projects/openssl/bignum/proofs/lib/TopLevel.v:30-46). *)
Lemma m_fds_mo0 : forall segs lim en inp,
  m_fds (mo0 segs lim en inp)
  = m_fds (init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp).
Proof. reflexivity. Qed.

Lemma m_fs_mo0 : forall segs lim en inp,
  m_fs (mo0 segs lim en inp)
  = m_fs (init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp).
Proof. reflexivity. Qed.

Lemma init_config_run : forall segs pc ph lim en inp,
  init_config (run_segments segs inp (en_sp en) (en_mmap_base en)) pc ph
    (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp
  = mkCfg (init_machine_state (run_segments segs inp (en_sp en) (en_mmap_base en)) pc ph
             (en_sp en) (en_mmap_base en) (en_draw en) inp)
          (mo0 segs lim en inp).
Proof.
  intros segs pc ph lim en inp. unfold init_config, mo0.
  rewrite segments_reserved_run_segments. reflexivity.
Qed.

Lemma mo0_alloc_top : forall segs lim en inp,
  alloc_top (m_vmmaps (mo0 segs lim en inp)) = (bv_unsigned (en_sp en) - stack_max_size)%Z.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mo0_alloc_top_ceiling : forall segs pc ph lim en inp,
  in_va_size inp = Sv48 ->
  valid_entry (mkImage segs pc ph) en inp ->
  alloc_top (m_vmmaps (mo0 segs lim en inp)) = @alloc_ceiling (ceiling_of_sp (bv_unsigned (en_sp en))).
Proof.
  intros segs pc ph lim en inp Hsv48 Hve. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hve.
  destruct en as [sp brk mb rnd]. destruct Hve as (Hsp & _ & _ & _). destruct Hsp as (H1 & H2 & H3).
  rewrite mo0_alloc_top. cbn [en_sp]. unfold sp_window_lo, sp_window_hi, stack_max_size in *.
  rewrite ceiling_of_sp_eq; [reflexivity| lia | exact H3].
Qed.

(* [comment removed for export] *)
Lemma vie_va_size : forall inp, valid_input_either inp -> in_va_size inp = Sv48.
Proof. intros inp Hv. red in Hv. repeat match goal with H : _ /\ _ |- _ => destruct H end. assumption. Qed.

(* [comment removed for export] *)
Lemma vie_reader : forall inp, valid_input_either inp -> in_channel_reader inp = true.
Proof. intros inp Hv. red in Hv. repeat match goal with H : _ /\ _ |- _ => destruct H end. assumption. Qed.

Lemma vie_launch : forall inp, valid_input_either inp -> valid_launch inp.
Proof. intros inp Hv. red in Hv. repeat match goal with H : _ /\ _ |- _ => destruct H end. assumption. Qed.  (* [comment removed for export] *)

Lemma mo0_not_halted : forall segs lim en inp, m_halted (mo0 segs lim en inp) = None.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma vie_fs_keys : forall inp, valid_input_either inp -> fs_keys_relative (in_image_fs inp).
Proof. intros inp (_ & _ & _ & v & _). exact v. Qed.

Lemma vi_fs_keys : forall inp, valid_input inp -> fs_keys_relative (in_image_fs inp).
Proof. intros inp (_ & _ & _ & v & _). exact v. Qed.

(* [minv_init] at this revision carries TWO premises (Lib/Nodes.v:566-568:
   [fs_keys_relative (in_image_fs inp) -> in_channel_reader inp = true]), so
   discharge both explicitly, as the donor does
   (projects/openssl/bignum/proofs/lib/TopLevel.v:88-92). *)
Lemma mo0_minv : forall segs lim en inp, valid_input_either inp -> minv (mo0 segs lim en inp).
Proof.
  intros segs lim en inp Hvi.
  exact (minv_init (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp
           (vie_fs_keys inp Hvi) (vie_reader inp Hvi)).
Qed.

Lemma ms0_svc : forall segs pc ph en inp, ms_svc_pending (ms0 segs pc ph en inp) = None.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Remark frm0_init : frm0 (Z_to_bv 32 0).
Proof. reflexivity. Qed.

Lemma ms0_frm0 : forall segs pc ph en inp, frm0 (ms_fcsr (ms0 segs pc ph en inp)).
Proof. intros. exact frm0_init. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition tree_ok {R : Type} (segs : list Segment) (pc : N) (ph : PhdrInfo) (lim : Z)
    (t : prog_tree R) (Q : R -> machine_state -> Prop) : Prop :=
  forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
    impl segs (at_node segs) (t inp en) Q (ms0 segs pc ph en inp)
    /\ leaves_unreachable_m nstep (t inp en) (mo0 segs lim en inp)
    /\ tsafe nstep nsafe (t inp en) (mo0 segs lim en inp).

(* [comment removed for export] *)
Definition tree_traces {R : Type} (t : itree node R) (mo : Model) : list event -> Prop :=
  fun tr => exists full, ttrace nstep nexit t mo full /\ is_prefix tr full.

(* [comment removed for export] *)
Definition trees_equiv {RS RT : Type} (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
    (segsT : list Segment) (pcT : N) (phT : PhdrInfo) (tS : prog_tree RS) (tT : prog_tree RT) : Prop :=
  forall enS enT inp,
    valid_entry (mkImage segsS pcS phS) enS inp ->
    valid_entry (mkImage segsT pcT phT) enT inp ->
    valid_input_either inp ->
    trace_equiv (tree_traces (tS inp enS) (mo0 segsS source_alloc_limit enS inp))
                (tree_traces (tT inp enT) (mo0 segsT target_alloc_limit enT inp)).

(* [comment removed for export] *)
Lemma trees_equiv_of_ttrace : forall {RS RT : Type} (tS : itree node RS) (tT : itree node RT) moS moT,
  (forall tr, ttrace nstep nexit tS moS tr <-> ttrace nstep nexit tT moT tr) ->
  trace_equiv (tree_traces tS moS) (tree_traces tT moT).
Proof.
  intros RS RT tS tT moS moT H tr. unfold tree_traces.
  split; intros (full & Hf & Hp); exists full; split; auto; apply H; exact Hf.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma run_eq : forall segs pc ph lim en inp,
  run (mkImage segs pc ph) lim en inp =
  let vsegs := run_segments segs inp (en_sp en) (en_mmap_base en) in
  let c0 := mkCfg (init_machine_state vsegs pc ph (en_sp en) (en_mmap_base en) (en_draw en) inp) (mo0 segs lim en inp) in
  {| bh_traces := obs_trace vsegs c0;
     bh_errors := reaches_error vsegs c0;
     bh_all_errors := all_traces_error vsegs c0;
     bh_unmodeled := reaches_unmodeled vsegs c0 |}.
Proof.
  (* The rewrite must fire BEFORE the entry record is destructed: at the
     revision [init_config]'s machine state reads [run_segments segs inp
     (en_sp en) (en_mmap_base en)], and a [cbn] that reduces those
     projections first leaves no subterm matching [init_config_run]'s
     right-hand side.  Donor:
     projects/openssl/bignum/proofs/lib/TopLevel.v:138-146. *)
  intros segs pc ph lim en inp. cbv zeta.
  rewrite <- (init_config_run segs pc ph lim en inp).
  destruct en as [sp brk mb rnd]. cbn [run en_sp en_brk en_mmap_base en_draw]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma run_scfg_eq : forall cfg segs pc ph lim en inp,
  run_scfg cfg (mkImage segs pc ph) lim en inp =
  let vsegs := run_segments segs inp (en_sp en) (en_mmap_base en) in
  let c0 := mkCfg (init_machine_state vsegs pc ph (en_sp en) (en_mmap_base en) (en_draw en) inp) (mo0 segs lim en inp) in
  {| bh_traces := obs_trace_cfg vsegs cfg c0;
     bh_errors := reaches_error_cfg vsegs cfg c0;
     bh_all_errors := all_traces_error_cfg vsegs cfg c0;
     bh_unmodeled := reaches_unmodeled_cfg vsegs cfg c0 |}.
Proof.
  (* Same order as [run_eq]: rewrite under [cbv zeta] with [en] still a
     variable (projects/openssl/bignum/proofs/lib/TopLevel.v:157-161). *)
  intros cfg segs pc ph lim en inp. cbv zeta.
  rewrite <- (init_config_run segs pc ph lim en inp).
  destruct en as [sp brk mb rnd]. cbn [run_scfg en_sp en_brk en_mmap_base en_draw]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma run_of_tree : forall {R : Type} segs pc ph lim (t : itree node R) (Q : R -> machine_state -> Prop) en inp,
  impl segs (at_node segs) t Q (ms0 segs pc ph en inp) ->
  leaves_unreachable_m nstep t (mo0 segs lim en inp) ->
  tsafe nstep nsafe t (mo0 segs lim en inp) ->
  valid_input_either inp ->                                  (* [comment removed for export] *)
  trace_equiv (bh_traces (run_scfg ncfg (mkImage segs pc ph) lim en inp)) (tree_traces t (mo0 segs lim en inp))
  /\ ~ bh_errors (run_scfg ncfg (mkImage segs pc ph) lim en inp)
  /\ ~ bh_unmodeled (run_scfg ncfg (mkImage segs pc ph) lim en inp).
Proof.
  intros R segs pc ph lim t Q en inp Himpl Hleaves Hsafe Hvi.
  rewrite run_scfg_eq. cbv zeta. cbn [bh_traces bh_errors bh_unmodeled].
  (* The run reads [run_segments segs inp sp mbase] = segs ++ tail
     (75d69e00 theories/LinuxProcessSem/Run.v:328-330:
     [Definition run_segments segs inp sp mbase := segs ++ vdso_segments (in_kernel inp) sp mbase]).
     The walk is over segs; [RsLift.impl_rs_nodes] carries it to segs ++ tail
     at the state with the run's ROM, which is [ms0 (segs ++ tail)].
     Donor: projects/openssl/bignum/proofs/lib/TopLevel.v:170-200. *)
  set (tail := vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en)).
  pose proof (vdso_segments_inert (in_kernel inp) (en_sp en) (en_mmap_base en)) as Hin. fold tail in Hin.
  change (run_segments segs inp (en_sp en) (en_mmap_base en)) with (segs ++ tail).
  destruct (init_behaviour_scfg_eqv (segs ++ tail) ncfg pc ph (en_sp en) (en_mmap_base en) (en_draw en) inp (mo0 segs lim en inp))
    as (Htr & Herr & _ & Hunm).
  change (init_ms (segs ++ tail) pc ph (en_sp en) (en_mmap_base en) (en_draw en) inp)
    with (ms0 (segs ++ tail) pc ph en inp) in Htr, Herr, Hunm.
  pose proof (impl_rs_nodes segs tail Hin _ t Q (ms0 segs pc ph en inp) Himpl) as Himpl'.
  change (rs_ms segs tail (ms0 segs pc ph en inp)) with (ms0 (segs ++ tail) pc ph en inp) in Himpl'.
  pose proof (nodes_sound (segs ++ tail)) as NS.
  pose proof (mo0_minv segs lim en inp Hvi) as Hminv.
  split; [| split].
  - intros tr. rewrite (Htr tr). unfold tree_traces.
    apply (impl_run_traces2 node (segs ++ tail) ncfg (at_node (segs ++ tail)) nstep nexit minv nsafe NS t _ _ _
             Himpl' Hleaves (mo0_not_halted _ _ _ _) Hminv Hsafe (ms0_svc _ _ _ _ _)).
  - rewrite Herr.
    apply (impl_run_safe2 node (segs ++ tail) ncfg (at_node (segs ++ tail)) nstep nexit minv nsafe NS t _ _ _
             Himpl' Hleaves (mo0_not_halted _ _ _ _) Hminv Hsafe (ms0_svc _ _ _ _ _)).
  - rewrite Hunm.
    apply (impl_run_modeled2 node (segs ++ tail) ncfg (at_node (segs ++ tail)) nstep nexit minv nsafe NS t _ _ _
             Himpl' Hleaves (mo0_not_halted _ _ _ _) Hminv Hsafe (ms0_svc _ _ _ _ _)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma trace_equiv_sym : forall T1 T2, trace_equiv T1 T2 -> trace_equiv T2 T1.
Proof. intros T1 T2 H tr. symmetry. apply H. Qed.

Lemma trace_equiv_trans : forall T1 T2 T3, trace_equiv T1 T2 -> trace_equiv T2 T3 -> trace_equiv T1 T3.
Proof. intros T1 T2 T3 H1 H2 tr. rewrite (H1 tr). apply H2. Qed.

Theorem strong_universal_from_trees_gen :
  forall {RS RT : Type}
         (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo)
         (tS : prog_tree RS) (tT : prog_tree RT)
         (QS : RS -> machine_state -> Prop) (QT : RT -> machine_state -> Prop),
    tree_ok segsS pcS phS source_alloc_limit tS QS ->
    tree_ok segsT pcT phT target_alloc_limit tT QT ->
    trees_equiv segsS pcS phS segsT pcT phT tS tT ->
    strong_universal_T_scfg ncfg (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  intros RS RT segsS pcS phS segsT pcT phT tS tT QS QT HS HT HEQ enS enT inp HvS HvT Hvi. apply valid_input_either_of_valid_input in Hvi.
  destruct (HS enS inp HvS Hvi) as (HimplS & HleavesS & HsafeS).
  destruct (HT enT inp HvT Hvi) as (HimplT & HleavesT & HsafeT).
  destruct (run_of_tree segsS pcS phS source_alloc_limit (tS inp enS) QS enS inp HimplS HleavesS HsafeS Hvi)
    as (HtrS & _ & HmodS).
  destruct (run_of_tree segsT pcT phT target_alloc_limit (tT inp enT) QT enT inp HimplT HleavesT HsafeT Hvi)
    as (HtrT & HerrT & _).
  split.
  - (* [comment removed for export] *) exact HmodS.
  - (* [comment removed for export] *)
    right. split; [| exact HerrT].
    eapply trace_equiv_trans; [exact HtrS|].
    eapply trace_equiv_trans; [exact (HEQ enS enT inp HvS HvT Hvi)|].
    apply trace_equiv_sym. exact HtrT.
Qed.

(* [comment removed for export] *)
Theorem error_free_from_trees_gen :
  forall {RS RT : Type}
         (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo)
         (tS : prog_tree RS) (tT : prog_tree RT)
         (QS : RS -> machine_state -> Prop) (QT : RT -> machine_state -> Prop),
    tree_ok segsS pcS phS source_alloc_limit tS QS ->
    tree_ok segsT pcT phT target_alloc_limit tT QT ->
    trees_equiv segsS pcS phS segsT pcT phT tS tT ->
    strong_universal_error_free_T_scfg ncfg (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  intros RS RT segsS pcS phS segsT pcT phT tS tT QS QT HS HT HEQ enS enT inp HvS HvT Hvi. apply valid_input_either_of_valid_input in Hvi.
  destruct (HS enS inp HvS Hvi) as (HimplS & HleavesS & HsafeS).
  destruct (HT enT inp HvT Hvi) as (HimplT & HleavesT & HsafeT).
  destruct (run_of_tree segsS pcS phS source_alloc_limit (tS inp enS) QS enS inp HimplS HleavesS HsafeS Hvi)
    as (HtrS & HerrS & _).
  destruct (run_of_tree segsT pcT phT target_alloc_limit (tT inp enT) QT enT inp HimplT HleavesT HsafeT Hvi)
    as (HtrT & HerrT & _).
  split; [exact HerrS|]. split; [exact HerrT|].
  eapply trace_equiv_trans; [exact HtrS|].
  eapply trace_equiv_trans; [exact (HEQ enS enT inp HvS HvT Hvi)|].
  apply trace_equiv_sym. exact HtrT.
Qed.

(* [comment removed for export] *)
Theorem error_free_scfg_budgets_from_trees_gen :
  forall {RS RT : Type}
         (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo)
         (tS : prog_tree RS) (tT : prog_tree RT)
         (QS : RS -> machine_state -> Prop) (QT : RT -> machine_state -> Prop),
    tree_ok segsS pcS phS source_alloc_limit tS QS ->
    tree_ok segsT pcT phT target_alloc_limit tT QT ->
    trees_equiv segsS pcS phS segsT pcT phT tS tT ->
    strong_universal_error_free_T_scfg_budgets ncfg ShippedBudgets.lim_source ShippedBudgets.lim_target
      (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  intros. apply (strong_universal_error_free_T_scfg_budgets_of_scfg ncfg).
  eapply error_free_from_trees_gen; eassumption.
Qed.

(* [comment removed for export] *)
Theorem error_free_scfg_from_trees_gen :
  forall {RS RT : Type}
         (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo)
         (tS : prog_tree RS) (tT : prog_tree RT)
         (QS : RS -> machine_state -> Prop) (QT : RT -> machine_state -> Prop),
    tree_ok segsS pcS phS source_alloc_limit tS QS ->
    tree_ok segsT pcT phT target_alloc_limit tT QT ->
    trees_equiv segsS pcS phS segsT pcT phT tS tT ->
    strong_universal_error_free_T_scfg ncfg (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof. intros. eapply error_free_from_trees_gen; eassumption. Qed.

Theorem strong_universal_scfg_from_trees_gen :
  forall {RS RT : Type}
         (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo)
         (tS : prog_tree RS) (tT : prog_tree RT)
         (QS : RS -> machine_state -> Prop) (QT : RT -> machine_state -> Prop),
    tree_ok segsS pcS phS source_alloc_limit tS QS ->
    tree_ok segsT pcT phT target_alloc_limit tT QT ->
    trees_equiv segsS pcS phS segsT pcT phT tS tT ->
    strong_universal_T_scfg ncfg (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof. intros. eapply strong_universal_from_trees_gen; eassumption. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
