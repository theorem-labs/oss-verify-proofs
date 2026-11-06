(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv FP.
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
  init_ms segs pc ph (en_sp en) (en_draw en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp).

Lemma ms0_eq : forall segs pc ph en inp,
  ms0 segs pc ph en inp =
  MS (mkR_init (en_sp en)) bvmap_empty (Z_to_bv 64 (Z.of_N pc)) (Z_to_bv 32 0) None
     (wrap_mem ph (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) (seg_rom segs).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition mo0 (segs : list Segment) (lim : Z) (en : ExecEntry) (inp : ProcInput) : Model :=
  init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp.

Lemma init_config_eq : forall segs pc ph lim en inp,
  init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp
  = mkCfg (init_machine_state segs pc ph (en_sp en) (en_draw en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (mo0 segs lim en inp).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mo0_not_halted : forall segs lim en inp, m_halted (mo0 segs lim en inp) = None.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma valid_input_fs : forall inp, valid_input inp -> valid_fs (in_fs inp).
Proof. intros inp (_ & _ & H & _). exact H. Qed.

Lemma valid_input_rel : forall inp, valid_input inp -> fs_keys_relative (in_image_fs inp).
Proof. intros inp (_ & _ & _ & H & _). exact H. Qed.

Lemma mo0_minv : forall segs lim en inp, valid_input inp -> minv (mo0 segs lim en inp).
Proof. intros segs lim en inp Hvi. apply minv_init. exact (valid_input_rel inp Hvi). Qed.

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
  forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
    impl segs (at_node segs) (npeek segs) (t inp en) Q (ms0 segs pc ph en inp)
    /\ leaves_unreachable_m nstep (t inp en) (mo0 segs lim en inp)
    /\ tsafe nstep nsafe (t inp en) (mo0 segs lim en inp).

(* [comment removed for export] *)
Definition tree_traces {R : Type} (t : itree node R) (mo : Model) : list event -> Prop :=
  fun tr => exists full, ttrace nstep nexit t mo full /\ is_prefix tr full.

(* [comment removed for export] *)
Definition tree_exits {R : Type} (t : itree node R) (mo : Model) : list event -> Prop :=
  fun tr => exists full, texit nstep nexit t mo full /\ is_prefix tr full.

Lemma tree_traces_exits : forall {R : Type} (t : itree node R) mo tr,
  leaves_unreachable_m nstep t mo -> tree_traces t mo tr -> tree_exits t mo tr.
Proof.
  intros R t mo tr Hl (full & Hf & Hp). exists full. split; [|exact Hp].
  eapply ttrace_texit; eassumption.
Qed.

(* [comment removed for export] *)
Definition tree_wins {R : Type} (segs : list Segment) (t : itree node R) (mo : Model) : list event -> Prop :=
  fun tr => wins (npeek segs) nstep nexit t mo (is_prefix tr).

(* [comment removed for export] *)
Definition trees_equiv_lim {RS RT : Type} (limS limT : Z) (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
    (segsT : list Segment) (pcT : N) (phT : PhdrInfo) (tS : prog_tree RS) (tT : prog_tree RT) : Prop :=
  forall enS enT inp,
    valid_entry (mkImage segsS pcS phS) enS inp ->
    valid_entry (mkImage segsT pcT phT) enT inp ->
    valid_input inp ->
    (forall tr, tree_exits (tS inp enS) (mo0 segsS limS enS inp) tr ->
                tree_wins segsT (tT inp enT) (mo0 segsT limT enT inp) tr)
    /\ (forall tr, tree_exits (tT inp enT) (mo0 segsT limT enT inp) tr ->
                   tree_wins segsS (tS inp enS) (mo0 segsS limS enS inp) tr).

(* [comment removed for export] *)
Definition trees_equiv {RS RT : Type} := @trees_equiv_lim RS RT source_alloc_limit target_alloc_limit.

(* [comment removed for export] *)
Lemma texit_wexit_wins : forall {RS RT : Type} segsT (tS : itree node RS) (tT : itree node RT) moS moT,
  (forall full, texit nstep nexit tS moS full -> wexit (npeek segsT) nstep nexit tT moT (eq full)) ->
  forall tr, tree_exits tS moS tr -> tree_wins segsT tT moT tr.
Proof.
  intros RS RT segsT tS tT moS moT H tr (full & Hx & Hp). unfold tree_wins.
  eapply wins_mono; [apply wexit_wins; apply H; exact Hx|]. intros tr0 <-. exact Hp.
Qed.

Lemma trees_equiv_lim_of_wexit : forall {RS RT : Type} limS limT segsS pcS phS segsT pcT phT (tS : prog_tree RS) (tT : prog_tree RT),
  (forall enS enT inp,
    valid_entry (mkImage segsS pcS phS) enS inp ->
    valid_entry (mkImage segsT pcT phT) enT inp ->
    valid_input inp ->
    (forall full, texit nstep nexit (tS inp enS) (mo0 segsS limS enS inp) full ->
                  wexit (npeek segsT) nstep nexit (tT inp enT) (mo0 segsT limT enT inp) (eq full))
    /\ (forall full, texit nstep nexit (tT inp enT) (mo0 segsT limT enT inp) full ->
                  wexit (npeek segsS) nstep nexit (tS inp enS) (mo0 segsS limS enS inp) (eq full))) ->
  trees_equiv_lim limS limT segsS pcS phS segsT pcT phT tS tT.
Proof.
  intros RS RT limS limT segsS pcS phS segsT pcT phT tS tT H enS enT inp HvS HvT Hvi.
  destruct (H enS enT inp HvS HvT Hvi) as [HST HTS]. split; eapply texit_wexit_wins; eassumption.
Qed.

Lemma trees_equiv_of_wexit : forall {RS RT : Type} segsS pcS phS segsT pcT phT (tS : prog_tree RS) (tT : prog_tree RT),
  (forall enS enT inp,
    valid_entry (mkImage segsS pcS phS) enS inp ->
    valid_entry (mkImage segsT pcT phT) enT inp ->
    valid_input inp ->
    (forall full, texit nstep nexit (tS inp enS) (mo0 segsS source_alloc_limit enS inp) full ->
                  wexit (npeek segsT) nstep nexit (tT inp enT) (mo0 segsT target_alloc_limit enT inp) (eq full))
    /\ (forall full, texit nstep nexit (tT inp enT) (mo0 segsT target_alloc_limit enT inp) full ->
                  wexit (npeek segsS) nstep nexit (tS inp enS) (mo0 segsS source_alloc_limit enS inp) (eq full))) ->
  trees_equiv segsS pcS phS segsT pcT phT tS tT.
Proof. intros RS RT segsS pcS phS segsT pcT phT tS tT. apply trees_equiv_lim_of_wexit. Qed.

(* [comment removed for export] *)
Lemma tree_exits_wins : forall {R : Type} segs (t : itree node R) mo tr,
  npfree (npeek segs) t -> tree_exits t mo tr -> tree_wins segs t mo tr.
Proof.
  intros R segs t mo tr Hnp (full & Hf & Hp). unfold tree_wins.
  eapply wins_mono; [apply wexit_wins; apply texit_wexit; eassumption|]. intros tr0 <-. exact Hp.
Qed.

Lemma trees_equiv_of_texit : forall {RS RT : Type} segsS segsT (tS : itree node RS) (tT : itree node RT) moS moT,
  npfree (npeek segsS) tS -> npfree (npeek segsT) tT ->
  (forall tr, texit nstep nexit tS moS tr <-> texit nstep nexit tT moT tr) ->
  (forall tr, tree_exits tS moS tr -> tree_wins segsT tT moT tr)
  /\ (forall tr, tree_exits tT moT tr -> tree_wins segsS tS moS tr).
Proof.
  intros RS RT segsS segsT tS tT moS moT HnS HnT H. split; intros tr (full & Hf & Hp).
  - apply tree_exits_wins; [exact HnT|]. exists full. split; [apply H; exact Hf|exact Hp].
  - apply tree_exits_wins; [exact HnS|]. exists full. split; [apply H; exact Hf|exact Hp].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma run_eq : forall segs pc ph lim en inp,
  run_scfg CFG (mkImage segs pc ph) lim en inp =
  let c0 := mkCfg (init_machine_state segs pc ph (en_sp en) (en_draw en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (mo0 segs lim en inp) in
  {| bh_traces := obs_trace_cfg segs CFG c0;
     bh_errors := reaches_error_cfg segs CFG c0;
     bh_all_errors := all_traces_error_cfg segs CFG c0;
     bh_unmodeled := reaches_unmodeled_cfg segs CFG c0 |}.
Proof. intros segs pc ph lim [sp brk mb rnd] inp. reflexivity. Qed.

(* [comment removed for export] *)
Lemma run_of_tree : forall {R : Type} segs pc ph lim (t : itree node R) (Q : R -> machine_state -> Prop) en inp,
  impl segs (at_node segs) (npeek segs) t Q (ms0 segs pc ph en inp) ->
  leaves_unreachable_m nstep t (mo0 segs lim en inp) ->
  tsafe nstep nsafe t (mo0 segs lim en inp) ->
  valid_input inp ->
  (forall tr, bh_traces (run_scfg CFG (mkImage segs pc ph) lim en inp) tr -> tree_traces t (mo0 segs lim en inp) tr)
  /\ (forall tr, tree_wins segs t (mo0 segs lim en inp) tr -> bh_traces (run_scfg CFG (mkImage segs pc ph) lim en inp) tr)
  /\ ~ bh_errors (run_scfg CFG (mkImage segs pc ph) lim en inp).
Proof.
  intros R segs pc ph lim t Q en inp Himpl Hleaves Hsafe Hvi.
  pose proof (mo0_minv segs lim en inp Hvi) as Hminv.
  rewrite run_eq. cbn [bh_traces bh_errors bh_unmodeled].
  destruct (init_behaviourC_eqv segs CFG pc ph (en_sp en) (en_draw en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (mo0 segs lim en inp))
    as (Htr & Herr).
  change (init_ms segs pc ph (en_sp en) (en_draw en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) with (ms0 segs pc ph en inp) in Htr, Herr.
  pose proof (nodes_sound segs) as NS.
  split; [| split].
  - intros tr. rewrite (Htr tr). unfold tree_traces.
    apply (impl_run_sound2 node segs CFG (at_node segs) (npeek segs) nstep nexit minv nsafe NS t _ _ _
             Himpl Hleaves (mo0_not_halted _ _ _ _) Hminv Hsafe).
  - intros tr Hw. rewrite (Htr tr).
    apply (impl_run_complete2_obs node segs CFG (at_node segs) (npeek segs) nstep nexit minv nsafe NS t _ _ _
             Himpl Hleaves (mo0_not_halted _ _ _ _) Hminv Hsafe tr Hw).
  - rewrite Herr.
    apply (impl_run_safe2 node segs CFG (at_node segs) (npeek segs) nstep nexit minv nsafe NS t _ _ _
             Himpl Hleaves (mo0_not_halted _ _ _ _) Hminv Hsafe (ms0_svc _ _ _ _ _)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma trace_equiv_sym : forall T1 T2, trace_equiv T1 T2 -> trace_equiv T2 T1.
Proof. intros T1 T2 H tr. symmetry. apply H. Qed.

Lemma trace_equiv_trans : forall T1 T2 T3, trace_equiv T1 T2 -> trace_equiv T2 T3 -> trace_equiv T1 T3.
Proof. intros T1 T2 T3 H1 H2 tr. rewrite (H1 tr). apply H2. Qed.

(* [comment removed for export] *)
Theorem strong_equiv_error_free_scfg_from_trees :
  forall {RS RT : Type} (limS limT : Z)
         (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo)
         (tS : prog_tree RS) (tT : prog_tree RT)
         (QS : RS -> machine_state -> Prop) (QT : RT -> machine_state -> Prop),
    tree_ok segsS pcS phS limS tS QS ->
    tree_ok segsT pcT phT limT tT QT ->
    trees_equiv_lim limS limT segsS pcS phS segsT pcT phT tS tT ->
    forall enS enT inp,
      valid_entry (mkImage segsS pcS phS) enS inp ->
      valid_entry (mkImage segsT pcT phT) enT inp ->
      valid_input inp ->
      strong_equiv_error_free_budgets_scfg CFG limS limT (mkImage segsS pcS phS) (mkImage segsT pcT phT) enS enT inp.
Proof.
  intros RS RT limS limT segsS pcS phS segsT pcT phT tS tT QS QT HS HT HEQ enS enT inp HvS HvT Hvi.
  destruct (HS enS inp HvS Hvi) as (HimplS & HleavesS & HsafeS).
  destruct (HT enT inp HvT Hvi) as (HimplT & HleavesT & HsafeT).
  destruct (run_of_tree segsS pcS phS limS (tS inp enS) QS enS inp HimplS HleavesS HsafeS Hvi)
    as (HsoundS & HcomplS & HerrS).
  destruct (run_of_tree segsT pcT phT limT (tT inp enT) QT enT inp HimplT HleavesT HsafeT Hvi)
    as (HsoundT & HcomplT & HerrT).
  destruct (HEQ enS enT inp HvS HvT Hvi) as [HST HTS].
  split; [exact HerrS|]. split; [exact HerrT|].
  intros tr. split.
  - intros H. apply HcomplT, HST. apply (tree_traces_exits _ _ _ HleavesS). apply HsoundS, H.
  - intros H. apply HcomplS, HTS. apply (tree_traces_exits _ _ _ HleavesT). apply HsoundT, H.
Qed.

(* [comment removed for export] *)
Theorem strong_universal_error_free_scfg_budgets_from_trees_gen :
  forall {RS RT : Type} (limS limT : Z)
         (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo)
         (tS : prog_tree RS) (tT : prog_tree RT)
         (QS : RS -> machine_state -> Prop) (QT : RT -> machine_state -> Prop),
    tree_ok segsS pcS phS limS tS QS ->
    tree_ok segsT pcT phT limT tT QT ->
    trees_equiv_lim limS limT segsS pcS phS segsT pcT phT tS tT ->
    strong_universal_error_free_T_scfg_budgets CFG limS limT (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  intros RS RT limS limT segsS pcS phS segsT pcT phT tS tT QS QT HS HT HEQ enS enT inp HvS HvT Hvi _.
  eapply strong_equiv_error_free_scfg_from_trees; eassumption.
Qed.

(* [comment removed for export] *)
Theorem strong_universal_error_free_scfg_from_trees_gen :
  forall {RS RT : Type}
         (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo)
         (tS : prog_tree RS) (tT : prog_tree RT)
         (QS : RS -> machine_state -> Prop) (QT : RT -> machine_state -> Prop),
    tree_ok segsS pcS phS source_alloc_limit tS QS ->
    tree_ok segsT pcT phT target_alloc_limit tT QT ->
    trees_equiv segsS pcS phS segsT pcT phT tS tT ->
    strong_universal_error_free_T_scfg CFG (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  intros RS RT segsS pcS phS segsT pcT phT tS tT QS QT HS HT HEQ enS enT inp HvS HvT Hvi.
  exact (strong_equiv_error_free_scfg_from_trees source_alloc_limit target_alloc_limit
           segsS pcS phS segsT pcT phT tS tT QS QT HS HT HEQ enS enT inp HvS HvT Hvi).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3 ImgTgtUbsan.

(* [comment removed for export] *)
Theorem strong_universal_error_free_from_trees :
  forall (tS tT : prog_tree (Exc.exc unit)) (postS postT : unit -> machine_state -> Prop),
  tree_ok ssegs Plain.M.init_pc Plain.M.phdrs source_alloc_limit tS (epost postS) ->
  tree_ok usegs Ubsan.M.init_pc Ubsan.M.phdrs target_alloc_limit tT (epost postT) ->
  trees_equiv ssegs Plain.M.init_pc Plain.M.phdrs
              usegs Ubsan.M.init_pc Ubsan.M.phdrs tS tT ->
  strong_universal_error_free_T_scfg_budgets
    (mkSpuriousCfg false true true true true true)
    ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
  intros tS tT postS postT HS HT HEQ.
  exact (strong_universal_error_free_scfg_budgets_from_trees_gen source_alloc_limit target_alloc_limit
           ssegs _ _ usegs _ _ tS tT (epost postS) (epost postT) HS HT HEQ).
Qed.
