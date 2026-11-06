(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv FP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition prog_tree (R : Type) : Type := ProcInput -> ExecEntry -> itree node R.

Definition ms0 (segs : list Segment) (pc : N) (ph : PhdrInfo)
    (en : ExecEntry) (inp : ProcInput) : machine_state :=
  init_ms segs pc ph (en_sp en) (en_draw en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp).

Lemma ms0_eq : forall segs pc ph en inp,
  ms0 segs pc ph en inp =
  MS (mkR_init (en_sp en)) bvmap_empty (Z_to_bv 64 (Z.of_N pc)) (Z_to_bv 32 0) None
     (wrap_mem ph (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) (seg_rom segs).
Proof. reflexivity. Qed.

Definition mo0 (segs : list Segment) (lim : Z) (en : ExecEntry) (inp : ProcInput) : Model :=
  init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp.

Lemma init_config_eq : forall segs pc ph lim en inp,
  init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp
  = mkCfg (init_machine_state segs pc ph (en_sp en) (en_draw en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (mo0 segs lim en inp).
Proof. reflexivity. Qed.

Lemma mo0_alloc_top : forall segs lim en inp,
  alloc_top (m_vmmaps (mo0 segs lim en inp)) = (bv_unsigned (en_sp en) - stack_max_size)%Z.
Proof. reflexivity. Qed.

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

Lemma vie_va_size : forall inp, valid_input_either inp -> in_va_size inp = Sv48.
Proof. intros inp (_ & _ & _ & _ & _ & _ & _ & _ & v & _). exact v. Qed.

Lemma mo0_not_halted : forall segs lim en inp, m_halted (mo0 segs lim en inp) = None.
Proof. reflexivity. Qed.

Lemma mo0_minv : forall segs lim en inp, minv (mo0 segs lim en inp).
Proof. intros. apply minv_init. Qed.

Lemma ms0_svc : forall segs pc ph en inp, ms_svc_pending (ms0 segs pc ph en inp) = None.
Proof. reflexivity. Qed.

Remark frm0_init : frm0 (Z_to_bv 32 0).
Proof. reflexivity. Qed.

Lemma ms0_frm0 : forall segs pc ph en inp, frm0 (ms_fcsr (ms0 segs pc ph en inp)).
Proof. intros. exact frm0_init. Qed.

Definition tree_ok {R : Type} (segs : list Segment) (pc : N) (ph : PhdrInfo) (lim : Z)
    (t : prog_tree R) (Q : R -> machine_state -> Prop) : Prop :=
  forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
    impl segs (at_node segs) (t inp en) Q (ms0 segs pc ph en inp)
    /\ leaves_unreachable_m nstep (t inp en) (mo0 segs lim en inp)
    /\ tsafe nstep nsafeU (t inp en) (mo0 segs lim en inp).

Definition tree_traces {R : Type} (t : itree node R) (mo : Model) : list event -> Prop :=
  fun tr => exists full, ttrace nstep nexit t mo full /\ is_prefix tr full.

Definition trees_equiv {RS RT : Type} (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
    (segsT : list Segment) (pcT : N) (phT : PhdrInfo) (tS : prog_tree RS) (tT : prog_tree RT) : Prop :=
  forall enS enT inp,
    valid_entry (mkImage segsS pcS phS) enS inp ->
    valid_entry (mkImage segsT pcT phT) enT inp ->
    valid_input_either inp ->
    forall tS' tT', resolves tS' (tS inp enS) -> resolves tT' (tT inp enT) ->
    trace_equiv (tree_traces tS' (mo0 segsS source_alloc_limit enS inp))
                (tree_traces tT' (mo0 segsT target_alloc_limit enT inp)).

Lemma trees_equiv_of_ttrace : forall {RS RT : Type} (tS : itree node RS) (tT : itree node RT) moS moT,
  (forall tr, ttrace nstep nexit tS moS tr <-> ttrace nstep nexit tT moT tr) ->
  trace_equiv (tree_traces tS moS) (tree_traces tT moT).
Proof.
  intros RS RT tS tT moS moT H tr. unfold tree_traces.
  split; intros (full & Hf & Hp); exists full; split; auto; apply H; exact Hf.
Qed.

Lemma run_scfg_eq : forall cfg segs pc ph lim en inp,
  run_scfg cfg (mkImage segs pc ph) lim en inp =
  let c0 := mkCfg (init_machine_state segs pc ph (en_sp en) (en_draw en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (mo0 segs lim en inp) in
  {| bh_traces := obs_trace_cfg segs cfg c0;
     bh_errors := reaches_error_cfg segs cfg c0;
     bh_all_errors := all_traces_error_cfg segs cfg c0;
     bh_unmodeled := reaches_unmodeled_cfg segs cfg c0 |}.
Proof. intros cfg segs pc ph lim [sp brk mb rnd] inp. reflexivity. Qed.

Lemma run_of_tree : forall {R : Type} segs pc ph lim (t : itree node R) (Q : R -> machine_state -> Prop) en inp,
  impl segs (at_node segs) t Q (ms0 segs pc ph en inp) ->
  leaves_unreachable_m nstep t (mo0 segs lim en inp) ->
  tsafe nstep nsafeU t (mo0 segs lim en inp) ->
  exists t', resolves t' t
  /\ trace_equiv (bh_traces (run_scfg ACFG (mkImage segs pc ph) lim en inp)) (tree_traces t' (mo0 segs lim en inp))
  /\ ~ bh_errors (run_scfg ACFG (mkImage segs pc ph) lim en inp)
  /\ ~ bh_unmodeled (run_scfg ACFG (mkImage segs pc ph) lim en inp).
Proof.
  intros R segs pc ph lim t Q en inp Himpl Hleaves Hsafe.
  rewrite run_scfg_eq. cbn [bh_traces bh_errors bh_unmodeled].
  destruct (init_behaviour_scfg_eqv ACFG segs pc ph (en_sp en) (en_draw en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (mo0 segs lim en inp))
    as (Htr & Herr & _ & Hunm).
  change (init_ms segs pc ph (en_sp en) (en_draw en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) with (ms0 segs pc ph en inp) in Htr, Herr, Hunm.
  pose proof (nodes_sound segs) as NS.
  destruct (impl_run_traces3 node segs ACFG (at_node segs) nstep nexit minv nsafeU NS t _ _ _
              Himpl Hleaves (mo0_not_halted _ _ _ _) (mo0_minv _ _ _ _) Hsafe (ms0_svc _ _ _ _ _)) as (t' & Hres & Htr').
  exists t'. split; [exact Hres|].
  split; [| split].
  - intros tr. rewrite (Htr tr). unfold tree_traces. exact (Htr' tr).
  - rewrite Herr.
    apply (impl_run_safe2 node segs ACFG (at_node segs) nstep nexit minv nsafeU NS t _ _ _
             Himpl Hleaves (mo0_not_halted _ _ _ _) (mo0_minv _ _ _ _) Hsafe (ms0_svc _ _ _ _ _)).
  - rewrite Hunm.
    apply (impl_run_modeled2 node segs ACFG (at_node segs) nstep nexit minv nsafeU NS t _ _ _
             Himpl Hleaves (mo0_not_halted _ _ _ _) (mo0_minv _ _ _ _) Hsafe (ms0_svc _ _ _ _ _)).
Qed.

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
    strong_universal_T_scfg ACFG (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  intros RS RT segsS pcS phS segsT pcT phT tS tT QS QT HS HT HEQ enS enT inp HvS HvT Hvi. apply valid_input_either_of_valid_input in Hvi.
  destruct (HS enS inp HvS Hvi) as (HimplS & HleavesS & HsafeS).
  destruct (HT enT inp HvT Hvi) as (HimplT & HleavesT & HsafeT).
  destruct (run_of_tree segsS pcS phS source_alloc_limit (tS inp enS) QS enS inp HimplS HleavesS HsafeS)
    as (tS' & HrS & HtrS & _ & HmodS).
  destruct (run_of_tree segsT pcT phT target_alloc_limit (tT inp enT) QT enT inp HimplT HleavesT HsafeT)
    as (tT' & HrT & HtrT & HerrT & _).
  split.
  -   exact HmodS.
  -
    right. split; [| exact HerrT].
    eapply trace_equiv_trans; [exact HtrS|].
    eapply trace_equiv_trans; [exact (HEQ enS enT inp HvS HvT Hvi tS' tT' HrS HrT)|].
    apply trace_equiv_sym. exact HtrT.
Qed.

Theorem error_free_from_trees_gen :
  forall {RS RT : Type}
         (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo)
         (tS : prog_tree RS) (tT : prog_tree RT)
         (QS : RS -> machine_state -> Prop) (QT : RT -> machine_state -> Prop),
    tree_ok segsS pcS phS source_alloc_limit tS QS ->
    tree_ok segsT pcT phT target_alloc_limit tT QT ->
    trees_equiv segsS pcS phS segsT pcT phT tS tT ->
    strong_universal_error_free_T_scfg ACFG (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  intros RS RT segsS pcS phS segsT pcT phT tS tT QS QT HS HT HEQ enS enT inp HvS HvT Hvi. apply valid_input_either_of_valid_input in Hvi.
  destruct (HS enS inp HvS Hvi) as (HimplS & HleavesS & HsafeS).
  destruct (HT enT inp HvT Hvi) as (HimplT & HleavesT & HsafeT).
  destruct (run_of_tree segsS pcS phS source_alloc_limit (tS inp enS) QS enS inp HimplS HleavesS HsafeS)
    as (tS' & HrS & HtrS & HerrS & _).
  destruct (run_of_tree segsT pcT phT target_alloc_limit (tT inp enT) QT enT inp HimplT HleavesT HsafeT)
    as (tT' & HrT & HtrT & HerrT & _).
  split; [exact HerrS|]. split; [exact HerrT|].
  eapply trace_equiv_trans; [exact HtrS|].
  eapply trace_equiv_trans; [exact (HEQ enS enT inp HvS HvT Hvi tS' tT' HrS HrT)|].
  apply trace_equiv_sym. exact HtrT.
Qed.

Theorem error_free_scfg_from_trees_gen :
  forall {RS RT : Type}
         (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo)
         (tS : prog_tree RS) (tT : prog_tree RT)
         (QS : RS -> machine_state -> Prop) (QT : RT -> machine_state -> Prop),
    tree_ok segsS pcS phS source_alloc_limit tS QS ->
    tree_ok segsT pcT phT target_alloc_limit tT QT ->
    trees_equiv segsS pcS phS segsT pcT phT tS tT ->
    strong_universal_error_free_T_scfg ACFG
      (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  intros. eapply error_free_from_trees_gen; eassumption.
Qed.

Theorem strong_universal_scfg_from_trees_gen :
  forall {RS RT : Type}
         (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo)
         (tS : prog_tree RS) (tT : prog_tree RT)
         (QS : RS -> machine_state -> Prop) (QT : RT -> machine_state -> Prop),
    tree_ok segsS pcS phS source_alloc_limit tS QS ->
    tree_ok segsT pcT phT target_alloc_limit tT QT ->
    trees_equiv segsS pcS phS segsT pcT phT tS tT ->
    strong_universal_T_scfg ACFG
      (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  intros. eapply strong_universal_from_trees_gen; eassumption.
Qed.

From OSSVerify.simdjson.fuzz_dump_raw_tape.images Require Import Plain.
From OSSVerify.simdjson.fuzz_dump_raw_tape.images Require Import Ubsan.
Module SrcP := Plain.

Theorem strong_universal_from_trees :
  forall (tS tT : prog_tree (Exc.exc unit)) (postS postT : unit -> machine_state -> Prop),
  tree_ok SrcP.M.loaded_segments SrcP.M.init_pc SrcP.M.phdrs
          source_alloc_limit tS (epost postS) ->
  tree_ok Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs
          target_alloc_limit tT (epost postT) ->
  trees_equiv SrcP.M.loaded_segments SrcP.M.init_pc SrcP.M.phdrs
              Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs
              tS tT ->
  strong_universal_T_scfg ACFG
    (mkImage SrcP.M.loaded_segments SrcP.M.init_pc SrcP.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof. intros tS tT postS postT. apply strong_universal_from_trees_gen. Qed.

Theorem error_free_from_trees :
  forall (tS tT : prog_tree (Exc.exc unit)) (postS postT : unit -> machine_state -> Prop),
  tree_ok SrcP.M.loaded_segments SrcP.M.init_pc SrcP.M.phdrs
          source_alloc_limit tS (epost postS) ->
  tree_ok Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs
          target_alloc_limit tT (epost postT) ->
  trees_equiv SrcP.M.loaded_segments SrcP.M.init_pc SrcP.M.phdrs
              Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs
              tS tT ->
  strong_universal_error_free_T_scfg ACFG
    (mkImage SrcP.M.loaded_segments SrcP.M.init_pc SrcP.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof. intros tS tT postS postT. apply error_free_from_trees_gen. Qed.

Theorem error_free_scfg_from_trees :
  forall (tS tT : prog_tree (Exc.exc unit)) (postS postT : unit -> machine_state -> Prop),
  tree_ok SrcP.M.loaded_segments SrcP.M.init_pc SrcP.M.phdrs
          source_alloc_limit tS (epost postS) ->
  tree_ok Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs
          target_alloc_limit tT (epost postT) ->
  trees_equiv SrcP.M.loaded_segments SrcP.M.init_pc SrcP.M.phdrs
              Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs
              tS tT ->
  strong_universal_error_free_T_scfg ACFG
    (mkImage SrcP.M.loaded_segments SrcP.M.init_pc SrcP.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof. intros tS tT postS postT. apply error_free_scfg_from_trees_gen. Qed.

