(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (halts_of_impl_tree takes the launch's channel-reader premise (in_channel_reader) and a bound segs_top segs <= 0x10000000; its walk premise uses init_ms's new arguments (the mmap base and the ProcInput), and its leaves and safety premises start from the initial model with the vDSO (with_vdso); re-proved by lifting the walk to run_segments, the run's segments with the vDSO pair; the Proof using lists of msteps_must_exit_in and tree_at_must_exit_in shortened; imports Vdso, RunSegs and InitMem). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Monad Specs Run Vdso.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv Cfg RunSegs InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require InitMem.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Bridge.
  Variable node : Type.
  Variable segs : list Segment.
  Variable at_node : node -> machine_state -> Prop.
  Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
  Variable nexit : node -> Model -> word -> Model -> Prop.
  Variable minv : Model -> Prop.
  Variable nsafe : node -> Model -> Prop.
  Hypothesis NS : node_sound node segs at_node nstep nexit minv nsafe.
  (* [comment removed for export] *)
  Hypothesis NK : forall n mo code mo', nexit n mo code mo' -> m_killed mo' = None.
  (* [comment removed for export] *)
  Variable S : list word.
  Hypothesis NC : forall n mo code mo', nexit n mo code mo' -> In code S.

  (* [comment removed for export] *)
  Lemma msteps_must_exit_in : forall ms ms1 mo,
    msteps segs ms ms1 ->
    m_halted mo = None -> minv mo ->
    must_exit_in_at_cfg ACFG segs S (mkCfg ms1 mo) ->
    must_exit_in_at_cfg ACFG segs S (mkCfg ms mo).
  Proof using NS.
    intros ms ms1 mo Hm Hh Hinv Hend.
    induction Hm as [ms | ms msa ms1 H1 H2 IH].
    - exact Hend.
    - apply must_exit_in_at_cfg_running.
      + exact Hh.
      + exists [], (SNext (mkCfg msa mo)). apply (mstep_sstep_cfg segs ms msa mo Hh (ns_nolazy _ _ _ _ _ _ _ NS mo Hinv) H1).
      + intros evs Hss. destruct (sstep_cfg_mstep_inv segs ms mo msa evs SError (ns_nolazy _ _ _ _ _ _ _ NS mo Hinv) H1 Hss) as [_ E].
        discriminate E.
      + intros evs c' Hss. destruct (sstep_cfg_mstep_inv segs ms mo msa evs (SNext c') (ns_nolazy _ _ _ _ _ _ _ NS mo Hinv) H1 Hss) as [_ E].
        injection E as ->. exact (IH Hend).
  Qed.

  Theorem tree_at_must_exit_in : forall {R} (t : itree node R) Q ms mo,
    tree_at segs at_node nstep minv nsafe t Q ms mo ->
    must_exit_in_at_cfg ACFG segs S (mkCfg ms mo).
  Proof using NS NK NC.
    intros R t. induction t as [r | n k IH]; intros Q ms mo HT.
    - destruct HT as (_ & Hl & _). destruct (leaves_unreachable_m_ret node nstep r mo Hl).
    - pose proof HT as (Ht & Hl & Hh & Hinv & Hsf).
      cbn in Ht. destruct Ht as (ms1 & Hm & Hat & Hk).
      apply (msteps_must_exit_in ms ms1 mo Hm Hh Hinv).
      apply must_exit_in_at_cfg_running.
      + exact Hh.
      + destruct (ns_progress _ _ _ _ _ _ _ NS n ms1 mo Hat Hh Hinv (proj1 Hsf)) as [(rsp & mo' & evs & Hst) | (code & mo' & Hex)].
        * destruct (ns_sound _ _ _ _ _ _ _ NS n ms1 mo rsp mo' evs Hat Hh Hinv (proj1 Hsf) Hst) as (_ & _ & Hss). eauto.
        * destruct (ns_exit _ _ _ _ _ _ _ NS n ms1 mo code mo' Hat Hh Hinv (proj1 Hsf) Hex) as (_ & Hss). eauto.
      + intros evs Hss.
        destruct (ns_complete _ _ _ _ _ _ _ NS n ms1 mo evs SError Hat Hh Hinv (proj1 Hsf) Hss)
          as [(rsp & mo' & E & _) | (code & mo' & E & _)]; discriminate E.
      + intros evs c' Hss.
        destruct (ns_complete _ _ _ _ _ _ _ NS n ms1 mo evs (SNext c') Hat Hh Hinv (proj1 Hsf) Hss)
          as [(rsp & mo' & E & Hst) | (code & mo' & E & Hex & _)].
        * injection E as ->.
          destruct (tree_at_step node segs at_node nstep nexit minv nsafe NS n k Q ms1 mo rsp mo' evs Hat Hk Hl Hh Hinv Hsf Hst) as [HT' _].
          exact (IH rsp Q (nret ms1 rsp) mo' HT').
        * injection E as ->.
          destruct (ns_exit _ _ _ _ _ _ _ NS n ms1 mo code mo' Hat Hh Hinv (proj1 Hsf) Hex) as (Hh' & _).
          apply (must_exit_in_at_cfg_halted ACFG segs S _ code); cbn [cfg_model];
            [exact Hh' | exact (NC n mo code mo' Hex) | exact (NK n mo code mo' Hex)].
  Qed.
End Bridge.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma must_exit_in_at_eqv : forall segs S c,
  must_exit_in_at_cfg ACFG segs S c -> forall c', cfg_eqv c c' -> must_exit_in_at_cfg ACFG segs S c'.
Proof.
  intros segs S c H. induction H as [c code Hh Hin Hk | c Hnone Hprog Hnoerr Hnext IH]; intros c' Heqv.
  - destruct c as [ms mo], c' as [ms' mo']. destruct Heqv as [_ Hmo]. cbn in *. subst.
    apply (must_exit_in_at_cfg_halted ACFG segs S _ code); cbn; assumption.
  - apply must_exit_in_at_cfg_running.
    + destruct c as [ms mo], c' as [ms' mo']. destruct Heqv as [_ Hmo]. cbn in *. subst. exact Hnone.
    + destruct Hprog as (evs & st & Hst).
      destruct (sstep_cfg_eqv_scfg segs ACFG c c' evs st Heqv Hst) as (X' & Hst' & _). eauto.
    + intros evs Hst'.
      destruct (sstep_cfg_eqv_scfg segs ACFG c' c evs SError (cfg_eqv_sym _ _ Heqv) Hst') as (X & Hst & HX).
      destruct X as [c2|]; simpl in HX; [contradiction|]. exact (Hnoerr evs Hst).
    + intros evs c2' Hst'.
      destruct (sstep_cfg_eqv_scfg segs ACFG c' c evs (SNext c2') (cfg_eqv_sym _ _ Heqv) Hst') as (X & Hst & HX).
      destruct X as [c2|]; simpl in HX; [|contradiction].
      apply (IH evs c2 Hst). apply cfg_eqv_sym. exact HX.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma hx_nexit_not_killed : forall n mo code mo', nexit n mo code mo' -> m_killed mo' = None.
Proof.
  intros n mo code mo' H. destruct n; cbn in H; try contradiction.
  destruct H as [_ ->]. apply m_killed_with_halted.
Qed.

(* [comment removed for export] *)
Lemma hx_nexit_any : forall n mo code mo', nexit n mo code mo' -> In code AnyExit.codes.
Proof.
  intros n mo code mo' H. destruct n; cbn [nexit] in H; try contradiction.
  destruct H as [-> _]. apply any_exit_covers.
Qed.

(* [comment removed for export] *)
Theorem halts_of_impl_tree : forall segs pc ph lim {R} (t : itree node R) (Q : R -> machine_state -> Prop) en inp,
  valid_entry (mkImage segs pc ph) en inp ->
  in_va_size inp = Sv48 ->
  in_channel_reader inp = true ->
  (InitMem.segs_top segs <= 0x10000000)%Z ->
  impl segs (at_node segs) t Q
       (init_ms segs pc ph (en_sp en) (en_mmap_base en) (en_draw en) inp) ->
  leaves_unreachable_m nstep t (with_vdso (vdso_run_init (ed_vdso (en_draw en)))
    (init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp)) ->
  tsafe nstep nsafe t (with_vdso (vdso_run_init (ed_vdso (en_draw en)))
    (init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp)) ->
  must_exit_in_scfg ACFG AnyExit.codes (mkImage segs pc ph) lim en inp.
Proof.
  intros segs pc ph lim R t Q [sp brk0 mbase rnd] inp Hve Hsv48 Hrdr Htop Himpl0 Hleaves Hsafe.
  cbn [en_sp en_brk en_mmap_base en_draw] in Himpl0, Hleaves, Hsafe.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hve. destruct Hve as (Vsp & _ & Vmb & _ & _).
  (* LPS 727298f3 runs over [run_segments segs inp sp mbase]: lift the walk to it. *)
  pose proof (impl_lift segs (vdso_segments (in_kernel inp) sp mbase)
                (fun s Hs => vdso_segments_high (in_kernel inp) sp mbase (InitMem.segs_top segs + 8) Vsp Vmb ltac:(lia) s Hs)
                t Q _ Himpl0) as Himpl.
  cbn [must_exit_in_scfg]. unfold init_config.
  set (V := run_segments segs inp sp mbase).
  change (segs ++ vdso_segments (in_kernel inp) sp mbase) with V in Himpl.
  replace (segments_reserved V) with (segments_reserved segs)
    by (symmetry; apply segments_reserved_vdso_app).
  set (mo := with_vdso (vdso_run_init (ed_vdso rnd)) (init_model (segments_reserved segs) brk0 mbase sp lim inp)) in *.
  assert (Hminv : minv mo).
  { change (minv (init_model (segments_reserved segs) brk0 mbase sp lim inp)).
    apply minv_init; [|exact Hrdr]. destruct Vsp as (L & H & _). lia. }
  pose proof Himpl as Himpl'.
  change (impl V (at_node V) t
            (fun (r : R) (ms' : machine_state) => exists ms0 : machine_state, ms' = with_rom ms0 (seg_rom V) /\ Q r ms0)
            (init_ms V pc ph sp mbase rnd inp)) in Himpl'.
  apply (must_exit_in_at_eqv V AnyExit.codes
           (mkCfg (init_ms V pc ph sp mbase rnd inp) mo)).
  - eapply (tree_at_must_exit_in node V (at_node V) nstep nexit minv nsafe (nodes_sound V)
             hx_nexit_not_killed AnyExit.codes hx_nexit_any t).
    split; [exact Himpl' | split; [exact Hleaves | split; [reflexivity | split; [exact Hminv | exact Hsafe]]]].
  - split; [| reflexivity]. cbn [cfg_ms]. apply ms_eqv_sym. apply init_machine_state_eqv.
Qed.
