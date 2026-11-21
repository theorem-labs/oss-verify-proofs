(** * Lib.ITreeFO — the itree-of-syscall-nodes run lemmas over a spurious-failure configuration

    [Lib.ITree] relates a node tree to the UNFILTERED step relation [Run.sstep] through [node_sound].
    Statements issued with memory set to "fails only if forced" speak about [Run.sstep_cfg cfg]; this
    file is the same development over that relation: [node_sound_cfg] is [node_sound] with every
    [sstep] read as [sstep_cfg segs cfg], and each run lemma below is its [Lib.ITree] / [Lib.Halts]
    twin, proof for proof, ending in [obs_trace_cfg], [reaches_error_cfg], [reaches_unmodeled_cfg] and
    [MustExit.must_exit_in_at_cfg].  The tree side ([impl], [tsafe], [ttrace], [leaves_unreachable_m],
    [tree_at]) does not mention the step relation and is reused from [Lib.ITree] unchanged. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Lib Require Import PropExec MState Mem Exec ITree Halts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Lemma star_cfg_trans : forall segs cfg c1 t1 c2 t2 c3,
  star_cfg segs cfg c1 t1 c2 -> star_cfg segs cfg c2 t2 c3 -> star_cfg segs cfg c1 (t1 ++ t2) c3.
Proof.
  intros segs cfg c1 t1 c2 t2 c3 H1; revert t2 c3.
  induction H1 as [c | c1 evs c2 tr c3 Hss H IH]; intros t2 c4 H2; [exact H2 |].
  rewrite <- app_assoc. eapply star_cfg_step; [exact Hss | exact (IH _ _ H2)].
Qed.

Lemma star_cfg_one : forall segs cfg c evs c',
  sstep_cfg segs cfg c evs (SNext c') -> star_cfg segs cfg c evs c'.
Proof.
  intros segs cfg c evs c' H. rewrite <- (app_nil_r evs).
  eapply star_cfg_step; [exact H | apply star_cfg_refl].
Qed.

Section ITreeFO.

Variable cfg : SpuriousCfg.
Variable node : Type.
Variable segs : list Segment.
Variable at_node : node -> machine_state -> Prop.
Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit : node -> Model -> word -> Model -> Prop.
Variable minv : Model -> Prop.
Variable nsafe : node -> Model -> Prop.

(** [ITree.node_sound] over the filtered relation, field for field. *)
Record node_sound_cfg : Prop := {
  nsc_nolazy : forall mo, minv mo -> m_vm_lazy mo = [];
  nsc_pending : forall n ms, at_node n ms -> ms_svc_pending ms <> None;
  nsc_complete : forall n ms mo evs X, at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      sstep_cfg segs cfg (mkCfg ms mo) evs X ->
        (exists rsp mo', X = SNext (mkCfg (nret ms rsp) mo') /\ nstep n mo rsp mo' evs)
     \/ (exists code mo', X = SNext (mkCfg ms mo') /\ nexit n mo code mo' /\ evs = [ExitEv code (m_fs mo')]);
  nsc_sound : forall n ms mo rsp mo' evs, at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      nstep n mo rsp mo' evs ->
      m_halted mo' = None /\ minv mo'
      /\ sstep_cfg segs cfg (mkCfg ms mo) evs (SNext (mkCfg (nret ms rsp) mo'));
  nsc_exit : forall n ms mo code mo', at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      nexit n mo code mo' ->
      m_halted mo' = Some code
      /\ sstep_cfg segs cfg (mkCfg ms mo) [ExitEv code (m_fs mo')] (SNext (mkCfg ms mo'));
  nsc_progress : forall n ms mo, at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      (exists rsp mo' evs, nstep n mo rsp mo' evs) \/ (exists code mo', nexit n mo code mo')
}.

Let TreeAt := fun {R} (t : itree node R) Q ms mo => tree_at segs at_node nstep minv nsafe t Q ms mo.

(* -------------------------------------------------------------------------
   Instruction steps: the filtered relation's instruction constructors are [sstep]'s
   ------------------------------------------------------------------------- *)

Lemma sstep_cfg_mstep_inv : forall ms mo ms' evs X,
  m_vm_lazy mo = [] ->
  mstep segs ms ms' ->
  sstep_cfg segs cfg (mkCfg ms mo) evs X ->
  evs = [] /\ X = SNext (mkCfg ms' mo).
Proof.
  intros ms mo ms' evs X Hlz Hm Hss.
  exact (sstep_mstep_inv segs ms mo ms' evs X Hlz Hm (sstep_cfg_sub segs cfg _ _ _ Hss)).
Qed.

Lemma sstep_cfg_not_halted' : forall ms mo evs X,
  sstep_cfg segs cfg (mkCfg ms mo) evs X -> m_halted mo = None.
Proof. intros ms mo evs X Hss. inversion Hss; subst; assumption. Qed.

Lemma star_cfg_halted_nil : forall ms mo tr c',
  m_halted mo <> None -> star_cfg segs cfg (mkCfg ms mo) tr c' -> tr = [] /\ c' = mkCfg ms mo.
Proof.
  intros ms mo tr c' Hh Hstar. inversion Hstar; subst.
  - split; reflexivity.
  - exfalso. apply Hh. eapply sstep_cfg_not_halted'; eassumption.
Qed.

Lemma mstep_sstep_cfg : forall ms ms' mo,
  m_halted mo = None -> m_vm_lazy mo = [] -> mstep segs ms ms' ->
  sstep_cfg segs cfg (mkCfg ms mo) [] (SNext (mkCfg ms' mo)).
Proof.
  intros ms ms' mo Hh Hlz Hm. apply sstep_cfg_instr; [exact Hh | exact (proj1 Hm) |].
  apply mi_account_step_mstep; assumption.
Qed.

Lemma msteps_star_cfg : forall ms ms' mo,
  m_halted mo = None -> m_vm_lazy mo = [] -> msteps segs ms ms' ->
  star_cfg segs cfg (mkCfg ms mo) [] (mkCfg ms' mo).
Proof.
  intros ms ms' mo Hh Hlz Hm. induction Hm as [ms | ms ms1 ms2 H1 H2 IH].
  - apply star_cfg_refl.
  - change ([] : list event) with ([] ++ [] : list event).
    eapply star_cfg_step; [apply mstep_sstep_cfg; eassumption | exact IH].
Qed.

(* -------------------------------------------------------------------------
   The tree invariant along filtered steps
   ------------------------------------------------------------------------- *)

Lemma tree_at_step_cfg : node_sound_cfg -> forall {R} n (k : resp -> itree node R) Q ms1 mo rsp mo' evs,
  at_node n ms1 -> (forall rsp, impl segs at_node (k rsp) Q (nret ms1 rsp)) ->
  leaves_unreachable_m nstep (Vis n k) mo -> m_halted mo = None -> minv mo ->
  tsafe nstep nsafe (Vis n k) mo ->
  nstep n mo rsp mo' evs ->
  TreeAt (k rsp) Q (nret ms1 rsp) mo'
  /\ sstep_cfg segs cfg (mkCfg ms1 mo) evs (SNext (mkCfg (nret ms1 rsp) mo')).
Proof.
  intros NS R n k Q ms1 mo rsp mo' evs Hat Hk Hl Hh Hinv Hsf Hst.
  destruct (nsc_sound NS n ms1 mo rsp mo' evs Hat Hh Hinv (proj1 Hsf) Hst) as (Hh' & Hinv' & Hss).
  split; [| exact Hss]. split; [apply Hk |]. split; [eapply leaves_unreachable_m_step; eassumption |].
  split; [exact Hh' |]. split; [exact Hinv' |]. eapply tsafe_step; eassumption.
Qed.

Lemma impl_sstep_inv_cfg : node_sound_cfg -> forall {R} (t : itree node R) Q ms mo evs X,
  TreeAt t Q ms mo ->
  sstep_cfg segs cfg (mkCfg ms mo) evs X ->
     (exists ms', X = SNext (mkCfg ms' mo) /\ evs = [] /\ mstep segs ms ms' /\ TreeAt t Q ms' mo)
  \/ (exists n k rsp mo', t = Vis n k /\ at_node n ms /\ X = SNext (mkCfg (nret ms rsp) mo')
        /\ nstep n mo rsp mo' evs /\ TreeAt (k rsp) Q (nret ms rsp) mo')
  \/ (exists n k code mo', t = Vis n k /\ at_node n ms /\ X = SNext (mkCfg ms mo')
        /\ nexit n mo code mo' /\ evs = [ExitEv code (m_fs mo')] /\ m_halted mo' = Some code).
Proof.
  intros NS R t Q ms mo evs X HT Hss. destruct HT as (Ht & Hl & Hh & Hinv & Hsf).
  destruct (impl_inv _ _ _ _ t Q ms mo Ht Hl) as (n & k & ms1 & -> & Hm & Hat & Hk).
  inversion Hm; subst.
  - destruct (nsc_complete NS n ms1 mo evs X Hat Hh Hinv (proj1 Hsf) Hss)
      as [(rsp & mo' & HX & Hst) | (code & mo' & HX & Hex & Hevs)].
    + right; left. destruct (tree_at_step_cfg NS n k Q ms1 mo rsp mo' evs Hat Hk Hl Hh Hinv Hsf Hst) as [HT' _].
      exists n, k, rsp, mo'. split; [reflexivity |]. split; [exact Hat |]. split; [exact HX |].
      split; [exact Hst | exact HT'].
    + right; right. destruct (nsc_exit NS n ms1 mo code mo' Hat Hh Hinv (proj1 Hsf) Hex) as (Hh' & _).
      exists n, k, code, mo'. repeat split; auto.
  - left. match goal with H1 : mstep segs ms ?x, H2 : msteps segs ?x ms1 |- _ =>
      destruct (sstep_cfg_mstep_inv ms mo x evs X (nsc_nolazy NS mo Hinv) H1 Hss) as (-> & ->);
      exists x; split; [reflexivity |]; split; [reflexivity |]; split; [exact H1 |];
      split; [cbn; exists ms1; split; [exact H2 |]; split; [exact Hat | exact Hk] |];
      split; [exact Hl |]; split; [exact Hh |]; split; [exact Hinv | exact Hsf] end.
Qed.

(* -------------------------------------------------------------------------
   Traces, errors and uncovered points of the filtered run (Lib.ITree's run lemmas)
   ------------------------------------------------------------------------- *)

Lemma ttrace_exists_cfg : node_sound_cfg -> forall {R} (t : itree node R) Q ms mo,
  TreeAt t Q ms mo -> exists full, ttrace nstep nexit t mo full.
Proof.
  intros NS R t. induction t as [r | n k IH]; intros Q ms mo HT.
  - destruct HT as (_ & Hl & _). destruct (leaves_unreachable_m_ret node nstep r mo Hl).
  - destruct HT as (Ht & Hl & Hh & Hinv & Hsf).
    cbn in Ht. destruct Ht as (ms1 & Hm & Hat & Hk).
    destruct (nsc_progress NS n ms1 mo Hat Hh Hinv (proj1 Hsf))
      as [(rsp & mo' & evs & Hst) | (code & mo' & Hex)].
    + destruct (tree_at_step_cfg NS n k Q ms1 mo rsp mo' evs Hat Hk Hl Hh Hinv Hsf Hst) as [HT' _].
      destruct (IH rsp Q (nret ms1 rsp) mo' HT') as (full' & Hfull').
      exists (evs ++ full'). cbn. right. exists rsp, mo', evs, full'. repeat split; assumption.
    + exists [ExitEv code (m_fs mo')]. cbn. left. exists code, mo'. split; [assumption | reflexivity].
Qed.

Definition run_inv_cfg {R} Q (c : config) : Prop :=
  (exists t : itree node R, TreeAt t Q (cfg_ms c) (cfg_model c))
  \/ m_halted (cfg_model c) <> None.

Lemma run_inv_sstep_cfg : node_sound_cfg -> forall {R} Q c evs X,
  run_inv_cfg (R:=R) Q c -> sstep_cfg segs cfg c evs X ->
  exists c', X = SNext c' /\ run_inv_cfg (R:=R) Q c'.
Proof.
  intros NS R Q [ms mo] evs X Hg Hss. destruct Hg as [(t & HT) | Hh]; cbn in *.
  - destruct (impl_sstep_inv_cfg NS t Q ms mo evs X HT Hss)
      as [(ms' & -> & _ & _ & HT') | [(n & k & rsp & mo' & _ & _ & -> & _ & HT')
         | (n & k & code & mo' & _ & _ & -> & _ & _ & Hh')]].
    + eexists; split; [reflexivity |]. left. exists t. exact HT'.
    + eexists; split; [reflexivity |]. left. exists (k rsp). exact HT'.
    + eexists; split; [reflexivity |]. right. cbn. congruence.
  - exfalso. apply Hh. eapply sstep_cfg_not_halted'; eassumption.
Qed.

Lemma run_inv_star_cfg : node_sound_cfg -> forall {R} Q c tr c',
  star_cfg segs cfg c tr c' -> run_inv_cfg (R:=R) Q c -> run_inv_cfg (R:=R) Q c'.
Proof.
  intros NS R Q c tr c' Hstar. induction Hstar as [c | c1 evs c2 tr c3 Hss Hstar IH]; intros Hg; [exact Hg |].
  destruct (run_inv_sstep_cfg NS Q c1 evs (SNext c2) Hg Hss) as (c2' & E & Hg'). inversion E; subst. auto.
Qed.

Lemma star_ttrace_prefix_cfg : node_sound_cfg -> forall {R} Q c tr c',
  star_cfg segs cfg c tr c' ->
  forall (t : itree node R) ms mo, c = mkCfg ms mo -> TreeAt t Q ms mo ->
  exists full, ttrace nstep nexit t mo full /\ is_prefix tr full.
Proof.
  intros NS R Q c tr c' Hstar.
  induction Hstar as [c | c1 evs c2 tr c3 Hss Hstar IH]; intros t ms mo -> HT.
  - destruct (ttrace_exists_cfg NS t Q ms mo HT) as (full & Hf).
    exists full. split; [exact Hf | apply is_prefix_nil].
  - destruct (impl_sstep_inv_cfg NS t Q ms mo evs (SNext c2) HT Hss)
      as [(ms' & E & -> & _ & HT') | [(n & k & rsp & mo' & -> & Hat & E & Hst & HT')
         | (n & k & code & mo' & -> & Hat & E & Hex & -> & Hh')]]; inversion E; subst.
    + exact (IH t ms' mo eq_refl HT').
    + destruct (IH (k rsp) (nret ms rsp) mo' eq_refl HT') as (full' & Hf' & Hp').
      exists (evs ++ full'). split.
      * cbn. right. exists rsp, mo', evs, full'. repeat split; assumption.
      * apply is_prefix_app_l. exact Hp'.
    + destruct (star_cfg_halted_nil ms mo' tr c3) as [-> _]; [congruence | exact Hstar |].
      exists [ExitEv code (m_fs mo')]. split.
      * cbn. left. exists code, mo'. split; [assumption | reflexivity].
      * cbn. split; [reflexivity | exact I].
Qed.

Lemma ttrace_star_cfg : node_sound_cfg -> forall {R} (t : itree node R) Q ms mo full,
  ttrace nstep nexit t mo full -> TreeAt t Q ms mo ->
  exists c', star_cfg segs cfg (mkCfg ms mo) full c'.
Proof.
  intros NS R t. induction t as [r | n k IH]; intros Q ms mo full Hf HT.
  - destruct HT as (_ & Hl & _). destruct (leaves_unreachable_m_ret node nstep r mo Hl).
  - destruct HT as (Ht & Hl & Hh & Hinv & Hsf).
    cbn in Ht. destruct Ht as (ms1 & Hm & Hat & Hk).
    pose proof (msteps_star_cfg ms ms1 mo Hh (nsc_nolazy NS mo Hinv) Hm) as Hs0.
    cbn in Hf. destruct Hf as [(code & mo' & Hex & ->) | (rsp & mo' & evs & tr' & Hst & Hf' & ->)].
    + destruct (nsc_exit NS n ms1 mo code mo' Hat Hh Hinv (proj1 Hsf) Hex) as (_ & Hss).
      exists (mkCfg ms1 mo'). change [ExitEv code (m_fs mo')] with ([] ++ [ExitEv code (m_fs mo')]).
      eapply star_cfg_trans; [exact Hs0 |]. apply star_cfg_one. exact Hss.
    + destruct (tree_at_step_cfg NS n k Q ms1 mo rsp mo' evs Hat Hk Hl Hh Hinv Hsf Hst) as [HT' Hss].
      destruct (IH rsp Q (nret ms1 rsp) mo' tr' Hf' HT') as (c' & Hs').
      exists c'. change (evs ++ tr') with ([] ++ (evs ++ tr')).
      eapply star_cfg_trans; [exact Hs0 |]. eapply star_cfg_step; [exact Hss | exact Hs'].
Qed.

Theorem impl_run_traces2_cfg : node_sound_cfg -> forall {R} (t : itree node R) Q ms mo,
  impl segs at_node t Q ms -> leaves_unreachable_m nstep t mo -> m_halted mo = None -> minv mo ->
  tsafe nstep nsafe t mo ->
  forall tr, obs_trace_cfg segs cfg (mkCfg ms mo) tr <->
             exists full, ttrace nstep nexit t mo full /\ is_prefix tr full.
Proof.
  intros NS R t Q ms mo Ht Hl Hh Hinv Hsf tr.
  assert (HT : TreeAt t Q ms mo) by (repeat split; assumption). split.
  - intros (tr' & c & Hstar & Hp).
    destruct (star_ttrace_prefix_cfg NS Q (mkCfg ms mo) tr' c Hstar t ms mo eq_refl HT) as (full & Hf & Hp').
    exists full. split; [exact Hf | eapply is_prefix_trans; eassumption].
  - intros (full & Hf & Hp).
    destruct (ttrace_star_cfg NS t Q ms mo full Hf HT) as (c' & Hs).
    exists full, c'. split; assumption.
Qed.

Theorem impl_run_safe2_cfg : node_sound_cfg -> forall {R} (t : itree node R) Q ms mo,
  impl segs at_node t Q ms -> leaves_unreachable_m nstep t mo -> m_halted mo = None -> minv mo ->
  tsafe nstep nsafe t mo ->
  ~ reaches_error_cfg segs cfg (mkCfg ms mo).
Proof.
  intros NS R t Q ms mo Ht Hl Hh Hinv Hsf (tr & c & evs & Hstar & Hss).
  assert (Hg : run_inv_cfg (R:=R) Q c).
  { eapply run_inv_star_cfg; [exact NS | exact Hstar |]. left. exists t. cbn. repeat split; assumption. }
  destruct (run_inv_sstep_cfg NS Q c evs SError Hg Hss) as (c' & E & _). discriminate E.
Qed.

Theorem impl_run_modeled2_cfg : node_sound_cfg -> forall {R} (t : itree node R) Q ms mo,
  impl segs at_node t Q ms -> leaves_unreachable_m nstep t mo -> m_halted mo = None -> minv mo ->
  tsafe nstep nsafe t mo ->
  ~ reaches_unmodeled_cfg segs cfg (mkCfg ms mo).
Proof.
  intros NS R t Q ms mo Ht Hl Hh Hinv Hsf Hun.
  apply (impl_run_safe2_cfg NS t Q ms mo Ht Hl Hh Hinv Hsf).
  exact (reaches_unmodeled_cfg_reaches_error_cfg segs cfg _ Hun).
Qed.

(* -------------------------------------------------------------------------
   Halting (Lib.Halts over the filtered relation)
   ------------------------------------------------------------------------- *)

Lemma sstep_cfg_exit_event_not_killed : forall c code fs c',
  sstep_cfg segs cfg c [ExitEv code fs] (SNext c') ->
  m_halted (cfg_model c') = Some code ->
  m_killed (cfg_model c') = None.
Proof.
  intros c code fs c' Hss Hh.
  exact (sstep_exit_event_not_killed segs c code fs c' (sstep_cfg_sub segs cfg _ _ _ Hss) Hh).
Qed.

Theorem tree_at_must_exit_cfg : node_sound_cfg -> forall (S : list word) {R} (t : itree node R) Q ms mo,
  (forall n mo1 code mo2, nexit n mo1 code mo2 -> In code S) ->
  TreeAt t Q ms mo ->
  must_exit_in_at_cfg cfg segs S (mkCfg ms mo).
Proof.
  intros NS S R t. induction t as [r | n k IH]; intros Q ms mo HS HT.
  - destruct HT as (_ & Hl & _). destruct (leaves_unreachable_m_ret node nstep r mo Hl).
  - pose proof HT as HT0. destruct HT as (Ht & Hl & Hh & Hinv & Hsf).
    cbn in Ht. destruct Ht as (ms1 & Hm & Hat & Hk).
    assert (MAIN : forall msx, msteps segs msx ms1 -> must_exit_in_at_cfg cfg segs S (mkCfg msx mo)).
    { intros msx Hmx. induction Hmx as [msx | msx msa msb Hstep Hrest IHm].
      - assert (HTx : TreeAt (Vis n k) Q msx mo).
        { split; [| split; [exact Hl | split; [exact Hh | split; [exact Hinv | exact Hsf]]]].
          cbn. exists msx. split; [apply msteps_refl |]. split; [exact Hat | exact Hk]. }
        apply must_exit_in_at_cfg_running.
        + exact Hh.
        + destruct (nsc_progress NS n msx mo Hat Hh Hinv (proj1 Hsf))
            as [(rsp & mo' & evs & Hst) | (code & mo' & Hex)].
          * destruct (nsc_sound NS n msx mo rsp mo' evs Hat Hh Hinv (proj1 Hsf) Hst) as (_ & _ & Hss).
            exists evs, (SNext (mkCfg (nret msx rsp) mo')). exact Hss.
          * destruct (nsc_exit NS n msx mo code mo' Hat Hh Hinv (proj1 Hsf) Hex) as (_ & Hss).
            exists [ExitEv code (m_fs mo')], (SNext (mkCfg msx mo')). exact Hss.
        + intros evs Herr.
          destruct (impl_sstep_inv_cfg NS (Vis n k) Q msx mo evs SError HTx Herr)
            as [(ms' & E & _) | [(n' & k' & rsp & mo' & _ & _ & E & _) | (n' & k' & code & mo' & _ & _ & E & _)]];
            discriminate E.
        + intros evs c' Hss.
          destruct (impl_sstep_inv_cfg NS (Vis n k) Q msx mo evs (SNext c') HTx Hss)
            as [(ms' & E & _ & Hms & _) | [(n' & k' & rsp & mo' & Et & _ & E & Hst & HT')
               | (n' & k' & code & mo' & Et & _ & E & Hex & Hevs & Hh')]].
          * exfalso. pose proof (mstep_not_svc segs msx ms' Hms) as Hn.
            exact (nsc_pending NS n msx Hat Hn).
          * injection Et as En Ek. subst n' k'. injection E as ->.
            apply (IH rsp Q (nret msx rsp) mo' HS HT').
          * injection Et as En Ek. subst n' k'. injection E as ->. subst evs.
            apply (must_exit_in_at_cfg_halted cfg segs S (mkCfg msx mo') code).
            -- exact Hh'.
            -- exact (HS n mo code mo' Hex).
            -- exact (sstep_cfg_exit_event_not_killed (mkCfg msx mo) code (m_fs mo') (mkCfg msx mo') Hss Hh').
      - assert (HTx : TreeAt (Vis n k) Q msx mo).
        { split; [| split; [exact Hl | split; [exact Hh | split; [exact Hinv | exact Hsf]]]].
          cbn. exists msb. split; [eapply msteps_cons; eassumption |]. split; [exact Hat | exact Hk]. }
        apply must_exit_in_at_cfg_running.
        + exact Hh.
        + exists [], (SNext (mkCfg msa mo)).
          apply mstep_sstep_cfg; [exact Hh | exact (nsc_nolazy NS mo Hinv) | exact Hstep].
        + intros evs Herr.
          destruct (impl_sstep_inv_cfg NS (Vis n k) Q msx mo evs SError HTx Herr)
            as [(ms' & E & _) | [(n' & k' & rsp & mo' & _ & _ & E & _) | (n' & k' & code & mo' & _ & _ & E & _)]];
            discriminate E.
        + intros evs c' Hss.
          destruct (impl_sstep_inv_cfg NS (Vis n k) Q msx mo evs (SNext c') HTx Hss)
            as [(ms' & E & _ & Hms & _) | [(n' & k' & rsp & mo' & Et & Hat' & _) | (n' & k' & code & mo' & Et & Hat' & _)]].
          * injection E as ->. rewrite (mstep_det segs msx ms' msa Hms Hstep). exact (IHm Hm Hat Hk).
          * exfalso. exact (nsc_pending NS n' msx Hat' (mstep_not_svc segs msx msa Hstep)).
          * exfalso. exact (nsc_pending NS n' msx Hat' (mstep_not_svc segs msx msa Hstep)). }
    exact (MAIN ms Hm).
Qed.

Theorem impl_run_must_exit2_cfg : node_sound_cfg ->
  forall (S : list word) {R} (t : itree node R) Q ms mo,
  impl segs at_node t Q ms -> leaves_unreachable_m nstep t mo -> m_halted mo = None -> minv mo ->
  tsafe nstep nsafe t mo ->
  (forall n mo1 code mo2, nexit n mo1 code mo2 -> In code S) ->
  must_exit_in_at_cfg cfg segs S (mkCfg ms mo).
Proof.
  intros NS S R t Q ms mo Ht Hl Hh Hinv Hsf HS.
  apply (tree_at_must_exit_cfg NS S t Q ms mo HS).
  split; [exact Ht | split; [exact Hl | split; [exact Hh | split; [exact Hinv | exact Hsf]]]].
Qed.

End ITreeFO.
