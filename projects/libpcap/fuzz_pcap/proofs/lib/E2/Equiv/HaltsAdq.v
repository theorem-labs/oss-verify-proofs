(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Exec ITree Nodes RegsEquiv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2 Require Import TopLevel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Eqv.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

#[using="Type"] Lemma must_exit_in_at_cfg_eqv : forall S c,
  must_exit_in_at_cfg cfg segs S c -> forall c', cfg_eqv c c' -> must_exit_in_at_cfg cfg segs S c'.
Proof.
  intros S c H. induction H as [c code Hh Hin Hk | c Hnone Hprog Hnoerr Hnext IH]; intros c' Heqv.
  - destruct Heqv as [_ Hm]. apply (must_exit_in_at_cfg_halted cfg segs S c' code); [rewrite <- Hm; exact Hh | exact Hin | rewrite <- Hm; exact Hk].
  - pose proof (cfg_eqv_sym _ _ Heqv) as Heqv'.
    apply must_exit_in_at_cfg_running.
    + destruct Heqv as [_ Hm]. rewrite <- Hm. exact Hnone.
    + destruct Hprog as (evs & st & Hst).
      destruct (sstepC_cfg_eqv segs cfg c c' evs st Heqv Hst) as (X' & Hst' & _). exists evs, X'. exact Hst'.
    + intros evs Herr.
      destruct (sstepC_cfg_eqv segs cfg c' c evs SError Heqv' Herr) as (X & HstX & HX).
      destruct X as [d|]; cbn in HX; [contradiction|]. exact (Hnoerr evs HstX).
    + intros evs d' Hst'.
      destruct (sstepC_cfg_eqv segs cfg c' c evs (SNext d') Heqv' Hst') as (X & HstX & HX).
      destruct X as [d|]; cbn in HX; [|contradiction].
      apply (IH evs d HstX d'). apply cfg_eqv_sym. exact HX.
Qed.
End Eqv.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MustExitTree.
Variable node : Type.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable at_node : node -> machine_state -> Prop.
Variable npeek : node -> option (machine_state -> resp).
Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit : node -> Model -> word -> Model -> Prop.
Variable minv : Model -> Prop.
Variable nsafe : node -> Model -> Prop.
Hypothesis NS : node_sound node segs cfg at_node npeek nstep nexit minv nsafe.
(* [comment removed for export] *)
Hypothesis NK : forall n mo code mo', nexit n mo code mo' -> m_killed mo' = None.

Notation implX := (impl segs at_node npeek).
Notation itreeX := (itree node).

(* [comment removed for export] *)
Fixpoint exits_in {R} (t : itreeX R) (mo : Model) (S : word -> Prop) : Prop :=
  match t with
  | Ret _ => True
  | Vis n k => (forall code mo', nexit n mo code mo' -> S code)
               /\ (forall rsp mo' evs, nstep n mo rsp mo' evs -> exits_in (k rsp) mo' S)
  end.

#[using="Type"] Lemma exits_in_mono : forall {R} (t : itreeX R) mo (S S' : word -> Prop),
  (forall c, S c -> S' c) -> exits_in t mo S -> exits_in t mo S'.
Proof.
  intros R t. induction t as [r|n k IH]; intros mo S S' HS H; cbn in *; [exact I|].
  destruct H as [H1 H2]. split; [intros code mo' Hx; apply HS; eapply H1; exact Hx|].
  intros rsp mo' evs Hst. eapply IH; [exact HS| eapply H2; exact Hst].
Qed.

#[using="Type"] Lemma exits_in_bind : forall {A B} (t : itreeX A) (f : A -> itreeX B) mo S,
  exits_in (ITree.bind node t f) mo S <->
  exits_in t mo S /\ (forall tr r mo', tpath nstep t mo tr r mo' -> exits_in (f r) mo' S).
Proof.
  intros A B t. induction t as [r|n k IH]; intros f mo S; cbn in *.
  - split.
    + intros H. split; [exact I|]. intros tr r0 mo' (<- & -> & _). exact H.
    + intros [_ H]. apply (H [] r mo). repeat split; reflexivity.
  - split.
    + intros [Hn Hk]. split.
      * split; [exact Hn|]. intros rsp mo' evs Hst. exact (proj1 (proj1 (IH rsp f mo' S) (Hk _ _ _ Hst))).
      * intros tr r mo' (rsp & mo1 & evs & tr' & Hst & Hp & ->).
        exact (proj2 (proj1 (IH rsp f mo1 S) (Hk _ _ _ Hst)) tr' r mo' Hp).
    + intros [[Hn Hk] Hf]. split; [exact Hn|]. intros rsp mo' evs Hst.
      apply (proj2 (IH rsp f mo' S)). split; [eapply Hk; eassumption|].
      intros tr r mo'' Hp. apply (Hf (evs ++ tr)). exists rsp, mo', evs, tr. repeat split; assumption.
Qed.

(* [comment removed for export] *)
#[using="node at_node npeek nstep nexit nsafe NS"] Lemma must_exit_in_at_msteps : forall S ms ms1 mo,
  m_halted mo = None -> minv mo ->
  msteps segs ms ms1 ->
  must_exit_in_at_cfg cfg segs S (mkCfg ms1 mo) ->
  must_exit_in_at_cfg cfg segs S (mkCfg ms mo).
Proof.
  intros S ms ms1 mo Hh Hinv Hm. induction Hm as [ms|ms msa ms2 H1 H2 IH]; intros Hend.
  - exact Hend.
  - pose proof (ns_nolazy _ _ _ _ _ _ _ _ _ NS mo Hinv) as Hl.
    apply must_exit_in_at_cfg_running.
    + exact Hh.
    + exists [], (SNext (mkCfg msa mo)). apply (mstep_sstep segs cfg); assumption.
    + intros evs Herr. destruct (sstep_mstep_inv segs cfg ms mo msa evs SError Hl H1 Herr) as [_ E]. discriminate E.
    + intros evs c' Hst. destruct (sstep_mstep_inv segs cfg ms mo msa evs (SNext c') Hl H1 Hst) as [_ E].
      injection E as E. subst c'. apply IH. exact Hend.
Qed.

#[using="NS NK"] Theorem impl_must_exit_in : forall {R} (t : itreeX R) Q ms mo (S : list word),
  implX t Q ms ->
  leaves_unreachable_m nstep t mo -> m_halted mo = None -> minv mo -> tsafe nstep nsafe t mo ->
  exits_in t mo (fun c => In c S) ->
  must_exit_in_at_cfg cfg segs S (mkCfg ms mo).
Proof.
  intros R t. induction t as [r|n k IH]; intros Q ms mo S Ht Hl Hh Hinv Hsf Hex.
  - exfalso. exact (leaves_unreachable_m_ret _ nstep _ _ Hl).
  - cbn in Ht. destruct Ht as (ms1 & Hm & Hcase).
    apply (must_exit_in_at_msteps S ms ms1 mo Hh Hinv Hm).
    destruct Hsf as [Hns Hsfk]. destruct Hex as [HexK Hexk].
    destruct Hcase as [[Hat Hk]|(f & Hn & Hk)].
    + (* [comment removed for export] *)
      apply must_exit_in_at_cfg_running.
      * exact Hh.
      * destruct (ns_progress _ _ _ _ _ _ _ _ _ NS n ms1 mo Hat Hh Hinv Hns)
          as [(rsp & mo' & evs & Hst)|(code & mo' & Hexit)].
        -- destruct (ns_sound _ _ _ _ _ _ _ _ _ NS n ms1 mo rsp mo' evs Hat Hh Hinv Hns Hst) as (_ & _ & Hss). eauto.
        -- destruct (ns_exit _ _ _ _ _ _ _ _ _ NS n ms1 mo code mo' Hat Hh Hinv Hns Hexit) as (_ & Hss). eauto.
      * intros evs Herr.
        destruct (ns_complete _ _ _ _ _ _ _ _ _ NS n ms1 mo evs SError Hat Hh Hinv Hns Herr)
          as [(rsp & mo' & E & _)|(code & mo' & E & _)]; discriminate E.
      * intros evs c' Hst.
        destruct (ns_complete _ _ _ _ _ _ _ _ _ NS n ms1 mo evs (SNext c') Hat Hh Hinv Hns Hst)
          as [(rsp & mo' & E & Hnst)|(code & mo' & E & Hexit & _)].
        -- injection E as ->.
           destruct (ns_sound _ _ _ _ _ _ _ _ _ NS n ms1 mo rsp mo' evs Hat Hh Hinv Hns Hnst) as (Hh' & Hinv' & _).
           apply (IH rsp Q (nret ms1 rsp) mo' S (Hk rsp)).
           ++ eapply leaves_unreachable_m_step; eassumption.
           ++ exact Hh'.
           ++ exact Hinv'.
           ++ eapply Hsfk; eassumption.
           ++ eapply Hexk; eassumption.
        -- injection E as ->.
           destruct (ns_exit _ _ _ _ _ _ _ _ _ NS n ms1 mo code mo' Hat Hh Hinv Hns Hexit) as (Hh' & _).
           apply (must_exit_in_at_cfg_halted cfg segs S (mkCfg ms1 mo') code); cbn [cfg_model].
           ++ exact Hh'.
           ++ eapply HexK; eassumption.
           ++ eapply NK; eassumption.
    + (* [comment removed for export] *)
      pose proof (ns_peek _ _ _ _ _ _ _ _ _ NS n f ms1 mo Hn) as Hst.
      apply (IH (f ms1) Q ms1 mo S Hk).
      * eapply leaves_unreachable_m_step; eassumption.
      * exact Hh.
      * exact Hinv.
      * eapply Hsfk; eassumption.
      * eapply Hexk; eassumption.
Qed.
End MustExitTree.

Arguments exits_in {node} nstep nexit {R} t mo S.

(* [comment removed for export] *)
Section ExitsExc.
Variable node : Type.
Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit : node -> Model -> word -> Model -> Prop.
Import ITree.Exc.

#[using="Type"] Lemma exits_in_ebind : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) mo S,
  exits_in nstep nexit (ebind t f) mo S <->
  exits_in nstep nexit t mo S /\ (forall tr a mo', tpath nstep t mo tr (Ok a) mo' -> exits_in nstep nexit (f a) mo' S).
Proof.
  intros A B t f mo S. unfold ebind. rewrite exits_in_bind. split.
  - intros [Ht Hf]. split; [exact Ht|]. intros tr a mo' Hp. exact (Hf tr (Ok a) mo' Hp).
  - intros [Ht Hf]. split; [exact Ht|]. intros tr [|a] mo' Hp; [exact I|]. exact (Hf tr a mo' Hp).
Qed.
End ExitsExc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma refusal_decided_classic : forall cfg i m, refusal_decided cfg i m.
Proof.
  intros cfg i m _.
  destruct (classic (exists eff' m' evs', Specs.syscall_spec i m (Monad.Ok eff' m' evs') /\ refusal_b i m (eff_ret eff') = false)) as [H|H].
  - left. exact H.
  - right. intros eff' m' evs' Hs. destruct (refusal_b i m (eff_ret eff')) eqn:E; [reflexivity|].
    exfalso. apply H. exists eff', m', evs'. split; [exact Hs| exact E].
Qed.

Lemma decided_from_classic : forall cfg segs c, decided_from cfg segs c.
Proof. intros cfg segs c tr c' x8 _ _. apply refusal_decided_classic. Qed.

Lemma must_exit_in_at_cfg_down : forall cfg1 cfg2 segs S c,
  cfg_le cfg1 cfg2 -> must_exit_in_at_cfg cfg2 segs S c -> must_exit_in_at_cfg cfg1 segs S c.
Proof.
  intros cfg1 cfg2 segs S c Hle H.
  exact (must_exit_in_at_cfg_mono cfg1 cfg2 segs S c Hle (decided_from_classic cfg1 segs c) H).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nexit_nokill : forall n mo code mo', nexit n mo code mo' -> m_killed mo' = None.
Proof.
  intros n mo code mo' H. destruct n; cbn in H; try contradiction.
  destruct H as [_ ->]. apply m_killed_with_halted.
Qed.

(* [comment removed for export] *)
Lemma nexit_code : forall n mo code mo', nexit n mo code mo' ->
  exists c, n = NExit c /\ code = bv_and (Z_to_bv 64 c) (Z_to_bv 64 255).
Proof.
  intros n mo code mo' H. destruct n; cbn in H; try contradiction.
  destruct H as [-> _]. eexists. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma must_exit_of_tree_CFG : forall {R : Type} segs pc ph lim (t : itree node R) (Q : R -> machine_state -> Prop) en inp (S : list word),
  impl segs (at_node segs) (npeek segs) t Q (ms0 segs pc ph en inp) ->
  leaves_unreachable_m nstep t (mo0 segs lim en inp) ->
  tsafe nstep nsafe t (mo0 segs lim en inp) ->
  exits_in nstep nexit t (mo0 segs lim en inp) (fun c => In c S) ->
  valid_input inp ->
  must_exit_in_at_cfg CFG segs S (mkCfg (ms0 segs pc ph en inp) (mo0 segs lim en inp)).
Proof.
  intros R segs pc ph lim t Q en inp S Himpl Hleaves Hsafe Hex Hvi.
  exact (impl_must_exit_in node segs CFG (at_node segs) (npeek segs) nstep nexit minv nsafe
           (nodes_sound segs) nexit_nokill t Q _ _ S Himpl Hleaves (mo0_not_halted _ _ _ _)
           (mo0_minv segs lim en inp Hvi) Hsafe Hex).
Qed.

(* [comment removed for export] *)
Theorem must_exit_of_tree : forall {R : Type} segs pc ph lim (t : itree node R) (Q : R -> machine_state -> Prop) en inp (S : list word),
  impl segs (at_node segs) (npeek segs) t Q (ms0 segs pc ph en inp) ->
  leaves_unreachable_m nstep t (mo0 segs lim en inp) ->
  tsafe nstep nsafe t (mo0 segs lim en inp) ->
  exits_in nstep nexit t (mo0 segs lim en inp) (fun c => In c S) ->
  valid_input inp ->
  must_exit_in_scfg forced_only_cfg S (mkImage segs pc ph) lim en inp.
Proof.
  intros R segs pc ph lim t Q en inp S Himpl Hleaves Hsafe Hex Hvi.
  pose proof (must_exit_of_tree_CFG segs pc ph lim t Q en inp S Himpl Hleaves Hsafe Hex Hvi) as H.
  destruct en as [sp brk mb rnd]. unfold must_exit_in_scfg.
  change (init_config segs pc ph sp brk mb rnd lim inp)
    with (init_config segs pc ph (en_sp (mkEntry sp brk mb rnd)) (en_brk (mkEntry sp brk mb rnd))
                      (en_mmap_base (mkEntry sp brk mb rnd)) (en_draw (mkEntry sp brk mb rnd)) lim inp).
  rewrite init_config_eq.
  apply (must_exit_in_at_cfg_down forced_only_cfg CFG segs S _ (forced_only_cfg_least CFG)).
  apply (must_exit_in_at_cfg_eqv segs CFG S _ H).
  split; [|reflexivity]. cbn [cfg_ms]. apply ms_eqv_sym. apply init_machine_state_eqv.
Qed.

(* [comment removed for export] *)
Theorem halts_of_tree : forall {R : Type} segs pc ph lim (S : list word) (t : prog_tree R) (Q : R -> machine_state -> Prop),
  tree_ok segs pc ph lim t Q ->
  (forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
     exits_in nstep nexit (t inp en) (mo0 segs lim en inp) (fun c => In c S)) ->
  halts_allowed_T_scfg_budgets forced_only_cfg lim S (mkImage segs pc ph).
Proof.
  intros R segs pc ph lim S t Q HT HX en inp Hen Hvi _.
  destruct (HT en inp Hen Hvi) as (Himpl & Hleaves & Hsafe).
  exact (must_exit_of_tree segs pc ph lim (t inp en) Q en inp S Himpl Hleaves Hsafe (HX en inp Hen Hvi) Hvi).
Qed.
