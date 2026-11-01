(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import SimInv ExitSim CatSim MmapSim AllocSim AllocSim2 WallSim.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Export CfgRun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

Lemma is_prefix_app_r {A} : forall (l m a : list A),
  is_prefix a l -> is_prefix a (l ++ m).
Proof.
  induction l as [|x l IH]; intros m a H.
  - destruct a; [apply is_prefix_nil | cbn in H; contradiction].
  - destruct a as [|y a]; cbn in *; [exact I|].
    destruct H as [-> H]. split; [reflexivity | apply IH; exact H].
Qed.

Lemma is_prefix_app_split {A} : forall (l a b : list A),
  is_prefix b (l ++ a) ->
  is_prefix b l \/ exists b', b = l ++ b' /\ is_prefix b' a.
Proof.
  induction l as [|x l IH]; intros a b H.
  - right. exists b. split; [reflexivity | exact H].
  - destruct b as [|y b]; cbn in H; [left; exact I|].
    destruct H as [-> H]. destruct (IH a b H) as [Hp | (b' & -> & Hp)].
    + left. cbn. split; [reflexivity | exact Hp].
    + right. exists b'. split; [reflexivity | exact Hp].
Qed.

Lemma is_prefix_nil_r {A} : forall (a : list A), is_prefix a [] -> a = [].
Proof. destruct a; cbn; [reflexivity | contradiction]. Qed.

Definition TSet := list event -> Prop.

Definition t_eq (T T' : TSet) : Prop := forall tr, T tr <-> T' tr.

Lemma t_eq_refl : forall T, t_eq T T. Proof. firstorder. Qed.
Lemma t_eq_sym : forall T T', t_eq T T' -> t_eq T' T. Proof. firstorder. Qed.
Lemma t_eq_trans : forall T1 T2 T3, t_eq T1 T2 -> t_eq T2 T3 -> t_eq T1 T3.
Proof. firstorder. Qed.

Definition t_nil : TSet := fun tr => tr = [].

Definition t_emit (evs : list event) (T : TSet) : TSet :=
  fun tr => is_prefix tr evs \/ exists tr', tr = evs ++ tr' /\ T tr'.

Definition t_alt {I : Type} (f : I -> TSet) : TSet := fun tr => exists i, f i tr.

Definition t_alt2 (A B : TSet) : TSet := fun tr => A tr \/ B tr.

Definition t_exit (code : word) (fs : Fs.Fs) : TSet :=
  t_emit [ExitEv code fs] t_nil.

Definition wr_index (buf : list byte) : Type :=
  {n : nat | (1 <= n)%nat /\ (n <= length buf)%nat}.

Definition wr_full (buf : list byte) (Hnb : (1 <= length buf)%nat)
    : wr_index buf :=
  exist _ (length buf) (conj Hnb (Nat.le_refl _)).

Definition t_write_ch (ch : word) (buf : list byte) (T : TSet) : TSet :=
  t_alt (fun i : wr_index buf =>
           t_emit (map (WriteEv ch) (firstn (proj1_sig i) buf)) T).

Definition t_writes_pick (bufs : list (list byte)) (T : TSet) : TSet :=
  fold_right (t_write_ch (Z_to_bv 64 1)) T bufs.

Lemma t_emit_nil_eq : forall T, T [] -> t_eq (t_emit [] T) T.
Proof.
  intros T H0 tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & HT)];
      [apply is_prefix_nil_r in Hp; subst tr; exact H0 | exact HT].
  - intro HT. right. exists tr. split; [reflexivity | exact HT].
Qed.

Lemma t_writes_pick_nil : forall T, t_writes_pick [] T = T. Proof. reflexivity. Qed.
Lemma t_writes_pick_cons : forall buf bufs T,
  t_writes_pick (buf :: bufs) T = t_write_ch (Z_to_bv 64 1) buf (t_writes_pick bufs T).
Proof. reflexivity. Qed.

Definition t_writes_ch (ch : word) (bufs : list (list byte)) (T : TSet) : TSet :=
  fold_right (fun buf acc => t_emit (map (WriteEv ch) buf) acc) T bufs.

Definition t_writes (bufs : list (list byte)) (T : TSet) : TSet :=
  t_writes_ch (Z_to_bv 64 1) bufs T.

Lemma t_writes_nil : forall T, t_writes [] T = T. Proof. reflexivity. Qed.
Lemma t_writes_cons : forall buf bufs T,
  t_writes (buf :: bufs) T
  = t_emit (map (WriteEv (Z_to_bv 64 1)) buf) (t_writes bufs T).
Proof. reflexivity. Qed.
Lemma t_writes_ch_cons : forall ch buf bufs T,
  t_writes_ch ch (buf :: bufs) T
  = t_emit (map (WriteEv ch) buf) (t_writes_ch ch bufs T).
Proof. reflexivity. Qed.

Lemma t_emit_has_nil : forall e T, t_emit e T [].
Proof. intros e T. left. apply is_prefix_nil. Qed.

Lemma t_writes_ch_exit_has_nil : forall ch bufs code fs,
  t_writes_ch ch bufs (t_exit code fs) [].
Proof.
  intros ch [|b bs] code fs; cbn [t_writes_ch fold_right];
    apply t_emit_has_nil.
Qed.

Lemma t_writes_ch_exit_iff : forall ch bufs code fs tr,
  t_writes_ch ch bufs (t_exit code fs) tr
  <-> is_prefix tr (wevents_ch ch bufs ++ [ExitEv code fs]).
Proof.
  intros ch bufs; induction bufs as [|buf bufs IH]; intros code fs tr.
  - cbn [wevents_ch app]. unfold t_writes_ch, fold_right, t_exit, t_emit, t_nil.
    split.
    + intros [H | (tr' & -> & ->)]; [exact H | rewrite app_nil_r; apply is_prefix_refl].
    + intro H. left. exact H.
  - rewrite t_writes_ch_cons. cbn [wevents_ch]. rewrite <- app_assoc.
    unfold t_emit at 1. split.
    + intros [H | (tr' & -> & Hc)].
      * apply is_prefix_app_r; exact H.
      * apply is_prefix_app_mono. apply IH. exact Hc.
    + intro H. apply is_prefix_app_split in H as [H | (tr' & -> & H)].
      * left; exact H.
      * right. exists tr'. split; [reflexivity | apply IH; exact H].
Qed.

Lemma t_writes_exit_iff : forall bufs code fs tr,
  t_writes bufs (t_exit code fs) tr
  <-> is_prefix tr (wevents bufs ++ [ExitEv code fs]).
Proof.
  intros bufs code fs tr. unfold t_writes.
  rewrite t_writes_ch_exit_iff, wevents_ch_fd1. reflexivity.
Qed.

Lemma t_alt_wall : forall (ch : word) (rest : list byte) (T : TSet),
  T [] -> (1 <= length rest)%nat ->
  t_eq (t_alt (fun i : wr_index rest =>
          t_emit (map (WriteEv ch) (firstn (proj1_sig i) rest))
                 (t_emit (map (WriteEv ch) (skipn (proj1_sig i) rest)) T)))
       (t_emit (map (WriteEv ch) rest) T).
Proof.
  intros ch rest T HT Hnb tr. split.
  - intros [[n [Hn1 Hn2]] Hi]. cbn [proj1_sig] in Hi.
    destruct Hi as [Hp | (tr1 & -> & Hi)].
    + left. eapply is_prefix_trans; [exact Hp|].
      rewrite <- (firstn_skipn n rest) at 2. rewrite map_app.
      apply is_prefix_app_r. apply is_prefix_refl.
    + destruct Hi as [Hp | (tr2 & -> & Ht)].
      * left.
        rewrite <- (firstn_skipn n rest) at 2. rewrite map_app.
        apply is_prefix_app_mono. exact Hp.
      * right. exists tr2. split; [|exact Ht].
        rewrite app_assoc, <- map_app, firstn_skipn. reflexivity.
  - intros [Hp | (tr' & -> & Ht)].
    + exists (wr_full rest Hnb). unfold wr_full. cbn [proj1_sig].
      rewrite firstn_all. left. exact Hp.
    + exists (wr_full rest Hnb). unfold wr_full. cbn [proj1_sig].
      rewrite firstn_all, skipn_all. right.
      exists tr'. split; [reflexivity|].
      cbn [map]. right. exists tr'. split; [reflexivity | exact Ht].
Qed.

Lemma t_writes_ch_pick_exit_iff : forall ch bufs code fs tr,
  Forall (fun b => (1 <= length b)%nat) bufs ->
  (fold_right (t_write_ch ch) (t_exit code fs) bufs tr
   <-> exists full, wpick ch bufs full /\
       is_prefix tr (full ++ [ExitEv code fs])).
Proof.
  intros ch bufs code fs tr Hall; revert tr;
    induction Hall as [|buf bufs Hnb Hall IH]; intros tr.
  - cbn [fold_right]. unfold t_exit, t_emit, t_nil.
    split.
    + intros [H | (tr' & -> & ->)].
      * exists []. split; [apply wp_nil | exact H].
      * exists []. split; [apply wp_nil|].
        rewrite app_nil_r. cbn [app]. apply is_prefix_refl.
    + intros (full & Hw & Hp). inversion Hw; subst full.
      left. exact Hp.
  - cbn [fold_right]. unfold t_write_ch at 1, t_alt at 1.
    split.
    + intros [[n [Hn1 Hn2]] Hi]. cbn [proj1_sig] in Hi.
      destruct Hi as [H | (tr' & -> & Hc)].
      * exists (map (WriteEv ch) (firstn n buf) ++ wevents_ch ch bufs).
        split; [apply wp_cons; [exact Hn1 | exact Hn2 | apply wpick_wevents; exact Hall]|].
        rewrite <- app_assoc.
        eapply is_prefix_trans; [exact H | apply is_prefix_app_r; apply is_prefix_refl].
      * apply IH in Hc. destruct Hc as (full & Hw & Hp).
        exists (map (WriteEv ch) (firstn n buf) ++ full).
        split; [apply wp_cons; assumption|].
        rewrite <- app_assoc. apply is_prefix_app_mono. exact Hp.
    + intros (full & Hw & Hp).
      inversion Hw as [|buf' bufs' n tr0 Hn1 Hn2 Hw0]; subst.
      rewrite <- app_assoc in Hp.
      apply is_prefix_app_split in Hp as [Hp | (tr' & -> & Hp)].
      * exists (exist _ n (conj Hn1 Hn2)). cbn [proj1_sig]. left. exact Hp.
      * exists (exist _ n (conj Hn1 Hn2)). cbn [proj1_sig]. right.
        exists tr'. split; [reflexivity|].
        apply IH. exists tr0. split; assumption.
Qed.

Lemma t_writes_pick_exit_iff : forall bufs code fs tr,
  Forall (fun b => (1 <= length b)%nat) bufs ->
  (t_writes_pick bufs (t_exit code fs) tr
   <-> exists full, wpick (Z_to_bv 64 1) bufs full /\
       is_prefix tr (full ++ [ExitEv code fs])).
Proof. intros. apply t_writes_ch_pick_exit_iff. assumption. Qed.

Lemma two_traces_t_alt2 : forall bf cf bs cs fs tr,
  t_alt2 (t_writes bf (t_exit cf fs)) (t_writes bs (t_exit cs fs)) tr
  <-> MmapSim.two_traces bf cf bs cs fs tr.
Proof.
  intros. unfold t_alt2, MmapSim.two_traces.
  rewrite !t_writes_exit_iff. reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.

Definition node_ok (c : config) (I : Type) (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstep_cfg segs ACFG c (evs i) (SNext (nx i)))
  /\ (forall e st, sstep_cfg segs ACFG c e st -> exists i, e = evs i /\ st = SNext (nx i)).
Definition node_ok_raw (c : config) (I : Type) (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstep segs c (evs i) (SNext (nx i)))
  /\ (forall e st, sstep segs c e st -> exists i, e = evs i /\ st = SNext (nx i)).
Lemma node_ok_of_transparent : forall c (I : Type) (evs : I -> list event) (nx : I -> config),
  node_ok_raw c I evs nx -> cfg_transparent segs c -> node_ok c I evs nx.
Proof.
  intros c I evs nx raw transp.
  destruct raw as [raw_moves raw_only].
  refine (conj (fun i => transp (evs i) (SNext (nx i)) (raw_moves i)) _).
  intros e st cfg_move.
  exact (raw_only e st (sstep_of_cfg segs c e st cfg_move)).
Qed.
Lemma node_ok_sstep : forall c (I : Type) (evs : I -> list event) (nx : I -> config) i,
  node_ok c I evs nx -> sstep segs c (evs i) (SNext (nx i)).
Proof.
  intros c I evs nx i node.
  exact (sstep_of_cfg segs c (evs i) (SNext (nx i)) (proj1 node i)).
Qed.

Inductive realizes : config -> TSet -> Prop :=
| rz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                   (T : I -> TSet) (i0 : I),
    node_ok c I evs nx ->
    (forall i, realizes (nx i) (T i)) ->
    realizes c (t_alt (fun i => t_emit (evs i) (T i)))
| rz_halt : forall c,
    m_halted (cfg_model c) <> None ->
    realizes c t_nil
| rz_conseq : forall c T T',
    realizes c T -> t_eq T T' -> realizes c T'.

Lemma realizes_nonempty : forall c T, realizes c T -> T [].
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

Lemma realizes_pclosed : forall c T, realizes c T ->
  forall tr tr', T tr -> is_prefix tr' tr -> T tr'.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros tr tr' HT Hp.
  - destruct HT as [i [Hpre | (tr0 & -> & HT0)]]; exists i.
    + left. eapply is_prefix_trans; eauto.
    + apply is_prefix_app_split in Hp as [Hp | (tr0' & -> & Hp)].
      * left. exact Hp.
      * right. exists tr0'. split; [reflexivity | eapply IH; eauto].
  - unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
  - apply Heq. eapply IH; [apply Heq; exact HT | exact Hp].
Qed.

Lemma realizes_star_only : forall c T, realizes c T ->
  forall tr c', star_cfg segs ACFG c tr c' -> T tr.
Proof.
  intros c T real.
  induction real as [c I evs nx Tk i0 node kids ih | c halt | c T0 T1 real ih same];
    intros tr c' run.
  - destruct node as [_ only]. revert only.
    destruct run as [c0 | c0 ev c1 rest c2 first rest_run]; intro only.
    + exists i0. left. apply is_prefix_nil.
    + destruct (only ev (SNext c1) first) as (i & ev_is & lands_at).
      injection lands_at as c1_is. subst ev c1.
      exists i. right. exists rest. split; [reflexivity|].
      exact (ih i rest c2 rest_run).
  - exact (proj1 (star_cfg_halted_nil segs c tr c' halt run)).
  - exact (proj1 (same tr) (ih tr c' run)).
Qed.

Lemma realizes_admits : forall c T, realizes c T ->
  forall tr, T tr -> obs_trace_cfg segs ACFG c tr.
Proof.
  intros c T real.
  induction real as [c I evs nx Tk i0 node kids ih | c halt | c T0 T1 real ih same];
    intros tr member.
  - destruct member as [i [short | (tail & tr_is & tail_in)]].
    + exists (evs i), (nx i).
      split; [apply star_cfg_one; exact (proj1 node i) | exact short].
    + destruct (ih i tail tail_in) as (full & cend & run & pre).
      subst tr. exists (evs i ++ full), cend. split.
      * exact (star_cfg_step segs ACFG c (evs i) (nx i) full cend (proj1 node i) run).
      * apply is_prefix_app_mono. exact pre.
  - unfold t_nil in member. subst tr. apply obs_trace_cfg_nil.
  - exact (ih tr (proj2 (same tr) member)).
Qed.

Theorem realizes_obs_iff : forall c T, realizes c T ->
  forall tr, obs_trace_cfg segs ACFG c tr <-> T tr.
Proof.
  intros c T real tr. split.
  2: exact (realizes_admits c T real tr).
  intros (full & cend & run & pre).
  exact (realizes_pclosed c T real full tr (realizes_star_only c T real full cend run) pre).
Qed.

Lemma sstep_halted_none : forall c e st,
  sstep segs c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.

Lemma realizes_step : forall c T e c',
  realizes c T -> sstep_cfg segs ACFG c e (SNext c') -> exists T', realizes c' T'.
Proof.
  intros c T e c' real. revert e c'.
  induction real as [c I evs nx Tk i0 node kids ih | c halt | c T0 T1 real ih same];
    intros e c' move.
  - destruct (proj2 node e (SNext c') move) as (i & _ & lands_at).
    injection lands_at as c'_is. subst c'. exists (Tk i). exact (kids i).
  - destruct (halt (sstep_cfg_halted_none segs c e (SNext c') move)).
  - exact (ih e c' move).
Qed.

Lemma realizes_no_sserror : forall c T e,
  realizes c T -> ~ sstep_cfg segs ACFG c e SError.
Proof.
  intros c T e real.
  induction real as [c I evs nx Tk i0 node kids ih | c halt | c T0 T1 real ih same];
    intro bad.
  - destruct (proj2 node e SError bad) as (i & _ & wrong). discriminate wrong.
  - exact (halt (sstep_cfg_halted_none segs c e SError bad)).
  - exact (ih bad).
Qed.

Definition rz_path (c : config) : Prop := exists T, realizes c T.

Lemma realizes_star : forall c T tr c',
  realizes c T -> star_cfg segs ACFG c tr c' -> exists T', realizes c' T'.
Proof.
  intros c T tr c' real run.
  refine (star_cfg_inv segs rz_path _ c tr c' (ex_intro _ T real) run).
  intros c1 evs c2 [T1 real1] move.
  exact (realizes_step c1 T1 evs c2 real1 move).
Qed.

Theorem realizes_no_error : forall c T, realizes c T -> ~ reaches_error_cfg segs ACFG c.
Proof.
  intros c T real (tr & cend & evs & run & bad).
  destruct (realizes_star c T tr cend real run) as [Tend real_end].
  exact (realizes_no_sserror cend Tend evs real_end bad).
Qed.

Lemma t_alt_unit : forall (f : unit -> TSet), t_eq (t_alt f) (f tt).
Proof.
  intros f tr. split; [intros [[] Hf]; exact Hf | intro Hf; exists tt; exact Hf].
Qed.

Lemma rz_silent1 : forall c c' T,
  node_ok c unit (fun _ => []) (fun _ => c') ->
  realizes c' T ->
  realizes c T.
Proof.
  intros c c' T Hnode Hc.
  apply (rz_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (rz_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply realizes_nonempty; exact Hc ].
Qed.

Lemma rz_emit1 : forall c c' e T,
  node_ok c unit (fun _ => e) (fun _ => c') ->
  realizes c' T ->
  realizes c (t_emit e T).
Proof.
  intros c c' e T Hnode Hc.
  apply (rz_conseq c (t_alt (fun _ : unit => t_emit e T))).
  - apply (rz_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode).
    intros []; exact Hc.
  - apply t_alt_unit.
Qed.

Lemma rz_alt2 : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
                       (a0 : IA) (b0 : IB),
  node_ok c (IA + IB) (fun _ => []) nx ->
  (forall i, realizes (nx (inl i)) A) ->
  (forall i, realizes (nx (inr i)) B) ->
  realizes c (t_alt2 A B).
Proof.
  intros c IA IB nx A B a0 b0 Hnode HA HB.
  assert (HA0 : A []) by (eapply realizes_nonempty; apply (HA a0)).
  assert (HB0 : B []) by (eapply realizes_nonempty; apply (HB b0)).
  apply (rz_conseq c
    (t_alt (fun i : IA + IB =>
              t_emit [] (match i with inl _ => A | inr _ => B end)))).
  - apply (rz_node c (IA + IB) (fun _ => []) nx
             (fun i => match i with inl _ => A | inr _ => B end) (inl a0) Hnode).
    intros [i|i]; [apply HA | apply HB].
  - intro tr. unfold t_alt2. split.
    + intros [[i|i] Hi];
        [ left; exact (proj1 (t_emit_nil_eq A HA0 tr) Hi)
        | right; exact (proj1 (t_emit_nil_eq B HB0 tr) Hi) ].
    + intros [H | H];
        [ exists (inl a0); exact (proj2 (t_emit_nil_eq A HA0 tr) H)
        | exists (inr b0); exact (proj2 (t_emit_nil_eq B HB0 tr) H) ].
Qed.

Lemma node_instr : forall ms model ms',
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  node_ok (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' live no_lazy idle runs.
  assert (acct : mi_account_step segs ms model = MachineOk (ms', model)).
  { rewrite (mi_account_step_no_lazy segs ms model no_lazy), runs. reflexivity. }
  apply node_ok_of_transparent; [| exact (transparent_instr segs ms model idle)].
  split.
  - intros _. exact (sstep_instr segs ms model ms' model live idle acct).
  - intros e st move. exists tt.
    inversion move; subst; first [split; [reflexivity | congruence] | congruence].
Qed.

Lemma rz_step : forall ms model ms' T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  realizes (mkCfg ms' model) T ->
  realizes (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  eapply rz_silent1; [apply node_instr; eassumption | exact Hc].
Qed.

Lemma rz_msteps : forall ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  realizes (mkCfg ms' model) T ->
  realizes (mkCfg ms model) T.
Proof.
  intros ms ms' model T Hh Hlazy Hms;
    induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
    intro Hc; [exact Hc|].
  eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
                  | apply IH; exact Hc].
Qed.

Lemma node_write1 : forall ms model x8 buf,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  node_ok (mkCfg ms model) (wr_index buf)
          (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
          (fun i => mkCfg (advance_past_svc
                             (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                          model).
Proof.
  intros ms model x8 buf live no_lazy fd1 pend is64 to_fd1 reads modeled nonempty.
  assert (transp : cfg_transparent segs (mkCfg ms model))
    by exact (transparent_nonalloc_no segs ms model x8 64 pend is64 eq_refl).
  split.
  - intros [n [lo hi]]. apply transp. cbn [proj1_sig].
    rewrite <- (apply_effect_copyins_no_write ms (len_word (firstn n buf)) [(ms_gpr ms 1, n)]).
    exact (sstep_syscall segs ms model x8 _ model model _ live pend
             (write1_ok_n segs ms x8 model buf n fd1 is64 to_fd1 reads modeled lo hi) live
             (materialize_model_accesses_no_lazy model _ no_lazy)).
  - intros e st move.
    pose proof (sstep_cfg_sys_inv segs ACFG ms model x8 e st pend move) as outcomes.
    cbv zeta in outcomes.
    destruct outcomes as
      [ (eff & model1 & evs0 & spec & _ & _ & landing)
      | [ (eff & model1 & evs0 & code & spec & halted1 & _ & _ & _)
      | [ (eff & model1 & evs0 & sig & spec & killed1 & _ & _)
      | (unmod & _ & _) ] ] ].
    + destruct (write1_ok_inv segs ms x8 model eff model1 evs0 buf fd1 is64 to_fd1 reads nonempty spec)
        as (n & lo & hi & eff_is & model1_is & evs0_is).
      subst eff model1 evs0.
      rewrite (materialize_model_accesses_no_lazy model _ no_lazy) in landing.
      destruct landing as [e_is st_is]. subst e st.
      exists (exist _ n (conj lo hi)). split; [reflexivity|].
      rewrite apply_effect_copyins_no_write. reflexivity.
    + destruct (write1_ok_inv segs ms x8 model eff model1 evs0 buf fd1 is64 to_fd1 reads nonempty spec)
        as (n & _ & _ & _ & model1_is & _).
      subst model1. rewrite live in halted1. discriminate halted1.
    + destruct (write1_ok_inv segs ms x8 model eff model1 evs0 buf fd1 is64 to_fd1 reads nonempty spec)
        as (n & _ & _ & _ & model1_is & _).
      subst model1. rewrite (m_killed_of_m_halted_none model live) in killed1. discriminate killed1.
    + destruct (write1_no_unmodeled segs ms x8 model buf fd1 is64 to_fd1 reads modeled nonempty unmod).
Qed.

Lemma rz_write1 : forall ms model x8 buf T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     realizes (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model) T) ->
  realizes (mkCfg ms model) (t_write_ch (Z_to_bv 64 1) buf T).
Proof.
  intros ms model x8 buf T Hh Hlazy Hfd Hsvc Hno Hg Hr Hbm Hnb Hc.
  unfold t_write_ch.
  apply (rz_node (mkCfg ms model) (wr_index buf)
           (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
           (fun i => mkCfg (advance_past_svc
                              (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                           model)
           (fun _ => T) (wr_full buf Hnb)).
  - apply (node_write1 ms model x8 buf); assumption.
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.

Lemma rz_exit : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  realizes (mkCfg ms model)
           (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros ms model x8 live pend exit_no.
  assert (transp : cfg_transparent segs (mkCfg ms model)).
  { destruct exit_no as [is93 | is94].
    - exact (transparent_nonalloc_no segs ms model x8 93 pend is93 eq_refl).
    - exact (transparent_nonalloc_no segs ms model x8 94 pend is94 eq_refl). }
  assert (spec : syscall_spec (sys_input segs ms x8) model
                   (Ok (mkEffect (Z_to_bv 64 0) [] [])
                       (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) [])).
  { apply (proj2 (syscall_spec_exit (sys_input segs ms x8) model _ exit_no)).
    rewrite (in_arg_sys_input segs ms x8 0) by lia.
    cbv [exit_spec bind set_halted modify ret_only pure].
    exists tt, (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model), [], [].
    split; [reflexivity | split; reflexivity]. }
  refine (rz_emit1 (mkCfg ms model)
            (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))
            [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)] t_nil _ _).
  2: { apply rz_halt. cbn [cfg_model]. rewrite m_halted_with_halted. discriminate. }
  split.
  - intros _. apply transp.
    pose proof (sstep_exit segs ms model x8 _ _ [] _ live pend spec
                  (m_halted_with_halted _ model) (m_killed_with_halted _ model)) as raw.
    rewrite m_fs_with_halted in raw. exact raw.
  - intros e st move.
    destruct (sstep_exit_inv segs ms model x8 e st live pend exit_no
                (sstep_of_cfg segs _ e st move)) as [e_is st_is].
    exists tt. exact (conj e_is st_is).
Qed.

Lemma rz_munmap : forall ms model x8 T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  realizes (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                  (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) T ->
  realizes (mkCfg ms model) T.
Proof.
  intros ms model x8 T live no_lazy pend is215 args after.
  refine (rz_silent1 _ _ T _ after).
  assert (alive1 : m_halted (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) = None).
  { rewrite munmap_model_halted. exact live. }
  assert (mat : materialize_model_accesses
                  (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
                  (syscall_effect_accesses (munmap_eff ms))
                = Some (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)).
  { apply materialize_model_accesses_no_lazy. apply munmap_model_no_lazy. exact no_lazy. }
  split.
  - intros _.
    exact (sstep_cfg_syscall segs ACFG ms model x8 (munmap_eff ms) _ _ [] live pend
             (munmap_ok segs ms x8 model is215 args)
             (acfg_nonspurious_no segs ms x8 215 model (munmap_eff ms) is215 eq_refl)
             alive1 mat).
  - intros e st move. exists tt.
    pose proof (sstep_cfg_sys_inv segs ACFG ms model x8 e st pend move) as outcomes.
    cbv zeta in outcomes.
    destruct outcomes as
      [ (eff & model1 & evs0 & spec & _ & _ & landing)
      | [ (eff & model1 & evs0 & code & spec & halted1 & _ & _ & _)
      | [ (eff & model1 & evs0 & sig & spec & killed1 & _ & _)
      | (unmod & _ & _) ] ] ];
      [ destruct (munmap_ok_inv segs ms x8 model eff model1 evs0 is215 args spec)
          as (eff_is & model1_is & evs0_is); subst eff model1 evs0
      | destruct (munmap_ok_inv segs ms x8 model eff model1 evs0 is215 args spec)
          as (_ & model1_is & _); subst model1
      | destruct (munmap_ok_inv segs ms x8 model eff model1 evs0 is215 args spec)
          as (_ & model1_is & _); subst model1
      | ].
    + rewrite mat in landing. exact landing.
    + rewrite alive1 in halted1. discriminate halted1.
    + rewrite (m_killed_of_m_halted_none _ alive1) in killed1. discriminate killed1.
    + destruct (munmap_no_unmodeled segs ms x8 model is215 args unmod).
Qed.
Lemma grant_not_refusal : forall ms model a,
  grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
  ret_in_errnos mmap_errnos a = false.
Proof.
  intros ms model a granted.
  destruct (grant_ok_unpack (ms_gpr ms 0) model a _ granted) as [aligned _].
  exact (ret_in_errnos_ENOMEM_aligned a aligned).
Qed.
Lemma node_mmap_grant : forall ms model x8,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
  node_ok (mkCfg ms model)
    {a : word | grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true}
    (fun _ => [])
    (fun i => match i with exist _ a _ =>
       mkCfg (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
             (mmap_model a (page_round_up (ms_gpr ms 1)) model) end).
Proof.
  intros ms model x8 live no_lazy pend is222 args [a0 granted0].
  assert (not_refused : forall a,
            grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
            refusal_b (sys_input segs ms x8) model a = false).
  { intros a granted.
    rewrite (refusal_b_222 (sys_input segs ms x8) model a is222).
    exact (grant_not_refusal ms model a granted). }
  split.
  - intros [a granted].
    apply (sstep_cfg_syscall_nonrefusal segs ACFG ms model x8 _
             (mmap_model a (page_round_up (ms_gpr ms 1)) model) _ [] live pend).
    + exact (mmap_succ_ok segs ms x8 model a is222 args granted).
    + exact (not_refused a granted).
    + rewrite mmap_model_halted. exact live.
    + apply materialize_model_accesses_no_lazy. rewrite mmap_model_lazy. exact no_lazy.
  - intros e st move.
    pose proof (sstep_cfg_sys_inv segs ACFG ms model x8 e st pend move) as outcomes.
    cbv zeta in outcomes.
    destruct outcomes as
      [ (eff & model1 & evs0 & spec & fair & _ & landing)
      | [ (eff & model1 & evs0 & code & spec & halted1 & _ & _ & _)
      | [ (eff & model1 & evs0 & sig & spec & killed1 & _ & _)
      | (unmod & _ & _) ] ] ].
    + destruct (mmap_ok_inv segs ms x8 model eff model1 evs0 is222 args spec)
        as [evs0_nil [(errno & listed & eff_is & _) | (a & granted & eff_is & model1_is)]].
      * subst eff. exfalso. apply fair.
        apply (refusal_spurious_of_grant ACFG _ model _
                 (mkEffect a0 [] [(a0, page_round_up (ms_gpr ms 1))])
                 (mmap_model a0 (page_round_up (ms_gpr ms 1)) model) []).
        -- exact (acfg_family_off_222 (sys_input segs ms x8) is222).
        -- rewrite (refusal_b_222 (sys_input segs ms x8) model _ is222).
           exact (ret_in_errnos_errno mmap_errnos errno listed).
        -- exact (mmap_succ_ok segs ms x8 model a0 is222 args granted0).
        -- exact (not_refused a0 granted0).
      * subst eff model1 evs0.
        rewrite (materialize_model_accesses_no_lazy _ _
                   (eq_trans (mmap_model_lazy a (page_round_up (ms_gpr ms 1)) model) no_lazy))
          in landing.
        destruct landing as [e_is st_is]. subst e st.
        exists (exist _ a granted). split; reflexivity.
    + destruct (mmap_ok_inv segs ms x8 model eff model1 evs0 is222 args spec)
        as [_ [(errno & _ & _ & model1_is) | (a & _ & _ & model1_is)]];
        subst model1; [ | rewrite mmap_model_halted in halted1 ];
        rewrite live in halted1; discriminate halted1.
    + destruct (mmap_ok_inv segs ms x8 model eff model1 evs0 is222 args spec)
        as [_ [(errno & _ & _ & model1_is) | (a & _ & _ & model1_is)]];
        subst model1.
      * rewrite (m_killed_of_m_halted_none model live) in killed1. discriminate killed1.
      * rewrite (m_killed_of_m_halted_none _ (eq_trans (mmap_model_halted _ _ model) live))
          in killed1.
        discriminate killed1.
    + destruct (mmap_no_unmodeled segs ms x8 model is222 args unmod).
Qed.

Lemma rz_mmap : forall ms model x8 B,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
     realizes (mkCfg (advance_past_svc
                       (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                     (mmap_model a (page_round_up (ms_gpr ms 1)) model)) B) ->
  (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
  realizes (mkCfg ms model) B.
Proof.
  intros ms model x8 B live no_lazy pend is222 args after_grant some_grant.
  pose proof (node_mmap_grant ms model x8 live no_lazy pend is222 args some_grant) as node.
  destruct some_grant as [a0 granted0].
  assert (B_nil : B []) by exact (realizes_nonempty _ _ (after_grant a0 granted0)).
  eapply rz_conseq.
  - apply (rz_node _ _ _ _ (fun _ => B) (exist _ a0 granted0) node).
    intros [a granted]. exact (after_grant a granted).
  - intro tr. split.
    + intros [_ member]. exact (proj1 (t_emit_nil_eq B B_nil tr) member).
    + intro member. exists (exist _ a0 granted0).
      exact (proj2 (t_emit_nil_eq B B_nil tr) member).
Qed.

End WithSegs.

Lemma realizes_run_scfg :
  forall segs pc ph sp brk0 mb rnd (lim : Z) (T : TSet) (inp : ProcInput),
  realizes segs (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  Equivalence.error_free (run_scfg ACFG (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp)
  /\ trace_equiv (bh_traces (run_scfg ACFG (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp)) T.
Proof.
  intros segs pc ph sp brk0 mb rnd lim T inp real.
  split.
  - apply no_error_error_free_scfg. exact (realizes_no_error segs _ T real).
  - exact (realizes_obs_iff segs _ T real).
Qed.
Theorem shape_error_free_equiv :


  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T : TSet) (inp : ProcInput),
  realizes source_segs
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes target_segs
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T ->
  Equivalence.error_free (run_scfg ACFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.error_free (run_scfg ACFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg ACFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg ACFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros src_segs spc sph ssp sbrk smb srnd slim tgt_segs tpc tph tsp tbrk tmb trnd tlim T inp
    src_real tgt_real.
  destruct (realizes_run_scfg _ _ _ _ _ _ _ _ T inp src_real) as [src_clean src_traces].
  destruct (realizes_run_scfg _ _ _ _ _ _ _ _ T inp tgt_real) as [tgt_clean tgt_traces].
  refine (conj src_clean (conj tgt_clean _)).
  intro tr. exact (iff_trans (src_traces tr) (iff_sym (tgt_traces tr))).
Qed.

Theorem shape_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T : TSet) (inp : ProcInput),
  realizes source_segs
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes target_segs
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T ->
  Equivalence.modeled (run_scfg ACFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run_scfg ACFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run_scfg ACFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros src_segs spc sph ssp sbrk smb srnd slim tgt_segs tpc tph tsp tbrk tmb trnd tlim T inp
    src_real tgt_real.
  destruct (shape_error_free_equiv src_segs spc sph ssp sbrk smb srnd slim
              tgt_segs tpc tph tsp tbrk tmb trnd tlim T inp src_real tgt_real)
    as (_ & tgt_clean & same_traces).
  split.
  - apply no_error_modeled_scfg. exact (realizes_no_error src_segs _ T src_real).
  - right. exact (conj same_traces tgt_clean).
Qed.

Lemma cat_realizes : forall segs ms model bufs code,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  to_wexit segs ms bufs code ->
  bufs_modeled bufs ->
  realizes segs (mkCfg ms model) (t_writes_pick bufs (t_exit code (m_fs model))).
Proof.
  intros segs ms model bufs code Hh Hlazy Hfd Hte. revert model Hh Hlazy Hfd.
  induction Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH];
    intros model Hh Hlazy Hfd Hbm.
  - rewrite t_writes_pick_nil. eapply rz_exit; eassumption.
  - apply Forall_cons_iff in Hbm as [Hb Hbs].
    rewrite t_writes_pick_cons. eapply rz_write1; try eassumption.
    intros n Hn1 Hn2. apply IH; assumption.
  - eapply rz_step; try eassumption. apply IH; assumption.
Qed.

Lemma exitline_realizes_aux : forall segs ms bufs code model,
  to_wexit segs ms bufs code -> bufs = [] ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  realizes segs (mkCfg ms model) (t_exit code (m_fs model)).
Proof.
  intros segs ms bufs code model Hte.
  induction Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH]; intros Hbufs Hh;
    [| discriminate Hbufs |]; intro Hlazy.
  - eapply rz_exit; eassumption.
  - eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep |].
    apply IH; [solve [assumption | reflexivity] | exact Hh | exact Hlazy].
Qed.

Lemma exitline_realizes : forall segs ms code model,
  to_wexit segs ms [] code ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  realizes segs (mkCfg ms model) (t_exit code (m_fs model)).
Proof.
  intros segs ms code model Hte Hh Hlazy.
  exact (exitline_realizes_aux segs ms [] code model Hte eq_refl Hh Hlazy).
Qed.

Lemma rz_wall1_mut : forall segs model,
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  (forall ms rest k, to_wall segs (Z_to_bv 64 1) ms rest k ->
     buf_modeled rest ->
     forall T : TSet, T [] ->
     (forall ms', k ms' -> realizes segs (mkCfg ms' model) T) ->
     realizes segs (mkCfg ms model)
       (t_emit (map (WriteEv (Z_to_bv 64 1)) rest) T))
  /\ (forall ms rest k, to_wall_tail segs (Z_to_bv 64 1) ms rest k ->
     buf_modeled rest ->
     forall T : TSet, T [] ->
     (forall ms', k ms' -> realizes segs (mkCfg ms' model) T) ->
     realizes segs (mkCfg ms model)
       (t_emit (map (WriteEv (Z_to_bv 64 1)) rest) T)).
Proof.
  intros segs model Hh Hlazy Hfd.
  apply (to_wall_mutind segs (Z_to_bv 64 1)
    (fun ms rest k => buf_modeled rest -> forall T : TSet, T [] ->
       (forall ms', k ms' -> realizes segs (mkCfg ms' model) T) ->
       realizes segs (mkCfg ms model)
         (t_emit (map (WriteEv (Z_to_bv 64 1)) rest) T))
    (fun ms rest k => buf_modeled rest -> forall T : TSet, T [] ->
       (forall ms', k ms' -> realizes segs (mkCfg ms' model) T) ->
       realizes segs (mkCfg ms model)
         (t_emit (map (WriteEv (Z_to_bv 64 1)) rest) T))).
  -
    intros ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont IH Hbm T HT Hk.
    eapply rz_conseq.
    { apply (rz_node segs (mkCfg ms model) (wr_index rest)
        (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) rest))
        (fun i => mkCfg (advance_past_svc
                           (set_gpr0 ms (len_word (firstn (proj1_sig i) rest))))
                        model)
        (fun i => t_emit (map (WriteEv (Z_to_bv 64 1))
                              (skipn (proj1_sig i) rest)) T)
        (wr_full rest Hnb)).
      - apply (node_write1 segs ms model x8 rest); assumption.
      - intros [n [Hn1 Hn2]]. cbn [proj1_sig].
        apply (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbm) T HT Hk). }
    apply t_alt_wall; [exact HT | exact Hnb].
  -
    intros ms k Hk Hbm T HT Hcont.
    eapply rz_conseq; [apply Hcont; exact Hk|].
    cbn [map]. apply t_eq_sym. apply t_emit_nil_eq. exact HT.
  -
    intros ms rest k Hnb Hw IH Hbm T HT Hk. exact (IH Hbm T HT Hk).
  -
    intros ms ms' rest k Hsvc Hstep Ht IH Hbm T HT Hk.
    eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
                    | exact (IH Hbm T HT Hk)].
Qed.

Lemma wall_realizes : forall segs ms model bufs code,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  to_wallexit segs (Z_to_bv 64 1) bufs code ms ->
  bufs_modeled bufs ->
  realizes segs (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))).
Proof.
  intros segs ms model bufs code Hh Hlazy Hfd Hw Hbm. revert ms Hw Hbm.
  induction bufs as [|buf rest IH]; intros ms Hw Hbm.
  - exact (exitline_realizes segs ms code model Hw Hh Hlazy).
  - destruct Hw as [Hnb Ht]. apply Forall_cons_iff in Hbm as [Hb Hbs].
    rewrite t_writes_cons.
    eapply (proj2 (rz_wall1_mut segs model Hh Hlazy Hfd)).
    + exact Ht.
    + exact Hb.
    + unfold t_writes. apply t_writes_ch_exit_has_nil.
    + intros ms' Hk. apply IH; [exact Hk | exact Hbs].
Qed.

Lemma twm_realizes_mut : forall segs,
  (forall ms model bufs code, MmapSim.twm segs ms model bufs code ->
     m_halted model = None -> m_vm_lazy model = [] -> fd1chan model -> bufs_modeled bufs ->
     realizes segs (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))))
  /\ (forall ms model rest bufs code, MmapSim.twm_pend segs ms model rest bufs code ->
     m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
     buf_modeled rest -> bufs_modeled bufs ->
     realizes segs (mkCfg ms model)
       (t_emit (map (WriteEv (Z_to_bv 64 1)) rest)
               (t_writes bufs (t_exit code (m_fs model)))))
  /\ (forall ms model rest bufs code, MmapSim.twm_tail segs ms model rest bufs code ->
     m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
     buf_modeled rest -> bufs_modeled bufs ->
     realizes segs (mkCfg ms model)
       (t_emit (map (WriteEv (Z_to_bv 64 1)) rest)
               (t_writes bufs (t_exit code (m_fs model))))).
Proof.
  intros segs.
  apply (MmapSim.twm_mutind segs
    (fun ms model bufs code =>
       m_halted model = None -> m_vm_lazy model = [] -> fd1chan model -> bufs_modeled bufs ->
       realizes segs (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))))
    (fun ms model rest bufs code =>
       m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
       buf_modeled rest -> bufs_modeled bufs ->
       realizes segs (mkCfg ms model)
         (t_emit (map (WriteEv (Z_to_bv 64 1)) rest)
                 (t_writes bufs (t_exit code (m_fs model)))))
    (fun ms model rest bufs code =>
       m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
       buf_modeled rest -> bufs_modeled bufs ->
       realizes segs (mkCfg ms model)
         (t_emit (map (WriteEv (Z_to_bv 64 1)) rest)
                 (t_writes bufs (t_exit code (m_fs model)))))).
  -
    intros ms model x8 Hsvc Hx8 Hh Hlazy Hfd Hbm. eapply rz_exit; eassumption.
  -
    intros ms model buf bufs code Hnb Hp IH Hh Hlazy Hfd Hbm.
    apply Forall_cons_iff in Hbm as [Hb Hbs].
    rewrite t_writes_cons. exact (IH Hh Hlazy Hfd Hb Hbs).
  -
    intros ms model x8 bufs code Hsvc Hno Hargs Hte IH Hh Hlazy Hfd Hbm.
    eapply rz_munmap; try eassumption.
    rewrite <- (munmap_model_fs (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model).
    apply IH; [rewrite munmap_model_halted; exact Hh
              | exact (munmap_model_no_lazy _ _ _ Hlazy)
              | apply munmap_model_fd1chan; exact Hfd | exact Hbm].
  -
    intros ms ms' model bufs code Hsvc Hstep Hte IH Hh Hlazy Hfd Hbm.
    eapply rz_step; try eassumption. apply IH; assumption.
  -
    intros ms model x8 rest bufs code Hsvc Hno Hg Hr Hnb Hcont IH Hh Hlazy Hfd Hbr Hbm.
    eapply rz_conseq.
    { apply (rz_node segs (mkCfg ms model) (wr_index rest)
        (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) rest))
        (fun i => mkCfg (advance_past_svc
                           (set_gpr0 ms (len_word (firstn (proj1_sig i) rest))))
                        model)
        (fun i => t_emit (map (WriteEv (Z_to_bv 64 1))
                              (skipn (proj1_sig i) rest))
                         (t_writes bufs (t_exit code (m_fs model))))
        (wr_full rest Hnb)).
      - apply (node_write1 segs ms model x8 rest); assumption.
      - intros [n [Hn1 Hn2]]. cbn [proj1_sig].
        apply (IH n Hn1 Hn2 Hh Hlazy Hfd (buf_modeled_skipn n rest Hbr) Hbm). }
    apply t_alt_wall;
      [unfold t_writes; apply t_writes_ch_exit_has_nil | exact Hnb].
  -
    intros ms model bufs code Hte IH Hh Hlazy Hfd Hbr Hbm.
    eapply rz_conseq; [apply IH; assumption|].
    cbn [map]. apply t_eq_sym. apply t_emit_nil_eq.
    unfold t_writes. apply t_writes_ch_exit_has_nil.
  -
    intros ms model rest bufs code Hnb Hp IH Hh Hlazy Hfd Hbr Hbm.
    exact (IH Hh Hlazy Hfd Hbr Hbm).
  -
    intros ms ms' model rest bufs code Hsvc Hstep Ht IH Hh Hlazy Hfd Hbr Hbm.
    eapply rz_step; try eassumption. exact (IH Hh Hlazy Hfd Hbr Hbm).
Qed.

Lemma twm_realizes : forall segs ms model bufs code,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  MmapSim.twm segs ms model bufs code ->
  bufs_modeled bufs ->
  realizes segs (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))).
Proof.
  intros segs ms model bufs code Hh Hlazy Hfd Hte.
  exact (proj1 (twm_realizes_mut segs) ms model bufs code Hte Hh Hlazy Hfd).
Qed.

Lemma tmw_realizes : forall segs ms model bf cf bs cs,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  MmapSim.tmw segs ms model bf cf bs cs ->
  bufs_modeled bf -> bufs_modeled bs ->
  realizes segs (mkCfg ms model) (t_writes bs (t_exit cs (m_fs model))).
Proof.
  intros segs ms model bf cf bs cs Hh Hlazy Hfd Hte. revert Hh Hlazy Hfd.
  induction Hte as
    [ms model x8 bf cf bs cs Hsvc Hno Hargs Hfail Hsucc Hex
    | ms ms' model bf cf bs cs Hsvc Hstep Hte IH]; intros Hh Hlazy Hfd Hbf Hbs.
  - eapply rz_mmap; try eassumption.
    + intros a Ha.
      rewrite <- (mmap_model_fs a (page_round_up (ms_gpr ms 1)) model).
      apply twm_realizes;
        [rewrite mmap_model_halted; exact Hh
        | exact (eq_trans (mmap_model_lazy _ _ _) Hlazy)
        | apply mmap_model_fd1chan; exact Hfd
        | apply Hsucc; exact Ha | exact Hbs].
  - eapply rz_step; try eassumption. apply IH; assumption.
Qed.

Theorem cat_strong_equiv_alg :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
         bufs code (inp : ProcInput),
  to_wexit source_segs
    (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) bufs code ->
  to_wexit target_segs
    (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) bufs code ->
  bufs_modeled bufs ->
  Equivalence.modeled (run_scfg ACFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run_scfg ACFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run_scfg ACFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros src_segs spc sph ssp sbrk smb srnd slim tgt_segs tpc tph tsp tbrk tmb trnd tlim
    bufs code inp src_run tgt_run modeled_bufs.
  apply (shape_strong_equiv src_segs spc sph ssp sbrk smb srnd slim
           tgt_segs tpc tph tsp tbrk tmb trnd tlim
           (t_writes_pick bufs (t_exit code (in_fs inp))) inp).
  - unfold init_config.
    rewrite <- (m_fs_init_model (segments_reserved src_segs) sbrk smb ssp slim inp).
    exact (cat_realizes src_segs _ _ bufs code
             (m_halted_init_model _ _ _ _ _ _) eq_refl (init_model_fd1chan _ _ _ _ _ _)
             src_run modeled_bufs).
  - unfold init_config.
    rewrite <- (m_fs_init_model (segments_reserved tgt_segs) tbrk tmb tsp tlim inp).
    exact (cat_realizes tgt_segs _ _ bufs code
             (m_halted_init_model _ _ _ _ _ _) eq_refl (init_model_fd1chan _ _ _ _ _ _)
             tgt_run modeled_bufs).
Qed.


Theorem mmap_strong_equiv_alg :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
         bf cf bs cs (inp : ProcInput),
  MmapSim.tmw source_segs (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
      (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp) bf cf bs cs ->
  MmapSim.tmw target_segs (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
      (init_model (segments_reserved target_segs) abrk amb asp alim inp) bf cf bs cs ->
  bufs_modeled bf -> bufs_modeled bs ->
  Equivalence.modeled (run_scfg ACFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run_scfg ACFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run_scfg ACFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros src_segs spc sph ssp sbrk smb srnd slim tgt_segs tpc tph tsp tbrk tmb trnd tlim
    bf cf bs cs inp src_run tgt_run fail_bufs ok_bufs.
  apply (shape_strong_equiv src_segs spc sph ssp sbrk smb srnd slim
           tgt_segs tpc tph tsp tbrk tmb trnd tlim
           (t_writes bs (t_exit cs (in_fs inp))) inp).
  - unfold init_config.
    rewrite <- (m_fs_init_model (segments_reserved src_segs) sbrk smb ssp slim inp).
    exact (tmw_realizes src_segs _ _ bf cf bs cs
             (m_halted_init_model _ _ _ _ _ _) eq_refl (init_model_fd1chan _ _ _ _ _ _)
             src_run fail_bufs ok_bufs).
  - unfold init_config.
    rewrite <- (m_fs_init_model (segments_reserved tgt_segs) tbrk tmb tsp tlim inp).
    exact (tmw_realizes tgt_segs _ _ bf cf bs cs
             (m_halted_init_model _ _ _ _ _ _) eq_refl (init_model_fd1chan _ _ _ _ _ _)
             tgt_run fail_bufs ok_bufs).
Qed.

Corollary rz_alloc_writes : forall segs ms0 ms model x8 bf cf bs cs,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  msteps segs ms0 ms ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  (forall e, In e mmap_errnos ->
     to_wexit segs (advance_past_svc (set_gpr0 ms (errno_ret e))) bf cf) ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
     MmapSim.twm segs
       (advance_past_svc
          (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
       (mmap_model a (page_round_up (ms_gpr ms 1)) model) bs cs) ->
  (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
  bufs_modeled bf -> bufs_modeled bs ->
  realizes segs (mkCfg ms0 model) (t_writes bs (t_exit cs (m_fs model))).
Proof.
  intros segs ms0 ms model x8 bf cf bs cs Hh Hlazy Hfd Hms Hsvc Hno Hargs Hfail Hsucc Hex
    Hbf Hbs.
  eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |].
  eapply rz_mmap; try eassumption.
  - intros a Ha.
    rewrite <- (mmap_model_fs a (page_round_up (ms_gpr ms 1)) model).
    apply twm_realizes;
      [rewrite mmap_model_halted; exact Hh
      | exact (eq_trans (mmap_model_lazy _ _ _) Hlazy)
      | apply mmap_model_fd1chan; exact Hfd
      | apply Hsucc; exact Ha | exact Hbs].
Qed.

Definition t_outcomes (fs : Fs.Fs)
    (U : (list (list byte) * word) -> Prop) : TSet :=
  fun tr => exists o, U o /\ is_prefix tr (AllocSim.outcome_trace fs o).

Lemma t_alt_emit_nil : forall (I : Type) (f : I -> TSet),
  (forall i, f i []) -> t_eq (t_alt (fun i => t_emit [] (f i))) (t_alt f).
Proof.
  intros I f H tr. split.
  - intros [i Hi]. exists i. exact (proj1 (t_emit_nil_eq (f i) (H i) tr) Hi).
  - intros [i Hi]. exists i. exact (proj2 (t_emit_nil_eq (f i) (H i) tr) Hi).
Qed.


Lemma t_outcomes_two_alt2 : forall fs bf cf bs cs,
  t_eq (t_outcomes fs (AllocSim2.two_outcomes bf cf bs cs))
       (t_alt2 (t_writes bf (t_exit cf fs)) (t_writes bs (t_exit cs fs))).
Proof.
  intros fs bf cf bs cs tr.
  unfold t_outcomes, AllocSim2.two_outcomes, AllocSim.outcome_trace, t_alt2.
  rewrite !t_writes_exit_iff. split.
  - intros (o & [-> | ->] & Hp); cbn [fst snd] in Hp; [left | right]; exact Hp.
  - intros [Hp | Hp]; [exists (bf, cf) | exists (bs, cs)]; cbn [fst snd]; auto.
Qed.

Definition t_writes_ch_pick (ch : word) (bufs : list (list byte)) (T : TSet) : TSet :=
  fold_right (t_write_ch ch) T bufs.

Lemma t_writes_ch_pick_1 : forall bufs T, t_writes_ch_pick (Z_to_bv 64 1) bufs T = t_writes_pick bufs T.
Proof. reflexivity. Qed.

Lemma t_writes_ch_pick_cons : forall ch buf bufs T,
  t_writes_ch_pick ch (buf :: bufs) T = t_write_ch ch buf (t_writes_ch_pick ch bufs T).
Proof. reflexivity. Qed.

Lemma node_write_ch : forall segs ms model fd ch x8 buf,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model -> fd32 fd = fd ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  node_ok segs (mkCfg ms model) (wr_index buf)
          (fun i => map (WriteEv ch) (firstn (proj1_sig i) buf))
          (fun i => mkCfg (advance_past_svc
                             (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                          model).
Proof.
  intros segs ms model fd ch x8 buf live no_lazy chan fd_fixed pend is64 to_fd reads modeled
    nonempty.
  pose proof (fun eff model1 evs0 spec =>
                write_ch_ok_inv segs ms x8 model fd ch eff model1 evs0 buf
                  chan fd_fixed is64 to_fd reads nonempty spec) as only_writes.
  refine (conj _ _).
  - intros [n [lo hi]].
    apply (transparent_nonalloc_no segs ms model x8 64 pend is64 eq_refl).
    cbn [proj1_sig].
    rewrite <- (apply_effect_copyins_no_write ms (len_word (firstn n buf)) [(ms_gpr ms 1, n)]).
    exact (sstep_syscall segs ms model x8 _ model model _ live pend
             (write_ch_ok_n segs ms x8 model fd ch buf n chan fd_fixed is64 to_fd reads modeled lo hi)
             live (materialize_model_accesses_no_lazy model _ no_lazy)).
  - intros e st move.
    pose proof (sstep_cfg_sys_inv segs ACFG ms model x8 e st pend move) as outcomes.
    cbv zeta in outcomes.
    destruct outcomes as
      [ (eff & model1 & evs0 & spec & _ & _ & landing)
      | [ (eff & model1 & evs0 & code & spec & halted1 & _ & _ & _)
      | [ (eff & model1 & evs0 & sig & spec & killed1 & _ & _)
      | (unmod & _ & _) ] ] ].
    + destruct (only_writes eff model1 evs0 spec) as (n & lo & hi & eff_is & model1_is & evs0_is).
      subst eff model1 evs0.
      rewrite (materialize_model_accesses_no_lazy model _ no_lazy) in landing.
      destruct landing as [e_is st_is]. subst e st.
      exists (exist _ n (conj lo hi)). split; [reflexivity|].
      rewrite apply_effect_copyins_no_write. reflexivity.
    + destruct (only_writes eff model1 evs0 spec) as (n & _ & _ & _ & model1_is & _).
      subst model1. rewrite live in halted1. discriminate halted1.
    + destruct (only_writes eff model1 evs0 spec) as (n & _ & _ & _ & model1_is & _).
      subst model1. rewrite (m_killed_of_m_halted_none model live) in killed1. discriminate killed1.
    + exact (False_ind _ (write_ch_no_unmodeled segs ms x8 model fd ch buf
                            chan fd_fixed is64 to_fd reads modeled nonempty unmod)).
Qed.

Lemma rz_write_ch : forall segs ms model fd ch x8 buf T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model -> fd32 fd = fd ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     realizes segs
       (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model) T) ->
  realizes segs (mkCfg ms model) (t_write_ch ch buf T).
Proof.
  intros segs ms model fd ch x8 buf T Hh Hlazy Hfdc H32 Hsvc Hno Hg Hr Hbm Hnb Hc.
  unfold t_write_ch.
  apply (rz_node segs (mkCfg ms model) (wr_index buf)
           (fun i => map (WriteEv ch) (firstn (proj1_sig i) buf))
           (fun i => mkCfg (advance_past_svc
                              (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                           model)
           (fun _ => T) (wr_full buf Hnb)).
  - eapply node_write_ch; eassumption.
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.

Lemma cat_realizes_ch : forall segs fd ch ms model bufs code,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model -> fd32 fd = fd ->
  to_wexit_ch segs fd ms bufs code ->
  bufs_modeled bufs ->
  realizes segs (mkCfg ms model) (t_writes_ch_pick ch bufs (t_exit code (m_fs model))).
Proof.
  intros segs fd ch ms model bufs code Hh Hlazy Hfdc H32 Hte.
  revert model Hh Hlazy Hfdc.
  induction Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH];
    intros model Hh Hlazy Hfdc Hbm.
  - eapply rz_exit; eassumption.
  - apply Forall_cons_iff in Hbm as [Hb Hbs].
    rewrite t_writes_ch_pick_cons. eapply rz_write_ch; try eassumption.
    intros n Hn1 Hn2. apply IH; assumption.
  - eapply rz_step; try eassumption. apply IH; assumption.
Qed.

Theorem cat_ch_strong_equiv_alg :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
         (fd ch : word) bufs code (inp : ProcInput),
  fd32 fd = fd ->
  (forall reserved brk0 mb1 sp1 lim1 inp1,
     fdchan fd ch (init_model reserved brk0 mb1 sp1 lim1 inp1)) ->
  to_wexit_ch source_segs fd
    (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) bufs code ->
  to_wexit_ch target_segs fd
    (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) bufs code ->
  bufs_modeled bufs ->
  Equivalence.modeled (run_scfg ACFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run_scfg ACFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run_scfg ACFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros src_segs spc sph ssp sbrk smb srnd slim tgt_segs tpc tph tsp tbrk tmb trnd tlim
    fd ch bufs code inp fd_fixed chan_init src_run tgt_run modeled_bufs.
  apply (shape_strong_equiv src_segs spc sph ssp sbrk smb srnd slim
           tgt_segs tpc tph tsp tbrk tmb trnd tlim
           (t_writes_ch_pick ch bufs (t_exit code (in_fs inp))) inp).
  - unfold init_config.
    rewrite <- (m_fs_init_model (segments_reserved src_segs) sbrk smb ssp slim inp).
    exact (cat_realizes_ch src_segs fd ch _ _ bufs code
             (m_halted_init_model _ _ _ _ _ _) eq_refl (chan_init _ _ _ _ _ _) fd_fixed
             src_run modeled_bufs).
  - unfold init_config.
    rewrite <- (m_fs_init_model (segments_reserved tgt_segs) tbrk tmb tsp tlim inp).
    exact (cat_realizes_ch tgt_segs fd ch _ _ bufs code
             (m_halted_init_model _ _ _ _ _ _) eq_refl (chan_init _ _ _ _ _ _) fd_fixed
             tgt_run modeled_bufs).
Qed.


Corollary cat_strong_equiv_alg_via_ch :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
         bufs code (inp : ProcInput),
  to_wexit source_segs
    (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) bufs code ->
  to_wexit target_segs
    (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) bufs code ->
  bufs_modeled bufs ->
  Equivalence.modeled (run_scfg ACFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run_scfg ACFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run_scfg ACFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros src_segs spc sph ssp sbrk smb srnd slim tgt_segs tpc tph tsp tbrk tmb trnd tlim
    bufs code inp src_run tgt_run modeled_bufs.
  refine (cat_ch_strong_equiv_alg src_segs spc sph ssp sbrk smb srnd slim
            tgt_segs tpc tph tsp tbrk tmb trnd tlim (Z_to_bv 64 1) (Z_to_bv 64 1) bufs code inp
            eq_refl _ (to_wexit_ch_1 _ _ _ _ src_run) (to_wexit_ch_1 _ _ _ _ tgt_run) modeled_bufs).
  intros reserved brk0 mb1 sp1 lim1 inp1.
  exact (conj (init_model_fd1chan reserved brk0 mb1 sp1 lim1 inp1) eq_refl).
Qed.
