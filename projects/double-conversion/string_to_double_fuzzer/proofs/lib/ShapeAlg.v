(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the process input's new fields; the new initial stack layout; the vDSO mapping; the reader fact of the output channels; the place_declined_b premise on successful mmap answers; munmap can be refused; the model's error returns; the mapping ledger's reserved ranges and mmap base; write's access_ok range; walks over the binary's segments lifted to the run's segment list). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run OmniRun.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import SimInv ExitSim CatSim MmapSim AllocSim AllocSim2 WallSim.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import RomBase RomWrite.
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

(* =========================================================================
   LAYER 1 — shapes: prefix-closed trace sets and their combinators
   ========================================================================= *)

(** A shape.  Intended invariant (established for every shape a
    configuration realizes, see [realizes_nonempty] / [realizes_pclosed]):
    nonempty and prefix-closed. *)
Definition TSet := list event -> Prop.

Definition t_eq (T T' : TSet) : Prop := forall tr, T tr <-> T' tr.

Lemma t_eq_refl : forall T, t_eq T T. Proof. firstorder. Qed.
Lemma t_eq_sym : forall T T', t_eq T T' -> t_eq T' T. Proof. firstorder. Qed.
Lemma t_eq_trans : forall T1 T2 T3, t_eq T1 T2 -> t_eq T2 T3 -> t_eq T1 T3.
Proof. firstorder. Qed.

(** The terminated shape: only the empty trace. *)
Definition t_nil : TSet := fun tr => tr = [].

(** Emit a fixed block of events, then continue as [T].  The left
    disjunct is what keeps the result prefix-closed: a run may be
    observed part-way through the block. *)
Definition t_emit (evs : list event) (T : TSet) : TSet :=
  fun tr => is_prefix tr evs \/ exists tr', tr = evs ++ tr' /\ T tr'.

(** Indexed nondeterministic choice. *)
Definition t_alt {I : Type} (f : I -> TSet) : TSet := fun tr => exists i, f i tr.

(** Binary choice. *)
Definition t_alt2 (A B : TSet) : TSet := fun tr => A tr \/ B tr.

(** Terminating leaf: exit with [code], final file system [fs]. *)
Definition t_exit (code : word) (fs : Fs.Fs) : TSet :=
  t_emit [ExitEv code fs] t_nil.

(** The index type of a single channel write's resolutions: the
    delivered length, any nonempty prefix of the buffer.  (For an empty
    buffer the type is EMPTY — the model EFAULTs an empty readable
    prefix, so no realized shape ever contains one.) *)
Definition wr_index (buf : list byte) : Type :=
  {n : nat | (1 <= n)%nat /\ (n <= length buf)%nat}.

Definition wr_full (buf : list byte) (Hnb : (1 <= length buf)%nat)
    : wr_index buf :=
  exist _ (length buf) (conj Hnb (Nat.le_refl _)).

(** A single [write(ch, ...)] of buffer [buf]: the environment delivers
    a chosen nonempty prefix, then the continuation. *)
Definition t_write_ch (ch : word) (buf : list byte) (T : TSet) : TSet :=
  t_alt (fun i : wr_index buf =>
           t_emit (map (WriteEv ch) (firstn (proj1_sig i) buf)) T).

(** A list of [write(1, ...)] buffers, then the continuation. *)
Definition t_writes_pick (bufs : list (list byte)) (T : TSet) : TSet :=
  fold_right (t_write_ch (Z_to_bv 64 1)) T bufs.

(** A shape prefixed by no events is that shape (given nonemptiness, which
    every realized shape has). *)
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

(* -------------------------------------------------------------------------
   The FULL-DELIVERY write combinators: the shape of a write realized
   through a put-style retry loop, whose trace contribution is the whole
   buffer regardless of the environment's chunking (WallSim's nodes).
   ------------------------------------------------------------------------- *)

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

(** Every emit-chain shape contains the empty trace. *)
Lemma t_emit_has_nil : forall e T, t_emit e T [].
Proof. intros e T. left. apply is_prefix_nil. Qed.

Lemma t_writes_ch_exit_has_nil : forall ch bufs code fs,
  t_writes_ch ch bufs (t_exit code fs) [].
Proof.
  intros ch [|b bs] code fs; cbn [t_writes_ch fold_right];
    apply t_emit_has_nil.
Qed.

(** The bridge to the hand-written shapes' spelling of the same set:
    [CatSim]'s "prefixes of [wevents bufs ++ [ExitEv code fs]]". *)
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

(** A single retry-loop write node collapses to one [t_emit] of the
    whole buffer: the per-delivery alternatives denote the same set. *)
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

(** The bridge to the hand-written shapes' spelling of the same set:
    [CatSim]'s "prefixes of [full ++ [ExitEv code fs]] over the delivery
    choices [wpick ch bufs full]".  Nonemptiness of every buffer (which
    every realized shape has, [CatSim.to_wexit_bufs_nonempty]) is what
    makes the two spellings agree: an empty buffer empties BOTH sides
    from that point on.

    This is what [t_writes_ch_pick] DENOTES, and it is the per-delivery
    twin of [t_writes_ch_exit_iff] above.  It has no proof caller — the
    example developments reach the same set through [realizes_obs_iff]
    — and it is kept anyway, for the same reason [t_writes_ch_exit_iff]
    is: the shape algebra states what each of its shapes means, and
    [t_writes_ch_pick] is the shape this development added.  Deleting it
    would leave the algebra characterizing the full-delivery shape that
    short writes replaced and saying nothing about the one that replaced
    it. *)
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

(** [MmapSim.two_traces] is the binary alternative of two write-then-exit
    shapes (on all-nonempty buffer lists). *)
Lemma two_traces_t_alt2 : forall bf cf bs cs fs tr,
  t_alt2 (t_writes bf (t_exit cf fs)) (t_writes bs (t_exit cs fs)) tr
  <-> MmapSim.two_traces bf cf bs cs fs tr.
Proof.
  intros. unfold t_alt2, MmapSim.two_traces.
  rewrite !t_writes_exit_iff. reflexivity.
Qed.

(* =========================================================================
   LAYER 2 — realization
   ========================================================================= *)

Section WithSegs.
Variable segs : list Segment.

(** The syscall/step boundary interface.  A node at configuration [c] is
    characterized by an index type [I] of RESOLUTIONS, the events each
    resolution emits, and the successor configuration each resolution
    reaches.  [node_ok] says the set of admissible transitions is EXACTLY
    that — which in particular rules out [SError], and hence rules out
    both faults and unmodeled configurations, at this node.

    This is the ONLY thing a per-binary proof (symbolic executor, Hoare
    logic, hand-written [step_*] chain) must supply about a syscall: the
    [*_ok] lemma is clause 1, the [sstep_*_inv] lemma is clause 2. *)
Definition node_ok (c : config) (I : Type)
    (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstep segs c (evs i) (SNext (nx i)))
  /\ (forall e st, sstep segs c e st -> exists i, e = evs i /\ st = SNext (nx i)).

(** The one reachability relation. *)
Inductive realizes : config -> TSet -> Prop :=
| rz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                   (T : I -> TSet) (i0 : I),
    node_ok c I evs nx ->
    (* LPS 08b1429: the node's system call reads no byte the run's backing adds
       ([RomBase.sys_rob]; [RomStable] lifts a walk to the run's segment list) *)
    sys_rob segs c ->
    (forall i, realizes (nx i) (T i)) ->
    realizes c (t_alt (fun i => t_emit (evs i) (T i)))
| rz_halt : forall c,
    m_halted (cfg_model c) <> None ->
    realizes c t_nil
| rz_conseq : forall c T T',
    realizes c T -> t_eq T T' -> realizes c T'.

(* -------------------------------------------------------------------------
   Structural facts: every realized shape is nonempty and prefix-closed.
   ------------------------------------------------------------------------- *)

Lemma realizes_nonempty : forall c T, realizes c T -> T [].
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

Lemma realizes_pclosed : forall c T, realizes c T ->
  forall tr tr', T tr -> is_prefix tr' tr -> T tr'.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq];
    intros tr tr' HT Hp.
  - destruct HT as [i [Hpre | (tr0 & -> & HT0)]]; exists i.
    + left. eapply is_prefix_trans; eauto.
    + apply is_prefix_app_split in Hp as [Hp | (tr0' & -> & Hp)].
      * left. exact Hp.
      * right. exists tr0'. split; [reflexivity | eapply IH; eauto].
  - unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
  - apply Heq. eapply IH; [apply Heq; exact HT | exact Hp].
Qed.

(* -------------------------------------------------------------------------
   Soundness: every reachable trace is in the shape.
   ------------------------------------------------------------------------- *)

Lemma realizes_star_only : forall c T, realizes c T ->
  forall tr c', star segs c tr c' -> T tr.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq];
    intros tr c' Hstar.
  - inversion Hstar as [|c1 e c2 tr2 c3 Hss Hstar2]; subst.
    + exists i0. left. apply is_prefix_nil.
    + destruct Hnode as [_ Hsound].
      destruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
      inversion Heq2; subst c2.
      exists i. right. exists tr2. split; [reflexivity | eapply IH; exact Hstar2].
  - destruct (star_halted_nil segs c tr c' Hh Hstar) as [-> _]. reflexivity.
  - apply Heq. eapply IH; exact Hstar.
Qed.

(* -------------------------------------------------------------------------
   Completeness: every trace in the shape is admitted.
   ------------------------------------------------------------------------- *)

Lemma realizes_admits : forall c T, realizes c T ->
  forall tr, T tr -> obs_trace segs c tr.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq];
    intros tr HT.
  - destruct Hnode as [Hcomp _].
    destruct HT as [i [Hpre | (tr0 & -> & HT0)]].
    + exists (evs i), (nx i). split; [apply star_one; apply Hcomp | exact Hpre].
    + destruct (IH i tr0 HT0) as (tr'' & c'' & Hstar & Hp).
      exists (evs i ++ tr''), c''.
      split; [eapply star_step; [apply Hcomp | exact Hstar] | apply is_prefix_app_mono; exact Hp].
  - unfold t_nil in HT; subst tr. apply obs_trace_nil.
  - apply IH. apply Heq. exact HT.
Qed.

(** The master observation theorem: shape membership IS trace-prefix-set
    membership, with no closure operator on either side. *)
Theorem realizes_obs_iff : forall c T, realizes c T ->
  forall tr, obs_trace segs c tr <-> T tr.
Proof.
  intros c T H tr. split.
  - intros (tr' & c' & Hstar & Hp).
    eapply realizes_pclosed; [exact H | eapply realizes_star_only; eauto | exact Hp].
  - apply realizes_admits; exact H.
Qed.

(* -------------------------------------------------------------------------
   No error.
   ------------------------------------------------------------------------- *)

Lemma sstep_halted_none : forall c e st,
  sstep segs c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.

Lemma realizes_step : forall c T e c',
  realizes c T -> sstep segs c e (SNext c') -> exists T', realizes c' T'.
Proof.
  intros c T e c' H; revert e c';
  induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq];
    intros e c' Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
    inversion Heq2; subst c'. exists (T i). apply Hcont.
  - exfalso. apply Hh. eapply sstep_halted_none; exact Hss.
  - eapply IH; exact Hss.
Qed.

Lemma realizes_no_sserror : forall c T e,
  realizes c T -> ~ sstep segs c e SError.
Proof.
  intros c T e H; revert e;
  induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq];
    intros e Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
  - apply Hh. eapply sstep_halted_none; exact Hss.
  - eapply IH; exact Hss.
Qed.

Definition rz_path (c : config) : Prop := exists T, realizes c T.

(* -------------------------------------------------------------------------
   The omni reading of [realizes]
   ------------------------------------------------------------------------- *)

(** [realizes] is already an exact omni judgment — [node_ok] says the
    admissible transitions are EXACTLY the indexed family — so both
    coinductive judgments of [OmniRun] fall out of one induction over
    the shape: every finite prefix is in the shape ([cosafe], from
    [realizes_star_only] through [OmniRun.star_cosafe]) and every
    execution that ends halts with its trace in the shape ([coexec],
    by induction over the shape).  The "admits" half,
    [realizes_admits], is the existential one and stays as it is. *)
Lemma realizes_cosafe : forall c T, realizes c T -> cosafe segs c T.
Proof.
  intros c T H. apply star_cosafe.
  intros tr c' Hstar. exact (realizes_star_only c T H tr c' Hstar).
Qed.

Theorem realizes_coexec : forall c T, realizes c T ->
  OmniRun.coexec segs c (fun tr o => T tr /\ ~ is_error o).
Proof.
  intros c T H.
  induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq].
  - apply coexec_step.
    + destruct Hnode as [Hcomp _]. eapply sstep_halted_none. apply (Hcomp i0).
    + intros e Hss. exfalso. destruct Hnode as [_ Hsound].
      destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate Hbad.
    + intros e c' Hss. destruct Hnode as [_ Hsound].
      destruct (Hsound e (SNext c') Hss) as (i & -> & Heq2).
      inversion Heq2; subst c'.
      eapply coexec_conseq; [exact (IH i) |].
      intros tr o (HT & Hno). split; [| exact Hno].
      exists i. right. exists tr. split; [reflexivity | exact HT].
  - apply coexec_halt; [exact Hh | split; [reflexivity | exact (fun h => h)]].
  - eapply coexec_conseq; [exact IH |].
    intros tr o (HT & Hno). split; [apply Heq; exact HT | exact Hno].
Qed.

Theorem realizes_no_error : forall c T, realizes c T -> ~ reaches_error segs c.
Proof.
  intros c T H. apply coexec_no_error.
  eapply coexec_conseq; [exact (realizes_coexec c T H) |].
  intros tr o (_ & Hno). exact Hno.
Qed.

(** Bites.  A realised shape never takes the escape: [OmniRun.exec … errors]
    is refuted, because the one execution it would be realised by
    ([OmniRun.exec_realizes]) ends in an error and [realizes_coexec] says
    no ending execution does. *)
Lemma realizes_not_errors : forall c T, realizes c T -> ~ OmniRun.exec segs c errors.
Proof.
  intros c T H Hex.
  destruct (exec_realizes _ _ _ Hex) as (tr & o & Hm & Herr).
  exact (proj2 (coexec_sound _ _ _ _ Hm _ (realizes_coexec c T H)) Herr).
Qed.

(** ... and every trace of the shape is really produced, so a prefix
    postcondition that excludes one of them — prefix-closed, hence a
    candidate for [OmniEquivalence.omni_trace_equiv] — is refuted. *)
Lemma realizes_refutes_excluding : forall c T tr,
  realizes c T -> T tr -> ~ cosafe segs c (fun tr' => ~ is_prefix tr tr').
Proof.
  intros c T tr H HT Hc.
  destruct (realizes_admits c T H tr HT) as (tr' & c' & Hstar & Hp).
  exact (cosafe_star _ _ _ _ _ Hc Hstar Hp).
Qed.

(* =========================================================================
   Combinators — every one is continuation-polymorphic
   ========================================================================= *)

Lemma t_alt_unit : forall (f : unit -> TSet), t_eq (t_alt f) (f tt).
Proof.
  intros f tr. split; [intros [[] Hf]; exact Hf | intro Hf; exists tt; exact Hf].
Qed.

(** A silent [unit]-indexed node collapses to its continuation. *)
Lemma rz_silent1 : forall c c' T,
  node_ok c unit (fun _ => []) (fun _ => c') -> sys_rob segs c ->
  realizes c' T ->
  realizes c T.
Proof.
  intros c c' T Hnode Hrob Hc.
  apply (rz_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (rz_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode Hrob).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply realizes_nonempty; exact Hc ].
Qed.

(** A silent node whose every resolution continues as the SAME shape.
    [rz_silent1] is the [unit] case; a node whose resolutions a program
    cannot tell apart — an [munmap] that answers -ENOMEM beside the cut,
    with the same output either way — needs this one. *)
Lemma rz_silent_all : forall c (I : Type) (nx : I -> config) (T : TSet) (i0 : I),
  node_ok c I (fun _ => []) nx -> sys_rob segs c ->
  (forall i, realizes (nx i) T) ->
  realizes c T.
Proof.
  intros c I nx T i0 Hnode Hrob HT.
  assert (HT0 : T []) by (eapply realizes_nonempty; apply (HT i0)).
  apply (rz_conseq c (t_alt (fun _ : I => t_emit [] T))).
  - apply (rz_node c I (fun _ => []) nx (fun _ => T) i0 Hnode Hrob).
    intros i; exact (HT i).
  - intro tr. split.
    + intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
    + intro H. exists i0. exact (proj2 (t_emit_nil_eq T HT0 tr) H).
Qed.

(** A [unit]-indexed node emitting a block. *)
Lemma rz_emit1 : forall c c' e T,
  node_ok c unit (fun _ => e) (fun _ => c') -> sys_rob segs c ->
  realizes c' T ->
  realizes c (t_emit e T).
Proof.
  intros c c' e T Hnode Hrob Hc.
  apply (rz_conseq c (t_alt (fun _ : unit => t_emit e T))).
  - apply (rz_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode Hrob).
    intros []; exact Hc.
  - apply t_alt_unit.
Qed.

(** A SILENT two-way nondeterministic node: the resolutions split into two
    groups, each group's members all continuing as the same shape.  This is
    the mmap/brk pattern. *)
Lemma rz_alt2 : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
                       (a0 : IA) (b0 : IB),
  node_ok c (IA + IB) (fun _ => []) nx -> sys_rob segs c ->
  (forall i, realizes (nx (inl i)) A) ->
  (forall i, realizes (nx (inr i)) B) ->
  realizes c (t_alt2 A B).
Proof.
  intros c IA IB nx A B a0 b0 Hnode Hrob HA HB.
  assert (HA0 : A []) by (eapply realizes_nonempty; apply (HA a0)).
  assert (HB0 : B []) by (eapply realizes_nonempty; apply (HB b0)).
  apply (rz_conseq c
    (t_alt (fun i : IA + IB =>
              t_emit [] (match i with inl _ => A | inr _ => B end)))).
  - apply (rz_node c (IA + IB) (fun _ => []) nx
             (fun i => match i with inl _ => A | inr _ => B end) (inl a0) Hnode Hrob).
    intros [i|i]; [apply HA | apply HB].
  - intro tr. unfold t_alt2. split.
    + intros [[i|i] Hi];
        [ left; exact (proj1 (t_emit_nil_eq A HA0 tr) Hi)
        | right; exact (proj1 (t_emit_nil_eq B HB0 tr) Hi) ].
    + intros [H | H];
        [ exists (inl a0); exact (proj2 (t_emit_nil_eq A HA0 tr) H)
        | exists (inr b0); exact (proj2 (t_emit_nil_eq B HB0 tr) H) ].
Qed.

(* -------------------------------------------------------------------------
   Concrete nodes: instruction step, write(1), exit, munmap, mmap.
   ------------------------------------------------------------------------- *)

Lemma node_instr : forall ms model ms',
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  node_ok (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' Hh Hlazy Hsvc Hstep. split.
  - intros []. apply (sstep_instr segs ms model ms' model);
      [assumption | assumption |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
  - intros e st Hss.
    destruct (sstep_instr_inv segs ms model ms' e st Hlazy Hsvc Hstep Hss) as [-> ->].
    exists tt. split; reflexivity.
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
  eapply rz_silent1; [apply node_instr; eassumption | apply sys_rob_instr; exact Hsvc | exact Hc].
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

(** The [write(1, buf, len)] node: one resolution per delivered length
    (any nonempty prefix of the buffer). *)
Lemma node_write1 : forall ms model x8 buf,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  (* the range [vfs_write]'s [access_ok] accepts; see [CatSim.write1_check_n] *)
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  node_ok (mkCfg ms model) (wr_index buf)
          (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
          (fun i => mkCfg (advance_past_svc
                             (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                          model).
Proof.
  intros ms model x8 buf Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hbm Hnb. split.
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig].
    rewrite <- (apply_effect_copyins_no_write ms (len_word (firstn n buf))
                  [(ms_gpr ms 1, n)]).
    apply (sstep_syscall segs ms model x8
             (with_copyins [(ms_gpr ms 1, n)]
                (mkEffect (len_word (firstn n buf)) [] [])) model
             model (map (WriteEv (Z_to_bv 64 1)) (firstn n buf))).
    + exact Hh.
    + exact Hsvc.
    + apply write1_ok_n; assumption.
    + exact Hh.
    + apply materialize_model_accesses_no_lazy. exact Hlazy.
  - intros e st Hss.
    destruct (sstep_write_inv segs ms model x8 buf e st
                Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hbm Hnb Hss)
      as (n & Hn1 & Hn2 & -> & ->).
    exists (exist _ n (conj Hn1 Hn2)). split; reflexivity.
Qed.

Lemma rz_write1 : forall ms model x8 buf T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     realizes (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model) T) ->
  realizes (mkCfg ms model) (t_write_ch (Z_to_bv 64 1) buf T).
Proof.
  intros ms model x8 buf T Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hbm Hnb Hc.
  unfold t_write_ch.
  apply (rz_node (mkCfg ms model) (wr_index buf)
           (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
           (fun i => mkCfg (advance_past_svc
                              (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                           model)
           (fun _ => T) (wr_full buf Hnb)).
  - apply (node_write1 ms model x8 buf); assumption.
  - apply (write1_rob segs ms model x8 buf); assumption.
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.

(** The [exit] leaf. *)
Lemma rz_exit : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  realizes (mkCfg ms model)
           (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros ms model x8 Hh Hsvc Hx8.
  set (code := bv_and (ms_gpr ms 0) (Z_to_bv 64 255)).
  unfold t_exit.
  eapply (rz_emit1 (mkCfg ms model) (mkCfg ms (with_halted code model))).
  - split.
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
      (eapply sys_rob_memfree; [exact Hsvc | rewrite Hx8'; first [exact memfree_93 | exact memfree_94]]).
  - apply rz_halt. cbn. discriminate.
Qed.

(** The [munmap] node (silent, model-changing), with the two answers its
    arm admits: a refusal from [munmap_errnos], which changes nothing,
    and the cut.  Both continue as the same shape: a program whose
    output differs between them is not described by this node. *)
Lemma rz_munmap : forall ms model x8 T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  (forall e, In e munmap_errnos ->
     realizes (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) T) ->
  realizes (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                  (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) T ->
  realizes (mkCfg ms model) T.
Proof.
  intros ms model x8 T Hh Hlazy Hsvc Hno Hargs HA HB.
  apply (rz_silent_all (mkCfg ms model) ({e : Z | In e munmap_errnos} + unit)
           (fun i => match i with
              | inl (exist _ e _) =>
                  mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
              | inr _ =>
                  mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
              end) T (inr tt)).
  - split.
    + intros [[e He] | []]; cbn.
      * rewrite <- (apply_effect_no_write ms (errno_ret e)).
        apply (sstep_syscall segs ms model x8 (mkEffect (errno_ret e) [] [])
                 model model []).
        -- exact Hh.
        -- exact Hsvc.
        -- apply munmap_fail_ok; assumption.
        -- exact Hh.
        -- apply materialize_model_accesses_no_lazy. exact Hlazy.
      * apply (sstep_syscall segs ms model x8 (munmap_eff ms)
                 (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
                 (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
        -- exact Hh.
        -- exact Hsvc.
        -- apply munmap_ok; assumption.
        -- rewrite munmap_model_halted; exact Hh.
        -- apply materialize_model_accesses_no_lazy.
           exact (munmap_model_no_lazy _ _ _ Hlazy).
    + intros e st Hss.
      destruct (sstep_munmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hss)
        as [-> [(er & Her & ->) | ->]].
      * exists (inl (exist _ er Her)). split; reflexivity.
      * exists (inr tt). split; reflexivity.
  - eapply sys_rob_memfree; [exact Hsvc | rewrite Hno; exact memfree_215].
  - intros [[e He] | []]; cbn; [exact (HA e He) | exact HB].
Qed.

(** The [mmap] node: the two-resolution silent nondeterministic node.
    Failure resolutions (an errno from [mmap_errnos]) continue as [A];
    success resolutions (a grantable address) continue as [B]. *)
Lemma rz_mmap : forall ms model x8 A B,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  (forall e, In e mmap_errnos ->
     realizes (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) A) ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
     realizes (mkCfg (advance_past_svc
                       (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                     (mmap_model a (page_round_up (ms_gpr ms 1)) model)) B) ->
  (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
  realizes (mkCfg ms model) (t_alt2 A B).
Proof.
  intros ms model x8 A B Hh Hlazy Hsvc Hno Hargs Hdecl HA HB Hex.
  set (n := page_round_up (ms_gpr ms 1)).
  set (nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1))).
  destruct Hex as [a0 Ha0].
  pose (IA := {e : Z | In e mmap_errnos}).
  pose (IB := {a : word | grant_ok (ms_gpr ms 0) model a nZ = true}).
  pose (nx := fun (i : IA + IB) =>
    match i with
    | inl (exist _ e _) => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
    | inr (exist _ a _) =>
        mkCfg (advance_past_svc (apply_effect ms (mkEffect a [] [(a, n)])))
              (mmap_model a n model)
    end).
  apply (rz_alt2 (mkCfg ms model) IA IB nx A B
           (exist _ ENOMEM ENOMEM_in_mmap_errnos) (exist _ a0 Ha0)).
  - split.
    + intros [[e He] | [a Ha]]; cbn.
      * rewrite <- (apply_effect_no_write ms (errno_ret e)).
        apply (sstep_syscall segs ms model x8 (mkEffect (errno_ret e) [] [])
                 model model []).
        -- exact Hh.
        -- exact Hsvc.
        -- apply mmap_fail_ok; assumption.
        -- exact Hh.
        -- apply materialize_model_accesses_no_lazy. exact Hlazy.
      * apply (sstep_syscall segs ms model x8 (mkEffect a [] [(a, n)])
                 (mmap_model a n model) (mmap_model a n model) []).
        -- exact Hh.
        -- exact Hsvc.
        -- apply mmap_succ_ok; assumption.
        -- rewrite mmap_model_halted; exact Hh.
        -- apply materialize_model_accesses_no_lazy.
           exact (eq_trans (mmap_model_lazy _ _ _) Hlazy).
    + intros e st Hss.
      destruct (sstep_mmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hdecl Hss)
        as [-> [(er & Her & ->) | (a & Ha & ->)]].
      * exists (inl (exist _ er Her)). split; reflexivity.
      * exists (inr (exist _ a Ha)). split; reflexivity.
  - eapply sys_rob_memfree; [exact Hsvc | rewrite Hno; exact memfree_222].
  - intros [e He]; cbn. apply HA; exact He.
  - intros [a Ha]; cbn. apply HB; exact Ha.
Qed.

End WithSegs.

(* =========================================================================
   The master equivalence theorem
   ========================================================================= *)

(** A source and a target realizing the SAME shape are equivalent, and the
    source is covered by the model.  This replaces every
    [*_strong_equiv] lemma in [Common/]: there is one theorem, and the
    shape is the only thing the two per-binary proofs must agree on. *)
(** The omni ingredients of the master theorem, one per conjunct. *)
Lemma shape_omni_corun :
  forall segs pc ph sp brk0 mb rnd (lim : Z) (T : TSet) (inp : ProcInput),
  realizes (run_segments segs inp sp mb) (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) T ->
  omni_corun (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
    (fun tr o => T tr /\ ~ is_error o).
Proof. intros. cbn [omni_corun]. apply realizes_coexec; assumption. Qed.

Lemma shape_omni_cosafe :
  forall segs pc ph sp brk0 mb rnd (lim : Z) (T : TSet) (inp : ProcInput),
  realizes (run_segments segs inp sp mb) (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) T ->
  omni_cosafe (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp T.
Proof. intros. cbn [omni_cosafe]. apply realizes_cosafe; assumption. Qed.

(** Two realisations of the same shape agree on every prefix-closed
    postcondition: the refinement pair, each side's trace set being the
    shape. *)
Lemma shape_omni_trace_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T : TSet) (inp : ProcInput),
  realizes (run_segments source_segs inp rsp rmb)
    (init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes (run_segments target_segs inp asp amb)
    (init_config (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd alim inp) T ->
  omni_trace_equiv (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd)
                   (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    T inp Hsource Htarget.
  apply omni_trace_equiv_refinement. cbn [run bh_traces omni_cosafe]. split.
  - apply (cosafe_obs_iff _ _ _ (obs_trace_is_prefix_closed _ _)).
    intros tr Hobs. apply (realizes_obs_iff _ _ _ Htarget).
    apply (realizes_obs_iff _ _ _ Hsource). exact Hobs.
  - apply (cosafe_obs_iff _ _ _ (obs_trace_is_prefix_closed _ _)).
    intros tr Hobs. apply (realizes_obs_iff _ _ _ Hsource).
    apply (realizes_obs_iff _ _ _ Htarget). exact Hobs.
Qed.

Lemma shape_omni_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T : TSet) (inp : ProcInput),
  realizes (run_segments source_segs inp rsp rmb)
    (init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes (run_segments target_segs inp asp amb)
    (init_config (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd alim inp) T ->
  omni_equiv (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd)
             (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    T inp Hsource Htarget.
  right. split.
  - eapply shape_omni_trace_equiv; eassumption.
  - eapply coexec_conseq; [apply (shape_omni_corun _ _ _ _ _ _ _ _ _ _ Htarget) |].
    intros tr o (_ & Hno). exact Hno.
Qed.

(** The master theorem in omni shape: at the two role budgets, a source
    and a target realizing the SAME shape satisfy
    [OmniEquivalence.omni_strong_equiv]. *)
Theorem shape_omni_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd
         (T : TSet) (inp : ProcInput),
  realizes (run_segments source_segs inp rsp rmb)
    (init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd
       source_alloc_limit inp) T ->
  realizes (run_segments target_segs inp asp amb)
    (init_config (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd
       target_alloc_limit inp) T ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd T inp
    Hsource Htarget.
  split.
  - cbn [image_run_segments img_segments en_sp en_mmap_base].
    eapply coexec_conseq; [apply (shape_omni_corun _ _ _ _ _ _ _ _ _ _ Hsource) |].
    intros tr o (_ & Hno). exact (never_errors_covered _ _ _ Hno).
  - eapply shape_omni_equiv; eassumption.
Qed.

(** A source and a target realizing the SAME shape are equivalent, and the
    source is covered by the model.  This replaces every
    [*_strong_equiv] lemma in [Common/]: there is one theorem, and the
    shape is the only thing the two per-binary proofs must agree on.
    From the omni ingredients above through the compat [iff]s. *)
Theorem shape_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T : TSet) (inp : ProcInput),
  realizes (run_segments source_segs inp rsp rmb)
    (init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes (run_segments target_segs inp asp amb)
    (init_config (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd alim inp) T ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    T inp Hsource Htarget.
  split.
  - apply modeled_iff. cbn [image_run_segments img_segments en_sp en_mmap_base].
    eapply coexec_conseq; [apply (shape_omni_corun _ _ _ _ _ _ _ _ _ _ Hsource) |].
    intros tr o (_ & Hno). exact (never_errors_covered _ _ _ Hno).
  - apply equiv_iff. eapply shape_omni_equiv; eassumption.
Qed.

(* =========================================================================
   Sanity: the existing shapes are instances
   ========================================================================= *)

(** [CatSim.to_wexit] realizes [t_writes_pick bufs (t_exit code fs)]. *)
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
    | ms x8 buf bufs code Hsvc Hno Hg Hr Hok Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH];
    intros model Hh Hlazy Hfd Hbm.
  - rewrite t_writes_pick_nil. eapply rz_exit; eassumption.
  - apply Forall_cons_iff in Hbm as [Hb Hbs].
    rewrite t_writes_pick_cons. eapply rz_write1; try eassumption.
    intros n Hn1 Hn2. apply IH; assumption.
  - eapply rz_step; try eassumption. apply IH; assumption.
Qed.

(** [MmapSim.twm] (writes / munmap / exit) realizes the same shape. *)
(* -------------------------------------------------------------------------
   Wall nodes: a put-style retry loop collapses to ONE [t_emit] of the
   full buffer.
   ------------------------------------------------------------------------- *)

(** The exit straight line realizes the exit leaf (no fd needed). *)
Lemma exitline_realizes_aux : forall segs ms bufs code model,
  to_wexit segs ms bufs code -> bufs = [] ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  realizes segs (mkCfg ms model) (t_exit code (m_fs model)).
Proof.
  intros segs ms bufs code model Hte.
  induction Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr Hok Hnb Hcont IH
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
  - (* twl_write *)
    intros ms x8 rest k Hsvc Hno Hg Hr Hok Hnb Hcont IH Hbm T HT Hk.
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
      - apply (write1_rob segs ms model x8 rest); assumption.
      - intros [n [Hn1 Hn2]]. cbn [proj1_sig].
        apply (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbm) T HT Hk). }
    apply t_alt_wall; [exact HT | exact Hnb].
  - (* twt_done *)
    intros ms k Hk Hbm T HT Hcont.
    eapply rz_conseq; [apply Hcont; exact Hk|].
    cbn [map]. apply t_eq_sym. apply t_emit_nil_eq. exact HT.
  - (* twt_more *)
    intros ms rest k Hnb Hw IH Hbm T HT Hk. exact (IH Hbm T HT Hk).
  - (* twt_step *)
    intros ms ms' rest k Hsvc Hstep Ht IH Hbm T HT Hk.
    eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
                    | exact (IH Hbm T HT Hk)].
Qed.

(** [WallSim.to_wallexit] realizes the FULL-DELIVERY write-list shape:
    the original [t_writes]. *)
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

(** [MmapSim.twm] (retry-loop writes / munmap / exit) realizes the same
    FULL-DELIVERY shape.  The wall structure here is [twm]'s own mutual
    pend/tail pair, so the collapse is replayed over [twm_mutind]. *)
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
  - (* twm_exit *)
    intros ms model x8 Hsvc Hx8 Hh Hlazy Hfd Hbm. eapply rz_exit; eassumption.
  - (* twm_write *)
    intros ms model buf bufs code Hnb Hp IH Hh Hlazy Hfd Hbm.
    apply Forall_cons_iff in Hbm as [Hb Hbs].
    rewrite t_writes_cons. exact (IH Hh Hlazy Hfd Hb Hbs).
  - (* twm_munmap *)
    intros ms model x8 bufs code Hsvc Hno Hargs Hfail IHfail Hcut IH Hh Hlazy Hfd Hbm.
    eapply rz_munmap;
      [exact Hh | exact Hlazy | exact Hsvc | exact Hno | exact Hargs | | ].
    + intros e He. exact (IHfail e He Hh Hlazy Hfd Hbm).
    + rewrite <- (munmap_model_fs (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model).
      apply IH; [rewrite munmap_model_halted; exact Hh
                | exact (munmap_model_no_lazy _ _ _ Hlazy)
                | apply munmap_model_fd1chan; exact Hfd | exact Hbm].
  - (* twm_step *)
    intros ms ms' model bufs code Hsvc Hstep Hte IH Hh Hlazy Hfd Hbm.
    eapply rz_step; try eassumption. apply IH; assumption.
  - (* twmp_write *)
    intros ms model x8 rest bufs code Hsvc Hno Hg Hr Hok Hnb Hcont IH Hh Hlazy Hfd Hbr Hbm.
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
      - apply (write1_rob segs ms model x8 rest); assumption.
      - intros [n [Hn1 Hn2]]. cbn [proj1_sig].
        apply (IH n Hn1 Hn2 Hh Hlazy Hfd (buf_modeled_skipn n rest Hbr) Hbm). }
    apply t_alt_wall;
      [unfold t_writes; apply t_writes_ch_exit_has_nil | exact Hnb].
  - (* twmt_done *)
    intros ms model bufs code Hte IH Hh Hlazy Hfd Hbr Hbm.
    eapply rz_conseq; [apply IH; assumption|].
    cbn [map]. apply t_eq_sym. apply t_emit_nil_eq.
    unfold t_writes. apply t_writes_ch_exit_has_nil.
  - (* twmt_more *)
    intros ms model rest bufs code Hnb Hp IH Hh Hlazy Hfd Hbr Hbm.
    exact (IH Hh Hlazy Hfd Hbr Hbm).
  - (* twmt_step *)
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

(** [MmapSim.tmw] (deterministic prefix, then the branching mmap) realizes
    the binary alternative of two write-then-exit shapes. *)
Lemma tmw_realizes : forall segs ms model bf cf bs cs,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  MmapSim.tmw segs ms model bf cf bs cs ->
  bufs_modeled bf -> bufs_modeled bs ->
  realizes segs (mkCfg ms model)
    (t_alt2 (t_writes bf (t_exit cf (m_fs model)))
            (t_writes bs (t_exit cs (m_fs model)))).
Proof.
  intros segs ms model bf cf bs cs Hh Hlazy Hfd Hte. revert Hh Hlazy Hfd.
  induction Hte as
    [ms model x8 bf cf bs cs Hsvc Hno Hargs Hdecl Hfail Hsucc Hex
    | ms ms' model bf cf bs cs Hsvc Hstep Hte IH]; intros Hh Hlazy Hfd Hbf Hbs.
  - eapply rz_mmap; try eassumption.
    + intros e He. apply twm_realizes;
        [exact Hh | exact Hlazy | exact Hfd | apply Hfail; exact He | exact Hbf].
    + intros a Ha.
      rewrite <- (mmap_model_fs a (page_round_up (ms_gpr ms 1)) model).
      apply twm_realizes;
        [rewrite mmap_model_halted; exact Hh
        | exact (eq_trans (mmap_model_lazy _ _ _) Hlazy)
        | apply mmap_model_fd1chan; exact Hfd
        | apply Hsucc; exact Ha | exact Hbs].
  - eapply rz_step; try eassumption. apply IH; assumption.
Qed.


(** [CatSim.cat_strong_equiv_te], re-derived from the single master
    theorem, on a launch with a reader on stdout (the realizations below
    take [CatSim.fd1chan], because a reader-gone write KILLS the
    process). *)
Theorem cat_strong_equiv_alg :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
         bufs code (inp : ProcInput),
  to_wexit (run_segments source_segs inp rsp rmb)
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
    bufs code ->
  to_wexit (run_segments target_segs inp asp amb)
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
    bufs code ->
  bufs_modeled bufs ->
  in_channel_reader inp = true ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    bufs code inp Hs Ht Hbm Hr.
  apply (shape_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd rlim
           target_segs apc aph asp abrk amb arnd alim
           (t_writes_pick bufs (t_exit code (in_fs inp))) inp).
  - unfold init_config.
    apply (cat_realizes (run_segments source_segs inp rsp rmb)
             (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
             (with_vdso (vdso_run_init (ed_vdso rrnd))
                (init_model (segments_reserved (run_segments source_segs inp rsp rmb))
                   rbrk rmb rsp rlim inp))
             bufs code eq_refl eq_refl
             (init_model_fd1chan (segments_reserved (run_segments source_segs inp rsp rmb))
                rbrk rmb rsp rlim inp Hr) Hs Hbm).
  - unfold init_config.
    apply (cat_realizes (run_segments target_segs inp asp amb)
             (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
             (with_vdso (vdso_run_init (ed_vdso arnd))
                (init_model (segments_reserved (run_segments target_segs inp asp amb))
                   abrk amb asp alim inp))
             bufs code eq_refl eq_refl
             (init_model_fd1chan (segments_reserved (run_segments target_segs inp asp amb))
                abrk amb asp alim inp Hr) Ht Hbm).
Qed.

(** The same, in the shape of [OmniEquivalence.omni_strong_equiv], at the
    two role budgets. *)
Theorem cat_omni_strong_equiv_alg :
  forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd
         bufs code (inp : ProcInput),
  to_wexit (run_segments source_segs inp rsp rmb)
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
    bufs code ->
  to_wexit (run_segments target_segs inp asp amb)
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
    bufs code ->
  bufs_modeled bufs ->
  in_channel_reader inp = true ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd
    bufs code inp Hs Ht Hbm Hr.
  apply (shape_omni_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd
           target_segs apc aph asp abrk amb arnd
           (t_writes_pick bufs (t_exit code (in_fs inp))) inp).
  - unfold init_config.
    apply (cat_realizes (run_segments source_segs inp rsp rmb)
             (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
             (with_vdso (vdso_run_init (ed_vdso rrnd))
                (init_model (segments_reserved (run_segments source_segs inp rsp rmb))
                   rbrk rmb rsp source_alloc_limit inp))
             bufs code eq_refl eq_refl
             (init_model_fd1chan (segments_reserved (run_segments source_segs inp rsp rmb))
                rbrk rmb rsp source_alloc_limit inp Hr) Hs Hbm).
  - unfold init_config.
    apply (cat_realizes (run_segments target_segs inp asp amb)
             (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
             (with_vdso (vdso_run_init (ed_vdso arnd))
                (init_model (segments_reserved (run_segments target_segs inp asp amb))
                   abrk amb asp target_alloc_limit inp))
             bufs code eq_refl eq_refl
             (init_model_fd1chan (segments_reserved (run_segments target_segs inp asp amb))
                abrk amb asp target_alloc_limit inp Hr) Ht Hbm).
Qed.

(** [MmapSim.mmap_strong_equiv_te], re-derived from the same theorem, on
    a launch with a reader on stdout. *)
Theorem mmap_strong_equiv_alg :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
         bf cf bs cs (inp : ProcInput),
  MmapSim.tmw (run_segments source_segs inp rsp rmb)
      (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
      (with_vdso (vdso_run_init (ed_vdso rrnd))
         (init_model (segments_reserved (run_segments source_segs inp rsp rmb)) rbrk rmb rsp
            rlim inp)) bf cf bs cs ->
  MmapSim.tmw (run_segments target_segs inp asp amb)
      (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
      (with_vdso (vdso_run_init (ed_vdso arnd))
         (init_model (segments_reserved (run_segments target_segs inp asp amb)) abrk amb asp
            alim inp)) bf cf bs cs ->
  bufs_modeled bf -> bufs_modeled bs ->
  in_channel_reader inp = true ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    bf cf bs cs inp Hs Ht Hbf Hbs Hr.
  apply (shape_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd rlim
           target_segs apc aph asp abrk amb arnd alim
           (t_alt2 (t_writes bf (t_exit cf (in_fs inp))) (t_writes bs (t_exit cs (in_fs inp))))
           inp).
  - unfold init_config.
    apply (tmw_realizes (run_segments source_segs inp rsp rmb)
             (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
             (with_vdso (vdso_run_init (ed_vdso rrnd))
                (init_model (segments_reserved (run_segments source_segs inp rsp rmb))
                   rbrk rmb rsp rlim inp))
             bf cf bs cs eq_refl eq_refl
             (init_model_fd1chan (segments_reserved (run_segments source_segs inp rsp rmb))
                rbrk rmb rsp rlim inp Hr) Hs Hbf Hbs).
  - unfold init_config.
    apply (tmw_realizes (run_segments target_segs inp asp amb)
             (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
             (with_vdso (vdso_run_init (ed_vdso arnd))
                (init_model (segments_reserved (run_segments target_segs inp asp amb))
                   abrk amb asp alim inp))
             bf cf bs cs eq_refl eq_refl
             (init_model_fd1chan (segments_reserved (run_segments target_segs inp asp amb))
                abrk amb asp alim inp Hr) Ht Hbf Hbs).
Qed.

(** The same, in the shape of [OmniEquivalence.omni_strong_equiv], at the
    two role budgets. *)
Theorem mmap_omni_strong_equiv_alg :
  forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd
         bf cf bs cs (inp : ProcInput),
  MmapSim.tmw (run_segments source_segs inp rsp rmb)
      (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
      (with_vdso (vdso_run_init (ed_vdso rrnd))
         (init_model (segments_reserved (run_segments source_segs inp rsp rmb)) rbrk rmb rsp
            source_alloc_limit inp)) bf cf bs cs ->
  MmapSim.tmw (run_segments target_segs inp asp amb)
      (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
      (with_vdso (vdso_run_init (ed_vdso arnd))
         (init_model (segments_reserved (run_segments target_segs inp asp amb)) abrk amb asp
            target_alloc_limit inp)) bf cf bs cs ->
  bufs_modeled bf -> bufs_modeled bs ->
  in_channel_reader inp = true ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd
    bf cf bs cs inp Hs Ht Hbf Hbs Hr.
  apply (shape_omni_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd
           target_segs apc aph asp abrk amb arnd
           (t_alt2 (t_writes bf (t_exit cf (in_fs inp))) (t_writes bs (t_exit cs (in_fs inp))))
           inp).
  - unfold init_config.
    apply (tmw_realizes (run_segments source_segs inp rsp rmb)
             (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
             (with_vdso (vdso_run_init (ed_vdso rrnd))
                (init_model (segments_reserved (run_segments source_segs inp rsp rmb))
                   rbrk rmb rsp source_alloc_limit inp))
             bf cf bs cs eq_refl eq_refl
             (init_model_fd1chan (segments_reserved (run_segments source_segs inp rsp rmb))
                rbrk rmb rsp source_alloc_limit inp Hr) Hs Hbf Hbs).
  - unfold init_config.
    apply (tmw_realizes (run_segments target_segs inp asp amb)
             (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
             (with_vdso (vdso_run_init (ed_vdso arnd))
                (init_model (segments_reserved (run_segments target_segs inp asp amb))
                   abrk amb asp target_alloc_limit inp))
             bf cf bs cs eq_refl eq_refl
             (init_model_fd1chan (segments_reserved (run_segments target_segs inp asp amb))
                abrk amb asp target_alloc_limit inp Hr) Ht Hbf Hbs).
Qed.

(* =========================================================================
   The allocation-prologue composition, DERIVED
   ========================================================================= *)

(** "Silent nondeterministic allocation prologue, then a deterministic
    write-list-then-exit tail."

    Without this lemma, this composition needs a new hand-written shape
    file per allocator/tail combination.  Here it is four lines: the mmap node
    combinator with the [CatSim] tail bridge plugged into both
    continuations.  Nothing about it is specific to [to_wexit] — any
    [realizes] derivation may be plugged in, including one produced by a
    reflective symbolic executor. *)
Corollary rz_alloc_writes : forall segs ms0 ms model x8 bf cf bs cs,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  msteps segs ms0 ms ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  (forall e, In e mmap_errnos ->
     to_wexit segs (advance_past_svc (set_gpr0 ms (errno_ret e))) bf cf) ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
     MmapSim.twm segs
       (advance_past_svc
          (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
       (mmap_model a (page_round_up (ms_gpr ms 1)) model) bs cs) ->
  (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
  bufs_modeled bf -> bufs_modeled bs ->
  realizes segs (mkCfg ms0 model)
    (t_alt2 (t_writes_pick bf (t_exit cf (m_fs model)))
            (t_writes bs (t_exit cs (m_fs model)))).
Proof.
  intros segs ms0 ms model x8 bf cf bs cs Hh Hlazy Hfd Hms Hsvc Hno Hargs Hdecl Hfail Hsucc Hex
    Hbf Hbs.
  eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |].
  eapply rz_mmap; try eassumption.
  - intros e He. apply cat_realizes;
      [exact Hh | exact Hlazy | exact Hfd | apply Hfail; exact He | exact Hbf].
  - intros a Ha.
    rewrite <- (mmap_model_fs a (page_round_up (ms_gpr ms 1)) model).
    apply twm_realizes;
      [rewrite mmap_model_halted; exact Hh
      | exact (eq_trans (mmap_model_lazy _ _ _) Hlazy)
      | apply mmap_model_fd1chan; exact Hfd
      | apply Hsucc; exact Ha | exact Hbs].
Qed.

(* =========================================================================
   Bridge: AllocSim's brk-branching shape
   ========================================================================= *)

(** The trace set an [AllocSim.to_outcomes] outcome SET denotes: the
    prefixes of the candidate traces of each outcome, over the
    per-buffer delivery choices [wpick].  This is exactly the right-hand
    side of [AllocSim.alloc_obs_iff]. *)
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

(** [AllocSim.to_outcomes] realizes [t_outcomes].  The brk node is an
    [rz_node] indexed by the admissible syscall resolutions; receptivity
    ([AllocSim.brk_receptive]) supplies the inhabitant [rz_node] needs. *)
Lemma outcomes_realizes : forall segs ms model U,
  AllocSim.to_outcomes segs ms model U ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  realizes segs (mkCfg ms model) (t_outcomes (m_fs model) U).
Proof.
  intros segs ms model U Hto.
  induction Hto as
    [ ms model bufs code U Hfd Hte Hbm HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hno Hcont IH HU ];
    intros Hh Hlazy.
  - (* tou_wexit: the retry-loop write-list tail *)
    eapply rz_conseq;
      [apply (wall_realizes segs ms model bufs code Hh Hlazy Hfd Hte Hbm)|].
    intro tr. rewrite t_writes_exit_iff.
    unfold t_outcomes, AllocSim.outcome_trace. split.
    + intro Hp. exists (bufs, code). split; [apply HU; reflexivity | exact Hp].
    + intros (o & Ho & Hp). apply HU in Ho. subst o. exact Hp.
  - (* tou_step *)
    eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
                    | apply IH; assumption].
  - (* tou_brk: the indexed nondeterministic node *)
    pose (P := fun p : SyscallEffect * Model =>
                 syscall_spec (sys_input segs ms x8) model (Ok (fst p) (snd p) [])).
    pose (nx := fun (i : sig P) =>
                  mkCfg (advance_past_svc (apply_effect ms (fst (proj1_sig i))))
                        (snd (proj1_sig i))).
    pose (Ti := fun (i : sig P) =>
                  t_outcomes (m_fs model) (T (fst (proj1_sig i)) (snd (proj1_sig i)))).
    destruct (AllocSim.brk_receptive segs ms x8 model Hno)
      as (eff0 & model0 & Hspec0).
    assert (Hcont' : forall i : sig P, realizes segs (nx i) (Ti i)).
    { intros [[eff model'] Hspec]. cbn in Hspec. unfold nx, Ti; cbn.
      destruct (AllocSim.brk_step_shape segs ms x8 model eff model' [] Hh Hlazy Hno Hspec)
        as (_ & Hh' & Hfs & _ & Hlazy').
      rewrite <- Hfs. apply (IH eff model' []);
        [exact Hspec | exact Hh' | exact (eq_trans Hlazy' Hlazy)]. }
    eapply rz_conseq.
    { apply (rz_node segs (mkCfg ms model) (sig P) (fun _ => []) nx Ti
               (exist P (eff0, model0) Hspec0));
        [| eapply sys_rob_memfree; [exact Hsvc | rewrite Hno; exact memfree_214] | exact Hcont'].
      split.
      - intros [[eff model'] Hspec]. cbn in Hspec. unfold nx; cbn.
        destruct (AllocSim.brk_step_shape segs ms x8 model eff model' [] Hh Hlazy Hno Hspec)
          as (_ & Hh' & _ & _ & Hlazy').
        apply (sstep_syscall segs ms model x8 eff model' model' []); try assumption.
        apply materialize_model_accesses_no_lazy. exact (eq_trans Hlazy' Hlazy).
      - intros e st Hss.
        destruct (AllocSim.sstep_brk_inv segs ms model x8 e st
                    Hh Hlazy Hsvc Hno Hss)
          as (eff & model' & Hspec & -> & ->).
        exists (exist P (eff, model') Hspec). split; reflexivity. }
    eapply t_eq_trans;
      [apply t_alt_emit_nil; intro i; eapply realizes_nonempty; apply Hcont'|].
    intro tr. unfold t_alt, Ti, t_outcomes; cbn. split.
    + intros ([[eff model'] Hspec] & o & Ho & Hp). cbn in Ho, Hspec.
      exists o. split; [apply HU; exists eff, model', []; auto | exact Hp].
    + intros (o & Ho & Hp). apply HU in Ho.
      destruct Ho as (eff & model' & evs & Hspec & Ht).
      destruct (AllocSim.brk_step_shape segs ms x8 model eff model' evs Hh Hlazy Hno Hspec)
        as (-> & _ & _ & _).
      exists (exist P (eff, model') Hspec). cbn.
      exists o. split; [exact Ht | exact Hp].
Qed.

(** The two-element outcome set of [AllocSim2] is the binary alternative
    of two write-then-exit shapes — the SAME [TSet] a [tmw] target lands
    on.  That equality is the whole content of the mixed-allocator glue. *)
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

(** [AllocSim2.alloc_mmap_strong_equiv], re-derived from the master
    theorem: a brk-allocating source and an mmap-allocating target that
    realize the SAME shape, on a launch with a reader on stdout (the
    target's [tmw] realization takes [CatSim.fd1chan]). *)
Theorem alloc_mmap_strong_equiv_alg :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
         bf cf bs cs (inp : ProcInput),
  AllocSim.to_outcomes (run_segments source_segs inp rsp rmb)
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
    (with_vdso (vdso_run_init (ed_vdso rrnd))
       (init_model (segments_reserved (run_segments source_segs inp rsp rmb)) rbrk rmb rsp
          rlim inp))
    (AllocSim2.two_outcomes bf cf bs cs) ->
  MmapSim.tmw (run_segments target_segs inp asp amb)
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
    (with_vdso (vdso_run_init (ed_vdso arnd))
       (init_model (segments_reserved (run_segments target_segs inp asp amb)) abrk amb asp
          alim inp)) bf cf bs cs ->
  bufs_modeled bf -> bufs_modeled bs ->
  in_channel_reader inp = true ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    bf cf bs cs inp Hs Ht Hbf Hbs Hr.
  apply (shape_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd rlim
           target_segs apc aph asp abrk amb arnd alim
           (t_alt2 (t_writes bf (t_exit cf (in_fs inp))) (t_writes bs (t_exit cs (in_fs inp))))
           inp).
  - unfold init_config.
    eapply rz_conseq;
      [apply outcomes_realizes; [exact Hs | reflexivity | reflexivity]|].
    apply t_outcomes_two_alt2.
  - unfold init_config.
    apply (tmw_realizes (run_segments target_segs inp asp amb)
             (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
             (with_vdso (vdso_run_init (ed_vdso arnd))
                (init_model (segments_reserved (run_segments target_segs inp asp amb))
                   abrk amb asp alim inp))
             bf cf bs cs eq_refl eq_refl
             (init_model_fd1chan (segments_reserved (run_segments target_segs inp asp amb))
                abrk amb asp alim inp Hr) Ht Hbf Hbs).
Qed.

(** The same, in the shape of [OmniEquivalence.omni_strong_equiv], at the
    two role budgets. *)
Theorem alloc_mmap_omni_strong_equiv_alg :
  forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd
         bf cf bs cs (inp : ProcInput),
  AllocSim.to_outcomes (run_segments source_segs inp rsp rmb)
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
    (with_vdso (vdso_run_init (ed_vdso rrnd))
       (init_model (segments_reserved (run_segments source_segs inp rsp rmb)) rbrk rmb rsp
          source_alloc_limit inp))
    (AllocSim2.two_outcomes bf cf bs cs) ->
  MmapSim.tmw (run_segments target_segs inp asp amb)
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
    (with_vdso (vdso_run_init (ed_vdso arnd))
       (init_model (segments_reserved (run_segments target_segs inp asp amb)) abrk amb asp
          target_alloc_limit inp)) bf cf bs cs ->
  bufs_modeled bf -> bufs_modeled bs ->
  in_channel_reader inp = true ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd
    bf cf bs cs inp Hs Ht Hbf Hbs Hr.
  apply (shape_omni_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd
           target_segs apc aph asp abrk amb arnd
           (t_alt2 (t_writes bf (t_exit cf (in_fs inp))) (t_writes bs (t_exit cs (in_fs inp))))
           inp).
  - unfold init_config.
    eapply rz_conseq;
      [apply outcomes_realizes; [exact Hs | reflexivity | reflexivity]|].
    apply t_outcomes_two_alt2.
  - unfold init_config.
    apply (tmw_realizes (run_segments target_segs inp asp amb)
             (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
             (with_vdso (vdso_run_init (ed_vdso arnd))
                (init_model (segments_reserved (run_segments target_segs inp asp amb))
                   abrk amb asp target_alloc_limit inp))
             bf cf bs cs eq_refl eq_refl
             (init_model_fd1chan (segments_reserved (run_segments target_segs inp asp amb))
                abrk amb asp target_alloc_limit inp Hr) Ht Hbf Hbs).
Qed.


(* =========================================================================
   CHANNEL-PARAMETRIC SHAPE

   [t_writes_pick] and [cat_realizes] above are hardwired to channel 1.  These
   are their (fd, channel)-parametric twins, built on [CatSim]'s
   [to_wexit_ch]; [t_writes_ch_pick_1] and [cat_strong_equiv_alg] exhibit the
   channel-1 development as the instance.  A stderr-reporting binary uses
   [cat_ch_strong_equiv_alg] at [fd = ch = 2].
   ========================================================================= *)

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
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  node_ok segs (mkCfg ms model) (wr_index buf)
          (fun i => map (WriteEv ch) (firstn (proj1_sig i) buf))
          (fun i => mkCfg (advance_past_svc
                             (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                          model).
Proof.
  intros segs ms model fd ch x8 buf Hh Hlazy Hfdc H32 Hsvc Hno Hg Hr Hok Hbm Hnb. split.
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig].
    rewrite <- (apply_effect_copyins_no_write ms (len_word (firstn n buf))
                  [(ms_gpr ms 1, n)]).
    apply (sstep_syscall segs ms model x8
             (with_copyins [(ms_gpr ms 1, n)]
                (mkEffect (len_word (firstn n buf)) [] [])) model
             model (map (WriteEv ch) (firstn n buf))).
    + exact Hh.
    + exact Hsvc.
    + eapply write_ch_ok_n; eassumption.
    + exact Hh.
    + apply materialize_model_accesses_no_lazy. exact Hlazy.
  - intros e st Hss.
    destruct (sstep_write_ch_inv segs fd ch H32 ms model x8 buf e st
                Hh Hlazy Hfdc Hsvc Hno Hg Hr Hok Hbm Hnb Hss)
      as (n & Hn1 & Hn2 & -> & ->).
    exists (exist _ n (conj Hn1 Hn2)). split; reflexivity.
Qed.

Lemma rz_write_ch : forall segs ms model fd ch x8 buf T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model -> fd32 fd = fd ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     realizes segs
       (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model) T) ->
  realizes segs (mkCfg ms model) (t_write_ch ch buf T).
Proof.
  intros segs ms model fd ch x8 buf T Hh Hlazy Hfdc H32 Hsvc Hno Hg Hr Hok Hbm Hnb Hc.
  unfold t_write_ch.
  apply (rz_node segs (mkCfg ms model) (wr_index buf)
           (fun i => map (WriteEv ch) (firstn (proj1_sig i) buf))
           (fun i => mkCfg (advance_past_svc
                              (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                           model)
           (fun _ => T) (wr_full buf Hnb)).
  - eapply node_write_ch; eassumption.
  - eapply write_ch_rob; eassumption.
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
    | ms x8 buf bufs code Hsvc Hno Hg Hr Hok Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH];
    intros model Hh Hlazy Hfdc Hbm.
  - eapply rz_exit; eassumption.
  - apply Forall_cons_iff in Hbm as [Hb Hbs].
    rewrite t_writes_ch_pick_cons. eapply rz_write_ch; try eassumption.
    intros n Hn1 Hn2. apply IH; assumption.
  - eapply rz_step; try eassumption. apply IH; assumption.
Qed.

(** The channel-parametric [cat_strong_equiv_alg], on a launch with a
    reader on the far end of [fd]: the delivery shape this builds on is
    the reader-present one, because a reader-gone write KILLS the process
    (see [CatSim.fd1chan]). *)
Theorem cat_ch_strong_equiv_alg :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
         (fd ch : word) bufs code (inp : ProcInput),
  fd32 fd = fd ->
  (forall reserved brk0 mb1 sp1 lim1 inp1,
     in_channel_reader inp1 = true ->
     fdchan fd ch (init_model reserved brk0 mb1 sp1 lim1 inp1)) ->
  in_channel_reader inp = true ->
  to_wexit_ch (run_segments source_segs inp rsp rmb) fd
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
    bufs code ->
  to_wexit_ch (run_segments target_segs inp asp amb) fd
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
    bufs code ->
  bufs_modeled bufs ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    fd ch bufs code inp H32 Hinit Hrdr Hs Ht Hbm.
  apply (shape_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd rlim
           target_segs apc aph asp abrk amb arnd alim
           (t_writes_ch_pick ch bufs (t_exit code (in_fs inp))) inp).
  - unfold init_config.
    apply (cat_realizes_ch (run_segments source_segs inp rsp rmb) fd ch
             (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
             (with_vdso (vdso_run_init (ed_vdso rrnd))
                (init_model (segments_reserved (run_segments source_segs inp rsp rmb))
                   rbrk rmb rsp rlim inp))
             bufs code eq_refl eq_refl
             (Hinit (segments_reserved (run_segments source_segs inp rsp rmb))
                rbrk rmb rsp rlim inp Hrdr) H32 Hs Hbm).
  - unfold init_config.
    apply (cat_realizes_ch (run_segments target_segs inp asp amb) fd ch
             (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
             (with_vdso (vdso_run_init (ed_vdso arnd))
                (init_model (segments_reserved (run_segments target_segs inp asp amb))
                   abrk amb asp alim inp))
             bufs code eq_refl eq_refl
             (Hinit (segments_reserved (run_segments target_segs inp asp amb))
                abrk amb asp alim inp Hrdr) H32 Ht Hbm).
Qed.

(** The same, in the shape of [OmniEquivalence.omni_strong_equiv], at the
    two role budgets. *)
Theorem cat_ch_omni_strong_equiv_alg :
  forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd
         (fd ch : word) bufs code (inp : ProcInput),
  fd32 fd = fd ->
  (forall reserved brk0 mb1 sp1 lim1 inp1,
     in_channel_reader inp1 = true ->
     fdchan fd ch (init_model reserved brk0 mb1 sp1 lim1 inp1)) ->
  in_channel_reader inp = true ->
  to_wexit_ch (run_segments source_segs inp rsp rmb) fd
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
    bufs code ->
  to_wexit_ch (run_segments target_segs inp asp amb) fd
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
    bufs code ->
  bufs_modeled bufs ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd
    fd ch bufs code inp H32 Hinit Hrdr Hs Ht Hbm.
  apply (shape_omni_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd
           target_segs apc aph asp abrk amb arnd
           (t_writes_ch_pick ch bufs (t_exit code (in_fs inp))) inp).
  - unfold init_config.
    apply (cat_realizes_ch (run_segments source_segs inp rsp rmb) fd ch
             (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
             (with_vdso (vdso_run_init (ed_vdso rrnd))
                (init_model (segments_reserved (run_segments source_segs inp rsp rmb))
                   rbrk rmb rsp source_alloc_limit inp))
             bufs code eq_refl eq_refl
             (Hinit (segments_reserved (run_segments source_segs inp rsp rmb))
                rbrk rmb rsp source_alloc_limit inp Hrdr) H32 Hs Hbm).
  - unfold init_config.
    apply (cat_realizes_ch (run_segments target_segs inp asp amb) fd ch
             (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
             (with_vdso (vdso_run_init (ed_vdso arnd))
                (init_model (segments_reserved (run_segments target_segs inp asp amb))
                   abrk amb asp target_alloc_limit inp))
             bufs code eq_refl eq_refl
             (Hinit (segments_reserved (run_segments target_segs inp asp amb))
                abrk amb asp target_alloc_limit inp Hrdr) H32 Ht Hbm).
Qed.

(** ... and the fd-1 theorem is its instance, on a launch with a reader. *)
Corollary cat_strong_equiv_alg_via_ch :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
         bufs code (inp : ProcInput),
  in_channel_reader inp = true ->
  to_wexit (run_segments source_segs inp rsp rmb)
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
    bufs code ->
  to_wexit (run_segments target_segs inp asp amb)
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
    bufs code ->
  bufs_modeled bufs ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros. eapply (cat_ch_strong_equiv_alg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                    (Z_to_bv 64 1) (Z_to_bv 64 1));
    [ reflexivity
    | intros; apply fd1chan_fdchan; apply init_model_fd1chan; assumption
    | eassumption
    | apply to_wexit_ch_1; eassumption
    | apply to_wexit_ch_1; eassumption
    | eassumption ].
Qed.
