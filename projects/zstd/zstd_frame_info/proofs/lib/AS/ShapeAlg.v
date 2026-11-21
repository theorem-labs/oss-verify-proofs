(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the access_okb premise (vfs_write's access_ok range) on node_write1, rz_write1, node_write_ch and rz_write_ch, the realizes proofs re-proved for it; munmap under the alloc-only config: munmap_eff_nonrefusal, munmap_errno_spurious (errno answers are spurious refusals), node_munmap_cfg and rz_silent_all added, rz_munmap re-proved through them with a new premise over its munmap_errnos successors; #[using] attributes dropped from 3 lemmas; imports Vdso; rz_node takes RomBase.sys_rob, so rz_silent1, rz_silent_all, rz_emit1 and rz_alt2 take it too, discharged at the instruction, write (RomWrite.write1_rob, write_ch_rob), exit and munmap nodes; imports RomBase, RomWrite). *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem Require Import Vdso.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AS Require Import SimInv ExitSim CatSim MmapSim AllocSim WallSim.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AS Require Import RomBase RomWrite.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)

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

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition TSet := list event -> Prop.

Definition t_eq (T T' : TSet) : Prop := forall tr, T tr <-> T' tr.

Lemma t_eq_refl : forall T, t_eq T T. Proof. firstorder. Qed.
Lemma t_eq_sym : forall T T', t_eq T T' -> t_eq T' T. Proof. firstorder. Qed.
Lemma t_eq_trans : forall T1 T2 T3, t_eq T1 T2 -> t_eq T2 T3 -> t_eq T1 T3.
Proof. firstorder. Qed.

(* [comment removed for export] *)
Definition t_nil : TSet := fun tr => tr = [].

(* [comment removed for export] *)
Definition t_emit (evs : list event) (T : TSet) : TSet :=
  fun tr => is_prefix tr evs \/ exists tr', tr = evs ++ tr' /\ T tr'.

(* [comment removed for export] *)
Definition t_alt {I : Type} (f : I -> TSet) : TSet := fun tr => exists i, f i tr.

(* [comment removed for export] *)
Definition t_alt2 (A B : TSet) : TSet := fun tr => A tr \/ B tr.

(* [comment removed for export] *)
Definition t_exit (code : word) (fs : Fs.Fs) : TSet :=
  t_emit [ExitEv code fs] t_nil.

(* [comment removed for export] *)
Definition wr_index (buf : list byte) : Type :=
  {n : nat | (1 <= n)%nat /\ (n <= length buf)%nat}.

Definition wr_full (buf : list byte) (Hnb : (1 <= length buf)%nat)
    : wr_index buf :=
  exist _ (length buf) (conj Hnb (Nat.le_refl _)).

(* [comment removed for export] *)
Definition t_write_ch (ch : word) (buf : list byte) (T : TSet) : TSet :=
  t_alt (fun i : wr_index buf =>
           t_emit (map (WriteEv ch) (firstn (proj1_sig i) buf)) T).

(* [comment removed for export] *)
Definition t_writes_pick (bufs : list (list byte)) (T : TSet) : TSet :=
  fold_right (t_write_ch (Z_to_bv 64 1)) T bufs.

(* [comment removed for export] *)
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

(* [comment removed for export] *)

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

(* [comment removed for export] *)
Lemma t_emit_has_nil : forall e T, t_emit e T [].
Proof. intros e T. left. apply is_prefix_nil. Qed.

Lemma t_writes_ch_exit_has_nil : forall ch bufs code fs,
  t_writes_ch ch bufs (t_exit code fs) [].
Proof.
  intros ch [|b bs] code fs; cbn [t_writes_ch fold_right];
    apply t_emit_has_nil.
Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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


(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition node_ok (c : config) (I : Type)
    (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstep_cfg segs ACFG c (evs i) (SNext (nx i)))
  /\ (forall e st, sstep_cfg segs ACFG c e st -> exists i, e = evs i /\ st = SNext (nx i)).

Definition pnode_ok (c : config) (I : Type)
    (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstep segs c (evs i) (SNext (nx i)))
  /\ (forall e st, sstep segs c e st -> exists i, e = evs i /\ st = SNext (nx i)).

#[using="Type"] Lemma node_ok_of_pnode : forall c I evs nx,
  cfg_transparent segs c -> pnode_ok c I evs nx -> node_ok c I evs nx.
Proof.
  intros c I evs nx Htr [Hcomp Hsound]. split.
  - intros i. apply Htr. apply Hcomp.
  - intros e st Hss. apply Hsound. exact (sstep_of_cfg segs ACFG _ _ _ Hss).
Qed.

#[using="Type"] Lemma transparent_exit_no : forall ms model x8,
  ms_svc_pending ms = Some x8 -> is_exit_no x8 -> cfg_transparent segs (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc [E|E]; apply (transparent_nonalloc segs ms model x8 Hsvc); rewrite E;
    apply alloc_no_b_false; reflexivity.
Qed.

(* [comment removed for export] *)
Inductive realizes : config -> TSet -> Prop :=
| rz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                   (T : I -> TSet) (i0 : I),
    node_ok c I evs nx ->
    (* LPS 727298f3: the node's system call reads no byte the run's backing adds
       ([RomBase.sys_rob]; [RomStable.run_init] lifts a walk to the run's start) *)
    sys_rob segs c ->
    (forall i, realizes (nx i) (T i)) ->
    realizes c (t_alt (fun i => t_emit (evs i) (T i)))
| rz_halt : forall c,
    m_halted (cfg_model c) <> None ->
    realizes c t_nil
| rz_conseq : forall c T T',
    realizes c T -> t_eq T T' -> realizes c T'.

(* [comment removed for export] *)

#[using="Type"] Lemma realizes_nonempty : forall c T, realizes c T -> T [].
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

#[using="Type"] Lemma realizes_pclosed : forall c T, realizes c T ->
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

(* [comment removed for export] *)

#[using="Type"] Lemma realizes_star_only : forall c T, realizes c T ->
  forall tr c', star_cfg segs ACFG c tr c' -> T tr.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq];
    intros tr c' Hstar.
  - inversion Hstar as [|c1 e c2 tr2 c3 Hss Hstar2]; subst.
    + exists i0. left. apply is_prefix_nil.
    + destruct Hnode as [_ Hsound].
      destruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
      inversion Heq2; subst c2.
      exists i. right. exists tr2. split; [reflexivity | eapply IH; exact Hstar2].
  - destruct (star_cfg_halted_nil segs ACFG c tr c' Hh Hstar) as [-> _]. reflexivity.
  - apply Heq. eapply IH; exact Hstar.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma realizes_admits : forall c T, realizes c T ->
  forall tr, T tr -> obs_trace_cfg segs ACFG c tr.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq];
    intros tr HT.
  - destruct Hnode as [Hcomp _].
    destruct HT as [i [Hpre | (tr0 & -> & HT0)]].
    + exists (evs i), (nx i). split; [apply star_cfg_one; apply Hcomp | exact Hpre].
    + destruct (IH i tr0 HT0) as (tr'' & c'' & Hstar & Hp).
      exists (evs i ++ tr''), c''.
      split; [eapply star_cfg_step; [apply Hcomp | exact Hstar] | apply is_prefix_app_mono; exact Hp].
  - unfold t_nil in HT; subst tr. apply obs_trace_cfg_nil.
  - apply IH. apply Heq. exact HT.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem realizes_obs_iff : forall c T, realizes c T ->
  forall tr, obs_trace_cfg segs ACFG c tr <-> T tr.
Proof.
  intros c T H tr. split.
  - intros (tr' & c' & Hstar & Hp).
    eapply realizes_pclosed; [exact H | eapply realizes_star_only; eauto | exact Hp].
  - apply realizes_admits; exact H.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma sstep_halted_none : forall c e st,
  sstep segs c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.

#[using="Type"] Lemma realizes_step : forall c T e c',
  realizes c T -> sstep_cfg segs ACFG c e (SNext c') -> exists T', realizes c' T'.
Proof.
  intros c T e c' H; revert e c';
  induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq];
    intros e c' Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
    inversion Heq2; subst c'. exists (T i). apply Hcont.
  - exfalso. apply Hh. eapply sstep_cfg_halted_none; exact Hss.
  - eapply IH; exact Hss.
Qed.

#[using="Type"] Lemma realizes_no_sserror : forall c T e,
  realizes c T -> ~ sstep_cfg segs ACFG c e SError.
Proof.
  intros c T e H; revert e;
  induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq];
    intros e Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
  - apply Hh. eapply sstep_cfg_halted_none; exact Hss.
  - eapply IH; exact Hss.
Qed.

Definition rz_path (c : config) : Prop := exists T, realizes c T.

#[using="Type"] Lemma rz_path_star : forall c tr c',
  star_cfg segs ACFG c tr c' -> rz_path c -> rz_path c'.
Proof.
  intros c tr c' Hstar. induction Hstar as [c | c1 evs c2 tr c3 Hss Hstar IH]; intros Hp; [exact Hp|].
  apply IH. destruct Hp as [T HT]. exact (realizes_step c1 T evs c2 HT Hss).
Qed.

#[using="Type"] Theorem realizes_no_error : forall c T, realizes c T -> ~ reaches_error_cfg segs ACFG c.
Proof.
  intros c T H (tr & c' & evs & Hstar & Herr).
  destruct (rz_path_star c tr c' Hstar (ex_intro _ T H)) as [T' HT'].
  exact (realizes_no_sserror c' T' evs HT' Herr).
Qed.


(* [comment removed for export] *)

#[using="Type"] Lemma t_alt_unit : forall (f : unit -> TSet), t_eq (t_alt f) (f tt).
Proof.
  intros f tr. split; [intros [[] Hf]; exact Hf | intro Hf; exists tt; exact Hf].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_silent1 : forall c c' T,
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

(* [comment removed for export] *)
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

#[using="Type"] Lemma rz_emit1 : forall c c' e T,
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

(* [comment removed for export] *)
#[using="Type"] Lemma rz_alt2 : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
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

(* [comment removed for export] *)

#[using="Type"] Lemma node_instr : forall ms model ms',
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  node_ok (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' Hh Hlazy Hsvc Hstep.
  apply node_ok_of_pnode; [apply transparent_instr; exact Hsvc |]. split.
  - intros []. apply (sstep_instr segs ms model ms' model);
      [assumption | assumption |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
  - intros e st Hss.
    destruct (sstep_instr_inv segs ms model ms' e st Hlazy Hsvc Hstep Hss) as [-> ->].
    exists tt. split; reflexivity.
Qed.

#[using="Type"] Lemma rz_step : forall ms model ms' T,
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

#[using="Type"] Lemma rz_msteps : forall ms ms' model T,
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

(* [comment removed for export] *)
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
  (* node_ok is stated over sstep_cfg segs ACFG (:244-247), while sstep_syscall below gives
     a plain sstep, so the two do not unify and without the bridge the build reads :542
     "Unable to unify sstep segs ... with sstep_cfg segs ACFG ...".  The bridge is this
     unit's own node_ok_of_pnode (:254-255) with a cfg_transparent witness.  64 (write) is
     NOT in the alloc family, so alloc_no_b 64 = false holds by reflexivity -- unlike 215,
     where the same goal is FALSE at #38 and the family-off route is required instead.
     Argument order is this unit's Lib/Cfg.v:236 discharged over segs, the spelling
     AS/RefNodes.v:636 already uses.  node_write1 is the ONLY node_ok lemma in this file
     that lacked the step; the other six already have it. *)
  intros ms model x8 buf Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hbm Hnb.
  apply node_ok_of_pnode; [apply (transparent_nonalloc_no segs ms model x8 64 Hsvc Hno); reflexivity |]. split.
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

(* [comment removed for export] *)
#[using="Type"] Lemma rz_exit : forall ms model x8,
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
  - apply node_ok_of_pnode; [exact (transparent_exit_no ms model x8 Hsvc Hx8) |]. split.
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
  - exact (sys_rob_exit segs ms model x8 Hsvc Hx8).
  - apply rz_halt. cbn. discriminate.
Qed.

(* --- munmap (215) under ACFG -----------------------------------------------
   All MEASURED at 727298f3 unless marked.
   - Run.v:1865  alloc_mark_sysnos = [214;215;216;222;226].  215 IS on the list,
     so alloc_no_b 215 = true and the transparent_nonalloc_no route node_write1
     takes for 64 (:548) is UNAVAILABLE here -- the note at :542 is confirmed.
   - Run.v:1788  injected_table's row for 215 is
     [mkInjectedArm 215 FamAlloc munmap_errnos], and ACFG = alloc_only_cfg false
     has sc_alloc = false (Run.v:1689-1690), so injected_family_off ACFG = true
     (Lib/Cfg.v acfg_family_off_215) and refusal_b = ret_in_errnos munmap_errnos
     (Lib/Cfg.v refusal_b_215).  The transparent_family_on route is therefore
     unavailable too: BOTH cfg_transparent routes are closed for 215.
   - Run.v:2285-2294  sstep_cfg_syscall's fourth premise is
     ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff.
   - Checks/SpuriousCfg.v:903-913 munmap_refusal_spurious_alloc_only: at 215
     EVERY admitted refusal is spurious under alloc_only_cfg false.
   So the -ENOMEM successors are not sstep_cfg steps at all, and the old
   two-branch index set {e | In e munmap_errnos} + unit made node_ok FALSE,
   not merely unprovable.  The repair is the INDEX SET.  rz_munmap's statement
   below is UNCHANGED: its HA premise is now unused, and leaving an unused
   premise is the conservative direction -- dropping it would be a
   strengthening.  munmap_refusal_spurious_alloc_only is re-derived here from
   this unit's own Lib/Cfg.v pieces so that no Checks file has to be required. *)
Lemma munmap_eff_nonrefusal : forall ms model x8,
  bv_unsigned x8 = 215%Z ->
  refusal_b (sys_input segs ms x8) model (eff_ret (munmap_eff ms)) = false.
Proof.
  intros ms model x8 Hno.
  assert (Hin : bv_unsigned (in_sysno (sys_input segs ms x8)) = 215%Z)
    by (rewrite in_sysno_sys_input; exact Hno).
  rewrite (refusal_b_215 _ _ _ Hin). reflexivity.
Qed.

Lemma munmap_errno_spurious : forall ms model x8 e,
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  In e munmap_errnos ->
  spurious_refusal_cfg ACFG (sys_input segs ms x8) model (mkEffect (errno_ret e) [] []).
Proof.
  intros ms model x8 e Hno Hargs He.
  assert (Hin : bv_unsigned (in_sysno (sys_input segs ms x8)) = 215%Z)
    by (rewrite in_sysno_sys_input; exact Hno).
  apply (refusal_spurious_of_grant ACFG (sys_input segs ms x8) model
           (mkEffect (errno_ret e) [] []) (munmap_eff ms)
           (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
  - exact (acfg_family_off_215 _ Hin).
  - rewrite (refusal_b_215 _ _ _ Hin).
    exact (ret_in_errnos_errno munmap_errnos e He).
  - exact (munmap_ok segs ms x8 model Hno Hargs).
  - exact (munmap_eff_nonrefusal ms model x8 Hno).
Qed.

(* The one-successor node.  Shared with SpinAlg.node_munmap, which states the
   same thing and whose own two-branch index set was false for the same reason. *)
Lemma node_munmap_cfg : forall ms model x8,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  node_ok (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                    (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Hargs. split.
  - intros [].
    apply (sstep_cfg_syscall_nonrefusal segs ACFG ms model x8 (munmap_eff ms)
             (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
             (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
    + exact Hh.
    + exact Hsvc.
    + apply munmap_ok; assumption.
    + exact (munmap_eff_nonrefusal ms model x8 Hno).
    + rewrite munmap_model_halted; exact Hh.
    + apply materialize_model_accesses_no_lazy.
      exact (munmap_model_no_lazy _ _ _ Hlazy).
  - intros evs st Hss.
    destruct (sstep_cfg_svc_inv_g segs ACFG ms model x8 evs st Hsvc Hss)
      as [(eff & mo' & mo'' & Hspec & Hns & Hh' & Hmat & ->)
        | [(eff & mo' & evs0 & Hspec & Hns & Hh' & Hmat & -> & ->)
        | [(eff & mo' & evs0 & code & Hspec & Hh' & Hk' & -> & ->)
        | [(eff & mo' & evs0 & sig & Hspec & Hk' & -> & ->)
        | (Hspec & -> & ->)]]]].
    + destruct (munmap_ok_inv segs ms x8 model eff mo' evs Hno Hargs Hspec)
        as (-> & [(er & Her & -> & ->) | (-> & ->)]).
      * exfalso. exact (Hns (munmap_errno_spurious ms model x8 er Hno Hargs Her)).
      * rewrite (materialize_model_accesses_no_lazy _ _
                   (munmap_model_no_lazy _ _ _ Hlazy)) in Hmat.
        inversion Hmat; subst. exists tt. split; reflexivity.
    + exfalso.
      destruct (munmap_ok_inv segs ms x8 model eff mo' evs0 Hno Hargs Hspec)
        as (_ & [(er & Her & -> & ->) | (-> & ->)]).
      * rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat.
        discriminate Hmat.
      * rewrite (materialize_model_accesses_no_lazy _ _
                   (munmap_model_no_lazy _ _ _ Hlazy)) in Hmat.
        discriminate Hmat.
    + exfalso.
      destruct (munmap_ok_inv segs ms x8 model eff mo' evs0 Hno Hargs Hspec)
        as (_ & [(er & Her & _ & ->) | (_ & ->)]).
      * rewrite Hh in Hh'. discriminate Hh'.
      * rewrite munmap_model_halted, Hh in Hh'. discriminate Hh'.
    + exfalso.
      destruct (munmap_ok_inv segs ms x8 model eff mo' evs0 Hno Hargs Hspec)
        as (_ & [(er & Her & _ & ->) | (_ & ->)]).
      * rewrite (m_killed_of_m_halted_none _ Hh) in Hk'. discriminate Hk'.
      * rewrite m_killed_of_m_halted_none in Hk';
          [discriminate Hk' | rewrite munmap_model_halted; exact Hh].
    + exfalso. exact (munmap_no_unmodeled segs ms x8 model Hno Hargs Hspec).
Qed.

(* [comment removed for export] *)
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
  (* HA is deliberately unused: see the note above node_munmap_cfg. *)
  intros ms model x8 T Hh Hlazy Hsvc Hno Hargs HA HB.
  apply (rz_silent_all (mkCfg ms model) unit
           (fun _ => mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                           (munmap_model (ms_gpr ms 0)
                                         (page_round_up (ms_gpr ms 1)) model))
           T tt).
  - exact (node_munmap_cfg ms model x8 Hh Hlazy Hsvc Hno Hargs).
  - eapply sys_rob_memfree; [exact Hsvc | rewrite Hno; exact memfree_215].
  - intros []. exact HB.
Qed.

End WithSegs.

(* [comment removed for export] *)

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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


(* [comment removed for export] *)

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
  intros segs ms model fd ch x8 buf Hh Hlazy Hfdc H32 Hsvc Hno Hg Hr Hok Hbm Hnb.
  (* The generalised-channel twin of node_write1 (:520), and the EASY half of the
     same bridge: 64 is NOT in alloc_mark_sysnos (727298f3:Run.v:1865 is
     [214;215;216;222;226]), so alloc_no_b 64 = false by reflexivity and
     transparent_nonalloc_no applies -- unlike 215, where both transparency routes
     are shut and the index set had to move instead.  Same text as :548.  No index
     set moves and no statement changes; the two halves below are unchanged,
     because pnode_ok states them over plain sstep, which is what they already
     prove and what sstep_write_ch_inv already consumes. *)
  apply node_ok_of_pnode;
    [apply (transparent_nonalloc_no segs ms model x8 64 Hsvc Hno); reflexivity |].
  split.
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
  - apply (write_ch_rob segs ms model fd ch x8 buf); assumption.
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
