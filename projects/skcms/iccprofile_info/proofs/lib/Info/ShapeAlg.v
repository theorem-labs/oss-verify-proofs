(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require PropExec RelSpec SimInv ExitSim CatSim MmapSim AllocSim.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require CatExec.
Unset Nia Cache.  (* [comment removed for export] *)

Module AllocSim2.
(* [comment removed for export] *)

Import Stdlib.NArith.NArith Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SimInv OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ExitSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.AllocSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim.
Unset Lia Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition two_outcomes (bf : list (list byte)) (cf : word)
    (bs : list (list byte)) (cs : word)
    : (list (list byte) * word) -> Prop :=
  fun o => o = (bf, cf) \/ o = (bs, cs).

End AllocSim2.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require WallSim.

(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec RelSpec SimInv ExitSim CatSim MmapSim AllocSim. Import AllocSim2. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import WallSim.
Unset Lia Cache.

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
Lemma two_traces_t_alt2 : forall bf cf bs cs fs tr,
  t_alt2 (t_writes bf (t_exit cf fs)) (t_writes bs (t_exit cs fs)) tr
  <-> MmapSim.two_traces bf cf bs cs fs tr.
Proof.
  intros. unfold t_alt2, MmapSim.two_traces.
  rewrite !t_writes_exit_iff. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition CFG : SpuriousCfg := mkSpuriousCfg false true true true true true.

(* [comment removed for export] *)
Definition alloc_no (x8 : word) : bool :=
  match injected_arm (bv_unsigned x8) with
  | Some a => negb (family_may_fail CFG (ia_family a))
  | None => false
  end.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition node_ok_s (c : config) (I : Type)
    (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstep segs c (evs i) (SNext (nx i)))
  /\ (forall e st, sstep segs c e st -> exists i, e = evs i /\ st = SNext (nx i)).

Definition node_ok (c : config) (I : Type)
    (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstep_cfg segs CFG c (evs i) (SNext (nx i)))
  /\ (forall e st, sstep_cfg segs CFG c e st -> exists i, e = evs i /\ st = SNext (nx i)).

(* [comment removed for export] *)
Definition nonalloc (c : config) : Prop :=
  forall x8, ms_svc_pending (cfg_ms c) = Some x8 ->
    injected_family_off CFG (sys_input segs (cfg_ms c) x8) = false.

Lemma nonalloc_instr : forall ms model, ms_svc_pending ms = None -> nonalloc (mkCfg ms model).
Proof. intros ms model H x8 H'. cbn [cfg_ms] in H'. congruence. Qed.

Lemma nonalloc_no : forall ms model x8,
  ms_svc_pending ms = Some x8 -> alloc_no x8 = false -> nonalloc (mkCfg ms model).
Proof.
  intros ms model x8 H Hno y H'. cbn [cfg_ms] in *. rewrite H in H'. injection H' as <-.
  exact Hno.
Qed.

(* [comment removed for export] *)
Lemma sstep_cfg_of_nonalloc : forall c e st,
  nonalloc c -> sstep segs c e st -> sstep_cfg segs CFG c e st.
Proof.
  intros c e st Hna H. destruct H as
    [ms model ms' model' Hh Hsvc Hacc
    | ms model Hh Hsvc Hacc
    | ms model Hh Hsvc Hacc
    | ms model x8 eff model' model'' evs Hh Hsvc Hspec Hh' Hmat
    | ms model x8 eff model' evs Hh Hsvc Hspec Hh' Hmat
    | ms model x8 eff model' evs code Hh Hsvc Hspec Hh' Hk
    | ms model x8 eff model' evs sig Hh Hsvc Hspec Hk
    | ms model x8 Hh Hsvc Hspec].
  - eapply sstep_cfg_instr; eassumption.
  - eapply sstep_cfg_instr_fault; eassumption.
  - eapply sstep_cfg_instr_unmodeled; eassumption.
  - eapply sstep_cfg_syscall; try eassumption.
    intros (Hoff & _ & _). specialize (Hna x8 Hsvc). cbn [cfg_ms] in Hna. rewrite Hna in Hoff. discriminate.
  - eapply sstep_cfg_syscall_materialization_fault; try eassumption.
    intros (Hoff & _ & _). specialize (Hna x8 Hsvc). cbn [cfg_ms] in Hna. rewrite Hna in Hoff. discriminate.
  - eapply sstep_cfg_exit; eassumption.
  - (* [comment removed for export] *) eapply sstep_cfg_killed; eassumption.
  - eapply sstep_cfg_syscall_unmodeled; eassumption.
Qed.

Lemma node_ok_of_s : forall c I evs nx,
  nonalloc c -> node_ok_s c I evs nx -> node_ok c I evs nx.
Proof.
  intros c I evs nx Hna [Hc Hs]. split.
  - intros i. apply sstep_cfg_of_nonalloc; [exact Hna | apply Hc].
  - intros e st H. apply Hs. exact (sstep_cfg_sub segs CFG c e st H).
Qed.

(* [comment removed for export] *)
Definition forced_refusals (c : config) : Prop :=
  forall x8, ms_svc_pending (cfg_ms c) = Some x8 ->
    forall eff m' evs, syscall_spec (sys_input segs (cfg_ms c) x8) (cfg_model c) (Ok eff m' evs) ->
      refusal_b (sys_input segs (cfg_ms c) x8) (cfg_model c) (eff_ret eff) = true.

Lemma sstep_cfg_of_forced : forall c e st,
  forced_refusals c -> sstep segs c e st -> sstep_cfg segs CFG c e st.
Proof.
  intros c e st Hfo H. destruct H as
    [ms model ms' model' Hh Hsvc Hacc
    | ms model Hh Hsvc Hacc
    | ms model Hh Hsvc Hacc
    | ms model x8 eff model' model'' evs Hh Hsvc Hspec Hh' Hmat
    | ms model x8 eff model' evs Hh Hsvc Hspec Hh' Hmat
    | ms model x8 eff model' evs code Hh Hsvc Hspec Hh' Hk
    | ms model x8 eff model' evs sig Hh Hsvc Hspec Hk
    | ms model x8 Hh Hsvc Hspec].
  - eapply sstep_cfg_instr; eassumption.
  - eapply sstep_cfg_instr_fault; eassumption.
  - eapply sstep_cfg_instr_unmodeled; eassumption.
  - eapply sstep_cfg_syscall; try eassumption.
    intros (_ & _ & (eff' & m2 & evs2 & Hs2 & Hr2)).
    pose proof (Hfo x8 Hsvc eff' m2 evs2 Hs2) as Hr. cbn [cfg_ms cfg_model] in Hr. congruence.
  - eapply sstep_cfg_syscall_materialization_fault; try eassumption.
    intros (_ & _ & (eff' & m2 & evs2 & Hs2 & Hr2)).
    pose proof (Hfo x8 Hsvc eff' m2 evs2 Hs2) as Hr. cbn [cfg_ms cfg_model] in Hr. congruence.
  - eapply sstep_cfg_exit; eassumption.
  - (* [comment removed for export] *) eapply sstep_cfg_killed; eassumption.
  - eapply sstep_cfg_syscall_unmodeled; eassumption.
Qed.

Lemma node_ok_of_s_forced : forall c I evs nx,
  forced_refusals c -> node_ok_s c I evs nx -> node_ok c I evs nx.
Proof.
  intros c I evs nx Hfo [Hc Hs]. split.
  - intros i. apply sstep_cfg_of_forced; [exact Hfo | apply Hc].
  - intros e st H. apply Hs. exact (sstep_cfg_sub segs CFG c e st H).
Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)

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

(* [comment removed for export] *)

Lemma sstep_cfg_halted_none : forall c e st,
  sstep_cfg segs CFG c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.

Lemma star_cfg_halted_nil : forall c tr c',
  m_halted (cfg_model c) <> None -> star_cfg segs CFG c tr c' -> tr = [].
Proof.
  intros c tr c' Hh H. destruct H as [c | c1 evs c2 tr c3 Hss _]; [reflexivity|].
  exfalso. apply Hh. exact (sstep_cfg_halted_none _ _ _ Hss).
Qed.

Lemma realizes_star_only : forall c T, realizes c T ->
  forall tr c', star_cfg segs CFG c tr c' -> T tr.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros tr c' Hstar.
  - inversion Hstar as [|c1 e c2 tr2 c3 Hss Hstar2]; subst.
    + exists i0. left. apply is_prefix_nil.
    + destruct Hnode as [_ Hsound].
      destruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
      inversion Heq2; subst c2.
      exists i. right. exists tr2. split; [reflexivity | eapply IH; exact Hstar2].
  - rewrite (star_cfg_halted_nil c tr c' Hh Hstar). reflexivity.
  - apply Heq. eapply IH; exact Hstar.
Qed.

(* [comment removed for export] *)

Lemma obs_trace_cfg_nil : forall c, obs_trace_cfg segs CFG c [].
Proof. intros c. exists [], c. split; [apply star_cfg_refl | apply is_prefix_nil]. Qed.

Lemma star_cfg_one : forall c evs c', sstep_cfg segs CFG c evs (SNext c') -> star_cfg segs CFG c evs c'.
Proof.
  intros c evs c' H. rewrite <- (app_nil_r evs).
  econstructor; [exact H | apply star_cfg_refl].
Qed.

Lemma realizes_admits : forall c T, realizes c T ->
  forall tr, T tr -> obs_trace_cfg segs CFG c tr.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
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
Theorem realizes_obs_iff : forall c T, realizes c T ->
  forall tr, obs_trace_cfg segs CFG c tr <-> T tr.
Proof.
  intros c T H tr. split.
  - intros (tr' & c' & Hstar & Hp).
    eapply realizes_pclosed; [exact H | eapply realizes_star_only; eauto | exact Hp].
  - apply realizes_admits; exact H.
Qed.

(* [comment removed for export] *)

Lemma sstep_halted_none : forall c e st,
  sstep segs c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.

Lemma realizes_step : forall c T e c',
  realizes c T -> sstep_cfg segs CFG c e (SNext c') -> exists T', realizes c' T'.
Proof.
  intros c T e c' H; revert e c';
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros e c' Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
    inversion Heq2; subst c'. exists (T i). apply Hcont.
  - exfalso. apply Hh. eapply sstep_cfg_halted_none; exact Hss.
  - eapply IH; exact Hss.
Qed.

Lemma realizes_no_sserror : forall c T e,
  realizes c T -> ~ sstep_cfg segs CFG c e SError.
Proof.
  intros c T e H; revert e;
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros e Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
  - apply Hh. eapply sstep_cfg_halted_none; exact Hss.
  - eapply IH; exact Hss.
Qed.

Definition rz_path (c : config) : Prop := exists T, realizes c T.

Lemma star_cfg_inv (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep_cfg segs CFG c evs (SNext c') -> Inv c') :
  forall c tr c', Inv c -> star_cfg segs CFG c tr c' -> Inv c'.
Proof.
  intros c tr c' HInv Hstar. induction Hstar; [exact HInv|].
  apply IHHstar. eapply Hstep; eauto.
Qed.

Theorem realizes_no_error : forall c T, realizes c T -> ~ reaches_error_cfg segs CFG c.
Proof.
  intros c T H (tr & c' & evs & Hstar & Hss).
  destruct (star_cfg_inv rz_path
              ltac:(intros c1 e c2 (T1 & H1) Hs; eapply realizes_step; eauto)
              c tr c' (ex_intro _ T H) Hstar) as (T' & H').
  exact (realizes_no_sserror c' T' evs H' Hss).
Qed.

(* [comment removed for export] *)

Lemma t_alt_unit : forall (f : unit -> TSet), t_eq (t_alt f) (f tt).
Proof.
  intros f tr. split; [intros [[] Hf]; exact Hf | intro Hf; exists tt; exact Hf].
Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)

Lemma node_instr : forall ms model ms',
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  node_ok (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' Hh Hlazy Hsvc Hstep.
  apply node_ok_of_s; [apply nonalloc_instr; exact Hsvc|]. split.
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


(* [comment removed for export] *)
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
  - apply node_ok_of_s.
    { apply (nonalloc_no ms model x8 Hsvc). unfold alloc_no.
      destruct Hx8 as [E | E]; rewrite E; reflexivity. }
    split.
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
  - apply rz_halt. cbn. discriminate.
Qed.

(* [comment removed for export] *)
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
  intros ms model x8 T Hh Hlazy Hsvc Hno Hargs Hc.
  eapply rz_silent1; [| exact Hc].
  apply node_ok_of_s; [apply (nonalloc_no ms model x8 Hsvc); unfold alloc_no; rewrite Hno; reflexivity|].
  split.
  - intros []. apply (sstep_syscall segs ms model x8 (munmap_eff ms)
                        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
                        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
    + exact Hh.
    + exact Hsvc.
    + apply munmap_ok; assumption.
    + rewrite munmap_model_halted; exact Hh.
    + apply materialize_model_accesses_no_lazy.
      exact (munmap_model_no_lazy _ _ _ Hlazy).
  - intros e st Hss.
    destruct (sstep_munmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hss)
      as [-> ->].
    exists tt. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sstep_cfg_svc_inv : forall ms model x8 e st,
  ms_svc_pending ms = Some x8 ->
  sstep_cfg segs CFG (mkCfg ms model) e st ->
  (exists eff model' evs,
      syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)
      /\ ((exists model'', ~ spurious_refusal_cfg CFG (sys_input segs ms x8) model eff
             /\ m_halted model' = None /\ e = evs
             /\ materialize_model_accesses model' (syscall_effect_accesses eff) = Some model''
             /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model''))
          \/ (~ spurious_refusal_cfg CFG (sys_input segs ms x8) model eff
              /\ m_halted model' = None /\ e = []
              /\ materialize_model_accesses model' (syscall_effect_accesses eff) = None
              /\ st = SError)
          \/ (exists code, m_halted model' = Some code
              /\ e = evs ++ [ExitEv code (m_fs model')]
              /\ st = SNext (mkCfg ms model'))
          \/ (exists sig, m_killed model' = Some sig
              /\ e = evs ++ [KillEv sig (m_fs model')]
              /\ st = SNext (mkCfg ms model'))))
  \/ (syscall_spec (sys_input segs ms x8) model Unmodeled /\ e = [] /\ st = SError).
Proof.
  intros ms model x8 e st Hsvc Hss.
  inversion Hss; subst; try congruence.
  - match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split; [eassumption|].
    left. eexists. repeat split; eauto.
  - match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split; [eassumption|].
    right. left. repeat split; auto.
  - match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split; [eassumption|].
    right. right. left. eexists. repeat split; eauto.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split; [eassumption|].
    right. right. right. eexists. repeat split; eauto.
  - match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    right. repeat split; auto.
Qed.

(* [comment removed for export] *)
Lemma node_alloc_success : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (R : outcome SyscallEffect -> Prop) (i0 : I),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  injected_family_off CFG (sys_input segs ms x8) = true ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> R o) ->
  (forall i, R (Ok (effs i) (ms' i) [])) ->
  (forall i, refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = false) ->
  (forall o, R o -> (exists i, o = Ok (effs i) (ms' i) [])
                   \/ (exists eff m' evs, o = Ok eff m' evs
                          /\ refusal_b (sys_input segs ms x8) model (eff_ret eff) = true
                          /\ m_halted m' = None)) ->
  ~ R Unmodeled ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  node_ok (mkCfg ms model) I (fun _ => [])
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' R i0 Hh Hsvc Hoff HR Hin Hnr Hout Hnu Hh' Hlazy. split.
  - intros i. apply (sstep_cfg_syscall segs CFG ms model x8 (effs i) (ms' i) (ms' i) []).
    + exact Hh.
    + exact Hsvc.
    + apply HR, Hin.
    + intros (_ & Hr & _). rewrite Hnr in Hr. discriminate.
    + apply Hh'.
    + apply materialize_model_accesses_no_lazy. apply Hlazy.
  - intros e st Hss.
    assert (Hsp : forall eff m' evs, R (Ok eff m' evs) ->
                  refusal_b (sys_input segs ms x8) model (eff_ret eff) = true ->
                  spurious_refusal_cfg CFG (sys_input segs ms x8) model eff).
    { intros eff m' evs _ Hr. split; [exact Hoff|]. split; [exact Hr|].
      exists (effs i0), (ms' i0), []. split; [apply HR, Hin | apply Hnr]. }
    destruct (sstep_cfg_svc_inv ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hns & Hh2 & -> & Hmat & ->) | [(Hns & Hh2 & -> & Hmat & ->) | [(code & Hh2 & -> & ->) | (sig & Hk2 & -> & ->)]]])
         | (Hc & -> & ->)].
    + apply HR in Hc. destruct (Hout _ Hc) as [(i & Hi) | (eff' & m' & evs' & Hi & Hr & _)].
      * apply Ok_inj in Hi as (-> & -> & ->).
        rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat. injection Hmat as <-.
        exists i. split; reflexivity.
      * apply Ok_inj in Hi as (-> & -> & ->). exfalso. exact (Hns (Hsp _ _ _ Hc Hr)).
    + apply HR in Hc. destruct (Hout _ Hc) as [(i & Hi) | (eff' & m' & evs' & Hi & Hr & _)].
      * apply Ok_inj in Hi as (-> & -> & ->).
        rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat. discriminate.
      * apply Ok_inj in Hi as (-> & -> & ->). exfalso. exact (Hns (Hsp _ _ _ Hc Hr)).
    + apply HR in Hc. destruct (Hout _ Hc) as [(i & Hi) | (eff' & m' & evs' & Hi & _ & Hhm)].
      * apply Ok_inj in Hi as (-> & -> & ->). rewrite Hh' in Hh2. discriminate.
      * apply Ok_inj in Hi as (-> & -> & ->). rewrite Hhm in Hh2. discriminate.
    + (* [comment removed for export] *)
      apply HR in Hc. destruct (Hout _ Hc) as [(i & Hi) | (eff' & m' & evs' & Hi & _ & Hhm)].
      * apply Ok_inj in Hi as (-> & -> & ->). rewrite (m_killed_of_m_halted_none _ (Hh' i)) in Hk2. discriminate.
      * apply Ok_inj in Hi as (-> & -> & ->). rewrite (m_killed_of_m_halted_none _ Hhm) in Hk2. discriminate.
    + exfalso. apply Hnu. apply HR. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma refusal_b_arm : forall i m ret (no : Z) fam es,
  bv_unsigned (in_sysno i) = no -> no <> 214%Z ->
  injected_arm no = Some (mkInjectedArm no fam es) ->
  refusal_b i m ret = ret_in_errnos es ret.
Proof.
  intros i m ret no fam es Hno H214 Harm. unfold refusal_b. rewrite Hno.
  replace (no =? 214)%Z with false by (symmetry; apply Z.eqb_neq; exact H214).
  rewrite Harm. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ret_in_errnos_small : forall es (ret : word),
  Forall (fun e => (1 <= e <= 4095)%Z) es ->
  (bv_unsigned ret < two_pow_64 - 4095)%Z ->
  ret_in_errnos es ret = false.
Proof.
  intros es ret Hes Hr. unfold ret_in_errnos.
  induction Hes as [|e es He Hes IH]; [reflexivity|]. cbn [existsb].
  rewrite IH, orb_false_r. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E.
  rewrite errno_ret_unsigned in E by lia. lia.
Qed.

Lemma injected_arm_222 : injected_arm 222%Z = Some (mkInjectedArm 222%Z FamAlloc mmap_errnos).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mmap_spurious : forall ms model x8 e a,
  bv_unsigned x8 = 222%Z -> mmap_args_ok ms -> In e mmap_errnos ->
  grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
  spurious_refusal_cfg CFG (sys_input segs ms x8) model (mkEffect (errno_ret e) [] []).
Proof.
  intros ms model x8 e a Hno Hargs He Ha.
  split; [| split].
  - unfold injected_family_off. cbn [in_sysno sys_input]. rewrite Hno, injected_arm_222. reflexivity.
  - unfold refusal_b. cbn [in_sysno sys_input eff_ret]. rewrite Hno, injected_arm_222.
    cbn [Z.eqb Pos.eqb ia_errnos]. destruct He as [<- | []].
    unfold ret_in_errnos, mmap_errnos. cbn [existsb]. rewrite bv_eqb_refl. reflexivity.
  - exists (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))]),
           (mmap_model a (page_round_up (ms_gpr ms 1)) model), [].
    split; [apply mmap_succ_ok; assumption|].
    unfold refusal_b. cbn [in_sysno sys_input eff_ret]. rewrite Hno, injected_arm_222.
    cbn [Z.eqb Pos.eqb ia_errnos].
    destruct (grant_ok_unpack _ _ _ _ Ha) as (_ & _ & Htop & _ & _).
    pose proof (alloc_top_room (m_vmmaps model)) as Hroom.
    pose proof (page_round_up_Z_nonneg (bv_unsigned (ms_gpr ms 1)) ltac:(apply bv_unsigned_in_range)).
    unfold ret_in_errnos, mmap_errnos. cbn [existsb]. rewrite orb_false_r.
    apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E.
    rewrite errno_ret_unsigned in E by (vm_compute; congruence).
    unfold stack_max_size, two_pow_64 in *. change ENOMEM with 12%Z in E. lia.
Qed.

(* [comment removed for export] *)
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
  intros ms model x8 B Hh Hlazy Hsvc Hno Hargs HB Hex.
  set (n := page_round_up (ms_gpr ms 1)).
  set (nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1))).
  destruct Hex as [a0 Ha0].
  pose (IB := {a : word | grant_ok (ms_gpr ms 0) model a nZ = true}).
  pose (nx := fun (i : IB) =>
    match i with
    | exist _ a _ =>
        mkCfg (advance_past_svc (apply_effect ms (mkEffect a [] [(a, n)])))
              (mmap_model a n model)
    end).
  apply (rz_conseq (mkCfg ms model) (t_alt (fun i : IB => t_emit [] B))).
  2:{ intros tr. split; [intros [_ Ht]; exact (proj1 (t_emit_nil_eq B (realizes_nonempty _ _ (HB a0 Ha0)) tr) Ht)
                        | intros Ht; exists (exist _ a0 Ha0);
                          exact (proj2 (t_emit_nil_eq B (realizes_nonempty _ _ (HB a0 Ha0)) tr) Ht)]. }
  apply (rz_node (mkCfg ms model) IB (fun _ => []) nx (fun _ => B) (exist _ a0 Ha0)).
  - split.
    + intros [a Ha]; cbn.
      apply (sstep_cfg_syscall segs CFG ms model x8 (mkEffect a [] [(a, n)])
               (mmap_model a n model) (mmap_model a n model) []).
      * exact Hh.
      * exact Hsvc.
      * apply mmap_succ_ok; assumption.
      * intros (_ & Hr & _). revert Hr.
        unfold refusal_b. cbn [in_sysno sys_input eff_ret]. rewrite Hno, injected_arm_222.
        cbn [Z.eqb Pos.eqb ia_errnos].
        destruct (grant_ok_unpack _ _ _ _ Ha) as (_ & _ & Htop & _ & _).
        pose proof (alloc_top_room (m_vmmaps model)) as Hroom.
        pose proof (page_round_up_Z_nonneg (bv_unsigned (ms_gpr ms 1)) ltac:(apply bv_unsigned_in_range)).
        unfold ret_in_errnos, mmap_errnos. cbn [existsb]. rewrite orb_false_r.
        intros E. apply bv_eqb_eq in E. apply (f_equal bv_unsigned) in E.
        rewrite errno_ret_unsigned in E by (vm_compute; congruence).
        unfold stack_max_size, two_pow_64, nZ in *. change ENOMEM with 12%Z in E. lia.
      * rewrite mmap_model_halted; exact Hh.
      * apply materialize_model_accesses_no_lazy.
        exact (eq_trans (mmap_model_lazy _ _ _) Hlazy).
    + intros e st Hss.
      destruct (sstep_cfg_svc_inv ms model x8 e st Hsvc Hss)
        as [(eff & model' & ev & Hc & [(m'' & Hns & Hh2 & -> & Hmat & ->) | [(Hns & Hh2 & -> & Hmat & ->) | [(code & Hh2 & -> & ->) | (sig & Hk2 & -> & ->)]]])
           | (Hc & -> & ->)].
      * destruct (mmap_ok_inv segs ms x8 model eff model' ev Hno Hargs Hc) as (-> & [(er & Her & -> & ->) | (a & Ha & -> & ->)]).
        -- exfalso. exact (Hns (mmap_spurious ms model x8 er a0 Hno Hargs Her Ha0)).
        -- rewrite (materialize_model_accesses_no_lazy _ _ (eq_trans (mmap_model_lazy _ _ _) Hlazy)) in Hmat.
           injection Hmat as <-. exists (exist _ a Ha). split; reflexivity.
      * destruct (mmap_ok_inv segs ms x8 model eff model' ev Hno Hargs Hc) as (-> & [(er & Her & -> & ->) | (a & Ha & -> & ->)]).
        -- rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat. discriminate.
        -- rewrite (materialize_model_accesses_no_lazy _ _ (eq_trans (mmap_model_lazy _ _ _) Hlazy)) in Hmat.
           discriminate.
      * destruct (mmap_ok_inv segs ms x8 model eff model' ev Hno Hargs Hc) as (-> & [(er & Her & -> & ->) | (a & Ha & -> & ->)]).
        -- rewrite Hh in Hh2. discriminate.
        -- rewrite mmap_model_halted, Hh in Hh2. discriminate.
      * (* [comment removed for export] *)
        destruct (mmap_ok_inv segs ms x8 model eff model' ev Hno Hargs Hc) as (-> & [(er & Her & -> & ->) | (a & Ha & -> & ->)]).
        -- rewrite (m_killed_of_m_halted_none _ Hh) in Hk2. discriminate.
        -- rewrite (m_killed_of_m_halted_none _ (eq_trans (mmap_model_halted _ _ _) Hh)) in Hk2. discriminate.
      * exfalso. exact (mmap_no_unmodeled segs ms x8 model Hno Hargs Hc).
  - intros [a Ha]; cbn. apply HB; exact Ha.
Qed.

End WithSegs.

(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem shape_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb (rrnd : EntryDraw) (rlim : Z)
         target_segs apc aph asp abrk amb (arnd : EntryDraw) (alim : Z)
         (T : TSet) (inp : ProcInput),
  realizes source_segs
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes target_segs
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T ->
  Equivalence.modeled (run_scfg CFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run_scfg CFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run_scfg CFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim T inp Hsource Htarget.
  split.
  { intros Hun. apply (realizes_no_error _ _ _ Hsource).
    exact (reaches_unmodeled_cfg_reaches_error_cfg _ CFG _ Hun). }
  right. split.
  - intro tr. cbn.
    rewrite (realizes_obs_iff source_segs _ T Hsource tr).
    rewrite (realizes_obs_iff target_segs _ T Htarget tr).
    reflexivity.
  - cbn. eapply realizes_no_error; exact Htarget.
Qed.

(* [comment removed for export] *)


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


(* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)
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


(* [comment removed for export] *)
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


(* [comment removed for export] *)

Definition t_writes_ch_pick (ch : word) (bufs : list (list byte)) (T : TSet) : TSet :=
  fold_right (t_write_ch ch) T bufs.

Lemma t_writes_ch_pick_1 : forall bufs T, t_writes_ch_pick (Z_to_bv 64 1) bufs T = t_writes_pick bufs T.
Proof. reflexivity. Qed.

Lemma t_writes_ch_pick_cons : forall ch buf bufs T,
  t_writes_ch_pick ch (buf :: bufs) T = t_write_ch ch buf (t_writes_ch_pick ch bufs T).
Proof. reflexivity. Qed.

