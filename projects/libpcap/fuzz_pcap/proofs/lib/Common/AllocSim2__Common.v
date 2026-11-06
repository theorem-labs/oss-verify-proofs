(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim MmapSim.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From LinuxProcessSemantics.Riscv Require Prelude Sem.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Prelude Mm.Mmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require WallSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module AllocSim2.
(* [comment removed for export] *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim MmapSim. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.SimInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.ExitSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition two_outcomes (bf : list (list byte)) (cf : word)
    (bs : list (list byte)) (cs : word)
    : (list (list byte) * word) -> Prop :=
  fun o => o = (bf, cf) \/ o = (bs, cs).

(* [comment removed for export] *)
Lemma alloc_mmap_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bf cf bs cs inp,
  to_outcomes source_segs
    (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp)
    (two_outcomes bf cf bs cs) ->
  tmw target_segs
    (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (init_model (segments_reserved target_segs) abrk amb asp alim inp) bf cf bs cs ->
  bufs_modeled bf -> bufs_modeled bs ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bf cf bs cs
    inp Hsource Htarget Hbf Hbs.
  split.
  { apply no_error_run_modeled.
    apply (alloc_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim inp
             (two_outcomes bf cf bs cs) Hsource). }
  right. split.
  - intro tr. cbn.
    rewrite (alloc_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim inp
               (two_outcomes bf cf bs cs) Hsource tr).
    rewrite (mmap_obs_iff_te target_segs apc aph asp abrk amb arnd alim inp
               bf cf bs cs Htarget Hbf Hbs tr).
    unfold two_traces, two_outcomes, outcome_trace.
    split.
    + intros (o & [-> | ->] & Hp); cbn [fst snd] in Hp; [left | right]; exact Hp.
    + intros [Hp | Hp]; [exists (bf, cf) | exists (bs, cs)];
        cbn [fst snd]; auto.
  - cbn.
    apply (mmap_no_error_run_te target_segs apc aph asp abrk amb arnd alim inp
             bf cf bs cs Htarget Hbf Hbs).
Qed.

(* [comment removed for export] *)
Lemma alloc_mmap_omni_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bf cf bs cs inp,
  to_outcomes source_segs
    (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
    (two_outcomes bf cf bs cs) ->
  tmw target_segs
    (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp) bf cf bs cs ->
  bufs_modeled bf -> bufs_modeled bs ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bf cf bs cs
    inp Hsource Htarget Hbf Hbs.
  apply strong_equiv_iff.
  apply (alloc_mmap_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit
           target_segs apc aph asp abrk amb arnd target_alloc_limit bf cf bs cs inp
           Hsource Htarget Hbf Hbs).
Qed.
End AllocSim2.

(* [comment removed for export] *)
Module ShapeAlg.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude Mm.Mmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require MmapSim AllocSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require WallSim. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.SimInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.ExitSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.AllocSim2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.WallSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)

Definition CFG : SpuriousCfg := mkSpuriousCfg false true true true true true.

#[using="Type"] Lemma CFG_alloc_only : CFG = alloc_only_cfg false.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition alloc_no (n : Z) : bool :=
  (Z.eqb 214 n || Z.eqb 216 n || Z.eqb 222 n || Z.eqb 226 n)%bool.

#[using="Type"] Lemma injected_family_off_CFG : forall i,
  injected_family_off CFG i = alloc_no (bv_unsigned (in_sysno i)).
Proof.
  intros i. unfold injected_family_off, injected_arm, alloc_no.
  generalize (bv_unsigned (in_sysno i)) as n. intros n.
  cbn [lookup_injected injected_table ia_no ia_family family_may_fail CFG negb
       sc_alloc sc_fs sc_fd sc_net sc_cred sc_intr].
  repeat match goal with
    |- context [Z.eqb ?a n] =>
      let a' := eval cbv in a in
      change (Z.eqb a n) with (Z.eqb a' n);
      destruct (Z.eqb_spec a' n) as [<-|?]; [reflexivity|]
  end.
  reflexivity.
Qed.

(* [comment removed for export] *)
Definition unfiltered (c : config) : Prop :=
  forall x8, ms_svc_pending (cfg_ms c) = Some x8 -> alloc_no (bv_unsigned x8) = false.

#[using="Type"] Lemma unfiltered_nosvc : forall ms model,
  ms_svc_pending ms = None -> unfiltered (mkCfg ms model).
Proof. intros ms model H x8 Hx. cbn in Hx. congruence. Qed.

#[using="Type"] Lemma unfiltered_sysno : forall ms model x8,
  ms_svc_pending ms = Some x8 -> alloc_no (bv_unsigned x8) = false ->
  unfiltered (mkCfg ms model).
Proof. intros ms model x8 Hs Ha y Hy. cbn in Hy. congruence. Qed.

#[using="Type"] Lemma unfiltered_family_on : forall ms model x8,
  unfiltered (mkCfg ms model) -> ms_svc_pending ms = Some x8 ->
  injected_family_off CFG (sys_input segs ms x8) = false.
Proof.
  intros ms model x8 Hu Hs. rewrite injected_family_off_CFG, in_sysno_sys_input. exact (Hu x8 Hs).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sstep_cfg_of_unfiltered : forall c e st,
  unfiltered c -> sstep segs c e st -> sstep_cfg segs CFG c e st.
Proof.
  intros c e st Hu Hss.
  inversion Hss; subst;
    [ eapply sstep_cfg_instr | eapply sstep_cfg_instr_fault | eapply sstep_cfg_instr_unmodeled
    | eapply sstep_cfg_syscall | eapply sstep_cfg_syscall_materialization_fault
    | eapply sstep_cfg_exit | eapply sstep_cfg_killed | eapply sstep_cfg_syscall_unmodeled ]; eauto;
    apply spurious_refusal_family_on; eapply unfiltered_family_on; eauto.
Qed.

(* [comment removed for export] *)
Definition all_nonrefusal (c : config) : Prop :=
  forall x8 eff m' evs, ms_svc_pending (cfg_ms c) = Some x8 ->
    syscall_spec (sys_input segs (cfg_ms c) x8) (cfg_model c) (Ok eff m' evs) ->
    refusal_b (sys_input segs (cfg_ms c) x8) (cfg_model c) (eff_ret eff) = false.

#[using="Type"] Lemma sstep_cfg_of_nonrefusal : forall c e st,
  all_nonrefusal c -> sstep segs c e st -> sstep_cfg segs CFG c e st.
Proof.
  intros c e st Hnr Hss.
  inversion Hss; subst;
    [ eapply sstep_cfg_instr | eapply sstep_cfg_instr_fault | eapply sstep_cfg_instr_unmodeled
    | eapply sstep_cfg_syscall | eapply sstep_cfg_syscall_materialization_fault
    | eapply sstep_cfg_exit | eapply sstep_cfg_killed | eapply sstep_cfg_syscall_unmodeled ]; eauto;
    apply spurious_refusal_not_refusal; eapply Hnr; cbn; eauto.
Qed.

(* [comment removed for export] *)
Definition all_refusal (c : config) : Prop :=
  forall x8 eff m' evs, ms_svc_pending (cfg_ms c) = Some x8 ->
    syscall_spec (sys_input segs (cfg_ms c) x8) (cfg_model c) (Ok eff m' evs) ->
    refusal_b (sys_input segs (cfg_ms c) x8) (cfg_model c) (eff_ret eff) = true.

#[using="Type"] Lemma sstep_cfg_of_forced : forall c e st,
  all_refusal c -> sstep segs c e st -> sstep_cfg segs CFG c e st.
Proof.
  intros c e st Hall Hss.
  inversion Hss; subst;
    [ eapply sstep_cfg_instr | eapply sstep_cfg_instr_fault | eapply sstep_cfg_instr_unmodeled
    | eapply sstep_cfg_syscall | eapply sstep_cfg_syscall_materialization_fault
    | eapply sstep_cfg_exit | eapply sstep_cfg_killed | eapply sstep_cfg_syscall_unmodeled ]; eauto;
    intros (_ & _ & (eff' & m2 & evs' & Hspec' & Hnr'));
    match goal with Hsvc : ms_svc_pending ?ms = Some ?x8 |- _ =>
      pose proof (Hall x8 eff' m2 evs' Hsvc Hspec') as Hr'; cbn [cfg_ms cfg_model] in Hr';
      rewrite Hr' in Hnr'; discriminate Hnr' end.
Qed.

(* [comment removed for export] *)
Definition node_ok (c : config) (I : Type)
    (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstep segs c (evs i) (SNext (nx i)))
  /\ (forall e st, sstep segs c e st -> exists i, e = evs i /\ st = SNext (nx i)).

Definition cnode_ok (c : config) (I : Type)
    (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstep_cfg segs CFG c (evs i) (SNext (nx i)))
  /\ (forall e st, sstep_cfg segs CFG c e st -> exists i, e = evs i /\ st = SNext (nx i)).

#[using="Type"] Lemma cnode_lift : forall c I evs nx,
  unfiltered c -> node_ok c I evs nx -> cnode_ok c I evs nx.
Proof.
  intros c I evs nx Hu [Hs Hc]. split.
  - intros i. apply sstep_cfg_of_unfiltered; [exact Hu | apply Hs].
  - intros e st Hss. apply Hc. eapply sstep_cfg_sub. exact Hss.
Qed.

#[using="Type"] Lemma cnode_lift_nr : forall c I evs nx,
  all_nonrefusal c -> node_ok c I evs nx -> cnode_ok c I evs nx.
Proof.
  intros c I evs nx Hnr [Hs Hc]. split.
  - intros i. apply sstep_cfg_of_nonrefusal; [exact Hnr | apply Hs].
  - intros e st Hss. apply Hc. eapply sstep_cfg_sub. exact Hss.
Qed.

#[using="Type"] Lemma cnode_lift_forced : forall c I evs nx,
  all_refusal c -> node_ok c I evs nx -> cnode_ok c I evs nx.
Proof.
  intros c I evs nx Hall [Hs Hc]. split.
  - intros i. apply sstep_cfg_of_forced; [exact Hall | apply Hs].
  - intros e st Hss. apply Hc. eapply sstep_cfg_sub. exact Hss.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ms_gpr0_apply_effect : forall ms eff,
  ms_gpr (advance_past_svc (apply_effect ms eff)) 0 = eff_ret eff.
Proof.
  intros ms eff. unfold ms_gpr, advance_past_svc, apply_effect. cbn [ms_regs].
  unfold set_reg.
  match goal with |- context [bv_eqb ?a ?b] => destruct (bv_eqb a b) eqn:E end.
  - exfalso. apply bv_eqb_eq in E. apply (f_equal bv_unsigned) in E. cbv in E. discriminate E.
  - cbn [ms_regs]. unfold reg_get.
    replace (Z_to_bv 5 (10 + Z.of_nat 0)) with (10 : bv 5) by (apply bv_eq; reflexivity).
    rewrite bvmap_get_set_same. reflexivity.
Qed.

#[using="Type"] Lemma advance_past_svc_pending : forall ms, ms_svc_pending (advance_past_svc ms) = None.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sstep_svc_inv0 : forall ms model x8 e st,
  ms_svc_pending ms = Some x8 ->
  sstep segs (mkCfg ms model) e st ->
  (exists eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs)
     /\ ((m_halted m' = None
           /\ ((exists m'', e = evs /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m''))
               \/ (e = [] /\ st = SError)))
         \/ (exists code, m_halted m' = Some code /\ st = SNext (mkCfg ms m'))))
  \/ (syscall_spec (sys_input segs ms x8) model Unmodeled /\ e = [] /\ st = SError).
Proof.
  intros ms model x8 e st Hsvc Hss.
  inversion Hss; subst; try congruence;
    match goal with H : ms_svc_pending ms = Some ?y |- _ => rewrite Hsvc in H; injection H as <- end.
  - left. eexists _, _, _. split; [eassumption|]. left. split; [assumption|].
    left. eexists. split; reflexivity.
  - left. eexists _, _, _. split; [eassumption|]. left. split; [assumption|].
    right. split; reflexivity.
  - left. eexists _, _, _. split; [eassumption|]. right. eexists. split; [eassumption | reflexivity].
  - left. eexists _, _, _. split; [eassumption|]. right.
    match goal with Hk : m_killed ?mm = Some _ |- _ =>
      destruct (m_halted mm) as [code|] eqn:Hhc;
        [| rewrite (m_killed_of_m_halted_none _ Hhc) in Hk; discriminate Hk];
      exists code; split; [reflexivity | reflexivity] end.
  - right. repeat split; auto.
Qed.

#[using="Type"] Lemma sstep_cfg_svc_inv : forall ms model x8 e st,
  ms_svc_pending ms = Some x8 ->
  sstep_cfg segs CFG (mkCfg ms model) e st ->
  (exists eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs)
     /\ ((m_halted m' = None /\ ~ spurious_refusal_cfg CFG (sys_input segs ms x8) model eff
           /\ ((exists m'', e = evs /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m''))
               \/ (e = [] /\ st = SError)))
         \/ (exists code, m_halted m' = Some code /\ st = SNext (mkCfg ms m'))))
  \/ (syscall_spec (sys_input segs ms x8) model Unmodeled /\ e = [] /\ st = SError).
Proof.
  intros ms model x8 e st Hsvc Hss.
  inversion Hss; subst; try congruence;
    match goal with H : ms_svc_pending ms = Some ?y |- _ => rewrite Hsvc in H; injection H as <- end.
  - left. eexists _, _, _. split; [eassumption|]. left. split; [assumption|]. split; [assumption|].
    left. eexists. split; reflexivity.
  - left. eexists _, _, _. split; [eassumption|]. left. split; [assumption|]. split; [assumption|].
    right. split; reflexivity.
  - left. eexists _, _, _. split; [eassumption|]. right. eexists. split; [eassumption | reflexivity].
  - left. eexists _, _, _. split; [eassumption|]. right.
    match goal with Hk : m_killed ?mm = Some _ |- _ =>
      destruct (m_halted mm) as [code|] eqn:Hhc;
        [| rewrite (m_killed_of_m_halted_none _ Hhc) in Hk; discriminate Hk];
      exists code; split; [reflexivity | reflexivity] end.
  - right. repeat split; auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma svc_succ_ret : forall ms e1 e2 m1 m2,
  SNext (mkCfg (advance_past_svc (apply_effect ms e1)) m1)
  = SNext (mkCfg (advance_past_svc (apply_effect ms e2)) m2) ->
  eff_ret e1 = eff_ret e2.
Proof.
  intros ms e1 e2 m1 m2 E.
  pose proof (f_equal (fun st => match st with SNext c => ms_gpr (cfg_ms c) 0 | _ => eff_ret e1 end) E) as Er.
  cbn beta iota delta [cfg_ms] in Er. rewrite !ms_gpr0_apply_effect in Er. exact Er.
Qed.

#[using="Type"] Lemma svc_succ_not_self : forall ms x8 eff m1 m2,
  ms_svc_pending ms = Some x8 ->
  SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m1) <> SNext (mkCfg ms m2).
Proof.
  intros ms x8 eff m1 m2 Hsvc E.
  pose proof (f_equal (fun st => match st with SNext c => ms_svc_pending (cfg_ms c) | _ => None end) E) as Ep.
  cbn beta iota delta [cfg_ms] in Ep. rewrite advance_past_svc_pending, Hsvc in Ep. discriminate Ep.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sstep_cfg_of_sstep_succ : forall ms model x8 e c',
  ms_svc_pending ms = Some x8 ->
  sstep segs (mkCfg ms model) e (SNext c') ->
  (forall eff m'', c' = mkCfg (advance_past_svc (apply_effect ms eff)) m'' ->
      refusal_b (sys_input segs ms x8) model (eff_ret eff) = false) ->
  sstep_cfg segs CFG (mkCfg ms model) e (SNext c').
Proof.
  intros ms model x8 e c' Hsvc Hss Hnr.
  inversion Hss; subst; try congruence;
    match goal with H : ms_svc_pending ms = Some ?y |- _ => rewrite Hsvc in H; injection H as <- end.
  - eapply sstep_cfg_syscall; eauto. apply spurious_refusal_not_refusal. eapply Hnr. reflexivity.
  - eapply sstep_cfg_exit; eauto.
  - eapply sstep_cfg_killed; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cnode_prune : forall ms model x8 (I : Type) (evs : I -> list event)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (keep : I -> bool) (i0 : I),
  ms_svc_pending ms = Some x8 ->
  alloc_no (bv_unsigned x8) = true ->
  node_ok (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) ->
  (forall i, keep i = true -> refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = false) ->
  (forall i, keep i = false -> refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = true) ->
  keep i0 = true ->
  cnode_ok (mkCfg ms model) {i : I | keep i = true}
           (fun j => evs (proj1_sig j))
           (fun j => mkCfg (advance_past_svc (apply_effect ms (effs (proj1_sig j)))) (ms' (proj1_sig j))).
Proof.
  intros ms model x8 I evs effs ms' keep i0 Hsvc Ha [Hs Hc] Hk Hd Hi0.
  assert (Hoff : injected_family_off CFG (sys_input segs ms x8) = true)
    by (rewrite injected_family_off_CFG, in_sysno_sys_input; exact Ha).
  (* [comment removed for export] *)
  assert (Hgrant : exists eff m' ev, syscall_spec (sys_input segs ms x8) model (Ok eff m' ev)
                                  /\ refusal_b (sys_input segs ms x8) model (eff_ret eff) = false).
  { destruct (sstep_svc_inv0 ms model x8 _ _ Hsvc (Hs i0))
      as [(eff & m' & ev & Hspec & [(Hh' & [(m'' & Eev & Est) | (_ & Est)]) | (code & Hcode & Est)])
         | (_ & _ & Est)]; try discriminate Est.
    - exists eff, m', ev. split; [exact Hspec|].
      first [rewrite <- (svc_succ_ret _ _ _ _ _ Est) | rewrite (svc_succ_ret _ _ _ _ _ Est)]. apply Hk. exact Hi0.
    - exfalso. first [exact (svc_succ_not_self _ _ _ _ _ Hsvc Est) | symmetry in Est; exact (svc_succ_not_self _ _ _ _ _ Hsvc Est)]. }
  split.
  - intros [i Hki]. cbn [proj1_sig].
    apply (sstep_cfg_of_sstep_succ ms model x8); [exact Hsvc | apply Hs |].
    intros eff m'' E.
    rewrite <- (svc_succ_ret ms (effs i) eff (ms' i) m'' (f_equal SNext E)). apply Hk. exact Hki.
  - intros e st Hcs.
    destruct (Hc e st (sstep_cfg_sub _ _ _ _ _ Hcs)) as (i & -> & ->).
    destruct (keep i) eqn:Hki.
    + exists (exist _ i Hki). split; reflexivity.
    + exfalso.
      destruct (sstep_cfg_svc_inv ms model x8 _ _ Hsvc Hcs)
        as [(eff & m' & ev & Hspec & [(Hh' & Hns & [(m'' & _ & Est) | (_ & Est)]) | (code & Hcode & Est)])
           | (_ & _ & Est)]; try discriminate Est.
      * apply Hns. split; [exact Hoff|]. split; [| exact Hgrant].
        first [rewrite <- (svc_succ_ret _ _ _ _ _ Est) | rewrite (svc_succ_ret _ _ _ _ _ Est)]. apply Hd. exact Hki.
      * first [exact (svc_succ_not_self _ _ _ _ _ Hsvc Est) | symmetry in Est; exact (svc_succ_not_self _ _ _ _ _ Hsvc Est)].
Qed.

(* [comment removed for export] *)
Inductive realizes : config -> TSet -> Prop :=
| rz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                   (T : I -> TSet) (i0 : I),
    cnode_ok c I evs nx ->
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
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

#[using="Type"] Lemma realizes_pclosed : forall c T, realizes c T ->
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

#[using="Type"] Lemma sstep_cfg_halted_none : forall c e st,
  sstep_cfg segs CFG c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.

#[using="Type"] Lemma sstep_halted_none : forall c e st,
  sstep segs c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.

#[using="Type"] Lemma star_cfg_halted_nil : forall c tr c',
  m_halted (cfg_model c) <> None -> star_cfg segs CFG c tr c' -> tr = [] /\ c' = c.
Proof.
  intros c tr c' Hh Hs. inversion Hs; subst; [split; reflexivity|].
  exfalso. apply Hh. eapply sstep_cfg_halted_none. eassumption.
Qed.

#[using="Type"] Lemma realizes_star_only : forall c T, realizes c T ->
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
  - destruct (star_cfg_halted_nil c tr c' Hh Hstar) as [-> _]. reflexivity.
  - apply Heq. eapply IH; exact Hstar.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma star_cfg_one : forall c e c',
  sstep_cfg segs CFG c e (SNext c') -> star_cfg segs CFG c e c'.
Proof.
  intros c e c' H. rewrite <- (app_nil_r e). eapply star_cfg_step; [exact H | apply star_cfg_refl].
Qed.

#[using="Type"] Lemma star_cfg_trans : forall c1 t1 c2 t2 c3,
  star_cfg segs CFG c1 t1 c2 -> star_cfg segs CFG c2 t2 c3 -> star_cfg segs CFG c1 (t1 ++ t2) c3.
Proof.
  intros c1 t1 c2 t2 c3 H1 H2. induction H1; [exact H2|].
  rewrite <- app_assoc. eapply star_cfg_step; eauto.
Qed.

#[using="Type"] Lemma star_cfg_trans_nil : forall c1 c2 c3,
  star_cfg segs CFG c1 [] c2 -> star_cfg segs CFG c2 [] c3 -> star_cfg segs CFG c1 [] c3.
Proof. intros c1 c2 c3 H1 H2. exact (star_cfg_trans _ _ _ _ _ H1 H2). Qed.

#[using="Type"] Lemma realizes_admits : forall c T, realizes c T ->
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
  - unfold t_nil in HT; subst tr. exists [], c. split; [apply star_cfg_refl | apply is_prefix_nil].
  - apply IH. apply Heq. exact HT.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem realizes_obs_iff : forall c T, realizes c T ->
  forall tr, obs_trace_cfg segs CFG c tr <-> T tr.
Proof.
  intros c T H tr. split.
  - intros (tr' & c' & Hstar & Hp).
    eapply realizes_pclosed; [exact H | eapply realizes_star_only; eauto | exact Hp].
  - apply realizes_admits; exact H.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma realizes_step : forall c T e c',
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

#[using="Type"] Lemma realizes_no_sserror : forall c T e,
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

#[using="Type"] Lemma realizes_star : forall c T tr c',
  realizes c T -> star_cfg segs CFG c tr c' -> exists T', realizes c' T'.
Proof.
  intros c T tr c' H Hs. revert T H. induction Hs as [c | c1 e c2 tr2 c3 Hss Hs IH]; intros T H.
  - exists T. exact H.
  - destruct (realizes_step _ _ _ _ H Hss) as [T2 H2]. exact (IH T2 H2).
Qed.

#[using="Type"] Theorem realizes_no_error : forall c T, realizes c T -> ~ reaches_error_cfg segs CFG c.
Proof.
  intros c T H (tr & c' & evs & Hstar & Herr).
  destruct (realizes_star _ _ _ _ H Hstar) as [T' H']. exact (realizes_no_sserror _ _ _ H' Herr).
Qed.

Definition rz_path (c : config) : Prop := exists T, realizes c T.

(* [comment removed for export] *)

#[using="Type"] Lemma t_alt_unit : forall (f : unit -> TSet), t_eq (t_alt f) (f tt).
Proof.
  intros f tr. split; [intros [[] Hf]; exact Hf | intro Hf; exists tt; exact Hf].
Qed.

#[using="Type"] Lemma t_alt_const : forall (I : Type) (i0 : I) (K : TSet), t_eq (t_alt (fun _ : I => K)) K.
Proof.
  intros I i0 K tr. split; [intros [_ Hf]; exact Hf | intro Hf; exists i0; exact Hf].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_silent1 : forall c c' T,
  cnode_ok c unit (fun _ => []) (fun _ => c') ->
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

#[using="Type"] Lemma rz_silent1u : forall c c' T,
  unfiltered c ->
  node_ok c unit (fun _ => []) (fun _ => c') ->
  realizes c' T ->
  realizes c T.
Proof. intros c c' T Hu Hn Hc. eapply rz_silent1; [apply cnode_lift; [exact Hu | exact Hn] | exact Hc]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_silent : forall c (I : Type) (nx : I -> config) (i0 : I) T,
  cnode_ok c I (fun _ => []) nx ->
  (forall i, realizes (nx i) T) ->
  realizes c T.
Proof.
  intros c I nx i0 T Hnode Hc.
  apply (rz_conseq c (t_alt (fun _ : I => t_emit [] T))).
  - apply (rz_node c I (fun _ => []) nx (fun _ => T) i0 Hnode). exact Hc.
  - eapply t_eq_trans; [apply (t_alt_const I i0)|]. apply t_emit_nil_eq. eapply realizes_nonempty; exact (Hc i0).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_emit1 : forall c c' e T,
  cnode_ok c unit (fun _ => e) (fun _ => c') ->
  realizes c' T ->
  realizes c (t_emit e T).
Proof.
  intros c c' e T Hnode Hc.
  apply (rz_conseq c (t_alt (fun _ : unit => t_emit e T))).
  - apply (rz_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode).
    intros []; exact Hc.
  - apply t_alt_unit.
Qed.

#[using="Type"] Lemma rz_emit1u : forall c c' e T,
  unfiltered c ->
  node_ok c unit (fun _ => e) (fun _ => c') ->
  realizes c' T ->
  realizes c (t_emit e T).
Proof. intros c c' e T Hu Hn Hc. eapply rz_emit1; [apply cnode_lift; [exact Hu | exact Hn] | exact Hc]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_alt2 : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
                       (a0 : IA) (b0 : IB),
  cnode_ok c (IA + IB) (fun _ => []) nx ->
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

#[using="Type"] Lemma rz_alt2u : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
                       (a0 : IA) (b0 : IB),
  unfiltered c ->
  node_ok c (IA + IB) (fun _ => []) nx ->
  (forall i, realizes (nx (inl i)) A) ->
  (forall i, realizes (nx (inr i)) B) ->
  realizes c (t_alt2 A B).
Proof. intros c IA IB nx A B a0 b0 Hu Hn HA HB. exact (rz_alt2 c IA IB nx A B a0 b0 (cnode_lift _ _ _ _ Hu Hn) HA HB). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma node_instr0 : forall ms model ms',
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

(* [comment removed for export] *)
#[using="Type"] Lemma node_instr : forall ms model ms',
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  cnode_ok (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' Hh Hlazy Hsvc Hstep.
  apply cnode_lift; [apply unfiltered_nosvc; exact Hsvc | apply node_instr0; assumption].
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
  eapply rz_silent1; [apply node_instr; eassumption | exact Hc].
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
#[using="Type"] Lemma star_cfg_instr : forall ms model ms',
  m_halted model = None -> m_vm_lazy model = [] -> ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  star_cfg segs CFG (mkCfg ms model) [] (mkCfg ms' model).
Proof.
  intros ms model ms' Hh Hl Hs Hst. apply star_cfg_one.
  exact (proj1 (node_instr ms model ms' Hh Hl Hs Hst) tt).
Qed.

#[using="Type"] Lemma star_cfg_msteps : forall ms ms' model,
  m_halted model = None -> m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  star_cfg segs CFG (mkCfg ms model) [] (mkCfg ms' model).
Proof.
  intros ms ms' model Hh Hl Hms.
  induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH]; [apply star_cfg_refl|].
  eapply star_cfg_trans_nil; [| exact IH]. eapply star_cfg_instr; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma node_write1 : forall ms model x8 buf,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  cnode_ok (mkCfg ms model) (wr_index buf)
          (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
          (fun i => mkCfg (advance_past_svc
                             (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                          model).
Proof.
  intros ms model x8 buf Hh Hlazy Hfd Hsvc Hno Hg Hr Hbm Hnb.
  apply cnode_lift; [eapply unfiltered_sysno; [exact Hsvc | rewrite Hno; reflexivity]|]. split.
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
                Hh Hlazy Hfd Hsvc Hno Hg Hr Hbm Hnb Hss)
      as (n & Hn1 & Hn2 & -> & ->).
    exists (exist _ n (conj Hn1 Hn2)). split; reflexivity.
Qed.

#[using="Type"] Lemma rz_write1 : forall ms model x8 buf T,
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
  - split.
    + intros []. cbn.
      replace [ExitEv code (m_fs model)]
        with ([] ++ [ExitEv code (m_fs (with_halted code model))]) by reflexivity.
      apply (sstep_cfg_exit segs CFG ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted code model) [] code);
        [exact Hh | exact Hsvc
         | apply (exit_dispatch_ok (sys_input segs ms x8) model);
           rewrite in_sysno_sys_input; exact Hx8
         | reflexivity
         | apply m_killed_with_halted ].
    + intros e st Hss. apply sstep_cfg_sub in Hss.
      destruct (sstep_exit_inv segs ms model x8 e st Hh Hsvc Hx8 Hss) as [-> ->].
      exists tt. split; reflexivity.
  - apply rz_halt. cbn. discriminate.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_munmap : forall ms model x8 T,
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
  eapply rz_silent1u; [eapply unfiltered_sysno; [exact Hsvc | rewrite Hno; reflexivity] | | exact Hc]. split.
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
#[using="Type"] Lemma pruZ_nonneg : forall z, (0 <= z)%Z -> (0 <= page_round_up_Z z)%Z.
Proof.
  intros z Hz. unfold page_round_up_Z, page_size.
  apply Z.mul_nonneg_nonneg; [|lia]. apply Z.div_pos; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mmap_refusal_b : forall ms x8 model r,
  bv_unsigned x8 = 222%Z ->
  refusal_b (sys_input segs ms x8) model r = errno_ret_in mmap_errnos r.
Proof.
  intros ms x8 model r Hno. unfold refusal_b. rewrite in_sysno_sys_input, Hno. reflexivity.
Qed.

#[using="Type"] Lemma grant_not_refusal : forall ms x8 model a n hint,
  bv_unsigned x8 = 222%Z -> (0 <= n)%Z ->
  grant_ok hint model a n = true ->
  refusal_b (sys_input segs ms x8) model a = false.
Proof.
  intros ms x8 model a n hint Hno Hn Hg. rewrite (mmap_refusal_b _ _ _ _ Hno).
  eapply grant_not_errno; eassumption.
Qed.

#[using="Type"] Lemma errno_refusal : forall ms x8 model e,
  bv_unsigned x8 = 222%Z -> In e mmap_errnos ->
  refusal_b (sys_input segs ms x8) model (errno_ret e) = true.
Proof.
  intros ms x8 model e Hno He. rewrite (mmap_refusal_b _ _ _ _ Hno). apply errno_ret_in_intro. exact He.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_mmap : forall ms model x8 B,
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
  pose (IA := {e : Z | In e mmap_errnos}).
  pose (IB := {a : word | grant_ok (ms_gpr ms 0) model a nZ = true}).
  pose (effs := fun (i : IA + IB) =>
    match i with
    | inl (exist _ e _) => mkEffect (errno_ret e) [] []
    | inr (exist _ a _) => mkEffect a [] [(a, n)]
    end).
  pose (ms' := fun (i : IA + IB) =>
    match i with
    | inl _ => model
    | inr (exist _ a _) => mmap_model a n model
    end).
  pose (keep := fun (i : IA + IB) => match i with inl _ => false | inr _ => true end).
  assert (Hnode : node_ok (mkCfg ms model) (IA + IB) (fun _ => [])
                    (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i))).
  { split.
    + intros [[e He] | [a Ha]]; cbn.
      * apply (sstep_syscall segs ms model x8 (mkEffect (errno_ret e) [] [])
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
      destruct (sstep_mmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hss)
        as [-> [(er & Her & ->) | (a & Ha & ->)]].
      * exists (inl (exist _ er Her)). cbn. rewrite apply_effect_no_write. split; reflexivity.
      * exists (inr (exist _ a Ha)). split; reflexivity. }
  pose proof (cnode_prune ms model x8 (IA + IB) (fun _ => []) effs ms' keep (inr (exist _ a0 Ha0))
                Hsvc ltac:(rewrite Hno; reflexivity) Hnode) as Hc.
  eapply (rz_silent _ {i : IA + IB | keep i = true} _ (exist _ (inr (exist _ a0 Ha0)) eq_refl)).
  - apply Hc.
    + intros [[e He] | [a Ha]] Hk; [discriminate Hk|]. cbn.
      apply (grant_not_refusal ms x8 model a nZ (ms_gpr ms 0) Hno); [| exact Ha].
      unfold nZ. apply page_round_up_Z_nonneg. pose proof (u64_range (ms_gpr ms 1)). lia.
    + intros [[e He] | [a Ha]] Hk; [|discriminate Hk]. cbn. apply errno_refusal; assumption.
    + reflexivity.
  - intros [[[e He] | [a Ha]] Hk]; [discriminate Hk|]. cbn. apply HB. exact Ha.
Qed.

End WithSegs.

(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem shape_strong_equiv_ef :
  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T : TSet) (inp : ProcInput),
  realizes source_segs
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes target_segs
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T ->
  error_free (run_scfg CFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg CFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg CFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg CFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    T inp Hsource Htarget.
  split; [| split].
  - cbn. eapply realizes_no_error; exact Hsource.
  - cbn. eapply realizes_no_error; exact Htarget.
  - intro tr. cbn.
    rewrite (realizes_obs_iff source_segs _ T Hsource tr).
    rewrite (realizes_obs_iff target_segs _ T Htarget tr).
    reflexivity.
Qed.

Corollary shape_strong_equiv_ef_eq :
  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T T' : TSet) (inp : ProcInput),
  realizes source_segs
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes target_segs
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T' ->
  t_eq T T' ->
  error_free (run_scfg CFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg CFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg CFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg CFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros until T'. intros inp Hs Ht Heq.
  eapply shape_strong_equiv_ef; [| exact Ht].
  eapply rz_conseq; [exact Hs | exact Heq].
Qed.

(* [comment removed for export] *)
Lemma realizes_error_free : forall segs pc ph sp brk0 mb rnd lim inp T,
  realizes segs (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  error_free (run_scfg CFG (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof. intros. cbn. eapply realizes_no_error; eassumption. Qed.

Lemma realizes_traces_iff : forall segs pc ph sp brk0 mb rnd lim inp T tr,
  realizes segs (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  bh_traces (run_scfg CFG (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) tr <-> T tr.
Proof. intros. cbn. apply realizes_obs_iff. assumption. Qed.

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
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  cnode_ok segs (mkCfg ms model) (wr_index buf)
          (fun i => map (WriteEv ch) (firstn (proj1_sig i) buf))
          (fun i => mkCfg (advance_past_svc
                             (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                          model).
Proof.
  intros segs ms model fd ch x8 buf Hh Hlazy Hfdc H32 Hsvc Hno Hg Hr Hbm Hnb.
  apply cnode_lift; [eapply unfiltered_sysno; [exact Hsvc | rewrite Hno; reflexivity]|]. split.
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
                Hh Hlazy Hfdc Hsvc Hno Hg Hr Hbm Hnb Hss)
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

(* [comment removed for export] *)
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

Lemma cat_realizes : forall segs ms model bufs code,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  to_wexit segs ms bufs code ->
  bufs_modeled bufs ->
  realizes segs (mkCfg ms model) (t_writes_pick bufs (t_exit code (m_fs model))).
Proof.
  intros segs ms model bufs code Hh Hl Hfd Hte Hbm. rewrite <- t_writes_ch_pick_1.
  eapply (cat_realizes_ch segs (Z_to_bv 64 1) (Z_to_bv 64 1)); try eassumption.
  - apply fd1chan_fdchan. exact Hfd.
  - reflexivity.
  - apply to_wexit_ch_1. exact Hte.
Qed.
End ShapeAlg.
