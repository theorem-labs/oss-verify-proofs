(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Frame Exec ITree Nodes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2 Require Import TopLevel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import AcctCore ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ITreeA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Lemma CFG_eq : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.CFG = Nodes.CFG.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition tfam : Type := ProcInput -> ExecEntry -> list event -> Prop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition side_srz (segs : list Segment) (pc : N) (ph : PhdrInfo) (lim : Z) (T : tfam) : Prop :=
  forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
    SpinAlg.srealizes segs (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp) (T inp en).

Lemma side_srz_run : forall segs pc ph lim T en inp,
  side_srz segs pc ph lim T -> valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
  (forall tr, bh_traces (run_scfg CFG (mkImage segs pc ph) lim en inp) tr <-> T inp en tr)
  /\ ~ bh_errors (run_scfg CFG (mkImage segs pc ph) lim en inp).
Proof.
  intros segs pc ph lim T en inp H Hv Hi. specialize (H en inp Hv Hi).
  rewrite run_eq. cbv zeta. cbn [bh_traces bh_errors]. rewrite init_config_eq in H. split.
  - intros tr. exact (SpinAlg.srealizes_obs_iff segs _ _ H tr).
  - exact (SpinAlg.srealizes_no_error segs _ _ H).
Qed.

(* [comment removed for export] *)
Lemma side_srz_eq : forall segs pc ph lim (T T' : tfam),
  (forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
      SpinAlg.srealizes segs (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp) (T' inp en)
      /\ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.t_eq (T' inp en) (T inp en)) ->
  side_srz segs pc ph lim T.
Proof.
  intros segs pc ph lim T T' H en inp Hv Hi. destruct (H en inp Hv Hi) as [Hs Heq].
  eapply SpinAlg.srz_conseq; [exact Hs| exact Heq].
Qed.

(* [comment removed for export] *)
Section BootMain.
Variable node : Type.
Variable segs : list Segment.
Variable at_node : node -> footprint -> machine_state -> Prop.
Variable sil : footprint -> machine_state -> machine_state -> Prop.
Variable npeek : node -> option (machine_state -> resp).
Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit : node -> Model -> word -> Model -> Prop.
Variable minv : Model -> Prop.
Variable nsafe : node -> Model -> Prop.
Variable fstep : node -> resp -> footprint -> footprint -> Prop.
Variable NMAX : nat.
Hypothesis NS : node_soundA node segs at_node npeek nstep nexit minv nsafe NMAX.
Hypothesis SS : sil_soundA segs sil minv NMAX.

(* [comment removed for export] *)
#[using="NS SS"] Lemma srealizes_boot_main : forall (c0 : config) (AtMain : machine_state -> Model -> Prop) (K : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.TSet),
  (forall K', (forall ms mo_, AtMain ms mo_ -> SpinAlg.srealizes segs (mkCfg ms mo_) K') -> SpinAlg.srealizes segs c0 K') ->
  (forall ms mo_, AtMain ms mo_ ->
     exists (R : Type) (t : itree node R) RNG A Q mo,
       npfree npeek t /\
       tree_atA segs at_node sil npeek nstep minv nsafe fstep NMAX RNG A t Q ms mo mo_ /\
       OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.t_eq (ptraces nstep nexit t mo) K) ->
  SpinAlg.srealizes segs c0 K.
Proof.
  intros c0 AtMain K BOOT MAIN. apply BOOT. intros ms mo_ HM.
  destruct (MAIN ms mo_ HM) as (R & t & RNG & A & Q & mo & NP & HT & HEQ).
  eapply SpinAlg.srz_conseq; [| exact HEQ].
  eapply (implF_srealizes segs at_node sil npeek nstep nexit minv nsafe fstep NMAX NS SS); eassumption.
Qed.

(* [comment removed for export] *)
#[using="NS SS"] Lemma srealizes_boot_main_adq : forall (c0 : config) (AtMain : machine_state -> Model -> Prop) (K : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.TSet),
  (forall K', (forall ms mo_, AtMain ms mo_ -> SpinAlg.srealizes segs (mkCfg ms mo_) K') -> SpinAlg.srealizes segs c0 K') ->
  (forall ms mo_, AtMain ms mo_ ->
     exists (R : Type) (t : itree node R) RNG A Q mo,
       tree_atA segs at_node sil npeek nstep minv nsafe fstep NMAX RNG A t Q ms mo mo_ /\
       (forall tr, ptraces nstep nexit t mo tr -> K tr) /\
       (forall tr, K tr -> wins npeek nstep nexit t mo (is_prefix tr))) ->
  SpinAlg.srealizes segs c0 K.
Proof.
  intros c0 AtMain K BOOT MAIN. apply BOOT. intros ms mo_ HM.
  destruct (MAIN ms mo_ HM) as (R & t & RNG & A & Q & mo & HT & HSUB & HWIN).
  destruct (implF_adequate segs at_node sil npeek nstep nexit minv nsafe fstep NMAX NS SS t RNG A Q ms mo mo_ HT) as (A1 & A2 & A3).
  eapply SpinAlg.srz_conseq; [exact A1|]. intros tr. split.
  - intros Htr. apply HSUB. apply A2. exact Htr.
  - intros Htr. destruct (A3 _ (HWIN tr Htr)) as (tr0 & Hobs & Hp).
    exact (SpinAlg.srealizes_pclosed segs _ _ A1 tr0 tr Hobs Hp).
Qed.

(* [comment removed for export] *)
#[using="NS SS"] Theorem strong_universal_error_free_scfg_budgets_from_tree_adq :
  forall {RS : Type} (limS limT : Z)
         (segsS : list Segment) (pcS : N) (phS : PhdrInfo) (pcT : N) (phT : PhdrInfo)
         (tS : prog_tree RS) (QS : RS -> machine_state -> Prop)
         (AtMain : ProcInput -> ExecEntry -> machine_state -> Model -> Prop)
         (MainTree : ProcInput -> ExecEntry -> forall R : Type, itree node R -> Model -> Prop),
    tree_ok segsS pcS phS limS tS QS ->
    (* [comment removed for export] *)
    (forall enT inp, valid_entry (mkImage segs pcT phT) enT inp -> valid_input inp ->
       forall K', (forall ms mo_, AtMain inp enT ms mo_ -> SpinAlg.srealizes segs (mkCfg ms mo_) K') ->
                  SpinAlg.srealizes segs (init_config segs pcT phT (en_sp enT) (en_brk enT) (en_mmap_base enT) (en_draw enT) limT inp) K') ->
    (* [comment removed for export] *)
    (forall enT inp, valid_entry (mkImage segs pcT phT) enT inp -> valid_input inp ->
       forall ms mo_, AtMain inp enT ms mo_ ->
         exists (R : Type) (t : itree node R) RNG A Q mo,
           tree_atA segs at_node sil npeek nstep minv nsafe fstep NMAX RNG A t Q ms mo mo_ /\ MainTree inp enT R t mo) ->
    (* [comment removed for export] *)
    (forall enS enT inp,
       valid_entry (mkImage segsS pcS phS) enS inp -> valid_entry (mkImage segs pcT phT) enT inp -> valid_input inp ->
       forall (R : Type) (t : itree node R) mo, MainTree inp enT R t mo ->
         (forall tr, ptraces nstep nexit t mo tr -> tree_wins segsS (tS inp enS) (mo0 segsS limS enS inp) tr)
         /\ (forall tr, tree_exits (tS inp enS) (mo0 segsS limS enS inp) tr -> wins npeek nstep nexit t mo (is_prefix tr))) ->
    strong_universal_error_free_T_scfg_budgets CFG limS limT (mkImage segsS pcS phS) (mkImage segs pcT phT).
Proof.
  intros RS limS limT segsS pcS phS pcT phT tS QS AtMain MainTree HS BOOT MAIN HEQ enS enT inp HvS HvT Hvi _.
  destruct (HS enS inp HvS Hvi) as (HimplS & HleavesS & HsafeS).
  destruct (run_of_tree segsS pcS phS limS (tS inp enS) QS enS inp HimplS HleavesS HsafeS Hvi)
    as (HsoundS & HcomplS & HerrS).
  set (K := (fun tr => bh_traces (run_scfg CFG (mkImage segsS pcS phS) limS enS inp) tr) : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.TSet).
  assert (SRZ : SpinAlg.srealizes segs (init_config segs pcT phT (en_sp enT) (en_brk enT) (en_mmap_base enT) (en_draw enT) limT inp) K).
  { apply (srealizes_boot_main_adq _ (AtMain inp enT) K (BOOT enT inp HvT Hvi)).
    intros ms mo_ HM. destruct (MAIN enT inp HvT Hvi ms mo_ HM) as (R & t & RNG & A & Q & mo & HT & HMT).
    destruct (HEQ enS enT inp HvS HvT Hvi R t mo HMT) as [HTS HST].
    exists R, t, RNG, A, Q, mo. split; [exact HT|]. split.
    - intros tr Htr. apply HcomplS. apply HTS. exact Htr.
    - intros tr Htr. apply HST. apply (tree_traces_exits _ _ _ HleavesS). apply HsoundS. exact Htr. }
  split; [exact HerrS|].
  rewrite (run_eq segs pcT phT limT enT inp). cbv zeta. cbn [bh_traces bh_errors]. rewrite init_config_eq in SRZ. split.
  - exact (SpinAlg.srealizes_no_error segs _ _ SRZ).
  - intros tr. split.
    + intros H. apply (SpinAlg.srealizes_obs_iff segs _ _ SRZ tr). exact H.
    + intros H. apply (SpinAlg.srealizes_obs_iff segs _ _ SRZ tr) in H. exact H.
Qed.
End BootMain.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition tree_fam_equiv {RS : Type} (limS : Z) (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
    (segsT : list Segment) (pcT : N) (phT : PhdrInfo) (tS : prog_tree RS) (TT : tfam) : Prop :=
  forall enS enT inp,
    valid_entry (mkImage segsS pcS phS) enS inp ->
    valid_entry (mkImage segsT pcT phT) enT inp ->
    valid_input inp ->
    (forall tr, tree_exits (tS inp enS) (mo0 segsS limS enS inp) tr -> TT inp enT tr)
    /\ (forall tr, TT inp enT tr -> tree_wins segsS (tS inp enS) (mo0 segsS limS enS inp) tr).

Theorem strong_universal_error_free_scfg_budgets_from_tree_srz :
  forall {RS : Type} (limS limT : Z)
         (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo)
         (tS : prog_tree RS) (QS : RS -> machine_state -> Prop) (TT : tfam),
    tree_ok segsS pcS phS limS tS QS ->
    side_srz segsT pcT phT limT TT ->
    tree_fam_equiv limS segsS pcS phS segsT pcT phT tS TT ->
    strong_universal_error_free_T_scfg_budgets CFG limS limT (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  intros RS limS limT segsS pcS phS segsT pcT phT tS QS TT HS HT HEQ enS enT inp HvS HvT Hvi _.
  destruct (HS enS inp HvS Hvi) as (HimplS & HleavesS & HsafeS).
  destruct (run_of_tree segsS pcS phS limS (tS inp enS) QS enS inp HimplS HleavesS HsafeS Hvi)
    as (HsoundS & HcomplS & HerrS).
  destruct (side_srz_run segsT pcT phT limT TT enT inp HT HvT Hvi) as (HtrT & HerrT).
  destruct (HEQ enS enT inp HvS HvT Hvi) as [HST HTS].
  split; [exact HerrS|]. split; [exact HerrT|].
  intros tr. split.
  - intros H. apply HtrT, HST. apply (tree_traces_exits _ _ _ HleavesS). apply HsoundS, H.
  - intros H. apply HcomplS, HTS, HtrT, H.
Qed.
