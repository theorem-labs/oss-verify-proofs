(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Exec ITree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require ShapeAlg SpinAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Scfg Require Import Fcfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope bv_scope.

Definition alw := word -> Prop.
Definition alw_le (A A' : alw) : Prop := forall p, A p -> A' p.
Lemma alw_le_refl : forall A, alw_le A A. Proof. intros A p H; exact H. Qed.
Lemma alw_le_trans : forall A B C, alw_le A B -> alw_le B C -> alw_le A C.
Proof. intros A B C H1 H2 p H. apply H2, H1, H. Qed.

Definition fp_le (R R' : footprint) : Prop := forall b j, R b j -> R' b j.
Lemma fp_le_refl : forall R, fp_le R R. Proof. intros R b j H; exact H. Qed.
Lemma fp_le_trans : forall A B C, fp_le A B -> fp_le B C -> fp_le A C.
Proof. intros A B C H1 H2 b j H. apply H2, H1, H. Qed.
Lemma rng_fp_le : forall R R' lo len, fp_le R R' -> rng R lo len -> rng R' lo len.
Proof. intros R R' lo len HL (A & B & H). split; [exact A|]. split; [exact B|]. intros b j Hb Hj. apply HL, H; assumption. Qed.

Lemma fp_ok_mono : forall lz lz' (A A' : alw),
  (forall p, page_in_ranges p lz' = true -> page_in_ranges p lz = true) ->
  alw_le A A' ->
  fp_le (fp_ok lz A) (fp_ok lz' A').
Proof.
  intros lz lz' A A' SUB LE b j H k Hk Hb.
  destruct (H k Hk Hb) as [NL | AL].
  - left. destruct (page_in_ranges _ lz') eqn:E; [|reflexivity]. apply SUB in E. congruence.
  - right. apply LE, AL.
Qed.

Section ITreeA.

Variable node : Type.
Variable segs : list Segment.

Variable at_node : node -> footprint -> machine_state -> Prop.

Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit : node -> Model -> word -> Model -> Prop.
Variable minv : Model -> Prop.
Variable nsafe : node -> Model -> Prop.

Variable fstep : node -> resp -> footprint -> footprint -> Prop.

Variable NMAX : nat.

Definition mrel (A : alw) (mo mo_ : Model) : Prop :=
  same_but_mat mo mo_ /\ m_vm_materialized mo = [] /\
  List.NoDup (m_vm_materialized mo_) /\ (forall p, List.In p (m_vm_materialized mo_) -> A p).

Definition acct_ok (RNG : footprint) (A : alw) (mo : Model) : Prop :=
  footprint_ok (m_vm_lazy mo) A RNG /\
  (exists L, List.NoDup L /\ (List.length L <= NMAX)%nat /\ forall p, A p -> List.In p L) /\
  (nonlazy_bytes mo + Z.of_nat NMAX * page_size <= vm_limit (m_vmmaps mo))%Z.

Lemma mrel_ainv : forall RNG A mo mo_,
  acct_ok RNG A mo -> mrel A mo mo_ -> ainv (m_vm_lazy mo) A NMAX mo_.
Proof.
  intros RNG A mo mo_ (FOK & FIN & ROOM) (SB & CAN & ND & AL).
  pose proof (same_but_mat_frame _ _ SB) as (_ & VM & LZ & _).
  constructor; auto.
  - rewrite (same_but_mat_nonlazy _ _ SB), VM. exact ROOM.
Qed.

Lemma mrel_halted : forall A mo mo_, mrel A mo mo_ -> m_halted mo_ = m_halted mo.
Proof. intros A mo mo_ (SB & _). apply same_but_mat_halted. exact SB. Qed.

Lemma mrel_fs : forall A mo mo_, mrel A mo mo_ -> m_fs mo_ = m_fs mo.
Proof.
  intros A mo mo_ (SB & _). pose proof (same_but_mat_frame _ _ SB) as (_ & _ & _ & _ & FS & _).
  unfold m_fs. rewrite FS. reflexivity.
Qed.

Lemma mrel_le : forall A A' mo mo_, mrel A mo mo_ -> alw_le A A' -> mrel A' mo mo_.
Proof. intros A A' mo mo_ (SB & CAN & ND & AL) LE. split; [exact SB|]. split; [exact CAN|]. split; [exact ND|]. intros p Hp. apply LE, AL, Hp. Qed.

Lemma mrel_after : forall A mo mo_ mo_',
  mrel A mo mo_ -> same_but_mat mo_ mo_' -> ainv (m_vm_lazy mo) A NMAX mo_' -> mrel A mo mo_'.
Proof.
  intros A mo mo_ mo_' (SB & CAN & _ & _) SB' INV. split; [eapply same_but_mat_trans; eauto|].
  split; [exact CAN|]. destruct INV as [_ ND AL _ _]. auto.
Qed.

Definition mpost (A : alw) (mo' mo_' : Model) : Prop := mrel A mo' mo_'.

Record node_soundA : Prop := {

  nsA_pending : forall n RNG ms, at_node n RNG ms -> ms_svc_pending ms <> None;

  nsA_complete : forall n RNG A ms mo mo_ evs X,
      at_node n RNG ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      footprint_ok (m_vm_lazy mo) A RNG -> mrel A mo mo_ -> ainv (m_vm_lazy mo) A NMAX mo_ ->
      sstep_cfg segs fcfg (mkCfg ms mo_) evs X ->
        (exists rsp mo' mo_', X = SNext (mkCfg (nret ms rsp) mo_') /\ nstep n mo rsp mo' evs /\ mpost A mo' mo_')
     \/ (exists code mo' mo_', X = SNext (mkCfg ms mo_') /\ nexit n mo code mo' /\
                              evs = [ExitEv code (m_fs mo')] /\ m_halted mo_' = Some code);

  nsA_sound : forall n RNG A ms mo mo_ rsp mo' evs,
      at_node n RNG ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      footprint_ok (m_vm_lazy mo) A RNG -> mrel A mo mo_ -> ainv (m_vm_lazy mo) A NMAX mo_ ->
      nstep n mo rsp mo' evs ->
      m_halted mo' = None /\ minv mo' /\
      exists mo_', sstep_cfg segs fcfg (mkCfg ms mo_) evs (SNext (mkCfg (nret ms rsp) mo_')) /\ mpost A mo' mo_';
  nsA_exit : forall n RNG A ms mo mo_ code mo',
      at_node n RNG ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      mrel A mo mo_ ->
      nexit n mo code mo' ->
      m_halted mo' = Some code /\
      exists mo_', sstep_cfg segs fcfg (mkCfg ms mo_) [ExitEv code (m_fs mo')] (SNext (mkCfg ms mo_')) /\ m_halted mo_' = Some code;

  nsA_progress : forall n RNG A ms mo mo_, at_node n RNG ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      footprint_ok (m_vm_lazy mo) A RNG -> mrel A mo mo_ -> ainv (m_vm_lazy mo) A NMAX mo_ ->
      (exists rsp mo' evs, nstep n mo rsp mo' evs) \/ (exists code mo', nexit n mo code mo')
}.

Fixpoint implF {R} (RNG : footprint) (t : itree node R)
    (Q : R -> footprint -> machine_state -> Prop) (ms : machine_state) : Prop :=
  match t with
  | Ret r => evtF segs RNG (Q r RNG) ms
  | Vis n k => evtF segs RNG (fun ms1 => at_node n RNG ms1 /\
                 forall rsp RNG', fstep n rsp RNG RNG' -> implF RNG' (k rsp) Q (nret ms1 rsp)) ms
  end.

Lemma implF_ret_intro : forall {R} RNG (r : R) Q ms, evtF segs RNG (Q r RNG) ms -> implF RNG (Ret r) Q ms.
Proof. intros. exact H. Qed.

Lemma implF_mono : forall {R} RNG (t : itree node R) (Q Q' : R -> footprint -> machine_state -> Prop) ms,
  implF RNG t Q ms -> (forall r RNG' ms', Q r RNG' ms' -> Q' r RNG' ms') -> implF RNG t Q' ms.
Proof.
  intros R RNG t; revert RNG. induction t as [r|n k IH]; intros RNG Q Q' ms H HQ; cbn in *.
  - eapply evtF_mono; [exact H|]. cbn. intros ms' H'. apply HQ. exact H'.
  - eapply evtF_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp RNG' HF. eapply IH; eauto.
Qed.

Lemma implF_evtF : forall {R} RNG (t : itree node R) Q P ms,
  evtF segs RNG P ms -> (forall ms', P ms' -> implF RNG t Q ms') -> implF RNG t Q ms.
Proof.
  intros R RNG t Q P ms H K. destruct t; cbn in *; eapply evtF_cut; eauto; intros ms' HP; apply (K _ HP).
Qed.

Lemma implF_bind : forall {A B} RNG (t : itree node A) (f : A -> itree node B) Q1 Q ms,
  implF RNG t Q1 ms -> (forall r RNG' ms', Q1 r RNG' ms' -> implF RNG' (f r) Q ms') -> implF RNG (bind node t f) Q ms.
Proof.
  intros A B RNG t; revert RNG. induction t as [r|n k IH]; intros RNG f Q1 Q ms H Hf; cbn [bind].
  - cbn in H. eapply implF_evtF; [exact H|]. intros ms' HQ. exact (Hf _ _ _ HQ).
  - cbn in H |- *. eapply evtF_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp RNG' HF. eapply IH; eauto.
Qed.

Fixpoint tsafeA {R} (RNG : footprint) (A : alw) (t : itree node R) (mo : Model) : Prop :=
  acct_ok RNG A mo /\
  match t with
  | Ret _ => True
  | Vis n k => nsafe n mo /\
      forall rsp mo' evs, nstep n mo rsp mo' evs ->
        exists RNG' A', fstep n rsp RNG RNG' /\ alw_le A A' /\ tsafeA RNG' A' (k rsp) mo'
  end.

Lemma tsafeA_acct : forall {R} RNG A (t : itree node R) mo, tsafeA RNG A t mo -> acct_ok RNG A mo.
Proof. intros R RNG A [r|n k] mo H; exact (proj1 H). Qed.

Definition ptraces {R} (t : itree node R) (mo : Model) : ShapeAlg.TSet :=
  fun tr => exists full, ttrace nstep nexit t mo full /\ is_prefix tr full.

Definition tree_atA {R} (RNG : footprint) (A : alw) (t : itree node R) Q
    (ms : machine_state) (mo mo_ : Model) : Prop :=
  implF RNG t Q ms /\ leaves_unreachable_m nstep t mo /\ m_halted mo = None /\ minv mo /\
  tsafeA RNG A t mo /\ mrel A mo mo_.

Lemma tree_atA_ainv : forall {R} RNG A (t : itree node R) Q ms mo mo_,
  tree_atA RNG A t Q ms mo mo_ -> ainv (m_vm_lazy mo) A NMAX mo_.
Proof. intros R RNG A t Q ms mo mo_ (_ & _ & _ & _ & TS & MR). eapply mrel_ainv; [eapply tsafeA_acct; exact TS| exact MR]. Qed.

Lemma tree_atA_step : node_soundA -> forall {R} RNG A n (k : resp -> itree node R) Q ms1 mo mo_ rsp mo' evs,
  at_node n RNG ms1 -> (forall rsp RNG', fstep n rsp RNG RNG' -> implF RNG' (k rsp) Q (nret ms1 rsp)) ->
  leaves_unreachable_m nstep (Vis n k) mo -> m_halted mo = None -> minv mo -> tsafeA RNG A (Vis n k) mo ->
  mrel A mo mo_ ->
  nstep n mo rsp mo' evs ->
  exists RNG' A' mo_',
    tree_atA RNG' A' (k rsp) Q (nret ms1 rsp) mo' mo_'
    /\ sstep_cfg segs fcfg (mkCfg ms1 mo_) evs (SNext (mkCfg (nret ms1 rsp) mo_')).
Proof.
  intros NS R RNG A n k Q ms1 mo mo_ rsp mo' evs Hat Hk Hl Hh Hinv Hsf MR Hst.
  pose proof Hsf as (ACC & Hns & Hk').
  destruct (Hk' rsp mo' evs Hst) as (RNG' & A' & HF & HLE & Hsf').
  pose proof (mrel_ainv RNG A mo mo_ ACC MR) as INV.
  destruct (nsA_sound NS n RNG A ms1 mo mo_ rsp mo' evs Hat Hh Hinv Hns (proj1 ACC) MR INV Hst)
    as (Hh' & Hinv' & mo_' & Hss & MP).
  exists RNG', A', mo_'. split; [|exact Hss].
  split; [apply Hk; exact HF|]. split; [eapply leaves_unreachable_m_step; eassumption|].
  split; [exact Hh'|]. split; [exact Hinv'|]. split; [exact Hsf'|].
  eapply mrel_le; [exact MP| exact HLE].
Qed.

Lemma ttrace_exists : node_soundA -> forall {R} (t : itree node R) RNG A Q ms mo mo_,
  tree_atA RNG A t Q ms mo mo_ -> exists full, ttrace nstep nexit t mo full.
Proof.
  intros NS R t. induction t as [r|n k IH]; intros RNG A Q ms mo mo_ HT.
  - destruct HT as (_ & Hl & _). destruct (leaves_unreachable_m_ret _ nstep r mo Hl).
  - pose proof HT as (Ht & Hl & Hh & Hinv & Hsf & MR).
    cbn [implF] in Ht.

    pose proof (tree_atA_ainv _ _ _ _ _ _ _ HT) as INV.
    destruct (evtF_lift segs (m_vm_lazy mo) A NMAX RNG _ ms mo_ (proj1 (tsafeA_acct _ _ _ _ Hsf)) INV
                ltac:(rewrite (mrel_halted _ _ _ MR); exact Hh) Ht)
      as (ms1 & mo1_ & CS & [Hat1 Hk1] & INV1 & SB1).
    assert (MR1 : mrel A mo mo1_) by (eapply mrel_after; eauto).
    destruct (nsA_progress NS n RNG A ms1 mo mo1_ Hat1 Hh Hinv (proj1 (proj2 Hsf)) (proj1 (tsafeA_acct _ _ _ _ Hsf)) MR1 INV1)
      as [(rsp & mo' & evs & Hst)|(code & mo' & Hex)].
    + destruct (tree_atA_step NS RNG A n k Q ms1 mo mo1_ rsp mo' evs Hat1 Hk1 Hl Hh Hinv Hsf MR1 Hst) as (RNG' & A' & mo_' & HT' & _).
      destruct (IH rsp RNG' A' Q (nret ms1 rsp) mo' mo_' HT') as (full' & Hfull').
      exists (evs ++ full'). cbn. right. exists rsp, mo', evs, full'. repeat split; assumption.
    + exists [ExitEv code (m_fs mo')]. cbn. left. exists code, mo'. split; [assumption|reflexivity].
Qed.

Lemma ptraces_nonempty : node_soundA -> forall {R} (t : itree node R) RNG A Q ms mo mo_,
  tree_atA RNG A t Q ms mo mo_ -> ptraces t mo [].
Proof.
  intros NS R t RNG A Q ms mo mo_ HT. destruct (ttrace_exists NS t RNG A Q ms mo mo_ HT) as (full & Hf).
  exists full. split; [exact Hf| apply is_prefix_nil].
Qed.

Lemma cstep_node_ok : forall ms mo ms' mo',
  cstep segs (ms, mo) (ms', mo') ->
  ShapeAlg.node_ok segs (mkCfg ms mo) unit (fun _ => []) (fun _ => mkCfg ms' mo').
Proof.
  intros ms mo ms' mo' (Hh & Hs & Ha). cbn in Hh, Hs, Ha.
  apply ShapeAlg.node_ok_lift; [apply step_nonspur_instr; exact Hs|]. split.
  - intros _. eapply sstep_instr; eauto.
  - intros e st Hss. exists tt. inversion Hss; subst; try congruence.
    all: try (rewrite Ha in *; congruence).
    match goal with H : mi_account_step segs ms mo = MachineOk _ |- _ => rewrite Ha in H; inversion H; subst; auto end.
Qed.

Lemma csteps_srealizes : forall ms mo ms' mo' T,
  csteps segs (ms, mo) (ms', mo') ->
  SpinAlg.srealizes segs (mkCfg ms' mo') T -> SpinAlg.srealizes segs (mkCfg ms mo) T.
Proof.
  intros ms mo ms' mo' T CS.
  remember (ms, mo) as c eqn:Ec. remember (ms', mo') as c' eqn:Ec'.
  revert ms mo ms' mo' Ec Ec'. induction CS as [c|c c1 c2 ST CS IH]; intros ms mo ms' mo' -> E2 Hs.
  - inversion E2; subst. exact Hs.
  - destruct c1 as [ms1 mo1]. eapply SpinAlg.srz_silent1; [apply cstep_node_ok; exact ST|].
    eapply IH; eauto.
Qed.

Section NodeCase.
  Context {R : Type}.
  Variables (n : node) (k : resp -> itree node R) (Q : R -> footprint -> machine_state -> Prop).
  Variables (RNG : footprint) (A : alw) (ms1 : machine_state) (mo mo1_ : Model).
  Hypothesis NS : node_soundA.
  Hypothesis Hat : at_node n RNG ms1.
  Hypothesis Hk : forall rsp RNG', fstep n rsp RNG RNG' -> implF RNG' (k rsp) Q (nret ms1 rsp).
  Hypothesis Hl : leaves_unreachable_m nstep (Vis n k) mo.
  Hypothesis Hh : m_halted mo = None.
  Hypothesis Hinv : minv mo.
  Hypothesis Hsf : tsafeA RNG A (Vis n k) mo.
  Hypothesis MR : mrel A mo mo1_.

  Hypothesis IH : forall rsp RNG' A' ms' mo' mo_',
    tree_atA RNG' A' (k rsp) Q ms' mo' mo_' -> SpinAlg.srealizes segs (mkCfg ms' mo_') (ptraces (k rsp) mo').

  Let c1 : config := mkCfg ms1 mo1_.

  Definition succ : Type := { ce : config * list event | sstep_cfg segs fcfg c1 (snd ce) (SNext (fst ce)) }.
  Definition s_evs (i : succ) : list event := snd (proj1_sig i).
  Definition s_nx (i : succ) : config := fst (proj1_sig i).

  Definition s_T (i : succ) : ShapeAlg.TSet :=
    fun tr =>
      (m_halted (cfg_model (s_nx i)) = None /\
       exists rsp mo', cfg_ms (s_nx i) = nret ms1 rsp /\ nstep n mo rsp mo' (s_evs i) /\
                      mpost A mo' (cfg_model (s_nx i)) /\ ptraces (k rsp) mo' tr)
      \/ (m_halted (cfg_model (s_nx i)) <> None /\ tr = []).

  Lemma INV1 : ainv (m_vm_lazy mo) A NMAX mo1_.
  Proof. eapply mrel_ainv; [eapply tsafeA_acct; exact Hsf| exact MR]. Qed.

  Lemma FOK : footprint_ok (m_vm_lazy mo) A RNG.
  Proof. exact (proj1 (tsafeA_acct _ _ _ _ Hsf)). Qed.

  Lemma NSF : nsafe n mo.
  Proof. exact (proj1 (proj2 Hsf)). Qed.

  Lemma succ_node_ok : ShapeAlg.node_ok segs c1 succ s_evs s_nx.
  Proof.
    split.
    - intros [[c e] Hs]. exact Hs.
    - intros e st Hss.
      destruct (nsA_complete NS n RNG A ms1 mo mo1_ e st Hat Hh Hinv NSF FOK MR INV1 Hss)
        as [(rsp & mo' & mo_' & -> & _) | (code & mo' & mo_' & -> & _)].
      + exists (exist _ (mkCfg (nret ms1 rsp) mo_', e) Hss). split; reflexivity.
      + exists (exist _ (mkCfg ms1 mo_', e) Hss). split; reflexivity.
  Qed.

  Lemma step_tree_atA : forall rsp mo' evs mo_',
    nstep n mo rsp mo' evs -> mpost A mo' mo_' ->
    exists RNG' A', tree_atA RNG' A' (k rsp) Q (nret ms1 rsp) mo' mo_'.
  Proof.
    intros rsp mo' evs mo_' Hst MP.
    pose proof Hsf as (ACC & Hns & Hk').
    destruct (Hk' rsp mo' evs Hst) as (RNG' & A' & HF & HLE & Hsf').
    destruct (nsA_sound NS n RNG A ms1 mo mo1_ rsp mo' evs Hat Hh Hinv Hns FOK MR INV1 Hst) as (Hh' & Hinv' & _).
    exists RNG', A'. split; [apply Hk; exact HF|]. split; [eapply leaves_unreachable_m_step; eassumption|].
    split; [exact Hh'|]. split; [exact Hinv'|]. split; [exact Hsf'|]. eapply mrel_le; eauto.
  Qed.

  Lemma succ_srealizes : forall i, SpinAlg.srealizes segs (s_nx i) (s_T i).
  Proof.
    intros [[c e] Hss]. unfold s_nx, s_evs, s_T. cbn [proj1_sig fst snd].
    destruct (nsA_complete NS n RNG A ms1 mo mo1_ e (SNext c) Hat Hh Hinv NSF FOK MR INV1 Hss)
      as [(rsp & mo' & mo_' & E & Hst & MP) | (code & mo' & mo_' & E & Hex & -> & Hh')]; inversion E; subst; cbn [cfg_ms cfg_model].
    -
      destruct (step_tree_atA rsp mo' e mo_' Hst MP) as (RNG' & A' & HT').
      pose proof (IH rsp RNG' A' _ _ _ HT') as SR.
      eapply SpinAlg.srz_conseq; [exact SR|].
      assert (Hh0 : m_halted mo_' = None).
      { rewrite (mrel_halted _ _ _ MP). exact (proj1 (proj2 (proj2 HT'))). }
      intros tr. split.
      + intros Htr. left. split; [exact Hh0|]. exists rsp, mo'. split; [reflexivity|]. split; [exact Hst|]. split; [exact MP| exact Htr].
      + intros [(_ & rsp2 & mo2 & Ems & Hst2 & MP2 & Htr) | [Hc _]]; [| exfalso; apply Hc; exact Hh0].

        destruct (step_tree_atA rsp2 mo2 e mo_' Hst2 MP2) as (RNG2 & A2 & HT2).
        rewrite <- Ems in HT2.
        pose proof (IH rsp2 RNG2 A2 _ _ _ HT2) as SR2.
        apply (SpinAlg.srealizes_obs_iff segs _ _ SR tr).
        apply (SpinAlg.srealizes_obs_iff segs _ _ SR2 tr). exact Htr.
    -
      eapply SpinAlg.srz_conseq; [apply SpinAlg.srz_halt; cbn; congruence|].
      intros tr. unfold ShapeAlg.t_nil. split.
      + intros ->. right. split; [cbn; congruence| reflexivity].
      + intros [(Hc & _) | [_ ->]]; [cbn in Hc; congruence| reflexivity].
  Qed.

  Lemma node_shape_eq :
    ShapeAlg.t_eq (ShapeAlg.t_alt (fun i => ShapeAlg.t_emit (s_evs i) (s_T i))) (ptraces (Vis n k) mo).
  Proof.
    intros tr. unfold ShapeAlg.t_alt, ShapeAlg.t_emit, ptraces. split.
    - intros ([[c e] Hss] & Hi). unfold s_nx, s_evs, s_T in Hi. cbn [proj1_sig fst snd] in Hi.
      destruct (nsA_complete NS n RNG A ms1 mo mo1_ e (SNext c) Hat Hh Hinv NSF FOK MR INV1 Hss)
        as [(rsp & mo' & mo_' & E & Hst & MP) | (code & mo' & mo_' & E & Hex & -> & Hh')]; inversion E; subst; cbn [cfg_ms cfg_model] in Hi.
      + destruct (step_tree_atA rsp mo' e mo_' Hst MP) as (RNG' & A' & HT').
        destruct Hi as [Hp | (tr' & -> & [(_ & rsp2 & mo2 & Ems & Hst2 & MP2 & (full2 & Hf2 & Hp2)) | [Hc _]])].
        * destruct (ttrace_exists NS (k rsp) RNG' A' Q _ _ _ HT') as (full' & Hf').
          exists (e ++ full'). split; [| eapply is_prefix_trans; [exact Hp| apply is_prefix_app]].
          cbn. right. exists rsp, mo', e, full'. repeat split; assumption.
        * exists (e ++ full2). split; [| apply is_prefix_app_l; exact Hp2].
          cbn. right. exists rsp2, mo2, e, full2. repeat split; assumption.
        * exfalso. apply Hc. cbn [s_nx proj1_sig fst snd cfg_model]. rewrite (mrel_halted _ _ _ MP). exact (proj1 (proj2 (proj2 HT'))).
      + destruct Hi as [Hp | (tr' & -> & [(Hc & _) | [_ ->]])].
        * exists [ExitEv code (m_fs mo')]. split; [| exact Hp]. cbn. left. exists code, mo'. auto.
        * cbn [s_nx proj1_sig fst snd cfg_model] in Hc. congruence.
        * exists [ExitEv code (m_fs mo')]. split. { cbn. left. exists code, mo'. auto. }
          rewrite app_nil_r. apply is_prefix_refl.
    - intros (full & Hf & Hp). cbn in Hf.
      destruct Hf as [(code & mo' & Hex & ->) | (rsp & mo' & evs & tr' & Hst & Hf' & ->)].
      + destruct (nsA_exit NS n RNG A ms1 mo mo1_ code mo' Hat Hh Hinv NSF MR Hex) as (Hh' & mo_' & Hss & Hh_').
        exists (exist _ (mkCfg ms1 mo_', [ExitEv code (m_fs mo')]) Hss). cbn [s_evs s_nx proj1_sig fst snd].
        left. exact Hp.
      + destruct (nsA_sound NS n RNG A ms1 mo mo1_ rsp mo' evs Hat Hh Hinv NSF FOK MR INV1 Hst) as (Hh' & Hinv' & mo_' & Hss & MP).
        exists (exist _ (mkCfg (nret ms1 rsp) mo_', evs) Hss). unfold s_evs, s_nx, s_T. cbn [proj1_sig fst snd cfg_ms cfg_model].
        destruct (ShapeAlg.is_prefix_app_split _ _ _ Hp) as [Hp1 | (tr2 & -> & Hp2)].
        * left. exact Hp1.
        * right. exists tr2. split; [reflexivity|]. left. cbn [s_nx proj1_sig fst snd cfg_model cfg_ms].
          split; [rewrite (mrel_halted _ _ _ MP); exact Hh'|].
          exists rsp, mo'. split; [reflexivity|]. split; [exact Hst|]. split; [exact MP|]. exists tr'. auto.
  Qed.

  Lemma node_srealizes : SpinAlg.srealizes segs c1 (ptraces (Vis n k) mo).
  Proof.

    destruct (nsA_progress NS n RNG A ms1 mo mo1_ Hat Hh Hinv NSF FOK MR INV1) as [(rsp & mo' & evs & Hst)|(code & mo' & Hex)].
    - destruct (nsA_sound NS n RNG A ms1 mo mo1_ rsp mo' evs Hat Hh Hinv NSF FOK MR INV1 Hst) as (_ & _ & mo_' & Hss & _).
      eapply SpinAlg.srz_conseq; [| apply node_shape_eq].
      apply (SpinAlg.srz_node segs c1 succ s_evs s_nx s_T (exist _ (mkCfg (nret ms1 rsp) mo_', evs) Hss)
               succ_node_ok succ_srealizes).
    - destruct (nsA_exit NS n RNG A ms1 mo mo1_ code mo' Hat Hh Hinv NSF MR Hex) as (_ & mo_' & Hss & _).
      eapply SpinAlg.srz_conseq; [| apply node_shape_eq].
      apply (SpinAlg.srz_node segs c1 succ s_evs s_nx s_T (exist _ (mkCfg ms1 mo_', [ExitEv code (m_fs mo')]) Hss)
               succ_node_ok succ_srealizes).
  Qed.
End NodeCase.

Theorem implF_srealizes : node_soundA -> forall {R} (t : itree node R) RNG A Q ms mo mo_,
  tree_atA RNG A t Q ms mo mo_ -> SpinAlg.srealizes segs (mkCfg ms mo_) (ptraces t mo).
Proof.
  intros NS R t. induction t as [r|n k IHk]; intros RNG A Q ms mo mo_ HT.
  - destruct HT as (_ & Hl & _). destruct (leaves_unreachable_m_ret _ nstep r mo Hl).
  - pose proof HT as (Ht & Hl & Hh & Hinv & Hsf & MR).
    cbn [implF] in Ht.
    pose proof (tree_atA_ainv _ _ _ _ _ _ _ HT) as INV.
    destruct (evtF_lift segs (m_vm_lazy mo) A NMAX RNG _ ms mo_ (proj1 (tsafeA_acct _ _ _ _ Hsf)) INV
                ltac:(rewrite (mrel_halted _ _ _ MR); exact Hh) Ht)
      as (ms1 & mo1_ & CS & [Hat1 Hk1] & INV1 & SB1).
    assert (MR1 : mrel A mo mo1_) by (eapply mrel_after; eauto).
    eapply csteps_srealizes; [exact CS|].
    apply (node_srealizes n k Q RNG A ms1 mo mo1_ NS Hat1 Hk1 Hl Hh Hinv Hsf MR1).
    intros rsp RNG' A' ms' mo' mo_' HT'. eapply IHk. exact HT'.
Qed.

Theorem implF_obs_trace : node_soundA -> forall {R} (t : itree node R) RNG A Q ms mo mo_,
  tree_atA RNG A t Q ms mo mo_ ->
  forall tr, obs_trace_cfg segs fcfg (mkCfg ms mo_) tr <-> ptraces t mo tr.
Proof. intros NS R t RNG A Q ms mo mo_ HT. apply SpinAlg.srealizes_obs_iff. eapply implF_srealizes; eauto. Qed.

Theorem implF_no_error : node_soundA -> forall {R} (t : itree node R) RNG A Q ms mo mo_,
  tree_atA RNG A t Q ms mo mo_ -> ~ reaches_error_cfg segs fcfg (mkCfg ms mo_).
Proof. intros NS R t RNG A Q ms mo mo_ HT. eapply SpinAlg.srealizes_no_error. eapply implF_srealizes; eauto. Qed.

Theorem implF_modeled : node_soundA -> forall {R} (t : itree node R) RNG A Q ms mo mo_,
  tree_atA RNG A t Q ms mo mo_ -> ~ reaches_unmodeled_cfg segs fcfg (mkCfg ms mo_).
Proof.
  intros NS R t RNG A Q ms mo mo_ HT Hu. apply reaches_unmodeled_cfg_reaches_error_cfg in Hu. revert Hu.
  eapply implF_no_error; eauto.
Qed.

Definition epostF {X} (Q : X -> footprint -> machine_state -> Prop) : exc X -> footprint -> machine_state -> Prop :=
  fun r RNG ms => match r with Unr => True | Ok a => Q a RNG ms end.

Lemma implF_ret_unr : forall {X} RNG (Q : X -> footprint -> machine_state -> Prop) ms,
  implF RNG (Ret Unr) (epostF Q) ms.
Proof. intros X RNG Q ms. cbn. apply evtF_done. exact I. Qed.

Lemma implF_ret_ok : forall {X} RNG (Q : X -> footprint -> machine_state -> Prop) a ms,
  evtF segs RNG (Q a RNG) ms -> implF RNG (Ret (Ok a)) (epostF Q) ms.
Proof. intros X RNG Q a ms H. exact H. Qed.

Lemma implF_ebind : forall {X Y} RNG (t : itree node (exc X)) (f : X -> itree node (exc Y)) Q1 Q ms,
  implF RNG t (epostF Q1) ms -> (forall a RNG' ms', Q1 a RNG' ms' -> implF RNG' (f a) (epostF Q) ms') ->
  implF RNG (ebind t f) (epostF Q) ms.
Proof.
  intros X Y RNG t f Q1 Q ms Ht Hf. unfold ebind. eapply implF_bind; [exact Ht|].
  intros [|a] RNG' ms' H'; cbn in H'.
  - apply implF_ret_unr.
  - apply Hf. exact H'.
Qed.

Lemma implF_epost_mono : forall {X} RNG (t : itree node (exc X)) (Q Q' : X -> footprint -> machine_state -> Prop) ms,
  implF RNG t (epostF Q) ms -> (forall a RNG' ms', Q a RNG' ms' -> Q' a RNG' ms') -> implF RNG t (epostF Q') ms.
Proof.
  intros X RNG t Q Q' ms H HQ. eapply implF_mono; [exact H|]. intros [|a] RNG' ms'; cbn; auto.
Qed.

Lemma implF_enode : forall {X} RNG n (pl : resp -> option X) (Q : X -> footprint -> machine_state -> Prop) ms,
  evtF segs RNG (fun ms1 => at_node n RNG ms1 /\
                   forall rsp RNG' a, fstep n rsp RNG RNG' -> pl rsp = Some a -> evtF segs RNG' (Q a RNG') (nret ms1 rsp)) ms ->
  implF RNG (enode n pl) (epostF Q) ms.
Proof.
  intros X RNG n pl Q ms H. cbn. eapply evtF_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp RNG' HF. specialize (Hk rsp RNG'). destruct (pl rsp) as [a|]; cbn.
  - apply Hk; [exact HF| reflexivity].
  - apply evtF_done. exact I.
Qed.

End ITreeA.

Arguments mrel A mo mo_ /.
Arguments implF {node} segs at_node fstep {R} RNG t Q ms.
Arguments tsafeA {node} nstep nsafe fstep NMAX {R} RNG A t mo.
Arguments ptraces {node} nstep nexit {R} t mo _.
Arguments tree_atA {node} segs at_node nstep minv nsafe fstep NMAX {R} RNG A t Q ms mo mo_.
Arguments implF_srealizes {node} segs at_node nstep nexit minv nsafe fstep NMAX _ {R} t RNG A Q ms mo mo_ _.
Arguments implF_obs_trace {node} segs at_node nstep nexit minv nsafe fstep NMAX _ {R} t RNG A Q ms mo mo_ _.
Arguments implF_no_error {node} segs at_node nstep nexit minv nsafe fstep NMAX _ {R} t RNG A Q ms mo mo_ _.
