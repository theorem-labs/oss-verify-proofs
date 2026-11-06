(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import CfgStep CatSim ShapeAlg.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes ITreeCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition node_alloc (n : node) : bool :=
  match n with NBrk _ | NMmap _ _ _ _ | NMprotect _ _ _ => true | _ => false end.

Definition node_refusal_b (n : node) (mo : Model) (r : word) : bool :=
  if node_alloc n then match node_input n with Some i => refusal_b i mo r | None => false end else false.

Definition nstep_c (n : node) (mo : Model) (eff : resp) (mo' : Model) (evs : list event) : Prop :=
  nstep n mo eff mo' evs /\
  (node_refusal_b n mo (eff_ret eff) = true ->
   forall eff2 mo2 evs2, nstep n mo eff2 mo2 evs2 -> node_refusal_b n mo (eff_ret eff2) = true).

Definition node_decided (n : node) (mo : Model) : Prop :=
  (exists eff mo' evs, nstep n mo eff mo' evs /\ node_refusal_b n mo (eff_ret eff) = false)
  \/ (forall eff mo' evs, nstep n mo eff mo' evs -> node_refusal_b n mo (eff_ret eff) = true).

Definition nsafe_c (n : node) (mo : Model) : Prop :=
  nsafe n mo /\ (node_alloc n = true -> node_decided n mo).

Lemma nstep_c_nstep : forall n mo eff mo' evs, nstep_c n mo eff mo' evs -> nstep n mo eff mo' evs.
Proof. intros n mo eff mo' evs H. exact (proj1 H). Qed.

Lemma node_refusal_nonalloc : forall n mo r, node_alloc n = false -> node_refusal_b n mo r = false.
Proof. intros n mo r Hn. unfold node_refusal_b. rewrite Hn. reflexivity. Qed.

Lemma nstep_c_of_nonalloc : forall n mo eff mo' evs, node_alloc n = false -> nstep n mo eff mo' evs -> nstep_c n mo eff mo' evs.
Proof. intros n mo eff mo' evs Hn H. split; [exact H|]. rewrite (node_refusal_nonalloc n mo _ Hn). discriminate. Qed.

(* [comment removed for export] *)
Lemma nstep_c_of_grant : forall n mo eff mo' evs, nstep n mo eff mo' evs -> node_refusal_b n mo (eff_ret eff) = false ->
  nstep_c n mo eff mo' evs.
Proof. intros n mo eff mo' evs H Hr. split; [exact H|]. rewrite Hr. discriminate. Qed.

(* [comment removed for export] *)
Lemma nstep_c_grant_only : forall n mo eff mo' evs,
  (exists eff2 mo2 evs2, nstep n mo eff2 mo2 evs2 /\ node_refusal_b n mo (eff_ret eff2) = false) ->
  nstep_c n mo eff mo' evs -> node_refusal_b n mo (eff_ret eff) = false.
Proof.
  intros n mo eff mo' evs (eff2 & mo2 & evs2 & H2 & Hr2) [_ Hc].
  destruct (node_refusal_b n mo (eff_ret eff)) eqn:Hr; [| reflexivity].
  rewrite (Hc eq_refl eff2 mo2 evs2 H2) in Hr2. discriminate Hr2.
Qed.

Lemma nsafe_c_of_nonalloc : forall n mo, node_alloc n = false -> nsafe n mo -> nsafe_c n mo.
Proof. intros n mo Hn H. split; [exact H|]. intros E. rewrite Hn in E. discriminate E. Qed.

Lemma node_decided_of_grant : forall n mo eff mo' evs, nstep n mo eff mo' evs -> node_refusal_b n mo (eff_ret eff) = false ->
  node_decided n mo.
Proof. intros n mo eff mo' evs H Hr. left. exists eff, mo', evs. split; assumption. Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma at_node_svc : forall n ms, at_node segs n ms -> exists x8, ms_svc_pending ms = Some x8.
Proof.
  intros n ms Hat. destruct n as [| | | | | |c| | | |]; cbn [at_node] in Hat;
    first [ destruct Hat as [[H|H] _]; eexists; exact H
          | destruct Hat as [H _]; eexists; exact H
          | eexists; exact Hat ].
Qed.

(* [comment removed for export] *)
Lemma at_node_pending_on : forall n ms mo, node_alloc n = false -> at_node segs n ms -> pending_on segs kit_cfg (mkCfg ms mo).
Proof.
  intros n ms mo Hn Hat.
  destruct n as [fd bufs|path|fd buf count|fd|fd req| |c|req|a l p f|a l|a l p]; try discriminate Hn; cbn [at_node] in Hat.
  - destruct Hat as [H _]. exact (kit_pending_on_sysno segs ms mo _ 66 H ltac:(apply unsigned_lit; lia) eq_refl).
  - destruct Hat as [H _]. exact (kit_pending_on_sysno segs ms mo _ 56 H ltac:(apply unsigned_lit; lia) eq_refl).
  - destruct Hat as [H _]. exact (kit_pending_on_sysno segs ms mo _ 63 H ltac:(apply unsigned_lit; lia) eq_refl).
  - destruct Hat as [H _]. exact (kit_pending_on_sysno segs ms mo _ 57 H ltac:(apply unsigned_lit; lia) eq_refl).
  - destruct Hat as [H _]. exact (kit_pending_on_sysno segs ms mo _ 29 H ltac:(apply unsigned_lit; lia) eq_refl).
  - exact (kit_pending_on_sysno segs ms mo _ 96 Hat ltac:(apply unsigned_lit; lia) eq_refl).
  - destruct Hat as [[H|H] _].
    + exact (kit_pending_on_sysno segs ms mo _ 93 H ltac:(apply unsigned_lit; lia) eq_refl).
    + exact (kit_pending_on_sysno segs ms mo _ 94 H ltac:(apply unsigned_lit; lia) eq_refl).
  - destruct Hat as [H _]. exact (kit_pending_on_sysno segs ms mo _ 215 H ltac:(apply unsigned_lit; lia) eq_refl).
Qed.

(* [comment removed for export] *)
Lemma at_node_refusal : forall n ms mo x8 r, node_alloc n = true -> at_node segs n ms -> ms_svc_pending ms = Some x8 ->
  refusal_b (sys_input segs ms x8) mo r = node_refusal_b n mo r.
Proof.
  intros n ms mo x8 r Hn Hat Hsvc. unfold node_refusal_b. rewrite Hn.
  destruct n as [fd bufs|path|fd buf count|fd|fd req| |c|req|a l p f|a l|a l p]; try discriminate Hn;
    cbn [at_node] in Hat; cbn [node_input].
  - destruct Hat as [H Ha0]. rewrite H in Hsvc. injection Hsvc as <-.
    unfold refusal_b. rewrite in_sysno_si. cbn [pure_input in_sysno]. rewrite unsigned_lit by lia. cbn [Z.eqb Pos.eqb].
    rewrite in_a0_si, Ha0. reflexivity.
  - destruct Hat as [H _]. rewrite H in Hsvc. injection Hsvc as <-.
    unfold refusal_b. rewrite in_sysno_si. cbn [pure_input in_sysno]. reflexivity.
  - destruct Hat as [H _]. rewrite H in Hsvc. injection Hsvc as <-.
    unfold refusal_b. rewrite in_sysno_si. cbn [pure_input in_sysno]. reflexivity.
Qed.

Lemma at_node_pending_off : forall n ms mo, node_alloc n = true -> at_node segs n ms -> pending_off segs kit_cfg (mkCfg ms mo).
Proof.
  intros n ms mo Hn Hat.
  destruct n as [fd bufs|path|fd buf count|fd|fd req| |c|req|a l p f|a l|a l p]; try discriminate Hn; cbn [at_node] in Hat;
    destruct Hat as [H _].
  - exact (kit_pending_off_sysno segs ms mo _ 214 H ltac:(apply unsigned_lit; lia) eq_refl).
  - exact (kit_pending_off_sysno segs ms mo _ 222 H ltac:(apply unsigned_lit; lia) eq_refl).
  - exact (kit_pending_off_sysno segs ms mo _ 226 H ltac:(apply unsigned_lit; lia) eq_refl).
Qed.

(* [comment removed for export] *)
Lemma child_refusal_nret : forall n ms mo eff mo', node_alloc n = true -> at_node segs n ms -> m_halted mo' = None ->
  child_refusal_b segs (mkCfg ms mo) (mkCfg (nret ms eff) mo') = node_refusal_b n mo (eff_ret eff).
Proof.
  intros n ms mo eff mo' Hn Hat Hh. destruct (at_node_svc n ms Hat) as [x8 Hsvc].
  unfold nret. rewrite (child_refusal_b_syscall segs ms mo x8 eff mo' Hsvc Hh).
  exact (at_node_refusal n ms mo x8 (eff_ret eff) Hn Hat Hsvc).
Qed.

(* [comment removed for export] *)
Lemma nonrefusal_outcome_nstep : forall n ms mo, node_alloc n = true -> at_node segs n ms -> m_halted mo = None -> minv mo ->
  nsafe n mo -> nonrefusal_outcome segs (mkCfg ms mo) ->
  exists eff mo' evs, nstep n mo eff mo' evs /\ node_refusal_b n mo (eff_ret eff) = false.
Proof.
  intros n ms mo Hal Hat Hh Hminv Hsafe (x8 & eff & m1 & evs & Hsvc & Hspec & Hnr). cbn [cfg_ms cfg_model] in *.
  pose proof (nodes_sound segs) as NS.
  assert (NX : forall code mo', ~ nexit n mo code mo').
  { intros code mo' Hx. destruct n; try discriminate Hal; exact Hx. }
  assert (NR : forall rsp mo' m', SNext (mkCfg ms m') = SNext (mkCfg (nret ms rsp) mo') -> False).
  { intros rsp mo' m' E. assert (E1 : ms = nret ms rsp) by exact (f_equal (fun X => match X with SNext c => cfg_ms c | _ => ms end) E).
    pose proof (nret_svc ms rsp) as Hn. rewrite <- E1 in Hn. congruence. }
  destruct (m_killed m1) as [sig|] eqn:Hk.
  { pose proof (sstep_killed segs ms mo x8 eff m1 evs sig Hh Hsvc Hspec Hk) as Hst.
    destruct (ns_complete _ _ _ _ _ _ _ NS n ms mo _ _ Hat Hh Hminv Hsafe Hst) as [(rsp & mo' & E & _)|(code & mo' & _ & Hx & _)];
      [exfalso; exact (NR _ _ _ E)| exfalso; exact (NX _ _ Hx)]. }
  destruct (m_halted m1) as [code|] eqn:Hh1.
  { pose proof (sstep_exit segs ms mo x8 eff m1 evs code Hh Hsvc Hspec Hh1 Hk) as Hst.
    destruct (ns_complete _ _ _ _ _ _ _ NS n ms mo _ _ Hat Hh Hminv Hsafe Hst) as [(rsp & mo' & E & _)|(code' & mo' & _ & Hx & _)];
      [exfalso; exact (NR _ _ _ E)| exfalso; exact (NX _ _ Hx)]. }
  destruct (materialize_model_accesses m1 (syscall_effect_accesses eff)) as [m2|] eqn:Hm.
  - pose proof (sstep_syscall segs ms mo x8 eff m1 m2 evs Hh Hsvc Hspec Hh1 Hm) as Hst.
    destruct (ns_complete _ _ _ _ _ _ _ NS n ms mo _ _ Hat Hh Hminv Hsafe Hst) as [(rsp & mo' & E & Hn)|(code' & mo' & _ & Hx & _)];
      [| exfalso; exact (NX _ _ Hx)].
    exists rsp, mo', evs. split; [exact Hn|].
    destruct (ns_sound _ _ _ _ _ _ _ NS n ms mo rsp mo' evs Hat Hh Hminv Hsafe Hn) as (Hh' & _ & _).
    rewrite <- (child_refusal_nret n ms mo rsp mo' Hal Hat Hh').
    assert (Ec : mkCfg (advance_past_svc (apply_effect ms eff)) m2 = mkCfg (nret ms rsp) mo') by congruence.
    assert (Em : m2 = mo') by exact (f_equal cfg_model Ec).
    rewrite <- Ec.
    rewrite (child_refusal_b_syscall segs ms mo x8 eff m2 Hsvc ltac:(rewrite Em; exact Hh')). exact Hnr.
  - pose proof (sstep_syscall_materialization_fault segs ms mo x8 eff m1 evs Hh Hsvc Hspec Hh1 Hm) as Hst.
    destruct (ns_complete _ _ _ _ _ _ _ NS n ms mo _ _ Hat Hh Hminv Hsafe Hst) as [(rsp & mo' & E & _)|(code' & mo' & E & _)];
      discriminate E.
Qed.

Theorem nodes_sound_cfg : node_sound_cfg node segs (at_node segs) nstep_c nexit minv nsafe_c.
Proof.
  pose proof (nodes_sound segs) as NS. constructor.
  - (* [comment removed for export] *) exact (ns_lazy _ _ _ _ _ _ _ NS).
  - (* [comment removed for export] *)
    intros n ms mo evs X Hat Hh Hminv [Hsafe _] Hst.
    pose proof (sstep_cfg_sub segs kit_cfg _ _ _ Hst) as Hu.
    destruct (ns_complete _ _ _ _ _ _ _ NS n ms mo evs X Hat Hh Hminv Hsafe Hu)
      as [(rsp & mo' & -> & Hn)|(code & mo' & -> & Hx & ->)]; [left| right; eexists _, _; split; [reflexivity| split; [exact Hx| reflexivity]]].
    exists rsp, mo'. split; [reflexivity|]. split; [exact Hn|].
    intros Hr eff2 mo2 evs2 Hn2.
    destruct (node_alloc n) eqn:Hal; [| rewrite (node_refusal_nonalloc n mo _ Hal) in Hr; discriminate Hr].
    destruct (node_refusal_b n mo (eff_ret eff2)) eqn:Hr2; [reflexivity| exfalso].
    (* [comment removed for export] *)
    destruct (ns_sound _ _ _ _ _ _ _ NS n ms mo rsp mo' evs Hat Hh Hminv Hsafe Hn) as (Hh' & _ & _).
    apply (proj1 (sstep_cfg_next_iff segs kit_cfg _ _ _)) in Hst. destruct Hst as [_ Hns]. apply Hns.
    split; [exact (at_node_pending_off n ms mo Hal Hat)|].
    split; [rewrite (child_refusal_nret n ms mo rsp mo' Hal Hat Hh'); exact Hr|].
    destruct (ns_sound _ _ _ _ _ _ _ NS n ms mo eff2 mo2 evs2 Hat Hh Hminv Hsafe Hn2) as (Hh2 & _ & Hs2).
    apply (nonrefusal_outcome_of_child segs kit_cfg _ evs2 _ Hs2 (at_node_pending_off n ms mo Hal Hat) Hh2).
    rewrite (child_refusal_nret n ms mo eff2 mo2 Hal Hat Hh2). exact Hr2.
  - (* [comment removed for export] *)
    intros n ms mo rsp mo' evs Hat Hh Hminv [Hsafe _] [Hn Hc].
    destruct (ns_sound _ _ _ _ _ _ _ NS n ms mo rsp mo' evs Hat Hh Hminv Hsafe Hn) as (Hh' & Hinv' & Hs).
    split; [exact Hh'|]. split; [exact Hinv'|].
    apply (proj2 (sstep_cfg_next_iff segs kit_cfg _ _ _)). split; [exact Hs|].
    destruct (node_alloc n) eqn:Hal; [| apply spurious_child_not_on; exact (at_node_pending_on n ms mo Hal Hat)].
    destruct (node_refusal_b n mo (eff_ret rsp)) eqn:Hr.
    + (* [comment removed for export] *)
      intros (_ & _ & Hout).
      destruct (nonrefusal_outcome_nstep n ms mo Hal Hat Hh Hminv Hsafe Hout) as (eff2 & mo2 & evs2 & Hn2 & Hr2).
      rewrite (Hc eq_refl eff2 mo2 evs2 Hn2) in Hr2. discriminate Hr2.
    + apply spurious_child_not_refusal. rewrite (child_refusal_nret n ms mo rsp mo' Hal Hat Hh'). exact Hr.
  - (* [comment removed for export] *)
    intros n ms mo code mo' Hat Hh Hminv [Hsafe _] Hx.
    destruct (ns_exit _ _ _ _ _ _ _ NS n ms mo code mo' Hat Hh Hminv Hsafe Hx) as (Hh' & Hs).
    split; [exact Hh'|].
    apply (proj2 (sstep_cfg_next_iff segs kit_cfg _ _ _)). split; [exact Hs|].
    apply spurious_child_not_refusal. apply child_refusal_b_halted. cbn [cfg_model]. rewrite Hh'. discriminate.
  - (* [comment removed for export] *)
    intros n ms mo Hat Hh Hminv [Hsafe Hdec].
    destruct (ns_progress _ _ _ _ _ _ _ NS n ms mo Hat Hh Hminv Hsafe) as [(rsp & mo' & evs & Hn)|Hx]; [left| right; exact Hx].
    destruct (node_alloc n) eqn:Hal; [| exists rsp, mo', evs; exact (nstep_c_of_nonalloc n mo rsp mo' evs Hal Hn)].
    destruct (Hdec eq_refl) as [(eff2 & mo2 & evs2 & Hn2 & Hr2)|Hall].
    + exists eff2, mo2, evs2. exact (nstep_c_of_grant n mo eff2 mo2 evs2 Hn2 Hr2).
    + exists rsp, mo', evs. split; [exact Hn|]. intros _. exact Hall.
Qed.

End WithSegs.
