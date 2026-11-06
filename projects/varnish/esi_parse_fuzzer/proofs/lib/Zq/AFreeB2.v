(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic AMalmys AMal9l1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ABudget.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf AQPart AQWf2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQPart.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQPart OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQPart.AQWfJ.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pboth).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition free_lm (A : AState) (p : Z) : gmap Z liveinfo := delete p (a_livemap A).
Definition free_entry (li : liveinfo) : qentry := QE (li_chunk li) (li_n li).

Definition freeA_fast (A : AState) (p : Z) (li : liveinfo) (key : list Z) : AState :=
  mkA (a_pl A) (a_reg A) (a_cache_inited A) (a_cache A)
      (free_lm A p) (qpush_last (a_qthread A) (free_entry li)) (a_qglobal A) (a_sec A)
      (fst (depot_putC (a_depot A) key))
      (a_fhint A) (a_fframes A) (a_ia_inited A) (a_oom A) (a_tiny A) (a_qlimbo A) (a_scred A) (a_deadsh A) (a_pcred A) (a_paid A).

Definition freeA_new (A : AState) (p : Z) (li : liveinfo) (key : list Z) : AState :=
  let ks := pk_chunks (a_cache A kQuarantineBatchClass) in
  let kb := last ks 0 in
  mkA (a_pl A) (a_reg A) (a_cache_inited A) (cache_set (a_cache A) kQuarantineBatchClass (removelast ks))
      (free_lm A p) (qpush_new (a_qthread A) kb (free_entry li)) (a_qglobal A) (a_sec A)
      (fst (depot_putC (a_depot A) key))
      (a_fhint A) (a_fframes A) (a_ia_inited A) (a_oom A) (a_tiny A) (a_qlimbo A) (a_scred A) (a_deadsh A) (a_pcred A) (a_paid A).

Section WfFree.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {DR : DepotRep}.
  Variables (A : AState) (m : mem) (md : Model) (p n0 : Z) (li : liveinfo) (key : list Z).
  Hypothesis AI : pa_ainv A m md.
  Hypothesis LU : a_livemap A !! p = Some li.
  Hypothesis LN : li_n li = n0.
  Hypothesis KEYU : In key (p_dkeys (a_pl A)).
  Let W : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.

  Lemma free_uniq : forall u' li', a_livemap A !! u' = Some li' -> p <> u' -> li_chunk li <> li_chunk li'.
  Proof. intros. eapply (live_chunk_unique (a_sb A) (a_reg A) (a_livemap A) (a_sec A) p li (wfV A W) LU); eassumption. Qed.

  Lemma free_lrange : forall c k, li_chunk li = ChP (CP c k) -> 1 <= c <= 30 /\ 0 <= k < carved_count_ (a_reg A) c.
  Proof.
    intros c k E. (first [ pose proof ((wfV A W)) as dR_1; dand3 dR_1 as V1 _ _ | destruct (wfV A W) as (V1 & _ & _) ]). (first [ pose proof ((V1 p li LU)) as dR_2; dand3 dR_2 as N _ C | pose proof (V1 p li LU) as (N & _ & C) ]). cbv zeta in C. rewrite E in C.
    (first [ dand3 C as N2 Hc Hk | destruct C as (N2 & Hc & Hk) ]). cbv zeta in N. pose proof (class_of_range (li_n li) ltac:(lia)) as CR. rewrite <- Hc in CR.
    split; [exact CR| exact Hk].
  Qed.

  (* [comment removed for export] *)
  Lemma free_wfD : wf_depot_ (p_dkeys (a_pl A)) (fst (depot_putC (a_depot A) key)).
  Proof.
    (first [ pose proof ((wfD A W)) as dR_4; dand3 dR_4 as INC ND NN | destruct (wfD A W) as (INC & ND & NN) ]). split; [| split; [apply depot_putC_nodup; exact ND| apply depot_putC_nonnil; exact NN]].
    apply Forall_forall. intros k Hk. assert (INC' : incl (a_depot A) (p_dkeys (a_pl A))) by (intros x Hx; exact (proj1 (Forall_forall _ _) INC x Hx)).
    exact (depot_putC_incl _ _ _ INC' KEYU k Hk).
  Qed.

  Theorem free_fast_WF :
    a_qthread A <> [] -> Z.of_nat (length (ba_entries (last (a_qthread A) (BA 0 [])))) < kQuarantineBatchCount ->
    q_bytes (a_qthread A) + qe_bytes (free_entry li) <= kQuarantineCacheSize ->
    WF (freeA_fast A p li key).
  Proof.
    intros NE ROOM SZ.
    destruct W as [wP wM wR wC wX wV wQ wS wD wF wB wI wE wJ wN] eqn:EW. clear EW.
    constructor; cbn [freeA_fast a_pl a_reg a_cache_inited a_cache a_livemap a_qthread a_qglobal a_sec a_depot a_fhint a_fframes a_ia_inited a_oom a_tiny a_qlimbo a_scred a_deadsh a_pcred a_paid a_sb a_fs].
    - exact wP.
    - exact wM.
    - exact wR.
    - exact wC.
    - (* [comment removed for export] *) apply (proj2 (wf_partition_pfun (PT (a_reg A) (a_cache A) (free_lm A p) (qpush_last (a_qthread A) (free_entry li)) (a_qglobal A)))).
      unfold free_lm, free_entry. apply (pfun_free_push_last (a_reg A) (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A) p li).
      + apply (proj1 (wf_partition_pfun (PT _ _ _ _ _))). exact wX.
      + exact LU.
      + exact free_uniq.
      + exact free_lrange.
      + exact NE.
    - unfold free_lm. exact (wf_live_delete (a_sb A) (a_reg A) (a_livemap A) (a_sec A) p li wV LU).
    - unfold free_lm, free_entry. apply (wf_quarantine_push_last (a_reg A) (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A) p li wQ LU).
      + exact (wf_qentry_of_live (a_sb A) (a_reg A) (a_livemap A) (a_sec A) p li wV LU).
      + exact free_uniq.
      + exact NE.
      + exact ROOM.
      + exact SZ.
    - unfold free_lm, free_entry. exact (wf_sec_free_push_last AL_pboth (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A) p li wS LU NE).
    - exact free_wfD.
    - exact wF.
    - unfold free_lm, free_entry.
      (first [ dand3 wV as V1 _ V3 | destruct wV as (V1 & _ & V3) ]). pose proof (V1 p li LU) as (N & _). cbv zeta in N.
      apply (wf_budget_free_push_last (a_tiny A) (a_livemap A) (a_qthread A) (a_qglobal A) p li wB LU); [| exact NE].
      pose proof (as_livebytes_delete (a_livemap A) p li LU).
      pose proof (as_livebytes_nonneg (delete p (a_livemap A)) ltac:(intros u l Hu; rewrite lookup_delete_Some in Hu; destruct Hu as [_ Hu]; pose proof (V1 u l Hu) as (X & _); cbv zeta in X; lia)). lia.
    - exact wI.
    - exact wE.
    - exact wJ.
    - (* [comment removed for export] *) unfold free_lm, free_entry. exact (wf_prim_free_push_last (a_livemap A) (a_qthread A) (a_qglobal A) (a_paid A) (a_pcred A) p li wN LU NE).
  Qed.

  (* [comment removed for export] *)
  Local Notation ks24 := (pk_chunks (a_cache A kQuarantineBatchClass)).
  Local Notation kb := (last ks24 0).

  Lemma c24_facts : ks24 <> [] -> NoDup ks24 /\ In kb ks24 /\ 0 <= kb < carved_count_ (a_reg A) kQuarantineBatchClass /\
                    (forall k, In k (removelast ks24) <-> In k ks24 /\ k <> kb) /\ Z.of_nat (length ks24) <= max_count kQuarantineBatchClass.
  Proof.
    intros NE. destruct (wfC A W) as (C1 & _). (first [ pose proof ((C1 kQuarantineBatchClass ltac:(unfold kQuarantineBatchClass; lia))) as dR_6; dand4 dR_6 as L ND B _ | destruct (C1 kQuarantineBatchClass ltac:(unfold kQuarantineBatchClass; lia)) as (L & ND & B & _) ]). cbv zeta in L, ND, B.
    pose proof (kb_in (a_cache A) kb NE eq_refl) as IN.
    split; [exact ND|]. split; [exact IN|]. split; [exact (B _ IN)|]. split; [| exact L].
    intros k. apply (removelast_in_iff (a_cache A) kb ND NE eq_refl).
  Qed.

  (* [comment removed for export] *)
  Lemma kb_not_batch : ks24 <> [] -> ~ In kb (batch_indices_ (a_qthread A) (a_qglobal A)).
  Proof.
    intros NE Hin. (first [ pose proof ((c24_facts NE)) as dR_7; dand4 dR_7 as ND IN KR _ | destruct (c24_facts NE) as (ND & IN & KR & _) ]).
    pose proof (wfX A W kQuarantineBatchClass kb ltac:(unfold kQuarantineBatchClass; lia) KR) as X. cbv zeta in X.
    (first [ dand9 X as _ _ _ _ _ _ _ NCB _ | destruct X as (_ & _ & _ & _ & _ & _ & _ & NCB & _) ]). apply NCB. split; [exact IN| split; [reflexivity| exact Hin]].
  Qed.

  Theorem free_new_WF :
    ks24 <> [] ->
    (a_qthread A = [] \/ Z.of_nat (length (ba_entries (last (a_qthread A) (BA 0 [])))) = kQuarantineBatchCount) ->
    q_bytes (a_qthread A) + kQuarantineBatchBytes + qe_bytes (free_entry li) <= kQuarantineCacheSize ->
    WF (freeA_new A p li key).
  Proof.
    intros NE FULL SZ. (first [ pose proof ((c24_facts NE)) as dR_9; dand5 dR_9 as ND IN KR RL L24 | destruct (c24_facts NE) as (ND & IN & KR & RL & L24) ]).
    pose proof (kb_not_batch NE) as KNB.
    destruct W as [wP wM wR wC wX wV wQ wS wD wF wB wI wE wJ wN] eqn:EW. clear EW.
    constructor.
    - exact wP.
    - exact wM.
    - exact wR.
    - (* [comment removed for export] *)
      change (wf_caches_ (a_reg A) (cache_set (a_cache A) kQuarantineBatchClass (removelast ks24)) (a_cache_inited A)).
      apply (wf_caches_set (a_reg A) (a_cache A) (a_cache_inited A) kQuarantineBatchClass (removelast ks24) wC ltac:(unfold kQuarantineBatchClass; lia)).
      + rewrite removelast_length'. lia.
      + exact (proj1 (removelast_nodup ks24 ND)).
      + intros k Hk. apply RL in Hk as [Hk _]. destruct wC as (C1 & _). (first [ pose proof ((C1 kQuarantineBatchClass ltac:(unfold kQuarantineBatchClass; lia))) as dR_10; dand4 dR_10 as _ _ B _ | destruct (C1 kQuarantineBatchClass ltac:(unfold kQuarantineBatchClass; lia)) as (_ & _ & B & _) ]). exact (B k Hk).
      + intros CI. destruct wC as (C1 & _). (first [ pose proof ((C1 kQuarantineBatchClass ltac:(unfold kQuarantineBatchClass; lia))) as dR_11; dand4 dR_11 as _ _ _ Z0 | destruct (C1 kQuarantineBatchClass ltac:(unfold kQuarantineBatchClass; lia)) as (_ & _ & _ & Z0) ]). cbv zeta in Z0. rewrite (Z0 CI). reflexivity.
    - (* [comment removed for export] *)
      change (wf_partition_T (PT (a_reg A) (nb_cache (a_cache A)) (delete p (a_livemap A)) (qpush_new (a_qthread A) kb (QE (li_chunk li) (li_n li))) (a_qglobal A))).
      apply (proj2 (wf_partition_pfun (PT _ _ _ _ _))). rewrite <- (qpush_last_emptybatch (a_qthread A) kb).
      change (a_qthread A ++ [BA kb []]) with (nb_qt (a_qthread A) kb).
      apply (pfun_free_gen (a_reg A) (nb_cache (a_cache A)) (a_livemap A) (nb_qt (a_qthread A) kb) (a_qglobal A) p li).
      + apply (pfun_newbatch (a_reg A) (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A) kb); [| exact ND| exact NE| reflexivity| exact KR].
        apply (proj1 (wf_partition_pfun (PT _ _ _ _ _))). exact wX.
      + exact LU.
      + exact free_uniq.
      + exact free_lrange.
      + apply p_quar_push_last. intros H; apply app_eq_nil in H; destruct H; discriminate.
      + apply p_batch_push_last. intros H; apply app_eq_nil in H; destruct H; discriminate.
    - exact (wf_live_delete (a_sb A) (a_reg A) (a_livemap A) (a_sec A) p li wV LU).
    - apply (wf_quarantine_push_new (a_reg A) (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A) p li wQ LU).
      + exact (wf_qentry_of_live (a_sb A) (a_reg A) (a_livemap A) (a_sec A) p li wV LU).
      + exact free_uniq.
      + exact FULL.
      + exact KR.
      + exact KNB.
      + exact SZ.
    - exact (wf_sec_free_push_new AL_pboth (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A) p li wS LU kb).
    - exact free_wfD.
    - exact wF.
    - (first [ dand3 wV as V1 _ V3 | destruct wV as (V1 & _ & V3) ]). pose proof (V1 p li LU) as (N & _). cbv zeta in N.
      apply (wf_budget_free_push_new (a_tiny A) (a_livemap A) (a_qthread A) (a_qglobal A) p li wB LU).
      pose proof (as_livebytes_delete (a_livemap A) p li LU).
      pose proof (as_livebytes_nonneg (delete p (a_livemap A)) ltac:(intros u l Hu; rewrite lookup_delete_Some in Hu; destruct Hu as [_ Hu]; pose proof (V1 u l Hu) as (X & _); cbv zeta in X; lia)). lia.
    - exact wI.
    - exact wE.
    - exact wJ.
    - (* [comment removed for export] *) exact (wf_prim_free_push_new (a_livemap A) (a_qthread A) (a_qglobal A) (a_paid A) (a_pcred A) p li wN LU kb).
  Qed.
End WfFree.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xferA (A : AState) : AState :=
  mkA (a_pl A) (a_reg A) (a_cache_inited A) (a_cache A)
      (a_livemap A) [] (qtransfer (a_qthread A) (a_qglobal A)) (a_sec A) (a_depot A)
      (a_fhint A) (a_fframes A) (a_ia_inited A) (a_oom A) (a_tiny A) (a_qlimbo A) (a_scred A) (a_deadsh A) (a_pcred A) (a_paid A).

Section WfXfer.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variable (A : AState).
  Hypothesis W : WF A.
  (* [comment removed for export] *)
End WfXfer.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WFBdef.
Context {Clg : Ceiling}.
  Record WFB (B : Z) (A : AState) : Prop := {
    wgP : wf_place AL_pboth (a_pl A);
    wgM : wf_bigmaps_ (a_pl A) (a_sec A);
    wgR : wf_regions_ (a_reg A) (a_paid A) (a_cache_inited A);   (* [comment removed for export] *)
    wgC : wf_caches_ (a_reg A) (a_cache A) (a_cache_inited A);
    wgX : wf_partition_ (a_reg A) (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A);
    wgV : wf_live_ (a_sb A) (a_reg A) (a_livemap A) (a_sec A);
    wgQ : wf_quarantineB B (a_reg A) (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A);
    wgS : wf_sec_ AL_pboth (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A);
    wgD : wf_depot_ (p_dkeys (a_pl A)) (a_depot A);
    wgF : wf_fstack_ (a_fs A) (a_fhint A) (a_fframes A);
    wgB : wf_budget_ (a_tiny A) (a_livemap A) (a_qthread A) (a_qglobal A);
    wgI : a_qlimbo A = [];
    wgE : wf_dead_ (a_scred A) (a_deadsh A) (Z.of_nat (length (sr_chunks (a_sec A))));
    wgJ : wf_qcredit_ (a_qglobal A);
    wgN : wf_prim_ (a_livemap A) (a_qthread A) (a_qglobal A) (a_paid A) (a_pcred A) }.   (* [comment removed for export] *)
End WFBdef.

Section WfFreeB.
Context {Clg : Ceiling}.
  Context {DR : DepotRep}.
  Variables (A : AState) (m : mem) (md : Model) (p n0 : Z) (li : liveinfo) (key : list Z).
  Hypothesis AI : pa_ainv A m md.
  Hypothesis LU : a_livemap A !! p = Some li.
  Hypothesis LN : li_n li = n0.
  Hypothesis KEYU : In key (p_dkeys (a_pl A)).
  Let W : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.

  Theorem free_fast_WFB :
    a_qthread A <> [] -> Z.of_nat (length (ba_entries (last (a_qthread A) (BA 0 [])))) < kQuarantineBatchCount ->
    WFB (q_bytes (a_qthread A) + qe_bytes (free_entry li)) (freeA_fast A p li key).
  Proof.
    intros NE ROOM.
    destruct W as [wP wM wR wC wX wV wQ wS wD wF wB wI wE wJ wN] eqn:EW. clear EW.
    constructor; cbn [freeA_fast a_pl a_reg a_cache_inited a_cache a_livemap a_qthread a_qglobal a_sec a_depot a_fhint a_fframes a_ia_inited a_oom a_tiny a_qlimbo a_scred a_deadsh a_pcred a_paid a_sb a_fs].
    - exact wP.
    - exact wM.
    - exact wR.
    - exact wC.
    - apply (proj2 (wf_partition_pfun (PT (a_reg A) (a_cache A) (free_lm A p) (qpush_last (a_qthread A) (free_entry li)) (a_qglobal A)))).
      unfold free_lm, free_entry. apply (pfun_free_push_last (a_reg A) (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A) p li).
      + apply (proj1 (wf_partition_pfun (PT _ _ _ _ _))). exact wX.
      + exact LU.
      + exact (free_uniq A m md p li AI LU).
      + exact (free_lrange A m md p li AI LU).
      + exact NE.
    - unfold free_lm. exact (wf_live_delete (a_sb A) (a_reg A) (a_livemap A) (a_sec A) p li wV LU).
    - unfold free_lm, free_entry. apply (wf_quarantine_push_lastB (a_reg A) (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A) p li wQ LU).
      + exact (wf_qentry_of_live (a_sb A) (a_reg A) (a_livemap A) (a_sec A) p li wV LU).
      + exact (free_uniq A m md p li AI LU).
      + exact NE.
      + exact ROOM.
    - unfold free_lm, free_entry. exact (wf_sec_free_push_last AL_pboth (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A) p li wS LU NE).
    - exact (free_wfD A m md key AI KEYU).
    - exact wF.
    - unfold free_lm, free_entry.
      (first [ dand3 wV as V1 _ V3 | destruct wV as (V1 & _ & V3) ]). pose proof (V1 p li LU) as (N & _). cbv zeta in N.
      apply (wf_budget_free_push_last (a_tiny A) (a_livemap A) (a_qthread A) (a_qglobal A) p li wB LU); [| exact NE].
      pose proof (as_livebytes_delete (a_livemap A) p li LU).
      pose proof (as_livebytes_nonneg (delete p (a_livemap A)) ltac:(intros u l Hu; rewrite lookup_delete_Some in Hu; destruct Hu as [_ Hu]; pose proof (V1 u l Hu) as (X & _); cbv zeta in X; lia)). lia.
    - exact wI.
    - exact wE.
    - exact wJ.
    - (* [comment removed for export] *) unfold free_lm, free_entry. exact (wf_prim_free_push_last (a_livemap A) (a_qthread A) (a_qglobal A) (a_paid A) (a_pcred A) p li wN LU NE).
  Qed.

  Local Notation ks24 := (pk_chunks (a_cache A kQuarantineBatchClass)).
  Local Notation kb := (last ks24 0).

  Theorem free_new_WFB :
    ks24 <> [] ->
    (a_qthread A = [] \/ Z.of_nat (length (ba_entries (last (a_qthread A) (BA 0 [])))) = kQuarantineBatchCount) ->
    WFB (q_bytes (a_qthread A) + kQuarantineBatchBytes + qe_bytes (free_entry li)) (freeA_new A p li key).
  Proof.
    intros NE FULL. (first [ pose proof ((c24_facts A m md AI NE)) as dR_16; dand5 dR_16 as ND IN KR RL L24 | destruct (c24_facts A m md AI NE) as (ND & IN & KR & RL & L24) ]).
    pose proof (kb_not_batch A m md AI NE) as KNB.
    destruct W as [wP wM wR wC wX wV wQ wS wD wF wB wI wE wJ wN] eqn:EW. clear EW.
    constructor.
    - exact wP.
    - exact wM.
    - exact wR.
    - change (wf_caches_ (a_reg A) (cache_set (a_cache A) kQuarantineBatchClass (removelast ks24)) (a_cache_inited A)).
      apply (wf_caches_set (a_reg A) (a_cache A) (a_cache_inited A) kQuarantineBatchClass (removelast ks24) wC ltac:(unfold kQuarantineBatchClass; lia)).
      + rewrite removelast_length'. lia.
      + exact (proj1 (removelast_nodup ks24 ND)).
      + intros k Hk. apply RL in Hk as [Hk _]. destruct wC as (C1 & _). (first [ pose proof ((C1 kQuarantineBatchClass ltac:(unfold kQuarantineBatchClass; lia))) as dR_17; dand4 dR_17 as _ _ B _ | destruct (C1 kQuarantineBatchClass ltac:(unfold kQuarantineBatchClass; lia)) as (_ & _ & B & _) ]). exact (B k Hk).
      + intros CI. destruct wC as (C1 & _). (first [ pose proof ((C1 kQuarantineBatchClass ltac:(unfold kQuarantineBatchClass; lia))) as dR_18; dand4 dR_18 as _ _ _ Z0 | destruct (C1 kQuarantineBatchClass ltac:(unfold kQuarantineBatchClass; lia)) as (_ & _ & _ & Z0) ]). cbv zeta in Z0. rewrite (Z0 CI). reflexivity.
    - change (wf_partition_T (PT (a_reg A) (nb_cache (a_cache A)) (delete p (a_livemap A)) (qpush_new (a_qthread A) kb (QE (li_chunk li) (li_n li))) (a_qglobal A))).
      apply (proj2 (wf_partition_pfun (PT _ _ _ _ _))). rewrite <- (qpush_last_emptybatch (a_qthread A) kb).
      change (a_qthread A ++ [BA kb []]) with (nb_qt (a_qthread A) kb).
      apply (pfun_free_gen (a_reg A) (nb_cache (a_cache A)) (a_livemap A) (nb_qt (a_qthread A) kb) (a_qglobal A) p li).
      + apply (pfun_newbatch (a_reg A) (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A) kb); [| exact ND| exact NE| reflexivity| exact KR].
        apply (proj1 (wf_partition_pfun (PT _ _ _ _ _))). exact wX.
      + exact LU.
      + exact (free_uniq A m md p li AI LU).
      + exact (free_lrange A m md p li AI LU).
      + apply p_quar_push_last. intros H; apply app_eq_nil in H; destruct H; discriminate.
      + apply p_batch_push_last. intros H; apply app_eq_nil in H; destruct H; discriminate.
    - exact (wf_live_delete (a_sb A) (a_reg A) (a_livemap A) (a_sec A) p li wV LU).
    - apply (wf_quarantine_push_newB (a_reg A) (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A) p li wQ LU).
      + exact (wf_qentry_of_live (a_sb A) (a_reg A) (a_livemap A) (a_sec A) p li wV LU).
      + exact (free_uniq A m md p li AI LU).
      + exact FULL.
      + exact KR.
      + exact KNB.
    - exact (wf_sec_free_push_new AL_pboth (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A) p li wS LU kb).
    - exact (free_wfD A m md key AI KEYU).
    - exact wF.
    - (first [ dand3 wV as V1 _ V3 | destruct wV as (V1 & _ & V3) ]). pose proof (V1 p li LU) as (N & _). cbv zeta in N.
      apply (wf_budget_free_push_new (a_tiny A) (a_livemap A) (a_qthread A) (a_qglobal A) p li wB LU).
      pose proof (as_livebytes_delete (a_livemap A) p li LU).
      pose proof (as_livebytes_nonneg (delete p (a_livemap A)) ltac:(intros u l Hu; rewrite lookup_delete_Some in Hu; destruct Hu as [_ Hu]; pose proof (V1 u l Hu) as (X & _); cbv zeta in X; lia)). lia.
    - exact wI.
    - exact wE.
    - exact wJ.
    - (* [comment removed for export] *) exact (wf_prim_free_push_new (a_livemap A) (a_qthread A) (a_qglobal A) (a_paid A) (a_pcred A) p li wN LU kb).
  Qed.
End WfFreeB.

Section WfXferB.
Context {Clg : Ceiling}.
  Variables (B : Z) (A : AState).
  Hypothesis W : WFB B A.
  Theorem xfer_WFB : kQuarantineCacheSize < q_bytes (a_qthread A) -> q_bytes (a_qglobal A) + q_bytes (a_qthread A) <= kQuarantineMaxSize -> WF (xferA A).
  Proof.
    intros DR SZ. destruct W as [wP wM wR wC wX wV wQ wS wD wF wB wI wE wJ wN].
    constructor; cbn [xferA a_pl a_reg a_cache_inited a_cache a_livemap a_qthread a_qglobal a_sec a_depot a_fhint a_fframes a_ia_inited a_oom a_tiny a_qlimbo a_scred a_deadsh a_pcred a_paid a_sb a_fs].
    - exact wP.
    - exact wM.
    - exact wR.
    - exact wC.
    - apply (proj2 (wf_partition_pfun (PT (a_reg A) (a_cache A) (a_livemap A) [] (qtransfer (a_qthread A) (a_qglobal A))))).
      apply (partition_same (PT (a_reg A) (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A))).
      + apply (proj1 (wf_partition_pfun (PT _ _ _ _ _))). exact wX.
      + intros c. reflexivity.
      + intros c k s Hc Hk. destruct s; cbn [pholds pt_reg pt_cache pt_lm pt_qt pt_qg]; try tauto.
        * apply p_quar_transfer.
        * apply p_batch_transfer.
    - exact wV.
    - exact (wf_quarantine_transferB B (a_reg A) (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A) wQ SZ).
    - (first [ dand5 wS as S1 S2 S3 S4 S5 | destruct wS as (S1 & S2 & S3 & S4 & S5) ]). split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|].
      intros sc Hin. destruct (S5 sc Hin) as [L|Q]; [left; exact L| right]. apply (quarantined_chunks_transfer (a_qthread A) (a_qglobal A)). exact Q.
    - exact wD.
    - exact wF.
    - (first [ dand5 wB as B1 B2 B3 B4 B5 | destruct wB as (B1 & B2 & B3 & B4 & B5) ]). split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
      rewrite (tiny_quar_transfer (a_qthread A) (a_qglobal A)). exact B5.
    - exact wI.
    - exact wE.
    - apply (wf_qcredit_transfer (a_reg A) (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A) (a_tiny A) B wQ wB wJ DR).
    - (* [comment removed for export] *)
      apply (wf_prim_qsame (a_livemap A) (a_qthread A) [] (a_qglobal A) (qtransfer (a_qthread A) (a_qglobal A)) (a_paid A) (a_pcred A)); [| exact wN].
      intros e He. cbn [app] in He. rewrite qtransfer_entries in He. rewrite q_entries_app. apply in_app_iff in He. apply in_app_iff. tauto.
  Qed.
End WfXferB.

(* [comment removed for export] *)
Lemma WF_set_ia `{Clg : Ceiling} : forall A b, WF A -> WF (set_ia A b).
Proof. intros A b W. destruct W; constructor; assumption. Qed.
