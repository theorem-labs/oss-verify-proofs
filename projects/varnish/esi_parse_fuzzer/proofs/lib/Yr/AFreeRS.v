(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState AInv ABudget.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf AQPart AQWf2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQPart.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeB2 AFreeB3 AFreeB6.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQPart OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQPart.AQWfJ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pasan).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition recA2 (A : AState) (R rest : list batch) : AState :=
  mkA (a_pl A) (a_reg A) (a_cache_inited A) (a_cache A) (a_livemap A) [] rest (a_sec A) (a_depot A)
      (a_fhint A) (a_fframes A) (a_ia_inited A) (a_oom A) (a_tiny A) R (a_scred A) (a_deadsh A) (a_pcred A) (a_paid A).

(* [comment removed for export] *)
Section CEIL0.
Context {Clg : Ceiling}.
Definition wf_batch0_ (reg : Z -> region) (sec : secreg) (b : batch) : Prop :=
  Z.of_nat (length (ba_entries b)) <= kQuarantineBatchCount /\
  0 <= ba_idx b < carved_count_ reg kQuarantineBatchClass /\
  Forall (wf_qentry_ reg sec) (ba_entries b).
Lemma wf_batch0_of : forall reg sec b, wf_batch_ reg sec b -> wf_batch0_ reg sec b.
Proof. (intros reg sec b; (first [ intro dR_39; dand3 dR_39 as H1 H2 H3 | intros (H1 & H2 & H3) ])). split; [lia|]. split; [exact H2| exact H3]. Qed.

(* [comment removed for export] *)
Record WFR (A : AState) : Prop := {
  wrP : wf_place AL_pasan (a_pl A);
  wrM : wf_bigmaps_ (a_pl A) (a_sec A);
  wrR : wf_regions_ (a_reg A) (a_paid A) (a_cache_inited A);   (* [comment removed for export] *)
  wrC : wf_caches_ (a_reg A) (a_cache A) (a_cache_inited A);
  wrX : wf_partition_ (a_reg A) (a_cache A) (a_livemap A) [] (a_qglobal A ++ a_qlimbo A);
  wrV : wf_live_ (a_sb A) (a_reg A) (a_livemap A) (a_sec A);
  wrQ : wf_quarantine_ (a_reg A) (a_livemap A) [] (a_qglobal A) (a_sec A);
  wrL : Forall (wf_batch0_ (a_reg A) (a_sec A)) (a_qlimbo A) /\
        NoDup (batch_indices_ [] (a_qglobal A ++ a_qlimbo A)) /\ NoDup (quarantined_chunks_ [] (a_qglobal A ++ a_qlimbo A)) /\
        (forall u li, a_livemap A !! u = Some li -> ~ In (li_chunk li) (quarantined_chunks_ [] (a_qglobal A ++ a_qlimbo A)));
  wrS : wf_sec_ AL_pasan (a_livemap A) [] (a_qglobal A ++ a_qlimbo A) (a_sec A);
  wrD : wf_depot_ (p_dkeys (a_pl A)) (a_depot A);
  wrF : wf_fstack_ (a_fs A) (a_fhint A) (a_fframes A);
  wrB : wf_budget_ (a_tiny A) (a_livemap A) [] (a_qglobal A ++ a_qlimbo A);
  wrT : a_qthread A = [];
  wrI : a_cache_inited A = true;
  wrE : wf_dead_ (a_scred A) (a_deadsh A) (Z.of_nat (length (sr_chunks (a_sec A))));
  wrJ : wf_qcredit_ (a_qglobal A);
  wrN : wf_prim_ (a_livemap A) [] (a_qglobal A ++ a_qlimbo A) (a_paid A) (a_pcred A) }.   (* [comment removed for export] *)
End CEIL0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Exit.
Context {Clg : Ceiling}.
  Variable A : AState.
  Hypothesis W : WFR A.
  Hypothesis L0 : a_qlimbo A = [].

  Theorem WFR_exit : WF A.
  Proof.
    destruct W as [rP rM rR rC rX rV rQ (rL1 & rL2 & rL3 & rL4) rS rD rF rB rT rI rE rJ rN].
    rewrite L0, app_nil_r in *. constructor; rewrite ?rT; try assumption.
  Qed.
End Exit.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CapR.
Context {Clg : Ceiling}.
  Variable A : AState.
  Hypothesis W : WFR A.
  Lemma wfr_fa_cap : forall c, 1 <= c <= 30 ->
    rg_mapped_fa (a_reg A c) <= 2^29 - 2^26 /\ rg_allocated_user (a_reg A c) <= kAuCap - 2^27.
  Proof.
    intros c Hc. pose proof (class_size_range c Hc) as CR. pose proof (class_slack_range c) as SL.
    destruct (wrR A W) as (WR & _ & _). destruct (WR c Hc) as (A1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & A11 & A12).
    destruct (wrN A W) as (P0 & PS & _).
    pose proof (ALogic1.paid_sum_term (a_paid A) 30 c ltac:(lia) ltac:(cbn; lia)) as T.
    assert (Q1 : rg_allocated_user (a_reg A c) / class_size c <= rg_allocated_user (a_reg A c) / 32) by (apply Z.div_le_compat_l; lia).
    assert (Q2 : 32 * (rg_allocated_user (a_reg A c) / 32) <= rg_allocated_user (a_reg A c)) by (apply Z.mul_div_le; lia).
    rewrite PRIMCRED0_eq in PS. unfold kAuCap, kUserMapSize, kFreeArrayMapSize, kMaxSize, kQuarantineMaxSize, kQuarantineCacheSize in *. nia.
  Qed.
End CapR.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Enter.
Context {Clg : Ceiling}.
  Variables (A : AState) (B : Z).
  (* [comment removed for export] *)
  Hypothesis W : WFB B A.
  Hypothesis CI : a_cache_inited A = true.
  Hypothesis DR : kQuarantineCacheSize < q_bytes (a_qthread A).
  Let qg0 := qtransfer (a_qthread A) (a_qglobal A).
  Let Rr := rsplit qg0 kQuarantineMinSize.

  Lemma qmin_range : 0 <= kQuarantineMinSize <= kQuarantineMaxSize.
  Proof. unfold kQuarantineMinSize, kQuarantineMaxSize. lia. Qed.

  Theorem WFR_enter : WFR (recA2 A (fst Rr) (snd Rr)).
  Proof.
    destruct W as [wP wM wR wC wX wV wQ wS wD wF wB wI wE wJ wN].
    pose proof (rsplit_app qg0 kQuarantineMinSize) as APP. fold Rr in APP.
    destruct Rr as [R rest] eqn:ERr. cbn [fst snd]. cbv zeta in APP.
    assert (PERM : forall e, In e (q_entries (rest ++ R)) <-> In e (q_entries (a_qthread A) ++ q_entries (a_qglobal A))).
    { intros e. unfold q_entries. rewrite !flat_map_app, !in_app_iff.
      assert (X : In e (flat_map ba_entries R) \/ In e (flat_map ba_entries rest) <-> In e (flat_map ba_entries qg0)) by (rewrite APP, flat_map_app, in_app_iff; tauto).
      subst qg0. unfold qtransfer in X. rewrite flat_map_app, in_app_iff in X. tauto. }
    assert (PERM2 : forall e, In e (q_entries (rest ++ R)) <-> In e (q_entries (a_qthread A ++ a_qglobal A))).
    { intros e. rewrite (PERM e). unfold q_entries. rewrite flat_map_app. tauto. }
    assert (PERMi : forall i, In i (batch_indices_ [] (rest ++ R)) <-> In i (batch_indices_ (a_qthread A) (a_qglobal A))).
    { intros i. unfold batch_indices_. cbn [app]. rewrite !map_app, !in_app_iff.
      assert (X : In i (map ba_idx R) \/ In i (map ba_idx rest) <-> In i (map ba_idx qg0)) by (rewrite APP, map_app, in_app_iff; tauto).
      subst qg0. unfold qtransfer in X. rewrite map_app, in_app_iff in X. tauto. }
    assert (PERMc : forall ch, In ch (quarantined_chunks_ [] (rest ++ R)) <-> In ch (quarantined_chunks_ (a_qthread A) (a_qglobal A))).
    { intros ch. rewrite !quarantined_chunks_def, q_entries_nil. cbn [app]. rewrite !in_map_iff.
      split; ((first [ intro dR_40; dex1 dR_40 as e; destruct dR_40 as [E He] | intro dR_40; dand3 dR_40 as e E He | intros (e & E & He) ])); exists e; split; [exact E| apply PERM; exact He| exact E| apply PERM; exact He]. }
    (first [ dand8 wQ as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 | destruct wQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8) ]).
    assert (WQ0 : Forall (wf_batch_ (a_reg A) (a_sec A)) qg0 /\ NoDup (batch_indices_ [] qg0) /\ NoDup (quarantined_chunks_ [] qg0) /\
                  (forall u li, a_livemap A !! u = Some li -> ~ In (li_chunk li) (quarantined_chunks_ [] qg0))).
    { assert (E6 : batch_indices_ [] qg0 = map ba_idx (a_qglobal A) ++ map ba_idx (a_qthread A)).
      { rewrite batch_indices_def. subst qg0. unfold qtransfer. cbn [app]. rewrite map_app. reflexivity. }
      assert (E7 : quarantined_chunks_ [] qg0 = map qe_chunk (q_entries (a_qglobal A)) ++ map qe_chunk (q_entries (a_qthread A))).
      { rewrite quarantined_chunks_def, q_entries_nil. subst qg0. unfold qtransfer, q_entries. cbn [app]. rewrite flat_map_app, map_app. reflexivity. }
      split; [subst qg0; unfold qtransfer; apply Forall_app; split; assumption|].
      split; [rewrite E6; apply NoDup_app_comm; rewrite <- map_app; rewrite batch_indices_def in Q6; exact Q6|].
      split; [rewrite E7; apply NoDup_app_comm; rewrite <- map_app; rewrite quarantined_chunks_def in Q7; exact Q7|].
      intros u li Hu X. apply (Q8 u li Hu). apply (quarantined_chunks_transfer (a_qthread A) (a_qglobal A)). exact X. }
    (first [ dand4 WQ0 as W01 W06 W07 W08 | destruct WQ0 as (W01 & W06 & W07 & W08) ]).
    pose proof (wf_quarantine_rsplit (a_reg A) (a_livemap A) qg0 (a_sec A) kQuarantineMinSize W01 W06 W07 W08 qmin_range) as WQr.
    pose proof (rsplit_R_wf (a_reg A) (a_livemap A) qg0 (a_sec A) kQuarantineMinSize W01 W06 W07 W08 qmin_range) as WRr.
    fold Rr in WQr, WRr. rewrite ERr in WQr, WRr. cbv zeta in WQr, WRr. (first [ dand4 WRr as R1 R2 R3 R4 | destruct WRr as (R1 & R2 & R3 & R4) ]).
    (* [comment removed for export] *)
    assert (ND1 : NoDup (batch_indices_ [] (rest ++ R))) by (unfold batch_indices_; cbn [app]; rewrite map_app; apply NoDup_app_comm; exact R2).
    assert (ND2 : NoDup (quarantined_chunks_ [] (rest ++ R))).
    { rewrite quarantined_chunks_def, q_entries_nil. cbn [app]. unfold q_entries in R3 |- *. rewrite flat_map_app, map_app. apply NoDup_app_comm. exact R3. }
    constructor; cbn [recA2 a_pl a_reg a_cache_inited a_cache a_livemap a_qthread a_qglobal a_sec a_depot a_fhint a_fframes a_ia_inited a_oom a_tiny a_qlimbo a_scred a_deadsh a_pcred a_paid a_sb a_fs].
    - exact wP.
    - exact wM.
    - exact wR.
    - exact wC.
    - apply (proj2 (wf_partition_pfun (PT (a_reg A) (a_cache A) (a_livemap A) [] (rest ++ R)))).
      apply (partition_same (PT (a_reg A) (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A))).
      + apply (proj1 (wf_partition_pfun (PT _ _ _ _ _))). exact wX.
      + intros c. reflexivity.
      + intros c k s Hc Hk. destruct s; cbn [pholds pt_reg pt_cache pt_lm pt_qt pt_qg]; try tauto.
        * unfold p_quar_. cbn [app]. split; intros [n Hn]; exists n; apply PERM2; exact Hn.
        * unfold p_batch_. rewrite PERMi. tauto.
    - exact wV.
    - exact WQr.
    - split; [eapply Forall_impl; [| exact R1]; intros b Hb; exact (wf_batch0_of _ _ _ Hb)|].
      split; [exact ND1|]. split; [exact ND2|]. intros u li Hu X. apply (Q8 u li Hu). apply PERMc. exact X.
    - (first [ dand5 wS as S1 S2 S3 S4 S5 | destruct wS as (S1 & S2 & S3 & S4 & S5) ]). split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|].
      intros sc Hin. destruct (S5 sc Hin) as [L|Q]; [left; exact L| right]. apply PERMc. exact Q.
    - exact wD.
    - exact wF.
    - (first [ dand5 wB as B1 B2 B3 B4 B5 | destruct wB as (B1 & B2 & B3 & B4 & B5) ]). split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
      assert (TQ : tiny_quar_ [] (rest ++ R) = tiny_quar_ (a_qthread A) (a_qglobal A)); [| rewrite TQ; exact B5].
      rewrite <- (tiny_quar_transfer (a_qthread A) (a_qglobal A)). unfold tiny_quar_. cbn [app]. fold qg0. rewrite APP.
      unfold q_entries. rewrite !flat_map_app, !filter_app', !length_app. lia.
    - reflexivity.
    - exact CI.
    - exact wE.
    - pose proof (wf_qcredit_transfer (a_reg A) (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A) (a_tiny A) B
                    (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 (conj Q7 Q8))))))) wB wJ DR) as J0.
      fold qg0 in J0.
      pose proof (wf_qcredit_rsplit qg0 J0 kQuarantineMinSize ltac:(unfold kQuarantineMinSize; lia)) as JR. cbv zeta in JR.
      fold Rr in JR. rewrite ERr in JR. exact JR.
    - (* [comment removed for export] *)
      (first [ dand3 wN as N0 NS ND | destruct wN as (N0 & NS & ND) ]). split; [exact N0|]. split; [exact NS|].
      intros c k Hc [V|[n Hn]]; apply (ND c k Hc); [left; exact V| right]. exists n. apply PERM2. exact Hn.
  Qed.
End Enter.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RegC.
Context {Clg : Ceiling}.
  Variables (reg reg' : Z -> region) (sec : secreg).
  Hypothesis CC : forall c, carved_count_ reg' c = carved_count_ reg c.
  Lemma wf_qentry_regC : forall e, wf_qentry_ reg sec e -> wf_qentry_ reg' sec e.
  Proof. intros e H. unfold wf_qentry_ in *. destruct (qe_chunk e) as [[c k]|[mb n0]]; rewrite ?CC; exact H. Qed.
  Lemma wf_batch_regC : forall b, wf_batch_ reg sec b -> wf_batch_ reg' sec b.
  Proof. (intros b; (first [ intro dR_41; dand3 dR_41 as H1 H2 H3 | intros (H1 & H2 & H3) ])). split; [exact H1|]. split; [rewrite CC; exact H2|]. eapply Forall_impl; [| exact H3]. apply wf_qentry_regC. Qed.
  Lemma wf_batch0_regC : forall b, wf_batch0_ reg sec b -> wf_batch0_ reg' sec b.
  Proof. (intros b; (first [ intro dR_42; dand3 dR_42 as H1 H2 H3 | intros (H1 & H2 & H3) ])). split; [exact H1|]. split; [rewrite CC; exact H2|]. eapply Forall_impl; [| exact H3]. apply wf_qentry_regC. Qed.
  Lemma wf_live_regC : forall sb lm, wf_live_ sb reg lm sec -> wf_live_ sb reg' lm sec.
  Proof.
    (intros sb lm; (first [ intro dR_43; dand3 dR_43 as V1 V2 V3 | intros (V1 & V2 & V3) ])). split; [| exact (conj V2 V3)]. intros u li Hu. pose proof (V1 u li Hu) as X. cbv zeta in *.
    destruct (li_chunk li) as [[c k]|[mb n0]]; rewrite ?CC; exact X.
  Qed.
  Lemma wf_quarantine_regC : forall lm qt qg, wf_quarantine_ reg lm qt qg sec -> wf_quarantine_ reg' lm qt qg sec.
  Proof.
    (intros lm qt qg; (first [ intro dR_44; dand3 dR_44 as Q1 Q2 Q3 | intros (Q1 & Q2 & Q3) ])). split; [eapply Forall_impl; [| exact Q1]; apply wf_batch_regC|].
    split; [eapply Forall_impl; [| exact Q2]; apply wf_batch_regC| exact Q3].
  Qed.
End RegC.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section PfunRecp.
  Variables (reg : Z -> region) (cache : Z -> pcache) (lm : gmap Z liveinfo) (qg qg' : list batch) (c k fa' : Z).
  Let ks := pk_chunks (cache c).
  Let pr := cache_push_list ks (max_count c) k.
  Let T := PT reg cache lm [] qg.
  Let T' := PT (recp_reg reg cache c k fa') (recp_cache cache c k) lm [] qg'.
  Hypothesis P : pfun T.
  Hypothesis Hc : 1 <= c <= 30.
  Hypothesis Hk : 0 <= k < carved_count_ reg c.
  Hypothesis Q0 : p_quar_ [] qg c k.
  Hypothesis ND : NoDup ks.
  Hypothesis RG : forall x, In x ks -> 0 <= x < carved_count_ reg c.
  (* [comment removed for export] *)
  Hypothesis HQ : forall c' k', p_quar_ [] qg' c' k' <-> (p_quar_ [] qg c' k' /\ (c', k') <> (c, k)).
  Hypothesis HB : forall c' k', p_batch_ [] qg' c' k' <-> p_batch_ [] qg c' k'.

  Lemma NKs : ~ In k ks.
  Proof. intros H. destruct (P c k Hc Hk) as [_ U]. discriminate (U PQ PC Q0 ltac:(cbn [pholds pt_cache]; exact H)). Qed.
  Lemma NFk : ~ p_free_ reg c k.
  Proof. intros H. destruct (P c k Hc Hk) as [_ U]. discriminate (U PQ PF Q0 ltac:(cbn [pholds pt_reg]; exact H)). Qed.
  Lemma CFk : forall x, In x ks -> ~ In x (rg_free (reg c)).
  Proof.
    intros x Hx Hf. destruct (P c x Hc (RG x Hx)) as [_ U].
    discriminate (U PC PF ltac:(cbn [pholds pt_cache]; exact Hx) ltac:(cbn [pholds pt_reg]; exact Hf)).
  Qed.
  Lemma snd_in_ks : forall x, In x (snd pr) -> In x ks.
  Proof.
    intros x H. subst pr. unfold cache_push_list in H. destruct (Z.of_nat (length ks) =? max_count c); cbn [snd] in H; [| destruct H].
    apply (drain_in_iff ks (Z.to_nat (max_count c / 2))). right. exact H.
  Qed.
  Lemma k_in_fst : In k (fst pr).
  Proof. subst pr. unfold cache_push_list. destruct (Z.of_nat (length ks) =? max_count c); cbn [fst]; apply in_or_app; right; left; reflexivity. Qed.

  Theorem pfun_recp : pfun T'.
  Proof.
    pose proof NKs as NK. pose proof NFk as NF.
    pose proof (recp_in cache c k) as RI. pose proof (recp_disjoint cache c k ND NK) as DJ. fold ks pr in RI, DJ.
    intros c0 k0 Hc0 Hk0. cbn [pt_reg T'] in Hk0. rewrite recp_carved in Hk0.
    destruct (P c0 k0 Hc0 Hk0) as [[s0 Hs0] U].
    (* [comment removed for export] *)
    assert (CH : forall s, pholds T' c0 k0 s <->
              match s with
              | PF => pholds T c0 k0 PF \/ (c0 = c /\ In k0 (snd pr))
              | PC => (c0 = c /\ In k0 (fst pr)) \/ (c0 <> c /\ pholds T c0 k0 PC)
              | PV => pholds T c0 k0 PV
              | PQ => pholds T c0 k0 PQ /\ (c0, k0) <> (c, k)
              | PB => pholds T c0 k0 PB
              end).
    { intros s. destruct s; cbn [pholds T T' pt_reg pt_cache pt_lm pt_qt pt_qg].
      - apply p_free_recp.
      - apply p_cached_recp.
      - tauto.
      - apply HQ.
      - apply HB. }
    (* [comment removed for export] *)
    assert (TK : c0 = c -> k0 = k -> forall s, pholds T c0 k0 s -> s = PQ).
    { intros -> -> s Hs. exact (U s PQ Hs Q0). }
    split.
    - (* [comment removed for export] *)
      destruct (Z.eq_dec c0 c) as [->|NC].
      + destruct (Z.eq_dec k0 k) as [->|NKK].
        * exists PC. apply CH. left. split; [reflexivity| exact k_in_fst].
        * destruct s0.
          -- exists PF. apply CH. left. exact Hs0.
          -- cbn [pholds T pt_cache] in Hs0. destruct (in_dec Z.eq_dec k0 (snd pr)) as [I|NI].
             ++ exists PF. apply CH. right. split; [reflexivity| exact I].
             ++ exists PC. apply CH. left. split; [reflexivity|]. destruct (proj2 (RI k0) (or_introl Hs0)) as [H|H]; [exact H| exfalso; exact (NI H)].
          -- exists PV. apply CH. exact Hs0.
          -- exists PQ. apply CH. split; [exact Hs0| congruence].
          -- exists PB. apply CH. exact Hs0.
      + exists s0. apply CH. destruct s0; try tauto. split; [exact Hs0| congruence].
    - (* [comment removed for export] *)
      intros s1 s2 H1 H2. apply CH in H1. apply CH in H2. clear CH Hs0.
      assert (SND : In k0 (snd pr) -> c0 = c -> pholds T c0 k0 PC) by (intros I ->; cbn [pholds T pt_cache]; exact (snd_in_ks k0 I)).
      assert (FST : In k0 (fst pr) -> c0 = c -> k0 = k \/ pholds T c0 k0 PC).
      { intros I ->. destruct (proj1 (RI k0) (or_introl I)) as [H| ->]; [right; cbn [pholds T pt_cache]; exact H| left; reflexivity]. }
      clear RI HQ HB P Q0 ND RG NK NF Hk0 Hc0.
      destruct s1, s2; try reflexivity; exfalso; decompose [and or] H1; decompose [and or] H2.
      all: try match goal with H : In ?x (fst pr), E : ?y = c |- _ => destruct (FST H E) as [?|?] end.
      all: try match goal with H : In ?x (snd pr), E : ?y = c |- _ => pose proof (SND H E) end.
      all: try match goal with Ha : pholds T ?x ?y ?a, Hb : pholds T ?x ?y ?b |- _ =>
                  first [ discriminate (U _ _ Ha Hb) ] end.
      all: try match goal with E1 : ?y = c, E2 : ?x = k, Ha : pholds T _ _ ?a |- _ => discriminate (TK E1 E2 _ Ha) end.
      all: try match goal with Ha : In ?x (fst pr), Hb : In ?x (snd pr) |- _ => exact (DJ _ Ha Hb) end.
      all: try match goal with E1 : ?y = c, N : ?y <> c |- _ => exact (N E1) end.
      all: try match goal with E1 : ?y = c, E2 : ?x = k, N : (?y, ?x) <> (c, k) |- _ => apply N; rewrite E1, E2; reflexivity end.
  Qed.
End PfunRecp.

(* [comment removed for export] *)
Section PfunRecpB.
  Variables (reg : Z -> region) (cache : Z -> pcache) (lm : gmap Z liveinfo) (qg qg' : list batch) (c k fa' : Z).
  Let ks := pk_chunks (cache c).
  Let pr := cache_push_list ks (max_count c) k.
  Let T := PT reg cache lm [] qg.
  Let T' := PT (recp_reg reg cache c k fa') (recp_cache cache c k) lm [] qg'.
  Hypothesis P : pfun T.
  Hypothesis Hc : 1 <= c <= 30.
  Hypothesis Hk : 0 <= k < carved_count_ reg c.
  Hypothesis Q0 : p_batch_ [] qg c k.
  Hypothesis ND : NoDup ks.
  Hypothesis RG : forall x, In x ks -> 0 <= x < carved_count_ reg c.
  (* [comment removed for export] *)
  Hypothesis HQ : forall c' k', p_quar_ [] qg' c' k' <-> p_quar_ [] qg c' k'.
  Hypothesis HB : forall c' k', p_batch_ [] qg' c' k' <-> (p_batch_ [] qg c' k' /\ (c', k') <> (c, k)).

  Lemma NKsB : ~ In k ks.
  Proof. intros H. destruct (P c k Hc Hk) as [_ U]. discriminate (U PB PC Q0 ltac:(cbn [pholds pt_cache]; exact H)). Qed.
  Lemma NFkB : ~ p_free_ reg c k.
  Proof. intros H. destruct (P c k Hc Hk) as [_ U]. discriminate (U PB PF Q0 ltac:(cbn [pholds pt_reg]; exact H)). Qed.
  Lemma CFkB : forall x, In x ks -> ~ In x (rg_free (reg c)).
  Proof.
    intros x Hx Hf. destruct (P c x Hc (RG x Hx)) as [_ U].
    discriminate (U PC PF ltac:(cbn [pholds pt_cache]; exact Hx) ltac:(cbn [pholds pt_reg]; exact Hf)).
  Qed.
  Lemma snd_in_ksB : forall x, In x (snd pr) -> In x ks.
  Proof.
    intros x H. subst pr. unfold cache_push_list in H. destruct (Z.of_nat (length ks) =? max_count c); cbn [snd] in H; [| destruct H].
    apply (drain_in_iff ks (Z.to_nat (max_count c / 2))). right. exact H.
  Qed.
  Lemma k_in_fstB : In k (fst pr).
  Proof. subst pr. unfold cache_push_list. destruct (Z.of_nat (length ks) =? max_count c); cbn [fst]; apply in_or_app; right; left; reflexivity. Qed.

  Theorem pfun_recpB : pfun T'.
  Proof.
    pose proof NKsB as NK. pose proof NFkB as NF.
    pose proof (recp_in cache c k) as RI. pose proof (recp_disjoint cache c k ND NK) as DJ. fold ks pr in RI, DJ.
    intros c0 k0 Hc0 Hk0. cbn [pt_reg T'] in Hk0. rewrite recp_carved in Hk0.
    destruct (P c0 k0 Hc0 Hk0) as [[s0 Hs0] U].
    (* [comment removed for export] *)
    assert (CH : forall s, pholds T' c0 k0 s <->
              match s with
              | PF => pholds T c0 k0 PF \/ (c0 = c /\ In k0 (snd pr))
              | PC => (c0 = c /\ In k0 (fst pr)) \/ (c0 <> c /\ pholds T c0 k0 PC)
              | PV => pholds T c0 k0 PV
              | PQ => pholds T c0 k0 PQ
              | PB => pholds T c0 k0 PB /\ (c0, k0) <> (c, k)
              end).
    { intros s. destruct s; cbn [pholds T T' pt_reg pt_cache pt_lm pt_qt pt_qg].
      - apply p_free_recp.
      - apply p_cached_recp.
      - tauto.
      - apply HQ.
      - apply HB. }
    (* [comment removed for export] *)
    assert (TK : c0 = c -> k0 = k -> forall s, pholds T c0 k0 s -> s = PB).
    { intros -> -> s Hs. exact (U s PB Hs Q0). }
    split.
    - (* [comment removed for export] *)
      destruct (Z.eq_dec c0 c) as [->|NC].
      + destruct (Z.eq_dec k0 k) as [->|NKK].
        * exists PC. apply CH. left. split; [reflexivity| exact k_in_fstB].
        * destruct s0.
          -- exists PF. apply CH. left. exact Hs0.
          -- cbn [pholds T pt_cache] in Hs0. destruct (in_dec Z.eq_dec k0 (snd pr)) as [I|NI].
             ++ exists PF. apply CH. right. split; [reflexivity| exact I].
             ++ exists PC. apply CH. left. split; [reflexivity|]. destruct (proj2 (RI k0) (or_introl Hs0)) as [H|H]; [exact H| exfalso; exact (NI H)].
          -- exists PV. apply CH. exact Hs0.
          -- exists PQ. apply CH. exact Hs0.
          -- exists PB. apply CH. split; [exact Hs0| congruence].
      + exists s0. apply CH. destruct s0; try tauto. split; [exact Hs0| congruence].
    - (* [comment removed for export] *)
      intros s1 s2 H1 H2. apply CH in H1. apply CH in H2. clear CH Hs0.
      assert (SND : In k0 (snd pr) -> c0 = c -> pholds T c0 k0 PC) by (intros I ->; cbn [pholds T pt_cache]; exact (snd_in_ksB k0 I)).
      assert (FST : In k0 (fst pr) -> c0 = c -> k0 = k \/ pholds T c0 k0 PC).
      { intros I ->. destruct (proj1 (RI k0) (or_introl I)) as [H| ->]; [right; cbn [pholds T pt_cache]; exact H| left; reflexivity]. }
      clear RI HQ HB P Q0 ND RG NK NF Hk0 Hc0.
      destruct s1, s2; try reflexivity; exfalso; decompose [and or] H1; decompose [and or] H2.
      all: try match goal with H : In ?x (fst pr), E : ?y = c |- _ => destruct (FST H E) as [?|?] end.
      all: try match goal with H : In ?x (snd pr), E : ?y = c |- _ => pose proof (SND H E) end.
      all: try match goal with Ha : pholds T ?x ?y ?a, Hb : pholds T ?x ?y ?b |- _ =>
                  first [ discriminate (U _ _ Ha Hb) ] end.
      all: try match goal with E1 : ?y = c, E2 : ?x = k, Ha : pholds T _ _ ?a |- _ => discriminate (TK E1 E2 _ Ha) end.
      all: try match goal with Ha : In ?x (fst pr), Hb : In ?x (snd pr) |- _ => exact (DJ _ Ha Hb) end.
      all: try match goal with E1 : ?y = c, N : ?y <> c |- _ => exact (N E1) end.
      all: try match goal with E1 : ?y = c, E2 : ?x = k, N : (?y, ?x) <> (c, k) |- _ => apply N; rewrite E1, E2; reflexivity end.
  Qed.
End PfunRecpB.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Shed.
  Variables (rest more : list batch) (kb : Z) (e0 : qentry) (es : list qentry).
  Let qg := rest ++ (BA kb (e0 :: es) :: more).
  Let qg' := rest ++ (BA kb es :: more).

  Lemma shed_entries : forall x, In x (q_entries qg) <-> x = e0 \/ In x (q_entries qg').
  Proof.
    intros x. subst qg qg'. unfold q_entries. rewrite !flat_map_app. cbn [flat_map ba_entries app]. rewrite !in_app_iff. cbn [In].
    rewrite !in_app_iff. split; intros H; decompose [or] H; auto 6.
  Qed.
  Lemma shed_indices : batch_indices_ [] qg' = batch_indices_ [] qg.
  Proof. subst qg qg'. rewrite !batch_indices_def. cbn [app]. rewrite !map_app. reflexivity. Qed.
  Lemma shed_chunks_eq : exists L1 L2, quarantined_chunks_ [] qg = L1 ++ qe_chunk e0 :: L2 /\ quarantined_chunks_ [] qg' = L1 ++ L2.
  Proof.
    exists (map qe_chunk (q_entries rest)), (map qe_chunk (es ++ q_entries more)).
    rewrite !quarantined_chunks_def, !q_entries_nil. cbn [app]. subst qg qg'. unfold q_entries.
    rewrite !flat_map_app. cbn [flat_map]. rewrite !map_app. cbn [map app]. rewrite ?map_app. split; reflexivity.
  Qed.
  Lemma NoDup_del_mid : forall {X} (l1 l2 : list X) (x : X), NoDup (l1 ++ x :: l2) -> NoDup (l1 ++ l2) /\ ~ In x (l1 ++ l2).
  Proof.
    intros X l1 l2 x ND. apply NoDup_app_comm in ND. cbn [app] in ND. apply list.NoDup_cons in ND. destruct ND as [NI ND].
    split; [apply NoDup_app_comm; exact ND|]. intros H. apply NI. apply list_elem_of_In. rewrite in_app_iff in H |- *. tauto.
  Qed.
  Lemma shed_chunks : forall ch, In ch (quarantined_chunks_ [] qg) <-> ch = qe_chunk e0 \/ In ch (quarantined_chunks_ [] qg').
  Proof.
    intros ch. (first [ dand4 shed_chunks_eq as L1 L2 -> -> | destruct shed_chunks_eq as (L1 & L2 & -> & ->) ]). rewrite !in_app_iff. cbn [In]. split; intros H; decompose [or] H; auto.
  Qed.
  Lemma shed_nodup : NoDup (quarantined_chunks_ [] qg) -> NoDup (quarantined_chunks_ [] qg') /\ ~ In (qe_chunk e0) (quarantined_chunks_ [] qg').
  Proof. intros ND. (first [ dand4 shed_chunks_eq as L1 L2 E1 -> | destruct shed_chunks_eq as (L1 & L2 & E1 & ->) ]). rewrite E1 in ND. exact (NoDup_del_mid L1 L2 _ ND). Qed.
  Lemma shed_tiny : tiny_quar_ [] qg' <= tiny_quar_ [] qg.
  Proof.
    assert (E : forall l, tiny_quar_ [] l = ntiny (q_entries l)) by (intros l; rewrite tiny_quar_def, q_entries_nil; reflexivity).
    rewrite !E. subst qg qg'. unfold q_entries. rewrite !flat_map_app. cbn [flat_map ba_entries]. rewrite !ntiny_app, ntiny_cons.
    destruct (qe_n e0 <? 16); lia.
  Qed.
  (* [comment removed for export] *)
End Shed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Prim.
Context {Clg : Ceiling}.
  Variables (A : AState) (kb c k n fa' : Z) (es : list qentry) (more : list batch).
  Hypothesis W : WFR A.
  Hypothesis L : a_qlimbo A = BA kb (QE (ChP (CP c k)) n :: es) :: more.
  (* [comment removed for export] *)
  Hypothesis FA : Z.of_nat (length (pk_chunks (a_cache A c))) = max_count c ->
    4 * (Z.of_nat (length (rg_free (a_reg A c))) + max_count c / 2) <= fa' /\ rg_mapped_fa (a_reg A c) <= fa' /\
    fa' <= kFreeArraySize /\ fa' mod kFreeArrayMapSize = 0 /\
    fa' <= 4 * (rg_allocated_user (a_reg A c) / class_size c) + kFreeArrayMapSize (* [comment removed for export] *) /\ (rg_mapped_user (a_reg A c) = 0 -> False).

  Definition recpA : AState :=
    mkA (a_pl A) (recp_reg (a_reg A) (a_cache A) c k fa') (a_cache_inited A) (recp_cache (a_cache A) c k) (a_livemap A)
        [] (a_qglobal A) (a_sec A) (a_depot A) (a_fhint A) (a_fframes A) (a_ia_inited A) (a_oom A) (a_tiny A)
        (BA kb es :: more) (a_scred A) (a_deadsh A) (a_pcred A) (a_paid A).

  Let qg := a_qglobal A ++ (BA kb (QE (ChP (CP c k)) n :: es) :: more).
  Let qg' := a_qglobal A ++ (BA kb es :: more).

  Theorem WFR_prim : WFR recpA.
  Proof.
    destruct W as [rP rM rR rC rX rV rQ (rL1 & rL2 & rL3 & rL4) rS rD rF rB rT rI rE rJ rN]. rewrite L in *.
    pose proof (recp_carved (a_reg A) (a_cache A) c k fa') as CC.
    (* [comment removed for export] *)
    pose proof (Forall_inv rL1) as HB0. (first [ dand3 HB0 as HB1 HB2 HB3 | destruct HB0 as (HB1 & HB2 & HB3) ]). cbn [ba_entries ba_idx] in HB1, HB2, HB3.
    pose proof (Forall_inv HB3) as WE. unfold wf_qentry_ in WE. cbn [qe_n qe_chunk] in WE. (first [ dand4 WE as NR NP EC HK | destruct WE as (NR & NP & EC & HK) ]).
    assert (HC : 1 <= c <= 30) by (rewrite EC; apply class_of_range; lia).
    (first [ pose proof ((max_count_range c HC)) as dR_10; dand3 dR_10 as MC MCE _ | pose proof (max_count_range c HC) as (MC & MCE & _) ]).
    assert (MC2 : 2 <= max_count c /\ max_count c mod 2 = 0) by (split; [lia| rewrite MCE, Z.mul_comm, Z.mod_mul; [reflexivity| lia]]).
    assert (P0 : pfun (PT (a_reg A) (a_cache A) (a_livemap A) [] qg)) by (apply (proj1 (wf_partition_pfun (PT _ _ _ _ _))); exact rX).
    assert (Q0 : p_quar_ [] qg c k) by (exists n; cbn [app]; subst qg; unfold q_entries; rewrite flat_map_app, in_app_iff; right; left; reflexivity).
    (first [ dand3 rC as C1 C31 C0 | destruct rC as (C1 & C31 & C0) ]). (first [ pose proof ((C1 c ltac:(lia))) as dR_12; dand4 dR_12 as CL CND CRG _ | pose proof (C1 c ltac:(lia)) as (CL & CND & CRG & _) ]). cbv zeta in CL, CND, CRG.
    assert (NK : ~ In k (pk_chunks (a_cache A c))) by (exact (NKs (a_reg A) (a_cache A) (a_livemap A) qg c k P0 HC HK Q0)).
    assert (CF : forall x, In x (pk_chunks (a_cache A c)) -> ~ In x (rg_free (a_reg A c))) by (exact (CFk (a_reg A) (a_cache A) (a_livemap A) qg c P0 HC CRG)).
    pose proof (conj C1 (conj C31 C0)) as WC. rewrite rI in WC.
    (first [ dand3 rR as R1 R2 R3 | destruct rR as (R1 & R2 & R3) ]).
    pose proof (wf_caches_recp (a_reg A) (a_cache A) c k fa' WC HC HK NK MC2 FA) as WC'.
    pose proof (wf_region_recp (a_reg A) (a_cache A) c k fa' _ WC (R1 c HC) HC HK CF MC2 FA) as WR'.
    (* [comment removed for export] *)
    pose proof (shed_entries (a_qglobal A) more kb (QE (ChP (CP c k)) n) es) as SE. pose proof (shed_indices (a_qglobal A) more kb (QE (ChP (CP c k)) n) es) as SI.
    pose proof (shed_chunks (a_qglobal A) more kb (QE (ChP (CP c k)) n) es) as SC. cbn [qe_chunk] in SC.
    destruct (shed_nodup (a_qglobal A) more kb (QE (ChP (CP c k)) n) es rL3) as [ND' NIN]. cbn [qe_chunk] in NIN.
    pose proof (shed_tiny (a_qglobal A) more kb (QE (ChP (CP c k)) n) es) as ST. fold qg qg' in SE, SI, SC, ND', NIN, ST.
    constructor; cbn [recpA a_pl a_reg a_cache_inited a_cache a_livemap a_qthread a_qglobal a_sec a_depot a_fhint a_fframes a_ia_inited a_oom a_tiny a_qlimbo a_scred a_deadsh a_pcred a_paid a_sb a_fs];
      fold qg'.
    - exact rP.
    - exact rM.
    - split; [| split; [| intros _; exact rI]].
      + intros c' Hc'. unfold recp_reg. destruct (Z.of_nat (length (pk_chunks (a_cache A c))) =? max_count c) eqn:E; [| exact (R1 c' Hc')].
        unfold reg_set. destruct (Z.eqb_spec c' c) as [->|NE]; [| exact (R1 c' Hc')].
        unfold recp_reg in WR'. rewrite E in WR'. unfold reg_set in WR'. rewrite Z.eqb_refl in WR'. exact WR'.
      + intros c' Hc'. unfold recp_reg. destruct (Z.of_nat (length (pk_chunks (a_cache A c))) =? max_count c); [| exact (R2 c' Hc')].
        unfold reg_set. destruct (Z.eqb_spec c' c) as [->|NE]; [exfalso; exact (Hc' HC)| exact (R2 c' Hc')].
    - rewrite rI. exact WC'.
    - apply (proj2 (wf_partition_pfun (PT _ _ _ _ _))).
      apply (pfun_recp (a_reg A) (a_cache A) (a_livemap A) qg qg' c k fa' P0 HC HK Q0 CND).
      + intros c' k'. unfold p_quar_. cbn [app]. split.
        * intros [n' Hn']. split; [exists n'; apply SE; right; exact Hn'|].
          intros E. injection E as -> ->. apply NIN. rewrite quarantined_chunks_def, q_entries_nil. cbn [app]. apply in_map_iff. exists (QE (ChP (CP c k)) n'). split; [reflexivity| exact Hn'].
        * intros [[n' Hn'] NE]. exists n'. apply SE in Hn'. destruct Hn' as [E|Hn']; [exfalso; injection E as -> -> ->; exact (NE eq_refl)| exact Hn'].
      + intros c' k'. unfold p_batch_. rewrite SI. tauto.
    - apply (wf_live_regC (a_reg A)); [exact CC| exact rV].
    - apply (wf_quarantine_regC (a_reg A)); [exact CC| exact rQ].
    - split; [| split; [rewrite SI; exact rL2| split; [exact ND'|]]].
      + constructor; [| eapply Forall_impl; [| exact (Forall_inv_tail rL1)]; intros b Hb; exact (wf_batch0_regC _ _ _ CC b Hb)].
        apply (wf_batch0_regC (a_reg A)); [exact CC|]. split; [cbn [ba_entries]; cbn [length] in HB1; lia|]. split; [exact HB2| exact (Forall_inv_tail HB3)].
      + intros u li Hu X. apply (rL4 u li Hu). apply SC. right. exact X.
    - (first [ dand5 rS as S1 S2 S3 S4 S5 | destruct rS as (S1 & S2 & S3 & S4 & S5) ]). split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|].
      intros sc Hin. destruct (S5 sc Hin) as [LV|Q]; [left; exact LV| right]. apply SC in Q. destruct Q as [E|Q]; [discriminate E| exact Q].
    - exact rD.
    - exact rF.
    - (first [ dand5 rB as B1 B2 B3 B4 B5 | destruct rB as (B1 & B2 & B3 & B4 & B5) ]). split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. clear -B5 ST. subst qg qg'. lia.
    - reflexivity.
    - exact rI.
    - exact rE.
    - exact rJ.
    - (* [comment removed for export] *)
      (first [ dand3 rN as N0 NS ND | destruct rN as (N0 & NS & ND) ]). split; [exact N0|]. split; [exact NS|].
      intros c' k' Hc' [V|[n' Hn']]; apply (ND c' k' Hc'); [left; exact V| right]. exists n'. cbn [app]. apply SE. right. exact Hn'.
  Qed.
End Prim.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Drop.
  Variables (rest more : list batch) (kb : Z).
  Let qg := rest ++ (BA kb [] :: more).
  Let qg' := rest ++ more.

  Lemma drop_entries : q_entries qg' = q_entries qg.
  Proof. subst qg qg'. unfold q_entries. rewrite !flat_map_app. cbn [flat_map ba_entries app]. reflexivity. Qed.
  Lemma drop_chunks : quarantined_chunks_ [] qg' = quarantined_chunks_ [] qg.
  Proof. rewrite !quarantined_chunks_def, drop_entries. reflexivity. Qed.
  Lemma drop_tiny : tiny_quar_ [] qg' = tiny_quar_ [] qg.
  Proof. rewrite !tiny_quar_def, drop_entries. reflexivity. Qed.
  Lemma drop_indices_eq : exists L1 L2, batch_indices_ [] qg = L1 ++ kb :: L2 /\ batch_indices_ [] qg' = L1 ++ L2.
  Proof. exists (map ba_idx rest), (map ba_idx more). rewrite !batch_indices_def. cbn [app]. subst qg qg'. rewrite !map_app. cbn [map ba_idx]. split; reflexivity. Qed.
  Lemma drop_indices : forall i, In i (batch_indices_ [] qg) <-> i = kb \/ In i (batch_indices_ [] qg').
  Proof. intros i. (first [ dand4 drop_indices_eq as L1 L2 -> -> | destruct drop_indices_eq as (L1 & L2 & -> & ->) ]). rewrite !in_app_iff. cbn [In]. split; intros H; decompose [or] H; auto. Qed.
  Lemma drop_nodup : NoDup (batch_indices_ [] qg) -> NoDup (batch_indices_ [] qg') /\ ~ In kb (batch_indices_ [] qg').
  Proof. intros ND. (first [ dand4 drop_indices_eq as L1 L2 E1 -> | destruct drop_indices_eq as (L1 & L2 & E1 & ->) ]). rewrite E1 in ND. exact (NoDup_del_mid L1 L2 _ ND). Qed.
End Drop.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Batch.
Context {Clg : Ceiling}.
  Variables (A : AState) (kb fa' : Z) (more : list batch).
  Hypothesis W : WFR A.
  Hypothesis L : a_qlimbo A = BA kb [] :: more.
  Hypothesis FA : Z.of_nat (length (pk_chunks (a_cache A kQuarantineBatchClass))) = max_count kQuarantineBatchClass ->
    4 * (Z.of_nat (length (rg_free (a_reg A kQuarantineBatchClass))) + max_count kQuarantineBatchClass / 2) <= fa' /\
    rg_mapped_fa (a_reg A kQuarantineBatchClass) <= fa' /\
    fa' <= kFreeArraySize /\ fa' mod kFreeArrayMapSize = 0 /\
    fa' <= 4 * (rg_allocated_user (a_reg A kQuarantineBatchClass) / class_size kQuarantineBatchClass) + kFreeArrayMapSize (* [comment removed for export] *) /\
    (rg_mapped_user (a_reg A kQuarantineBatchClass) = 0 -> False).

  Definition recpbA : AState :=
    mkA (a_pl A) (recp_reg (a_reg A) (a_cache A) kQuarantineBatchClass kb fa') (a_cache_inited A) (recp_cache (a_cache A) kQuarantineBatchClass kb) (a_livemap A)
        [] (a_qglobal A) (a_sec A) (a_depot A) (a_fhint A) (a_fframes A) (a_ia_inited A) (a_oom A) (a_tiny A)
        more (a_scred A) (a_deadsh A) (a_pcred A) (a_paid A).

  Let qg := a_qglobal A ++ (BA kb [] :: more).
  Let qg' := a_qglobal A ++ more.
  #[local] Notation c24 := kQuarantineBatchClass.

  Theorem WFR_batch : WFR recpbA.
  Proof.
    destruct W as [rP rM rR rC rX rV rQ (rL1 & rL2 & rL3 & rL4) rS rD rF rB rT rI rE rJ rN]. rewrite L in *.
    pose proof (recp_carved (a_reg A) (a_cache A) c24 kb fa') as CC.
    pose proof (Forall_inv rL1) as HB0. (first [ dand3 HB0 as HB1 HK HB3 | destruct HB0 as (HB1 & HK & HB3) ]). cbn [ba_entries ba_idx] in HB1, HK, HB3.
    assert (HC : 1 <= c24 <= 30) by (unfold kQuarantineBatchClass; lia).
    (first [ pose proof ((max_count_range c24 HC)) as dR_19; dand3 dR_19 as MC MCE _ | pose proof (max_count_range c24 HC) as (MC & MCE & _) ]).
    assert (MC2 : 2 <= max_count c24 /\ max_count c24 mod 2 = 0) by (split; [lia| rewrite MCE, Z.mul_comm, Z.mod_mul; [reflexivity| lia]]).
    assert (P0 : pfun (PT (a_reg A) (a_cache A) (a_livemap A) [] qg)) by (apply (proj1 (wf_partition_pfun (PT _ _ _ _ _))); exact rX).
    pose proof (drop_indices (a_qglobal A) more kb) as DI. destruct (drop_nodup (a_qglobal A) more kb rL2) as [ND' NIN].
    pose proof (drop_chunks (a_qglobal A) more kb) as DC. pose proof (drop_tiny (a_qglobal A) more kb) as DT. pose proof (drop_entries (a_qglobal A) more kb) as DE.
    fold qg qg' in DI, ND', NIN, DC, DT, DE.
    assert (Q0 : p_batch_ [] qg c24 kb) by (split; [reflexivity| apply DI; left; reflexivity]).
    (first [ dand3 rC as C1 C31 C0 | destruct rC as (C1 & C31 & C0) ]). (first [ pose proof ((C1 c24 ltac:(lia))) as dR_21; dand4 dR_21 as CL CND CRG _ | pose proof (C1 c24 ltac:(lia)) as (CL & CND & CRG & _) ]). cbv zeta in CL, CND, CRG.
    assert (NK : ~ In kb (pk_chunks (a_cache A c24))) by (exact (NKsB (a_reg A) (a_cache A) (a_livemap A) qg c24 kb P0 HC HK Q0)).
    assert (CF : forall x, In x (pk_chunks (a_cache A c24)) -> ~ In x (rg_free (a_reg A c24))) by (exact (CFkB (a_reg A) (a_cache A) (a_livemap A) qg c24 P0 HC CRG)).
    pose proof (conj C1 (conj C31 C0)) as WC. rewrite rI in WC.
    (first [ dand3 rR as R1 R2 R3 | destruct rR as (R1 & R2 & R3) ]).
    pose proof (wf_caches_recp (a_reg A) (a_cache A) c24 kb fa' WC HC HK NK MC2 FA) as WC'.
    pose proof (wf_region_recp (a_reg A) (a_cache A) c24 kb fa' _ WC (R1 c24 HC) HC HK CF MC2 FA) as WR'.
    constructor; cbn [recpbA a_pl a_reg a_cache_inited a_cache a_livemap a_qthread a_qglobal a_sec a_depot a_fhint a_fframes a_ia_inited a_oom a_tiny a_qlimbo a_scred a_deadsh a_pcred a_paid a_sb a_fs];
      fold qg'.
    - exact rP.
    - exact rM.
    - split; [| split; [| intros _; exact rI]].
      + intros c' Hc'. unfold recp_reg. destruct (Z.of_nat (length (pk_chunks (a_cache A c24))) =? max_count c24) eqn:E; [| exact (R1 c' Hc')].
        unfold reg_set. destruct (Z.eqb_spec c' c24) as [->|NE]; [| exact (R1 c' Hc')].
        unfold recp_reg in WR'. rewrite E in WR'. unfold reg_set in WR'. rewrite Z.eqb_refl in WR'. exact WR'.
      + intros c' Hc'. unfold recp_reg. destruct (Z.of_nat (length (pk_chunks (a_cache A c24))) =? max_count c24); [| exact (R2 c' Hc')].
        unfold reg_set. destruct (Z.eqb_spec c' c24) as [->|NE]; [exfalso; exact (Hc' HC)| exact (R2 c' Hc')].
    - rewrite rI. exact WC'.
    - apply (proj2 (wf_partition_pfun (PT _ _ _ _ _))).
      apply (pfun_recpB (a_reg A) (a_cache A) (a_livemap A) qg qg' c24 kb fa' P0 HC HK Q0 CND).
      + intros c' k'. unfold p_quar_. cbn [app]. rewrite DE. tauto.
      + intros c' k'. unfold p_batch_. split.
        * intros [E I]. split; [split; [exact E| apply DI; right; exact I]|]. intros EE. injection EE as -> ->. exact (NIN I).
        * intros [[E I] NE]. split; [exact E|]. apply DI in I. destruct I as [->|I]; [exfalso; apply NE; rewrite E; reflexivity| exact I].
    - apply (wf_live_regC (a_reg A)); [exact CC| exact rV].
    - apply (wf_quarantine_regC (a_reg A)); [exact CC| exact rQ].
    - split; [| split; [exact ND'| split; [rewrite DC; exact rL3| intros u li Hu; rewrite DC; exact (rL4 u li Hu)]]].
      eapply Forall_impl; [| exact (Forall_inv_tail rL1)]. intros b Hb. exact (wf_batch0_regC _ _ _ CC b Hb).
    - (first [ dand5 rS as S1 S2 S3 S4 S5 | destruct rS as (S1 & S2 & S3 & S4 & S5) ]). split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|].
      intros sc Hin. rewrite DC. exact (S5 sc Hin).
    - exact rD.
    - exact rF.
    - (first [ dand5 rB as B1 B2 B3 B4 B5 | destruct rB as (B1 & B2 & B3 & B4 & B5) ]). split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. rewrite DT. exact B5.
    - reflexivity.
    - exact rI.
    - exact rE.
    - exact rJ.
    - (* [comment removed for export] *)
      (first [ dand3 rN as N0 NS ND | destruct rN as (N0 & NS & ND) ]). split; [exact N0|]. split; [exact NS|].
      intros c' k' Hc' [V|[n' Hn']]; apply (ND c' k' Hc'); [left; exact V| right]. exists n'. cbn [app] in Hn' |- *. first [rewrite (drop_entries (a_qglobal A) more kb) in Hn'; exact Hn' | rewrite <- (drop_entries (a_qglobal A) more kb); exact Hn'].
  Qed.
End Batch.


(* [comment removed for export] *)
Lemma bigmaps_sec_remove `{Clg : Ceiling} : forall (P : aplace) (sec : secreg) (i : nat),
(i < length (sr_chunks sec))%nat -> wf_bigmaps_ P sec -> wf_bigmaps_ P (sec_remove sec i).
Proof.
  intros P sec i IL [M1 M2]. set (chunks := sr_chunks sec) in *. unfold wf_bigmaps_, big_maps_ in *. cbn [sec_remove sr_chunks] in *.
  set (FIX := [(p_b6 P, kSpaceReserve); (p_pa P, kPtrArrayReserve); (kHighShadowMapBeg, kHighShadowMapSize); (kLowShadowMapBeg, 268435456);
               (p_thr P, 4096); (p_ctx P, 65536); (p_fs P, kFakeStackBytes); (p_nodes0 P, kDepotNodesBlock);
               (p_frames0 P, kStackStoreBlockBytes); (p_itab P, 3727360); (p_m64k P, 65536);
               (p_gvec P, 4096); (p_dvec P, 4096); (p_m11 P, 4096); (p_dtls P, 4096)]) in *.
  set (f := fun s0 : chunkS => (cs_map s0, map_size (cs_n s0))) in *.
  assert (LF : length FIX = 15%nat) by reflexivity.
  (* [comment removed for export] *)
  set (g := fun j : nat => if Nat.ltb j 15 then j else (15 + sr_src (length chunks) i (j - 15))%nat).
  assert (G1 : forall j, (j < 15)%nat -> g j = j) by (intros j Hj; unfold g; rewrite (proj2 (Nat.ltb_lt j 15) Hj); reflexivity).
  assert (G2 : forall j, (15 <= j)%nat -> g j = (15 + sr_src (length chunks) i (j - 15))%nat) by (intros j Hj; unfold g; rewrite (proj2 (Nat.ltb_ge j 15) Hj); reflexivity).
  assert (SRC : forall j x, nth_error (FIX ++ map f (swap_remove chunks i (CS 0 0))) j = Some x ->
                nth_error (FIX ++ map f chunks) (g j) = Some x /\ ((15 <= j)%nat -> (j - 15 < length chunks - 1)%nat)).
  { intros j x H. destruct (Nat.lt_ge_cases j 15) as [LT|GE].
    - rewrite (G1 j LT). rewrite nth_error_app1 in H by lia. rewrite nth_error_app1 by lia. split; [exact H| intros; lia].
    - rewrite (G2 j GE). rewrite nth_error_app2 in H by lia. rewrite LF in H.
      rewrite <- (swap_remove_map f chunks i (CS 0 0)) in H.
      destruct (swap_remove_src (map f chunks) i (f (CS 0 0)) (j - 15) x ltac:(rewrite length_map; exact IL) H) as [S JL].
      rewrite length_map in S, JL. rewrite nth_error_app2 by lia. rewrite LF. replace (15 + sr_src (length chunks) i (j - 15) - 15)%nat with (sr_src (length chunks) i (j - 15)) by lia.
      split; [exact S| intros _; exact JL]. }
  split.
  - intros j k bj sj bk sk Hj Hk NE.
    destruct (SRC j _ Hj) as [Sj Jl]. destruct (SRC k _ Hk) as [Sk Kl].
    apply (M1 (g j) (g k) bj sj bk sk Sj Sk).
    destruct (Nat.lt_ge_cases j 15) as [Lj|Lj]; destruct (Nat.lt_ge_cases k 15) as [Lk|Lk];
      rewrite ?(G1 j Lj), ?(G2 j Lj), ?(G1 k Lk), ?(G2 k Lk); try lia.
    specialize (Jl Lj). specialize (Kl Lk).
    pose proof (sr_src_inj (length chunks) i (j - 15) (k - 15) IL Jl Kl ltac:(lia)). lia.
  - intros b sz Hin. apply M2. apply in_app_iff in Hin as [Hin|Hin]; apply in_or_app; [left; exact Hin| right].
    apply in_map_iff in Hin as (s0 & <- & Hs0). apply in_map. apply (swap_remove_In chunks i (CS 0 0)); [exact IL| exact Hs0].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section Sec.
Context {Clg : Ceiling}.
  Variables (A : AState) (kb n : Z) (s : chunkS) (i : nat) (es : list qentry) (more : list batch) (dead' : list (Z * Z)).
  Hypothesis W : WFR A.
  Hypothesis L : a_qlimbo A = BA kb (QE (ChS s) n :: es) :: more.
  Hypothesis NTH : nth_error (sr_chunks (a_sec A)) i = Some s.
  Hypothesis DEADF : Forall (fun lh => ((kHighShadowMapBeg <= fst lh /\ snd lh <= kHighMemBeg) \/ (kLowShadowBeg <= fst lh /\ snd lh <= kShadowGapBeg))
                      /\ fst lh <= snd lh <= fst lh + kDeadShadowBytes /\ fst lh mod 8 = 0 /\ snd lh mod 8 = 0) dead'.
  Hypothesis DEADL : (length dead' <= 2)%nat.
  Hypothesis DEADB : hull_bytes dead' <= kDeadShadowBytes.

  Definition recsA : AState :=
    mkA (a_pl A) (a_reg A) (a_cache_inited A) (a_cache A) (a_livemap A)
        [] (a_qglobal A) (sec_remove (a_sec A) i) (a_depot A) (a_fhint A) (a_fframes A) (a_ia_inited A) (a_oom A) (a_tiny A)
        (BA kb es :: more) (a_scred A) (a_deadsh A ++ dead') (a_pcred A) (a_paid A).

  #[warnings="-notation-for-abbreviation"] Local Notation chunks := (sr_chunks (a_sec A)).
  Let qg := a_qglobal A ++ (BA kb (QE (ChS s) n :: es) :: more).
  Let qg' := a_qglobal A ++ (BA kb es :: more).
  Let IL : (i < length chunks)%nat. Proof. exact (nth_error_Some_lt _ _ _ NTH). Qed.
  Let NEC : chunks <> []. Proof. intros E. pose proof IL as H. rewrite E in H. cbn in H. lia. Qed.
  Let INs : In s chunks. Proof. eapply nth_error_In. exact NTH. Qed.

  Lemma rsec_nodup : NoDup chunks.
  Proof. destruct (wrS A W) as (S1 & _). exact (ABudget.NoDup_of_map cs_map _ S1). Qed.
  Lemma rchunks'_in_iff : forall y, In y (swap_remove chunks i (CS 0 0)) <-> In y chunks /\ y <> s.
  Proof. intros y. apply swap_remove_in_iff'; [exact rsec_nodup| exact NTH]. Qed.
  Lemma rchunks'_length : length (swap_remove chunks i (CS 0 0)) = (length chunks - 1)%nat.
  Proof. apply swap_remove_length. exact NEC. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rsec_live_other : forall u l, a_livemap A !! u = Some l -> li_chunk l <> ChS s.
  Proof.
    intros u l Hu E. (first [ pose proof ((wrL A W)) as dR_27; dand4 dR_27 as _ _ _ L4 | destruct (wrL A W) as (_ & _ & _ & L4) ]). apply (L4 u l Hu). rewrite L, E. fold qg.
    apply (shed_chunks (a_qglobal A) more kb (QE (ChS s) n) es). left. reflexivity.
  Qed.
  Lemma rsec_quar_other : ~ In (ChS s) (quarantined_chunks_ [] qg').
  Proof. (first [ pose proof ((wrL A W)) as dR_28; dand4 dR_28 as _ _ L3 _ | destruct (wrL A W) as (_ & _ & L3 & _) ]). rewrite L in L3. exact (proj2 (shed_nodup (a_qglobal A) more kb (QE (ChS s) n) es L3)). Qed.

  Lemma rsec_qentry : forall e, wf_qentry_ (a_reg A) (a_sec A) e -> qe_chunk e <> ChS s -> wf_qentry_ (a_reg A) (sec_remove (a_sec A) i) e.
  Proof.
    intros e H NE. unfold wf_qentry_ in *. destruct H as [H1 H2]. split; [exact H1|].
    destruct (qe_chunk e) as [[c k]|[mb n1]] eqn:EC; [exact H2|]. (first [ dand3 H2 as A1 A2 A3 | destruct H2 as (A1 & A2 & A3) ]). split; [exact A1|]. split; [exact A2|].
    cbn [sec_remove sr_chunks]. apply (proj2 (rchunks'_in_iff _)). split; [exact A3| congruence].
  Qed.

  Theorem WFR_sec : WFR recsA.
  Proof.
    pose proof rsec_live_other as LO. pose proof rsec_quar_other as QO. pose proof rsec_qentry as QE'. pose proof rchunks'_in_iff as CI. pose proof rchunks'_length as CL'.
    pose proof IL as ILn.
    destruct W as [rP rM rR rC rX rV rQ (rL1 & rL2 & rL3 & rL4) rS rD rF rB rT rI rE rJ rN]. rewrite L in *.
    pose proof (shed_entries (a_qglobal A) more kb (QE (ChS s) n) es) as SE. pose proof (shed_indices (a_qglobal A) more kb (QE (ChS s) n) es) as SI.
    pose proof (shed_chunks (a_qglobal A) more kb (QE (ChS s) n) es) as SC. cbn [qe_chunk] in SC.
    destruct (shed_nodup (a_qglobal A) more kb (QE (ChS s) n) es rL3) as [ND' NIN]. cbn [qe_chunk] in NIN.
    pose proof (shed_tiny (a_qglobal A) more kb (QE (ChS s) n) es) as ST.
    (* [comment removed for export] *)
    assert (QQ : forall e, In e (q_entries (a_qglobal A ++ (BA kb es :: more))) -> qe_chunk e <> ChS s).
    { intros e He E. apply QO. rewrite quarantined_chunks_def, q_entries_nil. cbn [app]. apply in_map_iff. exists e. split; [exact E| exact He]. }
    constructor; cbn [recsA a_pl a_reg a_cache_inited a_cache a_livemap a_qthread a_qglobal a_sec a_depot a_fhint a_fframes a_ia_inited a_oom a_tiny a_qlimbo a_scred a_deadsh a_pcred a_paid a_sb a_fs].
    - exact rP.
    - exact (bigmaps_sec_remove (a_pl A) (a_sec A) i ILn rM).
    - exact rR.
    - exact rC.
    - apply (proj2 (wf_partition_pfun (PT (a_reg A) (a_cache A) (a_livemap A) [] qg'))).
      apply (partition_same (PT (a_reg A) (a_cache A) (a_livemap A) [] qg)); [apply (proj1 (wf_partition_pfun (PT _ _ _ _ _))); exact rX| intros c; reflexivity|].
      intros c k st Hc Hk. destruct st; cbn [pholds pt_reg pt_cache pt_lm pt_qt pt_qg]; try tauto.
      + unfold p_quar_. subst qg qg'. cbn [app]. split; intros [n' Hn']; exists n'; [apply SE; right; exact Hn'|].
        apply SE in Hn'. destruct Hn' as [E|Hn']; [discriminate E| exact Hn'].
      + unfold p_batch_. subst qg qg'. rewrite SI. tauto.
    - (first [ dand3 rV as V1 V2 V3 | destruct rV as (V1 & V2 & V3) ]). split; [| exact (conj V2 V3)]. intros u l Hu. (first [ pose proof ((V1 u l Hu)) as dR_31; dand3 dR_31 as N U M | pose proof (V1 u l Hu) as (N & U & M) ]). cbv zeta in M |- *.
      split; [exact N|]. split; [exact U|]. destruct (li_chunk l) as [[c k]|[mb n1]] eqn:EC; [exact M|]. (first [ dand3 M as M1 M2 M3 | destruct M as (M1 & M2 & M3) ]).
      split; [exact M1|]. split; [exact M2|]. cbn [sec_remove sr_chunks]. apply (proj2 (CI _)). split; [exact M3|].
      intros E. apply (LO u l Hu). rewrite EC, <- E, M2. reflexivity.
    - (first [ dand8 rQ as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 | destruct rQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8) ]). unfold wf_quarantine_.
      split; [constructor|]. split; [| split; [exact Q3| split; [exact Q4| split; [exact Q5| split; [exact Q6| split; [exact Q7| exact Q8]]]]]].
      apply Forall_forall. intros b Hb. (first [ pose proof ((proj1 (Forall_forall _ _) Q2 b Hb)) as dR_34; dand3 dR_34 as B1 B2 B3 | pose proof (proj1 (Forall_forall _ _) Q2 b Hb) as (B1 & B2 & B3) ]).
      split; [exact B1|]. split; [exact B2|]. apply Forall_forall. intros e He. apply QE'; [exact (proj1 (Forall_forall _ _) B3 e He)|].
      apply QQ. unfold q_entries. rewrite flat_map_app, in_app_iff. left. apply in_flat_map. exists b. split; [exact Hb| exact He].
    - split; [| split; [rewrite SI; exact rL2| split; [exact ND'| intros u l Hu X; apply (rL4 u l Hu); apply SC; right; exact X]]].
      assert (HB : forall b, In b (BA kb es :: more) -> wf_batch0_ (a_reg A) (a_sec A) b -> wf_batch0_ (a_reg A) (sec_remove (a_sec A) i) b).
      { (intros b Hb; (first [ intro dR_45; dand3 dR_45 as B1 B2 B3 | intros (B1 & B2 & B3) ])). split; [exact B1|]. split; [exact B2|]. apply Forall_forall. intros e He. apply QE'; [exact (proj1 (Forall_forall _ _) B3 e He)|].
        apply QQ. unfold q_entries. rewrite flat_map_app, in_app_iff. right. apply in_flat_map. exists b. split; [exact Hb| exact He]. }
      (first [ pose proof ((Forall_inv rL1)) as dR_35; dand3 dR_35 as HB1 HB2 HB3 | pose proof (Forall_inv rL1) as (HB1 & HB2 & HB3) ]). cbn [ba_entries ba_idx] in HB1, HB2, HB3.
      constructor.
      + apply HB; [left; reflexivity|]. split; [cbn [ba_entries]; cbn [length] in HB1; lia|]. split; [exact HB2| exact (Forall_inv_tail HB3)].
      + apply Forall_forall. intros b Hb. apply HB; [right; exact Hb| exact (proj1 (Forall_forall _ _) (Forall_inv_tail rL1) b Hb)].
    - (first [ dand5 rS as S1 S2 S3 S4 S5 | destruct rS as (S1 & S2 & S3 & S4 & S5) ]). unfold wf_sec_. cbn [sec_remove sr_chunks sr_reserved].
      split; [| split; [| split; [exact S3| split]]].
      + rewrite <- (swap_remove_map cs_map chunks i (CS 0 0)). apply NoDup_swap_remove; [rewrite length_map; exact ILn| exact S1].
      + rewrite CL'. lia.
      + intros s0 Hs0. apply S4. exact (proj1 (proj1 (CI s0) Hs0)).
      + intros s0 Hs0. apply CI in Hs0 as [Hs0 NE]. destruct (S5 s0 Hs0) as [LV|Hq]; [left; exact LV| right].
        apply SC in Hq. destruct Hq as [E|Hq]; [exfalso; apply NE; congruence| exact Hq].
    - exact rD.
    - exact rF.
    - (first [ dand5 rB as B1 B2 B3 B4 B5 | destruct rB as (B1 & B2 & B3 & B4 & B5) ]). split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. clear -B5 ST. lia.
    - reflexivity.
    - exact rI.
    - (first [ dand4 rE as E1 E2 E3 E4 | destruct rE as (E1 & E2 & E3 & E4) ]). cbn [sec_remove sr_chunks]. rewrite CL'.
      split; [exact E1|]. split; [apply Forall_app; split; [exact E2| exact DEADF]|]. split.
      + rewrite length_app, Nat2Z.inj_add. clear -E3 DEADL ILn. lia.
      + rewrite hull_bytes_app. clear -E4 DEADB ILn. unfold kDeadShadowBytes in *. lia.
    - exact rJ.
    - (* [comment removed for export] *)
      (first [ dand3 rN as N0 NS ND | destruct rN as (N0 & NS & ND) ]). split; [exact N0|]. split; [exact NS|].
      intros c' k' Hc' [V|[n' Hn']]; apply (ND c' k' Hc'); [left; exact V| right]. exists n'. cbn [app]. apply SE. right. exact Hn'.
  Qed.
End Sec.
