(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmEncSpecs_u5 PmLibSpecsW_u5 PmRef_u5 PmRefFacts_u5 PmRefAllow_u5
  PmRefNonneg_u5 PmRefRead_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTopW Require Import ReadKitXW_u5.
Import ListNotations. Import PML. Import PMR. Import PMRR.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module RRWU.

Lemma ev_ind_nonneg : forall es ev, 0 <= PMES.ev_ind es ev.
Proof.
  assert (C : forall c, 0 <= PMES.comma c) by (intros c; unfold PMES.comma; destruct (0 <? PMES.ec_count c); lia).
  assert (N : forall es, 1 <= PMES.nl es) by (intros es; unfold PMES.nl, PMES.depth; lia).
  assert (P : forall es, 0 <= fst (PMES.pre_scalar es)).
  { intros [|c r]; cbn -[PMES.comma PMES.nl]; [lia|]. destruct (PMES.ec_arr c); cbn -[PMES.comma PMES.nl]; [|lia]. pose proof (C c). pose proof (N (c :: r)). lia. }
  assert (Q : forall ev, 0 <= PMES.quotes ev) by (intros ev; unfold PMES.quotes; destruct ev; try lia; destruct (_ || _); lia).
  intros es ev. destruct ev; unfold PMES.ev_ind.
  - destruct es as [|c r]; [lia|]. destruct (PMES.ec_arr c); [|lia]. pose proof (C c). pose proof (N (c :: r)). lia.
  - destruct es as [|c r]; [lia|]. destruct (PMES.ec_nla c); unfold PMES.depth; lia.
  - destruct es as [|c r]; [lia|]. pose proof (C c). pose proof (N (c :: r)). lia.
  - pose proof (P es). pose proof (Q (PMES.EvStr tag bs)). lia.
  - pose proof (P es). pose proof (Q PMES.EvNull). lia.
  - pose proof (P es). pose proof (Q (PMES.EvBool b)). lia.
  - pose proof (P es). pose proof (Q PMES.EvU64). lia.
  - pose proof (P es). pose proof (Q PMES.EvI64). lia.
  - pose proof (P es). pose proof (Q PMES.EvDbl). lia.
Qed.
Lemma ind_run_nonneg : forall ks es, 0 <= PMW.ind_run es ks.
Proof. induction ks as [|k r IH]; intros es; cbn -[PMW.ind_k PMW.step_k]; [lia|]. pose proof (ev_ind_nonneg es (PMW.eev_of k)). unfold PMW.ind_k. pose proof (IH (PMW.step_k es k)). lia. Qed.

Lemma wf_stack_nots : forall ps1, wf_ps ps1 -> ps_more ps1 = true -> Forall PMRA.nots (ps_stack ps1).
Proof.
  intros ps1 WF Hm. destruct WF as (_ & _ & _ & _ & C & T & HS & HC & HM). destruct (HM Hm) as (_ & _ & _ & HT & _). rewrite HS. unfold PMRA.nots.
  constructor; [unfold ST_ROOT, ST_STRING, ST_NUMBER; lia|]. apply Forall_app. split.
  - apply Forall_impl with (P := is_container); [|exact HC]. intros a [-> | ->]; unfold ST_OBJECT, ST_ARRAY, ST_STRING, ST_NUMBER; lia.
  - destruct HT as [[-> _] | [[-> _] | [(S & HS1 & -> & _) | (S & HS1 & -> & _)]]];
      repeat first [apply Forall_nil | apply Forall_cons]; try (destruct HS1 as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]); cbv; lia.
Qed.
Lemma rm_match_SIq : forall c M P ps, rm_match c M P ps -> wf_ps ps -> ps_more ps = true -> PMRN.SIq c.
Proof.
  intros c M P ps [CO [HS HN]] WF Hm. apply (PMRN.SIq_intro c ps CO); [| exact (wf_stack_nots ps WF Hm)].
  pose proof CO as (Cst & _). unfold PMRN.tok. rewrite Cst. intros [X|X]; [exact (proj1 (proj2 (HS X))) | exact (proj2 (HN X))].
Qed.
Lemma SIq_ctrl0 : PMRN.SIq ctrl0.
Proof. split; [intros _; cbn; lia | cbn; constructor; [unfold PMRA.nots, ST_ROOT, ST_STRING, ST_NUMBER; lia | constructor]]. Qed.

Lemma refill_ctrl : forall rs, r_c (fst (refill rs)) = r_c rs.
Proof. intros rs. exact (proj1 (PMRA.refill_facts rs)). Qed.
Lemma rloop_al_nonneg : forall F rs, PMRN.SIq (r_c rs) -> 0 <= t_al (rloop F rs).
Proof.
  induction F as [|F IH]; intros rs HS.
  - cbn. lia.
  - rewrite rloop_unfold. destruct (c_more (r_c rs)) eqn:Hm; cbn [negb]; [|cbn; lia].
    pose proof (refill_ctrl rs) as RC. destruct (refill rs) as [rs1 cd] eqn:Hr. cbn [fst snd] in RC |- *.
    destruct (Z.eqb_spec cd 0) as [->|Hcd]; cbn [negb]; [|cbn; lia].
    rewrite <- RC in HS. pose proof (PMRN.parse_some_alnn (r_c rs1) (r_w rs1) HS) as [A1 S1].
    set (q := parse_some (r_c rs1) (r_w rs1)) in *. fold (weof rs1). fold (rs_after q rs1).
    destruct (negb (q_code q =? 0)); [cbn [t_al fst snd]; exact A1|].
    destruct (weof rs1 && (c_st (q_c q) =? ST_START)); [cbn [t_al fst snd]; exact A1|].
    destruct (weof rs1 && negb _); [cbn [t_al fst snd]; exact A1|].
    specialize (IH (rs_after q rs1) S1). rewrite (t_eta (rloop F (rs_after q rs1))) in IH |- *. cbn [t_al fst snd] in IH |- *. lia.
Qed.
Lemma rpre_evs_al : forall e a t, t_evs (rpre e a t) = e ++ t_evs t /\ t_al (rpre e a t) = a + t_al t.
Proof. intros e a t. split; [apply t_evs_rpre | apply t_al_rpre]. Qed.

Lemma K_ALLOW_rloop : forall p, K p = t_evs (rloop (rfuel p) (rs0 p)) /\ ALLOW p = t_al (rloop (rfuel p) (rs0 p)).
Proof.
  intros p. unfold K, ALLOW, READ, rs0. cbv zeta.
  destruct (rloop (rfuel p) (RS ctrl0 [] p true false)) as [[[rs evs] al] code]. cbn [fst snd t_evs t_al].
  destruct (negb (code =? 0)); [split; reflexivity|]. destruct (rtail _ _) as [rs' u]. cbn [fst snd]. destruct (negb (u =? 0)); split; reflexivity.
Qed.

Lemma round_split : forall F'' rs rs1 q, c_more (r_c rs) = true -> refill rs = (rs1, 0) -> parse_some (r_c rs1) (r_w rs1) = q -> PMRN.SIq (r_c rs) ->
  exists er ar, t_evs (rloop (Datatypes.S F'') rs) = q_evs q ++ er /\ t_al (rloop (Datatypes.S F'') rs) = q_al q + ar /\ 0 <= ar.
Proof.
  intros F'' rs rs1 q Hm Hr Hq HS. rewrite rloop_unfold, Hm, Hr. cbn [negb fst snd]. rewrite Z.eqb_refl. cbn [negb]. rewrite Hq.
  assert (S1 : PMRN.SIq (q_c q)) by (rewrite <- Hq; apply PMRN.parse_some_alnn; pose proof (refill_ctrl rs) as RC; rewrite Hr in RC; cbn [fst] in RC; rewrite RC; exact HS).
  fold (weof rs1). fold (rs_after q rs1).
  destruct (negb (q_code q =? 0)); [exists [], 0; cbn [t_evs t_al fst snd]; rewrite app_nil_r; split; [reflexivity | split; lia]|].
  destruct (weof rs1 && (c_st (q_c q) =? ST_START)); [exists [], 0; cbn [t_evs t_al fst snd]; rewrite app_nil_r; split; [reflexivity | split; lia]|].
  destruct (weof rs1 && negb _); [exists [], 0; cbn [t_evs t_al fst snd]; rewrite app_nil_r; split; [reflexivity | split; lia]|].
  pose proof (rloop_al_nonneg F'' (rs_after q rs1) S1) as NN.
  rewrite (t_eta (rloop F'' (rs_after q rs1))) in NN |- *. cbn [t_evs t_al fst snd] in NN |- *.
  eexists; eexists. split; [reflexivity|]. split; [reflexivity | exact NN].
Qed.

Section S.
Variable IS : Z.
Variable rep : srep.
Let txt := srep_chars rep.

Lemma round_room : forall (eg0 eg : PMES.eghost) evs al F' rs rs1 q,
  RKW.accA rep evs al F' rs -> c_more (r_c rs) = true -> refill rs = (rs1, 0) -> parse_some (r_c rs1) (r_w rs1) = q -> PMRN.SIq (r_c rs) ->
  PMW.wroomU eg0 (K txt) (ALLOW txt) ->
  PMES.g_es eg = PMW.es_run (PMES.g_es eg0) evs -> (exists pay, 0 <= pay <= al /\ PMES.g_len eg = PMES.g_len eg0 + PMW.ind_run (PMES.g_es eg0) evs + pay) ->
  PMW.wroomU eg (q_evs q) (q_al q).
Proof.
  intros eg0 eg evs al F' rs rs1 q ACC Hm Hr Hq HS W0 HES (pay & HP & HL). unfold txt in *.
  destruct (RKW.accA_S IS rep evs al F' rs ACC) as [F'' ->]. destruct ACC as [ACC _].
  destruct (round_split F'' rs rs1 q Hm Hr Hq HS) as (er & ar & E1 & E2 & NN).
  destruct (K_ALLOW_rloop (srep_chars rep)) as [HK HA].
  rewrite HK, HA, ACC in W0. rewrite (proj1 (rpre_evs_al _ _ _)), (proj2 (rpre_evs_al _ _ _)), E1, E2 in W0.
  apply (PMW.wroomU_app eg (q_evs q) er (q_al q) ar); [| apply ind_run_nonneg | exact NN].
  exact (PMW.wroomU_shift eg0 eg evs (q_evs q ++ er) al (q_al q + ar) pay W0 HES HL HP).
Qed.
End S.
End RRWU.
