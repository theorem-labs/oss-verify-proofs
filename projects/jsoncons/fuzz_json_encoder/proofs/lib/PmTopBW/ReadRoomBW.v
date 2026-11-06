(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA L5Defs L5Core PmLibDefs PmLibDefsA PmLibSpecsA PmEncSpecs
  PmLibSpecsXA PmLibSpecsW PmLibSpecsXAW PmRef PmRefFacts PmRefFacts2 PmRefAllow PmRefNonneg PmRefRead.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmTopBW Require Import TopSpecsBW ReadKitXBW.
Import ListNotations. Import PML. Import PMR. Import PMRR.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module RRAW.
(* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma K_ALLOW_rloop : forall p, K p = t_evs (rloop (rfuel p) (rs0 p)) /\ ALLOW p = t_al (rloop (rfuel p) (rs0 p)).
Proof.
  intros p. unfold K, ALLOW, READ, rs0. cbv zeta.
  destruct (rloop (rfuel p) (RS ctrl0 [] p true false)) as [[[rs evs] al] code]. cbn [fst snd t_evs t_al].
  destruct (negb (code =? 0)); [split; reflexivity|]. destruct (rtail _ _) as [rs' u]. cbn [fst snd]. destruct (negb (u =? 0)); split; reflexivity.
Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Section S.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable IS : Z.
Variable rep : srep.
Variable CL : Z.
Let txt := srep_chars rep.

Lemma round_room : forall (eg0 eg : PMES.eghost) evs al F' rs rs1 q,
  RKAW.accA rep evs al F' rs -> c_more (r_c rs) = true -> refill rs = (rs1, 0) -> parse_some (r_c rs1) (r_w rs1) = q -> PMRN.SIq (r_c rs) ->
  PMXAW.wroom CL eg0 (K txt) (ALLOW txt) ->
  PMES.g_es eg = PMW.es_run (PMES.g_es eg0) evs -> (exists pay, 0 <= pay <= al /\ PMES.g_len eg = PMES.g_len eg0 + PMW.ind_run (PMES.g_es eg0) evs + pay) ->
  PMXAW.wroom CL eg (q_evs q) (q_al q).
Proof.
  intros eg0 eg evs al F' rs rs1 q ACC Hm Hr Hq HS W0 HES (pay & HP & HL). unfold txt in *.
  destruct (RKAW.accA_S IS rep evs al F' rs ACC) as [F'' ->]. destruct ACC as [ACC _].
  destruct (round_split F'' rs rs1 q Hm Hr Hq HS) as (er & ar & E1 & E2 & NN).
  destruct (K_ALLOW_rloop (srep_chars rep)) as [HK HA].
  rewrite HK, HA, ACC in W0. rewrite (proj1 (rpre_evs_al _ _ _)), (proj2 (rpre_evs_al _ _ _)), E1, E2 in W0.
  apply (PMXAW.wroom_app CL eg (q_evs q) er (q_al q) ar); [| apply PMXAW.ind_run_nonneg | exact NN].
  exact (PMXAW.wroom_shift CL eg0 eg evs (q_evs q ++ er) al (q_al q + ar) pay W0 HES HL HP).
Qed.
End S.
End RRAW.
