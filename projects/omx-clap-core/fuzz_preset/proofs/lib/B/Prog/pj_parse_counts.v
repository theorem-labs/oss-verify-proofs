(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: pj_parse's ROOM COUNTS (image-free pure facts for the kit's tpj_parse_specX, lib/A/PRH_FnPj.v
   blob 38a83863585f :655-658 (blob 5aca5cbe2cfb :653-656 on the cut), whose two room-count
   premises bound the peak of a request class along pj_parse's ALL-GRANTED events PresetReqAt.parse_evs sm tl []):
   - pjc_pkR_gtrace: parse_value's all-granted events at d = 0 are the first part of that list, so their peak is at
     most its peak (PresetRun.pkR_app);
   - pjc_cnt_run: the live set after ANY run of the reader at d = 0 (any outcome list ok) is inside the all-granted
     peak: by PjGrammar.agrees_jr_value the run is the all-granted one up to its first refusal and stops there, and a
     refused call makes no event (PresetReqAt.rd_hev (EFail _) = []), so its events are a prefix of the all-granted
     ones (PresetRun.pkR_prefix).
   They carry pj_parse's class-24 count to pj_free (out) after a refusal (the batch kit's PRH_FnPj.v tpj_free_specX :761) and
   parse_value's two counts to its C1 call (the batch kit's PRH_FnParse.v tparse_value_specX :307-310).
   THE HULL (route (b), lib/Spec/PresetHullBudget.v): the same first-part fact pays parse_value's hull budget out of
   pj_parse's (pjc_hull_budget_pv), leaves pj_free (out) the empty budget after parse_value's use
   (pjc_hull_budget_after_pv), and widens parse_value's hull use to pj_parse's list (pjc_hull_used_pv).
   proves no function (kind: glue lemma). No numeral. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar PresetReqAt PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetSecTotal PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG00 YGcfNames.
Import ListNotations.

Section c.
Variable sm : list Z -> Z * Z.

Lemma pjc_rd_hevs_app : forall a b,
  PresetReqAt.rd_hevs (a ++ b) = PresetReqAt.rd_hevs a ++ PresetReqAt.rd_hevs b.
Proof. intros a b. unfold PresetReqAt.rd_hevs. apply flat_map_app. Qed.

(* parse_value's all-granted events at d = 0 are the first part of pj_parse's *)
Lemma pjc_pkR_gtrace : forall f s tl,
  (PresetRun.pkR f s (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_value sm 0 tl [])))) <=
   PresetRun.pkR f s (PresetReqAt.parse_evs sm tl []))%nat.
Proof.
intros f s tl. unfold PresetReqAt.parse_evs, PresetReqAt.rtr. rewrite PjGrammar.jr_run_eq. cbn [snd].
rewrite PresetRun.pkR_app. apply Nat.le_max_l.
Qed.

(* the live set after any run of the reader at d = 0 is inside the all-granted peak *)
Lemma pjc_cnt_run : forall f s tl ok res tr okr,
  PjGrammar.jr_value sm 0 tl ok = (res, tr, okr) ->
  (PresetReqAt.cnt f (PresetReqAt.hlive_from s (PresetReqAt.rd_hevs tr)) <=
   PresetRun.pkR f s (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_value sm 0 tl [])))))%nat.
Proof.
intros f s tl ok res tr okr E.
pose proof (PjGrammar.agrees_jr_value sm 0 tl ok) as [Hup Href].
set (Tall := snd (fst (PjGrammar.jr_value sm 0 tl []))) in *.
destruct (PjGrammar.ok_upto_dec ok (PjGrammar.calls Tall)) as [U | (j & Hj & Hf & U)].
- rewrite (Hup U) in E. injection E as _ Etr _. subst tr.
  pose proof (PresetRun.pkR_prefix f (PresetReqAt.rd_hevs Tall) s (length (PresetReqAt.rd_hevs Tall))) as P.
  rewrite firstn_all in P. exact P.
- destruct (Href j Hj Hf U) as (P & Ev & rest & Em & Et & _ & _).
  rewrite Em in E. injection E as _ Etr _. subst tr.
  assert (Ep : PresetReqAt.rd_hevs (P ++ [PjGrammar.EFail (PjGrammar.esize Ev)]) =
               firstn (length (PresetReqAt.rd_hevs P)) (PresetReqAt.rd_hevs Tall)).
  { rewrite pjc_rd_hevs_app. change (PresetReqAt.rd_hevs [PjGrammar.EFail (PjGrammar.esize Ev)]) with (@nil PresetReqAt.hev).
    rewrite app_nil_r. rewrite Et, pjc_rd_hevs_app, firstn_app, firstn_all, Nat.sub_diag.
    cbn [firstn]. rewrite app_nil_r. reflexivity. }
  rewrite Ep. apply PresetRun.pkR_prefix.
Qed.

(* the two together: the live set after any run of the reader at d = 0 is inside pj_parse's all-granted peak *)
Lemma pjc_cnt_run_parse : forall f s tl ok res tr okr,
  PjGrammar.jr_value sm 0 tl ok = (res, tr, okr) ->
  (PresetReqAt.cnt f (PresetReqAt.hlive_from s (PresetReqAt.rd_hevs tr)) <=
   PresetRun.pkR f s (PresetReqAt.parse_evs sm tl []))%nat.
Proof.
intros f s tl ok res tr okr E.
exact (Nat.le_trans _ _ _ (pjc_cnt_run f s tl ok res tr okr E) (pjc_pkR_gtrace f s tl)).
Qed.

(* pj_parse's all-granted events: parse_value's at d = 0, then the rest *)
Lemma pjc_parse_evs_split : forall tl, exists R,
  PresetReqAt.parse_evs sm tl [] = PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_value sm 0 tl []))) ++ R.
Proof.
intros tl. unfold PresetReqAt.parse_evs, PresetReqAt.rtr. rewrite PjGrammar.jr_run_eq. cbn [snd].
eexists. reflexivity.
Qed.

(* the hull budget for pj_parse's list is one for parse_value's *)
Lemma pjc_hull_budget_pv : forall (cp : YGcfNames.CfParams) (S : YG00.astate) tl,
  PresetHullBudget.hull_budget S (PresetReqAt.parse_evs sm tl []) ->
  PresetHullBudget.hull_budget S (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_value sm 0 tl [])))).
Proof.
intros cp S tl H. destruct (pjc_parse_evs_split tl) as (R & E). rewrite E in H.
apply (PresetHullBudget.hull_budget_weaken S _ _ H).
- rewrite PresetSecTotal.nsec_app. lia.
- rewrite PresetSecTotal.tsec_app. pose proof (PresetSecTotal.tsec_nn R). lia.
Qed.

(* after parse_value used at most its list, the budget left is at least the empty one (pj_free (out)'s premise) *)
Lemma pjc_hull_budget_after_pv : forall (cp : YGcfNames.CfParams) (S S1 : YG00.astate) tl,
  PresetHullBudget.hull_budget S (PresetReqAt.parse_evs sm tl []) ->
  PresetHullBudget.hull_used S S1 (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_value sm 0 tl [])))) ->
  PresetHullBudget.hull_budget S1 [].
Proof.
intros cp S S1 tl H U. destruct (pjc_parse_evs_split tl) as (R & E). rewrite E in H.
exact (PresetHullBudget.hull_budget_nil S1 R (PresetHullBudget.hull_budget_app S S1 _ R H U)).
Qed.

(* a use of parse_value's list is a use of pj_parse's *)
Lemma pjc_hull_used_pv : forall (S S' : YG00.astate) tl,
  PresetHullBudget.hull_used S S' (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_value sm 0 tl [])))) ->
  PresetHullBudget.hull_used S S' (PresetReqAt.parse_evs sm tl []).
Proof.
intros S S' tl U. destruct (pjc_parse_evs_split tl) as (R & E). rewrite E.
exact (PresetHullBudget.hull_used_infix S S' [] _ R U).
Qed.
End c.
