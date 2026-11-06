(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset, Spec: the THREADED allocator hull premise (route (b)), its two
   text-facing names and their image-free arithmetic. Kind: model / count bound. Rule 24: no function is proved here.
   WHY. Every allocator call needs a Theorem Labs lane's admission at its entry (YGcfNames.cf_hull_ok; acall_pre_cf, YG0dcf.v,
   and QM_cf_of_room, YGcallcf.v, take it), and a realloc tree takes the ENTRY HEADROOM cf_hull_adm S n. A walk of a
   POST-FORM text (no run position at entry, lib/A/PRH_FnAlloc.v's FAMILY) has no fact that bounds the two meters
   nsec_cf / sec_T_cf: they are run totals that only grow. So the bound is threaded through the texts:
   - hull_budget S Eg, an ENTRY premise: the meters at S leave room for the event list Eg, the text's ALL-GRANTED
     list (the list its room-count premises already name: every allocation succeeds, ok = []);
   - hull_used S S' Eg, a POST conjunct with the SAME Eg: the call added at most Eg's counts. A refused or injected
     failure makes fewer entries (0 for the refused call: YGcfNames.secs_call_post), so the granted list bounds every
     arm, and no per-arm list is needed.
   A caller with no position pays callee k+1 from its own budget less what callees 1..k used (hull_budget_pay /
   hull_budget_app); a caller with a position pays from the run's count (lib/A/PresetHullPay.v); a leaf turns the
   budget into cf_hull_ok / cf_hull_adm at its call (lib/A/PresetHullPay.v, at preset's CfParams).
   THE COUNTS. State side: the cf layer's YGcfNames.nsec_cf / sec_T_cf (Z folds over the user entries of st_secs).
   List side: A17's PresetSecTotal.nsec / tsec (the HMal r / HRe _ r events with a secondary r, and the sum of their
   YG00.sec_map_size). A free, HFr, and a bulk free, HBulk, count 0 on both sides (free_cf keeps st_secs' counts,
   YGcfSecsStep.secs_free_step).
   GENERIC in the CfParams instance (the texts are): the caps are the class fields cf_kmax / cf_T_max.
   CLOSURE: Requires only YGcfNames, YGcfSecsStep, PresetReqAt (with PjGrammar), PresetSecTotal, all already in the
   text files' closure through lib/Spec/PresetRoomPos.v, so a text that Requires this file adds this file only.
   THE REFUSAL BOUND (section 4) is not needed by the threading (the used post is bounded by the granted list); it is
   here for a walk that tracks the tight per-arm list: a grammar call's events under any outcomes count at most its
   all-granted events, by PjGrammar.agrees. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG00 YGcfNames YGcfSecsStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetReqAt PresetRun PresetRoom
  PresetSecTotal.
Import ListNotations.
Local Open Scope Z_scope.

(* ================================================================ 1. the two names *)

Definition hull_budget {cp : YGcfNames.CfParams} (S : YG00.astate) (Eg : list PresetReqAt.hev) : Prop :=
  YGcfNames.nsec_cf S + Z.of_nat (PresetSecTotal.nsec Eg) <= YGcfNames.cf_kmax /\
  YGcfNames.sec_T_cf S + PresetSecTotal.tsec Eg <= YGcfNames.cf_T_max.

Definition hull_used (S S' : YG00.astate) (Eg : list PresetReqAt.hev) : Prop :=
  YGcfNames.nsec_cf S' <= YGcfNames.nsec_cf S + Z.of_nat (PresetSecTotal.nsec Eg) /\
  YGcfNames.sec_T_cf S' <= YGcfNames.sec_T_cf S + PresetSecTotal.tsec Eg.

(* ================================================================ 2. the use: composition and weakening *)

Lemma hull_used_refl : forall S Eg, hull_used S S Eg.
Proof. intros S Eg. pose proof (PresetSecTotal.tsec_nn Eg). unfold hull_used. lia. Qed.

(* a step that keeps both counts (free_cf, a fake frame, any step that leaves st_secs alone) *)
Lemma hull_used_same : forall S S' Eg, YGcfSecsStep.secs_same S S' -> hull_used S S' Eg.
Proof.
intros S S' Eg [N T]. pose proof (PresetSecTotal.tsec_nn Eg). unfold hull_used. rewrite N, T. lia.
Qed.

Lemma hull_used_secs : forall S S' Eg, YG00.st_secs S' = YG00.st_secs S -> hull_used S S' Eg.
Proof. intros S S' Eg E. exact (hull_used_same S S' Eg (YGcfSecsStep.secs_same_of_secs S S' E)). Qed.

Lemma hull_used_app : forall S S1 S2 A B, hull_used S S1 A -> hull_used S1 S2 B -> hull_used S S2 (A ++ B).
Proof.
intros S S1 S2 A B [N1 T1] [N2 T2]. unfold hull_used.
rewrite PresetSecTotal.nsec_app, Nat2Z.inj_add, PresetSecTotal.tsec_app. lia.
Qed.

Lemma hull_used_weaken : forall S S' A B, hull_used S S' A ->
  (PresetSecTotal.nsec A <= PresetSecTotal.nsec B)%nat -> PresetSecTotal.tsec A <= PresetSecTotal.tsec B ->
  hull_used S S' B.
Proof. intros S S' A B [N T] Hn Ht. unfold hull_used. lia. Qed.

(* a use inside a larger list: the pieces before and after count >= 0 *)
Lemma hull_used_infix : forall S S' P A Q, hull_used S S' A -> hull_used S S' (P ++ A ++ Q).
Proof.
intros S S' P A Q H. apply (hull_used_weaken S S' A); [exact H| |].
- rewrite !PresetSecTotal.nsec_app. lia.
- rewrite !PresetSecTotal.tsec_app. pose proof (PresetSecTotal.tsec_nn P). pose proof (PresetSecTotal.tsec_nn Q). lia.
Qed.

(* ================================================================ 3. the budget: paying a callee *)

Section budget.
Context {cp : YGcfNames.CfParams}.

Lemma hull_budget_weaken : forall S A B, hull_budget S B ->
  (PresetSecTotal.nsec A <= PresetSecTotal.nsec B)%nat -> PresetSecTotal.tsec A <= PresetSecTotal.tsec B ->
  hull_budget S A.
Proof. intros S A B [N T] Hn Ht. unfold hull_budget. lia. Qed.

Lemma hull_budget_nil : forall S Eg, hull_budget S Eg -> hull_budget S [].
Proof.
intros S Eg H. apply (hull_budget_weaken S [] Eg H); cbn [PresetSecTotal.tsec];
  [cbv [PresetSecTotal.nsec PresetRun.nprodR]; lia | exact (PresetSecTotal.tsec_nn Eg)].
Qed.

(* THE PAY STEP: a budget for Eg, a use of A since, and A plus the next callee's list R inside Eg (by count) leave a
   budget for R *)
Lemma hull_budget_pay : forall S S1 Eg A R, hull_budget S Eg -> hull_used S S1 A ->
  (PresetSecTotal.nsec A + PresetSecTotal.nsec R <= PresetSecTotal.nsec Eg)%nat ->
  PresetSecTotal.tsec A + PresetSecTotal.tsec R <= PresetSecTotal.tsec Eg ->
  hull_budget S1 R.
Proof. intros S S1 Eg A R [N T] [U V] Hn Ht. unfold hull_budget. lia. Qed.

(* the list forms: the next callee's list follows the used one in the budget's list *)
Lemma hull_budget_app : forall S S1 A R, hull_budget S (A ++ R) -> hull_used S S1 A -> hull_budget S1 R.
Proof.
intros S S1 A R H U. apply (hull_budget_pay S S1 (A ++ R) A R H U).
- rewrite PresetSecTotal.nsec_app. lia.
- rewrite PresetSecTotal.tsec_app. lia.
Qed.

Lemma hull_budget_infix : forall S S1 A R Q, hull_budget S (A ++ R ++ Q) -> hull_used S S1 A -> hull_budget S1 R.
Proof.
intros S S1 A R Q H U. apply (hull_budget_pay S S1 (A ++ R ++ Q) A R H U).
- rewrite !PresetSecTotal.nsec_app. lia.
- rewrite !PresetSecTotal.tsec_app. pose proof (PresetSecTotal.tsec_nn Q). lia.
Qed.

(* after the whole list is used, the room for nothing: the free's premise, and the admission at preset *)
Lemma hull_budget_used : forall S S' Eg, hull_budget S Eg -> hull_used S S' Eg -> hull_budget S' [].
Proof.
intros S S' Eg H U. apply (hull_budget_pay S S' Eg Eg [] H U);
  [cbv [PresetSecTotal.nsec PresetRun.nprodR]; lia | cbn [PresetSecTotal.tsec]; lia].
Qed.

(* a step that keeps both counts keeps the budget *)
Lemma hull_budget_same : forall S S' Eg, YGcfSecsStep.secs_same S S' -> hull_budget S Eg -> hull_budget S' Eg.
Proof. intros S S' Eg [N T] [A B]. unfold hull_budget. rewrite N, T. split; assumption. Qed.

End budget.

(* ================================================================ 4. one event's charge, and a call's use *)

(* A17's test is the allocator's (PresetSecTotal.from_primary_is_primary) *)
Lemma hull_nsec_mal : forall r,
  PresetSecTotal.nsec [PresetReqAt.HMal r] = (if YG00.from_primary r then 0 else 1)%nat.
Proof.
intros r. cbv [PresetSecTotal.nsec PresetRun.nprodR PresetRun.prod_evR]. change (PresetRoom.is_primary r) with (YG00.from_primary r).
destruct (YG00.from_primary r); reflexivity.
Qed.

Lemma hull_tsec_mal : forall r,
  PresetSecTotal.tsec [PresetReqAt.HMal r] = (if YG00.from_primary r then 0 else YG00.sec_map_size r).
Proof.
intros r. cbn [PresetSecTotal.tsec PresetSecTotal.sec_mapped]. change (PresetRoom.is_primary r) with (YG00.from_primary r).
destruct (YG00.from_primary r); cbn [negb]; lia.
Qed.

Lemma hull_nsec_re : forall m r, PresetSecTotal.nsec [PresetReqAt.HRe m r] = PresetSecTotal.nsec [PresetReqAt.HMal r].
Proof. reflexivity. Qed.

Lemma hull_tsec_re : forall m r, PresetSecTotal.tsec [PresetReqAt.HRe m r] = PresetSecTotal.tsec [PresetReqAt.HMal r].
Proof. reflexivity. Qed.

Lemma hull_count_fr : forall r,
  PresetSecTotal.nsec [PresetReqAt.HFr r] = 0%nat /\ PresetSecTotal.tsec [PresetReqAt.HFr r] = 0.
Proof. intros r. split; reflexivity. Qed.

Lemma hull_count_bulk : forall L,
  PresetSecTotal.nsec [PresetReqAt.HBulk L] = 0%nat /\ PresetSecTotal.tsec [PresetReqAt.HBulk L] = 0.
Proof. intros L. split; reflexivity. Qed.

Lemma hull_nsec_bulk : forall L, PresetSecTotal.nsec [PresetReqAt.HBulk L] = 0%nat.
Proof. reflexivity. Qed.

Lemma hull_tsec_bulk : forall L, PresetSecTotal.tsec [PresetReqAt.HBulk L] = 0.
Proof. reflexivity. Qed.

Lemma hull_nsec_nil : PresetSecTotal.nsec [] = 0%nat.
Proof. reflexivity. Qed.

Lemma hull_tsec_nil : PresetSecTotal.tsec [] = 0.
Proof. reflexivity. Qed.

(* the use of one allocator call of request r that returned q (malloc_cf, realloc (NULL, r), a realloc tree): A14's
   per-call rule YGcfNames.secs_call_post (YGcfSecsStep.secs_malloc_step / secs_realloc_step) *)
Lemma hull_used_of_call : forall r S q S', YGcfNames.secs_call_post r S (q, S') ->
  hull_used S S' [PresetReqAt.HMal r].
Proof.
intros r S q S' [N T]. cbn [fst snd] in N, T. unfold hull_used. rewrite hull_nsec_mal, hull_tsec_mal.
pose proof (PresetSecTotal.sec_map_size_pos r) as P.
unfold YGcfNames.secs_call_d, YGcfNames.secs_call_t in N, T.
destruct q; destruct (YG00.from_primary r); cbv beta iota in N, T |- *; lia.
Qed.

Lemma hull_used_of_call_re : forall m r S q S', YGcfNames.secs_call_post r S (q, S') ->
  hull_used S S' [PresetReqAt.HRe m r].
Proof.
intros m r S q S' H. pose proof (hull_used_of_call r S q S' H) as [N T].
unfold hull_used. rewrite hull_nsec_re, hull_tsec_re. split; assumption.
Qed.

(* a refused call (q = PNull) used nothing *)
Lemma hull_used_of_call_null : forall r S S', YGcfNames.secs_call_post r S (YG00.PNull, S') -> hull_used S S' [].
Proof.
intros r S S' [N T]. cbn [fst snd YGcfNames.secs_call_d YGcfNames.secs_call_t] in N, T. unfold hull_used.
cbv [PresetSecTotal.nsec PresetRun.nprodR]. cbn [PresetSecTotal.tsec Z.of_nat]. lia.
Qed.

(* ================================================================ 5. the refusal bound (optional for the walks) *)

(* the counts of a reader trace and of its parts *)
Lemma hull_rd_app : forall a b, PresetReqAt.rd_hevs (a ++ b) = PresetReqAt.rd_hevs a ++ PresetReqAt.rd_hevs b.
Proof. intros a b. unfold PresetReqAt.rd_hevs. apply flat_map_app. Qed.

(* a grammar call under ANY outcomes ok counts at most its all-granted events: under ok the trace is the granted
   one, or the granted one's prefix P followed by EFail, which makes no heap event (PresetReqAt.rd_hev), while the
   granted trace is P ++ E :: rest (PjGrammar.agrees) *)
Lemma hull_rd_agrees : forall (A : Type) (m : PjGrammar.M A) (ok : list bool), PjGrammar.agrees m ->
  (PresetSecTotal.nsec (PresetReqAt.rd_hevs (snd (fst (m ok)))) <=
     PresetSecTotal.nsec (PresetReqAt.rd_hevs (snd (fst (m [])))))%nat /\
  PresetSecTotal.tsec (PresetReqAt.rd_hevs (snd (fst (m ok)))) <=
    PresetSecTotal.tsec (PresetReqAt.rd_hevs (snd (fst (m [])))).
Proof.
intros A m ok H.
destruct (PjGrammar.ok_upto_dec ok (PjGrammar.calls (snd (fst (m []))))) as [Hu | (j & Hj & Hf & Hu)].
- rewrite (proj1 (H ok) Hu). cbn [fst snd]. split; lia.
- destruct (proj2 (H ok) j Hj Hf Hu) as (P & E & rest & E1 & E2 & _). rewrite E1, E2. cbn [fst snd].
  assert (EF : PresetReqAt.rd_hevs [PjGrammar.EFail (PjGrammar.esize E)] = []) by reflexivity.
  rewrite !hull_rd_app, EF, app_nil_r.
  rewrite !PresetSecTotal.nsec_app, !PresetSecTotal.tsec_app.
  pose proof (PresetSecTotal.tsec_nn (PresetReqAt.rd_hevs (E :: rest))). split; lia.
Qed.

(* the reading of x (PresetReqAt.rtr: jr_run's trace, which is jr_value 0's) *)
Lemma hull_rtr_agrees : forall sm x ok,
  (PresetSecTotal.nsec (PresetReqAt.rd_hevs (PresetReqAt.rtr sm ok x)) <=
     PresetSecTotal.nsec (PresetReqAt.rd_hevs (PresetReqAt.rtr sm [] x)))%nat /\
  PresetSecTotal.tsec (PresetReqAt.rd_hevs (PresetReqAt.rtr sm ok x)) <=
    PresetSecTotal.tsec (PresetReqAt.rd_hevs (PresetReqAt.rtr sm [] x)).
Proof.
intros sm x ok. unfold PresetReqAt.rtr. rewrite !PjGrammar.jr_run_eq. cbn [snd].
exact (hull_rd_agrees _ (PjGrammar.jr_value sm 0 x) ok (PjGrammar.agrees_jr_value sm 0 x)).
Qed.

(* one pj_parse of x (the reading, then on a refusal one HBulk, which counts 0) *)
Lemma hull_parse_evs_agrees : forall sm x ok,
  (PresetSecTotal.nsec (PresetReqAt.parse_evs sm x ok) <= PresetSecTotal.nsec (PresetReqAt.parse_evs sm x []))%nat /\
  PresetSecTotal.tsec (PresetReqAt.parse_evs sm x ok) <= PresetSecTotal.tsec (PresetReqAt.parse_evs sm x []).
Proof.
intros sm x ok. unfold PresetReqAt.parse_evs.
destruct (hull_rtr_agrees sm x ok) as [N T].
rewrite !PresetSecTotal.nsec_app, !PresetSecTotal.tsec_app.
destruct (fst (PjGrammar.jr_run sm x ok)); destruct (fst (PjGrammar.jr_run sm x [])); cbv beta iota;
  rewrite ?hull_nsec_nil, ?hull_tsec_nil, ?hull_nsec_bulk, ?hull_tsec_bulk; split; lia.
Qed.

(* the grammar calls the reader texts name (parse_value at depth d, parse_items) *)
Lemma hull_value_agrees : forall sm d x ok,
  (PresetSecTotal.nsec (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_value sm d x ok)))) <=
     PresetSecTotal.nsec (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_value sm d x [])))))%nat /\
  PresetSecTotal.tsec (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_value sm d x ok)))) <=
    PresetSecTotal.tsec (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_value sm d x [])))).
Proof. intros sm d x ok. exact (hull_rd_agrees _ _ ok (PjGrammar.agrees_jr_value sm d x)). Qed.

Lemma hull_items_agrees : forall sm d o x ok,
  (PresetSecTotal.nsec (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_items sm d o x ok)))) <=
     PresetSecTotal.nsec (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_items sm d o x [])))))%nat /\
  PresetSecTotal.tsec (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_items sm d o x ok)))) <=
    PresetSecTotal.tsec (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_items sm d o x [])))).
Proof. intros sm d o x ok. exact (hull_rd_agrees _ _ ok (PjGrammar.agrees_jr_items sm d o x)). Qed.

Print Assumptions hull_budget_pay.
Print Assumptions hull_budget_app.
Print Assumptions hull_budget_infix.
Print Assumptions hull_budget_used.
Print Assumptions hull_budget_same.
Print Assumptions hull_used_app.
Print Assumptions hull_used_infix.
Print Assumptions hull_used_same.
Print Assumptions hull_used_of_call.
Print Assumptions hull_used_of_call_re.
Print Assumptions hull_used_of_call_null.
Print Assumptions hull_rd_agrees.
Print Assumptions hull_parse_evs_agrees.
Print Assumptions hull_value_agrees.
Print Assumptions hull_items_agrees.
