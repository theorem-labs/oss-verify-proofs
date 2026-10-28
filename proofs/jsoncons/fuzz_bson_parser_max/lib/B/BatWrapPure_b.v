(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk As0Tables ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInitCache_b BatPopulate1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatClsRep_b BatClsGfa2_b BatClsRefill_b BatCARSpec_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma art_new_le : forall c cl, 1 <= c <= 30 -> art_cls_ok c cl -> 0 <= art_cls_new c cl <= 8192.
Proof.
  intros c cl Hc (_ & (Hau0 & Haumu) & Hrem & _). destruct (art_class_size_facts c Hc) as (Hsz & _). unfold art_cls_new.
  set (sz := AsanTab.class_size c) in *. split; [apply Z.div_pos; lia|].
  assert ((cl_mu cl + 262144 - cl_au cl) / sz < 8193); [|lia]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

Lemma art_mfa_step : forall c cl, 1 <= c <= 30 -> art_cls_ok c cl ->
  let tot := Z.of_nat (length (cl_free cl)) + art_cls_new c cl in
  art_cls_mfa' cl tot = cl_mfa cl \/ (4 * tot > cl_mfa cl /\ art_cls_mfa' cl tot = cl_mfa cl + 262144).
Proof.
  intros c cl Hc OK tot. pose proof (art_new_le c cl Hc OK) as Hnew. fold tot.
  destruct OK as (_ & _ & _ & _ & _ & _ & (kf & Emfa) & (Hmfa0 & Hmfa1) & Hnf4 & _).
  unfold art_cls_mfa'. destruct (4 * tot <=? cl_mfa cl) eqn:E; [left; reflexivity|right]. apply Z.leb_gt in E. split; [lia|].
  assert (Hlo : 262144 * kf < 4 * tot) by lia. assert (Hhi : 4 * tot <= 262144 * kf + 32768) by (unfold tot; lia).
  assert (Eq : (4 * tot + 262143) / 262144 = kf + 1). { symmetry. apply (Z.div_unique _ 262144 _ (4 * tot + 262143 - 262144 * (kf + 1))); lia. }
  rewrite Eq. lia.
Qed.

Lemma art_room_of_credit : forall c cl k, 1 <= c <= 30 -> art_cls_ok c cl -> 1 <= k ->
  cl_mu cl + 262144 * k <= 3758096384 - 262144 -> 4 * Z.of_nat (length (cl_free cl)) + 4 * 8192 * k <= 536870912 - 262144 ->
  cl_mu cl + 262144 <= 3758096384 /\ art_cls_mfa' cl (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) <= 536870912.
Proof.
  intros c cl k Hc OK Hk R1 R2. split; [lia|]. pose proof (art_new_le c cl Hc OK) as Hnew.
  destruct (art_mfa_step c cl Hc OK) as [E|(Hgt & E)]; cbv zeta in *; rewrite E.
  - destruct OK as (_ & _ & _ & _ & _ & _ & _ & (_ & H) & _). exact H.
  - destruct OK as (_ & _ & _ & _ & _ & _ & (kf & Emfa) & _ & Hnf4 & _).
    assert (4 * (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) <= 536870912 - 262144) by lia.
    assert (262144 * kf < 536870912 - 262144) by lia. assert (kf + 1 <= 2047) by lia. lia.
Qed.

Lemma art_ca_cost : forall spb c cl, 1 <= c <= 30 -> art_cls_ok c cl -> 0 <= art_cost_sum (art_ca_events spb c cl) <= 2 ^ 19.
Proof.
  intros spb c cl Hc OK. unfold art_ca_events, art_refill_events. destruct (cl_cache cl); [|cbn; lia].
  destruct (art_cls_needs_populate c cl); [|cbn; lia].
  destruct (art_mfa_step c cl Hc OK) as [E|(Hgt & E)]; cbv zeta in *.
  - pose proof OK as (_ & _ & _ & _ & _ & _ & _ & _ & Hnf4 & _).
    match goal with |- context [if ?b then _ else _] => destruct b eqn:Eb end; cbn [art_cost_sum fold_right art_cost]; [lia|].
    rewrite E. lia.
  - match goal with |- context [if ?b then _ else _] => destruct b eqn:Eb end; cbn [art_cost_sum fold_right art_cost]; [lia|]. rewrite E. lia.
Qed.

(* [comment removed for export] *)
Lemma art_ca_evok : forall RES BUDGET LENMAX KMAX log spb qs kbase c cl km,
  1 <= c <= 30 -> art_cls_ok c cl -> spb = 65536 * qs -> kbase < spb -> spb <= kbase + 65536 -> In (kbase, 0x2000011000) RES ->
  cl_mu cl = 262144 * km -> 0 <= km ->
  (cl_cache cl = [] -> art_cls_needs_populate c cl = true -> cl_mu cl + 262144 <= 3758096384
     /\ art_cls_mfa' cl (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) <= 536870912) ->
  art_cost_sum log + 2 ^ 19 <= BUDGET ->
  art_evok_list (art_EVOK RES BUDGET LENMAX KMAX) log (art_ca_events spb c cl).
Proof.
  intros RES BUDGET LENMAX KMAX log spb qs kbase c cl km Hc OK Espb Hk1 Hk2 HRES Emu Hkm Room HB.
  unfold art_ca_events, art_refill_events. destruct (cl_cache cl) eqn:Ec; [|exact I].
  destruct (art_cls_needs_populate c cl) eqn:NP; [|exact I]. destruct (Room eq_refl eq_refl) as (R1 & R2).
  pose proof OK as (_ & _ & _ & _ & _ & _ & (kf & Emfa) & (Hmfa0 & _) & _).
  assert (EV1 : art_EVOK RES BUDGET LENMAX KMAX log (AMmapFixed (spb + c * 2 ^ 32 + cl_mu cl) 262144)).
  { cbn [art_EVOK]. split. { rewrite Espb, Emu. replace (65536 * qs + c * 2 ^ 32 + 262144 * km) with ((16 * qs + c * 2 ^ 20 + 64 * km) * 4096) by lia. apply Z_mod_mult. }
    split; [reflexivity|]. split; [lia|]. split; [exists (kbase, 0x2000011000); cbn [fst snd]; split; [exact HRES|lia]|].
    rewrite art_cost_sum_snoc. cbn [art_cost]. lia. }
  destruct (art_mfa_step c cl Hc OK) as [E|(Hgt & E)]; cbv zeta in *.
  - match goal with |- context [if ?b then _ else _] => destruct b eqn:Eb end.
    + cbn [art_evok_list]. split; [exact EV1|exact I].
    + apply Z.leb_gt in Eb. exfalso. unfold art_cls_mfa' in E. rewrite (proj2 (Z.leb_gt _ _) Eb) in E.
      pose proof (Z.div_mod (4 * (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) + 262143) 262144 ltac:(lia)) as D.
      pose proof (Z.mod_pos_bound (4 * (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) + 262143) 262144 ltac:(lia)) as Rm. lia.
  - match goal with |- context [if ?b then _ else _] => destruct b eqn:Eb end; [apply Z.leb_le in Eb; lia|].
    cbn [art_evok_list]. split; [exact EV1|]. split; [|exact I]. rewrite E. replace (cl_mfa cl + 262144 - cl_mfa cl) with 262144 by lia.
    cbn [art_EVOK]. split. { rewrite Espb, Emfa. replace (65536 * qs + c * 2 ^ 32 + 3758096384 + 262144 * kf) with ((16 * qs + c * 2 ^ 20 + 917504 + 64 * kf) * 4096) by lia. apply Z_mod_mult. }
    split; [reflexivity|]. split; [lia|]. split; [exists (kbase, 0x2000011000); cbn [fst snd]; split; [exact HRES|rewrite E in R2; lia]|].
    rewrite !art_cost_sum_snoc. cbn [art_cost]. lia.
Qed.

(* [comment removed for export] *)
Lemma art_cls_ok_ca_pre : forall c cl, 1 <= c <= 30 -> art_cls_ok c cl ->
  (cl_cache cl = [] -> art_cls_needs_populate c cl = true -> cl_mu cl + 262144 <= 3758096384
     /\ art_cls_mfa' cl (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) <= 536870912) ->
  art_cls_ok c (art_ca_pre c cl).
Proof.
  intros c cl Hc OK Room. unfold art_ca_pre. destruct (cl_cache cl) eqn:Ec; [|exact OK].
  rewrite art_cls_refill_eq. apply art_cls_ok_take.
  - apply art_cls_ok_pre_take; [exact Hc|exact OK|]. intros NP. exact (Room eq_refl NP).
  - unfold art_cls_pre_take. destruct (art_cls_needs_populate c cl); [cbn [art_cls_populate cl_cache]|]; exact Ec.
  - apply art_pre_take_enough; assumption.
  - pose proof (art_refill_n_range c ltac:(lia)). lia.
Qed.
