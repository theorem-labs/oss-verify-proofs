(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/omx-clap-core/fuzz_preset/lib/A/PresetHullPay.v, with its module paths changed. *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset, the THREADED hull premise at preset's CfParams: what a walk does
   with lib/Spec/PresetHullBudget.v's hull_budget / hull_used at its allocator calls and where a payer with a run
   position gets the budget from. IMAGE-FREE (preset's CfParams instance lib/A/CfParamsPreset.v is shared by both
   images). Kind: model / count bound. Rule 24: no function is proved here.
   1. THE LEAF. At CfParams_preset the admission field cf_hull_ok S is `nsec_cf S <= preset_kmax /\ sec_T_cf S <=
      preset_T_max` and the entry headroom cf_hull_adm S r is preset_hull_adm S r (the charge of one call of request
      r). So hull_budget S Eg gives cf_hull_ok S (hull_ok_of_budget; QM_cf_of_room's and acall_pre_cf's admission
      premise), a budget for one event HMal r / HRe m r gives cf_hull_adm S r (hull_adm_of_budget_mal / _re; the
      realloc tree's entry premise), and a budget with its use gives cf_hull_ok after the call (hull_ok_after).
   2. THE TOP BUDGET. At ANY position i of a run of at most 4 calls, the interface's count conjunct (lib/Spec/
      PresetRoomPos.v rp_count, its premise discharged by YGcfSecsStep.secs_steps_cf_holds) and A17's prefix bounds
      (lib/Spec/PresetSecTotalRun.v nsec_run_prefix / tsec_run_prefix) put the meters at most rp_NB + 4 NCALL =
      100,572 and rp_TB + 4 TCALL = 43,154,232,300; a list of at most one call's counts (NCALL = 25,127 secondaries,
      TCALL = 10,520,122,619 mapped bytes) then fits under preset's caps 2 ^ 17 = 131,072 and 2 ^ 36 =
      68,719,476,736 (hull_budget_of_room_pos). This is how the driver and the entry-keyed texts pay a post-form
      callee: the run's allowance left at any position is at least one call's worth.
   3. ONE CALL'S WORTH, for the lists the payers pass: one event of request at most 2 ^ 30 (hull_nt_one_mal / _re;
      every text request is below cf_malloc_max = 2 ^ 28 + 2 ^ 27), one pj_parse of an input of at most MAXB bytes
      (hull_nt_parse, from A17's NT_parse), and any infix of one call's model events (hull_nt_infix_call, from A17's
      nsec_call / tsec_call; e.g. check_no_overread's all-granted list by PRH_FnCheck.ck_cno_evs_call).
   NOT Required by the text files: it Requires PresetSecTotalRun, whose closure has plain lib/Prog/*_c.v files. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG00 YGcfNames YGcfSecsStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetRun PresetRoomPos
  PresetSecTotal PresetSecTotalRun PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.

(* ================================================================ 1. the leaf *)

Lemma hull_ok_of_budget : forall S Eg, @PresetHullBudget.hull_budget CP S Eg -> @YGcfNames.cf_hull_ok CP S.
Proof.
intros S Eg [N T]. pose proof (PresetSecTotal.tsec_nn Eg).
change (@YGcfNames.cf_kmax CP) with CfParamsPreset.preset_kmax in N.
change (@YGcfNames.cf_T_max CP) with CfParamsPreset.preset_T_max in T.
change (@YGcfNames.cf_hull_ok CP S) with
  (YGcfNames.nsec_cf S <= CfParamsPreset.preset_kmax /\ YGcfNames.sec_T_cf S <= CfParamsPreset.preset_T_max).
lia.
Qed.

Lemma hull_adm_of_budget_mal : forall S r, @PresetHullBudget.hull_budget CP S [PresetReqAt.HMal r] ->
  @YGcfNames.cf_hull_adm CP S r.
Proof.
intros S r [N T]. rewrite PresetHullBudget.hull_nsec_mal in N. rewrite PresetHullBudget.hull_tsec_mal in T.
change (@YGcfNames.cf_kmax CP) with CfParamsPreset.preset_kmax in N.
change (@YGcfNames.cf_T_max CP) with CfParamsPreset.preset_T_max in T.
change (@YGcfNames.cf_hull_adm CP S r) with (CfParamsPreset.preset_hull_adm S r). unfold CfParamsPreset.preset_hull_adm.
destruct (YG00.from_primary r); cbv beta iota in N, T |- *; lia.
Qed.

Lemma hull_adm_of_budget_re : forall S m r, @PresetHullBudget.hull_budget CP S [PresetReqAt.HRe m r] ->
  @YGcfNames.cf_hull_adm CP S r.
Proof.
intros S m r [N T]. apply hull_adm_of_budget_mal. unfold PresetHullBudget.hull_budget.
rewrite <- (PresetHullBudget.hull_nsec_re m r), <- (PresetHullBudget.hull_tsec_re m r). split; assumption.
Qed.

(* after the call: the budget less its use is the admission at the post state *)
Lemma hull_ok_after : forall S S' Eg, @PresetHullBudget.hull_budget CP S Eg -> PresetHullBudget.hull_used S S' Eg ->
  @YGcfNames.cf_hull_ok CP S'.
Proof.
intros S S' Eg H U. exact (hull_ok_of_budget S' [] (PresetHullBudget.hull_budget_used S S' Eg H U)).
Qed.

(* ================================================================ 2. the top budget from a run position *)

Theorem hull_budget_of_room_pos : forall sm x os i H0 hist S Eg, (length os <= 4)%nat ->
  PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  Z.of_nat (PresetSecTotal.nsec Eg) <= PresetSecTotal.NCALL -> PresetSecTotal.tsec Eg <= PresetSecTotal.TCALL ->
  @PresetHullBudget.hull_budget CP S Eg.
Proof.
intros sm x os i H0 hist S Eg Hl HP Hn Ht. destruct HP as (_ & _ & _ & _ & _ & HC).
destruct (HC YGcfSecsStep.secs_steps_cf_holds) as [N T]. rewrite PresetRoomPos.rp_nsec_layer in N.
pose proof (PresetSecTotalRun.nsec_run_prefix sm x os i Hl) as Np.
pose proof (PresetSecTotalRun.tsec_run_prefix sm x os i Hl) as Tp.
rewrite PresetSecTotal.NCALL_value in Hn, Np. rewrite PresetSecTotal.TCALL_value in Ht, Tp.
unfold PresetRoomPos.rp_NB in N. unfold PresetRoomPos.rp_TB in T. change (2 ^ 30) with 1073741824 in T.
unfold PresetHullBudget.hull_budget.
change (@YGcfNames.cf_kmax CP) with 131072. change (@YGcfNames.cf_T_max CP) with 68719476736.
split; lia.
Qed.

(* ================================================================ 3. one call's worth *)

Lemma hull_nt_one_mal : forall r, 0 <= r <= 2 ^ 30 ->
  Z.of_nat (PresetSecTotal.nsec [PresetReqAt.HMal r]) <= PresetSecTotal.NCALL /\
  PresetSecTotal.tsec [PresetReqAt.HMal r] <= PresetSecTotal.TCALL.
Proof.
intros r Hr. change (2 ^ 30) with 1073741824 in Hr.
rewrite PresetHullBudget.hull_nsec_mal, PresetHullBudget.hull_tsec_mal, PresetSecTotal.NCALL_value,
  PresetSecTotal.TCALL_value.
destruct (YG00.from_primary r) eqn:E; cbv beta iota; [lia|].
assert (L : 64513 <= r).
{ apply PresetSecTotalRun.sec_req_lo. change (negb (YG00.from_primary r) = true). rewrite E. reflexivity. }
pose proof (PresetSecTotalRun.sec_map_size_le r L) as M. unfold PresetSecTotal.SEC_MAP_OVH in M. lia.
Qed.

Lemma hull_nt_one_re : forall m r, 0 <= r <= 2 ^ 30 ->
  Z.of_nat (PresetSecTotal.nsec [PresetReqAt.HRe m r]) <= PresetSecTotal.NCALL /\
  PresetSecTotal.tsec [PresetReqAt.HRe m r] <= PresetSecTotal.TCALL.
Proof.
intros m r Hr. rewrite PresetHullBudget.hull_nsec_re, PresetHullBudget.hull_tsec_re. exact (hull_nt_one_mal r Hr).
Qed.

Lemma hull_nt_parse : forall sm x ok, Z.of_nat (length x) <= PresetReqAt.MAXB ->
  Z.of_nat (PresetSecTotal.nsec (PresetReqAt.parse_evs sm x ok)) <= PresetSecTotal.NCALL /\
  PresetSecTotal.tsec (PresetReqAt.parse_evs sm x ok) <= PresetSecTotal.TCALL.
Proof.
intros sm x ok Hx. destruct (PresetSecTotalRun.NT_parse sm x ok Hx) as [N T].
pose proof (PresetSecTotalRun.tsec_treq (PresetReqAt.parse_evs sm x ok)) as Tt.
assert (RN : PresetSecTotal.RD_N = 3072) by (vm_compute; reflexivity).
assert (RT : PresetSecTotal.RD_T = 707810400) by (vm_compute; reflexivity).
rewrite RN in N. rewrite RT in T. rewrite PresetSecTotal.NCALL_value, PresetSecTotal.TCALL_value.
unfold PresetSecTotal.SEC_MAP_OVH in Tt. split; lia.
Qed.

Lemma hull_nt_infix_call : forall sm x o1 o2 o0 P Eg Q, PresetRun.call_evs sm x o1 o2 o0 = P ++ Eg ++ Q ->
  Z.of_nat (PresetSecTotal.nsec Eg) <= PresetSecTotal.NCALL /\ PresetSecTotal.tsec Eg <= PresetSecTotal.TCALL.
Proof.
intros sm x o1 o2 o0 P Eg Q E.
pose proof (PresetSecTotalRun.nsec_call sm x o1 o2 o0) as N. pose proof (PresetSecTotalRun.tsec_call sm x o1 o2 o0) as T.
rewrite E, !PresetSecTotal.nsec_app, !Nat2Z.inj_add in N. rewrite E, !PresetSecTotal.tsec_app in T.
pose proof (PresetSecTotal.tsec_nn P). pose proof (PresetSecTotal.tsec_nn Q). split; lia.
Qed.

Print Assumptions hull_ok_of_budget.
Print Assumptions hull_adm_of_budget_mal.
Print Assumptions hull_adm_of_budget_re.
Print Assumptions hull_ok_after.
Print Assumptions hull_budget_of_room_pos.
Print Assumptions hull_nt_one_mal.
Print Assumptions hull_nt_one_re.
Print Assumptions hull_nt_parse.
Print Assumptions hull_nt_infix_call.
