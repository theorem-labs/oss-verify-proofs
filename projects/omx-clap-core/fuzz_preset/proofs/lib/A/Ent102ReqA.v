(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Ent102ReqA.v, with its module paths and module names changed; 30 of its 60 lines of code are new or changed and 1 line of the source is left out. *)
(* omx-clap-core/fuzz_preset, harness fix #102 (both images; image-free): THE REQUEST BOUND of the walk of
   LLVMFuzzerTestOneInput (lib/A/Ent102CutsA.v ec_req_bound) PROVED from a Theorem Labs lane's bounds, so it is not a
   premise of the walk: every ledger request of the check_* subtrees on an input x of at most 0x300000 bytes is within
   g_most = PJ_ALLOC_BOUND (|x|) = 256 |x| + 20480 (fuzz_preset.c:810, set by fuzz_alloc_most at +0x13c).
   SOURCES: lib/Spec/PjReqBoundW.v 0394d1a7ad83 (rq_read_bound, rqw_read, rqa_crt_bound) from
   a working branch d6092ab75a2, by path. Its terms are the kit's (PRH_FnPj.RQ_pj_parse, PRH_FnCheck.RQW /
   RQA_crt, walkkit-next 3438f3406f33) with their bodies written out; the bridge below is conversion only
   (PRH_Reader.prh_jr_strtod and ReaderRes.jr_strtod have the same body: strtod_c.strtod_model txt is
   FloatScan.scan_strtod (txt ++ [0])), plus PjReqBoundW.crt_tree_form for ck_crt_tree.
   rule 24: proves no function (kind: segment lemma - a pure fact the walk's call sites cite). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqG YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjReqBoundW PjReqBoundC.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnPj PRH_FnCheck Ent102CutsA.
Import ListNotations.
Local Open Scope Z_scope.

(* the two strtod oracles are one term *)
Lemma ec_strtod_same : prh_jr_strtod = ReaderRes.jr_strtod.
Proof. reflexivity. Qed.

Lemma ec_rq_pj_parse : forall x, PRH_FnPj.RQ_pj_parse x = PjReqBoundW.rq_read prh_jr_strtod x.
Proof. reflexivity. Qed.

Lemma ec_rqw : forall t p, RQW t p = PjReqBoundW.rqw t p.
Proof. reflexivity. Qed.

Lemma ec_rqa_crt : forall t, RQA_crt t = PjReqBoundW.rqa_crt prh_jr_strtod t.
Proof.
intros t. unfold RQA_crt, PjReqBoundW.rqa_crt, RQA_rtt, PjReqBoundW.rqa_rtt, zmaxl.
rewrite PjReqBoundW.crt_tree_form. destruct t; reflexivity.
Qed.

(* THE ONE OPEN PREMISE of this file: check_round_trip's per-request ceiling (PRH_FnCheck.v:944). Stated exactly in
   the shape a Theorem Labs lane's lemma will take, so that it is swapped for a citation when that lands (owner, 15:4xZ:
   it measures RQ_crt at MAXB first; the margin is about 5.28e8 against cf_malloc_max - cf_head = 5.36e8, and
   RQ_crt's TX_req part has no bound in lib). Everything else in ec_req_bound is PROVED below. *)
Section req.
Context {cp : CfParams}.
Hypothesis sat_rq_crt :
  forall (x : list Z) (t : PjTree.jv), Z.of_nat (length x) <= EC_NMAX -> ck_read x = Some t ->
  RQ_crt t + cf_head < cf_malloc_max.

Theorem ec_req_bound_holds : ec_req_bound.
Proof.
unfold ec_req_bound, PJ_ALLOC_BOUND. intros x Hx. split.
- rewrite ec_rq_pj_parse. pose proof (PjReqBoundW.rq_read_bound prh_jr_strtod x). lia.
- intros t Ht. unfold ck_read in Ht. rewrite <- ec_strtod_same in Ht.
  rewrite (ec_rqw t true), (ec_rqw t false), ec_rqa_crt.
  pose proof (PjReqBoundW.rqw_read prh_jr_strtod x t true Ht).
  pose proof (PjReqBoundW.rqw_read prh_jr_strtod x t false Ht).
  pose proof (PjReqBoundW.rqa_crt_bound prh_jr_strtod x t Ht).
  pose proof (sat_rq_crt x t Hx Ht).
  repeat split; lia.
Qed.

End req.

(* AT THE CONCRETE CfParams, CLOSED: the premise is discharged by a Theorem Labs lane's rq_crt_cf_bound
   (lib/Spec/PjReqBoundC.v blob 196cc949112c, a working branch 65f21a2d711; via rq_crt_abs, RQ_crt t at
   most 352,321,446), through a reflexivity bridge to its LOCAL copies of the kit's RQ_crt and ck_read. Its cf_malloc_max
   is the FINAL value 402,653,184 (lands with a Theorem Labs lane's landing 1); THIS base's CfParams_preset still carries
   2 ^ 29 - 2 ^ 20 = 535,822,336, and since 402,653,184 <= 535,822,336 the fact holds at the value this base carries
   (and at the final one: the same bound, 352,321,446 + 16 < 402,653,184). *)
Lemma ec_rq_crt_bridge : forall t, RQ_crt t = PjReqBoundC.RQ_crt t.
Proof. reflexivity. Qed.
Lemma ec_ck_read_bridge : forall x, ck_read x = PjReqBoundC.ck_read x.
Proof. reflexivity. Qed.

(* the premise itself at the concrete CfParams, CLOSED: rows that carry sat_rq_crt as a Section premise (seg_L5b_A)
   are discharged with it at the instance *)
Lemma sat_rq_crt_preset : forall (x : list Z) (t : PjTree.jv), Z.of_nat (length x) <= EC_NMAX -> ck_read x = Some t ->
  RQ_crt t + @cf_head CfParamsPreset.CfParams_preset < @cf_malloc_max CfParamsPreset.CfParams_preset.
Proof.
intros x t Hx Ht.
rewrite ec_rq_crt_bridge. rewrite ec_ck_read_bridge in Ht.
pose proof (PjReqBoundC.rq_crt_cf_bound x t ltac:(unfold EC_NMAX in Hx; lia) Ht) as H.
unfold PjReqBoundC.cf_head, PjReqBoundC.cf_malloc_max in H.
change (@cf_head CfParamsPreset.CfParams_preset) with 16.
change (@cf_malloc_max CfParamsPreset.CfParams_preset) with (2 ^ 28 + 2 ^ 27).
lia.
Qed.

Theorem ec_req_bound_holds_preset : ec_req_bound (cp := CfParamsPreset.CfParams_preset).
Proof. apply ec_req_bound_holds. exact sat_rq_crt_preset. Qed.

Print Assumptions ec_req_bound_holds.
About ec_req_bound_holds.
Print Assumptions ec_req_bound_holds_preset.
Print Assumptions sat_rq_crt_preset.
