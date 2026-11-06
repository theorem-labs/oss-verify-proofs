(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QROt.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8l1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqdR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqdR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDM_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjdK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjdK. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4l4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4l4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QxrO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QxrO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qm2h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qm2h. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDgQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDgQ.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8Ie.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8Ie. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSCw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSCw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qbz7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qbz7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTru.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTru.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEQM.
Import ListNotations.
Import QlEo_c1.Mq0.Exc. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Open Scope mspec_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x5389c%Z.
Definition w_22 := 0x00010517%Z.
Definition w_25 := 0x59453603%Z.
Definition w_81 := 0xfb8ff0ef%Z.
Definition w_281 := 0xfffc3697%Z.
Definition w_282 := 0x9f068693%Z.
Definition w_332 := 0xfffc2597%Z.
Definition w_333 := 0x7dc58593%Z.
Definition w_360 := 0xfffbc597%Z.
Definition w_362 := 0x6b758593%Z.
Definition w_371 := 0xfffbc517%Z.
Definition w_372 := 0x68b50513%Z.
Definition w_378 := 0xfffbf517%Z.
Definition w_379 := 0x50950b93%Z.
Definition w_381 := 0xf49fa0ef%Z.
Definition w_383 := 0xf4dfa0ef%Z.
Definition w_389 := 0x1ec0a0ef%Z.
Definition w_395 := 0xfffbc617%Z.
Definition w_396 := 0x62b60613%Z.
Definition w_412 := 0xfffbc597%Z.
Definition w_413 := 0x5e758593%Z.
Definition w_426 := 0xfffc2597%Z.
Definition w_427 := 0x74458593%Z.
Definition w_438 := 0xfffbc597%Z.
Definition w_439 := 0x57f58893%Z.
Definition w_453 := 0xfffbc517%Z.
Definition w_454 := 0x54350513%Z.
Definition w_467 := 0xfffbc597%Z.
Definition w_468 := 0x50b58713%Z.
Definition w_473 := 0xfffbf697%Z.
Definition w_474 := 0x49068693%Z.
Definition w_530 := 0x8b4ff0ef%Z.
Definition w_533 := 0xfffbc597%Z.
Definition w_534 := 0x40358593%Z.
Definition w_543 := 0xfffbc597%Z.
Definition w_545 := 0x3db58893%Z.
Definition w_627 := 0x1c9090ef%Z.
Definition w_639 := 0xf01fe0ef%Z.
Definition w_648 := 0xeddfe0ef%Z.
Definition w_655 := 0xec1fe0ef%Z.
Definition w_668 := 0x125090ef%Z.
Definition w_680 := 0xe5dfe0ef%Z.
Definition w_689 := 0xe39fe0ef%Z.
Definition w_701 := 0x0a1090ef%Z.
Definition w_713 := 0xdd9fe0ef%Z.
Definition w_722 := 0xdb5fe0ef%Z.
Definition w_729 := 0xd99fe0ef%Z.
Definition w_742 := 0x7fc090ef%Z.
Definition w_754 := 0xd35fe0ef%Z.
Definition w_762 := 0xd15fe0ef%Z.
Definition w_798 := 0x8c5fa0ef%Z.
Definition w_883 := 0xf70fa0ef%Z.
Definition w_907 := 0xbd5fa0ef%Z.
Definition hi_22 := (Z_to_bv 20 16).
Definition hi_281 := (Z_to_bv 20 1048515).
Definition hi_332 := (Z_to_bv 20 1048514).
Definition hi_360 := (Z_to_bv 20 1048508).
Definition hi_371 := (Z_to_bv 20 1048508).
Definition hi_378 := (Z_to_bv 20 1048511).
Definition hi_395 := (Z_to_bv 20 1048508).
Definition hi_412 := (Z_to_bv 20 1048508).
Definition hi_426 := (Z_to_bv 20 1048514).
Definition hi_438 := (Z_to_bv 20 1048508).
Definition hi_453 := (Z_to_bv 20 1048508).
Definition hi_467 := (Z_to_bv 20 1048508).
Definition hi_473 := (Z_to_bv 20 1048511).
Definition hi_533 := (Z_to_bv 20 1048508).
Definition hi_543 := (Z_to_bv 20 1048508).
Definition lo_25 := (Z_to_bv 12 1428).
Definition lo_282 := (Z_to_bv 12 2544).
Definition lo_333 := (Z_to_bv 12 2012).
Definition lo_362 := (Z_to_bv 12 1719).
Definition lo_372 := (Z_to_bv 12 1675).
Definition lo_379 := (Z_to_bv 12 1289).
Definition lo_396 := (Z_to_bv 12 1579).
Definition lo_413 := (Z_to_bv 12 1511).
Definition lo_427 := (Z_to_bv 12 1860).
Definition lo_439 := (Z_to_bv 12 1407).
Definition lo_454 := (Z_to_bv 12 1347).
Definition lo_468 := (Z_to_bv 12 1291).
Definition lo_474 := (Z_to_bv 12 1168).
Definition lo_534 := (Z_to_bv 12 1027).
Definition lo_545 := (Z_to_bv 12 987).
Definition joff_81 := (Z_to_bv 21 2095032).
Definition joff_381 := (Z_to_bv 21 2076488).
Definition joff_383 := (Z_to_bv 21 2076492).
Definition joff_389 := (Z_to_bv 21 41452).
Definition joff_530 := (Z_to_bv 21 2093236).
Definition joff_627 := (Z_to_bv 21 39368).
Definition joff_639 := (Z_to_bv 21 2092800).
Definition joff_648 := (Z_to_bv 21 2092764).
Definition joff_655 := (Z_to_bv 21 2092736).
Definition joff_668 := (Z_to_bv 21 39204).
Definition joff_680 := (Z_to_bv 21 2092636).
Definition joff_689 := (Z_to_bv 21 2092600).
Definition joff_701 := (Z_to_bv 21 39072).
Definition joff_713 := (Z_to_bv 21 2092504).
Definition joff_722 := (Z_to_bv 21 2092468).
Definition joff_729 := (Z_to_bv 21 2092440).
Definition joff_742 := (Z_to_bv 21 38908).
Definition joff_754 := (Z_to_bv 21 2092340).
Definition joff_762 := (Z_to_bv 21 2092308).
Definition joff_798 := (Z_to_bv 21 2074820).
Definition joff_883 := (Z_to_bv 21 2074480).
Definition joff_907 := (Z_to_bv 21 2075604).
Definition G_102fd := 0x104f3%Z.
Definition G_10741 := 0x1338d%Z.
Definition G_107e0 := 0x13490%Z.
Definition G_11778 := 0x165a8%Z.
Definition G_11858 := 0x16688%Z.
Definition G_118c0 := 0x166f0%Z.
Definition got_ssp := got_ssp.
Definition GLOBALS_TOP := GLOBALS_TOP.
Definition STATIC_SPLIT := STATIC_SPLIT.
Definition ssp_guard := ssp_guard.
Definition e_194bc := 0x4edd8%Z.
Definition e_194c8 := 0x4ede4%Z.
Definition e_197bc := 0x4f29c%Z.
Definition e_fwritex := 0x53198%Z.
Definition e_memcpy := 0x5d6b0%Z.
Definition e_memset := 0x5dc30%Z.
Definition e_2596c := 0x5e09c%Z.
Lemma CODE : CodeAt.code_at rsegs 0x5389c (Q8l1.Mq1.printf_core_code 0x00010517%Z 0x59453603%Z 0xfb8ff0ef%Z 0xfffc3697%Z 0x9f068693%Z 0xfffc2597%Z 0x7dc58593%Z 0xfffbc597%Z 0x6b758593%Z 0xfffbc517%Z 0x68b50513%Z 0xfffbf517%Z 0x50950b93%Z 0xf49fa0ef%Z 0xf4dfa0ef%Z 0x1ec0a0ef%Z 0xfffbc617%Z 0x62b60613%Z 0xfffbc597%Z 0x5e758593%Z 0xfffc2597%Z 0x74458593%Z 0xfffbc597%Z 0x57f58893%Z 0xfffbc517%Z 0x54350513%Z 0xfffbc597%Z 0x50b58713%Z 0xfffbf697%Z 0x49068693%Z 0x8b4ff0ef%Z 0xfffbc597%Z 0x40358593%Z 0xfffbc597%Z 0x3db58893%Z 0x1c9090ef%Z 0xf01fe0ef%Z 0xeddfe0ef%Z 0xec1fe0ef%Z 0x125090ef%Z 0xe5dfe0ef%Z 0xe39fe0ef%Z 0x0a1090ef%Z 0xdd9fe0ef%Z 0xdb5fe0ef%Z 0xd99fe0ef%Z 0x7fc090ef%Z 0xd35fe0ef%Z 0xd15fe0ef%Z 0x8c5fa0ef%Z 0xf70fa0ef%Z 0xbd5fa0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x5389c mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x5389c /\ 0x5389c + 3632 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Definition fwritex_spec := @fwritex_spec.
End GwI.

Lemma zb_length : forall l, length (zb l) = length l.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [GwInst.gw_exact (@QROt.Mq1.zb_length) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq1.zb_length)]. Qed.
Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [GwInst.gw_exact (@QROt.Mq1.zb_app) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq1.zb_app)]. Qed.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@QQRC.Mq0.zb) (@QDgQ.zb) (Q6nq.gwt_def (@QROt.Mq1.wfile) (@QxrO.wfile) (Q6nq.gwt_def (@QQLG.Mq7.wfile) (@QxrO.wfile) (Q6nq.gwt_def (@Q8l1.Mq1.topok_stmt) (@QTru.topok_stmt) (Q6nq.gwt_def (@QROt.Mq1.ssp_cells) (@Qm2h.ssp_cells) (Q6nq.gwt_def (@Q91D.Mq2.ssp_cells) (@Qm2h.ssp_cells) (Q6nq.gwt_def (@QROt.Mq1.sink_frame_stmt) (@QTru.sink_frame_stmt) (Q6nq.gwt_def (@Q8l1.Mq1.sink_frame_stmt) (@QTru.sink_frame_stmt) (Q6nq.gwt_def (@QROt.Mq1.sink_flags_stmt) (@QTru.sink_flags_stmt) (Q6nq.gwt_def (@Q8l1.Mq1.sink_flags_stmt) (@QTru.sink_flags_stmt) (Q6nq.gwt_def (@QROt.Mq1.out_stmt) (@QTru.out_stmt) (Q6nq.gwt_def (@Q8l1.Mq1.out_stmt) (@QTru.out_stmt) (Q6nq.gwt_def (@QROt.Mq1.out_post) (@QTru.out_post) (Q6nq.gwt_def (@Q8l1.Mq1.out_post) (@QTru.out_post) (Q6nq.gwt_def (@QROt.Mq1.fwritex_post) (@QxrO.fwritex_post) (Q6nq.gwt_def (@QQLG.Mq7.fwritex_post) (@QxrO.fwritex_post) (Q6nq.gwt_def (@QROt.Mq1.fpcall_stmt) (@QTru.fpcall_stmt) (Q6nq.gwt_def (@Q8l1.Mq1.fpcall_stmt) (@QTru.fpcall_stmt) (Q6nq.gwt_def (@QROt.Mq1.fpcall_post) (@QTru.fpcall_post) (Q6nq.gwt_def (@Q8l1.Mq1.fpcall_post) (@QTru.fpcall_post) (Q6nq.gwt_def (@OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_shp.F_fmt_fp.fmt_fp_facts) (@Q8Ie.fmt_fp_facts) (Q6nq.gwt_def (@Q8l1.Mq1.TOPOK_sn) (@QTru.TOPOK_sn) (Q6nq.gwt_def (@QROt.Mq1.SINK_sn) (@QTru.SINK_sn) (Q6nq.gwt_def (@Q8l1.Mq1.SINK_sn) (@QTru.SINK_sn) (Q6nq.gwt_def (@Q8l1.Mq1.OUT_sn) (@QTru.OUT_sn) (Q6nq.gwt_def (@Q8l1.Mq1.OUTFP_sn) (@QTru.OUTFP_sn) Q6nq.gwt_nil)))))))))))))))))))))))))).
Lemma Forall_disjoint_from : ltac2:(Q6nq.tyx '(@QROt.Mq1.Forall_disjoint_from) [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]]); first [GwInst.gw_exact (@QROt.Mq1.Forall_disjoint_from) | autorewrite with gw_eqs; GwInst.gw_exact (@QROt.Mq1.Forall_disjoint_from)]. Qed.

Lemma bytes_at_func : ltac2:(Q6nq.ty1 'GwI.segs '(@QROt.Mq1.bytes_at_func) [] '(@nil Z) 'gwt_X).
Proof. first [GwApply.gw_by_name GwI.segs (@QROt.Mq1.bytes_at_func) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq1.bytes_at_func)]. Qed.
Lemma C8_func : forall m a (v w : word), rw_cells rsegs m a [C8 v] -> rw_cells rsegs m a [C8 w] -> v = w.
Proof. first [GwApply.gw_by_name GwI.segs (@QROt.Mq1.C8_func) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq1.C8_func)]. Qed.

Section SnProofs.
Variables (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (frest : list cell) (B TOP : Z).
Let SINK := SINK_sn Fp fl0 j1 j2 lbfw frest B TOP.

#[using="Type"] Lemma sn_sink_frame : sink_frame_stmt Fp B 80 SINK.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_sink_frame_stmt__3; @gw_eq_sink_frame_stmt__2; @gw_eq_sink_frame_stmt]]); first [GwApply.gw_by_name GwI.segs (@QROt.Mq1.sn_sink_frame) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq1.sn_sink_frame)]. Qed.

#[using="Type"] Lemma sn_sink_flags : sink_flags_stmt Fp SINK.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_sink_flags_stmt__3; @gw_eq_sink_flags_stmt__2; @gw_eq_sink_flags_stmt]]); first [GwApply.gw_by_name GwI.segs (@QROt.Mq1.sn_sink_flags) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq1.sn_sink_flags)]. Qed.

#[using="Type"] Lemma sn_topok : topok_stmt (TOPOK_sn TOP).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_TOPOK_sn__3; @gw_eq_TOPOK_sn__2; @gw_eq_TOPOK_sn]; [@gw_eq_topok_stmt__3; @gw_eq_topok_stmt__2; @gw_eq_topok_stmt]]); first [GwApply.gw_by_name GwI.segs (@QROt.Mq1.sn_topok) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq1.sn_topok)]. Qed.

#[using="Type"] Lemma sn_out : out_stmt Fp B 80 SINK (TOPOK_sn TOP) OUT_sn.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_OUT_sn__3; @gw_eq_OUT_sn__2; @gw_eq_OUT_sn]; [@gw_eq_TOPOK_sn__3; @gw_eq_TOPOK_sn__2; @gw_eq_TOPOK_sn]; [@gw_eq_out_stmt__3; @gw_eq_out_stmt__2; @gw_eq_out_stmt]]); first [GwApply.gw_by_name GwI.segs (@QROt.Mq1.sn_out) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq1.sn_out)]. Qed.

#[using="Type"] Lemma sn_fpcall : ltac2:(Q6nq.ty1 'GwI.segs '(@QROt.Mq1.sn_fpcall) [[@gw_eq_OUTFP_sn__3; @gw_eq_OUTFP_sn__2; @gw_eq_OUTFP_sn]; [@gw_eq_TOPOK_sn__3; @gw_eq_TOPOK_sn__2; @gw_eq_TOPOK_sn]; [@gw_eq_fmt_fp_facts__3; @gw_eq_fmt_fp_facts__2; @gw_eq_fmt_fp_facts]; [@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]] '([80]%Z : list Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_OUTFP_sn__3; @gw_eq_OUTFP_sn__2; @gw_eq_OUTFP_sn]; [@gw_eq_TOPOK_sn__3; @gw_eq_TOPOK_sn__2; @gw_eq_TOPOK_sn]; [@gw_eq_fmt_fp_facts__3; @gw_eq_fmt_fp_facts__2; @gw_eq_fmt_fp_facts]; [@gw_eq_fpcall_stmt__3; @gw_eq_fpcall_stmt__2; @gw_eq_fpcall_stmt]]); first [GwApply.gw_by_name GwI.segs (@QROt.Mq1.sn_fpcall) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QROt.Mq1.sn_fpcall)]. Qed.
End SnProofs.
