(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require AsFuzzContract.
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanFO BothAsanPlanImages AsanInit AsanMainLib AsanMainHooksBoth AsanMainDefsBoth
  AsanMainTreeBoth AsanNodesRP AsanMainCertLibBoth AsanMainItabBoth StartupHSBoth AsanMainCertP5h0Both.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanMainCertKWS_1Both AsanMainCertKWS_2Both AsanMainCertKWS_3Both AsanMainCertKWS_4Both AsanMainCertKW_1Both AsanMainCertKW_2Both AsanMainCertKW_3Both AsanMainCertKW_4Both.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
Definition CKW : class := ((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]).
Ltac kw_bool := first [ reflexivity | vm_compute; reflexivity ].
Ltac kw_seg H := eapply mtree_ok_segP; [ kw_bool | exact H | kw_bool | kw_bool | eapply mforest_ok_cons; [ reflexivity | | apply mforest_ok_nil ] ].
Ltac kw_pre0 H := eapply mtree_ok_pre0; [ kw_bool | exact H | kw_bool | kw_bool | eapply mforest_ok_cons; [ reflexivity | | apply mforest_ok_nil ] ].
Ltac kw_leaf H := eapply mtree_ok_leafP; [ kw_bool | exact H | kw_bool ].
Section KWTree.
  Variable PAY_1 : mtree.
  Hypothesis PAY_1_ok : mtree_ok KCm BFUELm FUELm ITmD 1 1 w1f_ps_r5bbbbbba_S_h0 ((((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, QMIN, 131071)]) PAY_1 = true.
  Variable PAY_2 : mtree.
  Hypothesis PAY_2_ok : mtree_ok KCm BFUELm FUELm ITmD 1 1 w2f_ps_r5bbbbbba_S_h0 ((((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 131071 + 1, QMAX)]) ++ [(QFlen, QMIN, 196607)]) PAY_2 = true.
  Variable PAY_2b : mtree.
  Hypothesis PAY_2b_ok : mtree_ok KCm BFUELm FUELm ITmD 1 1 w2bf_ps_r5bbbbbba_S_h0 ((((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 196607 + 1, QMAX)]) ++ [(QFlen, QMIN, 262143)]) PAY_2b = true.
  Variable PAY_3 : mtree.
  Hypothesis PAY_3_ok : mtree_ok KCm BFUELm FUELm ITmD 1 1 w3f_pl_r5bbbbbba_S_h0 ((((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 262143 + 1, QMAX)]) ++ [(QFlen, QMIN, 524287)]) PAY_3 = true.
  Variable PAY_4 : mtree.
  Hypothesis PAY_4_ok : mtree_ok KCm BFUELm FUELm ITmD 1 1 w4f_pl_r5bbbbbba_S_h0 ((((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 524287 + 1, QMAX)]) ++ [(QFlen, QMIN, 1048575)]) PAY_4 = true.
  Variable PAY_5 : mtree.
  Hypothesis PAY_5_ok : mtree_ok KCm BFUELm FUELm ITmD 1 1 w5f_pl_r5bbbbbba_S_h0 ((((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 1048575 + 1, QMAX)]) ++ [(QFlen, QMIN, 2097151)]) PAY_5 = true.
  Variable PAY_6 : mtree.
  Hypothesis PAY_6_ok : mtree_ok KCm BFUELm FUELm ITmD 1 1 w6f_pl_r5bbbbbba_S_h0 ((((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 2097151 + 1, QMAX)]) ++ [(QFlen, QMIN, 4194303)]) PAY_6 = true.
  Variable PAY_7 : mtree.
  Hypothesis PAY_7_ok : mtree_ok KCm BFUELm FUELm ITmD 1 1 w7f_pl_r5bbbbbba_S_h0 ((((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 4194303 + 1, QMAX)]) ++ [(QFlen, QMIN, 8388607)]) PAY_7 = true.
  Variable PAY_8 : mtree.
  Hypothesis PAY_8_ok : mtree_ok KCm BFUELm FUELm ITmD 1 1 w8f_pl_r5bbbbbba_S_h0 ((((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 8388607 + 1, QMAX)]) ++ [(QFlen, QMIN, 16777215)]) PAY_8 = true.
  Variable PAY_9 : mtree.
  Hypothesis PAY_9_ok : mtree_ok KCm BFUELm FUELm ITmD 1 1 w9f_pl_r5bbbbbba_S_h0 ((((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 16777215 + 1, QMAX)]) ++ [(QFlen, QMIN, 33554431)]) PAY_9 = true.
  Variable PAY_10 : mtree.
  Hypothesis PAY_10_ok : mtree_ok KCm BFUELm FUELm ITmD 1 1 w10f_pl_r5bbbbbba_S_h0 ((((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 33554431 + 1, QMAX)]) ++ [(QFlen, QMIN, 67108863)]) PAY_10 = true.
  Definition KWT0 : mtree :=
    (MPre 1 c1_ps_r5bbbbb_h0 [(0%nat, (1%nat, c1_ps_r5bbbbb_S_h0))] [(0%nat, (MPre 1 c1_ps_r5bbbbbs_h0 [(0%nat, (1%nat, c1_ps_r5bbbbbs_S_h0))] [(0%nat, (MSplit QFlen 131071 (MClass ((((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, QMIN, 131071)]) (MPre 1 w1f_ps_r5bbbbbba_h0 [(0%nat, (1%nat, w1f_ps_r5bbbbbba_S_h0))] [(0%nat, PAY_1)])) (MClass (((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 131071 + 1, QMAX)]) (MPre 1 c2_ps_r5bbbbbb_h0 [(0%nat, (1%nat, c2_ps_r5bbbbbb_S_h0))] [(0%nat, (MPre 1 c2_ps_r5bbbbbbs_h0 [(0%nat, (1%nat, c2_ps_r5bbbbbbs_S_h0))] [(0%nat, (MSplit QFlen 262143 (MSplit QFlen 196607 (MClass ((((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 131071 + 1, QMAX)]) ++ [(QFlen, QMIN, 196607)]) (MPre 1 w2f_ps_r5bbbbbba_h0 [(0%nat, (1%nat, w2f_ps_r5bbbbbba_S_h0))] [(0%nat, PAY_2)])) (MClass ((((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 196607 + 1, QMAX)]) ++ [(QFlen, QMIN, 262143)]) (MPre 1 w2bf_ps_r5bbbbbba_h0 [(0%nat, (1%nat, w2bf_ps_r5bbbbbba_S_h0))] [(0%nat, PAY_2b)]))) (MClass (((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 262143 + 1, QMAX)]) (MPre 1 c3_ps_r5bbbbbb_h0 [(0%nat, (1%nat, c3_ps_r5bbbbbb_S_h0))] [(0%nat, (MPre 1 c3_ps_r5bbbbbbs_h0 [(0%nat, (1%nat, c3_ps_r5bbbbbbs_S_h0))] [(0%nat, (MSplit QFlen 524287 (MClass ((((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 262143 + 1, QMAX)]) ++ [(QFlen, QMIN, 524287)]) (MPre 1 w3f_pl_r5bbbbbba_h0 [(0%nat, (1%nat, w3f_pl_r5bbbbbba_S_h0))] [(0%nat, PAY_3)])) (MClass (((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 524287 + 1, QMAX)]) (MPre 1 c4_pl_r5bbbbbb_h0 [(0%nat, (1%nat, c4_pl_r5bbbbbb_S_h0))] [(0%nat, (MPre 1 c4_ps_r5bbbbbbs_h0 [(0%nat, (1%nat, c4_ps_r5bbbbbbs_S_h0))] [(0%nat, (MSplit QFlen 1048575 (MClass ((((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 524287 + 1, QMAX)]) ++ [(QFlen, QMIN, 1048575)]) (MPre 1 w4f_pl_r5bbbbbba_h0 [(0%nat, (1%nat, w4f_pl_r5bbbbbba_S_h0))] [(0%nat, PAY_4)])) (MClass (((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 1048575 + 1, QMAX)]) (MPre 1 c5_pl_r5bbbbbb_h0 [(0%nat, (1%nat, c5_pl_r5bbbbbb_S_h0))] [(0%nat, (MPre 1 c5_ps_r5bbbbbbs_h0 [(0%nat, (1%nat, c5_ps_r5bbbbbbs_S_h0))] [(0%nat, (MSplit QFlen 2097151 (MClass ((((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 1048575 + 1, QMAX)]) ++ [(QFlen, QMIN, 2097151)]) (MPre 1 w5f_pl_r5bbbbbba_h0 [(0%nat, (1%nat, w5f_pl_r5bbbbbba_S_h0))] [(0%nat, PAY_5)])) (MClass (((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 2097151 + 1, QMAX)]) (MPre 1 c6_pl_r5bbbbbb_h0 [(0%nat, (1%nat, c6_pl_r5bbbbbb_S_h0))] [(0%nat, (MPre 1 c6_ps_r5bbbbbbs_h0 [(0%nat, (1%nat, c6_ps_r5bbbbbbs_S_h0))] [(0%nat, (MSplit QFlen 4194303 (MClass ((((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 2097151 + 1, QMAX)]) ++ [(QFlen, QMIN, 4194303)]) (MPre 1 w6f_pl_r5bbbbbba_h0 [(0%nat, (1%nat, w6f_pl_r5bbbbbba_S_h0))] [(0%nat, PAY_6)])) (MClass (((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 4194303 + 1, QMAX)]) (MPre 1 c7_pl_r5bbbbbb_h0 [(0%nat, (1%nat, c7_pl_r5bbbbbb_S_h0))] [(0%nat, (MPre 1 c7_ps_r5bbbbbbs_h0 [(0%nat, (1%nat, c7_ps_r5bbbbbbs_S_h0))] [(0%nat, (MSplit QFlen 8388607 (MClass ((((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 4194303 + 1, QMAX)]) ++ [(QFlen, QMIN, 8388607)]) (MPre 1 w7f_pl_r5bbbbbba_h0 [(0%nat, (1%nat, w7f_pl_r5bbbbbba_S_h0))] [(0%nat, PAY_7)])) (MClass (((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 8388607 + 1, QMAX)]) (MPre 1 c8_pl_r5bbbbbb_h0 [(0%nat, (1%nat, c8_pl_r5bbbbbb_S_h0))] [(0%nat, (MPre 1 c8_ps_r5bbbbbbs_h0 [(0%nat, (1%nat, c8_ps_r5bbbbbbs_S_h0))] [(0%nat, (MSplit QFlen 16777215 (MClass ((((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 8388607 + 1, QMAX)]) ++ [(QFlen, QMIN, 16777215)]) (MPre 1 w8f_pl_r5bbbbbba_h0 [(0%nat, (1%nat, w8f_pl_r5bbbbbba_S_h0))] [(0%nat, PAY_8)])) (MClass (((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 16777215 + 1, QMAX)]) (MPre 1 c9_pl_r5bbbbbb_h0 [(0%nat, (1%nat, c9_pl_r5bbbbbb_S_h0))] [(0%nat, (MPre 1 c9_ps_r5bbbbbbs_h0 [(0%nat, (1%nat, c9_ps_r5bbbbbbs_S_h0))] [(0%nat, (MSplit QFlen 33554431 (MClass ((((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 16777215 + 1, QMAX)]) ++ [(QFlen, QMIN, 33554431)]) (MPre 1 w9f_pl_r5bbbbbba_h0 [(0%nat, (1%nat, w9f_pl_r5bbbbbba_S_h0))] [(0%nat, PAY_9)])) (MClass (((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 33554431 + 1, QMAX)]) (MPre 1 c10_pl_r5bbbbbb_h0 [(0%nat, (1%nat, c10_pl_r5bbbbbb_S_h0))] [(0%nat, (MPre 1 c10_ps_r5bbbbbbs_h0 [(0%nat, (1%nat, c10_ps_r5bbbbbbs_S_h0))] [(0%nat, (MSplit QFlen 67108863 (MClass ((((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 33554431 + 1, QMAX)]) ++ [(QFlen, QMIN, 67108863)]) (MPre 1 w10f_pl_r5bbbbbba_h0 [(0%nat, (1%nat, w10f_pl_r5bbbbbba_S_h0))] [(0%nat, PAY_10)])) (MClass (((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QFlen, 65535 + 1, QMAX)]) ++ [(QFlen, 67108863 + 1, QMAX)]) (MPre 1 c11_pl_r5bbbbbb_h0 [(0%nat, (1%nat, c11_pl_r5bbbbbb_S_h0))] [(0%nat, (MLeaf 1 c11_pw_r5bbbbbbs_h0))]))))]))]))))]))]))))]))]))))]))]))))]))]))))]))]))))]))]))))]))]))))]))]))))]))]).
  Lemma KW_ok0 : mtree_ok KCm BFUELm FUELm ITmD 1 1 pp_sP5h0_S_h0 CKW KWT0 = true.
  Proof.
    unfold KWT0, CKW.
    kw_seg c1_ps_r5bbbbb_ok.
    kw_seg c1_ps_r5bbbbbs_ok.
    apply mtree_ok_split.
    apply mtree_ok_class; [kw_bool|].
    kw_seg w1f_ps_r5bbbbbba_ok.
    exact PAY_1_ok.
    apply mtree_ok_class; [kw_bool|].
    kw_seg c2_ps_r5bbbbbb_ok.
    kw_seg c2_ps_r5bbbbbbs_ok.
    apply mtree_ok_split.
    apply mtree_ok_split.
    apply mtree_ok_class; [kw_bool|].
    kw_seg w2f_ps_r5bbbbbba_ok.
    exact PAY_2_ok.
    apply mtree_ok_class; [kw_bool|].
    kw_seg w2bf_ps_r5bbbbbba_ok.
    exact PAY_2b_ok.
    apply mtree_ok_class; [kw_bool|].
    kw_seg c3_ps_r5bbbbbb_ok.
    kw_seg c3_ps_r5bbbbbbs_ok.
    apply mtree_ok_split.
    apply mtree_ok_class; [kw_bool|].
    kw_seg w3f_pl_r5bbbbbba_ok.
    exact PAY_3_ok.
    apply mtree_ok_class; [kw_bool|].
    kw_seg c4_pl_r5bbbbbb_ok.
    kw_seg c4_ps_r5bbbbbbs_ok.
    apply mtree_ok_split.
    apply mtree_ok_class; [kw_bool|].
    kw_seg w4f_pl_r5bbbbbba_ok.
    exact PAY_4_ok.
    apply mtree_ok_class; [kw_bool|].
    kw_seg c5_pl_r5bbbbbb_ok.
    kw_seg c5_ps_r5bbbbbbs_ok.
    apply mtree_ok_split.
    apply mtree_ok_class; [kw_bool|].
    kw_seg w5f_pl_r5bbbbbba_ok.
    exact PAY_5_ok.
    apply mtree_ok_class; [kw_bool|].
    kw_seg c6_pl_r5bbbbbb_ok.
    kw_seg c6_ps_r5bbbbbbs_ok.
    apply mtree_ok_split.
    apply mtree_ok_class; [kw_bool|].
    kw_seg w6f_pl_r5bbbbbba_ok.
    exact PAY_6_ok.
    apply mtree_ok_class; [kw_bool|].
    kw_seg c7_pl_r5bbbbbb_ok.
    kw_seg c7_ps_r5bbbbbbs_ok.
    apply mtree_ok_split.
    apply mtree_ok_class; [kw_bool|].
    kw_seg w7f_pl_r5bbbbbba_ok.
    exact PAY_7_ok.
    apply mtree_ok_class; [kw_bool|].
    kw_seg c8_pl_r5bbbbbb_ok.
    kw_seg c8_ps_r5bbbbbbs_ok.
    apply mtree_ok_split.
    apply mtree_ok_class; [kw_bool|].
    kw_seg w8f_pl_r5bbbbbba_ok.
    exact PAY_8_ok.
    apply mtree_ok_class; [kw_bool|].
    kw_seg c9_pl_r5bbbbbb_ok.
    kw_seg c9_ps_r5bbbbbbs_ok.
    apply mtree_ok_split.
    apply mtree_ok_class; [kw_bool|].
    kw_seg w9f_pl_r5bbbbbba_ok.
    exact PAY_9_ok.
    apply mtree_ok_class; [kw_bool|].
    kw_seg c10_pl_r5bbbbbb_ok.
    kw_seg c10_ps_r5bbbbbbs_ok.
    apply mtree_ok_split.
    apply mtree_ok_class; [kw_bool|].
    kw_seg w10f_pl_r5bbbbbba_ok.
    exact PAY_10_ok.
    apply mtree_ok_class; [kw_bool|].
    kw_seg c11_pl_r5bbbbbb_ok.
    kw_leaf c11_pw_r5bbbbbbs_ok.
  Qed.
End KWTree.
