(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages BothPlanImages BothTableL AsanInit BothStartup
  AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs BothMainDefs BothMain BothTop
  StartupPlanBoth StartupHSBoth BothStartupCert KindHSBoth MainHSBoth MainItabBoth TreesTopBoth.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP. Import APS.
Open Scope Z_scope.

Section K.
  Variable TTm : nat -> option (acs * plan * shape).      (* [comment removed for export] *)
  Hypothesis TTm_ok : tails_all_ok KCm BFUELm FUELm BITm TTm.
  Variable TM0 : nat -> mtree.
  Hypothesis TM0_ok : forall i, (i < 6)%nat -> mtree_ok KCm BFUELm FUELm BITm TTm 0 0 (HSA HS_main_both 0) (root_class i) (TM0 i) = true.

  Definition TREE_B : nat -> nat -> mtree := TreesTopBoth.TREE TM0.
  Lemma TREES_B : forall h ch i, HS_both h = Some ch -> (i < 6)%nat ->
    mtree_ok KCm BFUELm FUELm BITm TTm 0 0 (HSA HS_both h) (root_class i) (TREE_B h i) = true.
  Proof. exact (TreesTopBoth.TREES TTm TM0 TM0_ok). Qed.

  Definition both_certs_top : both_certs :=
    {| ac_IT0 := BothStartupCert.IT0b;
       ac_IT0_ok := BothStartupCert.IT0b_ok;
       ac_HS := HS_both;
       ac_plan := startup_plan_both;
       ac_shape := BothStartupCert.startup_shape_both;
       ac_KC0 := BothStartupCert.KC0; ac_BFUEL := BothStartupCert.BFUEL; ac_FUEL := BothStartupCert.FUEL;
       ac_TT0 := AP.TT_none;
       ac_TT0_ok := AP.tails_ok_none BSEGS BothStartupCert.IT0b BOTHL NX0 AsanInit.LIMIT BothStartupCert.KC0;
       ac_cert := BothStartupCert.startup_cert_both;
       ac_all_holes := BothStartupCert.startup_holes_both;
       ac_noblob := BothStartupCert.HSB_noblob;
       ac_KCm := KCm; ac_BFUELm := BFUELm; ac_FUELm := FUELm;
       ac_ITm := BITm; ac_ITm_ok := BITm_ok;
       ac_TTm := TTm; ac_TTm_ok := TTm_ok;
       ac_TREE := TREE_B;
       ac_TREES := TREES_B |}.
End K.
