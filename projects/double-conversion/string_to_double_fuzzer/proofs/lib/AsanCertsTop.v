(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanStartup
  AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs AsanMain AsanTop
  StartupPlanAsan StartupHSAsan AsanStartupCert KindHSAsan MainHSAsan MainItab TreesTopAsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP. Import APS.
Open Scope Z_scope.

Section K.
  Variable TTm : nat -> option (acs * plan * shape).      (* [comment removed for export] *)
  Hypothesis TTm_ok : tails_all_ok KCm BFUELm FUELm ITm TTm.
  Variable TM0 : nat -> mtree.
  Hypothesis TM0_ok : forall i, (i < 6)%nat -> mtree_ok KCm BFUELm FUELm ITm TTm 0 0 (HSA HS_main 0) (root_class i) (TM0 i) = true.

  Definition TREE_A : nat -> nat -> mtree := TreesTopAsan.TREE TM0.
  Lemma TREES_A : forall h ch i, HS_asan h = Some ch -> (i < 6)%nat ->
    mtree_ok KCm BFUELm FUELm ITm TTm 0 0 (HSA HS_asan h) (root_class i) (TREE_A h i) = true.
  Proof. exact (TreesTopAsan.TREES TTm TM0 TM0_ok). Qed.

  Definition asan_certs_top : asan_certs :=
    {| ac_IT0 := AsanStartupCert.IT0;
       ac_IT0_ok := AsanStartupCert.IT0_ok;
       ac_HS := HS_asan;
       ac_plan := startup_plan;
       ac_shape := AsanStartupCert.startup_shape;
       ac_KC0 := AsanStartupCert.KC0; ac_BFUEL := AsanStartupCert.BFUEL; ac_FUEL := AsanStartupCert.FUEL;
       ac_TT0 := AP.TT_none;
       ac_TT0_ok := AP.tails_ok_none ASEGS AsanStartupCert.IT0 ASAN NX0 AsanInit.LIMIT AsanStartupCert.KC0;
       ac_cert := AsanStartupCert.startup_cert;
       ac_all_holes := AsanStartupCert.startup_holes;
       ac_noblob := AsanStartupCert.HSA_noblob;
       ac_KCm := KCm; ac_BFUELm := BFUELm; ac_FUELm := FUELm;
       ac_ITm := ITm; ac_ITm_ok := ITm_ok;
       ac_TTm := TTm; ac_TTm_ok := TTm_ok;
       ac_TREE := TREE_A;
       ac_TREES := TREES_A |}.
End K.
