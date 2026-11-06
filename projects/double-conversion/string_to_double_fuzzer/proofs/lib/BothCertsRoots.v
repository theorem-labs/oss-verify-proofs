(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages BothPlanImages BothTableL AsanInit BothStartup
  AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs BothMainDefs BothMain BothTop
  MainHSBoth MainItabBoth BothCertsTop BTreesRoots03 BTreesRoot4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Section R5.
  Variable TTm : nat -> option (acs * plan * shape).      
  Hypothesis TTm_ok : tails_all_ok KCm BFUELm FUELm BITm TTm.
  Hypothesis T_r4_ok : mtree_ok KCm BFUELm FUELm BITm TTm 0 0 (HSA HS_main_both 0) (root_class 4) T_h0_r4 = true.
  Variable T_r5 : mtree.
  Hypothesis T_r5_ok : mtree_ok KCm BFUELm FUELm BITm TTm 0 0 (HSA HS_main_both 0) (root_class 5) T_r5 = true.

  Definition TM0 (i : nat) : mtree :=
    match i with
    | 0%nat => T_h0_r0 | 1%nat => T_h0_r1 | 2%nat => T_h0_r2 | 3%nat => T_h0_r3 | 4%nat => T_h0_r4
    | _ => T_r5
    end.
  Lemma TM0_ok : forall i, (i < 6)%nat -> mtree_ok KCm BFUELm FUELm BITm TTm 0 0 (HSA HS_main_both 0) (root_class i) (TM0 i) = true.
  Proof.
    intros i Hi. destruct i as [|[|[|[|[|[|i]]]]]]; cbn [TM0];
      [exact (T_h0_r0_ok TTm) | exact (T_h0_r1_ok TTm) | exact (T_h0_r2_ok TTm) | exact (T_h0_r3_ok TTm) | exact T_r4_ok | exact T_r5_ok | lia].
  Qed.

  Definition both_certs_roots : both_certs := both_certs_top TTm TTm_ok TM0 TM0_ok.
End R5.
