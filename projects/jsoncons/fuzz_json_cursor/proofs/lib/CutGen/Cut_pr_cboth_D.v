(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm9PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_pr_cboth_T Cut_pr_cboth_R0p0 Cut_pr_cboth_R0p1 Cut_pr_cboth_R0p2 Cut_pr_cboth_R0p3 Cut_pr_cboth_R0p4 Cut_pr_cboth_R1p0 Cut_pr_cboth_R1p1 Cut_pr_cboth_R2p0 Cut_pr_cboth_R2p1.
Definition cp0 : CC.cutpoint := Eval vm_compute in mkcp t0 o0.
Definition cp1 : CC.cutpoint := Eval vm_compute in mkcp t1 o1.
Definition cp2 : CC.cutpoint := Eval vm_compute in mkcp t2 o2.
Definition cp3 : CC.cutpoint := Eval vm_compute in mkcp t3 o3.
Definition cp4 : CC.cutpoint := Eval vm_compute in mkcp t4 o4.
Definition cp5 : CC.cutpoint := Eval vm_compute in mkcp t5 o5.
Definition cp6 : CC.cutpoint := Eval vm_compute in mkcp t6 o6.
Definition cp7 : CC.cutpoint := Eval vm_compute in mkcp t7 o7.
Definition cp8 : CC.cutpoint := Eval vm_compute in mkcp t8 o8.
Definition cp9 : CC.cutpoint := Eval vm_compute in mkcp t9 o9.
Definition cp10 : CC.cutpoint := Eval vm_compute in mkcp t10 o10.
Definition cp11 : CC.cutpoint := Eval vm_compute in mkcp t11 o11.
Definition cp12 : CC.cutpoint := Eval vm_compute in mkcp t12 o12.
Definition cp13 : CC.cutpoint := Eval vm_compute in mkcp t13 o13.
Definition cp14 : CC.cutpoint := Eval vm_compute in mkcp t14 o14.
Definition cp15 : CC.cutpoint := Eval vm_compute in mkcp t15 o15.
Definition cp16 : CC.cutpoint := Eval vm_compute in mkcp t16 o16.
Definition cp17 : CC.cutpoint := Eval vm_compute in mkcp t17 o17.
Definition cp18 : CC.cutpoint := Eval vm_compute in mkcp t18 o18.
Definition cp19 : CC.cutpoint := Eval vm_compute in mkcp t19 o19.
Definition cp20 : CC.cutpoint := Eval vm_compute in mkcp t20 o20.
Definition cp21 : CC.cutpoint := Eval vm_compute in mkcp t21 o21.
Definition cp22 : CC.cutpoint := Eval vm_compute in mkcp t22 o22.
Definition cp23 : CC.cutpoint := Eval vm_compute in mkcp t23 o23.
Definition cp24 : CC.cutpoint := Eval vm_compute in mkcp t24 o24.
Definition cp25 : CC.cutpoint := Eval vm_compute in mkcp t25 o25.
Definition cp26 : CC.cutpoint := Eval vm_compute in mkcp t26 o26.
Definition cp27 : CC.cutpoint := Eval vm_compute in mkcp t27 o27.
Definition cp28 : CC.cutpoint := Eval vm_compute in mkcp t28 o28.
Definition cp29 : CC.cutpoint := Eval vm_compute in mkcp t29 o29.
Definition cp30 : CC.cutpoint := Eval vm_compute in mkcp t30 o30.
Definition cp31 : CC.cutpoint := Eval vm_compute in mkcp t31 o31.
Definition cp32 : CC.cutpoint := Eval vm_compute in mkcp t32 o32.
Definition cp33 : CC.cutpoint := Eval vm_compute in mkcp t33 o33.
Definition cp34 : CC.cutpoint := Eval vm_compute in mkcp t34 o34.
Definition cp35 : CC.cutpoint := Eval vm_compute in mkcp t35 o35.
Definition cp36 : CC.cutpoint := Eval vm_compute in mkcp t36 o36.
Definition cp37 : CC.cutpoint := Eval vm_compute in mkcp t37 o37.
Definition cp38 : CC.cutpoint := Eval vm_compute in mkcp t38 o38.
Definition cp39 : CC.cutpoint := Eval vm_compute in mkcp t39 o39.
Definition cp40 : CC.cutpoint := Eval vm_compute in mkcp t40 o40.
Definition cp41 : CC.cutpoint := Eval vm_compute in mkcp t41 o41.
Definition cp42 : CC.cutpoint := Eval vm_compute in mkcp t42 o42.
Definition cp43 : CC.cutpoint := Eval vm_compute in mkcp t43 o43.
Definition cp44 : CC.cutpoint := Eval vm_compute in mkcp t44 o44.
Definition cp45 : CC.cutpoint := Eval vm_compute in mkcp t45 o45.
Definition cp46 : CC.cutpoint := Eval vm_compute in mkcp t46 o46.
Definition cp47 : CC.cutpoint := Eval vm_compute in mkcp t47 o47.
Definition cp48 : CC.cutpoint := Eval vm_compute in mkcp t48 o48.
Definition cp49 : CC.cutpoint := Eval vm_compute in mkcp t49 o49.
Definition cp50 : CC.cutpoint := Eval vm_compute in mkcp t50 o50.
Definition cp51 : CC.cutpoint := Eval vm_compute in mkcp t51 o51.
Definition cp52 : CC.cutpoint := Eval vm_compute in mkcp t52 o52.
Definition cp53 : CC.cutpoint := Eval vm_compute in mkcp t53 o53.
Definition cp54 : CC.cutpoint := Eval vm_compute in mkcp t54 o54.
Definition cp55 : CC.cutpoint := Eval vm_compute in mkcp t55 o55.
Definition cp56 : CC.cutpoint := Eval vm_compute in mkcp t56 o56.
Definition cp57 : CC.cutpoint := Eval vm_compute in mkcp t57 o57.
Definition cp58 : CC.cutpoint := Eval vm_compute in mkcp t58 o58.
Definition cp59 : CC.cutpoint := Eval vm_compute in mkcp t59 o59.
Definition cp60 : CC.cutpoint := Eval vm_compute in mkcp t60 o60.
Definition cp61 : CC.cutpoint := Eval vm_compute in mkcp t61 o61.
Definition cp62 : CC.cutpoint := Eval vm_compute in mkcp t62 o62.
Definition cp63 : CC.cutpoint := Eval vm_compute in mkcp t63 o63.
Definition CPS : list CC.cutpoint := [cp0; cp1; cp2; cp3; cp4; cp5; cp6; cp7; cp8; cp9; cp10; cp11; cp12; cp13; cp14; cp15; cp16; cp17; cp18; cp19; cp20; cp21; cp22; cp23; cp24; cp25; cp26; cp27; cp28; cp29; cp30; cp31; cp32; cp33; cp34; cp35; cp36; cp37; cp38; cp39; cp40; cp41; cp42; cp43; cp44; cp45; cp46; cp47; cp48; cp49; cp50; cp51; cp52; cp53; cp54; cp55; cp56; cp57; cp58; cp59; cp60; cp61; cp62; cp63].
Definition TAGS : list (list CC.tag) := Eval vm_compute in [map snd (CA.po_leaves o0); map snd (CA.po_leaves o1); map snd (CA.po_leaves o2); map snd (CA.po_leaves o3); map snd (CA.po_leaves o4); map snd (CA.po_leaves o5); map snd (CA.po_leaves o6); map snd (CA.po_leaves o7); map snd (CA.po_leaves o8); map snd (CA.po_leaves o9); map snd (CA.po_leaves o10); map snd (CA.po_leaves o11); map snd (CA.po_leaves o12); map snd (CA.po_leaves o13); map snd (CA.po_leaves o14); map snd (CA.po_leaves o15); map snd (CA.po_leaves o16); map snd (CA.po_leaves o17); map snd (CA.po_leaves o18); map snd (CA.po_leaves o19); map snd (CA.po_leaves o20); map snd (CA.po_leaves o21); map snd (CA.po_leaves o22); map snd (CA.po_leaves o23); map snd (CA.po_leaves o24); map snd (CA.po_leaves o25); map snd (CA.po_leaves o26); map snd (CA.po_leaves o27); map snd (CA.po_leaves o28); map snd (CA.po_leaves o29); map snd (CA.po_leaves o30); map snd (CA.po_leaves o31); map snd (CA.po_leaves o32); map snd (CA.po_leaves o33); map snd (CA.po_leaves o34); map snd (CA.po_leaves o35); map snd (CA.po_leaves o36); map snd (CA.po_leaves o37); map snd (CA.po_leaves o38); map snd (CA.po_leaves o39); map snd (CA.po_leaves o40); map snd (CA.po_leaves o41); map snd (CA.po_leaves o42); map snd (CA.po_leaves o43); map snd (CA.po_leaves o44); map snd (CA.po_leaves o45); map snd (CA.po_leaves o46); map snd (CA.po_leaves o47); map snd (CA.po_leaves o48); map snd (CA.po_leaves o49); map snd (CA.po_leaves o50); map snd (CA.po_leaves o51); map snd (CA.po_leaves o52); map snd (CA.po_leaves o53); map snd (CA.po_leaves o54); map snd (CA.po_leaves o55); map snd (CA.po_leaves o56); map snd (CA.po_leaves o57); map snd (CA.po_leaves o58); map snd (CA.po_leaves o59); map snd (CA.po_leaves o60); map snd (CA.po_leaves o61); map snd (CA.po_leaves o62); map snd (CA.po_leaves o63)].
Definition BLS : list CA.blocks := [BL0; BL1; BL2; BL3; BL4; BL5; BL6; BL7; BL8; BL9; BL10; BL11; BL12; BL13; BL14; BL15; BL16; BL17; BL18; BL19; BL20; BL21; BL22; BL23; BL24; BL25; BL26; BL27; BL28; BL29; BL30; BL31; BL32; BL33; BL34; BL35; BL36; BL37; BL38; BL39; BL40; BL41; BL42; BL43; BL44; BL45; BL46; BL47; BL48; BL49; BL50; BL51; BL52; BL53; BL54; BL55; BL56; BL57; BL58; BL59; BL60; BL61; BL62; BL63].
Definition HDECL := Cut_pr_cboth_T.HDECL.

Definition RETS : list (nat * nat * nat * Z) := [(40%nat, 15%nat, 0%nat, 1363704); (41%nat, 17%nat, 0%nat, 1363704); (42%nat, 21%nat, 0%nat, 1363704); (43%nat, 22%nat, 0%nat, 1363704); (44%nat, 25%nat, 0%nat, 1363704); (45%nat, 26%nat, 0%nat, 1363704); (46%nat, 28%nat, 0%nat, 1363704); (47%nat, 30%nat, 0%nat, 1363704); (48%nat, 32%nat, 1%nat, 1363704); (49%nat, 32%nat, 3%nat, 1363704); (50%nat, 34%nat, 0%nat, 1363704); (51%nat, 36%nat, 0%nat, 1363704); (52%nat, 40%nat, 0%nat, 520748); (53%nat, 41%nat, 0%nat, 520748); (54%nat, 42%nat, 0%nat, 520748); (55%nat, 43%nat, 0%nat, 520748); (56%nat, 44%nat, 0%nat, 520748); (57%nat, 45%nat, 0%nat, 520748); (58%nat, 46%nat, 0%nat, 520748); (59%nat, 47%nat, 0%nat, 520748); (60%nat, 48%nat, 0%nat, 520748); (61%nat, 49%nat, 0%nat, 520748); (62%nat, 50%nat, 0%nat, 520748); (63%nat, 51%nat, 0%nat, 520748)].
