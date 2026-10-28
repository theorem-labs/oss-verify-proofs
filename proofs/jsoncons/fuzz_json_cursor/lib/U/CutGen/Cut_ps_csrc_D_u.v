(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSums3C_u.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Import Cut_ps_csrc_T_u Cut_ps_csrc_R0_u Cut_ps_csrc_R1p0_u Cut_ps_csrc_R1p1_u Cut_ps_csrc_R2_u Cut_ps_csrc_R3_u Cut_ps_csrc_R4_u.
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
Definition cp64 : CC.cutpoint := Eval vm_compute in mkcp t64 o64.
Definition cp65 : CC.cutpoint := Eval vm_compute in mkcp t65 o65.
Definition cp66 : CC.cutpoint := Eval vm_compute in mkcp t66 o66.
Definition cp67 : CC.cutpoint := Eval vm_compute in mkcp t67 o67.
Definition cp68 : CC.cutpoint := Eval vm_compute in mkcp t68 o68.
Definition cp69 : CC.cutpoint := Eval vm_compute in mkcp t69 o69.
Definition cp70 : CC.cutpoint := Eval vm_compute in mkcp t70 o70.
Definition cp71 : CC.cutpoint := Eval vm_compute in mkcp t71 o71.
Definition cp72 : CC.cutpoint := Eval vm_compute in mkcp t72 o72.
Definition cp73 : CC.cutpoint := Eval vm_compute in mkcp t73 o73.
Definition cp74 : CC.cutpoint := Eval vm_compute in mkcp t74 o74.
Definition cp75 : CC.cutpoint := Eval vm_compute in mkcp t75 o75.
Definition cp76 : CC.cutpoint := Eval vm_compute in mkcp t76 o76.
Definition cp77 : CC.cutpoint := Eval vm_compute in mkcp t77 o77.
Definition cp78 : CC.cutpoint := Eval vm_compute in mkcp t78 o78.
Definition cp79 : CC.cutpoint := Eval vm_compute in mkcp t79 o79.
Definition cp80 : CC.cutpoint := Eval vm_compute in mkcp t80 o80.
Definition cp81 : CC.cutpoint := Eval vm_compute in mkcp t81 o81.
Definition cp82 : CC.cutpoint := Eval vm_compute in mkcp t82 o82.
Definition cp83 : CC.cutpoint := Eval vm_compute in mkcp t83 o83.
Definition cp84 : CC.cutpoint := Eval vm_compute in mkcp t84 o84.
Definition cp85 : CC.cutpoint := Eval vm_compute in mkcp t85 o85.
Definition cp86 : CC.cutpoint := Eval vm_compute in mkcp t86 o86.
Definition cp87 : CC.cutpoint := Eval vm_compute in mkcp t87 o87.
Definition cp88 : CC.cutpoint := Eval vm_compute in mkcp t88 o88.
Definition cp89 : CC.cutpoint := Eval vm_compute in mkcp t89 o89.
Definition cp90 : CC.cutpoint := Eval vm_compute in mkcp t90 o90.
Definition cp91 : CC.cutpoint := Eval vm_compute in mkcp t91 o91.
Definition cp92 : CC.cutpoint := Eval vm_compute in mkcp t92 o92.
Definition cp93 : CC.cutpoint := Eval vm_compute in mkcp t93 o93.
Definition cp94 : CC.cutpoint := Eval vm_compute in mkcp t94 o94.
Definition cp95 : CC.cutpoint := Eval vm_compute in mkcp t95 o95.
Definition cp96 : CC.cutpoint := Eval vm_compute in mkcp t96 o96.
Definition cp97 : CC.cutpoint := Eval vm_compute in mkcp t97 o97.
Definition cp98 : CC.cutpoint := Eval vm_compute in mkcp t98 o98.
Definition cp99 : CC.cutpoint := Eval vm_compute in mkcp t99 o99.
Definition cp100 : CC.cutpoint := Eval vm_compute in mkcp t100 o100.
Definition cp101 : CC.cutpoint := Eval vm_compute in mkcp t101 o101.
Definition cp102 : CC.cutpoint := Eval vm_compute in mkcp t102 o102.
Definition cp103 : CC.cutpoint := Eval vm_compute in mkcp t103 o103.
Definition cp104 : CC.cutpoint := Eval vm_compute in mkcp t104 o104.
Definition cp105 : CC.cutpoint := Eval vm_compute in mkcp t105 o105.
Definition cp106 : CC.cutpoint := Eval vm_compute in mkcp t106 o106.
Definition cp107 : CC.cutpoint := Eval vm_compute in mkcp t107 o107.
Definition cp108 : CC.cutpoint := Eval vm_compute in mkcp t108 o108.
Definition cp109 : CC.cutpoint := Eval vm_compute in mkcp t109 o109.
Definition cp110 : CC.cutpoint := Eval vm_compute in mkcp t110 o110.
Definition cp111 : CC.cutpoint := Eval vm_compute in mkcp t111 o111.
Definition cp112 : CC.cutpoint := Eval vm_compute in mkcp t112 o112.
Definition cp113 : CC.cutpoint := Eval vm_compute in mkcp t113 o113.
Definition cp114 : CC.cutpoint := Eval vm_compute in mkcp t114 o114.
Definition cp115 : CC.cutpoint := Eval vm_compute in mkcp t115 o115.
Definition cp116 : CC.cutpoint := Eval vm_compute in mkcp t116 o116.
Definition cp117 : CC.cutpoint := Eval vm_compute in mkcp t117 o117.
Definition cp118 : CC.cutpoint := Eval vm_compute in mkcp t118 o118.
Definition cp119 : CC.cutpoint := Eval vm_compute in mkcp t119 o119.
Definition cp120 : CC.cutpoint := Eval vm_compute in mkcp t120 o120.
Definition cp121 : CC.cutpoint := Eval vm_compute in mkcp t121 o121.
Definition cp122 : CC.cutpoint := Eval vm_compute in mkcp t122 o122.
Definition CPS : list CC.cutpoint := [cp0; cp1; cp2; cp3; cp4; cp5; cp6; cp7; cp8; cp9; cp10; cp11; cp12; cp13; cp14; cp15; cp16; cp17; cp18; cp19; cp20; cp21; cp22; cp23; cp24; cp25; cp26; cp27; cp28; cp29; cp30; cp31; cp32; cp33; cp34; cp35; cp36; cp37; cp38; cp39; cp40; cp41; cp42; cp43; cp44; cp45; cp46; cp47; cp48; cp49; cp50; cp51; cp52; cp53; cp54; cp55; cp56; cp57; cp58; cp59; cp60; cp61; cp62; cp63; cp64; cp65; cp66; cp67; cp68; cp69; cp70; cp71; cp72; cp73; cp74; cp75; cp76; cp77; cp78; cp79; cp80; cp81; cp82; cp83; cp84; cp85; cp86; cp87; cp88; cp89; cp90; cp91; cp92; cp93; cp94; cp95; cp96; cp97; cp98; cp99; cp100; cp101; cp102; cp103; cp104; cp105; cp106; cp107; cp108; cp109; cp110; cp111; cp112; cp113; cp114; cp115; cp116; cp117; cp118; cp119; cp120; cp121; cp122].
Definition TAGS : list (list CC.tag) := Eval vm_compute in [map snd (CA.po_leaves o0); map snd (CA.po_leaves o1); map snd (CA.po_leaves o2); map snd (CA.po_leaves o3); map snd (CA.po_leaves o4); map snd (CA.po_leaves o5); map snd (CA.po_leaves o6); map snd (CA.po_leaves o7); map snd (CA.po_leaves o8); map snd (CA.po_leaves o9); map snd (CA.po_leaves o10); map snd (CA.po_leaves o11); map snd (CA.po_leaves o12); map snd (CA.po_leaves o13); map snd (CA.po_leaves o14); map snd (CA.po_leaves o15); map snd (CA.po_leaves o16); map snd (CA.po_leaves o17); map snd (CA.po_leaves o18); map snd (CA.po_leaves o19); map snd (CA.po_leaves o20); map snd (CA.po_leaves o21); map snd (CA.po_leaves o22); map snd (CA.po_leaves o23); map snd (CA.po_leaves o24); map snd (CA.po_leaves o25); map snd (CA.po_leaves o26); map snd (CA.po_leaves o27); map snd (CA.po_leaves o28); map snd (CA.po_leaves o29); map snd (CA.po_leaves o30); map snd (CA.po_leaves o31); map snd (CA.po_leaves o32); map snd (CA.po_leaves o33); map snd (CA.po_leaves o34); map snd (CA.po_leaves o35); map snd (CA.po_leaves o36); map snd (CA.po_leaves o37); map snd (CA.po_leaves o38); map snd (CA.po_leaves o39); map snd (CA.po_leaves o40); map snd (CA.po_leaves o41); map snd (CA.po_leaves o42); map snd (CA.po_leaves o43); map snd (CA.po_leaves o44); map snd (CA.po_leaves o45); map snd (CA.po_leaves o46); map snd (CA.po_leaves o47); map snd (CA.po_leaves o48); map snd (CA.po_leaves o49); map snd (CA.po_leaves o50); map snd (CA.po_leaves o51); map snd (CA.po_leaves o52); map snd (CA.po_leaves o53); map snd (CA.po_leaves o54); map snd (CA.po_leaves o55); map snd (CA.po_leaves o56); map snd (CA.po_leaves o57); map snd (CA.po_leaves o58); map snd (CA.po_leaves o59); map snd (CA.po_leaves o60); map snd (CA.po_leaves o61); map snd (CA.po_leaves o62); map snd (CA.po_leaves o63); map snd (CA.po_leaves o64); map snd (CA.po_leaves o65); map snd (CA.po_leaves o66); map snd (CA.po_leaves o67); map snd (CA.po_leaves o68); map snd (CA.po_leaves o69); map snd (CA.po_leaves o70); map snd (CA.po_leaves o71); map snd (CA.po_leaves o72); map snd (CA.po_leaves o73); map snd (CA.po_leaves o74); map snd (CA.po_leaves o75); map snd (CA.po_leaves o76); map snd (CA.po_leaves o77); map snd (CA.po_leaves o78); map snd (CA.po_leaves o79); map snd (CA.po_leaves o80); map snd (CA.po_leaves o81); map snd (CA.po_leaves o82); map snd (CA.po_leaves o83); map snd (CA.po_leaves o84); map snd (CA.po_leaves o85); map snd (CA.po_leaves o86); map snd (CA.po_leaves o87); map snd (CA.po_leaves o88); map snd (CA.po_leaves o89); map snd (CA.po_leaves o90); map snd (CA.po_leaves o91); map snd (CA.po_leaves o92); map snd (CA.po_leaves o93); map snd (CA.po_leaves o94); map snd (CA.po_leaves o95); map snd (CA.po_leaves o96); map snd (CA.po_leaves o97); map snd (CA.po_leaves o98); map snd (CA.po_leaves o99); map snd (CA.po_leaves o100); map snd (CA.po_leaves o101); map snd (CA.po_leaves o102); map snd (CA.po_leaves o103); map snd (CA.po_leaves o104); map snd (CA.po_leaves o105); map snd (CA.po_leaves o106); map snd (CA.po_leaves o107); map snd (CA.po_leaves o108); map snd (CA.po_leaves o109); map snd (CA.po_leaves o110); map snd (CA.po_leaves o111); map snd (CA.po_leaves o112); map snd (CA.po_leaves o113); map snd (CA.po_leaves o114); map snd (CA.po_leaves o115); map snd (CA.po_leaves o116); map snd (CA.po_leaves o117); map snd (CA.po_leaves o118); map snd (CA.po_leaves o119); map snd (CA.po_leaves o120); map snd (CA.po_leaves o121); map snd (CA.po_leaves o122)].
Definition BLS : list CA.blocks := [BL0; BL1; BL2; BL3; BL4; BL5; BL6; BL7; BL8; BL9; BL10; BL11; BL12; BL13; BL14; BL15; BL16; BL17; BL18; BL19; BL20; BL21; BL22; BL23; BL24; BL25; BL26; BL27; BL28; BL29; BL30; BL31; BL32; BL33; BL34; BL35; BL36; BL37; BL38; BL39; BL40; BL41; BL42; BL43; BL44; BL45; BL46; BL47; BL48; BL49; BL50; BL51; BL52; BL53; BL54; BL55; BL56; BL57; BL58; BL59; BL60; BL61; BL62; BL63; BL64; BL65; BL66; BL67; BL68; BL69; BL70; BL71; BL72; BL73; BL74; BL75; BL76; BL77; BL78; BL79; BL80; BL81; BL82; BL83; BL84; BL85; BL86; BL87; BL88; BL89; BL90; BL91; BL92; BL93; BL94; BL95; BL96; BL97; BL98; BL99; BL100; BL101; BL102; BL103; BL104; BL105; BL106; BL107; BL108; BL109; BL110; BL111; BL112; BL113; BL114; BL115; BL116; BL117; BL118; BL119; BL120; BL121; BL122].
Definition HDECL := Cut_ps_csrc_T_u.HDECL.

Definition RETS : list (nat * nat * nat * Z) := [(14%nat, 1%nat, 0%nat, 409688); (15%nat, 1%nat, 1%nat, 409688); (16%nat, 1%nat, 3%nat, 260908); (17%nat, 1%nat, 4%nat, 409688); (18%nat, 1%nat, 5%nat, 409688); (19%nat, 1%nat, 7%nat, 245820); (20%nat, 1%nat, 8%nat, 245820); (21%nat, 2%nat, 1%nat, 409688); (22%nat, 3%nat, 0%nat, 410272); (23%nat, 3%nat, 1%nat, 410272); (24%nat, 3%nat, 3%nat, 245820); (25%nat, 3%nat, 4%nat, 410272); (26%nat, 3%nat, 5%nat, 410272); (27%nat, 3%nat, 6%nat, 245820); (28%nat, 3%nat, 7%nat, 410272); (29%nat, 3%nat, 8%nat, 410272); (30%nat, 3%nat, 9%nat, 245820); (31%nat, 3%nat, 10%nat, 410272); (32%nat, 3%nat, 11%nat, 410272); (33%nat, 3%nat, 12%nat, 245820); (34%nat, 4%nat, 0%nat, 245820); (35%nat, 5%nat, 0%nat, 245820); (36%nat, 6%nat, 0%nat, 245820); (37%nat, 7%nat, 0%nat, 245820); (38%nat, 7%nat, 3%nat, 410272); (39%nat, 7%nat, 4%nat, 410272); (40%nat, 7%nat, 5%nat, 410272); (41%nat, 7%nat, 6%nat, 410272); (42%nat, 7%nat, 7%nat, 410272); (43%nat, 7%nat, 10%nat, 410272); (44%nat, 7%nat, 11%nat, 410272); (45%nat, 7%nat, 12%nat, 410272); (46%nat, 7%nat, 13%nat, 410272); (47%nat, 7%nat, 14%nat, 410272); (48%nat, 7%nat, 17%nat, 410272); (49%nat, 7%nat, 18%nat, 410272); (50%nat, 7%nat, 19%nat, 410272); (51%nat, 7%nat, 20%nat, 410272); (52%nat, 7%nat, 21%nat, 410272); (53%nat, 8%nat, 1%nat, 245820); (54%nat, 9%nat, 1%nat, 245820); (55%nat, 10%nat, 0%nat, 245820); (56%nat, 11%nat, 0%nat, 245820); (57%nat, 12%nat, 0%nat, 245820); (58%nat, 13%nat, 0%nat, 245820); (59%nat, 13%nat, 2%nat, 410272); (60%nat, 13%nat, 3%nat, 410272); (61%nat, 13%nat, 4%nat, 410272); (62%nat, 13%nat, 5%nat, 410272); (63%nat, 13%nat, 6%nat, 410272); (64%nat, 13%nat, 8%nat, 410272); (65%nat, 13%nat, 9%nat, 410272); (66%nat, 13%nat, 10%nat, 410272); (67%nat, 13%nat, 11%nat, 410272); (68%nat, 13%nat, 12%nat, 410272); (69%nat, 13%nat, 14%nat, 410272); (70%nat, 13%nat, 15%nat, 410272); (71%nat, 13%nat, 16%nat, 410272); (72%nat, 13%nat, 17%nat, 410272); (73%nat, 13%nat, 18%nat, 410272); (74%nat, 17%nat, 0%nat, 260908); (75%nat, 39%nat, 0%nat, 410272); (76%nat, 40%nat, 0%nat, 410272); (77%nat, 41%nat, 0%nat, 410272); (78%nat, 42%nat, 0%nat, 410272); (79%nat, 44%nat, 0%nat, 410272); (80%nat, 45%nat, 0%nat, 410272); (81%nat, 46%nat, 0%nat, 410272); (82%nat, 47%nat, 0%nat, 410272); (83%nat, 49%nat, 0%nat, 410272); (84%nat, 50%nat, 0%nat, 410272); (85%nat, 51%nat, 0%nat, 410272); (86%nat, 52%nat, 0%nat, 410272); (87%nat, 60%nat, 0%nat, 410272); (88%nat, 61%nat, 0%nat, 410272); (89%nat, 62%nat, 0%nat, 410272); (90%nat, 63%nat, 0%nat, 410272); (91%nat, 65%nat, 0%nat, 410272); (92%nat, 66%nat, 0%nat, 410272); (93%nat, 67%nat, 0%nat, 410272); (94%nat, 68%nat, 0%nat, 410272); (95%nat, 70%nat, 0%nat, 410272); (96%nat, 71%nat, 0%nat, 410272); (97%nat, 72%nat, 0%nat, 410272); (98%nat, 73%nat, 0%nat, 410272); (99%nat, 76%nat, 0%nat, 410272); (100%nat, 77%nat, 0%nat, 410272); (101%nat, 78%nat, 0%nat, 410272); (102%nat, 80%nat, 0%nat, 410272); (103%nat, 81%nat, 0%nat, 410272); (104%nat, 82%nat, 0%nat, 410272); (105%nat, 84%nat, 0%nat, 410272); (106%nat, 85%nat, 0%nat, 410272); (107%nat, 86%nat, 0%nat, 410272); (108%nat, 88%nat, 0%nat, 410272); (109%nat, 89%nat, 0%nat, 410272); (110%nat, 90%nat, 0%nat, 410272); (111%nat, 92%nat, 0%nat, 410272); (112%nat, 93%nat, 0%nat, 410272); (113%nat, 94%nat, 0%nat, 410272); (114%nat, 96%nat, 0%nat, 410272); (115%nat, 97%nat, 0%nat, 410272); (116%nat, 98%nat, 0%nat, 410272); (117%nat, 101%nat, 0%nat, 410272); (118%nat, 104%nat, 0%nat, 410272); (119%nat, 107%nat, 0%nat, 410272); (120%nat, 110%nat, 0%nat, 410272); (121%nat, 113%nat, 0%nat, 410272); (122%nat, 116%nat, 0%nat, 410272)].
