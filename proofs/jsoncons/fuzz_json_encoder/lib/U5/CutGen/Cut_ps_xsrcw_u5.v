(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSums_u5 ParseSums2_u5 ParseSums2X_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import VisitSumsX.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Import Cut_ps_xsrcw_T_u5 Cut_ps_xsrcw_R0_u5 Cut_ps_xsrcw_R1_u5 Cut_ps_xsrcw_R2_u5 Cut_ps_xsrcw_R3_u5 Cut_ps_xsrcw_R4_u5.
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
Definition HDECL := Cut_ps_xsrcw_T_u5.HDECL.
Definition RETS : list (nat * nat * nat * Z) := [(14%nat, 1%nat, 0%nat, 436288); (15%nat, 1%nat, 1%nat, 436288); (16%nat, 1%nat, 3%nat, 306400); (17%nat, 1%nat, 4%nat, 436288); (18%nat, 1%nat, 5%nat, 436288); (19%nat, 1%nat, 7%nat, 284948); (20%nat, 1%nat, 8%nat, 284948); (21%nat, 2%nat, 1%nat, 436288); (22%nat, 3%nat, 0%nat, 436872); (23%nat, 3%nat, 1%nat, 436872); (24%nat, 3%nat, 3%nat, 284948); (25%nat, 3%nat, 4%nat, 436872); (26%nat, 3%nat, 5%nat, 436872); (27%nat, 3%nat, 6%nat, 284948); (28%nat, 3%nat, 7%nat, 436872); (29%nat, 3%nat, 8%nat, 436872); (30%nat, 3%nat, 9%nat, 284948); (31%nat, 3%nat, 10%nat, 436872); (32%nat, 3%nat, 11%nat, 436872); (33%nat, 3%nat, 12%nat, 284948); (34%nat, 4%nat, 0%nat, 284948); (35%nat, 5%nat, 0%nat, 284948); (36%nat, 6%nat, 0%nat, 284948); (37%nat, 7%nat, 0%nat, 284948); (38%nat, 7%nat, 3%nat, 436872); (39%nat, 7%nat, 4%nat, 436872); (40%nat, 7%nat, 5%nat, 436872); (41%nat, 7%nat, 6%nat, 436872); (42%nat, 7%nat, 7%nat, 436872); (43%nat, 7%nat, 10%nat, 436872); (44%nat, 7%nat, 11%nat, 436872); (45%nat, 7%nat, 12%nat, 436872); (46%nat, 7%nat, 13%nat, 436872); (47%nat, 7%nat, 14%nat, 436872); (48%nat, 7%nat, 17%nat, 436872); (49%nat, 7%nat, 18%nat, 436872); (50%nat, 7%nat, 19%nat, 436872); (51%nat, 7%nat, 20%nat, 436872); (52%nat, 7%nat, 21%nat, 436872); (53%nat, 8%nat, 1%nat, 284948); (54%nat, 9%nat, 1%nat, 284948); (55%nat, 10%nat, 0%nat, 284948); (56%nat, 11%nat, 0%nat, 284948); (57%nat, 12%nat, 0%nat, 284948); (58%nat, 13%nat, 0%nat, 284948); (59%nat, 13%nat, 2%nat, 436872); (60%nat, 13%nat, 3%nat, 436872); (61%nat, 13%nat, 4%nat, 436872); (62%nat, 13%nat, 5%nat, 436872); (63%nat, 13%nat, 6%nat, 436872); (64%nat, 13%nat, 8%nat, 436872); (65%nat, 13%nat, 9%nat, 436872); (66%nat, 13%nat, 10%nat, 436872); (67%nat, 13%nat, 11%nat, 436872); (68%nat, 13%nat, 12%nat, 436872); (69%nat, 13%nat, 14%nat, 436872); (70%nat, 13%nat, 15%nat, 436872); (71%nat, 13%nat, 16%nat, 436872); (72%nat, 13%nat, 17%nat, 436872); (73%nat, 13%nat, 18%nat, 436872); (74%nat, 17%nat, 0%nat, 306400); (75%nat, 39%nat, 0%nat, 436872); (76%nat, 40%nat, 0%nat, 436872); (77%nat, 41%nat, 0%nat, 436872); (78%nat, 42%nat, 0%nat, 436872); (79%nat, 44%nat, 0%nat, 436872); (80%nat, 45%nat, 0%nat, 436872); (81%nat, 46%nat, 0%nat, 436872); (82%nat, 47%nat, 0%nat, 436872); (83%nat, 49%nat, 0%nat, 436872); (84%nat, 50%nat, 0%nat, 436872); (85%nat, 51%nat, 0%nat, 436872); (86%nat, 52%nat, 0%nat, 436872); (87%nat, 60%nat, 0%nat, 436872); (88%nat, 61%nat, 0%nat, 436872); (89%nat, 62%nat, 0%nat, 436872); (90%nat, 63%nat, 0%nat, 436872); (91%nat, 65%nat, 0%nat, 436872); (92%nat, 66%nat, 0%nat, 436872); (93%nat, 67%nat, 0%nat, 436872); (94%nat, 68%nat, 0%nat, 436872); (95%nat, 70%nat, 0%nat, 436872); (96%nat, 71%nat, 0%nat, 436872); (97%nat, 72%nat, 0%nat, 436872); (98%nat, 73%nat, 0%nat, 436872); (99%nat, 76%nat, 0%nat, 436872); (100%nat, 77%nat, 0%nat, 436872); (101%nat, 78%nat, 0%nat, 436872); (102%nat, 80%nat, 0%nat, 436872); (103%nat, 81%nat, 0%nat, 436872); (104%nat, 82%nat, 0%nat, 436872); (105%nat, 84%nat, 0%nat, 436872); (106%nat, 85%nat, 0%nat, 436872); (107%nat, 86%nat, 0%nat, 436872); (108%nat, 88%nat, 0%nat, 436872); (109%nat, 89%nat, 0%nat, 436872); (110%nat, 90%nat, 0%nat, 436872); (111%nat, 92%nat, 0%nat, 436872); (112%nat, 93%nat, 0%nat, 436872); (113%nat, 94%nat, 0%nat, 436872); (114%nat, 96%nat, 0%nat, 436872); (115%nat, 97%nat, 0%nat, 436872); (116%nat, 98%nat, 0%nat, 436872); (117%nat, 101%nat, 0%nat, 436872); (118%nat, 104%nat, 0%nat, 436872); (119%nat, 107%nat, 0%nat, 436872); (120%nat, 110%nat, 0%nat, 436872); (121%nat, 113%nat, 0%nat, 436872); (122%nat, 116%nat, 0%nat, 436872)].
Lemma cert0 : src0_cut_cert ITR BF cp0 (CA.po_ops o0) (CA.po_ops2 o0) (CA.po_plan o0) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert1 : src0_cut_cert ITR BF cp1 (CA.po_ops o1) (CA.po_ops2 o1) (CA.po_plan o1) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert2 : src0_cut_cert ITR BF cp2 (CA.po_ops o2) (CA.po_ops2 o2) (CA.po_plan o2) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert3 : src0_cut_cert ITR BF cp3 (CA.po_ops o3) (CA.po_ops2 o3) (CA.po_plan o3) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert4 : src0_cut_cert ITR BF cp4 (CA.po_ops o4) (CA.po_ops2 o4) (CA.po_plan o4) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert5 : src0_cut_cert ITR BF cp5 (CA.po_ops o5) (CA.po_ops2 o5) (CA.po_plan o5) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert6 : src0_cut_cert ITR BF cp6 (CA.po_ops o6) (CA.po_ops2 o6) (CA.po_plan o6) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert7 : src0_cut_cert ITR BF cp7 (CA.po_ops o7) (CA.po_ops2 o7) (CA.po_plan o7) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert8 : src0_cut_cert ITR BF cp8 (CA.po_ops o8) (CA.po_ops2 o8) (CA.po_plan o8) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert9 : src0_cut_cert ITR BF cp9 (CA.po_ops o9) (CA.po_ops2 o9) (CA.po_plan o9) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert10 : src0_cut_cert ITR BF cp10 (CA.po_ops o10) (CA.po_ops2 o10) (CA.po_plan o10) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert11 : src0_cut_cert ITR BF cp11 (CA.po_ops o11) (CA.po_ops2 o11) (CA.po_plan o11) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert12 : src0_cut_cert ITR BF cp12 (CA.po_ops o12) (CA.po_ops2 o12) (CA.po_plan o12) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert13 : src0_cut_cert ITR BF cp13 (CA.po_ops o13) (CA.po_ops2 o13) (CA.po_plan o13) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert14 : src0_cut_cert ITR BF cp14 (CA.po_ops o14) (CA.po_ops2 o14) (CA.po_plan o14) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert15 : src0_cut_cert ITR BF cp15 (CA.po_ops o15) (CA.po_ops2 o15) (CA.po_plan o15) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert16 : src0_cut_cert ITR BF cp16 (CA.po_ops o16) (CA.po_ops2 o16) (CA.po_plan o16) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert17 : src0_cut_cert ITR BF cp17 (CA.po_ops o17) (CA.po_ops2 o17) (CA.po_plan o17) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert18 : src0_cut_cert ITR BF cp18 (CA.po_ops o18) (CA.po_ops2 o18) (CA.po_plan o18) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert19 : src0_cut_cert ITR BF cp19 (CA.po_ops o19) (CA.po_ops2 o19) (CA.po_plan o19) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert20 : src0_cut_cert ITR BF cp20 (CA.po_ops o20) (CA.po_ops2 o20) (CA.po_plan o20) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert21 : src0_cut_cert ITR BF cp21 (CA.po_ops o21) (CA.po_ops2 o21) (CA.po_plan o21) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert22 : src0_cut_cert ITR BF cp22 (CA.po_ops o22) (CA.po_ops2 o22) (CA.po_plan o22) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert23 : src0_cut_cert ITR BF cp23 (CA.po_ops o23) (CA.po_ops2 o23) (CA.po_plan o23) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert24 : src0_cut_cert ITR BF cp24 (CA.po_ops o24) (CA.po_ops2 o24) (CA.po_plan o24) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert25 : src0_cut_cert ITR BF cp25 (CA.po_ops o25) (CA.po_ops2 o25) (CA.po_plan o25) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert26 : src0_cut_cert ITR BF cp26 (CA.po_ops o26) (CA.po_ops2 o26) (CA.po_plan o26) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert27 : src0_cut_cert ITR BF cp27 (CA.po_ops o27) (CA.po_ops2 o27) (CA.po_plan o27) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert28 : src0_cut_cert ITR BF cp28 (CA.po_ops o28) (CA.po_ops2 o28) (CA.po_plan o28) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert29 : src0_cut_cert ITR BF cp29 (CA.po_ops o29) (CA.po_ops2 o29) (CA.po_plan o29) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert30 : src0_cut_cert ITR BF cp30 (CA.po_ops o30) (CA.po_ops2 o30) (CA.po_plan o30) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert31 : src0_cut_cert ITR BF cp31 (CA.po_ops o31) (CA.po_ops2 o31) (CA.po_plan o31) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert32 : src0_cut_cert ITR BF cp32 (CA.po_ops o32) (CA.po_ops2 o32) (CA.po_plan o32) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert33 : src0_cut_cert ITR BF cp33 (CA.po_ops o33) (CA.po_ops2 o33) (CA.po_plan o33) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert34 : src0_cut_cert ITR BF cp34 (CA.po_ops o34) (CA.po_ops2 o34) (CA.po_plan o34) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert35 : src0_cut_cert ITR BF cp35 (CA.po_ops o35) (CA.po_ops2 o35) (CA.po_plan o35) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert36 : src0_cut_cert ITR BF cp36 (CA.po_ops o36) (CA.po_ops2 o36) (CA.po_plan o36) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert37 : src0_cut_cert ITR BF cp37 (CA.po_ops o37) (CA.po_ops2 o37) (CA.po_plan o37) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert38 : src0_cut_cert ITR BF cp38 (CA.po_ops o38) (CA.po_ops2 o38) (CA.po_plan o38) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert39 : src0_cut_cert ITR BF cp39 (CA.po_ops o39) (CA.po_ops2 o39) (CA.po_plan o39) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert40 : src0_cut_cert ITR BF cp40 (CA.po_ops o40) (CA.po_ops2 o40) (CA.po_plan o40) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert41 : src0_cut_cert ITR BF cp41 (CA.po_ops o41) (CA.po_ops2 o41) (CA.po_plan o41) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert42 : src0_cut_cert ITR BF cp42 (CA.po_ops o42) (CA.po_ops2 o42) (CA.po_plan o42) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert43 : src0_cut_cert ITR BF cp43 (CA.po_ops o43) (CA.po_ops2 o43) (CA.po_plan o43) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert44 : src0_cut_cert ITR BF cp44 (CA.po_ops o44) (CA.po_ops2 o44) (CA.po_plan o44) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert45 : src0_cut_cert ITR BF cp45 (CA.po_ops o45) (CA.po_ops2 o45) (CA.po_plan o45) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert46 : src0_cut_cert ITR BF cp46 (CA.po_ops o46) (CA.po_ops2 o46) (CA.po_plan o46) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert47 : src0_cut_cert ITR BF cp47 (CA.po_ops o47) (CA.po_ops2 o47) (CA.po_plan o47) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert48 : src0_cut_cert ITR BF cp48 (CA.po_ops o48) (CA.po_ops2 o48) (CA.po_plan o48) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert49 : src0_cut_cert ITR BF cp49 (CA.po_ops o49) (CA.po_ops2 o49) (CA.po_plan o49) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert50 : src0_cut_cert ITR BF cp50 (CA.po_ops o50) (CA.po_ops2 o50) (CA.po_plan o50) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert51 : src0_cut_cert ITR BF cp51 (CA.po_ops o51) (CA.po_ops2 o51) (CA.po_plan o51) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert52 : src0_cut_cert ITR BF cp52 (CA.po_ops o52) (CA.po_ops2 o52) (CA.po_plan o52) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert53 : src0_cut_cert ITR BF cp53 (CA.po_ops o53) (CA.po_ops2 o53) (CA.po_plan o53) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert54 : src0_cut_cert ITR BF cp54 (CA.po_ops o54) (CA.po_ops2 o54) (CA.po_plan o54) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert55 : src0_cut_cert ITR BF cp55 (CA.po_ops o55) (CA.po_ops2 o55) (CA.po_plan o55) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert56 : src0_cut_cert ITR BF cp56 (CA.po_ops o56) (CA.po_ops2 o56) (CA.po_plan o56) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert57 : src0_cut_cert ITR BF cp57 (CA.po_ops o57) (CA.po_ops2 o57) (CA.po_plan o57) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert58 : src0_cut_cert ITR BF cp58 (CA.po_ops o58) (CA.po_ops2 o58) (CA.po_plan o58) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert59 : src0_cut_cert ITR BF cp59 (CA.po_ops o59) (CA.po_ops2 o59) (CA.po_plan o59) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert60 : src0_cut_cert ITR BF cp60 (CA.po_ops o60) (CA.po_ops2 o60) (CA.po_plan o60) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert61 : src0_cut_cert ITR BF cp61 (CA.po_ops o61) (CA.po_ops2 o61) (CA.po_plan o61) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert62 : src0_cut_cert ITR BF cp62 (CA.po_ops o62) (CA.po_ops2 o62) (CA.po_plan o62) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert63 : src0_cut_cert ITR BF cp63 (CA.po_ops o63) (CA.po_ops2 o63) (CA.po_plan o63) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert64 : src0_cut_cert ITR BF cp64 (CA.po_ops o64) (CA.po_ops2 o64) (CA.po_plan o64) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert65 : src0_cut_cert ITR BF cp65 (CA.po_ops o65) (CA.po_ops2 o65) (CA.po_plan o65) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert66 : src0_cut_cert ITR BF cp66 (CA.po_ops o66) (CA.po_ops2 o66) (CA.po_plan o66) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert67 : src0_cut_cert ITR BF cp67 (CA.po_ops o67) (CA.po_ops2 o67) (CA.po_plan o67) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert68 : src0_cut_cert ITR BF cp68 (CA.po_ops o68) (CA.po_ops2 o68) (CA.po_plan o68) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert69 : src0_cut_cert ITR BF cp69 (CA.po_ops o69) (CA.po_ops2 o69) (CA.po_plan o69) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert70 : src0_cut_cert ITR BF cp70 (CA.po_ops o70) (CA.po_ops2 o70) (CA.po_plan o70) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert71 : src0_cut_cert ITR BF cp71 (CA.po_ops o71) (CA.po_ops2 o71) (CA.po_plan o71) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert72 : src0_cut_cert ITR BF cp72 (CA.po_ops o72) (CA.po_ops2 o72) (CA.po_plan o72) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert73 : src0_cut_cert ITR BF cp73 (CA.po_ops o73) (CA.po_ops2 o73) (CA.po_plan o73) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert74 : src0_cut_cert ITR BF cp74 (CA.po_ops o74) (CA.po_ops2 o74) (CA.po_plan o74) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert75 : src0_cut_cert ITR BF cp75 (CA.po_ops o75) (CA.po_ops2 o75) (CA.po_plan o75) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert76 : src0_cut_cert ITR BF cp76 (CA.po_ops o76) (CA.po_ops2 o76) (CA.po_plan o76) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert77 : src0_cut_cert ITR BF cp77 (CA.po_ops o77) (CA.po_ops2 o77) (CA.po_plan o77) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert78 : src0_cut_cert ITR BF cp78 (CA.po_ops o78) (CA.po_ops2 o78) (CA.po_plan o78) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert79 : src0_cut_cert ITR BF cp79 (CA.po_ops o79) (CA.po_ops2 o79) (CA.po_plan o79) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert80 : src0_cut_cert ITR BF cp80 (CA.po_ops o80) (CA.po_ops2 o80) (CA.po_plan o80) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert81 : src0_cut_cert ITR BF cp81 (CA.po_ops o81) (CA.po_ops2 o81) (CA.po_plan o81) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert82 : src0_cut_cert ITR BF cp82 (CA.po_ops o82) (CA.po_ops2 o82) (CA.po_plan o82) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert83 : src0_cut_cert ITR BF cp83 (CA.po_ops o83) (CA.po_ops2 o83) (CA.po_plan o83) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert84 : src0_cut_cert ITR BF cp84 (CA.po_ops o84) (CA.po_ops2 o84) (CA.po_plan o84) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert85 : src0_cut_cert ITR BF cp85 (CA.po_ops o85) (CA.po_ops2 o85) (CA.po_plan o85) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert86 : src0_cut_cert ITR BF cp86 (CA.po_ops o86) (CA.po_ops2 o86) (CA.po_plan o86) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert87 : src0_cut_cert ITR BF cp87 (CA.po_ops o87) (CA.po_ops2 o87) (CA.po_plan o87) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert88 : src0_cut_cert ITR BF cp88 (CA.po_ops o88) (CA.po_ops2 o88) (CA.po_plan o88) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert89 : src0_cut_cert ITR BF cp89 (CA.po_ops o89) (CA.po_ops2 o89) (CA.po_plan o89) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert90 : src0_cut_cert ITR BF cp90 (CA.po_ops o90) (CA.po_ops2 o90) (CA.po_plan o90) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert91 : src0_cut_cert ITR BF cp91 (CA.po_ops o91) (CA.po_ops2 o91) (CA.po_plan o91) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert92 : src0_cut_cert ITR BF cp92 (CA.po_ops o92) (CA.po_ops2 o92) (CA.po_plan o92) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert93 : src0_cut_cert ITR BF cp93 (CA.po_ops o93) (CA.po_ops2 o93) (CA.po_plan o93) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert94 : src0_cut_cert ITR BF cp94 (CA.po_ops o94) (CA.po_ops2 o94) (CA.po_plan o94) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert95 : src0_cut_cert ITR BF cp95 (CA.po_ops o95) (CA.po_ops2 o95) (CA.po_plan o95) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert96 : src0_cut_cert ITR BF cp96 (CA.po_ops o96) (CA.po_ops2 o96) (CA.po_plan o96) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert97 : src0_cut_cert ITR BF cp97 (CA.po_ops o97) (CA.po_ops2 o97) (CA.po_plan o97) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert98 : src0_cut_cert ITR BF cp98 (CA.po_ops o98) (CA.po_ops2 o98) (CA.po_plan o98) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert99 : src0_cut_cert ITR BF cp99 (CA.po_ops o99) (CA.po_ops2 o99) (CA.po_plan o99) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert100 : src0_cut_cert ITR BF cp100 (CA.po_ops o100) (CA.po_ops2 o100) (CA.po_plan o100) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert101 : src0_cut_cert ITR BF cp101 (CA.po_ops o101) (CA.po_ops2 o101) (CA.po_plan o101) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert102 : src0_cut_cert ITR BF cp102 (CA.po_ops o102) (CA.po_ops2 o102) (CA.po_plan o102) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert103 : src0_cut_cert ITR BF cp103 (CA.po_ops o103) (CA.po_ops2 o103) (CA.po_plan o103) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert104 : src0_cut_cert ITR BF cp104 (CA.po_ops o104) (CA.po_ops2 o104) (CA.po_plan o104) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert105 : src0_cut_cert ITR BF cp105 (CA.po_ops o105) (CA.po_ops2 o105) (CA.po_plan o105) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert106 : src0_cut_cert ITR BF cp106 (CA.po_ops o106) (CA.po_ops2 o106) (CA.po_plan o106) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert107 : src0_cut_cert ITR BF cp107 (CA.po_ops o107) (CA.po_ops2 o107) (CA.po_plan o107) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert108 : src0_cut_cert ITR BF cp108 (CA.po_ops o108) (CA.po_ops2 o108) (CA.po_plan o108) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert109 : src0_cut_cert ITR BF cp109 (CA.po_ops o109) (CA.po_ops2 o109) (CA.po_plan o109) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert110 : src0_cut_cert ITR BF cp110 (CA.po_ops o110) (CA.po_ops2 o110) (CA.po_plan o110) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert111 : src0_cut_cert ITR BF cp111 (CA.po_ops o111) (CA.po_ops2 o111) (CA.po_plan o111) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert112 : src0_cut_cert ITR BF cp112 (CA.po_ops o112) (CA.po_ops2 o112) (CA.po_plan o112) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert113 : src0_cut_cert ITR BF cp113 (CA.po_ops o113) (CA.po_ops2 o113) (CA.po_plan o113) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert114 : src0_cut_cert ITR BF cp114 (CA.po_ops o114) (CA.po_ops2 o114) (CA.po_plan o114) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert115 : src0_cut_cert ITR BF cp115 (CA.po_ops o115) (CA.po_ops2 o115) (CA.po_plan o115) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert116 : src0_cut_cert ITR BF cp116 (CA.po_ops o116) (CA.po_ops2 o116) (CA.po_plan o116) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert117 : src0_cut_cert ITR BF cp117 (CA.po_ops o117) (CA.po_ops2 o117) (CA.po_plan o117) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert118 : src0_cut_cert ITR BF cp118 (CA.po_ops o118) (CA.po_ops2 o118) (CA.po_plan o118) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert119 : src0_cut_cert ITR BF cp119 (CA.po_ops o119) (CA.po_ops2 o119) (CA.po_plan o119) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert120 : src0_cut_cert ITR BF cp120 (CA.po_ops o120) (CA.po_ops2 o120) (CA.po_plan o120) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert121 : src0_cut_cert ITR BF cp121 (CA.po_ops o121) (CA.po_ops2 o121) (CA.po_plan o121) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert122 : src0_cut_cert ITR BF cp122 (CA.po_ops o122) (CA.po_ops2 o122) (CA.po_plan o122) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma tags_ok : CC.tags_chk CPS TAGS NF = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma plans : forall i c, nth_error CPS i = Some c -> CC.plan_sound RSEGS c.
Proof.
  intros i c H.
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert0)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert1)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert2)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert3)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert4)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert5)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert6)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert7)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert8)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert9)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert10)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert11)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert12)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert13)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert14)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert15)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert16)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert17)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert18)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert19)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert20)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert21)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert22)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert23)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert24)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert25)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert26)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert27)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert28)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert29)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert30)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert31)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert32)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert33)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert34)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert35)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert36)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert37)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert38)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert39)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert40)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert41)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert42)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert43)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert44)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert45)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert46)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert47)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert48)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert49)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert50)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert51)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert52)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert53)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert54)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert55)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert56)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert57)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert58)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert59)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert60)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert61)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert62)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert63)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert64)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert65)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert66)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert67)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert68)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert69)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert70)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert71)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert72)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert73)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert74)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert75)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert76)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert77)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert78)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert79)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert80)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert81)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert82)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert83)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert84)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert85)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert86)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert87)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert88)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert89)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert90)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert91)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert92)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert93)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert94)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert95)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert96)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert97)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert98)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert99)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert100)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert101)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert102)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert103)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert104)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert105)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert106)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert107)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert108)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert109)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert110)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert111)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert112)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert113)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert114)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert115)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert116)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert117)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert118)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert119)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert120)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert121)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert122)|].
  destruct i; discriminate H.
Qed.
Lemma NF_le : forall i c, nth_error CPS i = Some c -> (NF <= CC.cp_nx c)%nat.
Proof.
  assert (X : CC.cps_all CPS (fun _ c => Nat.leb NF (CC.cp_nx c)) = true) by (vm_cast_no_check (@eq_refl bool true)).
  intros i c H. apply Nat.leb_le. exact (CC.cps_all_sound _ _ X i c H).
Qed.
