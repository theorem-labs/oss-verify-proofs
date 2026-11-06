(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CertRefl CxRel CxPlan CxPlanSound CxGlue CxBatch.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import H0PlanImage H0Atable H0Sinv H0CheckG H0Chain H0Chain2 H0Hop H0Batch H0Fam.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import H0Drv H0Sel H0Fam2 K0AS0.
From OSSVerify.Proofs.openssl.hashtable.lib Require K0ADe1 K0AThme1 K0ADe1_1 K0AThme1_1 K0ADe4 K0AThme4 K0ADe4_1 K0AThme4_1 K0ADe5 K0AThme5 K0ADe5_1 K0AThme5_1 K0ADe8 K0AThme8 K0ADe8_1 K0AThme8_1 K0ADe9 K0AThme9 K0ADe9_1 K0AThme9_1 K0ADn10 K0AThmn10 K0ADe12 K0AThme12 K0ADe20 K0AThme20 K0ADf44 K0AThmf44 K0MDe0 K0MThme0 K0MDe2 K0MThme2 K0MDe3 K0MThme3 K0MDe6 K0MThme6 K0MDn7 K0MThmn7 K0MDn11 K0MThmn11 K0MDe13 K0MThme13 K0MDe14 K0MThme14 K0MDe15 K0MThme15 K0MDn16 K0MThmn16 K0MDn17 K0MThmn17 K0MDf19 K0MThmf19 K0MDe21 K0MThme21 K0MDe32 K0MThme32 K0ACDc0 K0ACThmc0 K0ACDc1 K0ACThmc1 K0ACDc2 K0ACThmc2 K0ACDc3 K0ACThmc3 K0SGDs K0SGThms K0SGDs1 K0SGThms1 K0ZGDz K0ZGThmz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.
(* [comment removed for export] *)
Definition HASHF : kentry := KRange (esub (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (ELit 14695981039346656037) (EExt false 0 1 (EAlu Instr.ALU_ADD (EBlob false 3 1 1) (EMd Instr.M_MUL (ELit 256) (EBlob false 3 2 1)))))) (EExt false 1 1 (EAlu Instr.ALU_ADD (EBlob false 3 1 1) (EMd Instr.M_MUL (ELit 256) (EBlob false 3 2 1)))))) (ELit 0))) (ELit 0))) (ELit 0))) (ELit 0))) (ELit 0))) (ELit 0))) (EVar 11)) 0 0.
Definition LIM : Z := 2147483648.
Definition g_K0A_e1 : gsel := GS K0ADe1.N0 K0A_cs [] K0ADe1.a0s
  [LN 13 23; LN 28 28] K0ADe1.leaves
  K0ADe1.ops K0ADe1.shapeB K0ADe1.sC2s false.
Definition g_K0A_e1_1 : gsel := GS K0ADe1_1.N0 K0A_cs [] K0ADe1_1.a0s
  [LN 24 27] K0ADe1_1.leaves
  K0ADe1_1.ops K0ADe1_1.shapeB K0ADe1_1.sC2s false.
Definition g_K0A_e4 : gsel := GS K0ADe4.N0 K0A_cs [] K0ADe4.a0s
  [LN 61 71; LN 76 76] K0ADe4.leaves
  K0ADe4.ops K0ADe4.shapeB K0ADe4.sC2s false.
Definition g_K0A_e4_1 : gsel := GS K0ADe4_1.N0 K0A_cs [] K0ADe4_1.a0s
  [LN 72 75] K0ADe4_1.leaves
  K0ADe4_1.ops K0ADe4_1.shapeB K0ADe4_1.sC2s false.
Definition g_K0A_e5 : gsel := GS K0ADe5.N0 K0A_cs [] K0ADe5.a0s
  [LN 77 87; LN 92 92] K0ADe5.leaves
  K0ADe5.ops K0ADe5.shapeB K0ADe5.sC2s false.
Definition g_K0A_e5_1 : gsel := GS K0ADe5_1.N0 K0A_cs [] K0ADe5_1.a0s
  [LN 88 91] K0ADe5_1.leaves
  K0ADe5_1.ops K0ADe5_1.shapeB K0ADe5_1.sC2s false.
Definition g_K0A_e8 : gsel := GS K0ADe8.N0 K0A_cs [] K0ADe8.a0s
  [LN 125 135; LN 140 140] K0ADe8.leaves
  K0ADe8.ops K0ADe8.shapeB K0ADe8.sC2s false.
Definition g_K0A_e8_1 : gsel := GS K0ADe8_1.N0 K0A_cs [] K0ADe8_1.a0s
  [LN 136 139] K0ADe8_1.leaves
  K0ADe8_1.ops K0ADe8_1.shapeB K0ADe8_1.sC2s false.
Definition g_K0A_e9 : gsel := GS K0ADe9.N0 K0A_cs [] K0ADe9.a0s
  [LN 141 151; LN 156 156] K0ADe9.leaves
  K0ADe9.ops K0ADe9.shapeB K0ADe9.sC2s false.
Definition g_K0A_e9_1 : gsel := GS K0ADe9_1.N0 K0A_cs [] K0ADe9_1.a0s
  [LN 152 155] K0ADe9_1.leaves
  K0ADe9_1.ops K0ADe9_1.shapeB K0ADe9_1.sC2s false.
Definition g_K0A_n10 : gsel := GS K0ADn10.N0 K0A_cs [] K0ADn10.a0s
  [LN 157 172; LN 173 188] K0ADn10.leaves
  K0ADn10.ops K0ADn10.shapeB K0ADn10.sC2s false.
Definition g_K0A_e12 : gsel := GS K0ADe12.N0 K0A_cs [] K0ADe12.a0s
  [LN 237 252; LN 253 268; LN 269 284] K0ADe12.leaves
  K0ADe12.ops K0ADe12.shapeB K0ADe12.sC2s false.
Definition g_K0A_e20 : gsel := GS K0ADe20.N0 K0A_cs [] K0ADe20.a0s
  [LN 1005 1020; LN 1021 1036; LN 1037 1052; LN 1053 1068; LN 1069 1084; LN 1085 1100; LN 1101 1116; LN 1117 1132; LN 1133 1148] K0ADe20.leaves
  K0ADe20.ops K0ADe20.shapeB K0ADe20.sC2s false.
Definition g_K0A_f44 : gsel := GS K0ADf44.N0 K0A_cs [] K0ADf44.a0s
  [LN 65517 65529] K0ADf44.leaves
  K0ADf44.ops K0ADf44.shapeB K0ADf44.sC2s false.
Definition g_K0M_e0 : gsel := GS K0MDe0.N0 K0A_cs [] K0MDe0.a0s
  [LN 11 11; LN 12 12] K0MDe0.leaves
  K0MDe0.ops K0MDe0.shapeB K0MDe0.sC2s false.
Definition g_K0M_e2 : gsel := GS K0MDe2.N0 K0A_cs [] K0MDe2.a0s
  [LN 29 39; LN 40 43; LN 44 44] K0MDe2.leaves
  K0MDe2.ops K0MDe2.shapeB K0MDe2.sC2s false.
Definition g_K0M_e3 : gsel := GS K0MDe3.N0 K0A_cs [] K0MDe3.a0s
  [LN 45 55; LN 56 59; LN 60 60] K0MDe3.leaves
  K0MDe3.ops K0MDe3.shapeB K0MDe3.sC2s false.
Definition g_K0M_e6 : gsel := GS K0MDe6.N0 K0A_cs [] K0MDe6.a0s
  [LN 93 103; LN 104 107; LN 108 108] K0MDe6.leaves
  K0MDe6.ops K0MDe6.shapeB K0MDe6.sC2s false.
Definition g_K0M_n7 : gsel := GS K0MDn7.N0 K0A_cs [] K0MDn7.a0s
  [LN 109 119; LN 120 123; LN 124 124] K0MDn7.leaves
  K0MDn7.ops K0MDn7.shapeB K0MDn7.sC2s false.
Definition g_K0M_n11 : gsel := GS K0MDn11.N0 K0A_cs [] K0MDn11.a0s
  [LN 189 204; LN 205 215; LN 216 219; LN 220 220; LN 221 231; LN 232 235; LN 236 236] K0MDn11.leaves
  K0MDn11.ops K0MDn11.shapeB K0MDn11.sC2s false.
Definition g_K0M_e13 : gsel := GS K0MDe13.N0 K0A_cs [] K0MDe13.a0s
  [LN 285 295; LN 296 299; LN 300 300; LN 301 311; LN 312 315; LN 316 316] K0MDe13.leaves
  K0MDe13.ops K0MDe13.shapeB K0MDe13.sC2s false.
Definition g_K0M_e14 : gsel := GS K0MDe14.N0 K0A_cs [] K0MDe14.a0s
  [LN 317 332; LN 333 348; LN 349 364; LN 365 375; LN 376 379; LN 380 380; LN 381 391; LN 392 395; LN 396 396] K0MDe14.leaves
  K0MDe14.ops K0MDe14.shapeB K0MDe14.sC2s false.
Definition g_K0M_e15 : gsel := GS K0MDe15.N0 K0A_cs [] K0MDe15.a0s
  [LN 397 407; LN 408 411; LN 412 412; LN 413 428; LN 429 444; LN 445 460; LN 461 471; LN 472 475; LN 476 476; LN 477 487; LN 488 491; LN 492 492] K0MDe15.leaves
  K0MDe15.ops K0MDe15.shapeB K0MDe15.sC2s false.
Definition g_K0M_n16 : gsel := GS K0MDn16.N0 K0A_cs [] K0MDn16.a0s
  [LN 493 508; LN 509 524; LN 525 540; LN 541 556; LN 557 567; LN 568 571; LN 572 572] K0MDn16.leaves
  K0MDn16.ops K0MDn16.shapeB K0MDn16.sC2s false.
Definition g_K0M_n17 : gsel := GS K0MDn17.N0 K0A_cs [] K0MDn17.a0s
  [LN 573 588; LN 589 604; LN 605 620; LN 621 631; LN 632 635; LN 636 636; LN 637 652; LN 653 663; LN 664 667; LN 668 668] K0MDn17.leaves
  K0MDn17.ops K0MDn17.shapeB K0MDn17.sC2s false.
Definition g_K0M_f19 : gsel := GS K0MDf19.N0 K0A_cs [] K0MDf19.a0s
  [LN 797 812; LN 813 828; LN 829 844; LN 845 860; LN 861 876; LN 877 892; LN 893 903; LN 904 907; LN 908 908; LN 909 924; LN 925 940; LN 941 956; LN 957 967; LN 968 971; LN 972 972; LN 973 988; LN 989 999; LN 1000 1003; LN 1004 1004] K0MDf19.leaves
  K0MDf19.ops K0MDf19.shapeB K0MDf19.sC2s false.
Definition g_K0M_e21 : gsel := GS K0MDe21.N0 K0A_cs [] K0MDe21.a0s
  [LN 1149 1164; LN 1165 1180; LN 1181 1196; LN 1197 1212; LN 1213 1228; LN 1229 1244; LN 1245 1255; LN 1256 1259; LN 1260 1260; LN 1261 1276; LN 1277 1292; LN 1293 1308; LN 1309 1319; LN 1320 1323; LN 1324 1324; LN 1325 1335; LN 1336 1339; LN 1340 1340] K0MDe21.leaves
  K0MDe21.ops K0MDe21.shapeB K0MDe21.sC2s false.
Definition g_K0M_e32 : gsel := GS K0MDe32.N0 K0A_cs [] K0MDe32.a0s
  [LN 8173 8999; LN 9000 9003; LN 9004 9004; LN 9005 9020; LN 9021 9036; LN 9037 9052; LN 9053 9068; LN 9069 9084; LN 9085 9100; LN 9101 9116; LN 9117 9132; LN 9133 9148; LN 9149 9164; LN 9165 9180; LN 9181 9196; LN 9197 9212; LN 9213 9228; LN 9229 9244; LN 9245 9255; LN 9256 9259; LN 9260 9260; LN 9261 9276; LN 9277 9292; LN 9293 9308; LN 9309 9319; LN 9320 9323; LN 9324 9324; LN 9325 9335; LN 9336 9339; LN 9340 9340] K0MDe32.leaves
  K0MDe32.ops K0MDe32.shapeB K0MDe32.sC2s false.
Definition g_K0AC_c0 : gsel := GS K0ACDc0.N0 K0A_cs [] K0ACDc0.a0s
  [LN 669 796; LN 1341 1628; LN 1629 2028; LN 2029 2332; LN 2333 2716; LN 2717 3260; LN 3261 4076; LN 4077 4668; LN 4669 5436] (map H0Fam2.l2_view K0ACDc0.leaves2)
  K0ACDc0.ops K0ACDc0.shapeB K0ACDc0.sC2s false.
Definition g_K0AC_c1 : gsel := GS K0ACDc1.N0 K0A_cs [] K0ACDc1.a0s
  [LN 5437 6540; LN 6541 8172; LN 9341 10908; LN 10909 12268; LN 12269 13084; LN 13085 16364; LN 16365 18700; LN 18701 20460; LN 20461 21820] (map H0Fam2.l2_view K0ACDc1.leaves2)
  K0ACDc1.ops K0ACDc1.shapeB K0ACDc1.sC2s false.
Definition g_K0AC_c2 : gsel := GS K0ACDc2.N0 K0A_cs [] K0ACDc2.a0s
  [LN 21821 24556; LN 24557 26188; LN 26189 28652; LN 28653 32748; LN 32749 36844; LN 36845 37436; LN 37437 40940; LN 40941 43676; LN 43677 45036] (map H0Fam2.l2_view K0ACDc2.leaves2)
  K0ACDc2.ops K0ACDc2.shapeB K0ACDc2.sC2s false.
Definition g_K0AC_c3 : gsel := GS K0ACDc3.N0 K0A_cs [] K0ACDc3.a0s
  [LN 45037 49132; LN 49133 52412; LN 52413 53228; LN 53229 57324; LN 57325 61420; LN 61421 65516] (map H0Fam2.l2_view K0ACDc3.leaves2)
  K0ACDc3.ops K0ACDc3.shapeB K0ACDc3.sC2s false.
Definition g_K0SG_s : gsel := GS K0SGDs.N0 K0A_cs [] K0SGDs.a0s
  [LN 1 7] K0SGDs.leaves
  K0SGDs.ops K0SGDs.shapeB K0SGDs.sC2s true.
Definition g_K0SG_s1 : gsel := GS K0SGDs1.N0 K0A_cs [] K0SGDs1.a0s
  [LN 8 10] K0SGDs1.leaves
  K0SGDs1.ops K0SGDs1.shapeB K0SGDs1.sC2s true.
Definition g_K0ZG_z : gsel := GS K0ZGDz.N0 K0A_cs [] K0ZGDz.a0s
  [LN 0 0] K0ZGDz.leaves
  K0ZGDz.ops K0ZGDz.shapeB K0ZGDz.sC2s true.
Definition fam : list gsel := [g_K0A_e1; g_K0A_e1_1; g_K0A_e4; g_K0A_e4_1; g_K0A_e5; g_K0A_e5_1; g_K0A_e8; g_K0A_e8_1; g_K0A_e9; g_K0A_e9_1; g_K0A_n10; g_K0A_e12; g_K0A_e20; g_K0A_f44; g_K0M_e0; g_K0M_e2; g_K0M_e3; g_K0M_e6; g_K0M_n7; g_K0M_n11; g_K0M_e13; g_K0M_e14; g_K0M_e15; g_K0M_n16; g_K0M_n17; g_K0M_f19; g_K0M_e21; g_K0M_e32; g_K0AC_c0; g_K0AC_c1; g_K0AC_c2; g_K0AC_c3; g_K0SG_s; g_K0SG_s1; g_K0ZG_z].
Definition cov : list (Z * Z * nat * nat) := [(0, 0, 34%nat, 0%nat); (1, 7, 32%nat, 0%nat); (8, 10, 33%nat, 0%nat); (11, 11, 14%nat, 0%nat); (12, 12, 14%nat, 1%nat); (13, 23, 0%nat, 0%nat); (24, 27, 1%nat, 0%nat); (28, 28, 0%nat, 1%nat); (29, 39, 15%nat, 0%nat); (40, 43, 15%nat, 1%nat); (44, 44, 15%nat, 2%nat); (45, 55, 16%nat, 0%nat); (56, 59, 16%nat, 1%nat); (60, 60, 16%nat, 2%nat); (61, 71, 2%nat, 0%nat); (72, 75, 3%nat, 0%nat); (76, 76, 2%nat, 1%nat); (77, 87, 4%nat, 0%nat); (88, 91, 5%nat, 0%nat); (92, 92, 4%nat, 1%nat); (93, 103, 17%nat, 0%nat); (104, 107, 17%nat, 1%nat); (108, 108, 17%nat, 2%nat); (109, 119, 18%nat, 0%nat); (120, 123, 18%nat, 1%nat); (124, 124, 18%nat, 2%nat); (125, 135, 6%nat, 0%nat); (136, 139, 7%nat, 0%nat); (140, 140, 6%nat, 1%nat); (141, 151, 8%nat, 0%nat); (152, 155, 9%nat, 0%nat); (156, 156, 8%nat, 1%nat); (157, 172, 10%nat, 0%nat); (173, 188, 10%nat, 1%nat); (189, 204, 19%nat, 0%nat); (205, 215, 19%nat, 1%nat); (216, 219, 19%nat, 2%nat); (220, 220, 19%nat, 3%nat); (221, 231, 19%nat, 4%nat); (232, 235, 19%nat, 5%nat); (236, 236, 19%nat, 6%nat); (237, 252, 11%nat, 0%nat); (253, 268, 11%nat, 1%nat); (269, 284, 11%nat, 2%nat); (285, 295, 20%nat, 0%nat); (296, 299, 20%nat, 1%nat); (300, 300, 20%nat, 2%nat); (301, 311, 20%nat, 3%nat); (312, 315, 20%nat, 4%nat); (316, 316, 20%nat, 5%nat); (317, 332, 21%nat, 0%nat); (333, 348, 21%nat, 1%nat); (349, 364, 21%nat, 2%nat); (365, 375, 21%nat, 3%nat); (376, 379, 21%nat, 4%nat); (380, 380, 21%nat, 5%nat); (381, 391, 21%nat, 6%nat); (392, 395, 21%nat, 7%nat); (396, 396, 21%nat, 8%nat); (397, 407, 22%nat, 0%nat); (408, 411, 22%nat, 1%nat); (412, 412, 22%nat, 2%nat); (413, 428, 22%nat, 3%nat); (429, 444, 22%nat, 4%nat); (445, 460, 22%nat, 5%nat); (461, 471, 22%nat, 6%nat); (472, 475, 22%nat, 7%nat); (476, 476, 22%nat, 8%nat); (477, 487, 22%nat, 9%nat); (488, 491, 22%nat, 10%nat); (492, 492, 22%nat, 11%nat); (493, 508, 23%nat, 0%nat); (509, 524, 23%nat, 1%nat); (525, 540, 23%nat, 2%nat); (541, 556, 23%nat, 3%nat); (557, 567, 23%nat, 4%nat); (568, 571, 23%nat, 5%nat); (572, 572, 23%nat, 6%nat); (573, 588, 24%nat, 0%nat); (589, 604, 24%nat, 1%nat); (605, 620, 24%nat, 2%nat); (621, 631, 24%nat, 3%nat); (632, 635, 24%nat, 4%nat); (636, 636, 24%nat, 5%nat); (637, 652, 24%nat, 6%nat); (653, 663, 24%nat, 7%nat); (664, 667, 24%nat, 8%nat); (668, 668, 24%nat, 9%nat); (669, 796, 28%nat, 0%nat); (797, 812, 25%nat, 0%nat); (813, 828, 25%nat, 1%nat); (829, 844, 25%nat, 2%nat); (845, 860, 25%nat, 3%nat); (861, 876, 25%nat, 4%nat); (877, 892, 25%nat, 5%nat); (893, 903, 25%nat, 6%nat); (904, 907, 25%nat, 7%nat); (908, 908, 25%nat, 8%nat); (909, 924, 25%nat, 9%nat); (925, 940, 25%nat, 10%nat); (941, 956, 25%nat, 11%nat); (957, 967, 25%nat, 12%nat); (968, 971, 25%nat, 13%nat); (972, 972, 25%nat, 14%nat); (973, 988, 25%nat, 15%nat); (989, 999, 25%nat, 16%nat); (1000, 1003, 25%nat, 17%nat); (1004, 1004, 25%nat, 18%nat); (1005, 1020, 12%nat, 0%nat); (1021, 1036, 12%nat, 1%nat); (1037, 1052, 12%nat, 2%nat); (1053, 1068, 12%nat, 3%nat); (1069, 1084, 12%nat, 4%nat); (1085, 1100, 12%nat, 5%nat); (1101, 1116, 12%nat, 6%nat); (1117, 1132, 12%nat, 7%nat); (1133, 1148, 12%nat, 8%nat); (1149, 1164, 26%nat, 0%nat); (1165, 1180, 26%nat, 1%nat); (1181, 1196, 26%nat, 2%nat); (1197, 1212, 26%nat, 3%nat); (1213, 1228, 26%nat, 4%nat); (1229, 1244, 26%nat, 5%nat); (1245, 1255, 26%nat, 6%nat); (1256, 1259, 26%nat, 7%nat); (1260, 1260, 26%nat, 8%nat); (1261, 1276, 26%nat, 9%nat); (1277, 1292, 26%nat, 10%nat); (1293, 1308, 26%nat, 11%nat); (1309, 1319, 26%nat, 12%nat); (1320, 1323, 26%nat, 13%nat); (1324, 1324, 26%nat, 14%nat); (1325, 1335, 26%nat, 15%nat); (1336, 1339, 26%nat, 16%nat); (1340, 1340, 26%nat, 17%nat); (1341, 1628, 28%nat, 1%nat); (1629, 2028, 28%nat, 2%nat); (2029, 2332, 28%nat, 3%nat); (2333, 2716, 28%nat, 4%nat); (2717, 3260, 28%nat, 5%nat); (3261, 4076, 28%nat, 6%nat); (4077, 4668, 28%nat, 7%nat); (4669, 5436, 28%nat, 8%nat); (5437, 6540, 29%nat, 0%nat); (6541, 8172, 29%nat, 1%nat); (8173, 8999, 27%nat, 0%nat); (9000, 9003, 27%nat, 1%nat); (9004, 9004, 27%nat, 2%nat); (9005, 9020, 27%nat, 3%nat); (9021, 9036, 27%nat, 4%nat); (9037, 9052, 27%nat, 5%nat); (9053, 9068, 27%nat, 6%nat); (9069, 9084, 27%nat, 7%nat); (9085, 9100, 27%nat, 8%nat); (9101, 9116, 27%nat, 9%nat); (9117, 9132, 27%nat, 10%nat); (9133, 9148, 27%nat, 11%nat); (9149, 9164, 27%nat, 12%nat); (9165, 9180, 27%nat, 13%nat); (9181, 9196, 27%nat, 14%nat); (9197, 9212, 27%nat, 15%nat); (9213, 9228, 27%nat, 16%nat); (9229, 9244, 27%nat, 17%nat); (9245, 9255, 27%nat, 18%nat); (9256, 9259, 27%nat, 19%nat); (9260, 9260, 27%nat, 20%nat); (9261, 9276, 27%nat, 21%nat); (9277, 9292, 27%nat, 22%nat); (9293, 9308, 27%nat, 23%nat); (9309, 9319, 27%nat, 24%nat); (9320, 9323, 27%nat, 25%nat); (9324, 9324, 27%nat, 26%nat); (9325, 9335, 27%nat, 27%nat); (9336, 9339, 27%nat, 28%nat); (9340, 9340, 27%nat, 29%nat); (9341, 10908, 29%nat, 2%nat); (10909, 12268, 29%nat, 3%nat); (12269, 13084, 29%nat, 4%nat); (13085, 16364, 29%nat, 5%nat); (16365, 18700, 29%nat, 6%nat); (18701, 20460, 29%nat, 7%nat); (20461, 21820, 29%nat, 8%nat); (21821, 24556, 30%nat, 0%nat); (24557, 26188, 30%nat, 1%nat); (26189, 28652, 30%nat, 2%nat); (28653, 32748, 30%nat, 3%nat); (32749, 36844, 30%nat, 4%nat); (36845, 37436, 30%nat, 5%nat); (37437, 40940, 30%nat, 6%nat); (40941, 43676, 30%nat, 7%nat); (43677, 45036, 30%nat, 8%nat); (45037, 49132, 31%nat, 0%nat); (49133, 52412, 31%nat, 1%nat); (52413, 53228, 31%nat, 2%nat); (53229, 57324, 31%nat, 3%nat); (57325, 61420, 31%nat, 4%nat); (61421, 65516, 31%nat, 5%nat); (65517, 65529, 13%nat, 0%nat)].
Definition qcov : list (Z * Z * nat * nat) := [].
Lemma TABLEN : forallb (fun g => Nat.eqb (length (gs_lnums g)) (length (gs_leaves g))) fam = true /\ map (fun g => length (gs_lnums g)) fam = [2%nat; 1%nat; 2%nat; 1%nat; 2%nat; 1%nat; 2%nat; 1%nat; 2%nat; 1%nat; 2%nat; 3%nat; 9%nat; 1%nat; 2%nat; 3%nat; 3%nat; 3%nat; 3%nat; 7%nat; 6%nat; 9%nat; 12%nat; 7%nat; 10%nat; 19%nat; 18%nat; 30%nat; 9%nat; 9%nat; 9%nat; 6%nat; 1%nat; 1%nat; 1%nat].
Proof. split; vm_compute; reflexivity. Qed.
Lemma CHK : H0Sel.fam_chk 56 57 58 0 HASHF fam cov qcov 65530 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma SHP : forallb (H0Sel.shp_chk 56 55) fam = true.
Proof. vm_compute. reflexivity. Qed.
Lemma SIDE : forallb grp_side (map gs_G fam) = true.
Proof. vm_compute. reflexivity. Qed.
Section D.
  Variables (sp : word) (STR0 : Z) (fs : Fs.Fs).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hstr : bv_unsigned sp + 192 <= STR0 < 2 ^ 47 - 32.
  Hypothesis Hstr8 : STR0 mod 8 = 0.
  Lemma HG : forall g, In g fam -> grp_stmt sp STR0 LIM fs (gs_G g).
  Proof.
    intros g Hg. unfold fam in Hg.
    destruct Hg as [<-|Hg]; [exact (K0AThme1.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0AThme1_1.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0AThme4.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0AThme4_1.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0AThme5.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0AThme5_1.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0AThme8.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0AThme8_1.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0AThme9.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0AThme9_1.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0AThmn10.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0AThme12.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0AThme20.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0AThmf44.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0MThme0.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0MThme2.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0MThme3.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0MThme6.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0MThmn7.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0MThmn11.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0MThme13.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0MThme14.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0MThme15.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0MThmn16.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0MThmn17.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0MThmf19.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0MThme21.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0MThme32.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0ACThmc0.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0ACThmc1.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0ACThmc2.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0ACThmc3.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0SGThms.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0SGThms1.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg as [<-|Hg]; [exact (K0ZGThmz.grp_sound sp STR0 fs Hsp Hstr Hstr8)|].
    destruct Hg.
  Qed.
  Lemma HBASE : forall g, In g fam -> gs_S0 g = inst_list K0A_cs (gs_sub g).
  Proof.
    intros g Hg. unfold fam in Hg.
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg as [<-|Hg]; [reflexivity|].
    destruct Hg.
  Qed.
  Theorem K0G_family : forall (PHIb : env -> Prop) t E R FULL model,
    H0Sel.tin_ok 0 t -> H0Sel.eokx 56 55 57 58 HASHF t E ->
    cs_ok HSEGS H0T LIM (SINVg PHIb sp STR0) (argHt STR0) (bv_unsigned sp) fs E K0A_cs R FULL model ->
    crz HSEGS (cfg_of HSEGS R (pc K0A_cs) FULL model) (H0Sel.TGT (H0Sel.t_n t <? 11) (Z.to_nat (H0Sel.t_calls t)) (H0Sel.t_cnt t) (m_fs model)).
  Proof.
    exact (H0Sel.family_numx sp STR0 LIM fs K0A_cs eq_refl 56 55 57 58 0 HASHF ltac:(lia) fam cov qcov 65530 HG HBASE SIDE CHK SHP).
  Qed.
End D.
Check K0G_family.
