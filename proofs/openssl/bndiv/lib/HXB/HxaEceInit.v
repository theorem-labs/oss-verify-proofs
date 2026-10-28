(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Common Require Import FastWord.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HX Require Import HxRegs HxVal HxMem HxStep HxHook.
Import ListNotations.
Local Open Scope uint63_scope.
Definition ESTK : int := 81920.
Definition eg_2 (r : int) : region := RG None (ESTK + r) 5 true DUnk 14%nat IEmpty.
Definition eg_3 (r : int) : region := RG None ((ESTK + r) >> 3) 0 false DZero 11%nat IEmpty.
Definition eg_4 : region := RG (Some 65536) 1589248 3 false (DImage 0%nat 0) 18%nat (IEmpty).
Definition eg_5 : region := RG (Some 5681152) 491520 3 false (DImage 2%nat 0) 16%nat (IEmpty).
Definition eg_6 : region := RG (Some 6186592) 2784 3 false (DUnk) 9%nat (fold_left (fun tr kc => iset 9%nat tr (fst kc) (snd kc)) [(0, CW (W false 1821748) 255); (4, CW (W false 2041372) 255); (12, CW (W false 2042688) 255)] IEmpty).
Definition eg_7 : region := RG (Some 6961656) 12 3 false (DUnk) 1%nat (fold_left (fun tr kc => iset 1%nat tr (fst kc) (snd kc)) [(0, CW (W false 2147450880) 255); (1, CW (W false 1) 15)] IEmpty).
Definition eg_8 : region := RG (Some 12411008) 2528 3 false (DUnk) 9%nat (fold_left (fun tr kc => iset 9%nat tr (fst kc) (snd kc)) [(44, CW (W false 2) 15); (48, CW (W false 3) 15); (180, CW (W false 0) 1); (200, CW (W false 2) 255); (204, CW (W false 2) 15); (208, CW (W false 1) 15)] IEmpty).
Definition eg_9 : region := RG (Some 12430840) 8 3 false (DUnk) 0%nat (fold_left (fun tr kc => iset 0%nat tr (fst kc) (snd kc)) [(0, CW (W false 12567032) 255)] IEmpty).
Definition eg_10 : region := RG (Some 12567040) 64 3 false (DUnk) 3%nat (fold_left (fun tr kc => iset 3%nat tr (fst kc) (snd kc)) [(2, CP 32 (W false 0))] IEmpty).
Definition eg_11 : region := RG (Some 2147459072) 1563136 3 false (DUnk) 18%nat (fold_left (fun tr kc => iset 18%nat tr (fst kc) (snd kc)) [(192904, CW (W false 4294967300) 17); (192923, CW (W false 17179869184) 17)] IEmpty).
Definition eg_32 : region := RG None 72 4 false DUnk 4%nat (fold_left (fun tr kc => iset 4%nat tr (fst kc) (snd kc)) [(3, CP 34 (W false 0))] IEmpty).
Definition eg_33 : region := RG None 9 0 false DZero 1%nat IEmpty.
Definition eg_34 : region := RG None 32 4 false DUnk 2%nat (fold_left (fun tr kc => iset 2%nat tr (fst kc) (snd kc)) [(0, CW (W false 1) 15); (1, CW (W false 0) 255); (2, CW (W false 1) 255); (3, CP 36 (W false 0))] IEmpty).
Definition eg_35 : region := RG None 4 0 false DZero 0%nat IEmpty.
Definition eg_36 : region := RG None 128 4 false DUnk 4%nat (fold_left (fun tr kc => iset 4%nat tr (fst kc) (snd kc)) [(0, CP 38 (W false 0))] IEmpty).
Definition eg_37 : region := RG None 16 0 false DZero 1%nat IEmpty.
Definition eg_38 : region := RG None 904 4 true DUnk 7%nat (fold_left (fun tr kc => iset 7%nat tr (fst kc) (snd kc)) [(0, CW (W false 0) 255); (1, CW (W false 0) 255); (2, CW (W false 0) 255); (3, CW (W false 0) 255); (4, CW (W false 0) 255); (5, CW (W false 0) 255); (6, CW (W false 0) 255); (7, CW (W false 0) 255); (8, CW (W false 0) 255); (9, CW (W false 0) 255); (10, CW (W false 0) 255); (11, CW (W false 0) 255); (12, CW (W false 0) 255); (13, CW (W false 0) 255); (14, CW (W false 0) 255); (15, CW (W false 0) 255); (16, CW (W false 0) 255); (17, CW (W false 0) 255); (18, CW (W false 0) 255); (19, CW (W false 0) 255); (20, CW (W false 0) 255); (21, CW (W false 0) 255); (22, CW (W false 0) 255); (23, CW (W false 0) 255); (24, CW (W false 0) 255); (25, CW (W false 0) 255); (26, CW (W false 0) 255); (27, CW (W false 0) 255); (28, CW (W false 0) 255); (29, CW (W false 0) 255); (30, CW (W false 0) 255); (31, CW (W false 0) 255); (32, CW (W false 0) 255); (33, CW (W false 0) 255); (34, CW (W false 0) 255); (35, CW (W false 0) 255); (36, CW (W false 0) 255); (37, CW (W false 0) 255); (38, CW (W false 0) 255); (39, CW (W false 0) 255); (40, CW (W false 0) 255); (41, CW (W false 0) 255); (42, CW (W false 0) 255); (43, CW (W false 0) 255); (44, CW (W false 0) 255); (45, CW (W false 0) 255); (46, CW (W false 0) 255); (47, CW (W false 0) 255); (48, CW (W false 0) 255); (49, CW (W false 0) 255); (50, CW (W false 0) 255); (51, CW (W false 0) 255); (52, CW (W false 0) 255); (53, CW (W false 0) 255); (54, CW (W false 0) 255); (55, CW (W false 0) 255); (56, CW (W false 0) 255); (57, CW (W false 0) 255); (58, CW (W false 0) 255); (59, CW (W false 0) 255); (60, CW (W false 0) 255); (61, CW (W false 0) 255); (62, CW (W false 0) 255); (63, CW (W false 0) 255); (64, CW (W false 0) 255); (65, CW (W false 0) 255); (66, CW (W false 0) 255); (67, CW (W false 0) 255); (68, CW (W false 0) 255); (69, CW (W false 0) 255); (70, CW (W false 0) 255); (71, CW (W false 0) 255); (72, CW (W false 0) 255); (73, CW (W false 0) 255); (74, CW (W false 0) 255); (75, CW (W false 0) 255); (76, CW (W false 0) 255); (77, CW (W false 0) 255); (78, CW (W false 0) 255); (79, CW (W false 0) 255); (80, CW (W false 0) 255); (81, CW (W false 0) 255); (82, CW (W false 0) 255); (83, CW (W false 0) 255); (84, CW (W false 0) 255); (85, CW (W false 0) 255); (86, CW (W false 0) 255); (87, CW (W false 0) 255); (88, CW (W true 9223372036854775807) 255); (89, CW (W true 9223372036854775807) 255); (90, CW (W true 9223372036854775807) 255); (91, CW (W true 9223372036854775807) 255); (92, CW (W true 9223372036854775807) 255); (93, CW (W true 9223372036854775807) 255); (94, CW (W true 9223372036854775807) 255); (95, CW (W true 9223372036854775807) 255); (96, CW (W false 0) 255); (97, CW (W false 0) 255); (98, CW (W false 0) 255); (99, CW (W false 0) 255); (100, CW (W false 0) 255); (101, CW (W false 0) 255); (102, CW (W false 0) 255); (103, CW (W false 0) 255); (104, CW (W false 0) 255); (105, CW (W false 0) 255); (106, CW (W false 0) 255); (107, CW (W false 0) 255); (108, CW (W false 0) 255); (109, CW (W false 0) 255); (110, CW (W false 0) 255); (111, CW (W false 0) 255); (112, CW (W false 0) 255)] IEmpty).
Definition eg_39 : region := RG None 113 0 false DZero 4%nat IEmpty.
Definition ME_4 : mem := mset IEmpty 4 eg_4.
Definition ME_5 : mem := mset ME_4 5 eg_5.
Definition ME_6 : mem := mset ME_5 6 eg_6.
Definition ME_7 : mem := mset ME_6 7 eg_7.
Definition ME_8 : mem := mset ME_7 8 eg_8.
Definition ME_9 : mem := mset ME_8 9 eg_9.
Definition ME_10 : mem := mset ME_9 10 eg_10.
Definition ME_11 : mem := mset ME_10 11 eg_11.
Definition ME_32 : mem := mset ME_11 32 eg_32.
Definition ME_33 : mem := mset ME_32 33 eg_33.
Definition ME_34 : mem := mset ME_33 34 eg_34.
Definition ME_35 : mem := mset ME_34 35 eg_35.
Definition ME_36 : mem := mset ME_35 36 eg_36.
Definition ME_37 : mem := mset ME_36 37 eg_37.
Definition ME_38 : mem := mset ME_37 38 eg_38.
Definition ME_39 : mem := mset ME_38 39 eg_39.
Definition ME_abs : mem := ME_39.
Definition ME_3 (r : int) : mem := mset ME_abs 3 (eg_3 r).
Definition ME (r : int) : mem := mset (ME_3 r) 2 (eg_2 r).
Definition absE : abstab := [(65536, 1654784, 4); (5681152, 6172672, 5); (6186592, 6189376, 6); (6961656, 6961668, 7); (12411008, 12413536, 8); (12430840, 12430848, 9); (12567040, 12567104, 10); (2147459072, 2149022208, 11)].
Definition RA_ECE : w64 := (W false 2024948).
Definition TE_GP : int := 1.
Definition TE_S0 : int := 19.
Definition NEXTE : int := 40.
Definition TRACES_E : list (list int) := [[2047280; 2048936; 2024948]; [2047344; 2048936; 2024948]].
Definition T_MK : int := 32.
Definition T_SA : int := 34.
Definition T_ND : int := 36.
Definition T_ES : int := 38.
Definition regsE (r : int) : regfile hval := RF (VC (W false 2024948)) (VP 2 (W false (ESTK + r))) (VP 1 (W false 0)) (VC (W false 12430928)) VU VU VU (VP 19 (W false 0)) (VP 20 (W false 0)) VU VU VU VU VU VU VU VU (VP 21 (W false 0)) (VP 22 (W false 0)) (VP 23 (W false 0)) (VP 24 (W false 0)) (VP 25 (W false 0)) (VP 26 (W false 0)) (VP 27 (W false 0)) (VP 28 (W false 0)) (VP 29 (W false 0)) (VP 30 (W false 0)) VU VU VU VU.
Definition SE0 (r : int) : sstate := SS (W false 2048852) (regsE r) RNone (ME r) absE NEXTE.
Definition TE_IMGSH : int := 11.
Definition RG_IMGSH_E : region := eg_11.
Definition CBT_E : list (int * Z * bool) := [(32%uint63, 72, false); (34%uint63, 32, false); (36%uint63, 128, false); (38%uint63, 904, true)]%Z.
Definition PC_ECE_FINAL : w64 := (W false 2049028).
Definition PC_ECE : w64 := (W false 2048852).
