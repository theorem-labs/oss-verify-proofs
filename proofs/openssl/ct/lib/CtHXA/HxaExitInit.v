(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common Require Import FastWord.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HX Require Import HxRegs HxVal HxMem HxStep HxHook.
Import ListNotations.
Local Open Scope uint63_scope.
Definition XSTK : int := 1024.
Definition xg_1 : region := RG None XSTK 4 true DUnk 7%nat IEmpty.
Definition xg_2 : region := RG (Some 65536) 1613824 3 false (DImage 0%nat 0) 18%nat (IEmpty).
Definition xg_3 : region := RG (Some 5451776) 495616 3 false (DImage 2%nat 0) 16%nat (IEmpty).
Definition xg_4 : region := RG (Some 5948592) 8 3 false (DUnk) 0%nat (fold_left (fun tr kc => iset 0%nat tr (fst kc) (snd kc)) [(0, CW (W false 5420256) 255)] IEmpty).
Definition xg_5 : region := RG (Some 5961504) 782912 3 false (DImage 3%nat 14112) 17%nat (IEmpty).
Definition xg_6 : region := RG (Some 6744448) 8 3 true (DUnk) 0%nat (fold_left (fun tr kc => iset 0%nat tr (fst kc) (snd kc)) [(0, CW (W false 1) 255)] IEmpty).
Definition xg_7 : region := RG (Some 6748240) 4 3 false (DUnk) 0%nat (fold_left (fun tr kc => iset 0%nat tr (fst kc) (snd kc)) [(0, CW (W false 1) 15)] IEmpty).
Definition xg_8 : region := RG (Some 6748400) 8 3 true (DUnk) 0%nat (fold_left (fun tr kc => iset 0%nat tr (fst kc) (snd kc)) [(0, CW (W false 0) 255)] IEmpty).
Definition xg_9 : region := RG (Some 6756508) 1 2 false (DUnk) 0%nat (fold_left (fun tr kc => iset 0%nat tr (fst kc) (snd kc)) [(0, CW (W false 1) 1)] IEmpty).
Definition xg_10 : region := RG (Some 6758456) 8 3 false (DUnk) 0%nat (fold_left (fun tr kc => iset 0%nat tr (fst kc) (snd kc)) [(0, CW (W false 2147450880) 255)] IEmpty).
Definition xg_11 : region := RG (Some 6761752) 1 3 false (DUnk) 0%nat (fold_left (fun tr kc => iset 0%nat tr (fst kc) (snd kc)) [(0, CW (W false 1) 1)] IEmpty).
Definition xg_12 : region := RG (Some 7355360) 8 3 false (DUnk) 0%nat (fold_left (fun tr kc => iset 0%nat tr (fst kc) (snd kc)) [(0, CW (W true 9223372036854775807) 255)] IEmpty).
Definition xg_13 : region := RG (Some 12210080) 8 3 true (DUnk) 0%nat (IEmpty).
Definition xg_14 : region := RG (Some 12210528) 8 3 true (DUnk) 0%nat (IEmpty).
Definition xg_15 : region := RG (Some 12210848) 40 3 true (DUnk) 3%nat (IEmpty).
Definition xg_16 : region := RG (Some 12210976) 8 3 true (DUnk) 0%nat (IEmpty).
Definition xg_17 : region := RG (Some 12217824) 16 3 true (DUnk) 1%nat (IEmpty).
Definition xg_18 : region := RG (Some 12224032) 56 3 true (DUnk) 3%nat (IEmpty).
Definition xg_19 : region := RG (Some 12224128) 80 3 true (DUnk) 4%nat (IEmpty).
Definition xg_20 : region := RG (Some 12224288) 40 3 true (DUnk) 3%nat (IEmpty).
Definition xg_21 : region := RG (Some 12224384) 80 3 true (DUnk) 4%nat (IEmpty).
Definition xg_22 : region := RG (Some 12224512) 24 3 true (DUnk) 2%nat (IEmpty).
Definition xg_23 : region := RG (Some 12224640) 496 3 true (DUnk) 6%nat (IEmpty).
Definition xg_24 : region := RG (Some 2147459072) 1537536 3 true (DUnk) 18%nat (IEmpty).
Definition MX_2 : mem := mset IEmpty 2 xg_2.
Definition MX_3 : mem := mset MX_2 3 xg_3.
Definition MX_4 : mem := mset MX_3 4 xg_4.
Definition MX_5 : mem := mset MX_4 5 xg_5.
Definition MX_6 : mem := mset MX_5 6 xg_6.
Definition MX_7 : mem := mset MX_6 7 xg_7.
Definition MX_8 : mem := mset MX_7 8 xg_8.
Definition MX_9 : mem := mset MX_8 9 xg_9.
Definition MX_10 : mem := mset MX_9 10 xg_10.
Definition MX_11 : mem := mset MX_10 11 xg_11.
Definition MX_12 : mem := mset MX_11 12 xg_12.
Definition MX_13 : mem := mset MX_12 13 xg_13.
Definition MX_14 : mem := mset MX_13 14 xg_14.
Definition MX_15 : mem := mset MX_14 15 xg_15.
Definition MX_16 : mem := mset MX_15 16 xg_16.
Definition MX_17 : mem := mset MX_16 17 xg_17.
Definition MX_18 : mem := mset MX_17 18 xg_18.
Definition MX_19 : mem := mset MX_18 19 xg_19.
Definition MX_20 : mem := mset MX_19 20 xg_20.
Definition MX_21 : mem := mset MX_20 21 xg_21.
Definition MX_22 : mem := mset MX_21 22 xg_22.
Definition MX_23 : mem := mset MX_22 23 xg_23.
Definition MX_24 : mem := mset MX_23 24 xg_24.
Definition MX : mem := mset MX_24 1 xg_1.
Definition absX : abstab := [(65536, 1679360, 2); (5451776, 5947392, 3); (5948592, 5948600, 4); (5961504, 6744416, 5); (6744448, 6744456, 6); (6748240, 6748244, 7); (6748400, 6748408, 8); (6756508, 6756509, 9); (6758456, 6758464, 10); (6761752, 6761753, 11); (7355360, 7355368, 12); (12210080, 12210088, 13); (12210528, 12210536, 14); (12210848, 12210888, 15); (12210976, 12210984, 16); (12217824, 12217840, 17); (12224032, 12224088, 18); (12224128, 12224208, 19); (12224288, 12224328, 20); (12224384, 12224464, 21); (12224512, 12224536, 22); (12224640, 12225136, 23); (2147459072, 2148996608, 24)].
Definition TX_RA : int := 25.
Definition TX_GP : int := 26.
Definition TX_S0 : int := 27.
Definition NEXTX : int := 39.
Definition regsX : regfile hval := RF (VP 25 (W false 0)) (VP 1 (W false XSTK)) (VP 26 (W false 0)) (VC (W false 12227568)) VU VU VU (VP 27 (W false 0)) (VP 28 (W false 0)) VU VU VU VU VU VU VU VU (VP 29 (W false 0)) (VP 30 (W false 0)) (VP 31 (W false 0)) (VP 32 (W false 0)) (VP 33 (W false 0)) (VP 34 (W false 0)) (VP 35 (W false 0)) (VP 36 (W false 0)) (VP 37 (W false 0)) (VP 38 (W false 0)) VU VU VU VU.
Definition S0X : sstate := SS (W false 2048976) regsX RNone MX absX NEXTX.
Definition PC_X_RET : w64 := (W false 2049020).
Definition TPVX : w64 := (W false 12227568).
Definition WX : list (Z * Z) := [(6744448, 6744456); (6748400, 6748408); (12210080, 12210088); (12210528, 12210536); (12210848, 12210888); (12210976, 12210984); (12217824, 12217840); (12224032, 12224088); (12224128, 12224208); (12224288, 12224328); (12224384, 12224464); (12224512, 12224536); (12224640, 12225136); (2147459072, 2148996608)]%Z.
