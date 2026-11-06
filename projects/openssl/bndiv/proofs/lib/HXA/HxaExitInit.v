(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.bndiv.lib.Common Require Import FastWord.
From OSSVerify.Proofs.openssl.bndiv.lib.Common.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bndiv.lib.HX Require Import HxRegs HxVal HxMem HxStep HxHook.
Import ListNotations.
Local Open Scope uint63_scope.
Definition XSTK : int := 1024.
Definition xg_1 : region := RG None XSTK 4 true DUnk 7%nat IEmpty.
Definition xg_2 : region := RG (Some 65536) 1609728 3 false (DImage 0%nat 0) 18%nat (IEmpty).
Definition xg_3 : region := RG (Some 5447680) 495616 3 false (DImage 2%nat 0) 16%nat (IEmpty).
Definition xg_4 : region := RG (Some 5945112) 8 3 false (DUnk) 0%nat (fold_left (fun tr kc => iset 0%nat tr (fst kc) (snd kc)) [(0, CW (W false 5416992) 255)] IEmpty).
Definition xg_5 : region := RG (Some 5958048) 781248 3 false (DImage 3%nat 14752) 17%nat (IEmpty).
Definition xg_6 : region := RG (Some 6739328) 8 3 true (DUnk) 0%nat (fold_left (fun tr kc => iset 0%nat tr (fst kc) (snd kc)) [(0, CW (W false 1) 255)] IEmpty).
Definition xg_7 : region := RG (Some 6743120) 4 3 false (DUnk) 0%nat (fold_left (fun tr kc => iset 0%nat tr (fst kc) (snd kc)) [(0, CW (W false 1) 15)] IEmpty).
Definition xg_8 : region := RG (Some 6743280) 8 3 true (DUnk) 0%nat (fold_left (fun tr kc => iset 0%nat tr (fst kc) (snd kc)) [(0, CW (W false 0) 255)] IEmpty).
Definition xg_9 : region := RG (Some 6751388) 1 2 false (DUnk) 0%nat (fold_left (fun tr kc => iset 0%nat tr (fst kc) (snd kc)) [(0, CW (W false 1) 1)] IEmpty).
Definition xg_10 : region := RG (Some 6753336) 8 3 false (DUnk) 0%nat (fold_left (fun tr kc => iset 0%nat tr (fst kc) (snd kc)) [(0, CW (W false 2147450880) 255)] IEmpty).
Definition xg_11 : region := RG (Some 6756632) 1 3 false (DUnk) 0%nat (fold_left (fun tr kc => iset 0%nat tr (fst kc) (snd kc)) [(0, CW (W false 1) 1)] IEmpty).
Definition xg_12 : region := RG (Some 7350240) 8 3 false (DUnk) 0%nat (fold_left (fun tr kc => iset 0%nat tr (fst kc) (snd kc)) [(0, CW (W true 9223372036854775807) 255)] IEmpty).
Definition xg_13 : region := RG (Some 12205216) 8 3 true (DUnk) 0%nat (IEmpty).
Definition xg_14 : region := RG (Some 12205600) 8 3 true (DUnk) 0%nat (IEmpty).
Definition xg_15 : region := RG (Some 12211808) 56 3 true (DUnk) 3%nat (IEmpty).
Definition xg_16 : region := RG (Some 12211904) 80 3 true (DUnk) 4%nat (IEmpty).
Definition xg_17 : region := RG (Some 12212064) 40 3 true (DUnk) 3%nat (IEmpty).
Definition xg_18 : region := RG (Some 12212160) 48 3 true (DUnk) 3%nat (IEmpty).
Definition xg_19 : region := RG (Some 12212544) 40 3 true (DUnk) 3%nat (IEmpty).
Definition xg_20 : region := RG (Some 12212672) 8 3 true (DUnk) 0%nat (IEmpty).
Definition xg_21 : region := RG (Some 12219488) 32 3 true (DUnk) 2%nat (IEmpty).
Definition xg_22 : region := RG (Some 12219552) 24 3 true (DUnk) 2%nat (IEmpty).
Definition xg_23 : region := RG (Some 12219680) 504 3 true (DUnk) 6%nat (IEmpty).
Definition xg_24 : region := RG (Some 2147459072) 1537024 3 true (DUnk) 18%nat (IEmpty).
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
Definition absX : abstab := [(65536, 1675264, 2); (5447680, 5943296, 3); (5945112, 5945120, 4); (5958048, 6739296, 5); (6739328, 6739336, 6); (6743120, 6743124, 7); (6743280, 6743288, 8); (6751388, 6751389, 9); (6753336, 6753344, 10); (6756632, 6756633, 11); (7350240, 7350248, 12); (12205216, 12205224, 13); (12205600, 12205608, 14); (12211808, 12211864, 15); (12211904, 12211984, 16); (12212064, 12212104, 17); (12212160, 12212208, 18); (12212544, 12212584, 19); (12212672, 12212680, 20); (12219488, 12219520, 21); (12219552, 12219576, 22); (12219680, 12220184, 23); (2147459072, 2148996096, 24)].
Definition TX_RA : int := 25.
Definition TX_GP : int := 26.
Definition TX_S0 : int := 27.
Definition NEXTX : int := 39.
Definition regsX : regfile hval := RF (VP 25 (W false 0)) (VP 1 (W false XSTK)) (VP 26 (W false 0)) (VC (W false 12222608)) VU VU VU (VP 27 (W false 0)) (VP 28 (W false 0)) VU VU VU VU VU VU VU VU (VP 29 (W false 0)) (VP 30 (W false 0)) (VP 31 (W false 0)) (VP 32 (W false 0)) (VP 33 (W false 0)) (VP 34 (W false 0)) (VP 35 (W false 0)) (VP 36 (W false 0)) (VP 37 (W false 0)) (VP 38 (W false 0)) VU VU VU VU.
Definition S0X : sstate := SS (W false 2046284) regsX RNone MX absX NEXTX.
Definition PC_X_RET : w64 := (W false 2046328).
Definition TPVX : w64 := (W false 12222608).
Definition WX : list (Z * Z) := [(6739328, 6739336); (6743280, 6743288); (12205216, 12205224); (12205600, 12205608); (12211808, 12211864); (12211904, 12211984); (12212064, 12212104); (12212160, 12212208); (12212544, 12212584); (12212672, 12212680); (12219488, 12219520); (12219552, 12219576); (12219680, 12220184); (2147459072, 2148996096)]%Z.
