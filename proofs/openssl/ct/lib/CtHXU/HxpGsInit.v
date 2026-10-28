(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common Require Import FastWord.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HX Require Import HxRegs HxVal HxMem HxStep HxHook.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope uint63_scope.

(* [comment removed for export] *)
Definition GSTK : int := 1024.

Definition T_GSTK : int := 1.
Definition T_ERRNO : int := 2.
Definition T_STOPPED : int := 3.
Definition T_BASEONCE : int := 4.
Definition T_OPTSDONE : int := 5.
Definition T_MONCE : int := 6.
Definition T_MKEY : int := 7.
Definition T_OLOCK : int := 8.
Definition T_TCBTSD : int := 9.
Definition T_TSD3 : int := 10.
Definition T_MK : int := 11.
Definition T_SA : int := 12.
Definition T_ND : int := 13.
Definition T_ES : int := 14.
Definition TC_RA : int := 15.
Definition TC_GP : int := 16.
Definition TC_S0 : int := 17.
Definition NEXTG : int := 29.

(* [comment removed for export] *)
Definition A_ERRNO : int := 0x333184.
Definition A_STOPPED : int := 0x3306e8.
Definition A_BASEONCE : int := 0x330700.
Definition A_OPTSDONE : int := 0x330740.
Definition A_MONCE : int := 0x330760.
Definition A_MKEY : int := 0x330768.
Definition A_OLOCK : int := 0x330730.
Definition A_TCBTSD : int := 0x3331d0.
Definition A_TSD3 : int := 0x3545a0.   (* [comment removed for export] *)
Definition V_TSDMAIN : int := 0x354590.
Definition TPVG : w64 := W false 0x333228.

(* [comment removed for export] *)
Definition cell0 (c : cell) : itrie cell := iset 0%nat IEmpty 0 c.

Definition gg_1 : region := RG None GSTK 4 true DUnk 7%nat IEmpty.
Definition gg_2 : region := RG (Some A_ERRNO) 4 2 true DUnk 0%nat IEmpty.                                (* [comment removed for export] *)
Definition gg_3 : region := RG (Some A_STOPPED) 1 0 false DUnk 0%nat (cell0 (CW (W false 0) 1)).          (* [comment removed for export] *)
Definition gg_4 : region := RG (Some A_BASEONCE) 8 3 false DUnk 0%nat (cell0 (CW (W false 4294967298) 255)).  (* [comment removed for export] *)
Definition gg_5 (od : int) : region := RG (Some A_OPTSDONE) 8 3 false DUnk 0%nat (cell0 (CW (W false od) 255)).  (* [comment removed for export] *)
Definition gg_6 : region := RG (Some A_MONCE) 8 3 false DUnk 0%nat (cell0 (CW (W false 8589934593) 255)).   (* [comment removed for export] *)
Definition gg_7 : region := RG (Some A_MKEY) 4 2 false DUnk 0%nat (cell0 (CW (W false 2) 15)).            (* [comment removed for export] *)
Definition gg_8 : region := RG (Some A_OLOCK) 8 3 false DUnk 0%nat IEmpty.                               (* [comment removed for export] *)
Definition gg_9 : region := RG (Some A_TCBTSD) 8 3 false DUnk 0%nat (cell0 (CW (W false V_TSDMAIN) 255)).  (* [comment removed for export] *)
Definition gg_10 : region := RG (Some A_TSD3) 8 3 false DUnk 0%nat (cell0 (CP T_MK (W false 0))).        (* [comment removed for export] *)
Definition gg_11 : region := RG None 72 4 false DUnk 4%nat (iset 4%nat IEmpty 3 (CP T_SA (W false 0))).    (* [comment removed for export] *)
Definition gg_12 : region := RG None 32 4 false DUnk 2%nat
  (iset 2%nat (iset 2%nat (iset 2%nat (iset 2%nat IEmpty 0 (CW (W false 1) 15)) 1 (CW (W false 0) 255)) 2 (CW (W false 1) 255)) 3 (CP T_ND (W false 0))).
Definition gg_13 : region := RG None 128 4 false DUnk 4%nat (iset 4%nat IEmpty 0 (CP T_ES (W false 0))).   (* [comment removed for export] *)
Definition gg_14 : region := RG None 904 4 false DUnk 7%nat IEmpty.                                    (* [comment removed for export] *)

Definition MG (od : int) : mem :=
  mset (mset (mset (mset (mset (mset (mset (mset (mset (mset (mset (mset (mset (mset IEmpty
    T_ERRNO gg_2) T_STOPPED gg_3) T_BASEONCE gg_4) T_OPTSDONE (gg_5 od)) T_MONCE gg_6) T_MKEY gg_7) T_OLOCK gg_8) T_TCBTSD gg_9) T_TSD3 gg_10)
    T_MK gg_11) T_SA gg_12) T_ND gg_13) T_ES gg_14) T_GSTK gg_1.

Definition absG : abstab :=
  [(A_ERRNO, A_ERRNO + 4, T_ERRNO); (A_STOPPED, A_STOPPED + 1, T_STOPPED); (A_BASEONCE, A_BASEONCE + 8, T_BASEONCE); (A_OPTSDONE, A_OPTSDONE + 8, T_OPTSDONE);
   (A_MONCE, A_MONCE + 8, T_MONCE); (A_MKEY, A_MKEY + 4, T_MKEY); (A_OLOCK, A_OLOCK + 8, T_OLOCK); (A_TCBTSD, A_TCBTSD + 8, T_TCBTSD); (A_TSD3, A_TSD3 + 8, T_TSD3)]%uint63.

Definition regsG (v : int) : regfile hval :=
  RF (VP TC_RA (W false 0)) (VP T_GSTK (W false GSTK)) (VP TC_GP (W false 0)) (VC TPVG) VU VU VU (VP TC_S0 (W false 0)) (VP (TC_S0 + 1) (W false 0))
     (VC (W false v)) VU VU VU VU VU VU VU
     (VP (TC_S0 + 2) (W false 0)) (VP (TC_S0 + 3) (W false 0)) (VP (TC_S0 + 4) (W false 0)) (VP (TC_S0 + 5) (W false 0)) (VP (TC_S0 + 6) (W false 0)) (VP (TC_S0 + 7) (W false 0))
     (VP (TC_S0 + 8) (W false 0)) (VP (TC_S0 + 9) (W false 0)) (VP (TC_S0 + 10) (W false 0)) (VP (TC_S0 + 11) (W false 0)) VU VU VU VU.

(* [comment removed for export] *)
Definition PC_GS : w64 := W false 0xe8a88.
Definition PC_GS_RET : w64 := W false 0xe8ba8.

Definition S0G (v od : int) : sstate := SS PC_GS (regsG v) RNone (MG od) absG NEXTG.
