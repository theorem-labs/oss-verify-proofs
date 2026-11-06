(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From Stdlib Require Import Uint63 PrimString.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan DietCodec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.

Definition sc_pair_nn (s : string) (i : int) : (nat * nat) * int :=
  let '(a, j) := sc_N s i in let '(b, k) := sc_N s j in ((a, b), k).
Definition sc_pair_ne (s : string) (i : int) : (nat * expr) * int :=
  let '(a, j) := sc_N s i in let '(e, k) := sc_E s j in ((a, e), k).
Definition sc_oE (s : string) (i : int) : option expr * int :=
  if PrimInt63.eqb (PrimString.get s i) 35%uint63
  then let '(e, j) := sc_E s (PrimInt63.add i 1%uint63) in (Some e, j)
  else (None, PrimInt63.add i 1%uint63).
(* [comment removed for export] *)
Definition sc_acs (s : string) (i : int) : acs * int :=
  let '(ss, i1) := sc_sstate s i in
  let '(mp, i2) := sc_listN sc_amap s i1 in
  let '(tot, i3) := sc_Z s i2 in
  let '(ylo, i4) := sc_Z s i3 in
  let '(eag, i5) := sc_Z s i4 in
  let '(vis, i6) := sc_listN sc_pair_ee s i5 in
  let '(gho, i7) := sc_listN sc_pair_ee s i6 in
  let '(aby, i8) := sc_Z s i7 in
  let '(brk, i9) := sc_E s i8 in
  let '(fd, i10) := sc_afd s i9 in
  (ACS ss mp tot ylo eag vis gho aby brk fd (PrimInt63.eqb (PrimString.get s i10) 35%uint63), PrimInt63.add i10 1%uint63).

Definition pc_snode (s : string) (i : int) : snode * int :=
  let k := PrimInt63.sub (PrimString.get s i) 48%uint63 in ((if PrimInt63.eqb k 0%uint63 then YMunmap else if PrimInt63.eqb k 1%uint63 then YBrk else YSetTid), PrimInt63.add i 1%uint63).
Definition pc_xnode (s : string) (i : int) : xnode * int :=
  let k := PrimInt63.sub (PrimString.get s i) 48%uint63 in ((if PrimInt63.eqb k 0%uint63 then XIMemset else if PrimInt63.eqb k 1%uint63 then XIMemcpy else if PrimInt63.eqb k 2%uint63 then XMemset else if PrimInt63.eqb k 3%uint63 then XMemcpy else if PrimInt63.eqb k 4%uint63 then XMemIsZero else if PrimInt63.eqb k 5%uint63 then XEnvScan else if PrimInt63.eqb k 6%uint63 then XPnScan else if PrimInt63.eqb k 7%uint63 then XLayout else if PrimInt63.eqb k 8%uint63 then XIStrncpy else if PrimInt63.eqb k 9%uint63 then XPopFree else XSniff), PrimInt63.add i 1%uint63).

Fixpoint pc_plan (f : nat) (s : string) (i : int) : plan * int :=
  match f with
  | O => (PContra, i)
  | S f' =>
      let hi := PrimInt63.sub (PrimString.get s i) 35%uint63 in
      let lo := PrimInt63.sub (PrimString.get s (PrimInt63.add i 1%uint63)) 48%uint63 in
      let i2 := PrimInt63.add i 2%uint63 in
      if PrimInt63.eqb hi 0%uint63 then (
        if PrimInt63.eqb lo 0%uint63 then let '(a0, j0) := sc_listN sc_Z s i2 in let '(a1, j1) := pc_plan f' s j0 in (PRun a0 a1, j1) else
        if PrimInt63.eqb lo 1%uint63 then let '(a0, j0) := sc_E s i2 in let '(a1, j1) := sc_Z s j0 in let '(a2, j2) := pc_plan f' s j1 in let '(a3, j3) := pc_plan f' s j2 in (PSplit a0 a1 a2 a3, j3) else
        if PrimInt63.eqb lo 2%uint63 then let '(a0, j0) := sc_E s i2 in let '(a1, j1) := sc_Z s j0 in let '(a2, j2) := pc_plan f' s j1 in let '(a3, j3) := pc_plan f' s j2 in (PCase2 a0 a1 a2 a3, j3) else
        if PrimInt63.eqb lo 3%uint63 then let '(a0, j0) := sc_E s i2 in let '(a1, j1) := sc_E s j0 in let '(a2, j2) := pc_plan f' s j1 in let '(a3, j3) := pc_plan f' s j2 in (PCaseDisj a0 a1 a2 a3, j3) else
        if PrimInt63.eqb lo 4%uint63 then let '(a0, j0) := sc_E s i2 in let '(a1, j1) := sc_E s j0 in let '(a2, j2) := sc_E s j1 in let '(a3, j3) := sc_E s j2 in let '(a4, j4) := pc_plan f' s j3 in (PShDisj a0 a1 a2 a3 a4, j4) else
        if PrimInt63.eqb lo 5%uint63 then (PContra, i2) else
        if PrimInt63.eqb lo 6%uint63 then let '(a0, j0) := sc_kentry s i2 in let '(a1, j1) := pc_plan f' s j0 in (PFact a0 a1, j1) else
        if PrimInt63.eqb lo 7%uint63 then let '(a0, j0) := sc_E s i2 in let '(a1, j1) := sc_Z s j0 in let '(a2, j2) := sc_N s j1 in let '(a3, j3) := pc_plan f' s j2 in (PJoin a0 a1 a2 a3, j3) else
        if PrimInt63.eqb lo 8%uint63 then let '(a0, j0) := sc_listN sc_N s i2 in let '(a1, j1) := pc_plan f' s j0 in (PForget a0 a1, j1) else
        if PrimInt63.eqb lo 9%uint63 then let '(a0, j0) := sc_E s i2 in let '(a1, j1) := sc_E s j0 in let '(a2, j2) := pc_plan f' s j1 in (PDropRange a0 a1 a2, j2) else
        if PrimInt63.eqb lo 10%uint63 then let '(a0, j0) := sc_listN sc_pair_ee s i2 in let '(a1, j1) := pc_plan f' s j0 in (PGcKeep a0 a1, j1) else
        if PrimInt63.eqb lo 11%uint63 then let '(a0, j0) := sc_N s i2 in let '(a1, j1) := pc_plan f' s j0 in (PBump a0 a1, j1) else
        if PrimInt63.eqb lo 12%uint63 then let '(a0, j0) := sc_listN sc_N s i2 in let '(a1, j1) := pc_plan f' s j0 in (PHavoc a0 a1, j1) else
        if PrimInt63.eqb lo 13%uint63 then let '(a0, j0) := sc_N s i2 in let '(a1, j1) := pc_plan f' s j0 in (PHavocBig a0 a1, j1) else
        if PrimInt63.eqb lo 14%uint63 then let '(a0, j0) := sc_N s i2 in let '(a1, j1) := sc_Z s j0 in let '(a2, j2) := sc_oE s j1 in let '(a3, j3) := pc_plan f' s j2 in (PFresh a0 a1 a2 a3, j3) else
        if PrimInt63.eqb lo 15%uint63 then let '(a0, j0) := pc_snode s i2 in let '(a1, j1) := pc_plan f' s j0 in (PSys a0 a1, j1) else (PContra, i2))
      else
      if PrimInt63.eqb hi 1%uint63 then (
        if PrimInt63.eqb lo 0%uint63 then let '(a0, j0) := pc_plan f' s i2 in let '(a1, j1) := pc_plan f' s j0 in (PMmap a0 a1, j1) else
        if PrimInt63.eqb lo 1%uint63 then let '(a0, j0) := pc_plan f' s i2 in let '(a1, j1) := pc_plan f' s j0 in let '(a2, j2) := pc_plan f' s j1 in (PMmapIn a0 a1 a2, j2) else
        if PrimInt63.eqb lo 2%uint63 then let '(a0, j0) := pc_plan f' s i2 in let '(a1, j1) := pc_plan f' s j0 in (PMprotect a0 a1, j1) else
        if PrimInt63.eqb lo 3%uint63 then let '(a0, j0) := pc_plan f' s i2 in let '(a1, j1) := pc_plan f' s j0 in (PBrk2 a0 a1, j1) else
        if PrimInt63.eqb lo 4%uint63 then let '(a0, j0) := pc_xnode s i2 in let '(a1, j1) := sc_listN sc_E s j0 in let '(a2, j2) := pc_plan f' s j1 in (PX a0 a1 a2, j2) else
        if PrimInt63.eqb lo 5%uint63 then let '(a0, j0) := sc_N s i2 in let '(a1, j1) := sc_listN sc_E s j0 in let '(a2, j2) := pc_plan f' s j1 in (PExt a0 a1 a2, j2) else
        if PrimInt63.eqb lo 6%uint63 then let '(a0, j0) := sc_N s i2 in let '(a1, j1) := sc_listN sc_E s j0 in let '(a2, j2) := pc_plan f' s j1 in (PEmit a0 a1 a2, j2) else
        if PrimInt63.eqb lo 7%uint63 then let '(a0, j0) := sc_N s i2 in let '(a1, j1) := sc_listN sc_E s j0 in let '(a2, j2) := pc_plan f' s j1 in let '(a3, j3) := pc_plan f' s j2 in (PExt2 a0 a1 a2 a3, j3) else
        if PrimInt63.eqb lo 8%uint63 then let '(a0, j0) := sc_N s i2 in let '(a1, j1) := sc_E s j0 in let '(a2, j2) := sc_acs s j1 in let '(a3, j3) := pc_plan f' s j2 in let '(a4, j4) := pc_plan f' s j3 in (PLoop a0 a1 a2 a3 a4, j4) else
        if PrimInt63.eqb lo 9%uint63 then (PNext, i2) else
        if PrimInt63.eqb lo 10%uint63 then let '(a0, j0) := sc_N s i2 in (PHandoff a0, j0) else
        if PrimInt63.eqb lo 11%uint63 then (PExit, i2) else
        if PrimInt63.eqb lo 12%uint63 then (PSpin, i2) else
        if PrimInt63.eqb lo 13%uint63 then let '(a0, j0) := sc_N s i2 in let '(a1, j1) := sc_Z s j0 in let '(a2, j2) := pc_plan f' s j1 in (PFog a0 a1 a2, j2) else
        if PrimInt63.eqb lo 14%uint63 then let '(a0, j0) := sc_N s i2 in let '(a1, j1) := sc_Z s j0 in let '(a2, j2) := pc_plan f' s j1 in (PFogNew a0 a1 a2, j2) else
        if PrimInt63.eqb lo 15%uint63 then let '(a0, j0) := sc_E s i2 in let '(a1, j1) := sc_E s j0 in let '(a2, j2) := pc_plan f' s j1 in (PGhost a0 a1 a2, j2) else (PContra, i2))
      else
      if PrimInt63.eqb hi 2%uint63 then (
        if PrimInt63.eqb lo 0%uint63 then let '(a0, j0) := sc_E s i2 in let '(a1, j1) := sc_E s j0 in let '(a2, j2) := pc_plan f' s j1 in (PUnvis a0 a1 a2, j2) else
        if PrimInt63.eqb lo 1%uint63 then let '(a0, j0) := sc_Z s i2 in let '(a1, j1) := sc_Z s j0 in let '(a2, j2) := pc_plan f' s j1 in (PHavocBrk a0 a1 a2, j2) else
        if PrimInt63.eqb lo 2%uint63 then let '(a0, j0) := sc_Z s i2 in let '(a1, j1) := sc_Z s j0 in let '(a2, j2) := pc_plan f' s j1 in (PIntro a0 a1 a2, j2) else
        if PrimInt63.eqb lo 3%uint63 then let '(a0, j0) := sc_Z s i2 in let '(a1, j1) := sc_listN sc_N s j0 in let '(a2, j2) := pc_plan f' s j1 in (PDiamond a0 a1 a2, j2) else
        if PrimInt63.eqb lo 4%uint63 then let '(a0, j0) := sc_listN sc_pair_nn s i2 in let '(a1, j1) := pc_plan f' s j0 in (PRename a0 a1, j1) else
        if PrimInt63.eqb lo 5%uint63 then let '(a0, j0) := pc_plan f' s i2 in (PCompact a0, j0) else
        if PrimInt63.eqb lo 6%uint63 then let '(a0, j0) := sc_N s i2 in let '(a1, j1) := sc_acs s j0 in let '(a2, j2) := sc_N s j1 in let '(a3, j3) := pc_plan f' s j2 in let '(a4, j4) := pc_plan f' s j3 in (PVia a0 a1 a2 a3 a4, j4) else
        if PrimInt63.eqb lo 7%uint63 then let '(a0, j0) := sc_N s i2 in (PMerge a0, j0) else
        if PrimInt63.eqb lo 8%uint63 then let '(a0, j0) := sc_E s i2 in let '(a1, j1) := sc_Z s j0 in let '(a2, j2) := pc_plan f' s j1 in (PAbstractCell a0 a1 a2, j2) else
        if PrimInt63.eqb lo 9%uint63 then let '(a0, j0) := sc_listN sc_E s i2 in let '(a1, j1) := pc_plan f' s j0 in (PHavocWords a0 a1, j1) else
        if PrimInt63.eqb lo 10%uint63 then let '(a0, j0) := sc_N s i2 in let '(a1, j1) := sc_E s j0 in let '(a2, j2) := pc_plan f' s j1 in (PRespell a0 a1 a2, j2) else
        if PrimInt63.eqb lo 11%uint63 then let '(a0, j0) := pc_plan f' s i2 in let '(a1, j1) := pc_plan f' s j0 in let '(a2, j2) := pc_plan f' s j1 in (PMmapInH a0 a1 a2, j2) else
        if PrimInt63.eqb lo 12%uint63 then let '(a0, j0) := sc_E s i2 in let '(a1, j1) := sc_Z s j0 in let '(a2, j2) := sc_N s j1 in let '(a3, j3) := pc_plan f' s j2 in (PJoinX a0 a1 a2 a3, j3) else
        if PrimInt63.eqb lo 13%uint63 then let '(a0, j0) := sc_Z s i2 in let '(a1, j1) := sc_N s j0 in let '(a2, j2) := sc_listN sc_N s j1 in let '(a3, j3) := pc_plan f' s j2 in (PDiamondT a0 a1 a2 a3, j3) else
        if PrimInt63.eqb lo 14%uint63 then let '(a0, j0) := sc_N s i2 in let '(a1, j1) := pc_plan f' s j0 in let '(a2, j2) := pc_plan f' s j1 in (PBand a0 a1 a2, j2) else
        if PrimInt63.eqb lo 15%uint63 then let '(a0, j0) := sc_Z s i2 in let '(a1, j1) := sc_Z s j0 in let '(a2, j2) := sc_Z s j1 in let '(a3, j3) := pc_plan f' s j2 in (PIntroG a0 a1 a2 a3, j3) else (PContra, i2))
      else
      if PrimInt63.eqb hi 3%uint63 then (
        if PrimInt63.eqb lo 0%uint63 then let '(a0, j0) := sc_E s i2 in let '(a1, j1) := sc_E s j0 in let '(a2, j2) := sc_Z s j1 in let '(a3, j3) := sc_listN sc_N s j2 in let '(a4, j4) := pc_plan f' s j3 in (PDiamondDisj a0 a1 a2 a3 a4, j4) else
        if PrimInt63.eqb lo 1%uint63 then let '(a0, j0) := sc_Z s i2 in let '(a1, j1) := sc_N s j0 in let '(a2, j2) := sc_listN sc_N s j1 in let '(a3, j3) := sc_N s j2 in let '(a4, j4) := pc_plan f' s j3 in (PDiamondTX a0 a1 a2 a3 a4, j4) else
        if PrimInt63.eqb lo 2%uint63 then let '(a0, j0) := sc_listN sc_E s i2 in let '(a1, j1) := pc_plan f' s j0 in (PGcDisj a0 a1, j1) else
        if PrimInt63.eqb lo 3%uint63 then let '(a0, j0) := pc_plan f' s i2 in (PGcRangeAuto a0, j0) else (PContra, i2))
      else (PContra, i2)
  end.

(* [comment removed for export] *)
Definition PLAN_FUEL : nat := 20000.
Definition dec_plan (s : string) : plan := fst (pc_plan PLAN_FUEL s 0%uint63).
Definition sc_sub (s : string) (i : int) : list (nat * expr) * int := sc_listN sc_pair_ne s i.
Definition dec_sub (s : string) : list (nat * expr) := fst (sc_sub s 0%uint63).
Definition dec_lsub (s : string) : list (list (nat * expr)) := fst (sc_listN sc_sub s 0%uint63).
Definition dec_lk (s : string) : list kentry := fst (sc_listN sc_kentry s 0%uint63).
Definition dec_llk (s : string) : list (list kentry) := fst (sc_listN (sc_listN sc_kentry) s 0%uint63).
Definition dec_lacs (s : string) : list acs := fst (sc_listN sc_acs s 0%uint63).
