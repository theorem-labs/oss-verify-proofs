(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From Stdlib Require Import Uint63 PrimString.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan StateCodec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.

Record penv : Type := PE {
  pe_plans : list plan; pe_acs : list acs; pe_exprs : list expr;
  pe_lnn : list (list (nat * nat)); pe_lee : list (list (expr * expr)); pe_ln : list (list nat) }.

(* [comment removed for export] *)
Definition pc_ix (s : string) (i : int) : nat * int :=
  let '(v, j) := sc_hex 16 s i 0%uint63 in (sc_nat 63 v, j).

Fixpoint pc_expr (ee : list expr) (f : nat) (s : string) (i : int) : expr * int :=
  match f with
  | O => (ELit 0, i)
  | S f' =>
      let c := PrimString.get s i in
      let i1 := PrimInt63.add i 1%uint63 in
      if PrimInt63.eqb c 35%uint63 then let '(v, j) := sc_hex 16 s i1 0%uint63 in (ELit (sc_Zp v), j)
      else if PrimInt63.eqb c 36%uint63 then let '(v, j) := sc_hex 16 s i1 0%uint63 in (EVar (sc_Nb v), j)
      else if PrimInt63.eqb c 43%uint63 then
        let '(a, j) := pc_expr ee f' s i1 in let '(b, k) := pc_expr ee f' s j in (EAlu ALU_ADD a b, k)
      else if PrimInt63.eqb c 64%uint63 then
        let '(a, j) := pc_expr ee f' s i1 in let '(b, k) := pc_expr ee f' s j in (EMd M_MUL a b, k)
      else if PrimInt63.eqb c 39%uint63 then
        let '(z, j) := sc_Z s i1 in let '(e, k) := pc_expr ee f' s j in (escale z e, k)
      else if PrimInt63.eqb c 40%uint63 then
        let '(e, j) := pc_expr ee f' s i1 in let '(z, k) := sc_Z s j in (eaddz e z, k)
      else if PrimInt63.eqb c 41%uint63 then
        let '(a, j) := pc_expr ee f' s i1 in let '(b, k) := pc_expr ee f' s j in (eadd a b, k)
      else if PrimInt63.eqb c 96%uint63 then
        let '(a, j) := pc_expr ee f' s i1 in let '(b, k) := pc_expr ee f' s j in (esub a b, k)
      else if PrimInt63.eqb c 126%uint63 then let '(n, j) := pc_ix s i1 in (List.nth n ee (ELit 0), j)
      else if PrimInt63.eqb c 45%uint63 then let '(v, j) := sc_hex 16 s i1 0%uint63 in (ELit (sc_Zn v), j)
      else if PrimInt63.eqb c 38%uint63 then
        let op := sc_aluop (PrimInt63.sub (PrimString.get s i1) 48%uint63) in
        let '(a, j) := pc_expr ee f' s (PrimInt63.add i 2%uint63) in let '(b, k) := pc_expr ee f' s j in (EAlu op a b, k)
      else if PrimInt63.eqb c 37%uint63 then
        let op := sc_aluop (PrimInt63.sub (PrimString.get s i1) 48%uint63) in
        let '(a, j) := pc_expr ee f' s (PrimInt63.add i 2%uint63) in let '(b, k) := pc_expr ee f' s j in (EAluw op a b, k)
      else if PrimInt63.eqb c 47%uint63 then
        let op := sc_mulop (PrimInt63.sub (PrimString.get s i1) 48%uint63) in
        let '(a, j) := pc_expr ee f' s (PrimInt63.add i 2%uint63) in let '(b, k) := pc_expr ee f' s j in (EMd op a b, k)
      else if PrimInt63.eqb c 124%uint63 then
        let op := sc_mulop (PrimInt63.sub (PrimString.get s i1) 48%uint63) in
        let '(a, j) := pc_expr ee f' s (PrimInt63.add i 2%uint63) in let '(b, k) := pc_expr ee f' s j in (EMdw op a b, k)
      else if PrimInt63.eqb c 91%uint63 then
        let '(lo, j) := sc_N s i1 in let '(n, k) := sc_N s j in let '(e, l) := pc_expr ee f' s k in (EExt false lo n e, l)
      else if PrimInt63.eqb c 93%uint63 then
        let '(lo, j) := sc_N s i1 in let '(n, k) := sc_N s j in let '(e, l) := pc_expr ee f' s k in (EExt true lo n e, l)
      else if PrimInt63.eqb c 123%uint63 then
        let '(b, j) := sc_N s i1 in let '(z, k) := sc_Z s j in let '(n, l) := sc_N s k in (EBlob false b z n, l)
      else if PrimInt63.eqb c 125%uint63 then
        let '(b, j) := sc_N s i1 in let '(z, k) := sc_Z s j in let '(n, l) := sc_N s k in (EBlob true b z n, l)
      else if PrimInt63.eqb c 94%uint63 then let '(z, j) := sc_Z s i in (ELit z, j)
      else (ELit 0, i1)
  end.
Definition pc_E (E : penv) (s : string) (i : int) : expr * int := pc_expr (pe_exprs E) 200 s i.

Definition pc_saddr (E : penv) (s : string) (i : int) : saddr * int :=
  let '(b, j) := pc_E E s i in let '(o, k) := sc_Z s j in (SA b o, k).
Definition pc_pair_se (E : penv) (s : string) (i : int) : (saddr * expr) * int :=
  let '(a, j) := pc_saddr E s i in let '(e, k) := pc_E E s j in ((a, e), k).
Definition pc_pair_ee (E : penv) (s : string) (i : int) : (expr * expr) * int :=
  let '(a, j) := pc_E E s i in let '(e, k) := pc_E E s j in ((a, e), k).
Definition pc_pair_nn (s : string) (i : int) : (nat * nat) * int :=
  let '(a, j) := sc_N s i in let '(b, k) := sc_N s j in ((a, b), k).
Definition pc_EZN (E : penv) (s : string) (i : int) : (expr * Z * nat) * int :=
  let '(e, j) := pc_E E s i in let '(z, k) := sc_Z s j in let '(n, l) := sc_N s k in ((e, z, n), l).

Definition pc_kentry (E : penv) (s : string) (i : int) : kentry * int :=
  let c := PrimString.get s i in
  let i1 := PrimInt63.add i 1%uint63 in
  if PrimInt63.eqb c 33%uint63 then
    let '(a, j) := pc_saddr E s i1 in let '(w, k) := sc_N s j in let '(v, l) := pc_E E s k in (KWord a w v, l)
  else if PrimInt63.eqb c 37%uint63 then
    let '(lo, j) := sc_Z s i1 in let '(hi, k) := sc_Z s j in (KImg lo hi, k)
  else if PrimInt63.eqb c 39%uint63 then
    let '(e, j) := pc_E E s i1 in let '(lo, k) := sc_Z s j in let '(hi, l) := sc_Z s k in (KRange e lo hi, l)
  else if PrimInt63.eqb c 35%uint63 then
    let '(a, j) := pc_saddr E s i1 in let '(n, k) := pc_E E s j in (KZero a n, k)
  else if PrimInt63.eqb c 36%uint63 then
    let '(a, j) := pc_saddr E s i1 in let '(n, k) := pc_E E s j in let '(b, l) := sc_N s k in (KBlob a n b, l)
  else if PrimInt63.eqb c 38%uint63 then
    let '(e, j) := pc_E E s i1 in let '(m, k) := sc_Z s j in (KAlign e m, k)
  else if PrimInt63.eqb c 40%uint63 then
    let '(a, j) := pc_saddr E s i1 in let '(n, k) := pc_E E s j in (KWr a n, k)
  else if PrimInt63.eqb c 41%uint63 then
    let '(a1, j) := pc_saddr E s i1 in let '(n1, k) := pc_E E s j in
    let '(a2, l) := pc_saddr E s k in let '(n2, m) := pc_E E s l in (KDisj a1 n1 a2 n2, m)
  else if PrimInt63.eqb c 43%uint63 then
    let '(a, j) := pc_saddr E s i1 in let '(n, k) := pc_E E s j in let '(z, l) := sc_Z s k in (KFill a n z, l)
  else if PrimInt63.eqb c 44%uint63 then
    let '(a, j) := pc_saddr E s i1 in let '(n, k) := pc_E E s j in (KUnk a n, k)
  else if PrimInt63.eqb c 47%uint63 then
    let '(t, j) := sc_N s i1 in let '(rs, k) := sc_listN (pc_pair_se E) s j in
    let '(args, l) := sc_listN (pc_E E) s k in let '(z, m) := sc_Z s l in (KPriv t rs args z, m)
  else (KImg 0 0, i1).

Definition pc_acs (E : penv) (s : string) (i : int) : acs * int :=
  let '(n, j) := pc_ix s (PrimInt63.add i 1%uint63) in (List.nth n (pe_acs E) (dec_acs ""%pstring), j).
Definition pc_lN (E : penv) (s : string) (i : int) : list nat * int :=
  if PrimInt63.eqb (PrimString.get s i) 33%uint63
  then let '(n, j) := pc_ix s (PrimInt63.add i 1%uint63) in (List.nth n (pe_ln E) nil, j)
  else sc_listN sc_N s i.
Definition pc_lNN (E : penv) (s : string) (i : int) : list (nat * nat) * int :=
  if PrimInt63.eqb (PrimString.get s i) 33%uint63
  then let '(n, j) := pc_ix s (PrimInt63.add i 1%uint63) in (List.nth n (pe_lnn E) nil, j)
  else sc_listN pc_pair_nn s i.
Definition pc_lEE (E : penv) (s : string) (i : int) : list (expr * expr) * int :=
  if PrimInt63.eqb (PrimString.get s i) 33%uint63
  then let '(n, j) := pc_ix s (PrimInt63.add i 1%uint63) in (List.nth n (pe_lee E) nil, j)
  else sc_listN (pc_pair_ee E) s i.
Definition pc_oE (E : penv) (s : string) (i : int) : option expr * int :=
  if PrimInt63.eqb (PrimString.get s i) 35%uint63
  then let '(e, j) := pc_E E s (PrimInt63.add i 1%uint63) in (Some e, j)
  else (None, PrimInt63.add i 1%uint63).
Definition pc_snode (s : string) (i : int) : snode * int :=
  let k := PrimInt63.sub (PrimString.get s i) 48%uint63 in
  (if PrimInt63.eqb k 0%uint63 then YMunmap else if PrimInt63.eqb k 1%uint63 then YBrk else YSetTid, PrimInt63.add i 1%uint63).
Definition pc_xnode (s : string) (i : int) : xnode * int :=
  let k := PrimInt63.sub (PrimString.get s i) 48%uint63 in
  (if PrimInt63.eqb k 0%uint63 then XIMemset else if PrimInt63.eqb k 1%uint63 then XIMemcpy else if PrimInt63.eqb k 2%uint63 then XMemset else if PrimInt63.eqb k 3%uint63 then XMemcpy else if PrimInt63.eqb k 4%uint63 then XMemIsZero else if PrimInt63.eqb k 5%uint63 then XEnvScan else if PrimInt63.eqb k 6%uint63 then XPnScan else if PrimInt63.eqb k 7%uint63 then XLayout else if PrimInt63.eqb k 8%uint63 then XIStrncpy else if PrimInt63.eqb k 9%uint63 then XPopFree else XSniff, PrimInt63.add i 1%uint63).

Fixpoint pc_plan (E : penv) (f : nat) (s : string) (i : int) : plan * int :=
  match f with
  | O => (PContra, i)
  | S f' =>
      let c := PrimString.get s i in
      if PrimInt63.eqb c 33%uint63 then
        let '(n, j) := pc_ix s (PrimInt63.add i 1%uint63) in (List.nth n (pe_plans E) PContra, j)
      else
      let hi := PrimInt63.sub c 35%uint63 in
      let lo := PrimInt63.sub (PrimString.get s (PrimInt63.add i 1%uint63)) 48%uint63 in
      let i2 := PrimInt63.add i 2%uint63 in
      if PrimInt63.eqb hi 0%uint63 then (
        if PrimInt63.eqb lo 0%uint63 then let '(a0, j0) := sc_listN sc_Z s i2 in let '(a1, j1) := pc_plan E f' s j0 in (PRun a0 a1, j1) else
        if PrimInt63.eqb lo 1%uint63 then let '(a0, j0) := pc_E E s i2 in let '(a1, j1) := sc_Z s j0 in let '(a2, j2) := pc_plan E f' s j1 in let '(a3, j3) := pc_plan E f' s j2 in (PSplit a0 a1 a2 a3, j3) else
        if PrimInt63.eqb lo 2%uint63 then let '(a0, j0) := pc_E E s i2 in let '(a1, j1) := sc_Z s j0 in let '(a2, j2) := pc_plan E f' s j1 in let '(a3, j3) := pc_plan E f' s j2 in (PCase2 a0 a1 a2 a3, j3) else
        if PrimInt63.eqb lo 3%uint63 then let '(a0, j0) := pc_E E s i2 in let '(a1, j1) := pc_E E s j0 in let '(a2, j2) := pc_plan E f' s j1 in let '(a3, j3) := pc_plan E f' s j2 in (PCaseDisj a0 a1 a2 a3, j3) else
        if PrimInt63.eqb lo 4%uint63 then let '(a0, j0) := pc_E E s i2 in let '(a1, j1) := pc_E E s j0 in let '(a2, j2) := pc_E E s j1 in let '(a3, j3) := pc_E E s j2 in let '(a4, j4) := pc_plan E f' s j3 in (PShDisj a0 a1 a2 a3 a4, j4) else
        if PrimInt63.eqb lo 5%uint63 then (PContra, i2) else
        if PrimInt63.eqb lo 6%uint63 then let '(a0, j0) := pc_kentry E s i2 in let '(a1, j1) := pc_plan E f' s j0 in (PFact a0 a1, j1) else
        if PrimInt63.eqb lo 7%uint63 then let '(a0, j0) := pc_E E s i2 in let '(a1, j1) := sc_Z s j0 in let '(a2, j2) := sc_N s j1 in let '(a3, j3) := pc_plan E f' s j2 in (PJoin a0 a1 a2 a3, j3) else
        if PrimInt63.eqb lo 8%uint63 then let '(a0, j0) := pc_lN E s i2 in let '(a1, j1) := pc_plan E f' s j0 in (PForget a0 a1, j1) else
        if PrimInt63.eqb lo 9%uint63 then let '(a0, j0) := pc_E E s i2 in let '(a1, j1) := pc_E E s j0 in let '(a2, j2) := pc_plan E f' s j1 in (PDropRange a0 a1 a2, j2) else
        if PrimInt63.eqb lo 10%uint63 then let '(a0, j0) := pc_lEE E s i2 in let '(a1, j1) := pc_plan E f' s j0 in (PGcKeep a0 a1, j1) else
        if PrimInt63.eqb lo 11%uint63 then let '(a0, j0) := sc_N s i2 in let '(a1, j1) := pc_plan E f' s j0 in (PBump a0 a1, j1) else
        if PrimInt63.eqb lo 12%uint63 then let '(a0, j0) := pc_lN E s i2 in let '(a1, j1) := pc_plan E f' s j0 in (PHavoc a0 a1, j1) else
        if PrimInt63.eqb lo 13%uint63 then let '(a0, j0) := sc_N s i2 in let '(a1, j1) := pc_plan E f' s j0 in (PHavocBig a0 a1, j1) else
        if PrimInt63.eqb lo 14%uint63 then let '(a0, j0) := sc_N s i2 in let '(a1, j1) := sc_Z s j0 in let '(a2, j2) := pc_oE E s j1 in let '(a3, j3) := pc_plan E f' s j2 in (PFresh a0 a1 a2 a3, j3) else
        if PrimInt63.eqb lo 15%uint63 then let '(a0, j0) := pc_snode s i2 in let '(a1, j1) := pc_plan E f' s j0 in (PSys a0 a1, j1) else (PContra, i2))
      else
      if PrimInt63.eqb hi 1%uint63 then (
        if PrimInt63.eqb lo 0%uint63 then let '(a0, j0) := pc_plan E f' s i2 in let '(a1, j1) := pc_plan E f' s j0 in (PMmap a0 a1, j1) else
        if PrimInt63.eqb lo 1%uint63 then let '(a0, j0) := pc_plan E f' s i2 in let '(a1, j1) := pc_plan E f' s j0 in let '(a2, j2) := pc_plan E f' s j1 in (PMmapIn a0 a1 a2, j2) else
        if PrimInt63.eqb lo 2%uint63 then let '(a0, j0) := pc_plan E f' s i2 in let '(a1, j1) := pc_plan E f' s j0 in (PMprotect a0 a1, j1) else
        if PrimInt63.eqb lo 3%uint63 then let '(a0, j0) := pc_plan E f' s i2 in let '(a1, j1) := pc_plan E f' s j0 in (PBrk2 a0 a1, j1) else
        if PrimInt63.eqb lo 4%uint63 then let '(a0, j0) := pc_xnode s i2 in let '(a1, j1) := sc_listN (pc_E E) s j0 in let '(a2, j2) := pc_plan E f' s j1 in (PX a0 a1 a2, j2) else
        if PrimInt63.eqb lo 5%uint63 then let '(a0, j0) := sc_N s i2 in let '(a1, j1) := sc_listN (pc_E E) s j0 in let '(a2, j2) := pc_plan E f' s j1 in (PExt a0 a1 a2, j2) else
        if PrimInt63.eqb lo 6%uint63 then let '(a0, j0) := sc_N s i2 in let '(a1, j1) := sc_listN (pc_E E) s j0 in let '(a2, j2) := pc_plan E f' s j1 in (PEmit a0 a1 a2, j2) else
        if PrimInt63.eqb lo 7%uint63 then let '(a0, j0) := sc_N s i2 in let '(a1, j1) := sc_listN (pc_E E) s j0 in let '(a2, j2) := pc_plan E f' s j1 in let '(a3, j3) := pc_plan E f' s j2 in (PExt2 a0 a1 a2 a3, j3) else
        if PrimInt63.eqb lo 8%uint63 then let '(a0, j0) := sc_N s i2 in let '(a1, j1) := pc_E E s j0 in let '(a2, j2) := pc_acs E s j1 in let '(a3, j3) := pc_plan E f' s j2 in let '(a4, j4) := pc_plan E f' s j3 in (PLoop a0 a1 a2 a3 a4, j4) else
        if PrimInt63.eqb lo 9%uint63 then (PNext, i2) else
        if PrimInt63.eqb lo 10%uint63 then let '(a0, j0) := sc_N s i2 in (PHandoff a0, j0) else
        if PrimInt63.eqb lo 11%uint63 then (PExit, i2) else
        if PrimInt63.eqb lo 12%uint63 then (PSpin, i2) else
        if PrimInt63.eqb lo 13%uint63 then let '(a0, j0) := sc_N s i2 in let '(a1, j1) := sc_Z s j0 in let '(a2, j2) := pc_plan E f' s j1 in (PFog a0 a1 a2, j2) else
        if PrimInt63.eqb lo 14%uint63 then let '(a0, j0) := sc_N s i2 in let '(a1, j1) := sc_Z s j0 in let '(a2, j2) := pc_plan E f' s j1 in (PFogNew a0 a1 a2, j2) else
        if PrimInt63.eqb lo 15%uint63 then let '(a0, j0) := pc_E E s i2 in let '(a1, j1) := pc_E E s j0 in let '(a2, j2) := pc_plan E f' s j1 in (PGhost a0 a1 a2, j2) else (PContra, i2))
      else
      if PrimInt63.eqb hi 2%uint63 then (
        if PrimInt63.eqb lo 0%uint63 then let '(a0, j0) := pc_E E s i2 in let '(a1, j1) := pc_E E s j0 in let '(a2, j2) := pc_plan E f' s j1 in (PUnvis a0 a1 a2, j2) else
        if PrimInt63.eqb lo 1%uint63 then let '(a0, j0) := sc_Z s i2 in let '(a1, j1) := sc_Z s j0 in let '(a2, j2) := pc_plan E f' s j1 in (PHavocBrk a0 a1 a2, j2) else
        if PrimInt63.eqb lo 2%uint63 then let '(a0, j0) := sc_Z s i2 in let '(a1, j1) := sc_Z s j0 in let '(a2, j2) := pc_plan E f' s j1 in (PIntro a0 a1 a2, j2) else
        if PrimInt63.eqb lo 3%uint63 then let '(a0, j0) := sc_Z s i2 in let '(a1, j1) := pc_lN E s j0 in let '(a2, j2) := pc_plan E f' s j1 in (PDiamond a0 a1 a2, j2) else
        if PrimInt63.eqb lo 4%uint63 then let '(a0, j0) := pc_lNN E s i2 in let '(a1, j1) := pc_plan E f' s j0 in (PRename a0 a1, j1) else
        if PrimInt63.eqb lo 5%uint63 then let '(a0, j0) := pc_plan E f' s i2 in (PCompact a0, j0) else
        if PrimInt63.eqb lo 6%uint63 then let '(a0, j0) := sc_N s i2 in let '(a1, j1) := pc_acs E s j0 in let '(a2, j2) := sc_N s j1 in let '(a3, j3) := pc_plan E f' s j2 in let '(a4, j4) := pc_plan E f' s j3 in (PVia a0 a1 a2 a3 a4, j4) else
        if PrimInt63.eqb lo 7%uint63 then let '(a0, j0) := sc_N s i2 in (PMerge a0, j0) else
        if PrimInt63.eqb lo 8%uint63 then let '(a0, j0) := pc_E E s i2 in let '(a1, j1) := sc_Z s j0 in let '(a2, j2) := pc_plan E f' s j1 in (PAbstractCell a0 a1 a2, j2) else
        if PrimInt63.eqb lo 9%uint63 then let '(a0, j0) := sc_listN (pc_E E) s i2 in let '(a1, j1) := pc_plan E f' s j0 in (PHavocWords a0 a1, j1) else
        if PrimInt63.eqb lo 10%uint63 then let '(a0, j0) := sc_N s i2 in let '(a1, j1) := pc_E E s j0 in let '(a2, j2) := pc_plan E f' s j1 in (PRespell a0 a1 a2, j2) else
        if PrimInt63.eqb lo 11%uint63 then let '(a0, j0) := pc_plan E f' s i2 in let '(a1, j1) := pc_plan E f' s j0 in let '(a2, j2) := pc_plan E f' s j1 in (PMmapInH a0 a1 a2, j2) else
        if PrimInt63.eqb lo 12%uint63 then let '(a0, j0) := pc_E E s i2 in let '(a1, j1) := pc_E E s j0 in let '(a2, j2) := sc_Z s j1 in let '(a3, j3) := pc_lN E s j2 in let '(a4, j4) := pc_plan E f' s j3 in (PCaseDisjJ a0 a1 a2 a3 a4, j4) else
        if PrimInt63.eqb lo 13%uint63 then let '(a0, j0) := pc_plan E f' s i2 in let '(a1, j1) := pc_plan E f' s j0 in (PCaseP a0 a1, j1) else
        if PrimInt63.eqb lo 14%uint63 then let '(a0, j0) := pc_E E s i2 in let '(a1, j1) := sc_listN sc_Z s j0 in let '(a2, j2) := sc_Z s j1 in let '(a3, j3) := pc_lN E s j2 in let '(a4, j4) := sc_listN (pc_EZN E) s j3 in let '(a5, j5) := pc_plan E f' s j4 in (PCaseNJ a0 a1 a2 a3 a4 a5, j5) else
        if PrimInt63.eqb lo 15%uint63 then let '(a0, j0) := pc_E E s i2 in let '(a1, j1) := pc_E E s j0 in let '(a2, j2) := pc_plan E f' s j1 in (PVisAbsorb a0 a1 a2, j2) else (PContra, i2))
      else
      if PrimInt63.eqb hi 3%uint63 then (
        if PrimInt63.eqb lo 0%uint63 then let '(a0, j0) := pc_E E s i2 in let '(a1, j1) := sc_N s j0 in let '(a2, j2) := pc_plan E f' s j1 in (PFreshCell a0 a1 a2, j2) else
        if PrimInt63.eqb lo 1%uint63 then let '(a0, j0) := pc_E E s i2 in let '(a1, j1) := sc_Z s j0 in let '(a2, j2) := sc_Z s j1 in let '(a3, j3) := pc_plan E f' s j2 in (PVisSplit a0 a1 a2 a3, j3) else
        if PrimInt63.eqb lo 2%uint63 then let '(a0, j0) := pc_E E s i2 in let '(a1, j1) := sc_Z s j0 in let '(a2, j2) := pc_E E s j1 in let '(a3, j3) := pc_plan E f' s j2 in (PVisHead a0 a1 a2 a3, j3) else
        if PrimInt63.eqb lo 3%uint63 then let '(a0, j0) := pc_E E s i2 in let '(a1, j1) := sc_Z s j0 in let '(a2, j2) := pc_plan E f' s j1 in (PUnvisHead a0 a1 a2, j2) else
        if PrimInt63.eqb lo 4%uint63 then let '(a0, j0) := pc_plan E f' s i2 in (PGhostDedup a0, j0) else
        if PrimInt63.eqb lo 5%uint63 then let '(a0, j0) := sc_Z s i2 in let '(a1, j1) := sc_Z s j0 in let '(a2, j2) := pc_plan E f' s j1 in (PHavocBrkP a0 a1 a2, j2) else
        if PrimInt63.eqb lo 6%uint63 then let '(a0, j0) := pc_lEE E s i2 in let '(a1, j1) := pc_lN E s j0 in let '(a2, j2) := pc_plan E f' s j1 in (PKeep a0 a1 a2, j2) else
        if PrimInt63.eqb lo 7%uint63 then let '(a0, j0) := pc_kentry E s i2 in let '(a1, j1) := pc_plan E f' s j0 in (PFactMem a0 a1, j1) else
        if PrimInt63.eqb lo 8%uint63 then let '(a0, j0) := pc_E E s i2 in let '(a1, j1) := pc_E E s j0 in let '(a2, j2) := pc_E E s j1 in let '(a3, j3) := pc_E E s j2 in let '(a4, j4) := pc_plan E f' s j3 in (PVisRespell a0 a1 a2 a3 a4, j4) else
        if PrimInt63.eqb lo 9%uint63 then let '(a0, j0) := pc_E E s i2 in let '(a1, j1) := pc_E E s j0 in let '(a2, j2) := pc_E E s j1 in let '(a3, j3) := pc_E E s j2 in let '(a4, j4) := pc_plan E f' s j3 in (PMapRespell a0 a1 a2 a3 a4, j4) else
        if PrimInt63.eqb lo 10%uint63 then let '(a0, j0) := pc_E E s i2 in let '(a1, j1) := sc_Z s j0 in let '(a2, j2) := sc_Z s j1 in let '(a3, j3) := pc_E E s j2 in let '(a4, j4) := sc_Z s j3 in let '(a5, j5) := pc_plan E f' s j4 in (PMemRespell a0 a1 a2 a3 a4 a5, j5) else
        if PrimInt63.eqb lo 11%uint63 then let '(a0, j0) := sc_N s i2 in let '(a1, j1) := sc_Z s j0 in let '(a2, j2) := pc_plan E f' s j1 in (PSrlSplit a0 a1 a2, j2) else
        if PrimInt63.eqb lo 12%uint63 then let '(a0, j0) := sc_N s i2 in let '(a1, j1) := sc_Z s j0 in let '(a2, j2) := pc_E E s j1 in let '(a3, j3) := pc_plan E f' s j2 in (PAndRange a0 a1 a2 a3, j3) else
        if PrimInt63.eqb lo 13%uint63 then let '(a0, j0) := sc_N s i2 in let '(a1, j1) := sc_Z s j0 in let '(a2, j2) := sc_N s j1 in let '(a3, j3) := pc_plan E f' s j2 in (PAndRangeR a0 a1 a2 a3, j3) else
        if PrimInt63.eqb lo 14%uint63 then let '(a0, j0) := sc_N s i2 in let '(a1, j1) := sc_Z s j0 in let '(a2, j2) := pc_plan E f' s j1 in (PSrlSplitAll a0 a1 a2, j2) else
        if PrimInt63.eqb lo 15%uint63 then let '(a0, j0) := sc_Z s i2 in let '(a1, j1) := sc_Z s j0 in let '(a2, j2) := pc_plan E f' s j1 in (PFdHavoc a0 a1 a2, j2) else (PContra, i2))
      else
      if PrimInt63.eqb hi 4%uint63 then (
        if PrimInt63.eqb lo 0%uint63 then let '(a0, j0) := pc_E E s i2 in let '(a1, j1) := sc_N s j0 in let '(a2, j2) := pc_plan E f' s j1 in (PFreshCellK a0 a1 a2, j2) else
        if PrimInt63.eqb lo 1%uint63 then let '(a0, j0) := pc_lN E s i2 in let '(a1, j1) := pc_plan E f' s j0 in (PVisPerm a0 a1, j1) else
        if PrimInt63.eqb lo 2%uint63 then let '(a0, j0) := pc_lNN E s i2 in (PHandoffM a0, j0) else
        if PrimInt63.eqb lo 3%uint63 then let '(a0, j0) := pc_E E s i2 in let '(a1, j1) := pc_E E s j0 in let '(a2, j2) := pc_plan E f' s j1 in (PFdRespell a0 a1 a2, j2) else
        if PrimInt63.eqb lo 4%uint63 then let '(a0, j0) := pc_E E s i2 in let '(a1, j1) := pc_E E s j0 in let '(a2, j2) := sc_N s j1 in let '(a3, j3) := pc_plan E f' s j2 in (PDisjNth a0 a1 a2 a3, j3) else
        if PrimInt63.eqb lo 5%uint63 then let '(a0, j0) := pc_plan E f' s i2 in let '(a1, j1) := pc_plan E f' s j0 in let '(a2, j2) := pc_plan E f' s j1 in (PMmapInS a0 a1 a2, j2) else (PContra, i2))
      else (PContra, i2)
  end.

Definition dec_plan (E : penv) (s : string) : plan :=
  fst (pc_plan E (S (sc_nat 63 (PrimString.length s))) s 0%uint63).
