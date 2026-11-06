(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From Stdlib Require Import Uint63 PrimString.
From LinuxProcessSemantics.Riscv Require Import Instr.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto.
Import ListNotations. Import AX2.

Fixpoint sc_hex (f : nat) (s : string) (i acc : int) : int * int :=
  match f with
  | O => (acc, i)
  | S f' =>
      let d := PrimInt63.sub (PrimString.get s i) 48%uint63 in
      if PrimInt63.ltb d 16%uint63
      then sc_hex f' s (PrimInt63.add i 1%uint63) (PrimInt63.lor (PrimInt63.lsl acc 4%uint63) d)
      else (acc, i)
  end.

Fixpoint sc_pos (f : nat) (x : int) : positive :=
  match f with
  | O => xH
  | S f' =>
      if PrimInt63.leb x 1%uint63 then xH
      else if PrimInt63.eqb (PrimInt63.land x 1%uint63) 0%uint63 then xO (sc_pos f' (PrimInt63.lsr x 1%uint63))
      else xI (sc_pos f' (PrimInt63.lsr x 1%uint63))
  end.
Definition sc_Zp (x : int) : Z := if PrimInt63.eqb x 0%uint63 then Z0 else Zpos (sc_pos 63 x).
Definition sc_Zn (x : int) : Z := if PrimInt63.eqb x 0%uint63 then Z0 else Zneg (sc_pos 63 x).

Fixpoint sc_nat (f : nat) (x : int) : nat :=
  match f with
  | O => O
  | S f' =>
      if PrimInt63.eqb x 0%uint63 then O
      else let h := sc_nat f' (PrimInt63.lsr x 1%uint63) in
           if PrimInt63.eqb (PrimInt63.land x 1%uint63) 0%uint63 then Nat.add h h else S (Nat.add h h)
  end.

Definition sc_Zsmall (s : string) (i : int) : Z * int :=
  let c := PrimString.get s i in
  let '(v, j) := sc_hex 16 s (PrimInt63.add i 1%uint63) 0%uint63 in
  if PrimInt63.eqb c 45%uint63 then (sc_Zn v, j) else (sc_Zp v, j).

Definition sc_Z (s : string) (i : int) : Z * int :=
  if PrimInt63.eqb (PrimString.get s i) 94%uint63 then
    let '(hi, j) := sc_Zsmall s (PrimInt63.add i 1%uint63) in
    let '(lo, k) := sc_Zsmall s j in
    (Z.add (Z.shiftl hi 60) lo, k)
  else sc_Zsmall s i.

Definition sc_N (s : string) (i : int) : nat * int :=
  let '(v, j) := sc_hex 16 s (PrimInt63.add i 1%uint63) 0%uint63 in (sc_nat 63 v, j).

Definition sc_aluop (k : int) : aluop :=
  if PrimInt63.eqb k 0%uint63 then ALU_ADD else if PrimInt63.eqb k 1%uint63 then ALU_SUB
  else if PrimInt63.eqb k 2%uint63 then ALU_SLL else if PrimInt63.eqb k 3%uint63 then ALU_SLT
  else if PrimInt63.eqb k 4%uint63 then ALU_SLTU else if PrimInt63.eqb k 5%uint63 then ALU_XOR
  else if PrimInt63.eqb k 6%uint63 then ALU_SRL else if PrimInt63.eqb k 7%uint63 then ALU_SRA
  else if PrimInt63.eqb k 8%uint63 then ALU_OR else ALU_AND.
Definition sc_mulop (k : int) : mulop :=
  if PrimInt63.eqb k 0%uint63 then M_MUL else if PrimInt63.eqb k 1%uint63 then M_MULH
  else if PrimInt63.eqb k 2%uint63 then M_MULHSU else if PrimInt63.eqb k 3%uint63 then M_MULHU
  else if PrimInt63.eqb k 4%uint63 then M_DIV else if PrimInt63.eqb k 5%uint63 then M_DIVU
  else if PrimInt63.eqb k 6%uint63 then M_REM else M_REMU.

Fixpoint sc_list {A : Type} (rd : string -> int -> A * int) (n : nat) (s : string) (i : int) : list A * int :=
  match n with
  | O => (nil, i)
  | S n' => let '(x, j) := rd s i in let '(l, k) := sc_list rd n' s j in (x :: l, k)
  end.
Definition sc_listN {A : Type} (rd : string -> int -> A * int) (s : string) (i : int) : list A * int :=
  let '(n, j) := sc_N s i in sc_list rd n s j.

Fixpoint sc_expr (f : nat) (s : string) (i : int) : expr * int :=
  match f with
  | O => (ELit 0, i)
  | S f' =>
      let c := PrimString.get s i in
      let i1 := PrimInt63.add i 1%uint63 in
      if PrimInt63.eqb c 35%uint63 then let '(v, j) := sc_hex 16 s i1 0%uint63 in (ELit (sc_Zp v), j)
      else if PrimInt63.eqb c 36%uint63 then let '(v, j) := sc_hex 16 s i1 0%uint63 in (EVar (sc_nat 63 v), j)
      else if PrimInt63.eqb c 43%uint63 then
        let '(a, j) := sc_expr f' s i1 in let '(b, k) := sc_expr f' s j in (EAlu ALU_ADD a b, k)
      else if PrimInt63.eqb c 64%uint63 then
        let '(a, j) := sc_expr f' s i1 in let '(b, k) := sc_expr f' s j in (EMd M_MUL a b, k)
      else if PrimInt63.eqb c 45%uint63 then let '(v, j) := sc_hex 16 s i1 0%uint63 in (ELit (sc_Zn v), j)
      else if PrimInt63.eqb c 38%uint63 then
        let op := sc_aluop (PrimInt63.sub (PrimString.get s i1) 48%uint63) in
        let '(a, j) := sc_expr f' s (PrimInt63.add i 2%uint63) in let '(b, k) := sc_expr f' s j in (EAlu op a b, k)
      else if PrimInt63.eqb c 37%uint63 then
        let op := sc_aluop (PrimInt63.sub (PrimString.get s i1) 48%uint63) in
        let '(a, j) := sc_expr f' s (PrimInt63.add i 2%uint63) in let '(b, k) := sc_expr f' s j in (EAluw op a b, k)
      else if PrimInt63.eqb c 47%uint63 then
        let op := sc_mulop (PrimInt63.sub (PrimString.get s i1) 48%uint63) in
        let '(a, j) := sc_expr f' s (PrimInt63.add i 2%uint63) in let '(b, k) := sc_expr f' s j in (EMd op a b, k)
      else if PrimInt63.eqb c 124%uint63 then
        let op := sc_mulop (PrimInt63.sub (PrimString.get s i1) 48%uint63) in
        let '(a, j) := sc_expr f' s (PrimInt63.add i 2%uint63) in let '(b, k) := sc_expr f' s j in (EMdw op a b, k)
      else if PrimInt63.eqb c 91%uint63 then
        let '(lo, j) := sc_N s i1 in let '(n, k) := sc_N s j in let '(e, l) := sc_expr f' s k in (EExt false lo n e, l)
      else if PrimInt63.eqb c 93%uint63 then
        let '(lo, j) := sc_N s i1 in let '(n, k) := sc_N s j in let '(e, l) := sc_expr f' s k in (EExt true lo n e, l)
      else if PrimInt63.eqb c 123%uint63 then
        let '(b, j) := sc_N s i1 in let '(z, k) := sc_Z s j in let '(n, l) := sc_N s k in (EBlob false b z n, l)
      else if PrimInt63.eqb c 125%uint63 then
        let '(b, j) := sc_N s i1 in let '(z, k) := sc_Z s j in let '(n, l) := sc_N s k in (EBlob true b z n, l)
      else if PrimInt63.eqb c 94%uint63 then let '(z, j) := sc_Z s i in (ELit z, j)
      else (ELit 0, i1)
  end.
Definition sc_E (s : string) (i : int) : expr * int := sc_expr 200 s i.

Definition sc_saddr (s : string) (i : int) : saddr * int :=
  let '(b, j) := sc_E s i in let '(o, k) := sc_Z s j in (SA b o, k).
Definition sc_sentry (s : string) (i : int) : sentry * int :=
  let '(a, j) := sc_saddr s i in let '(w, k) := sc_N s j in let '(v, l) := sc_E s k in (SE a w v, l).
Definition sc_pair_se (s : string) (i : int) : (saddr * expr) * int :=
  let '(a, j) := sc_saddr s i in let '(e, k) := sc_E s j in ((a, e), k).
Definition sc_pair_ee (s : string) (i : int) : (expr * expr) * int :=
  let '(a, j) := sc_E s i in let '(e, k) := sc_E s j in ((a, e), k).

Definition sc_kentry (s : string) (i : int) : kentry * int :=
  let c := PrimString.get s i in
  let i1 := PrimInt63.add i 1%uint63 in
  if PrimInt63.eqb c 33%uint63 then
    let '(a, j) := sc_saddr s i1 in let '(w, k) := sc_N s j in let '(v, l) := sc_E s k in (KWord a w v, l)
  else if PrimInt63.eqb c 37%uint63 then
    let '(lo, j) := sc_Z s i1 in let '(hi, k) := sc_Z s j in (KImg lo hi, k)
  else if PrimInt63.eqb c 39%uint63 then
    let '(e, j) := sc_E s i1 in let '(lo, k) := sc_Z s j in let '(hi, l) := sc_Z s k in (KRange e lo hi, l)
  else if PrimInt63.eqb c 35%uint63 then
    let '(a, j) := sc_saddr s i1 in let '(n, k) := sc_E s j in (KZero a n, k)
  else if PrimInt63.eqb c 36%uint63 then
    let '(a, j) := sc_saddr s i1 in let '(n, k) := sc_E s j in let '(b, l) := sc_N s k in (KBlob a n b, l)
  else if PrimInt63.eqb c 38%uint63 then
    let '(e, j) := sc_E s i1 in let '(m, k) := sc_Z s j in (KAlign e m, k)
  else if PrimInt63.eqb c 40%uint63 then
    let '(a, j) := sc_saddr s i1 in let '(n, k) := sc_E s j in (KWr a n, k)
  else if PrimInt63.eqb c 41%uint63 then
    let '(a1, j) := sc_saddr s i1 in let '(n1, k) := sc_E s j in
    let '(a2, l) := sc_saddr s k in let '(n2, m) := sc_E s l in (KDisj a1 n1 a2 n2, m)
  else if PrimInt63.eqb c 43%uint63 then
    let '(a, j) := sc_saddr s i1 in let '(n, k) := sc_E s j in let '(z, l) := sc_Z s k in (KFill a n z, l)
  else if PrimInt63.eqb c 44%uint63 then
    let '(a, j) := sc_saddr s i1 in let '(n, k) := sc_E s j in (KUnk a n, k)
  else (KImg 0 0, i1).

Definition sc_osaddr (s : string) (i : int) : option saddr * int :=
  if PrimInt63.eqb (PrimString.get s i) 35%uint63
  then let '(a, j) := sc_saddr s (PrimInt63.add i 1%uint63) in (Some a, j)
  else (None, PrimInt63.add i 1%uint63).

Definition sc_sstate (s : string) (i : int) : sym_state * int :=
  let '(p, i1) := sc_Z s i in
  let '(rg, i2) := sc_listN sc_E s i1 in
  let '(lg, i3) := sc_listN sc_sentry s i2 in
  let '(kn, i4) := sc_listN sc_kentry s i3 in
  let '(nx, i5) := sc_N s i4 in
  let '(rv, i6) := sc_osaddr s i5 in
  (SSR p rg lg kn nx rv, i6).

Definition sc_pair {A B : Type} (ra : string -> int -> A * int) (rb : string -> int -> B * int) (s : string) (i : int) : (A * B) * int :=
  let '(a, j) := ra s i in let '(b, k) := rb s j in ((a, b), k).
Definition lst {A : Type} (rd : string -> int -> A * int) : string -> int -> list A * int := sc_listN rd.
Definition sc_opt {A : Type} (rd : string -> int -> A * int) (s : string) (i : int) : option A * int :=
  if PrimInt63.eqb (PrimString.get s i) 35%uint63
  then let '(a, j) := rd s (PrimInt63.add i 1%uint63) in (Some a, j)
  else (None, PrimInt63.add i 1%uint63).
Definition sc_bool (s : string) (i : int) : bool * int := (PrimInt63.eqb (PrimString.get s i) 35%uint63, PrimInt63.add i 1%uint63).

Definition sc_regionP (s : string) (i : int) : SGP.region * int :=
  let '(b, j) := sc_E s i in let '(o, k) := sc_Z s j in let '(n, l) := sc_E s k in ((b, o, n), l).
Definition sc_regionR (s : string) (i : int) : SR.region * int :=
  let '(b, j) := sc_E s i in let '(o, k) := sc_Z s j in let '(n, l) := sc_Z s k in ((b, o, n), l).
Definition sc_sstep (s : string) (i : int) : SR.sstep * int :=
  let c := PrimString.get s i in
  let i1 := PrimInt63.add i 1%uint63 in
  if PrimInt63.eqb c 33%uint63 then let '(l, j) := sc_listN sc_Z s i1 in (SR.SBlock l, j)
  else if PrimInt63.eqb c 35%uint63 then (SR.SCopy, i1)
  else if PrimInt63.eqb c 36%uint63 then (SR.SFill, i1)
  else if PrimInt63.eqb c 37%uint63 then let '(n, j) := sc_N s i1 in (SR.SFsdSeq n, j)
  else if PrimInt63.eqb c 38%uint63 then let '(n, j) := sc_N s i1 in (SR.SFldSeq n, j)
  else if PrimInt63.eqb c 39%uint63 then let '(k, j) := sc_Z s i1 in (SR.SStrlen k, j)
  else if PrimInt63.eqb c 40%uint63 then let '(k, j) := sc_Z s i1 in (SR.SExpect k, j)
  else if PrimInt63.eqb c 41%uint63 then let '(k, j) := sc_Z s i1 in (SR.SDiamond k, j)
  else let '(n, j) := sc_N s i1 in (SR.SEvalReg n, j).
Definition sc_aitem (s : string) (i : int) : SGA.aitem * int :=
  let c := PrimString.get s i in
  let i1 := PrimInt63.add i 1%uint63 in
  if PrimInt63.eqb c 33%uint63 then let '(st, j) := sc_sstep s i1 in (SGA.AStep st, j)
  else if PrimInt63.eqb c 35%uint63 then (SGA.ACopyX, i1) else (SGA.AFillX, i1).

Definition run {A : Type} (rd : string -> int -> A * int) (s : string) : A := fst (rd s 0%uint63).

Module StrNota.
  Export PrimString.PStringNotations.
End StrNota.
