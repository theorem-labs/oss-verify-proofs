(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool.
From Stdlib Require Import PrimInt63 Uint63.
From Stdlib Require Export PrimString.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require Import AxSymExec3 AsanPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.

Module AcsDec.
Local Open Scope Z_scope.

Definition ch (s : string) (i : int) : int := PrimString.get s i.
Definition zof (c : int) : Z := Uint63.to_Z c.

Fixpoint znum (f : nat) (s : string) (i : int) (sh : Z) (acc : Z) : Z * int :=
  match f with
  | O => (acc, i)
  | S f' =>
      let c := ch s i in
      if PrimInt63.ltb c 80%uint63
      then znum f' s (PrimInt63.add i 1%uint63) (sh + 5) (acc + Z.shiftl (zof c - 48) sh)
      else (acc + Z.shiftl (zof c - 80) sh, PrimInt63.add i 1%uint63)
  end.

Definition num (s : string) (i : int) : Z * int :=
  if PrimInt63.eqb (ch s i) 45%uint63
  then let '(v, j) := znum 16 s (PrimInt63.add i 1%uint63) 0 0 in (Z.opp v, j)
  else znum 16 s i 0 0.
Definition nnum (s : string) (i : int) : nat * int := let '(v, j) := num s i in (Z.to_nat v, j).
Definition bit (s : string) (i : int) : bool := PrimInt63.eqb (ch s i) 49%uint63.
Definition code (s : string) (i : int) : Z := zof (ch s i) - 48.

Definition aluop_of (k : Z) : aluop :=
  match k with
  | 0 => ALU_ADD | 1 => ALU_SUB | 2 => ALU_SLL | 3 => ALU_SLT | 4 => ALU_SLTU | 5 => ALU_XOR | 6 => ALU_SRL | 7 => ALU_SRA | 8 => ALU_OR
  | _ => ALU_AND
  end.
Definition mulop_of (k : Z) : mulop :=
  match k with
  | 0 => M_MUL | 1 => M_MULH | 2 => M_MULHSU | 3 => M_MULHU | 4 => M_DIV | 5 => M_DIVU | 6 => M_REM | _ => M_REMU
  end.
Definition mkind_of (k : Z) : mkind :=
  match k with
  | 0 => KRW | 1 => KRWLAZY | 2 => KNONE | 3 => KNONELAZY | 4 => KFOG | 5 => KHOLE | _ => KRWE
  end.

Record dst := DS {
  d_i : int;
  d_es : list expr;
  d_ks : list kentry;
  d_ms : list amap;
  d_vis : list (expr * expr); d_gh : list (expr * expr); d_pg : bool;
  d_ss : option sym_state;
  d_out : option acs;
  d_ok : bool }.

Definition bad (d : dst) : dst :=
  DS (d_i d) (d_es d) (d_ks d) (d_ms d) (d_vis d) (d_gh d) (d_pg d) (d_ss d) (d_out d) false.
Definition pushe (d : dst) (j : int) (e : expr) : dst :=
  DS j (e :: d_es d) (d_ks d) (d_ms d) (d_vis d) (d_gh d) (d_pg d) (d_ss d) (d_out d) (d_ok d).
Definition sete (d : dst) (j : int) (es : list expr) : dst :=
  DS j es (d_ks d) (d_ms d) (d_vis d) (d_gh d) (d_pg d) (d_ss d) (d_out d) (d_ok d).
Definition addk (d : dst) (j : int) (es : list expr) (k : kentry) : dst :=
  DS j es (k :: d_ks d) (d_ms d) (d_vis d) (d_gh d) (d_pg d) (d_ss d) (d_out d) (d_ok d).

Definition tok (s : string) (d : dst) : dst :=
  let i := d_i d in let c := ch s i in let i1 := PrimInt63.add i 1%uint63 in
  if PrimInt63.eqb c 112%uint63   then let '(n, j) := num s i1 in pushe d j (ELit n)
  else if PrimInt63.eqb c 113%uint63   then let '(n, j) := nnum s i1 in pushe d j (EVar n)
  else if PrimInt63.eqb c 114%uint63   then
    match d_es d with b :: a :: r => sete d (PrimInt63.add i 2%uint63) (EAlu (aluop_of (code s i1)) a b :: r) | _ => bad d end
  else if PrimInt63.eqb c 115%uint63   then
    match d_es d with b :: a :: r => sete d (PrimInt63.add i 2%uint63) (EAluw (aluop_of (code s i1)) a b :: r) | _ => bad d end
  else if PrimInt63.eqb c 116%uint63   then
    match d_es d with b :: a :: r => sete d (PrimInt63.add i 2%uint63) (EMd (mulop_of (code s i1)) a b :: r) | _ => bad d end
  else if PrimInt63.eqb c 117%uint63   then
    match d_es d with b :: a :: r => sete d (PrimInt63.add i 2%uint63) (EMdw (mulop_of (code s i1)) a b :: r) | _ => bad d end
  else if PrimInt63.eqb c 118%uint63   then
    let b := bit s i1 in let '(lo, j) := nnum s (PrimInt63.add i 2%uint63) in let '(n, k) := nnum s j in
    match d_es d with e :: r => sete d k (EExt b lo n e :: r) | _ => bad d end
  else if PrimInt63.eqb c 119%uint63   then
    let b := bit s i1 in let '(k, j) := nnum s (PrimInt63.add i 2%uint63) in let '(o, l) := num s j in let '(n, m) := nnum s l in
    pushe d m (EBlob b k o n)
  else if PrimInt63.eqb c 120%uint63   then
    let '(off, j) := num s i1 in let '(w, k) := nnum s j in
    match d_es d with v :: b :: r => addk d k r (KWord (SA b off) w v) | _ => bad d end
  else if PrimInt63.eqb c 121%uint63   then
    let '(off, j) := num s i1 in
    match d_es d with n :: b :: r => addk d j r (KZero (SA b off) n) | _ => bad d end
  else if PrimInt63.eqb c 122%uint63   then
    let '(off, j) := num s i1 in let '(k, l) := nnum s j in
    match d_es d with n :: b :: r => addk d l r (KBlob (SA b off) n k) | _ => bad d end
  else if PrimInt63.eqb c 123%uint63   then
    let '(lo, j) := num s i1 in let '(hi, k) := num s j in addk d k (d_es d) (KImg lo hi)
  else if PrimInt63.eqb c 124%uint63   then
    let '(m, j) := num s i1 in
    match d_es d with e :: r => addk d j r (KAlign e m) | _ => bad d end
  else if PrimInt63.eqb c 125%uint63   then
    let '(lo, j) := num s i1 in let '(hi, k) := num s j in
    match d_es d with e :: r => addk d k r (KRange e lo hi) | _ => bad d end
  else if PrimInt63.eqb c 126%uint63   then
    let '(off, j) := num s i1 in
    match d_es d with n :: b :: r => addk d j r (KWr (SA b off) n) | _ => bad d end
  else if PrimInt63.eqb c 33%uint63   then
    let '(o1, j) := num s i1 in let '(o2, k) := num s j in
    match d_es d with n2 :: b2 :: n1 :: b1 :: r => addk d k r (KDisj (SA b1 o1) n1 (SA b2 o2) n2) | _ => bad d end
  else if PrimInt63.eqb c 35%uint63   then
    let '(off, j) := num s i1 in let '(cz, k) := num s j in
    match d_es d with n :: b :: r => addk d k r (KFill (SA b off) n cz) | _ => bad d end
  else if PrimInt63.eqb c 36%uint63   then
    let '(off, j) := num s i1 in
    match d_es d with n :: b :: r => addk d j r (KUnk (SA b off) n) | _ => bad d end
  else if PrimInt63.eqb c 37%uint63   then
    match d_es d with
    | len :: b :: r => DS (PrimInt63.add i 2%uint63) r (d_ks d) (AM b len (mkind_of (code s i1)) :: d_ms d) (d_vis d) (d_gh d) (d_pg d) (d_ss d) (d_out d) (d_ok d)
    | _ => bad d end
  else if PrimInt63.eqb c 38%uint63   then
    match d_es d with
    | b :: a :: r => if d_pg d then DS i1 r (d_ks d) (d_ms d) (d_vis d) ((a, b) :: d_gh d) true (d_ss d) (d_out d) (d_ok d)
                     else DS i1 r (d_ks d) (d_ms d) ((a, b) :: d_vis d) (d_gh d) false (d_ss d) (d_out d) (d_ok d)
    | _ => bad d end
  else if PrimInt63.eqb c 39%uint63   then
    DS i1 (d_es d) (d_ks d) (d_ms d) (d_vis d) (d_gh d) true (d_ss d) (d_out d) (d_ok d)
  else if PrimInt63.eqb c 41%uint63   then
    let '(pc, j) := num s i1 in let '(nx, k) := nnum s j in
    DS k [] [] (d_ms d) (d_vis d) (d_gh d) (d_pg d) (Some (SS pc (List.rev (d_es d)) [] (List.rev (d_ks d)) nx)) (d_out d) (d_ok d)
  else if PrimInt63.eqb c 43%uint63   then
    let '(tot, j) := num s i1 in let '(ylo, k) := num s j in let '(ea, l) := num s k in let '(ab, m) := num s l in
    let tid := bit s m in let f := code s (PrimInt63.add m 1%uint63) in let m2 := PrimInt63.add m 2%uint63 in
    let fdo : option (afd * expr * int) :=
      match f, d_es d with
      | 0, [brk] => Some (FdStd, brk, m2)
      | 2, [brk] => Some (FdDir, brk, m2)
      | 1, [off; len; brk] => let '(kk, m3) := nnum s m2 in Some (FdFile kk len off, brk, m3)
      | _, _ => None
      end in
    match d_ss d, fdo with
    | Some ss, Some (fd, brk, e) =>
        DS (PrimString.length s) [] [] [] [] [] false None
           (Some (ACS ss (List.rev (d_ms d)) tot ylo ea (List.rev (d_vis d)) (List.rev (d_gh d)) ab brk fd tid)) (d_ok d)
    | _, _ => bad d
    end
  else bad d.

Fixpoint loop (p : positive) (s : string) (len : int) (d : dst) : dst * bool :=
  let step1 (d : dst) : dst * bool :=
    if PrimInt63.ltb (d_i d) len then (if d_ok d then (tok s d, false) else (d, true)) else (d, true) in
  match p with
  | xH => step1 d
  | xO q => let '(d1, fin) := loop q s len d in if fin then (d1, true) else loop q s len d1
  | xI q => let '(d1, fin) := loop q s len d in if fin then (d1, true) else
            let '(d2, fin2) := loop q s len d1 in if fin2 then (d2, true) else step1 d2
  end.

Definition BAD : acs := ACS (SS 0 [] [] [] 0%nat) [] 0 0 0 [] [] 0 (ELit 0) FdStd false.

Definition acs_dec (s : string) : acs :=
  let d0 := DS 0%uint63 [] [] [] [] [] false None None true in
  let '(d, _) := loop (2^40)%positive s (PrimString.length s) d0 in
  match d_ok d, d_out d with
  | true, Some a => a
  | _, _ => BAD
  end.

End AcsDec.
