(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool.
From Stdlib Require Import PrimInt63 Uint63.
From Stdlib Require Export PrimString.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require Import AxSymExec3 AsanPlan MainExport.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.

Module MfDec.
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
Definition code (s : string) (i : int) : Z := zof (ch s i) - 48.
Definition mkind_of (k : Z) : mkind :=
  match k with
  | 0 => KRW | 1 => KRWLAZY | 2 => KNONE | 3 => KNONELAZY | 4 => KFOG | 5 => KHOLE | _ => KRWE
  end.

Record dst := DS {
  d_i : int;
  d_es : list zexp;
  d_mf : list mfact; d_pf : list pfact; d_le : list lentry; d_zz : list (zexp * zexp);
  d_ok : bool }.

Definition bad (d : dst) : dst := DS (d_i d) (d_es d) (d_mf d) (d_pf d) (d_le d) (d_zz d) false.
Definition pushe (d : dst) (j : int) (e : zexp) : dst := DS j (e :: d_es d) (d_mf d) (d_pf d) (d_le d) (d_zz d) (d_ok d).
Definition sete (d : dst) (j : int) (es : list zexp) : dst := DS j es (d_mf d) (d_pf d) (d_le d) (d_zz d) (d_ok d).
Definition addm (d : dst) (j : int) (es : list zexp) (m : mfact) : dst := DS j es (m :: d_mf d) (d_pf d) (d_le d) (d_zz d) (d_ok d).
Definition addp (d : dst) (j : int) (es : list zexp) (p : pfact) : dst := DS j es (d_mf d) (p :: d_pf d) (d_le d) (d_zz d) (d_ok d).
Definition addl (d : dst) (j : int) (es : list zexp) (l : lentry) : dst := DS j es (d_mf d) (d_pf d) (l :: d_le d) (d_zz d) (d_ok d).

Definition tok (s : string) (d : dst) : dst :=
  let i := d_i d in let c := ch s i in let i1 := PrimInt63.add i 1%uint63 in
  if PrimInt63.eqb c 112%uint63   then let '(n, j) := num s i1 in pushe d j (ZLit n)
  else if PrimInt63.eqb c 113%uint63   then let '(n, j) := nnum s i1 in pushe d j (ZV n)
  else if PrimInt63.eqb c 114%uint63   then match d_es d with b :: a :: r => sete d i1 (ZAdd a b :: r) | _ => bad d end
  else if PrimInt63.eqb c 115%uint63   then match d_es d with b :: a :: r => sete d i1 (ZMul a b :: r) | _ => bad d end
  else if PrimInt63.eqb c 116%uint63   then match d_es d with b :: a :: r => sete d i1 (ZAnd a b :: r) | _ => bad d end
  else if PrimInt63.eqb c 117%uint63   then match d_es d with b :: a :: r => sete d i1 (ZLtu a b :: r) | _ => bad d end
  else if PrimInt63.eqb c 118%uint63   then
    let '(w, j) := nnum s i1 in match d_es d with v :: a :: r => addm d j r (MCell a w v) | _ => bad d end
  else if PrimInt63.eqb c 119%uint63   then
    let '(n, j) := num s i1 in match d_es d with a :: r => addm d j r (MZeroC a n) | _ => bad d end
  else if PrimInt63.eqb c 120%uint63   then
    let '(w, j) := nnum s i1 in match d_es d with v :: a :: r => addm d j r (MRo a w v) | _ => bad d end
  else if PrimInt63.eqb c 121%uint63   then
    let '(n, j) := num s i1 in match d_es d with a :: r => addm d j r (MZero a n) | _ => bad d end
  else if PrimInt63.eqb c 122%uint63   then
    let '(n, j) := num s i1 in let '(cz, k) := num s j in match d_es d with a :: r => addm d k r (MFill a n cz) | _ => bad d end
  else if PrimInt63.eqb c 123%uint63   then
    let '(lo, j) := num s i1 in let '(hi, k) := num s j in addm d k (d_es d) (MImg lo hi)
  else if PrimInt63.eqb c 124%uint63   then
    let '(n, j) := num s i1 in match d_es d with a :: r => addm d j r (MWr a n) | _ => bad d end
  else if PrimInt63.eqb c 125%uint63   then match d_es d with n :: a :: r => addm d i1 r (MZeroS a n) | _ => bad d end
  else if PrimInt63.eqb c 126%uint63   then match d_es d with n :: a :: r => addm d i1 r (MWrS a n) | _ => bad d end
  else if PrimInt63.eqb c 33%uint63   then
    let '(n, j) := nnum s i1 in let '(lo, k) := num s j in let '(hi, l) := num s k in addp d l (d_es d) (PVar n lo hi)
  else if PrimInt63.eqb c 35%uint63   then
    let '(lo, j) := num s i1 in let '(hi, k) := num s j in match d_es d with e :: r => addp d k r (PRange e lo hi) | _ => bad d end
  else if PrimInt63.eqb c 36%uint63   then
    let '(n1, j) := num s i1 in let '(n2, k) := num s j in
    match d_es d with a2 :: a1 :: r => addp d k r (PDisj a1 n1 a2 n2) | _ => bad d end
  else if PrimInt63.eqb c 37%uint63   then
    match d_es d with n2 :: a2 :: n1 :: a1 :: r => addp d i1 r (PDisjS a1 n1 a2 n2) | _ => bad d end
  else if PrimInt63.eqb c 38%uint63   then
    let '(n, j) := num s i1 in let k := code s j in
    match d_es d with b :: r => addl d (PrimInt63.add j 1%uint63) r (LMap b n (mkind_of k)) | _ => bad d end
  else if PrimInt63.eqb c 39%uint63   then let '(n, j) := num s i1 in addl d j (d_es d) (LFog n)
  else if PrimInt63.eqb c 43%uint63   then
    match d_es d with b :: a :: r => DS i1 r (d_mf d) (d_pf d) (d_le d) ((a, b) :: d_zz d) (d_ok d) | _ => bad d end
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

Definition run (s : string) : dst :=
  let '(d, _) := loop (2^40)%positive s (PrimString.length s) (DS 0%uint63 [] [] [] [] [] true) in d.
Definition fin (d : dst) : bool := d_ok d && match d_es d with [] => true | _ => false end.

Definition mf_dec (s : string) : list mfact := let d := run s in if fin d then List.rev (d_mf d) else [].
Definition pf_dec (s : string) : list pfact := let d := run s in if fin d then List.rev (d_pf d) else [].
Definition le_dec (s : string) : list lentry := let d := run s in if fin d then List.rev (d_le d) else [].
Definition zz_dec (s : string) : list (zexp * zexp) := let d := run s in if fin d then List.rev (d_zz d) else [].

End MfDec.
