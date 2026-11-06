(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From Stdlib Require Import PrimInt63 Uint63 PrimString.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import W64 Val FI St Plan.

Record dst := DS {
  d_i : int; d_sv : list sv; d_fc : list fact; d_pl : list plan;
  d_svp : IMap.t sv; d_nsv : int; d_stp : IMap.t (list int); d_nst : int; d_ok : bool }.

Definition ch (s : string) (i : int) : int := PrimString.get s i.

Fixpoint dnum (f : nat) (s : string) (i : int) (sh acc : int) : int * int :=
  match f with
  | O => (acc, i)
  | S f' =>
      let c := ch s i in
      if PrimInt63.ltb c 80%uint63
      then dnum f' s (PrimInt63.add i 1%uint63) (PrimInt63.add sh 5%uint63) (PrimInt63.lor acc (PrimInt63.lsl (PrimInt63.sub c 48%uint63) sh))
      else (PrimInt63.lor acc (PrimInt63.lsl (PrimInt63.sub c 80%uint63) sh), PrimInt63.add i 1%uint63)
  end.
Definition num (s : string) (i : int) : int * int := dnum 14 s i 0%uint63 0%uint63.
Definition nat_of (n : int) : nat := Z.to_nat (Uint63.to_Z n).
Definition bit (s : string) (i : int) : bool := PrimInt63.eqb (ch s i) 49%uint63.

Fixpoint nums (n : nat) (s : string) (i : int) (acc : list int) : list int * int :=
  match n with
  | O => (List.rev' acc, i)
  | S n' => let '(v, j) := num s i in nums n' s j (v :: acc)
  end.

Definition aluop_of (c : int) : aluop :=
  let k := PrimInt63.sub c 48%uint63 in
  if PrimInt63.eqb k 0%uint63 then ALU_ADD else if PrimInt63.eqb k 1%uint63 then ALU_SUB else if PrimInt63.eqb k 2%uint63 then ALU_SLL
  else if PrimInt63.eqb k 3%uint63 then ALU_SLT else if PrimInt63.eqb k 4%uint63 then ALU_SLTU else if PrimInt63.eqb k 5%uint63 then ALU_XOR
  else if PrimInt63.eqb k 6%uint63 then ALU_SRL else if PrimInt63.eqb k 7%uint63 then ALU_SRA else if PrimInt63.eqb k 8%uint63 then ALU_OR
  else ALU_AND.
Definition mulop_of (c : int) : mulop :=
  let k := PrimInt63.sub c 48%uint63 in
  if PrimInt63.eqb k 0%uint63 then M_MUL else if PrimInt63.eqb k 1%uint63 then M_MULH else if PrimInt63.eqb k 2%uint63 then M_MULHSU
  else if PrimInt63.eqb k 3%uint63 then M_MULHU else if PrimInt63.eqb k 4%uint63 then M_DIV else if PrimInt63.eqb k 5%uint63 then M_DIVU
  else if PrimInt63.eqb k 6%uint63 then M_REM else M_REMU.
Definition ffmt_of (c : int) : ffmt := if PrimInt63.eqb c 48%uint63 then FMT_S else FMT_D.
Definition rmode_of (c : int) : rmode :=
  let k := PrimInt63.sub c 48%uint63 in
  if PrimInt63.eqb k 0%uint63 then RNE else if PrimInt63.eqb k 1%uint63 then RTZ else if PrimInt63.eqb k 2%uint63 then RDN
  else if PrimInt63.eqb k 3%uint63 then RUP else RMM.
Definition reg_of (c : int) : r5 :=
  match r5_of_Z (Uint63.to_Z (PrimInt63.sub c 48%uint63)) with Some r => r | None => X0 end.

Definition bad (d : dst) : dst := DS (d_i d) (d_sv d) (d_fc d) (d_pl d) (d_svp d) (d_nsv d) (d_stp d) (d_nst d) false.
Definition seti (d : dst) (i : int) : dst := DS i (d_sv d) (d_fc d) (d_pl d) (d_svp d) (d_nsv d) (d_stp d) (d_nst d) (d_ok d).
Definition psv (d : dst) (i : int) (v : sv) : dst := DS i (v :: d_sv d) (d_fc d) (d_pl d) (d_svp d) (d_nsv d) (d_stp d) (d_nst d) (d_ok d).
Definition ssv (d : dst) (i : int) (l : list sv) : dst := DS i l (d_fc d) (d_pl d) (d_svp d) (d_nsv d) (d_stp d) (d_nst d) (d_ok d).
Definition ppl (d : dst) (i : int) (svs : list sv) (pl : list plan) : dst :=
  DS i svs (d_fc d) pl (d_svp d) (d_nsv d) (d_stp d) (d_nst d) (d_ok d).

Fixpoint popn {A} (n : nat) (st acc : list A) : option (list A * list A) :=
  match n with
  | O => Some (acc, st)
  | S n' => match st with x :: st' => popn n' st' (x :: acc) | [] => None end
  end.

Definition dstops (d : dst) (s : string) (i : int) : option (list int * int) :=
  let c := ch s i in let i1 := PrimInt63.add i 1%uint63 in
  if PrimInt63.eqb c 83%uint63   then
    let '(n, j) := num s i1 in match IMap.find n (d_stp d) with Some l => Some (l, j) | None => None end
  else if PrimInt63.eqb c 84%uint63   then
    let '(b, j) := num s i1 in let '(n, k) := num s (PrimInt63.add j 1%uint63) in
    match IMap.find n (d_stp d) with Some l => Some (b :: l, k) | None => None end
  else if PrimInt63.eqb c 108%uint63   then
    let '(n, j) := num s i1 in let '(l, k) := nums (nat_of n) s j [] in Some (l, k)
  else None.

Fixpoint idrange (n : nat) (hi : int) (acc : list (int * sv)) : list (int * sv) :=
  match n with
  | O => acc
  | S n' => idrange n' (PrimInt63.sub hi 1%uint63) ((hi, VP hi wzero) :: acc)
  end.
Fixpoint dsubst (n : nat) (s : string) (i : int) (svs : list sv) (acc : list (int * sv)) : option (list (int * sv) * int * list sv) :=
  match n with
  | O => Some (acc, i, svs)
  | S n' =>
      let c := ch s i in let i1 := PrimInt63.add i 1%uint63 in
      if PrimInt63.eqb c 105%uint63   then
        let '(lo, j) := num s i1 in let '(hi, k) := num s j in
        dsubst n' s k svs (idrange (nat_of (PrimInt63.add (PrimInt63.sub hi lo) 1%uint63)) hi acc)
      else if PrimInt63.eqb c 106%uint63   then
        let '(key, j) := num s i1 in
        match svs with v :: svs' => dsubst n' s j svs' ((key, v) :: acc) | [] => None end
      else None
  end.

Definition w64_at (s : string) (i : int) : w64 * int :=
  let b := bit s i in let '(v, j) := num s (PrimInt63.add i 1%uint63) in (W64 b v, j).

Definition tok (s : string) (d : dst) : dst :=
  let i := d_i d in let c := ch s i in let i1 := PrimInt63.add i 1%uint63 in
  let bin (mk : sv -> sv -> sv) (j : int) : dst := match d_sv d with b :: a :: r => ssv d j (mk a b :: r) | _ => bad d end in
  let fct (mk : sv -> sv -> fact) : dst :=
    match d_sv d with
    | b :: a :: r => DS i1 r (mk a b :: d_fc d) (d_pl d) (d_svp d) (d_nsv d) (d_stp d) (d_nst d) (d_ok d)
    | _ => bad d end in
  if PrimInt63.eqb c 76%uint63   then let '(v, j) := num s i1 in psv d j (VL (W64 false v))
  else if PrimInt63.eqb c 80%uint63   then let '(k, j) := num s i1 in let '(o, l) := num s j in psv d l (VP k (W64 false o))
  else if PrimInt63.eqb c 82%uint63   then
    let '(n, j) := num s i1 in match IMap.find n (d_svp d) with Some v => psv d j v | None => bad d end
  else if PrimInt63.eqb c 121%uint63   then
    match dstops d s i1, d_pl d with
    | Some (l, j), k :: r => ppl d j (d_sv d) (PRun l k :: r)
    | _, _ => bad d end
  else if PrimInt63.eqb c 107%uint63   then
    let '(cid, j) := num s i1 in let '(n, l) := num s j in
    match popn (nat_of n) (d_pl d) [] with Some (ks, r) => ppl d l (d_sv d) (PCall cid ks :: r) | None => bad d end
  else if PrimInt63.eqb c 85%uint63   then
    let '(tid, j) := num s i1 in let '(n, l) := num s j in
    match dsubst (nat_of n) s l (d_sv d) [] with Some (sg, m, svs) => ppl d m svs (PCut tid sg :: d_pl d) | None => bad d end
  else if PrimInt63.eqb c 99%uint63   then
    match d_pl d with kF :: kT :: r => ppl d i1 (d_sv d) (PCase kT kF :: r) | _ => bad d end
  else if PrimInt63.eqb c 120%uint63   then let '(v, j) := num s i1 in ppl d j (d_sv d) (PFail v :: d_pl d)
  else if PrimInt63.eqb c 65%uint63   then bin (VAlu (aluop_of (ch s i1))) (PrimInt63.add i 2%uint63)
  else if PrimInt63.eqb c 77%uint63   then let '(v, j) := num s i1 in psv d j (VL (W64 true v))
  else if PrimInt63.eqb c 81%uint63   then let '(k, j) := num s i1 in let '(o, l) := num s j in psv d l (VP k (W64 true o))
  else if PrimInt63.eqb c 88%uint63   then
    let sx := bit s i1 in let '(lo, j) := num s (PrimInt63.add i 2%uint63) in let '(n, l) := num s j in
    match d_sv d with a :: r => ssv d l (VExt sx lo n a :: r) | _ => bad d end
  else if PrimInt63.eqb c 66%uint63   then
    let sx := bit s i1 in let '(jb, j) := num s (PrimInt63.add i 2%uint63) in let '(n, l) := num s j in
    match d_sv d with off :: r => ssv d l (VBlob sx jb off n :: r) | _ => bad d end
  else if PrimInt63.eqb c 87%uint63   then bin (VAluw (aluop_of (ch s i1))) (PrimInt63.add i 2%uint63)
  else if PrimInt63.eqb c 68%uint63   then bin (VMd (mulop_of (ch s i1))) (PrimInt63.add i 2%uint63)
  else if PrimInt63.eqb c 69%uint63   then bin (VMdw (mulop_of (ch s i1))) (PrimInt63.add i 2%uint63)
  else if PrimInt63.eqb c 73%uint63   then
    let '(lo, j) := num s i1 in let '(n, l) := num s j in
    match d_sv d with v :: a :: r => ssv d l (VIns lo n a v :: r) | _ => bad d end
  else if PrimInt63.eqb c 71%uint63   then
    let sx := bit s i1 in let '(k, j) := num s (PrimInt63.add i 2%uint63) in let '(o, l) := w64_at s j in let '(n, m) := num s l in
    psv d m (VBg sx k o n)
  else if PrimInt63.eqb c 70%uint63   then
    let k := ch s i1 in
    match d_sv d with
    | a :: r =>
        if PrimInt63.eqb k 48%uint63 then ssv d (PrimInt63.add i 2%uint63) (VF1 F1_NANBOX a :: r)
        else if PrimInt63.eqb k 49%uint63 then ssv d (PrimInt63.add i 2%uint63) (VF1 F1_LOW32SX a :: r)
        else ssv d (PrimInt63.add i 5%uint63)
               (VF1 (F1_FCVT (ffmt_of (ch s (PrimInt63.add i 2%uint63))) (ffmt_of (ch s (PrimInt63.add i 3%uint63)))
                             (rmode_of (ch s (PrimInt63.add i 4%uint63)))) a :: r)
    | [] => bad d end
  else if PrimInt63.eqb c 90%uint63   then
    match d_sv d with
    | v :: r => DS i1 r (d_fc d) (d_pl d) (IMap.add (d_nsv d) v (d_svp d)) (PrimInt63.add (d_nsv d) 1%uint63) (d_stp d) (d_nst d) (d_ok d)
    | [] => bad d end
  else if PrimInt63.eqb c 89%uint63   then
    let '(n, j) := num s i1 in let '(l, k) := nums (nat_of n) s j [] in
    DS k (d_sv d) (d_fc d) (d_pl d) (d_svp d) (d_nsv d) (IMap.add (d_nst d) l (d_stp d)) (PrimInt63.add (d_nst d) 1%uint63) (d_ok d)
  else if PrimInt63.eqb c 86%uint63   then
    let '(tid, j) := num s i1 in let '(n, l) := num s j in
    match dsubst (nat_of n) s l (d_sv d) [] with Some (sg, m, svs) => ppl d m svs (PCutDec tid sg :: d_pl d) | None => bad d end
  else if PrimInt63.eqb c 119%uint63   then
    let '(tid, j) := num s i1 in let '(n, l) := num s j in
    match dsubst (nat_of n) s l (d_sv d) [] with Some (sg, m, svs) => ppl d m svs (PEcall tid sg :: d_pl d) | None => bad d end
  else if PrimInt63.eqb c 115%uint63   then
    let r := reg_of (ch s i1) in let '(n, j) := num s (PrimInt63.add i 2%uint63) in let '(cnt, l) := num s j in
    match popn (nat_of cnt) (d_pl d) [] with Some (ks, rest) => ppl d l (d_sv d) (PSplit r n ks :: rest) | None => bad d end
  else if PrimInt63.eqb c 103%uint63   then
    match d_sv d, d_pl d with v :: svs, k :: r => ppl d (PrimInt63.add i 2%uint63) svs (PSetReg (reg_of (ch s i1)) v k :: r) | _, _ => bad d end
  else if PrimInt63.eqb c 98%uint63   then
    let '(x, j) := num s i1 in
    match d_sv d, d_pl d with v :: svs, k :: r => ppl d j svs (PSubst x v k :: r) | _, _ => bad d end
  else if PrimInt63.eqb c 109%uint63   then
    match d_pl d with k :: r => ppl d (PrimInt63.add i 2%uint63) (d_sv d) (PName (reg_of (ch s i1)) k :: r) | [] => bad d end
  else if PrimInt63.eqb c 104%uint63   then
    let '(x, j) := num s i1 in
    match d_sv d, d_pl d with v :: svs, k :: r => ppl d j svs (PSetHi x v k :: r) | _, _ => bad d end
  else if PrimInt63.eqb c 113%uint63   then
    match d_fc d, d_pl d with
    | f :: fs, k :: r => DS i1 (d_sv d) fs (PAssume f k :: r) (d_svp d) (d_nsv d) (d_stp d) (d_nst d) (d_ok d)
    | _, _ => bad d end
  else if PrimInt63.eqb c 102%uint63   then
    let '(k0, j) := num s i1 in let '(glo, l) := num s j in let '(ghi, m) := num s l in
    match d_pl d with k :: r => ppl d m (d_sv d) (PForget k0 glo ghi k :: r) | [] => bad d end
  else if PrimInt63.eqb c 112%uint63   then
    let '(n, j) := num s i1 in
    match d_pl d with k :: r => ppl d j (d_sv d) (PDropFacts (nat_of n) k :: r) | [] => bad d end
  else if PrimInt63.eqb c 114%uint63   then
    let '(k, j) := num s i1 in let '(lo, l) := w64_at s j in let '(hi, m) := w64_at s l in
    DS m (d_sv d) (FRange k lo hi :: d_fc d) (d_pl d) (d_svp d) (d_nsv d) (d_stp d) (d_nst d) (d_ok d)
  else if PrimInt63.eqb c 97%uint63   then
    let '(k, j) := num s i1 in let '(m0, l) := num s j in
    DS l (d_sv d) (FAlign k m0 :: d_fc d) (d_pl d) (d_svp d) (d_nsv d) (d_stp d) (d_nst d) (d_ok d)
  else if PrimInt63.eqb c 117%uint63   then fct FULt
  else if PrimInt63.eqb c 118%uint63   then fct FULe
  else if PrimInt63.eqb c 101%uint63   then fct FEq
  else if PrimInt63.eqb c 110%uint63   then fct FNe
  else if PrimInt63.eqb c 111%uint63   then fct FSLt
  else if PrimInt63.eqb c 116%uint63   then fct FSLe
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

Definition dec_plan (s : string) : plan :=
  let d0 := DS 0%uint63 [] [] [] IMap.empty 0%uint63 IMap.empty 0%uint63 true in
  let '(d, _) := loop (2^40)%positive s (PrimString.length s) d0 in
  match d_ok d, d_pl d, d_sv d, d_fc d with
  | true, [p], [], [] => p
  | _, _, _, _ => PFail 0%uint63
  end.

