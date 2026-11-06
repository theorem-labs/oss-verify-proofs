(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith Bool Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Unset Lia Cache.

Module W64.

Record w64 := W64 { wt : bool; wl : int }.

Definition two63 : Z := 9223372036854775808%Z.
Definition two64 : Z := 18446744073709551616%Z.

Definition w2Z (w : w64) : Z := (if wt w then two63 else 0) + to_Z (wl w).
Definition wbv (w : w64) : word := Z_to_bv 64 (w2Z w).

Definition Z2w (z : Z) : w64 :=
  let z' := z mod two64 in
  W64 (Z.leb two63 z') (of_Z (z' mod two63)).

Definition bv2w (b : word) : w64 := Z2w (bv_unsigned b).

Definition wzero : w64 := W64 false 0%uint63.
Definition wone  : w64 := W64 false 1%uint63.
Definition wlit (i : int) : w64 := W64 false i.

Definition weqb (a b : w64) : bool := Bool.eqb (wt a) (wt b) && PrimInt63.eqb (wl a) (wl b).

Definition ones63 : int := 9223372036854775807%uint63.
Definition mask32 : int := 4294967295%uint63.
Definition mask31 : int := 2147483647%uint63.
Definition bit31i : int := 2147483648%uint63.
Definition hi31of63 : int := 9223372032559808512%uint63.
Definition bit62i : int := 4611686018427387904%uint63.

Definition wltu (a b : w64) : bool :=
  match wt a, wt b with
  | false, true => true
  | true, false => false
  | _, _ => PrimInt63.ltb (wl a) (wl b)
  end.
Definition wleu (a b : w64) : bool := negb (wltu b a).

Definition wlts (a b : w64) : bool :=
  match wt a, wt b with
  | true, false => true
  | false, true => false
  | _, _ => PrimInt63.ltb (wl a) (wl b)
  end.

Definition wadd (a b : w64) : w64 :=
  let s := PrimInt63.add (wl a) (wl b) in
  let c := PrimInt63.ltb s (wl a) in
  W64 (xorb (xorb (wt a) (wt b)) c) s.

Definition wsub (a b : w64) : w64 :=
  let s := PrimInt63.sub (wl a) (wl b) in
  let c := PrimInt63.ltb (wl a) (wl b) in
  W64 (xorb (xorb (wt a) (wt b)) c) s.

Definition wneg (a : w64) : w64 := wsub wzero a.

Definition wand (a b : w64) : w64 := W64 (andb (wt a) (wt b)) (PrimInt63.land (wl a) (wl b)).
Definition wor  (a b : w64) : w64 := W64 (orb (wt a) (wt b)) (PrimInt63.lor (wl a) (wl b)).
Definition wxor (a b : w64) : w64 := W64 (xorb (wt a) (wt b)) (PrimInt63.lxor (wl a) (wl b)).
Definition wnot (a : w64) : w64 := W64 (negb (wt a)) (PrimInt63.lxor (wl a) ones63).

Definition shamt6 (b : w64) : int := PrimInt63.land (wl b) 63%uint63.
Definition shamt5 (b : w64) : int := PrimInt63.land (wl b) 31%uint63.

Definition wsll_k (a : w64) (k : int) : w64 :=
  if PrimInt63.eqb k 0%uint63 then a
  else W64 (Uint63.bit (wl a) (PrimInt63.sub 63%uint63 k)) (PrimInt63.lsl (wl a) k).

Definition wsrl_k (a : w64) (k : int) : w64 :=
  if PrimInt63.eqb k 0%uint63 then a
  else W64 false (PrimInt63.lor (PrimInt63.lsr (wl a) k)
                              (if wt a then PrimInt63.lsl 1%uint63 (PrimInt63.sub 63%uint63 k) else 0%uint63)).

Definition wsra_k (a : w64) (k : int) : w64 :=
  if PrimInt63.eqb k 0%uint63 then a
  else if wt a then

    let r := wsrl_k a k in
    W64 true (PrimInt63.lor (wl r) (PrimInt63.lsl ones63 (PrimInt63.sub 63%uint63 k)))
  else wsrl_k a k.

Definition wsll (a b : w64) : w64 := wsll_k a (shamt6 b).
Definition wsrl (a b : w64) : w64 := wsrl_k a (shamt6 b).
Definition wsra (a b : w64) : w64 := wsra_k a (shamt6 b).

Definition wofbool (b : bool) : w64 := if b then wone else wzero.

Definition wmul (a b : w64) : w64 :=
  let '(h, l) := PrimInt63.mulc (wl a) (wl b) in
  let b63 := Uint63.bit h 0%uint63 in
  let oa := Uint63.bit (wl a) 0%uint63 in
  let ob := Uint63.bit (wl b) 0%uint63 in
  W64 (xorb b63 (xorb (andb (wt a) ob) (andb (wt b) oa))) l.

Definition w2Zs (w : w64) : Z := if wt w then w2Z w - two64 else w2Z w.

Definition wmd (op : mulop) (a b : w64) : w64 :=
  match op with
  | M_MUL => wmul a b
  | M_MULH => Z2w (Z.shiftr (w2Zs a * w2Zs b) 64)
  | M_MULHSU => Z2w (Z.shiftr (w2Zs a * w2Z b) 64)
  | M_MULHU => Z2w (Z.shiftr (w2Z a * w2Z b) 64)
  | M_DIV => if weqb b wzero then Z2w (-1) else Z2w (Z.quot (w2Zs a) (w2Zs b))
  | M_DIVU => if weqb b wzero then Z2w (-1) else Z2w (Z.div (w2Z a) (w2Z b))
  | M_REM => if weqb b wzero then a else Z2w (Z.rem (w2Zs a) (w2Zs b))
  | M_REMU => if weqb b wzero then a else Z2w (Z.modulo (w2Z a) (w2Z b))
  end.

Definition walu (op : aluop) (a b : w64) : w64 :=
  match op with
  | ALU_ADD => wadd a b
  | ALU_SUB => wsub a b
  | ALU_SLL => wsll a b
  | ALU_SLT => wofbool (wlts a b)
  | ALU_SLTU => wofbool (wltu a b)
  | ALU_XOR => wxor a b
  | ALU_SRL => wsrl a b
  | ALU_SRA => wsra a b
  | ALU_OR => wor a b
  | ALU_AND => wand a b
  end.

Definition lo32 (a : w64) : int := PrimInt63.land (wl a) mask32.
Definition sx32 (i : int) : w64 :=
  if Uint63.bit i 31%uint63 then W64 true (PrimInt63.lor i hi31of63) else W64 false i.

Definition zx32 (i : int) : w64 := W64 false i.

Definition walu32 (op : aluop) (a b : w64) : w64 :=
  let x := lo32 a in let y := lo32 b in
  match op with
  | ALU_ADD => sx32 (PrimInt63.land (PrimInt63.add x y) mask32)
  | ALU_SUB => sx32 (PrimInt63.land (PrimInt63.sub x y) mask32)
  | ALU_SLL => let k := PrimInt63.land y 31%uint63 in sx32 (PrimInt63.land (PrimInt63.lsl x k) mask32)
  | ALU_SLT =>
      wofbool (PrimInt63.ltb (PrimInt63.lxor x bit31i) (PrimInt63.lxor y bit31i))
  | ALU_SLTU => wofbool (PrimInt63.ltb x y)
  | ALU_XOR => sx32 (PrimInt63.lxor x y)
  | ALU_SRL => let k := PrimInt63.land y 31%uint63 in sx32 (PrimInt63.lsr x k)
  | ALU_SRA => let k := PrimInt63.land y 31%uint63 in
      if Uint63.bit x 31%uint63
      then sx32 (PrimInt63.land (PrimInt63.lor (PrimInt63.lsr x k)
                                              (PrimInt63.lsl mask32 (PrimInt63.sub 32%uint63 k))) mask32)
      else sx32 (PrimInt63.lsr x k)
  | ALU_OR => sx32 (PrimInt63.lor x y)
  | ALU_AND => sx32 (PrimInt63.land x y)
  end.

Definition s32Z (i : int) : Z := if Uint63.bit i 31%uint63 then to_Z i - 4294967296 else to_Z i.

Definition Z2w32s (z : Z) : w64 := sx32 (of_Z (z mod 4294967296)).

Definition wmd32 (op : mulop) (a b : w64) : w64 :=
  let x := lo32 a in let y := lo32 b in
  match op with
  | M_MUL => sx32 (PrimInt63.land (PrimInt63.mul x y) mask32)
  | M_MULH => Z2w32s (Z.shiftr (s32Z x * s32Z y) 32)
  | M_MULHSU => Z2w32s (Z.shiftr (s32Z x * to_Z y) 32)
  | M_MULHU => Z2w32s (Z.shiftr (to_Z x * to_Z y) 32)
  | M_DIV => if PrimInt63.eqb y 0%uint63 then Z2w (-1) else Z2w32s (Z.quot (s32Z x) (s32Z y))
  | M_DIVU => if PrimInt63.eqb y 0%uint63 then Z2w (-1) else sx32 (PrimInt63.div x y)
  | M_REM => if PrimInt63.eqb y 0%uint63 then sx32 x else Z2w32s (Z.rem (s32Z x) (s32Z y))
  | M_REMU => if PrimInt63.eqb y 0%uint63 then sx32 x else sx32 (PrimInt63.mod x y)
  end.

Definition wbranch (c : branch_cond) (a b : w64) : bool :=
  match c with
  | BC_EQ => weqb a b
  | BC_NE => negb (weqb a b)
  | BC_LT => wlts a b
  | BC_GE => negb (wlts a b)
  | BC_LTU => wltu a b
  | BC_GEU => negb (wltu a b)
  end.

Definition ext_Z (sx : bool) (lo n : Z) (z : Z) : Z :=
  let u := (z / 2 ^ (8 * lo)) mod 2 ^ (8 * n) in
  if sx then (if Z.leb (2 ^ (8 * n - 1)) u then u - 2 ^ (8 * n) else u) mod two64 else u.

Definition wext (sx : bool) (lo n : int) (a : w64) : w64 :=
  if PrimInt63.eqb n 8%uint63 then a else
  let nbits := PrimInt63.lsl n 3%uint63 in
  let lobits := PrimInt63.lsl lo 3%uint63 in
  let m := PrimInt63.sub (PrimInt63.lsl 1%uint63 nbits) 1%uint63 in

  let sh := wsrl_k a lobits in
  let u := PrimInt63.land (wl sh) m in
  if sx && Uint63.bit u (PrimInt63.sub nbits 1%uint63)
  then W64 true (PrimInt63.lor u (PrimInt63.lxor ones63 m))
  else W64 false u.

Definition wins (lo n : int) (a v : w64) : w64 :=
  if PrimInt63.eqb n 8%uint63 then v else
  let nbits := PrimInt63.lsl n 3%uint63 in
  let lobits := PrimInt63.lsl lo 3%uint63 in
  let m := PrimInt63.sub (PrimInt63.lsl 1%uint63 nbits) 1%uint63 in
  let piece := W64 false (PrimInt63.land (wl v) m) in
  let hole := wnot (wsll_k (W64 false m) lobits) in
  wor (wand a hole) (wsll_k piece lobits).

Definition ins_Z (lo n : Z) (a v : Z) : Z :=
  let m := 2 ^ (8 * n) - 1 in
  Z.lor (Z.land a (Z.lnot (Z.shiftl m (8 * lo)))) (Z.shiftl (Z.land v m) (8 * lo)).

End W64.
