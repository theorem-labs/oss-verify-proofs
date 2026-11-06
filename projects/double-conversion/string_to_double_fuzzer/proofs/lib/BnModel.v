(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition zget (l : list Z) (i : Z) : Z := nth (Z.to_nat i) l 0.
Definition zlen {A} (l : list A) : Z := Z.of_nat (length l).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition B : Z := 268435456.               (* [comment removed for export] *)
Definition MASK : Z := 268435455.            (* [comment removed for export] *)
Definition CAP : Z := 128.                   (* [comment removed for export] *)
Definition kFive27_lo : Z := 0xfa10079d.     (* [comment removed for export] *)
Definition kFive27_hi : Z := 0x6765c793.     (* [comment removed for export] *)
Definition kFive13 : Z := 1220703125.        (* [comment removed for export] *)
Definition kFive (k : Z) : Z := 5 ^ k.       (* [comment removed for export] *)

Lemma B_eq : B = 2 ^ 28. Proof. reflexivity. Qed.
Lemma MASK_eq : MASK = 2 ^ 28 - 1. Proof. reflexivity. Qed.
Lemma kFive13_eq : kFive13 = 5 ^ 13. Proof. reflexivity. Qed.
Lemma kFive27_eq : kFive27_hi * 2 ^ 32 + kFive27_lo = 5 ^ 27. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record bn : Type := BN { cells : list Z; ex : Z }.

Definition used (b : bn) : Z := zlen (cells b).
Definition bn_zero : bn := BN [] 0.

(* [comment removed for export] *)
Fixpoint chunks (fuel : nat) (v : Z) : list Z :=
  match fuel with
  | O => []
  | S f => if v =? 0 then [] else (v mod B) :: chunks f (v / B)
  end.

Definition assign_u64 (v : Z) : bn := BN (chunks 3 v) 0.

(* [comment removed for export] *)
Fixpoint mul32_l (F c : Z) (l : list Z) : list Z * Z :=
  match l with
  | [] => ([], c)
  | x :: t => let p := F * x + c in
              let (r, c') := mul32_l F (p / B) t in ((p mod B) :: r, c')
  end.

Definition mul32 (F : Z) (b : bn) : bn :=
  if F =? 1 then b
  else if F =? 0 then bn_zero
  else match cells b with
       | [] => b
       | _ => let (r, c) := mul32_l F 0 (cells b) in BN (r ++ chunks 3 c) (ex b)
       end.

(* [comment removed for export] *)
Fixpoint mul64_l (lo hi c : Z) (l : list Z) : list Z * Z :=
  match l with
  | [] => ([], c)
  | x :: t => let tmp := c mod B + lo * x in
              let (r, c') := mul64_l lo hi (c / B + tmp / B + hi * x * 16) t in
              ((tmp mod B) :: r, c')
  end.

Definition mul64 (lo hi : Z) (b : bn) : bn :=
  match cells b with
  | [] => b
  | _ => let (r, c) := mul64_l lo hi 0 (cells b) in BN (r ++ chunks 3 c) (ex b)
  end.

(* [comment removed for export] *)
Fixpoint shl_l (s c : Z) (l : list Z) : list Z * Z :=
  match l with
  | [] => ([], c)
  | x :: t => let (r, c') := shl_l s (x / 2 ^ (28 - s)) t in
              (((x * 2 ^ s + c) mod B) :: r, c')
  end.

(* [comment removed for export] *)
Definition shl (n : Z) (b : bn) : bn :=
  match cells b with
  | [] => b
  | _ => let (r, c) := shl_l (n mod 28) 0 (cells b) in
         BN (if c =? 0 then r else r ++ [c]) (ex b + n / 28)
  end.

(* [comment removed for export] *)
Fixpoint pow27_loop (fuel : nat) (r : Z) (b : bn) : bn * Z :=
  match fuel with
  | O => (b, r)
  | S f => if r <? 27 then (b, r)
           else pow27_loop f (r - 27) (mul64 kFive27_lo kFive27_hi b)
  end.

Fixpoint pow13_loop (fuel : nat) (r : Z) (b : bn) : bn * Z :=
  match fuel with
  | O => (b, r)
  | S f => if r <? 13 then (b, r) else pow13_loop f (r - 13) (mul32 kFive13 b)
  end.

Definition mulpow10 (e : Z) (b : bn) : bn :=
  if e =? 0 then b
  else match cells b with
       | [] => b
       | _ => let (b1, r1) := pow27_loop (Z.to_nat (e / 27)) e b in
              let (b2, r2) := pow13_loop 2 r1 b1 in
              let b3 := if 0 <? r2 then mul32 (kFive r2) b2 else b2 in
              shl e b3
       end.

(* [comment removed for export] *)
Fixpoint addc_l (c : Z) (l : list Z) : list Z :=
  if c =? 0 then l
  else match l with
       | [] => [c]
       | x :: t => ((x + c) mod B) :: addc_l ((x + c) / B) t
       end.

Fixpoint add_l (c : Z) (l o : list Z) : list Z :=
  match o with
  | [] => addc_l c l
  | y :: o' => match l with
               | [] => ((y + c) mod B) :: add_l ((y + c) / B) [] o'
               | x :: t => ((x + y + c) mod B) :: add_l ((x + y + c) / B) t o'
               end
  end.

Definition add_bn (b : bn) (o : list Z) : bn := BN (add_l 0 (cells b) o) (ex b).

(* [comment removed for export] *)
Definition add_u64 (d : Z) (b : bn) : bn :=
  if d =? 0 then b else add_bn b (chunks 3 d).

(* [comment removed for export] *)
Fixpoint read_digits (ds : list Z) (r : Z) : Z :=
  match ds with
  | [] => r
  | d :: t => read_digits t (r * 10 + (d - 48))
  end.

(* [comment removed for export] *)
Fixpoint clamp_l (fuel : nat) (l : list Z) : list Z :=
  match fuel with
  | O => l
  | S f => if (0 <? zlen l) && (zget l (zlen l - 1) =? 0) then clamp_l f (removelast l) else l
  end.

Definition clamp (b : bn) : bn :=
  let l := clamp_l (length (cells b)) (cells b) in
  BN l (match l with [] => 0 | _ => ex b end).

(* [comment removed for export] *)
Definition ads_step (ds : list Z) (b : bn) : bn :=
  add_u64 (read_digits ds 0) (mulpow10 (zlen ds) b).

Fixpoint ads_loop (fuel : nat) (ds : list Z) (b : bn) : bn * list Z :=
  match fuel with
  | O => (b, ds)
  | S f => if zlen ds <? 19 then (b, ds)
           else ads_loop f (skipn 19 ds) (ads_step (firstn 19 ds) b)
  end.

Definition assign_decimal (ds : list Z) : bn :=
  let (b1, rest) := ads_loop (Nat.div (length ds) 19) ds bn_zero in
  clamp (ads_step rest b1).

(* [comment removed for export] *)
Definition bigit_or_zero (b : bn) (i : Z) : Z :=
  if used b + ex b <=? i then 0
  else if i <? ex b then 0
  else zget (cells b) (i - ex b).

Fixpoint cmp_loop (fuel : nat) (a b : bn) (i : Z) : Z :=
  match fuel with
  | O => 0
  | S f => if i <? Z.min (ex a) (ex b) then 0
           else let x := bigit_or_zero a i in
                let y := bigit_or_zero b i in
                if x <? y then -1 else if y <? x then 1 else cmp_loop f a b (i - 1)
  end.

Definition compare (a b : bn) : Z :=
  let la := used a + ex a in
  let lb := used b + ex b in
  if la <? lb then -1
  else if lb <? la then 1
  else cmp_loop (Z.to_nat (la - Z.min (ex a) (ex b))) a b (la - 1).

(* [comment removed for export] *)
Definition cbd (ds : list Z) (expo f e : Z) : Z :=
  let a0 := assign_decimal ds in
  let b0 := assign_u64 f in
  let a1 := if 0 <=? expo then mulpow10 expo a0 else a0 in
  let b1 := if 0 <=? expo then b0 else mulpow10 (- expo) b0 in
  let b2 := if 0 <? e then shl e b1 else b1 in
  let a2 := if 0 <? e then a1 else shl (- e) a1 in
  compare a2 b2.
