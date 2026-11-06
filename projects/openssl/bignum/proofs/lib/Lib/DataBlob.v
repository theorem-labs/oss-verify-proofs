(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List PrimString Uint63 Bool.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module DB.
Inductive T : Type := N (z : Z) | L (l : list T).

Definition st : Type := (list (list T) * option Z * bool)%type.

Definition flush (s : st) : st :=
  let '(fr, acc, neg) := s in
  match acc, fr with
  | Some z, f :: fr' => ((N (if neg then Z.opp z else z) :: f) :: fr', None, false)
  | _, _ => (fr, None, false)
  end.

Definition close (s : st) : st :=
  let '(fr, _, _) := flush s in
  match fr with
  | f :: g :: fr' => ((L (rev' f) :: g) :: fr', None, false)
  | _ => (fr, None, false)
  end.

Definition step (s : st) (c : int) : st :=
  let '(fr, acc, neg) := s in
  if (48 <=? c)%uint63 && (c <=? 57)%uint63 then (fr, Some (16 * (match acc with Some z => z | None => 0 end) + Uint63.to_Z (c - 48)%uint63)%Z, neg)
  else if (97 <=? c)%uint63 && (c <=? 102)%uint63 then (fr, Some (16 * (match acc with Some z => z | None => 0 end) + Uint63.to_Z (c - 87)%uint63)%Z, neg)
  else if (c =? 45)%uint63 then (fr, acc, true)
  else if (c =? 91)%uint63 || (c =? 40)%uint63 then ([] :: fr, None, false)
  else if (c =? 93)%uint63 || (c =? 41)%uint63 then close s
  else if (c =? 59)%uint63 || (c =? 44)%uint63 then flush s
  else s.

Fixpoint run (fuel : nat) (s : string) (i : int) (x : st) : st :=
  match fuel with
  | O => x
  | S k => if (i <? PrimString.length s)%uint63 then run k s (i + 1)%uint63 (step x (PrimString.get s i)) else x
  end.

Definition parse (s : string) : T :=
  let '(fr, _, _) := flush (run (Z.to_nat (Uint63.to_Z (PrimString.length s))) s 0%uint63 ([[]], None, false)) in
  match fr with
  | [ v :: _ ] => v
  | _ => L []
  end.

Definition z (t : T) : Z := match t with N v => v | L _ => 0%Z end.
Definition l {A} (f : T -> A) (t : T) : list A := match t with L xs => map f xs | N _ => [] end.
Definition p2 {A B} (f : T -> A) (g : T -> B) (a0 : A) (b0 : B) (t : T) : A * B :=
  match t with L [x; y] => (f x, g y) | _ => (a0, b0) end.
Definition p3 {A B C} (f : T -> A) (g : T -> B) (h : T -> C) (a0 : A) (b0 : B) (c0 : C) (t : T) : A * B * C :=
  match t with L [x; y; w] => (f x, g y, h w) | _ => (a0, b0, c0) end.

Definition lz (s : string) : list Z := l z (parse s).
Definition llz (s : string) : list (list Z) := l (l z) (parse s).
Definition lzzz (s : string) : list (Z * Z * Z) := l (p3 z z z 0%Z 0%Z 0%Z) (parse s).
Definition lzllz (s : string) : list (Z * list (list Z)) := l (p2 z (l (l z)) 0%Z []) (parse s).
End DB.

Goal DB.lzzz "[(490a0,e,20);(-1,2,3)]" = [(0x490a0, 14, 32); (-1, 2, 3)]%Z. Proof. vm_compute. reflexivity. Qed.
Goal DB.lzllz "[(a,[[1;2];[]]);(b,[])]" = [(10, [[1; 2]; []]); (11, [])]%Z. Proof. vm_compute. reflexivity. Qed.
Goal DB.llz "[[1];[];[ff;0]]" = [[1]; []; [255; 0]]%Z. Proof. vm_compute. reflexivity. Qed.
Goal DB.lz "[]" = []. Proof. vm_compute. reflexivity. Qed.
