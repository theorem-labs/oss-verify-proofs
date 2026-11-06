(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint add_words_c (a b : list Z) (c : Z) : list Z * Z :=
  match a, b with
  | x :: a', y :: b' =>
      let s := x + y + c in
      let '(r, c') := add_words_c a' b' (s / BW) in (s mod BW :: r, c')
  | _, _ => ([], c)
  end.
Definition add_words (a b : list Z) : list Z * Z := add_words_c a b 0.

(* [comment removed for export] *)
Fixpoint sub_words_c (a b : list Z) (c : Z) : list Z * Z :=
  match a, b with
  | x :: a', y :: b' =>
      let d := x - y - c in
      let '(r, c') := sub_words_c a' b' (if d <? 0 then 1 else 0) in (d mod BW :: r, c')
  | _, _ => ([], c)
  end.
Definition sub_words (a b : list Z) : list Z * Z := sub_words_c a b 0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint mul_words_c (a : list Z) (w c : Z) : list Z * Z :=
  match a with
  | x :: a' =>
      let s := x * w + c in
      let '(r, c') := mul_words_c a' w (s / BW) in (s mod BW :: r, c')
  | [] => ([], c)
  end.
Definition mul_words (a : list Z) (w : Z) : list Z * Z := mul_words_c a w 0.

(* [comment removed for export] *)
Fixpoint mul_add_words_c (r a : list Z) (w c : Z) : list Z * Z :=
  match r, a with
  | y :: r', x :: a' =>
      let s := x * w + y + c in
      let '(o, c') := mul_add_words_c r' a' w (s / BW) in (s mod BW :: o, c')
  | _, _ => ([], c)
  end.
Definition mul_add_words (r a : list Z) (w : Z) : list Z * Z := mul_add_words_c r a w 0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition num_bits_word (l : Z) : Z := if l =? 0 then 0 else Z.log2 l + 1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint dw_corr (fuel : nat) (h l dh dl q th tl : Z) : Z * Z * Z :=
  match fuel with
  | O => (q, th, tl)
  | S f =>
      let t := subw h th in
      if negb (t / HW =? 0) || (tl <=? (t * HW) mod BW + l / HW)
      then (q, th, tl)
      else dw_corr f h l dh dl (subw q 1) (subw th dh) (subw tl dl)
  end.

Definition DW_FUEL : nat := 4.

(* [comment removed for export] *)
Definition dw_round (h l d dh dl : Z) : Z * Z * Z :=
  let q0 := if h / HW =? dh then HW - 1 else h / dh in
  let '(q, th, tl) := dw_corr DW_FUEL h l dh dl q0 (mulw q0 dh) (mulw dl q0) in
  let t := tl / HW in
  let tl := (tl * HW) mod BW in
  let th := addw th t in
  let th := if l <? tl then addw th 1 else th in
  let l := subw l tl in
  let '(h, q) := if h <? th then (addw h d, subw q 1) else (h, q) in
  let h := subw h th in
  (q, h, l).

(* [comment removed for export] *)
Definition div_words (h l d : Z) : Z :=
  if d =? 0 then BW - 1 else
  let i := 64 - num_bits_word d in
  let h := if d <=? h then subw h d else h in
  let '(d, h, l) := if i =? 0 then (d, h, l)
                    else (shlw d i, Z.lor (shlw h i) (shrw l (64 - i)), shlw l i) in
  let dh := d / HW in                       (* [comment removed for export] *)
  let dl := d mod HW in                     (* [comment removed for export] *)
  let '(q1, h1, l1) := dw_round h l d dh dl in
  let ret := (q1 * HW) mod BW in            (* [comment removed for export] *)
  let h2 := (h1 * HW) mod BW + l1 / HW in   (* [comment removed for export] *)
  let l2 := ((l1 mod HW) * HW) mod BW in    (* [comment removed for export] *)
  let '(q2, _, _) := dw_round h2 l2 d dh dl in
  Z.lor ret q2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mul_comba8 (a b : list Z) : list Z := to_limbs 16 (lval a * lval b).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint mul_normal_loop (a bs : list Z) (r : list Z) (i : nat) : list Z :=
  match bs with
  | [] => r
  | w :: bs' =>
      let '(seg, c) := mul_add_words (skipn i r) a w in
      mul_normal_loop a bs' (firstn i r ++ seg ++ [c]) (S i)
  end.

(* [comment removed for export] *)
Definition mul_normal (a b : list Z) : list Z :=
  let '(a, b) := if (length a <? length b)%nat then (b, a) else (a, b) in
  match b with
  | [] => fst (mul_words a 0)
  | w :: b' => let '(seg, c) := mul_words a w in mul_normal_loop a b' (seg ++ [c]) 1
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint cmp_words (a b : list Z) : Z :=
  match a, b with
  | x :: a', y :: b' =>
      let c := cmp_words a' b' in
      if c =? 0 then (if x =? y then 0 else if y <? x then 1 else -1) else c
  | _, _ => 0
  end.

Definition nonzero (x : Z) : bool := negb (x =? 0).

(* [comment removed for export] *)
Definition cmp_part_words (a b : list Z) (cl : nat) : Z :=
  if existsb nonzero (skipn cl b) then -1
  else if existsb nonzero (skipn cl a) then 1
  else cmp_words (firstn cl a) (firstn cl b).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint sub_part_neg (b : list Z) (c : Z) : list Z * Z :=
  match b with
  | [] => ([], c)
  | t :: b' => let '(r, c') := sub_part_neg b' (if t =? 0 then c else 1) in ((0 - t - c) mod BW :: r, c')
  end.

(* [comment removed for export] *)
Fixpoint sub_part_pos (a : list Z) (c : Z) : list Z * Z :=
  match a with
  | [] => ([], c)
  | t :: a' => let '(r, c') := sub_part_pos a' (if t =? 0 then c else 0) in ((t - c) mod BW :: r, c')
  end.

(* [comment removed for export] *)
Definition sub_part_words (a b : list Z) (cl : nat) : list Z * Z :=
  let '(r, c) := sub_words (firstn cl a) (firstn cl b) in
  match skipn cl b with
  | _ :: _ => let '(r2, c2) := sub_part_neg (skipn cl b) c in (r ++ r2, c2)
  | [] => let '(r2, c2) := sub_part_pos (skipn cl a) c in (r ++ r2, c2)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint lshift_limbs (l : list Z) (lb : Z) (m : Z) : list Z * Z :=
  match l with
  | [] => ([], m)
  | n :: l' =>
      let '(r, mo) := lshift_limbs l' lb (if lb =? 0 then 0 else shrw n (64 - lb)) in
      (Z.lor (shlw n lb) m :: r, mo)
  end.

(* [comment removed for export] *)
Fixpoint rshift_limbs (l : list Z) (rb : Z) : list Z :=
  match l with
  | [] => []
  | n :: l' =>
      let hi := match l' with [] => 0 | m :: _ => if rb =? 0 then 0 else shlw m (64 - rb) end in
      Z.lor (shrw n rb) hi :: rshift_limbs l' rb
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint strip_top (d : list Z) (top : nat) : nat :=
  match top with
  | O => O
  | S t => if nth t d 0 =? 0 then strip_top d t else top
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint skip_zero_bytes (s : list Z) : list Z :=
  match s with
  | 0 :: s' => skip_zero_bytes s'
  | _ => s
  end.

(* [comment removed for export] *)
Fixpoint le_bytes_val (bs : list Z) : Z :=
  match bs with
  | [] => 0
  | b :: bs' => b mod 256 + 256 * le_bytes_val bs'
  end.

(* [comment removed for export] *)
Fixpoint bytes_to_limbs (n : nat) (bs : list Z) : list Z :=
  match n with
  | O => []
  | S n' => le_bytes_val (firstn 8 bs) :: bytes_to_limbs n' (skipn 8 bs)
  end.

(* [comment removed for export] *)
Definition bin2bn_limbs (s : list Z) : list Z :=
  bytes_to_limbs ((length s - 1) / 8 + 1) (rev s).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Module BnWordsTests.
Example ex_add : add_words [BW - 1; BW - 1] [1; 0] = ([0; 0], 1). Proof. vm_compute. reflexivity. Qed.
Example ex_sub : sub_words [0; 0] [1; 0] = ([BW - 1; BW - 1], 1). Proof. vm_compute. reflexivity. Qed.
Example ex_mul : mul_words [BW - 1; BW - 1] (BW - 1) = ([1; BW - 1], BW - 2). Proof. vm_compute. reflexivity. Qed.
Example ex_div1 : div_words 1 0 (2 ^ 63) = 2. Proof. vm_compute. reflexivity. Qed.
Example ex_div2 : div_words (2 ^ 63 + 5) 12345 (BW - 1) = ((2 ^ 63 + 5) * BW + 12345) / (BW - 1). Proof. vm_compute. reflexivity. Qed.
Example ex_div3 : div_words 3 7 5 = (3 * BW + 7) / 5. Proof. vm_compute. reflexivity. Qed.
Example ex_norm : lval (mul_normal [BW - 1; BW - 2; 7] [BW - 1; 3]) = lval [BW - 1; BW - 2; 7] * lval [BW - 1; 3].
Proof. vm_compute. reflexivity. Qed.
Example ex_cmp : cmp_words [5; 1] [6; 1] = -1. Proof. vm_compute. reflexivity. Qed.
Example ex_b2b : bin2bn_limbs [1; 2; 3; 4; 5; 6; 7; 8; 9] = [0x0203040506070809; 1]. Proof. vm_compute. reflexivity. Qed.
Example ex_lsh : lshift_limbs [2 ^ 63 + 1; 1] 1 0 = ([2; 3], 0). Proof. vm_compute. reflexivity. Qed.
Example ex_rsh : rshift_limbs [2; 3] 1 = [2 ^ 63 + 1; 1]. Proof. vm_compute. reflexivity. Qed.
End BnWordsTests.
