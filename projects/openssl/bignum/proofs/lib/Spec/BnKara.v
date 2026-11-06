(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Fixpoint carry_up (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: l' => let ln := addw x 1 in if ln =? 0 then ln :: carry_up l' else ln :: l'
  end.

Definition add_carry (l : list Z) (c1 : Z) : list Z :=
  match l with
  | [] => []
  | x :: l' => let ln := addw x c1 in if ln <? c1 mod BW then ln :: carry_up l' else ln :: l'
  end.

Definition kara_combine (n : nat) (neg : bool) (r t : list Z) : list Z * list Z :=
  let n2 := (2 * n)%nat in
  let '(s1, c1) := add_words (slice r 0 n2) (slice r n2 n2) in
  let t := splice t 0 s1 in
  let '(s2, c2) := if neg
                   then let '(s, bw) := sub_words (slice t 0 n2) (slice t n2 n2) in (s, c1 - bw)
                   else let '(s, cy) := add_words (slice t n2 n2) (slice t 0 n2) in (s, c1 + cy) in
  let t := splice t n2 s2 in
  let '(s3, c3) := add_words (slice r n n2) (slice t n2 n2) in
  let r := splice r n s3 in
  let c := c2 + c3 in
  let r := if c =? 0 then r else firstn (n + n2) r ++ add_carry (skipn (n + n2) r) c in
  (r, t).

Definition rec_diffs (a_lo a_hi b_lo b_hi : list Z) (tna tnb : nat) (c1 c2 : Z) : option (list Z * list Z * bool) :=
  let code := c1 * 3 + c2 in
  if code =? -4 then Some (fst (sub_part_words a_hi a_lo tna), fst (sub_part_words b_lo b_hi tnb), false)
  else if code =? -2 then Some (fst (sub_part_words a_hi a_lo tna), fst (sub_part_words b_hi b_lo tnb), true)
  else if code =? 2 then Some (fst (sub_part_words a_lo a_hi tna), fst (sub_part_words b_lo b_hi tnb), true)
  else if code =? 4 then Some (fst (sub_part_words a_lo a_hi tna), fst (sub_part_words b_hi b_lo tnb), false)
  else None.

Fixpoint mul_recursive (k : nat) (a b : list Z) (da db : nat) (r t : list Z) {struct k} : list Z * list Z :=
  let n2 := Nat.pow 2 k in
  if ((n2 =? 8) && (da =? 0) && (db =? 0))%nat then
    (splice r 0 (mul_comba8 (firstn 8 a) (firstn 8 b)), t)
  else if (n2 <? 16)%nat then

    let r := splice r 0 (mul_normal (firstn (n2 - da) a) (firstn (n2 - db) b)) in
    let r := if (0 <? da + db)%nat then splice r (2 * n2 - da - db) (repeat 0 (da + db)) else r in
    (r, t)
  else
    match k with
    | O => (r, t)
    | S k' =>
        let n := Nat.pow 2 k' in
        let tna := (n - da)%nat in
        let tnb := (n - db)%nat in
        let a_lo := firstn n a in let a_hi := slice a n tna in
        let b_lo := firstn n b in let b_hi := slice b n tnb in
        let c1 := cmp_part_words a_lo a_hi tna in
        let c2 := cmp_part_words b_hi b_lo tnb in
        let dif := rec_diffs a_lo a_hi b_lo b_hi tna tnb c1 c2 in
        let t := match dif with Some (t0, t1, _) => splice (splice t 0 t0) n t1 | None => t end in
        let neg := match dif with Some (_, _, ng) => ng | None => false end in
        let zero := match dif with Some _ => false | None => true end in
        let '(r, t) :=
          if ((n =? 8) && (da =? 0) && (db =? 0))%nat then
            let t := splice t n2 (if zero then repeat 0 16%nat else mul_comba8 (slice t 0 8) (slice t 8 8)) in
            let r := splice r 0 (mul_comba8 a_lo b_lo) in
            let r := splice r n2 (mul_comba8 a_hi b_hi) in
            (r, t)
          else
            let p := skipn (2 * n2) t in
            let '(tm, p) := if zero then (repeat 0 n2, p)
                            else mul_recursive k' (slice t 0 n) (slice t n n) 0 0 (slice t n2 n2) p in
            let '(rl, p) := mul_recursive k' a_lo b_lo 0 0 (slice r 0 n2) p in
            let '(rh, p) := mul_recursive k' a_hi b_hi da db (slice r n2 n2) p in
            (rl ++ rh, firstn n2 t ++ tm ++ p) in
        kara_combine n neg r t
    end.

Definition part_diffs (a_lo a_hi b_lo b_hi : list Z) (tna tnb : nat) (c1 c2 : Z) : list Z * list Z * bool :=
  let code := c1 * 3 + c2 in
  if code =? -4 then (fst (sub_part_words a_hi a_lo tna), fst (sub_part_words b_lo b_hi tnb), false)
  else if (code =? -3) || (code =? -2) then (fst (sub_part_words a_hi a_lo tna), fst (sub_part_words b_hi b_lo tnb), true)
  else if (code =? 3) || (code =? 4) then (fst (sub_part_words a_lo a_hi tna), fst (sub_part_words b_hi b_lo tnb), false)
  else (fst (sub_part_words a_lo a_hi tna), fst (sub_part_words b_lo b_hi tnb), true).

Fixpoint kara_find (ki : nat) (tna tnb : nat) : nat * bool :=
  let i := Nat.pow 2 ki in
  if ((i <? tna) || (i <? tnb))%nat then (ki, true)
  else if ((i =? tna) || (i =? tnb))%nat then (ki, false)
  else match ki with
       | O => (O, true)
       | S ki' => kara_find ki' tna tnb
       end.

Fixpoint mul_part_recursive (fuel : nat) (k : nat) (a b : list Z) (tna tnb : nat) (r t : list Z) {struct fuel}
  : list Z * list Z :=
  let n := Nat.pow 2 k in
  let n2 := (2 * n)%nat in
  if (n <? 8)%nat then (splice r 0 (mul_normal (firstn (n + tna) a) (firstn (n + tnb) b)), t)
  else
    match fuel with
    | O => (r, t)
    | S fuel' =>
        let a_lo := firstn n a in let a_hi := slice a n tna in
        let b_lo := firstn n b in let b_hi := slice b n tnb in
        let c1 := cmp_part_words a_lo a_hi tna in
        let c2 := cmp_part_words b_hi b_lo tnb in
        let '(t0, t1, neg) := part_diffs a_lo a_hi b_lo b_hi tna tnb c1 c2 in
        let t := splice (splice t 0 t0) n t1 in
        let '(r, t) :=
          if (n =? 8)%nat then
            let t := splice t n2 (mul_comba8 (slice t 0 8) (slice t 8 8)) in
            let r := splice r 0 (mul_comba8 a_lo b_lo) in
            let r := splice r n2 (mul_normal a_hi b_hi) in
            let r := splice r (n2 + tna + tnb) (repeat 0 (n2 - tna - tnb)) in
            (r, t)
          else
            let k' := (k - 1)%nat in
            let p := skipn (2 * n2) t in
            let '(tm, p) := mul_recursive k (slice t 0 n) (slice t n n) 0 0 (slice t n2 n2) p in
            let '(rl, p) := mul_recursive k a_lo b_lo 0 0 (slice r 0 n2) p in
            let i := Nat.pow 2 k' in
            let mx := Nat.max tna tnb in
            let rh := slice r n2 n2 in
            let '(rh, p) :=
              if (mx =? i)%nat then
                let '(o, p) := mul_recursive k' a_hi b_hi (i - tna) (i - tnb) (slice rh 0 (2 * i)) p in
                (splice (splice rh 0 o) (2 * i) (repeat 0 (n2 - 2 * i)), p)
              else if (i <? mx)%nat then
                let '(o, p) := mul_part_recursive fuel' k' a_hi b_hi (tna - i) (tnb - i) (slice rh 0 (4 * i)) p in
                (splice (splice rh 0 o) (tna + tnb) (repeat 0 (n2 - tna - tnb)), p)
              else
                let rh := repeat 0 n2 in
                if ((tna <? 16) && (tnb <? 16))%nat then (splice rh 0 (mul_normal a_hi b_hi), p)
                else
                  let '(ki, part) := kara_find (k' - 1) tna tnb in
                  let i := Nat.pow 2 ki in
                  if part then
                    let '(o, p) := mul_part_recursive fuel' ki a_hi b_hi (tna - i) (tnb - i) (slice rh 0 (4 * i)) p in
                    (splice rh 0 o, p)
                  else
                    let '(o, p) := mul_recursive ki a_hi b_hi (i - tna) (i - tnb) (slice rh 0 (2 * i)) p in
                    (splice rh 0 o, p) in
            (rl ++ rh, firstn n2 t ++ tm ++ p) in
        kara_combine n neg r t
    end.

Fixpoint scratch_rec (k : nat) : nat :=
  match k with
  | O => O
  | S k' => if (Nat.pow 2 k <? 16)%nat then O else (2 * Nat.pow 2 k + scratch_rec k')%nat
  end.

