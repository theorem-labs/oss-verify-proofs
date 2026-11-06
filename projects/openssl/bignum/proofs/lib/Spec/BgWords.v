(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Fixpoint sqr_words (a : list Z) : list Z :=
  match a with
  | [] => []
  | x :: a' => (x * x) mod BW :: (x * x) / BW :: sqr_words a'
  end.

Definition sqr_comba4 (a : list Z) : list Z := to_limbs 8 (lval a * lval a).
Definition sqr_comba8 (a : list Z) : list Z := to_limbs 16 (lval a * lval a).

Fixpoint sqr_normal_loop (a : list Z) (cnt k : nat) (r : list Z) : list Z :=
  match cnt with
  | O => r
  | S c =>
      let j := (length a - 1 - k)%nat in
      let '(seg, cy) := mul_add_words (slice r (1 + 2 * k) j) (slice a (1 + k) j) (nth k a 0) in
      sqr_normal_loop a c (S k) (splice r (1 + 2 * k) (seg ++ [cy]))
  end.

Definition sqr_normal (a r : list Z) : list Z * list Z :=
  let n := length a in
  let r := upd (upd r 0 0) (2 * n - 1) 0 in
  let r := if (1 <? n)%nat
           then let '(seg, cy) := mul_words (slice a 1 (n - 1)) (nth 0 a 0) in splice r 1 (seg ++ [cy])
           else r in
  let r := sqr_normal_loop a (n - 2) 1 r in
  let r := fst (add_words r r) in
  let tmp := sqr_words a in
  (fst (add_words r tmp), tmp).

Fixpoint sqr_recursive (k : nat) (a r t : list Z) {struct k} : list Z * list Z :=
  let n2 := Nat.pow 2 k in
  if (n2 =? 4)%nat then (splice r 0 (sqr_comba4 (firstn 4 a)), t)
  else if (n2 =? 8)%nat then (splice r 0 (sqr_comba8 (firstn 8 a)), t)
  else if (n2 <? 16)%nat then
    let '(ro, tmp) := sqr_normal (firstn n2 a) (firstn (2 * n2) r) in (splice r 0 ro, splice t 0 tmp)
  else
    match k with
    | O => (r, t)
    | S k' =>
        let n := Nat.pow 2 k' in
        let a_lo := firstn n a in
        let a_hi := slice a n n in
        let c1 := cmp_words a_lo a_hi in
        let t := if 0 <? c1 then splice t 0 (fst (sub_words a_lo a_hi))
                 else if c1 <? 0 then splice t 0 (fst (sub_words a_hi a_lo))
                 else t in
        let p := skipn (2 * n2) t in
        let '(tm, p) := if c1 =? 0 then (repeat 0 n2, p)
                        else sqr_recursive k' (slice t 0 n) (slice t n2 n2) p in
        let '(rl, p) := sqr_recursive k' a_lo (slice r 0 n2) p in
        let '(rh, p) := sqr_recursive k' a_hi (slice r n2 n2) p in
        kara_combine n true (rl ++ rh) (firstn n2 t ++ tm ++ p)
    end.

Fixpoint mont_reduce_loop (np : list Z) (n0 : Z) (nl : nat) (cnt i : nat) (rp : list Z) (carry : Z) : list Z * Z :=
  match cnt with
  | O => (rp, carry)
  | S c =>
      let w := mulw (nth i rp 0) n0 in
      let '(seg, v) := mul_add_words (slice rp i nl) np w in
      let rp := splice rp i seg in
      let old := nth (i + nl) rp 0 in
      let v := addw (addw v carry) old in
      let carry := if v <? old then 1 else if v =? old then carry else 0 in
      mont_reduce_loop np n0 nl c (S i) (upd rp (i + nl) v) carry
  end.

Fixpoint select_words (mask : Z) (a r : list Z) : list Z :=
  match a, r with
  | x :: a', y :: r' => Z.lor (Z.land mask x) (Z.land (BW - 1 - mask) y) :: select_words mask a' r'
  | _, _ => []
  end.

Definition mont_final (ap np : list Z) (carry : Z) : list Z :=
  let '(res, borrow) := sub_words ap np in
  select_words (subw carry borrow) ap res.

Definition window_bits (b : Z) : Z :=
  if 671 <? b then 6 else if 239 <? b then 5 else if 79 <? b then 4 else if 23 <? b then 3 else 1.

Fixpoint window_scan (bit : Z -> bool) (wstart : Z) (cnt : nat) (i : Z) (wvalue wend : Z) : Z * Z :=
  match cnt with
  | O => (wvalue, wend)
  | S c =>
      if wstart - i <? 0 then (wvalue, wend)
      else if bit (wstart - i) then window_scan bit wstart c (i + 1) (Z.lor (Z.shiftl wvalue (i - wend)) 1) i
      else window_scan bit wstart c (i + 1) wvalue wend
  end.

Module BgWordsTests.
Example ex_sqrn : let '(r, t) := sqr_normal [BW - 1; BW - 2; 7] (repeat 5 6) in
                  lval r = lval [BW - 1; BW - 2; 7] * lval [BW - 1; BW - 2; 7] /\ length r = 6%nat.
Proof. vm_compute. split; reflexivity. Qed.
Example ex_sqr1 : fst (sqr_normal [BW - 1] [3; 4]) = [1; BW - 2]. Proof. vm_compute. reflexivity. Qed.
Example ex_win : window_scan (fun n => Z.testbit 53 n) 5 3 1 1 0 = (13, 3). Proof. vm_compute. reflexivity. Qed.
End BgWordsTests.
