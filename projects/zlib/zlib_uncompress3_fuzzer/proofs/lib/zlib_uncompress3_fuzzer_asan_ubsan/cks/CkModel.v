(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.cks Require Import CkTables.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition M32  : Z := 4294967295.
Definition POLY : Z := 3988292384.
Definition X0   : Z := 2147483648.
Definition BASE : Z := 65521.
Definition NMAX : Z := 5552.

Definition Zlen {A} (l : list A) : Z := Z.of_nat (length l).


Definition bstep (b : Z) : Z :=
  if Z.odd b then Z.lxor (Z.shiftr b 1) POLY else Z.shiftr b 1.

Fixpoint mm_loop (i : nat) (a b p : Z) : Z :=
  let hit := Z.testbit a (Z.of_nat i) in
  let p' := if hit then Z.lxor p b else p in
  if hit && (a mod 2 ^ (Z.of_nat i) =? 0) then p'
  else match i with
       | O => p'
       | S i' => mm_loop i' a (bstep b) p'
       end.

Definition multmodp (a b : Z) : Z := mm_loop 31 a b 0.


Fixpoint x2n_loop (fuel : nat) (n k p : Z) : Z :=
  match fuel with
  | O => p
  | S f =>
      if n =? 0 then p
      else x2n_loop f (Z.shiftr n 1) (k + 1)
             (if Z.odd n then multmodp (x2n (k mod 32)) p else p)
  end.

Definition x2nmodp (n k : Z) : Z := x2n_loop 64 n k X0.

Lemma x2n_loop_done : forall f k p, x2n_loop f 0 k p = p.
Proof. intros [|f] k p; reflexivity. Qed.

Lemma x2n_loop_step : forall f n k p, n <> 0 ->
  x2n_loop (S f) n k p
  = x2n_loop f (Z.shiftr n 1) (k + 1) (if Z.odd n then multmodp (x2n (k mod 32)) p else p).
Proof. intros f n k p Hn. cbn [x2n_loop]. destruct (Z.eqb_spec n 0); [lia|reflexivity]. Qed.


Definition crc32_combine64 (crc1 crc2 len2 : Z) : Z :=
  Z.lxor (multmodp (x2nmodp len2 3) crc1) (Z.land crc2 M32).
Definition crc32_combine (crc1 crc2 len2 : Z) : Z := crc32_combine64 crc1 crc2 len2.
Definition crc32_combine_gen64 (len2 : Z) : Z := x2nmodp len2 3.
Definition crc32_combine_gen (len2 : Z) : Z := crc32_combine_gen64 len2.
Definition crc32_combine_op (crc1 crc2 op : Z) : Z :=
  Z.lxor (multmodp op crc1) (Z.land crc2 M32).


Definition crc_byte (c b : Z) : Z :=
  Z.lxor (Z.shiftr c 8) (ctab (Z.land (Z.lxor b c) 255)).

Definition crc_bytes (c : Z) (bs : list Z) : Z := fold_left crc_byte bs c.

Lemma crc_bytes_nil : forall c, crc_bytes c [] = c.
Proof. reflexivity. Qed.
Lemma crc_bytes_cons : forall c b bs, crc_bytes c (b :: bs) = crc_bytes (crc_byte c b) bs.
Proof. reflexivity. Qed.
Lemma crc_bytes_app : forall c bs1 bs2, crc_bytes c (bs1 ++ bs2) = crc_bytes (crc_bytes c bs1) bs2.
Proof. intros. unfold crc_bytes. apply fold_left_app. Qed.

Definition crc_word1 (x : Z) : Z := Z.lxor (Z.shiftr x 8) (ctab (Z.land x 255)).
Definition crc_word (x : Z) : Z := crc_word1 (crc_word1 (crc_word1 (crc_word1 x))).

Definition wle (b0 b1 b2 b3 : Z) : Z := b0 + 2 ^ 8 * b1 + 2 ^ 16 * b2 + 2 ^ 24 * b3.

Fixpoint words_le (bs : list Z) : list Z :=
  match bs with
  | b0 :: b1 :: b2 :: b3 :: rest => wle b0 b1 b2 b3 :: words_le rest
  | _ => []
  end.

Definition braid1 (c w : Z) : Z :=
  let x := Z.lxor c w in
  Z.lxor (Z.lxor (Z.lxor (btab 0 (Z.land x 255))
                         (btab 1 (Z.land (Z.shiftr x 8) 255)))
                 (btab 2 (Z.land (Z.shiftr x 16) 255)))
         (btab 3 (Z.land (Z.shiftr x 24) 255)).

Definition braid_step (cs : list Z) (blk : list Z) : list Z :=
  map (fun cw => braid1 (fst cw) (snd cw)) (combine cs (words_le blk)).

Definition block (i : nat) (bs : list Z) : list Z := firstn 20 (skipn (20 * i) bs).

Fixpoint blocks_of (n : nat) (bs : list Z) : list (list Z) :=
  match n with
  | O => []
  | S n' => firstn 20 bs :: blocks_of n' (skipn 20 bs)
  end.

Fixpoint braid_run (cs : list Z) (blocks : list (list Z)) : list Z :=
  match blocks with
  | [] => cs
  | blk :: rest => braid_run (braid_step cs blk) rest
  end.

Definition braid_state (cs : list Z) (i : nat) (bs : list Z) : list Z :=
  braid_run cs (blocks_of i bs).

Definition braid_last (cs : list Z) (blk : list Z) : Z :=
  match cs, words_le blk with
  | [c0; c1; c2; c3; c4], [w0; w1; w2; w3; w4] =>
      let r := crc_word (Z.lxor c0 w0) in
      let r := crc_word (Z.lxor (Z.lxor c1 w1) r) in
      let r := crc_word (Z.lxor (Z.lxor c2 w2) r) in
      let r := crc_word (Z.lxor (Z.lxor c3 w3) r) in
      crc_word (Z.lxor (Z.lxor c4 w4) r)
  | _, _ => 0
  end.

Definition align4 (adr : Z) : Z := (4 - adr mod 4) mod 4.

Definition crc_braid_phase (adr c : Z) (bs : list Z) : Z * list Z :=
  let na := align4 adr in
  let c1 := crc_bytes c (firstn (Z.to_nat na) bs) in
  let bs1 := skipn (Z.to_nat na) bs in
  let blks := Zlen bs1 / 20 in
  let cs := braid_state [c1; 0; 0; 0; 0] (Z.to_nat (blks - 1)) bs1 in
  let c2 := braid_last cs (block (Z.to_nat (blks - 1)) bs1) in
  (c2, skipn (Z.to_nat (20 * blks)) bs1).

Definition crc_pre (c : Z) : Z := Z.land (Z.lnot c) M32.

Definition crc32_z_model (adr c : Z) (bs : list Z) : Z :=
  let c0 := crc_pre c in
  let cr := if Zlen bs <? 23 then (c0, bs) else crc_braid_phase adr c0 bs in
  Z.lxor (crc_bytes (fst cr) (snd cr)) M32.

Definition crc32_model := crc32_z_model.


Definition lo16 (a : Z) : Z := Z.land a 65535.
Definition hi16 (a : Z) : Z := Z.land (Z.shiftr a 16) 65535.

Definition csub (x : Z) : Z := if BASE <=? x then x - BASE else x.

Fixpoint adler_fold (ab : Z * Z) (bs : list Z) : Z * Z :=
  match bs with
  | [] => ab
  | x :: r => let a := fst ab + x in adler_fold (a, snd ab + a) r
  end.

Lemma adler_fold_nil : forall ab, adler_fold ab [] = ab.
Proof. reflexivity. Qed.
Lemma adler_fold_cons : forall a b x r,
  adler_fold (a, b) (x :: r) = adler_fold (a + x, b + (a + x)) r.
Proof. reflexivity. Qed.
Lemma adler_fold_app : forall ab bs1 bs2,
  adler_fold ab (bs1 ++ bs2) = adler_fold (adler_fold ab bs1) bs2.
Proof.
  intros ab bs1; revert ab; induction bs1 as [|x r IH]; intros ab bs2; [reflexivity|].
  cbn [adler_fold app]. apply IH.
Qed.

Definition adler_comb (a b : Z) : Z := Z.lor a (Z.shiftl b 16).

Fixpoint adler_blocks (n : nat) (ab : Z * Z) (bs : list Z) : Z * Z :=
  match n with
  | O => ab
  | S n' =>
      let ab1 := adler_fold ab (firstn (Z.to_nat NMAX) bs) in
      adler_blocks n' (fst ab1 mod BASE, snd ab1 mod BASE) (skipn (Z.to_nat NMAX) bs)
  end.

Definition adler32_z_model (adler : Z) (bs : list Z) : Z :=
  let a := lo16 adler in
  let b := hi16 adler in
  let len := Zlen bs in
  if len =? 1 then
    let a1 := csub (a + hd 0 bs) in
    let b1 := csub (b + a1) in
    adler_comb a1 b1
  else if len <? 16 then
    let ab := adler_fold (a, b) bs in
    adler_comb (csub (fst ab)) (snd ab mod BASE)
  else
    let nblk := len / NMAX in
    let ab1 := adler_blocks (Z.to_nat nblk) (a, b) bs in
    let rest := skipn (Z.to_nat (NMAX * nblk)) bs in
    match rest with
    | [] => adler_comb (fst ab1) (snd ab1)
    | _ => let ab2 := adler_fold ab1 rest in
           adler_comb (fst ab2 mod BASE) (snd ab2 mod BASE)
    end.

Definition adler32_model := adler32_z_model.


Definition adler32_combine_model (adler1 adler2 len2 : Z) : Z :=
  if len2 <? 0 then M32
  else
    let rem := len2 mod BASE in
    let sum1 := Z.land adler1 65535 in
    let sum2 := (rem * sum1) mod BASE in
    let sum1 := sum1 + (Z.land adler2 65535 + BASE - 1) in
    let sum2 := sum2 + (Z.land (Z.shiftr adler1 16) 65535
                        + Z.land (Z.shiftr adler2 16) 65535 + BASE - rem) in
    let sum1 := csub sum1 in
    let sum1 := csub sum1 in
    let sum2 := if 2 * BASE <=? sum2 then sum2 - 2 * BASE else sum2 in
    let sum2 := csub sum2 in
    adler_comb sum1 sum2.
