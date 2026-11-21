(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.cks Require Import
  CkTables CkModel CkXt CkMultmodp CkMathCrc CkMathAdler.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).


Definition M20 : Z := 14757395258967641293.




































Lemma adler_blocks_bound16 : forall n a b bs, 0 <= a <= 65535 -> 0 <= b <= 65535 ->
  0 <= fst (adler_blocks n (a, b) bs) <= 65535 /\ 0 <= snd (adler_blocks n (a, b) bs) <= 65535.
Proof.
  induction n as [|n IH]; intros a b bs Ha Hb.
  - cbn. lia.
  - rewrite adler_blocks_S_front. cbv zeta.
    pose proof (mod_BASE_range (fst (adler_fold (a, b) (firstn (Z.to_nat NMAX) bs)))).
    pose proof (mod_BASE_range (snd (adler_fold (a, b) (firstn (Z.to_nat NMAX) bs)))).
    apply IH; unfold BASE in *; lia.
Qed.

Lemma lo16_le : forall x, 0 <= lo16 x <= 65535.
Proof. intros x. pose proof (lo16_range x). lia. Qed.

Lemma hi16_le : forall x, 0 <= hi16 x <= 65535.
Proof. intros x. pose proof (hi16_range x). lia. Qed.


Lemma csub_sltu : forall x, csub x = x - (if 65520 <? x then 65521 else 0).
Proof.
  intros x. unfold csub, BASE.
  destruct (Z.leb_spec 65521 x), (Z.ltb_spec 65520 x); lia.
Qed.

Lemma csub_sltu_shift16 : forall s,
  csub s * 2 ^ 16 = s * 2 ^ 16 - (if 65520 <? s then 65521 * 2 ^ 16 else 0).
Proof. intros s. rewrite csub_sltu. destruct (65520 <? s); lia. Qed.

Lemma adler_comb_machine : forall a b, adler_comb a b = Z.lor (b * 2 ^ 16) a.
Proof. intros a b. unfold adler_comb. rewrite Z.shiftl_mul_pow2 by lia. apply Z.lor_comm. Qed.


Lemma adler_len1_path : forall adler x, 0 <= x < 256 ->
  let a := lo16 adler in
  let b := hi16 adler in
  let a1 := a + x - (if 65520 <? a + x then 65521 else 0) in
  let s := a1 + b in
  Z.lor (s * 2 ^ 16 - (if 65520 <? s then 65521 * 2 ^ 16 else 0)) a1
  = adler32_z_model adler [x].
Proof.
  intros adler x Hx. cbv zeta. unfold adler32_z_model. cbn [Zlen length Z.of_nat Pos.of_succ_nat Z.eqb Pos.eqb hd].
  rewrite <- !csub_sltu. rewrite (Z.add_comm (csub (lo16 adler + x)) (hi16 adler)).
  rewrite <- csub_sltu_shift16. symmetry. apply adler_comb_machine.
Qed.

Lemma adler_short_path : forall adler bs, Zlen bs <> 1 -> Zlen bs < 16 ->
  let ab := adler_fold (lo16 adler, hi16 adler) bs in
  Z.lor ((snd ab - snd ab / BASE * BASE) * 2 ^ 16) (fst ab - (if 65520 <? fst ab then 65521 else 0))
  = adler32_z_model adler bs.
Proof.
  intros adler bs H1 H16. cbv zeta. unfold adler32_z_model.
  destruct (Z.eqb_spec (Zlen bs) 1); [lia|]. destruct (Z.ltb_spec (Zlen bs) 16); [|lia].
  rewrite <- csub_sltu, mod_BASE_sub. symmetry. apply adler_comb_machine.
Qed.

Lemma adler_long_path : forall adler bs, 16 <= Zlen bs ->
  let nblk := Zlen bs / NMAX in
  let ab1 := adler_blocks (Z.to_nat nblk) (lo16 adler, hi16 adler) bs in
  let rest := skipn (Z.to_nat (NMAX * nblk)) bs in
  adler32_z_model adler bs
  = match rest with
    | [] => Z.lor (snd ab1 * 2 ^ 16) (fst ab1)
    | _ => let ab2 := adler_fold ab1 rest in
           Z.lor ((snd ab2 - snd ab2 / BASE * BASE) * 2 ^ 16) (fst ab2 - fst ab2 / BASE * BASE)
    end.
Proof.
  intros adler bs H16. cbv zeta. unfold adler32_z_model.
  destruct (Z.eqb_spec (Zlen bs) 1); [lia|]. destruct (Z.ltb_spec (Zlen bs) 16); [lia|].
  destruct (skipn (Z.to_nat (NMAX * (Zlen bs / NMAX))) bs); rewrite ?mod_BASE_sub; apply adler_comb_machine.
Qed.

