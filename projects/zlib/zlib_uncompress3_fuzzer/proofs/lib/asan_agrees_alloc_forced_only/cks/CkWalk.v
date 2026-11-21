(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.cks Require Import
  CkTables CkModel CkXt CkMultmodp CkMathCrc CkMathAdler.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).


Definition M20 : Z := 14757395258967641293.

Lemma M20_val : M20 = 14757395258967641293.
Proof. reflexivity. Qed.

Lemma M20_build : (18446744072850558157 + (18446744072850558157 * 2 ^ 32) mod 2 ^ 64) mod 2 ^ 64 = M20.
Proof. vm_compute. reflexivity. Qed.

Theorem div20_magic_Z : forall x, 0 <= x < 2 ^ 64 -> x * M20 / 2 ^ 64 / 2 ^ 4 = x / 20.
Proof.
  intros x Hx. rewrite M20_val. rewrite Z.div_div by lia. change (2 ^ 64 * 2 ^ 4) with (2 ^ 68).
  pose proof (Z.div_mod x 20 ltac:(lia)) as Hx1.
  pose proof (Z.mod_pos_bound x 20 ltac:(lia)) as Hx2.
  set (q := x / 20) in *. set (r := x mod 20) in *.
  assert (HK : 14757395258967641293 * 20 = 2 ^ 68 + 4) by reflexivity.
  symmetry. apply (Z.div_unique_pos (x * 14757395258967641293) (2 ^ 68) q (q * 4 + r * 14757395258967641293)); lia.
Qed.

Theorem div20_magic : forall x, 0 <= x < 2 ^ 64 -> Z.shiftr (x * M20 / 2 ^ 64) 4 = x / 20.
Proof. intros x Hx. rewrite Z.shiftr_div_pow2 by lia. apply div20_magic_Z. exact Hx. Qed.

Lemma div20_ranges : forall x, 0 <= x < 2 ^ 64 ->
  0 <= x * M20 / 2 ^ 64 < 2 ^ 64 /\ 0 <= x / 20 <= x /\ 0 <= x - x / 20 * 20 < 20 /\
  x - x / 20 * 20 = x mod 20.
Proof.
  intros x Hx. rewrite M20_val.
  pose proof (Z.div_mod x 20 ltac:(lia)). pose proof (Z.mod_pos_bound x 20 ltac:(lia)).
  assert (0 <= x / 20) by (apply Z.div_pos; lia).
  assert (0 <= x * 14757395258967641293 / 2 ^ 64) by (apply Z.div_pos; lia).
  assert (x * 14757395258967641293 / 2 ^ 64 < 2 ^ 64) by (apply Z.div_lt_upper_bound; lia).
  lia.
Qed.

Lemma blks_ge_1 : forall len na, 23 <= len -> 0 <= na <= 3 -> 1 <= (len - na) / 20.
Proof. intros. apply Z.div_le_lower_bound; lia. Qed.


Lemma crc_byte_range : forall c b, 0 <= c < 2 ^ 32 -> 0 <= b < 256 -> 0 <= crc_byte c b < 2 ^ 32.
Proof.
  intros c b Hc Hb. rewrite crc_byte_step by lia. unfold crc_step. apply xtn_range. apply lxor_bound32; lia.
Qed.

Lemma crc_bytes_range : forall bs c, bytes bs -> 0 <= c < 2 ^ 32 -> 0 <= crc_bytes c bs < 2 ^ 32.
Proof.
  intros bs c Hbs Hc. rewrite crc_bytes_fold by assumption.
  apply crc_fold_range; [exact Hc | apply bytes_In; exact Hbs].
Qed.

Lemma crc_pre_range' : forall c, 0 <= crc_pre c < 2 ^ 32.
Proof. exact crc_pre_range. Qed.

Lemma crc_word1_range : forall x, 0 <= x < 2 ^ 32 -> 0 <= crc_word1 x < 2 ^ 32.
Proof. intros x Hx. rewrite crc_word1_xtn by lia. apply (xtn_range 8 x Hx). Qed.

Lemma braid1_range : forall c w, 0 <= c < 2 ^ 32 -> 0 <= w < 2 ^ 32 -> 0 <= braid1 c w < 2 ^ 32.
Proof. intros c w Hc Hw. rewrite braid1_lane by assumption. apply xtn_range. apply lxor_bound32; assumption. Qed.

Lemma wle_range' : forall b0 b1 b2 b3,
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 -> 0 <= wle b0 b1 b2 b3 < 2 ^ 32.
Proof. exact wle_range. Qed.


Lemma braid_state_lanes : forall i c bs, bytes bs -> 0 <= c < 2 ^ 32 -> (20 * i <= length bs)%nat ->
  exists l0 l1 l2 l3 l4, braid_state [c; 0; 0; 0; 0] i bs = [l0; l1; l2; l3; l4] /\
    0 <= l0 < 2 ^ 32 /\ 0 <= l1 < 2 ^ 32 /\ 0 <= l2 < 2 ^ 32 /\ 0 <= l3 < 2 ^ 32 /\ 0 <= l4 < 2 ^ 32.
Proof.
  intros i c bs Hbs Hc Hlen.
  destruct (braid_state_ok i [c; 0; 0; 0; 0] c bs (lanes_ok_init c Hc) Hbs Hlen)
    as (l0 & l1 & l2 & l3 & l4 & E & H0 & H1 & H2 & H3 & H4 & _).
  exists l0, l1, l2, l3, l4. repeat split; try exact E; lia.
Qed.

Lemma words_le_20 : forall b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 rest,
  words_le (b0::b1::b2::b3::b4::b5::b6::b7::b8::b9::b10::b11::b12::b13::b14::b15::b16::b17::b18::b19::rest)
  = wle b0 b1 b2 b3 :: wle b4 b5 b6 b7 :: wle b8 b9 b10 b11 :: wle b12 b13 b14 b15 :: wle b16 b17 b18 b19 :: words_le rest.
Proof. reflexivity. Qed.

Lemma braid_step_5 : forall l0 l1 l2 l3 l4 blk w0 w1 w2 w3 w4 ws,
  words_le blk = w0 :: w1 :: w2 :: w3 :: w4 :: ws ->
  braid_step [l0; l1; l2; l3; l4] blk = [braid1 l0 w0; braid1 l1 w1; braid1 l2 w2; braid1 l3 w3; braid1 l4 w4].
Proof. intros * Hw. unfold braid_step. rewrite Hw. reflexivity. Qed.

Lemma braid_last_5 : forall l0 l1 l2 l3 l4 blk w0 w1 w2 w3 w4,
  words_le blk = [w0; w1; w2; w3; w4] ->
  braid_last [l0; l1; l2; l3; l4] blk
  = crc_word (Z.lxor (Z.lxor l4 w4) (crc_word (Z.lxor (Z.lxor l3 w3) (crc_word (Z.lxor (Z.lxor l2 w2)
      (crc_word (Z.lxor (Z.lxor l1 w1) (crc_word (Z.lxor l0 w0))))))))).
Proof. intros * Hw. unfold braid_last. rewrite Hw. reflexivity. Qed.

Lemma block_eq : forall i bs, block i bs = firstn 20 (skipn (20 * i) bs).
Proof. reflexivity. Qed.

Lemma block_length' : forall i bs, (20 * S i <= length bs)%nat -> length (block i bs) = 20%nat.
Proof. exact block_length. Qed.

Lemma words_le_length5 : forall blk, length blk = 20%nat -> length (words_le blk) = 5%nat.
Proof.
  intros blk H.
  destruct blk as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 [|b9 [|b10 [|b11 [|b12 [|b13 [|b14 [|b15 [|b16 [|b17 [|b18 [|b19 [|x l]]]]]]]]]]]]]]]]]]]]];
    cbn in H; try lia. reflexivity.
Qed.


Definition crc_mid (adr c : Z) (bs : list Z) : Z * list Z :=
  if Zlen bs <? 23 then (crc_pre c, bs) else crc_braid_phase adr (crc_pre c) bs.

Lemma crc32_z_model_mid : forall adr c bs,
  crc32_z_model adr c bs = Z.lxor (crc_bytes (fst (crc_mid adr c bs)) (snd (crc_mid adr c bs))) M32.
Proof. intros. unfold crc32_z_model, crc_mid. destruct (Zlen bs <? 23); reflexivity. Qed.

Lemma crc_mid_short : forall adr c bs, Zlen bs < 23 -> crc_mid adr c bs = (crc_pre c, bs).
Proof. intros adr c bs H. unfold crc_mid. destruct (Z.ltb_spec (Zlen bs) 23); [reflexivity | lia]. Qed.

Lemma crc_mid_long : forall adr c bs, 23 <= Zlen bs -> crc_mid adr c bs = crc_braid_phase adr (crc_pre c) bs.
Proof. intros adr c bs H. unfold crc_mid. destruct (Z.ltb_spec (Zlen bs) 23); [lia | reflexivity]. Qed.

Lemma crc_braid_phase_eq : forall adr c bs,
  crc_braid_phase adr c bs =
  (let na := align4 adr in
   let c1 := crc_bytes c (firstn (Z.to_nat na) bs) in
   let bs1 := skipn (Z.to_nat na) bs in
   let blks := Zlen bs1 / 20 in
   let cs := braid_state [c1; 0; 0; 0; 0] (Z.to_nat (blks - 1)) bs1 in
   (braid_last cs (block (Z.to_nat (blks - 1)) bs1), skipn (Z.to_nat (20 * blks)) bs1)).
Proof. reflexivity. Qed.

Lemma crc_mid_range : forall adr c bs, bytes bs -> 0 <= fst (crc_mid adr c bs) < 2 ^ 32.
Proof.
  intros adr c bs Hbs. unfold crc_mid. pose proof (crc_pre_range c) as Hc.
  destruct (Z.ltb_spec (Zlen bs) 23) as [H|H]; [exact Hc|].
  rewrite (crc_braid_phase_fold adr (crc_pre c) bs Hbs Hc H). cbn [fst].
  apply crc_fold_range; [exact Hc | apply bytes_In, bytes_firstn, Hbs].
Qed.

Lemma crc_mid_bytes : forall adr c bs, bytes bs -> bytes (snd (crc_mid adr c bs)).
Proof.
  intros adr c bs Hbs. unfold crc_mid. pose proof (crc_pre_range c) as Hc.
  destruct (Z.ltb_spec (Zlen bs) 23) as [H|H]; [exact Hbs|].
  rewrite (crc_braid_phase_fold adr (crc_pre c) bs Hbs Hc H). cbn [snd]. apply bytes_skipn. exact Hbs.
Qed.

Lemma align4_spec : forall adr, 0 <= adr -> (adr + align4 adr) mod 4 = 0 /\ 0 <= align4 adr <= 3 /\
  (forall j, 0 <= j < align4 adr -> (adr + j) mod 4 <> 0).
Proof.
  intros adr Hadr. unfold align4. repeat split; try lia.
Qed.

Lemma align4_0 : forall adr, adr mod 4 = 0 -> align4 adr = 0.
Proof. intros adr H. unfold align4. rewrite H. reflexivity. Qed.

Lemma align4_step : forall adr, 0 <= adr -> adr mod 4 <> 0 -> align4 adr = 1 + align4 (adr + 1).
Proof. intros adr Hadr H. unfold align4. lia. Qed.


Lemma nmax_test : forall len, 0 <= len -> (347 <= Z.shiftr len 4 <-> NMAX <= len).
Proof. intros len H. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. unfold NMAX. lia. Qed.

Lemma len16_test : forall len, 0 <= len -> (Z.shiftr len 4 < 347 <-> len < NMAX).
Proof. intros len H. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. unfold NMAX. lia. Qed.


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

Lemma adler_inner_bound : forall n a b bs seg,
  0 <= a <= 65535 -> 0 <= b <= 65535 -> bytes seg -> Zlen seg <= NMAX ->
  let ab := adler_blocks n (a, b) bs in
  0 <= fst (adler_fold ab seg) < 2 ^ 21 /\ 0 <= snd (adler_fold ab seg) < 2 ^ 34.
Proof.
  intros n a b bs seg Ha Hb Hseg Hlen ab.
  pose proof (adler_blocks_bound16 n a b bs Ha Hb) as [H1 H2].
  subst ab. rewrite (adler_fold_pair seg).
  apply adler_fold_bound_nmax; [lia | lia | exact Hseg | exact Hlen].
Qed.

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

Lemma adler_comb_add' : forall a b, 0 <= a < 65536 -> 0 <= b -> Z.lor (b * 2 ^ 16) a = a + 65536 * b.
Proof. intros a b Ha Hb. rewrite <- adler_comb_machine. apply adler_comb_add; assumption. Qed.

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

Lemma adler_rest_length : forall bs : list Z, 0 <= Zlen bs ->
  Zlen (skipn (Z.to_nat (NMAX * (Zlen bs / NMAX))) bs) = Zlen bs mod NMAX.
Proof.
  intros bs H. unfold Zlen in *. rewrite length_skipn. unfold NMAX.
  pose proof (Z.div_mod (Z.of_nat (length bs)) 5552 ltac:(lia)).
  pose proof (Z.mod_pos_bound (Z.of_nat (length bs)) 5552 ltac:(lia)).
  assert (0 <= Z.of_nat (length bs) / 5552) by (apply Z.div_pos; lia).
  nia.
Qed.
