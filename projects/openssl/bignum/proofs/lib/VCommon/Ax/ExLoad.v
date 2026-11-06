(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import FastWord.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import ExLin ExVal ExBytes ExMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Lemma lor_shiftl_disj (x y k : Z) : 0 <= k -> 0 <= x < 2 ^ k -> 0 <= y ->
  Z.lor x (Z.shiftl y k) = x + Z.shiftl y k.
Proof.
  intros Hk Hx Hy. symmetry. rewrite Z.add_nocarry_lxor.
  - apply Z.lxor_lor. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_le_dec n k) as [Hlt|Hge].
    + rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
    + destruct (Z.eq_dec x 0) as [->|Hnz]; [rewrite Z.bits_0; reflexivity|].
      rewrite Z.bits_above_log2; [reflexivity | lia |]. apply Z.lt_le_trans with k; [|lia]. apply Z.log2_lt_pow2; lia.
  - apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_le_dec n k) as [Hlt|Hge].
    + rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
    + destruct (Z.eq_dec x 0) as [->|Hnz]; [rewrite Z.bits_0; reflexivity|].
      rewrite Z.bits_above_log2; [reflexivity | lia |]. apply Z.lt_le_trans with k; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma bytes_le_to_Z_zcombine (l : list byte) : bytes_le_to_Z l = zcombine (map bv_unsigned l).
Proof.
  induction l as [|b r IH]; [reflexivity|]. cbn [bytes_le_to_Z map zcombine]. rewrite IH.
  pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
  assert (Hr : 0 <= zcombine (map bv_unsigned r)).
  { rewrite <- IH. clear. induction r as [|c r IH]; cbn [bytes_le_to_Z]; [lia|].
    apply Z.lor_nonneg. split; [pose proof (bv_unsigned_in_range 8 c); lia | apply Z.shiftl_nonneg; exact IH]. }
  rewrite lor_shiftl_disj by (try lia; change (2 ^ 8) with 256; lia).
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. ring.
Qed.

Fixpoint all_lit (l : list abyte) : option (list int) :=
  match l with
  | [] => Some []
  | BL b :: r => match all_lit r with Some bs => Some (b :: bs) | None => None end
  | _ :: _ => None
  end.

Fixpoint icombine (bs : list int) : int :=
  match bs with
  | [] => 0%uint63
  | b :: r => (b + (icombine r << 8))%uint63
  end.

Lemma icombine_spec (bs : list int) : (length bs <= 7)%nat -> Forall (fun b => to_Z b < 256) bs ->
  to_Z (icombine bs) = zcombine (map to_Z bs).
Proof.
  intros Hl Hb. induction Hb as [|b r Hb Hr IH]; [reflexivity|]. cbn [icombine map zcombine length] in *.
  assert (Hr' : Forall (fun b => 0 <= b < 256) (map to_Z r)).
  { apply Forall_map. eapply Forall_impl; [|exact Hr]. intros c Hc. cbv beta in Hc |- *. pose proof (to_Z_bounded c). lia. }
  pose proof (zcombine_range _ Hr') as Hz. rewrite length_map in Hz.
  assert (H48 : 2 ^ (8 * Z.of_nat (length r)) <= 2 ^ 48) by (apply Z.pow_le_mono_r; lia).
  pose proof (to_Z_bounded b).
  change (2 ^ 48) with 281474976710656 in H48.
  rewrite add_spec, lsl_spec. rewrite IH by lia. change (to_Z 8%uint63) with 8. change (2 ^ 8) with 256. change wB with 9223372036854775808.
  rewrite (Z.mod_small (zcombine (map to_Z r) * 256)) by lia.
  rewrite Z.mod_small by lia. ring.
Qed.

Definition w_of_bytes8 (bs : list int) : w64 :=
  match bs with
  | [b0; b1; b2; b3; b4; b5; b6; b7] =>
      W (128 <=? b7)%uint63 (icombine [b0; b1; b2; b3; b4; b5; b6] + ((b7 land 127) << 56))%uint63
  | _ => w_zero
  end.

Lemma w_of_bytes8_spec (bs : list int) : length bs = 8%nat -> Forall (fun b => to_Z b < 256) bs ->
  wZ (w_of_bytes8 bs) = zcombine (map to_Z bs).
Proof.
  intros Hl Hb. destruct bs as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|]]]]]]]]]; try discriminate.
  pose proof Hb as Hb'. rewrite Forall_forall in Hb'.
  assert (B : forall c, In c [b0; b1; b2; b3; b4; b5; b6; b7] -> 0 <= to_Z c < 256).
  { intros c Hc. pose proof (to_Z_bounded c). specialize (Hb' c Hc). lia. }
  assert (Hb6 : Forall (fun b => to_Z b < 256) [b0; b1; b2; b3; b4; b5; b6]).
  { rewrite Forall_forall. intros c Hc. apply Hb'. cbn in Hc |- *. tauto. }
  pose proof (icombine_spec [b0; b1; b2; b3; b4; b5; b6] ltac:(cbn; lia) Hb6) as Hi.
  pose proof (Forall_impl _ (fun c (H : to_Z c < 256) => conj (proj1 (to_Z_bounded c)) H) Hb6) as Hb6'.
  pose proof (zcombine_range (map to_Z [b0; b1; b2; b3; b4; b5; b6])) as Hz.
  assert (Hz' : 0 <= zcombine (map to_Z [b0; b1; b2; b3; b4; b5; b6]) < 2 ^ 56).
  { apply Hz. apply Forall_map. exact Hb6'. }
  unfold w_of_bytes8, wZ. cbn [wh wl].
  pose proof (B b7 ltac:(cbn; tauto)) as H7.
  assert (E7 : to_Z (b7 land 127)%uint63 = to_Z b7 mod 128).
  { rewrite land_spec'. change (to_Z 127%uint63) with (Z.ones 7). rewrite Z.land_ones by lia. reflexivity. }
  assert (Esh : to_Z ((b7 land 127) << 56)%uint63 = (to_Z b7 mod 128) * 2 ^ 56).
  { rewrite lsl_spec, E7. change (to_Z 56%uint63) with 56. change wB with (2 ^ 63). apply Z.mod_small.
    pose proof (Z.mod_pos_bound (to_Z b7) 128 ltac:(lia)). change (2 ^ 56) with 72057594037927936. change (2^63) with 9223372036854775808. lia. }
  assert (Esum : to_Z (icombine [b0; b1; b2; b3; b4; b5; b6] + ((b7 land 127) << 56))%uint63
                 = zcombine (map to_Z [b0; b1; b2; b3; b4; b5; b6]) + (to_Z b7 mod 128) * 2 ^ 56).
  { rewrite add_spec, Hi, Esh. change wB with (2 ^ 63). apply Z.mod_small.
    pose proof (Z.mod_pos_bound (to_Z b7) 128 ltac:(lia)). change (2 ^ 56) with 72057594037927936 in *. change (2^63) with 9223372036854775808. lia. }
  rewrite Esum.
  change (map to_Z [b0; b1; b2; b3; b4; b5; b6; b7]) with (map to_Z [b0; b1; b2; b3; b4; b5; b6] ++ [to_Z b7]).
  assert (Happ : forall l z, zcombine (l ++ [z]) = zcombine l + 2 ^ (8 * Z.of_nat (length l)) * z).
  { induction l as [|c l IHl]; intros z; cbn [app zcombine length]; [cbn; lia|]. rewrite IHl. rewrite pow8. ring. }
  rewrite Happ. cbn [length map]. change (2 ^ (8 * Z.of_nat 7)) with 72057594037927936.
  change (2 ^ 56) with 72057594037927936.
  pose proof (Z.div_mod (to_Z b7) 128 ltac:(lia)).
  destruct (lebP 128 b7) as [E|E]; change (to_Z 128%uint63) with 128 in E.
  - assert (Hq : to_Z b7 / 128 = 1) by (symmetry; apply Z.div_unique with (r := to_Z b7 - 128); lia).
    unfold two63. lia.
  - assert (Hq : to_Z b7 / 128 = 0) by (apply Z.div_small; lia). lia.
Qed.

Lemma zext64_unsigned (n : N) (X : bv n) : (n <= 64)%N -> bv_unsigned (zext 64 X) = bv_unsigned X.
Proof.
  intros Hn. unfold zext. rewrite bv_zero_extend_unsigned' . unfold bv_wrap.
  pose proof (bv_unsigned_in_range n X) as HX. apply Z.mod_small. split; [lia|].
  apply Z.lt_le_trans with (bv_modulus n); [lia|]. unfold bv_modulus. apply Z.pow_le_mono_r; lia.
Qed.

Lemma sext64_unsigned (n : N) (X : bv n) : (1 <= n <= 64)%N ->
  bv_unsigned (sext 64 X) = if bv_unsigned X <? 2 ^ (Z.of_N n - 1) then bv_unsigned X else bv_unsigned X + two64 - 2 ^ Z.of_N n.
Proof.
  intros Hn. unfold sext. rewrite bv_sign_extend_unsigned. unfold bv_signed, bv_swrap, bv_wrap.
  pose proof (bv_unsigned_in_range n X) as HX. unfold bv_modulus in *. change (bv_modulus 64) with two64.
  unfold bv_half_modulus, bv_modulus.
  assert (Hp : 2 ^ Z.of_N n = 2 * 2 ^ (Z.of_N n - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
  assert (Hpos : 0 < 2 ^ (Z.of_N n - 1)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hh : 2 ^ Z.of_N n / 2 = 2 ^ (Z.of_N n - 1)) by (rewrite Hp; rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
  rewrite Hh. rewrite two64_eq in *. change (2 ^ Z.of_N 64) with (2 * two63) in *.
  assert (H64 : 2 ^ Z.of_N n <= 2 * two63) by (change (2 * two63) with (2 ^ 64); apply Z.pow_le_mono_r; lia).
  destruct (Z.ltb_spec (bv_unsigned X) (2 ^ (Z.of_N n - 1))).
  - rewrite (Z.mod_small (bv_unsigned X + 2 ^ (Z.of_N n - 1))) by lia.
    replace (bv_unsigned X + 2 ^ (Z.of_N n - 1) - 2 ^ (Z.of_N n - 1)) with (bv_unsigned X) by ring.
    apply Z.mod_small. lia.
  - replace (bv_unsigned X + 2 ^ (Z.of_N n - 1)) with ((bv_unsigned X - 2 ^ (Z.of_N n - 1)) + 1 * 2 ^ Z.of_N n) by lia.
    rewrite Z.mod_add by lia. rewrite (Z.mod_small (bv_unsigned X - 2 ^ (Z.of_N n - 1)) (2 ^ Z.of_N n)) by lia.
    replace (bv_unsigned X - 2 ^ (Z.of_N n - 1) - 2 ^ (Z.of_N n - 1)) with ((bv_unsigned X + 2 * two63 - 2 ^ Z.of_N n) + (-1) * (2 * two63)) by lia.
    rewrite Z.mod_add by (unfold two63; lia). apply Z.mod_small. lia.
Qed.

Lemma extract_le_unsigned (n : N) (bs : list byte) : (n <= 64)%N ->
  0 <= bytes_le_to_Z bs < 2 ^ Z.of_N n -> bv_unsigned (bv_extract 0 n (le_bytes_to_word bs)) = bytes_le_to_Z bs.
Proof.
  intros Hn Hb. rewrite bv_extract_unsigned. unfold le_bytes_to_word. rewrite Z_to_bv_unsigned.
  unfold bv_wrap. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r.
  assert (H64 : 2 ^ Z.of_N n <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small (bytes_le_to_Z bs)) by lia.
  unfold bv_modulus. apply Z.mod_small. exact Hb.
Qed.

Lemma mod_neg_small (a m : Z) : 0 < m -> - m <= a < 0 -> a mod m = a + m.
Proof.
  intros Hm Ha. replace a with ((a + m) + (-1) * m) at 1 by ring. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Definition msz_bits (sz : msize) : Z := match sz with SZ1 => 8 | SZ2 => 16 | SZ4 => 32 | SZ8 => 64 end.

Definition load_ext (sz : msize) (sg : bool) (z : w64) : w64 :=
  match sz with
  | SZ8 => z
  | SZ1 => if sg then (if w_ltu z (W false 128%uint63) then z else w_sub z (W false 256%uint63)) else z
  | SZ2 => if sg then (if w_ltu z (W false 32768%uint63) then z else w_sub z (W false 65536%uint63)) else z
  | SZ4 => if sg then (if w_ltu z (W false 2147483648%uint63) then z else w_sub z (W false 4294967296%uint63)) else z
  end.

Lemma load_ext_spec (ρ : valuation) (sz : msize) (sg : bool) (z : w64) (bs : list byte) :
  length bs = msz_n sz -> wZ z = bytes_le_to_Z bs ->
  aval_val ρ (VL (load_ext sz sg z)) (load_word sz sg bs).
Proof.
  intros Hl Hz. cbn [aval_val].
  assert (Hr : 0 <= bytes_le_to_Z bs < 2 ^ msz_bits sz).
  { rewrite bytes_le_to_Z_zcombine. assert (Hf : Forall (fun b => 0 <= b < 256) (map bv_unsigned bs)).
    { apply Forall_map. apply Forall_forall. intros b _. pose proof (bv_unsigned_in_range 8 b). change (bv_modulus 8) with 256 in *. lia. }
    pose proof (zcombine_range _ Hf) as H. rewrite length_map, Hl in H. destruct sz; cbn [msz_n msz_bits Z.of_nat] in *; exact H. }
  destruct sz; cbn [load_ext load_word msz_bits] in *.
  - destruct sg.
    + rewrite sext64_unsigned by lia. rewrite extract_le_unsigned by (try lia; exact Hr). rewrite <- Hz.
      rewrite w_ltu_spec. change (wZ (W false 128%uint63)) with 128. change (2 ^ (Z.of_N 8 - 1)) with 128.
      destruct (Z.ltb_spec (wZ z) 128); [reflexivity|]. rewrite wZ_sub. change (wZ (W false 256%uint63)) with 256.
      change (2 ^ Z.of_N 8) with 256. pose proof (wZ_range z). rewrite mod_neg_small; unfold two64 in *; lia.
    + rewrite zext64_unsigned by lia. rewrite extract_le_unsigned by (try lia; exact Hr). symmetry. exact Hz.
  - destruct sg.
    + rewrite sext64_unsigned by lia. rewrite extract_le_unsigned by (try lia; exact Hr). rewrite <- Hz.
      rewrite w_ltu_spec. change (wZ (W false 32768%uint63)) with 32768. change (2 ^ (Z.of_N 16 - 1)) with 32768.
      destruct (Z.ltb_spec (wZ z) 32768); [reflexivity|]. rewrite wZ_sub. change (wZ (W false 65536%uint63)) with 65536.
      change (2 ^ Z.of_N 16) with 65536. pose proof (wZ_range z). rewrite mod_neg_small; unfold two64 in *; lia.
    + rewrite zext64_unsigned by lia. rewrite extract_le_unsigned by (try lia; exact Hr). symmetry. exact Hz.
  - destruct sg.
    + rewrite sext64_unsigned by lia. rewrite extract_le_unsigned by (try lia; exact Hr). rewrite <- Hz.
      rewrite w_ltu_spec. change (wZ (W false 2147483648%uint63)) with 2147483648. change (2 ^ (Z.of_N 32 - 1)) with 2147483648.
      destruct (Z.ltb_spec (wZ z) 2147483648); [reflexivity|]. rewrite wZ_sub. change (wZ (W false 4294967296%uint63)) with 4294967296.
      change (2 ^ Z.of_N 32) with 4294967296. pose proof (wZ_range z). rewrite mod_neg_small; unfold two64 in *; lia.
    + rewrite zext64_unsigned by lia. rewrite extract_le_unsigned by (try lia; exact Hr). symmetry. exact Hz.
  - rewrite extract_le_unsigned by (try lia; exact Hr). symmetry. exact Hz.
Qed.

Definition lin_eqb (f g : lin) : bool := (fst f =? fst g) && teqb (snd f) (snd g).

Fixpoint frags_of (f : lin) (i : nat) (l : list abyte) : bool :=
  match l with
  | [] => Nat.eqb i 8
  | BF (VS g) j :: r => lin_eqb f g && Nat.eqb i j && frags_of f (S i) r
  | _ :: _ => false
  end.

Definition a_load_val (sz : msize) (sg : bool) (l : list abyte) : aval :=
  match all_lit l with
  | Some bs => VL (load_ext sz sg (match sz with SZ8 => w_of_bytes8 bs | _ => W false (icombine bs) end))
  | None =>
      match sz, l with
      | SZ8, BF (VS f) O :: _ => if frags_of f 0 l then VS f else VT
      | _, _ => VT
      end
  end.

Definition a_load_val' (s : store) (sz : msize) (sg : bool) (l : list abyte) : aval :=
  match a_load_val sz sg l with
  | VT =>
      match sz, l with
      | SZ1, [BF (VS f) O] =>
          match lrange s f with
          | Some (lo, hi) =>
              if sg then (if (0 <=? lo) && (hi <=? 127) then mk_vs s f
                          else if (128 <=? lo) && (hi <=? 255) then mk_vs s (laddc f (two64 - 256)) else VT)
              else (if (0 <=? lo) && (hi <=? 255) then mk_vs s f else VT)
          | None => VT
          end
      | _, _ => VT
      end
  | v => v
  end.

Definition astore_bytes (sz : msize) (v : aval) : list abyte :=
  let n := msz_n sz in
  match v with
  | VL x => map (fun i => BL (w_byte x i)) (seq 0 n)
  | VS _ => map (fun i => BF v i) (seq 0 n)
  | _ => repeat BT n
  end.

Lemma Z_to_le_bytes_nth (n : nat) (z : Z) (i : nat) : 0 <= z -> (i < n)%nat ->
  bv_unsigned (nth i (Z_to_le_bytes n z) (Z_to_bv 8 0)) = zbyte z i.
Proof.
  revert z i. induction n as [|n IH]; intros z i Hz Hi; [lia|]. cbn [Z_to_le_bytes].
  destruct i as [|i]; cbn [nth].
  - rewrite Z_to_bv_unsigned, zbyte_0. reflexivity.
  - rewrite IH by (try apply Z.shiftr_nonneg; lia). rewrite zbyte_S by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma zbyte_mod (z : Z) (k : Z) (i : nat) : 0 <= z -> 8 * Z.of_nat i + 8 <= k -> zbyte (z mod 2 ^ k) i = zbyte z i.
Proof.
  intros Hz Hk. unfold zbyte. set (A := 2 ^ (8 * Z.of_nat i)). set (B := 2 ^ (k - 8 * Z.of_nat i)).
  assert (HA : 0 < A) by (apply Z.pow_pos_nonneg; lia). assert (HB : 0 < B) by (apply Z.pow_pos_nonneg; lia).
  assert (Hp : 2 ^ k = A * B) by (unfold A, B; rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Hp. rewrite Z.rem_mul_r by lia.
  replace (z mod A + A * ((z / A) mod B)) with (z mod A + ((z / A) mod B) * A) by ring.
  rewrite Z.div_add by lia. rewrite Z.div_small by (apply Z.mod_pos_bound; lia). rewrite Z.add_0_l.
  assert (Hq : B = 256 * 2 ^ (k - 8 * Z.of_nat i - 8)) by (unfold B; rewrite <- (Z.pow_add_r 2 8) by lia; f_equal; lia).
  rewrite Hq. rewrite Z.rem_mul_r by (try lia; apply Z.pow_pos_nonneg; lia).
  replace ((z / A) mod 256 + 256 * ((z / A / 256) mod 2 ^ (k - 8 * Z.of_nat i - 8)))
    with ((z / A) mod 256 + ((z / A / 256) mod 2 ^ (k - 8 * Z.of_nat i - 8)) * 256) by ring.
  rewrite Z.mod_add by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma Forall2_of_nth {X Y : Type} (P : X -> Y -> Prop) (l1 : list X) (l2 : list Y) (d1 : X) (d2 : Y) :
  length l1 = length l2 -> (forall i, (i < length l1)%nat -> P (nth i l1 d1) (nth i l2 d2)) -> Forall2 P l1 l2.
Proof.
  revert l2; induction l1 as [|x r IH]; intros [|y l2] Hl H; cbn [length] in *; try discriminate; constructor.
  - exact (H 0%nat ltac:(lia)).
  - apply IH; [lia|]. intros i Hi. exact (H (S i) ltac:(lia)).
Qed.

Definition store_trunc (sz : msize) (w : bv 64) : Z := bv_unsigned w mod 2 ^ msz_bits sz.

Lemma store_bytes_trunc (sz : msize) (w : bv 64) : store_bytes sz w = Z_to_le_bytes (msz_n sz) (store_trunc sz w).
Proof.
  unfold store_bytes, store_trunc. pose proof (bvu_range w) as Hw.
  destruct sz; cbn [msz_bits msz_n].
  - rewrite bv_extract_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8). rewrite Z.shiftr_0_r. reflexivity.
  - rewrite bv_extract_unsigned. unfold bv_wrap. change (bv_modulus 16) with (2 ^ 16). rewrite Z.shiftr_0_r. reflexivity.
  - unfold low32. rewrite bv_extract_unsigned. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). rewrite Z.shiftr_0_r. reflexivity.
  - rewrite Z.mod_small; [reflexivity|]. unfold two64 in Hw. change (2 ^ 64) with 18446744073709551616. lia.
Qed.

