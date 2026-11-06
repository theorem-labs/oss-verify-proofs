(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import FastWord.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExLin ExVal ExBytes ExMem.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint all_lit (l : list abyte) : option (list int) :=
  match l with
  | [] => Some []
  | BL b :: r => match all_lit r with Some bs => Some (b :: bs) | None => None end
  | _ :: _ => None
  end.

Lemma all_lit_map (l : list abyte) (bs : list int) : all_lit l = Some bs -> l = map BL bs.
Proof.
  revert bs; induction l as [|[b| |v i] r IH]; intros bs H; cbn [all_lit] in H; try discriminate.
  - injection H as <-. reflexivity.
  - destruct (all_lit r) as [bs'|] eqn:E; [|discriminate]. injection H as <-. cbn [map]. f_equal. apply IH. reflexivity.
Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lin_eqb (f g : lin) : bool := (fst f =? fst g) && teqb (snd f) (snd g).

Lemma lin_eqb_eq (f g : lin) : lin_eqb f g = true -> f = g.
Proof.
  destruct f as [c ts], g as [d us]. unfold lin_eqb. cbn [fst snd]. intros H. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply teqb_eq in H2. subst. reflexivity.
Qed.

(* [comment removed for export] *)
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

Lemma frags_of_spec (f : lin) (l : list abyte) : forall i, frags_of f i l = true ->
  l = map (fun j => BF (VS f) j) (seq i (length l)) /\ (i + length l = 8)%nat.
Proof.
  induction l as [|ab r IH]; intros i H; cbn [frags_of] in H.
  - apply Nat.eqb_eq in H. split; [reflexivity | cbn; lia].
  - destruct ab as [| |v j]; try discriminate. destruct v as [|g| | |]; try discriminate.
    apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply lin_eqb_eq in H1. apply Nat.eqb_eq in H2. subst g j.
    destruct (IH (S i) H3) as [E L]. cbn [length seq map]. split; [f_equal; exact E | lia].
Qed.

Lemma zbyte_unique (ρ : valuation) (f : lin) (w w' : bv 64) :
  aval_val ρ (VS f) w -> aval_val ρ (VS f) w' -> w = w'.
Proof. cbn [aval_val]. intros H1 H2. apply bv_eq. rewrite H1, H2. reflexivity. Qed.

Lemma a_load_val_sound (ρ : valuation) (sz : msize) (sg : bool) (l : list abyte) (bs : list byte) :
  Forall2 (abyte_val ρ) l bs -> length l = msz_n sz ->
  aval_val ρ (a_load_val sz sg l) (load_word sz sg bs).
Proof.
  intros Hf Hl. pose proof (Forall2_length Hf) as Hlb. unfold a_load_val.
  destruct (all_lit l) as [ints|] eqn:Ea.
  - apply all_lit_map in Ea. subst l. rewrite length_map in Hl.
    assert (Hmap : map bv_unsigned bs = map to_Z ints).
    { revert Hf. clear. revert bs. induction ints as [|x r IH]; intros bs Hf; inversion Hf as [|? b ? bs' Hxb Hr]; subst; [reflexivity|].
      cbn [map abyte_val] in *. rewrite Hxb. f_equal. apply IH. exact Hr. }
    assert (Hlt : Forall (fun b => to_Z b < 256) ints).
    { apply Forall_forall. intros x Hx. assert (In (to_Z x) (map bv_unsigned bs)) by (rewrite Hmap; apply in_map; exact Hx).
      apply in_map_iff in H as [b [Hb _]]. pose proof (bv_unsigned_in_range 8 b). change (bv_modulus 8) with 256 in *. lia. }
    apply load_ext_spec; [rewrite <- Hlb, length_map; exact Hl|]. rewrite bytes_le_to_Z_zcombine, Hmap.
    destruct sz; cbn [msz_n] in Hl.
    + apply icombine_spec; [lia | exact Hlt].
    + apply icombine_spec; [lia | exact Hlt].
    + apply icombine_spec; [lia | exact Hlt].
    + apply w_of_bytes8_spec; [exact Hl | exact Hlt].
  - destruct sz; try exact I. destruct l as [|ab r]; [exact I|]. destruct ab as [| |v i]; try exact I.
    destruct v as [|f| | |]; try exact I. destruct i as [|i]; try exact I.
    destruct (frags_of f 0 (BF (VS f) 0 :: r)) eqn:Ef; [|exact I].
    destruct (frags_of_spec f _ 0 Ef) as [E L]. cbn [aval_val].
    (* [comment removed for export] *)
    assert (Hb : forall k, (k < 8)%nat -> exists w, aval_val ρ (VS f) w /\ bv_unsigned (nth k bs (Z_to_bv 8 0)) = zbyte (bv_unsigned w) k).
    { intros k Hk. rewrite E in Hf. clear -Hf Hk L.
      assert (Hk' : (k < length (map (fun j => BF (VS f) j) (seq 0 (length (BF (VS f) 0 :: r)))))%nat) by (rewrite length_map, length_seq; lia).
      destruct (Forall2_nth_error_ex _ _ bs k BT Hf Hk') as [b [Hb Hab]].
      rewrite (nth_map_seq0 (fun j => BF (VS f) j) _ k BT) in Hab by lia.
      destruct Hab as [w [Hw Hbw]]. exists w. split; [exact Hw|]. rewrite (nth_error_nth bs k _ Hb). exact Hbw. }
    assert (Hlen8 : length bs = 8%nat) by (rewrite <- Hlb; exact L).
    assert (Hm : map bv_unsigned bs = map (zbyte (leval ρ f)) (seq 0 8)).
    { apply nth_ext with (d := 0) (d' := 0).
      - rewrite !length_map, length_seq. exact Hlen8.
      - intros k Hk. rewrite length_map in Hk.
        rewrite (nth_map_seq0 (zbyte (leval ρ f)) 8 k 0) by lia.
        rewrite nth_indep with (d' := bv_unsigned (Z_to_bv 8 0)) by (rewrite length_map; exact Hk).
        rewrite map_nth. destruct (Hb k ltac:(lia)) as [w [Hw Hbw]]. cbn [aval_val] in Hw. rewrite Hbw, Hw. reflexivity. }
    destruct (Hb 0%nat ltac:(lia)) as [w0 [Hw0 _]]. cbn [aval_val] in Hw0.
    pose proof (bvu_range w0) as Hr0.
    unfold load_word. rewrite extract_le_unsigned.
    + rewrite bytes_le_to_Z_zcombine, Hm. rewrite zcombine_bytes by lia. change (8 * Z.of_nat 8) with 64.
      apply Z.mod_small. unfold two64 in *. change (2 ^ 64) with 18446744073709551616. lia.
    + lia.
    + rewrite bytes_le_to_Z_zcombine, Hm. rewrite zcombine_bytes by lia. change (8 * Z.of_nat 8) with 64.
      apply Z.mod_pos_bound. lia.
Qed.

(* [comment removed for export] *)
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

Lemma a_load_val'_sound (ρ : valuation) (s : store) (sz : msize) (sg : bool) (l : list abyte) (bs : list byte) :
  sat ρ s -> Forall2 (abyte_val ρ) l bs -> length l = msz_n sz ->
  aval_val ρ (a_load_val' s sz sg l) (load_word sz sg bs).
Proof.
  intros Hs Hf Hl. unfold a_load_val'. pose proof (a_load_val_sound ρ sz sg l bs Hf Hl) as H0.
  destruct (a_load_val sz sg l) eqn:E; try exact H0.
  destruct sz; try exact I. destruct l as [|ab [|ab2 l2]]; try exact I.
  2: { destruct ab as [| |v i]; try exact I; destruct v; try exact I; destruct i; exact I. }
  destruct ab as [| |v i]; try exact I.
  destruct v as [|f| | |]; try exact I. destruct i as [|i]; try exact I.
  destruct (lrange s f) as [[lo hi]|] eqn:Er; [|exact I].
  pose proof (lrange_sound ρ s f Hs _ Er) as Hr. cbn [fst snd] in Hr.
  inversion Hf as [|? b ? bs' Hab Hrest]; subst. inversion Hrest; subst.
  destruct Hab as [w [Hw Hb]]. cbn [aval_val] in Hw. rewrite Hw in Hb. rewrite zbyte_0 in Hb.
  assert (Hlw : bytes_le_to_Z [b] = bv_unsigned b) by (rewrite bytes_le_to_Z_zcombine; cbn [map zcombine]; lia).
  assert (Hbr : 0 <= bytes_le_to_Z [b] < 2 ^ 8) by (rewrite Hlw; pose proof (bv_unsigned_in_range 8 b); change (bv_modulus 8) with (2^8) in *; lia).
  destruct sg.
  - destruct ((0 <=? lo) && (hi <=? 127)) eqn:E1.
    + apply andb_prop in E1 as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
      apply mk_vs_sound; [exact Hs|]. cbn [load_word]. rewrite sext64_unsigned by lia.
      rewrite extract_le_unsigned by (try lia; exact Hbr). rewrite Hlw, Hb. rewrite Z.mod_small by lia.
      change (2 ^ (Z.of_N 8 - 1)) with 128. rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite Z.mod_small; [reflexivity|]. unfold two64; lia.
    + destruct ((128 <=? lo) && (hi <=? 255)) eqn:E2; [|exact I].
      apply andb_prop in E2 as [E2 E3]. apply Z.leb_le in E2. apply Z.leb_le in E3.
      apply mk_vs_sound; [exact Hs|]. cbn [load_word]. rewrite sext64_unsigned by lia.
      rewrite extract_le_unsigned by (try lia; exact Hbr). rewrite Hlw, Hb. rewrite Z.mod_small by lia.
      change (2 ^ (Z.of_N 8 - 1)) with 128. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite leval_laddc.
      change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small; [ring|]. unfold two64; lia.
  - destruct ((0 <=? lo) && (hi <=? 255)) eqn:E1; [|exact I].
    apply andb_prop in E1 as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    apply mk_vs_sound; [exact Hs|]. cbn [load_word]. rewrite zext64_unsigned by lia.
    rewrite extract_le_unsigned by (try lia; exact Hbr). rewrite Hlw, Hb. rewrite Z.mod_small by lia.
    rewrite Z.mod_small; [reflexivity|]. unfold two64; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

Lemma astore_bytes_sound (ρ : valuation) (sz : msize) (v : aval) (w : bv 64) :
  aval_val ρ v w -> Forall2 (abyte_val ρ) (astore_bytes sz v) (store_bytes sz w).
Proof.
  intros Hv. rewrite store_bytes_trunc. pose proof (bvu_range w) as Hw.
  assert (Htr : forall i, (i < msz_n sz)%nat -> zbyte (store_trunc sz w) i = zbyte (bv_unsigned w) i).
  { intros i Hi. unfold store_trunc. apply zbyte_mod; [lia|]. destruct sz; cbn [msz_bits msz_n] in *; lia. }
  assert (Htr0 : 0 <= store_trunc sz w) by (unfold store_trunc; apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; destruct sz; cbn; lia).
  assert (Hlen : length (astore_bytes sz v) = msz_n sz).
  { unfold astore_bytes. destruct v; rewrite ?length_map, ?length_seq, ?repeat_length; reflexivity. }
  apply (Forall2_of_nth _ _ _ BT (Z_to_bv 8 0)).
  - rewrite length_Z_to_le_bytes. exact Hlen.
  - intros i Hi. rewrite Hlen in Hi.
    assert (Hb : bv_unsigned (nth i (Z_to_le_bytes (msz_n sz) (store_trunc sz w)) (Z_to_bv 8 0)) = zbyte (bv_unsigned w) i).
    { rewrite (Z_to_le_bytes_nth _ _ _ Htr0 Hi). apply Htr. exact Hi. }
    unfold astore_bytes. destruct v as [x|f|lo hi| |km kv].
    + rewrite (nth_map_seq0 (fun i0 => BL (w_byte x i0)) _ i BT Hi). cbn [abyte_val]. cbn [aval_val] in Hv.
      rewrite Hb. rewrite w_byte_spec by (destruct sz; cbn in Hi; lia). rewrite Hv. reflexivity.
    + rewrite (nth_map_seq0 (fun i0 => BF (VS f) i0) _ i BT Hi). cbn [abyte_val]. exists w. split; [exact Hv | exact Hb].
    + rewrite nth_repeat. exact I.
    + rewrite nth_repeat. exact I.
    + rewrite nth_repeat. exact I.
Qed.

Lemma astore_bytes_length (sz : msize) (v : aval) : length (astore_bytes sz v) = msz_n sz.
Proof. unfold astore_bytes. destruct v; rewrite ?length_map, ?length_seq, ?repeat_length; reflexivity. Qed.
