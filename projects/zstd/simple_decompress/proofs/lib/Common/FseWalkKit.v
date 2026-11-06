(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import STRW_tac.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac showpc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "pc =" pc | _ => idtac "showpc: not an evt goal" end.
Ltac showreg r := let v := reg_val r in idtac "x" r "=" v.
Ltac showmem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => idtac "mem =" m end.

(* [comment removed for export] *)
Ltac call_pure_post :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO; hnf in PO; destruct_exs PO; subst ms';
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).
Tactic Notation "call_pure" uconstr(SPEC) := eapply evt_cut; [ eapply SPEC | call_pure_post ].

(* [comment removed for export] *)
Lemma ite_true : forall (A : Type) (b : bool) (x y : A), b = true -> (if b then x else y) = x.
Proof. intros A b x y ->. reflexivity. Qed.
Lemma ite_false : forall (A : Type) (b : bool) (x y : A), b = false -> (if b then x else y) = y.
Proof. intros A b x y ->. reflexivity. Qed.
Lemma ite_negb_true : forall (A : Type) (b : bool) (x y : A), b = true -> (if negb b then x else y) = y.
Proof. intros A b x y ->. reflexivity. Qed.
Lemma ite_negb_false : forall (A : Type) (b : bool) (x y : A), b = false -> (if negb b then x else y) = x.
Proof. intros A b x y ->. reflexivity. Qed.

(* [comment removed for export] *)
Lemma swrap32_eq : forall z, bv_swrap 32 z = (z + 2147483648) mod 4294967296 - 2147483648.
Proof. reflexivity. Qed.
Lemma swrap32_small : forall z, - 2147483648 <= z < 2147483648 -> bv_swrap 32 z = z.
Proof. intros z Hz. rewrite swrap32_eq. rewrite Z.mod_small by lia. lia. Qed.
Lemma wrap32_eq : forall z, bv_wrap 32 z = z mod 4294967296.
Proof. reflexivity. Qed.
Lemma wrap32_small : forall z, 0 <= z < 4294967296 -> bv_wrap 32 z = z.
Proof. intros. rewrite wrap32_eq. apply Z.mod_small. lia. Qed.
Lemma swrap16_eq : forall z, bv_swrap 16 z = (z + 32768) mod 65536 - 32768.
Proof. reflexivity. Qed.
Lemma swrap16_small : forall z, - 32768 <= z < 32768 -> bv_swrap 16 z = z.
Proof. intros z Hz. rewrite swrap16_eq. rewrite Z.mod_small by lia. lia. Qed.

(* [comment removed for export] *)
Lemma swrap32_eqm : forall x y, - 2147483648 <= y < 2147483648 -> (x - y) mod 4294967296 = 0 -> bv_swrap 32 x = y.
Proof. intros x y Hy Hm. rewrite swrap32_eq. Z.div_mod_to_equations. lia. Qed.
Ltac sw32 y :=
  match goal with |- context [bv_swrap 32 ?x] =>
    rewrite (swrap32_eqm x y) by (first [ lia | Z.div_mod_to_equations; lia ])
  end.

(* [comment removed for export] *)
Lemma unsigned_neg : forall z, - 2^63 <= z < 0 -> bv_unsigned (Z_to_bv 64 z) = z + 2^64.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  rewrite <- (Z.mod_add z 1) by lia. apply Z.mod_small. lia.
Qed.
Lemma signed_lit : forall z, - 2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). change (2^64 / 2) with (2^63).
  rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint u16s (ws : list word) : list byte :=
  match ws with [] => [] | w :: ws' => le2 w ++ u16s ws' end.

Lemma u16s_length : forall ws, length (u16s ws) = (2 * length ws)%nat.
Proof. induction ws; cbn -[le2]; [reflexivity|]. rewrite length_app, length_le2, IHws. lia. Qed.
Lemma u16s_app : forall a b, u16s (a ++ b) = u16s a ++ u16s b.
Proof. induction a; intros; cbn -[le2]; [reflexivity|]. rewrite IHa, app_assoc. reflexivity. Qed.

Ltac simpl_arr_sizes ::= rewrite ?u32s_length, ?u64s_length, ?upd_length, ?u16s_length, ?length_map in *.

Lemma u16s_split : forall ws i w, nth_error ws i = Some w ->
  exists pre post, ws = pre ++ w :: post /\ length pre = i /\
    u16s ws = u16s pre ++ le2 w ++ u16s post /\ length (u16s pre) = (2 * i)%nat.
Proof.
  intros ws i w H. destruct (nth_error_split _ _ _ H) as (pre & post & -> & Hlen).
  exists pre, post. rewrite u16s_app. cbn -[le2]. rewrite u16s_length. repeat split; lia.
Qed.

Section U16.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma u16ro_read : forall m A ws (i : Z) w a,
  bytes_at segs m A (u16s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> a = wa (A + 2 * i) ->
  ov_read_bytes segs m a 2 = Some (le2 w).
Proof.
  intros m A ws i w a Hb Hn Hi ->.
  destruct (u16s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (2 * i) with (Z.of_nat (2 * Z.to_nat i)) by lia.
  rewrite (bytes_at_ov_read segs m A (u16s ws) (2 * Z.to_nat i) 2 Hb).
  2:{ rewrite Eu, !length_app, length_le2, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le2; lia).
  rewrite length_le2, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Lemma u16arr_read : forall m A ws (i : Z) w a,
  u8arr segs m A (u16s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> a = wa (A + 2 * i) ->
  ov_read_bytes segs m a 2 = Some (le2 w).
Proof. intros m A ws i w a [Hb _]. apply u16ro_read. exact Hb. Qed.

Lemma u16arr_store_ok : forall m A ws (i : Z) a,
  u8arr segs m A (u16s ws) -> 0 <= i < Z.of_nat (length ws) -> a = wa (A + 2 * i) ->
  store_ok segs m a 2 = true.
Proof. intros m A ws i a [_ Hw] Hi ->. rewrite u16s_length in Hw. eapply wr_at_store_ok; eauto; lia. Qed.

Lemma u16arr_write : forall m A ws (i : Z) (v : word),
  u8arr segs m A (u16s ws) -> 0 <= i < Z.of_nat (length ws) ->
  u8arr segs (write_to_mem m (wa (A + 2 * i)) (le2 v)) A (u16s (upd ws (Z.to_nat i) v)).
Proof.
  intros m A ws i v [Hb Hw] Hi.
  destruct (upd_app_split ws (Z.to_nat i) v ltac:(lia)) as (pre & y & post & E & Hlen & Hupd).
  split.
  - eapply bytes_at_ext.
    { apply (bytes_at_write_inside segs m A (u16s ws) (2 * i) (le2 v) Hb); [lia|].
      rewrite length_le2, u16s_length. lia. }
    rewrite Hupd, E, !u16s_app. cbn [u16s].
    replace (Z.to_nat (2 * i)) with (length (u16s pre)) by (rewrite u16s_length; lia).
    apply upd_bytes_mid. rewrite !length_le2. reflexivity.
  - rewrite !u16s_length, upd_length in *. apply wr_at_write. exact Hw.
Qed.
End U16.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma byte_of_unsigned : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof.
  intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.
Lemma bytes_of_unsigned : forall bs : list byte, map (Z_to_bv 8) (map bv_unsigned bs) = bs.
Proof. induction bs as [|b bs IH]; cbn; [reflexivity|]. rewrite byte_of_unsigned, IH. reflexivity. Qed.
Lemma bytes_unsigned_range : forall bs : list byte, Forall (fun c => 0 <= c < 256) (map bv_unsigned bs).
Proof.
  induction bs as [|b bs IH]; cbn; constructor; [|exact IH].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.
Lemma byte_lit : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. intros c Hc. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

Lemma le2_of_pair : forall (b0 b1 : byte) c,
  - 32768 <= c < 32768 -> c mod 65536 = bv_unsigned b0 + 256 * bv_unsigned b1 ->
  le2 (Z_to_bv 64 c) = [b0; b1].
Proof.
  intros b0 b1 c Hc E.
  pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
  unfold bv_modulus in R0, R1. cbn in R0, R1.
  unfold le2. cbn [Z_to_le_bytes]. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  f_equal; [|f_equal].
  - rewrite <- (byte_of_unsigned b0). apply Z_to_bv8_mod. change (2^8) with 256. Z.div_mod_to_equations. lia.
  - rewrite <- (byte_of_unsigned b1). apply Z_to_bv8_mod. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    Z.div_mod_to_equations. lia.
Qed.

Lemma u16s_of_bytes : forall (n : nat) (bs : list byte), length bs = (2 * n)%nat ->
  exists ws : list Z, length ws = n /\ Forall (fun c => - 32768 <= c < 32768) ws /\ bs = u16s (map (Z_to_bv 64) ws).
Proof.
  induction n as [|n IH]; intros bs L.
  - destruct bs; [|cbn in L; lia]. exists []. repeat split; constructor.
  - destruct bs as [|b0 [|b1 bs]]; cbn in L; try lia.
    destruct (IH bs ltac:(lia)) as (ws & Lw & Fw & E).
    pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
    unfold bv_modulus in R0, R1. cbn in R0, R1.
    set (w := bv_unsigned b0 + 256 * bv_unsigned b1).
    exists ((if w <? 32768 then w else w - 65536) :: ws).
    split; [cbn; lia|]. split.
    + constructor; [|exact Fw]. destruct (Z.ltb_spec w 32768); subst w; lia.
    + cbn [map u16s]. rewrite <- E.
      rewrite (le2_of_pair b0 b1); [reflexivity| |].
      * destruct (Z.ltb_spec w 32768); subst w; lia.
      * destruct (Z.ltb_spec w 32768); subst w; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma swrap32_mod32 : forall z, (bv_swrap 32 z) mod 4294967296 = z mod 4294967296.
Proof. intros z. rewrite swrap32_eq. Z.div_mod_to_equations. lia. Qed.
Lemma swrap32_mod64_mod32 : forall z, ((bv_swrap 32 z) mod 18446744073709551616) mod 4294967296 = z mod 4294967296.
Proof. intros z. rewrite swrap32_eq. Z.div_mod_to_equations. lia. Qed.
Lemma mod64_mod32 : forall z, (z mod 18446744073709551616) mod 4294967296 = z mod 4294967296.
Proof. intros z. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma srliw_val : forall x k, 0 < k < 32 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 x) k) = (x mod 4294967296) / 2^k.
Proof.
  intros x k Hk. rewrite wrap32_eq, Z.shiftr_div_pow2 by lia.
  assert (P : 2 <= 2^k) by (change 2 with (2^1) at 1; apply Z.pow_le_mono_r; lia).
  pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)) as R.
  apply swrap32_small. split.
  - pose proof (Z.div_pos (x mod 4294967296) (2^k) ltac:(lia) ltac:(lia)). lia.
  - apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

(* [comment removed for export] *)
Lemma shiftl_mod32 : forall x k, 0 <= k < 32 -> Z.shiftl x (k mod 32) = x * 2^k.
Proof. intros x k Hk. rewrite Z.mod_small by lia. apply Z.shiftl_mul_pow2. lia. Qed.
Lemma sllw_pow2 : forall k, 0 <= k < 31 -> bv_swrap 32 (Z.shiftl 1 (k mod 32)) = 2^k.
Proof.
  intros k Hk. rewrite shiftl_mod32 by lia. rewrite Z.mul_1_l. apply swrap32_small.
  assert (0 < 2^k) by (apply Z.pow_pos_nonneg; lia).
  assert (2^k <= 2^30) by (apply Z.pow_le_mono_r; lia). change (2^30) with 1073741824 in *. lia.
Qed.
Lemma lor_pow2_1 : forall k, 1 <= k -> Z.lor (2^k) 1 = 2^k + 1.
Proof.
  intros k Hk.
  assert (P : 1 < 2^k) by (change 1 with (2^0) at 1; apply Z.pow_lt_mono_r; lia).
  rewrite Z.lor_comm. rewrite <- Z.lxor_lor by (apply zb_land_pow2_small; lia).
  rewrite zb_lxor_pow2_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma zext32_sh31 : forall x, 0 <= x < 4294967296 -> Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 31 = 2 * x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^32) with 4294967296. change (2^31) with 2147483648.
  rewrite Z.mod_small by lia. replace (x * 4294967296) with ((2 * x) * 2147483648) by lia. apply Z.div_mul. lia.
Qed.
Lemma zext32_sh32 : forall x, 0 <= x < 4294967296 -> Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 32 = x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^32) with 4294967296.
  rewrite Z.mod_small by lia. apply Z.div_mul. lia.
Qed.

(* [comment removed for export] *)
Lemma le1_lit : forall x, le1 (Z_to_bv 64 x) = [Z_to_bv 8 x].
Proof.
  intros x. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply Z_to_bv8_mod.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616. change (2^8) with 256.
  Z.div_mod_to_equations. lia.
Qed.
