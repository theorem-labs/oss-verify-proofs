From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c.
Import ListNotations.
Open Scope Z_scope.

Lemma ble_range : forall bs, 0 <= bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
  intros bs. rewrite bytes_le_to_Z_le_val.
  pose proof (le_val_range _ (bytes_ok_map bs)) as H. rewrite map_length in H.
  rewrite Z.pow_mul_r by lia. exact H.
Qed.

Lemma lw_val : forall bs, length bs = 4%nat ->
  sext 64 (bv_extract 0 32 (le_bytes_to_word bs)) = Z_to_bv 64 (bv_swrap 32 (bytes_le_to_Z bs)).
Proof.
  intros bs L. rewrite sext_small. f_equal. rewrite signed_of_extract by lia.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. f_equal.
  pose proof (ble_range bs) as H. rewrite L in H. apply bv_wrap_small. unfold bv_modulus. cbn in H. lia.
Qed.

Lemma lbu_val : forall bs, length bs = 1%nat ->
  zext 64 (bv_extract 0 8 (le_bytes_to_word bs)) = Z_to_bv 64 (bytes_le_to_Z bs).
Proof.
  intros bs L. rewrite zext_small. f_equal. rewrite extract_low_mod by lia.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned.
  pose proof (ble_range bs) as H. rewrite L in H. cbn in H.
  rewrite bv_wrap_small by (unfold bv_modulus; lia). apply Z.mod_small. cbn. lia.
Qed.

Lemma length_sub : forall bs k n, 0 <= k -> k + Z.of_nat n <= Z.of_nat (length bs) -> length (sub bs k n) = n.
Proof. intros bs k n Hk H. unfold sub. rewrite firstn_length, skipn_length. lia. Qed.

Lemma rd_sub : forall m a bs k n, bytes_at rsegs m a bs -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a + k)) n = Some (sub bs k n).
Proof. intros m a bs k n H Hk Hn. apply (bytes_at_read rsegs m a bs k n H Hk). lia. Qed.
Lemma nth_firstn : forall {X} n (l : list X) i, (i < n)%nat -> nth_error (firstn n l) i = nth_error l i.
Proof.
  intros X n. induction n as [|n IH]; intros l i Hi; [lia|].
  destruct l as [|x l]; [reflexivity|]. destruct i as [|i]; [reflexivity|]. cbn. apply IH. lia.
Qed.

Lemma nth_skipn : forall {X} n (l : list X) i, nth_error (skipn n l) i = nth_error l (n + i).
Proof.
  intros X n. induction n as [|n IH]; intros l i; [reflexivity|].
  destruct l as [|x l]; [destruct i; reflexivity|]. cbn. apply IH.
Qed.


Lemma bytes_at_sub : forall m a bs k n, bytes_at rsegs m a bs -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length bs) ->
  bytes_at rsegs m (a + k) (sub bs k n).
Proof.
  intros m a bs k n (Ha & Hl & H) Hk Hn. unfold sub.
  assert (Ln : length (firstn n (skipn (Z.to_nat k) bs)) = n) by (rewrite firstn_length, skipn_length; lia).
  split; [lia|]. split; [rewrite Ln; lia|].
  intros i Hi. rewrite Ln in Hi.
  rewrite nth_firstn by lia. rewrite nth_skipn.
  replace (a + k + Z.of_nat i) with (a + Z.of_nat (Z.to_nat k + i)) by lia.
  apply H. lia.
Qed.

Lemma memcmp_model_eq : forall n l r v, length l = n -> length r = n -> memcmp_model l r n = Some v ->
  (v = 0 <-> l = r) /\ -256 < v < 256.
Proof.
  induction n as [|n IH]; intros l r v Hl Hr Hm.
  - destruct l; [|discriminate]. destruct r; [|discriminate]. cbn in Hm. inversion Hm. split; [tauto|lia].
  - destruct l as [|a l]; [discriminate|]. destruct r as [|b r]; [discriminate|].
    cbn in Hl, Hr, Hm. pose proof (bv_unsigned_in_range 8 a) as Ra. pose proof (bv_unsigned_in_range 8 b) as Rb.
    unfold bv_modulus in Ra, Rb. change (2 ^ Z.of_N 8) with 256 in Ra, Rb.
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
    + destruct (IH l r v ltac:(lia) ltac:(lia) Hm) as [[I1 I2] I3]. split; [|exact I3].
      assert (a = b) by (apply bv_eq; exact E). subst b. split.
      * intros ->. f_equal. tauto.
      * intros Q. inversion Q. tauto.
    + inversion Hm. subst v. split; [|lia]. split.
      * intros. lia.
      * intros Q. inversion Q. subst. lia.
Qed.

Lemma memcmp6 : forall l r, length l = 6%nat -> length r = 6%nat ->
  exists v, memcmp_model l r 6 = Some v /\ (v = 0 <-> l = r) /\ -256 < v < 256.
Proof.
  intros l r Hl Hr. destruct (memcmp_model_total l r 6 ltac:(lia) ltac:(lia)) as [v Hv].
  exists v. split; [exact Hv|]. apply (memcmp_model_eq 6); assumption.
Qed.

Lemma eqb_small : forall v, -256 < v < 256 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  destruct (Z.eqb_spec v 0) as [->|N]; [reflexivity|].
  apply Z.eqb_neq. intros E. apply Z.mod_divide in E; [|lia]. destruct E as [c Ec]. nia.
Qed.

Lemma signed_lit : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, unsigned_lit_wrap.
  destruct (Z.ltb_spec 0 (z + 1)).
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec z (2^63)); lia.
  - replace (z mod 2^64) with (z + 2^64).
    + destruct (Z.ltb_spec (z + 2^64) (2^63)); lia.
    + symmetry. rewrite <- (Z.mod_add z 1 (2^64)) by lia. apply Z.mod_small. lia.
Qed.

Lemma lts_lit : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 ->
  bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_lts. rewrite !signed_lit by assumption. reflexivity. Qed.

Lemma ltu_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by assumption. reflexivity. Qed.

Lemma eqb_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit by assumption. reflexivity. Qed.

Lemma swrap32_small : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia. Qed.

Lemma s32_range : forall bs k, -2^31 <= s32_at bs k < 2^31.
Proof.
  intros bs k. unfold s32_at, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31).
  change (bv_modulus 32) with (2^32).
  pose proof (Z.mod_pos_bound (u_at bs k 4 + 2^31) (2^32) ltac:(lia)). lia.
Qed.

Lemma addiw_small : forall z c, 0 <= z < 2^64 -> -2^31 <= z + c < 2^31 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 z) + c)) = Z_to_bv 64 (z + c).
Proof. intros z c Hz Hc. rewrite unsigned_lit by lia. rewrite swrap32_small by lia. reflexivity. Qed.

Lemma shl32_shr32 : forall n, 0 <= n < 2^32 ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 n)) 32))) 32 = n.
Proof.
  intros n Hn. rewrite (unsigned_lit n) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_mul. lia.
Qed.

Lemma shl_lit : forall i k, 0 <= i -> 0 <= k -> i * 2^k < 2^64 ->
  bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 i)) k)) = i * 2^k.
Proof.
  intros i k Hi Hk H. rewrite (unsigned_lit i) by lia. rewrite Z.shiftl_mul_pow2 by lia. apply unsigned_lit. lia.
Qed.

Lemma mul48_lit : forall i, 0 <= i < 2^32 ->
  bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 i)) 6)) -
  bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 i)) 4)) = 48 * i.
Proof. intros i Hi. rewrite !shl_lit by lia. change (2^6) with 64. change (2^4) with 16. lia. Qed.

Lemma land7_lit : forall t, 0 <= t < 2^64 -> t mod 8 = 0 -> Z.land (bv_unsigned (Z_to_bv 64 t)) 7 = 0.
Proof.
  intros t Ht H8. rewrite unsigned_lit by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H8.
Qed.

Lemma land3_lit : forall t, 0 <= t < 2^64 -> t mod 4 = 0 -> Z.land (bv_unsigned (Z_to_bv 64 t)) 3 = 0.
Proof.
  intros t Ht H4. rewrite unsigned_lit by lia. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. exact H4.
Qed.

Lemma not_lit : forall t, 0 <= t < 2^64 ->
  Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 t)) 18446744073709551615) = Z_to_bv 64 (2^64 - 1 - t).
Proof. intros t Ht. rewrite unsigned_lit by lia. rewrite zb_lxor_ones by lia. f_equal. Qed.

Lemma sgtz_and_lit : forall n, 0 < n < 2^63 ->
  Z.land (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (v_slt (Z_to_bv 64 0) (Z_to_bv 64 n)))))
         (bv_unsigned (Z_to_bv 64 n)) = n.
Proof.
  intros n Hn. rewrite v_slt_b2z.
  rewrite (unsigned_lit 0) by lia. rewrite (unsigned_lit n) by lia.
  replace (Z.lxor 0 (2^63) <? Z.lxor n (2^63)) with true.
  2:{ symmetry. apply Z.ltb_lt. rewrite Z.lxor_0_l. rewrite zb_lxor_pow2_small by lia. lia. }
  cbn [Z.b2z]. rewrite (unsigned_lit 1) by lia. rewrite unsigned_lit_wrap.
  change ((0 - 1) mod 2^64) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
