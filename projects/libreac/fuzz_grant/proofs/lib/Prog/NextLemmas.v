From Stdlib Require Import ZArith List Lia Bool Znumtheory.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge Step.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantModel NextModel.
Import ListNotations.
Open Scope Z_scope.

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. exact H. Qed.

Lemma tb_range : forall T k, 0 <= tb T k < 256.
Proof. intros. unfold tb. apply byte_range. Qed.

Lemma u32_range : forall T k, 0 <= u32 T k < 4294967296.
Proof.
  intros. unfold u32.
  pose proof (tb_range T k). pose proof (tb_range T (k + 1)).
  pose proof (tb_range T (k + 2)). pose proof (tb_range T (k + 3)). lia.
Qed.

Lemma s32_range : forall T k, -2147483648 <= s32 T k < 2147483648.
Proof. intros. unfold s32. pose proof (u32_range T k). destruct (Z.ltb_spec (u32 T k) 2147483648); lia. Qed.

Lemma Z_to_bv8_self : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof.
  intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma nth_as_error : forall (l : list byte) i d, nth i l d = match nth_error l i with Some x => x | None => d end.
Proof. induction l as [|x l IH]; intros [|i] d; cbn; auto. Qed.

Lemma firstn_skipn_cons : forall (T : list byte) k n d, (k < length T)%nat ->
  firstn (S n) (skipn k T) = nth k T d :: firstn n (skipn (S k) T).
Proof.
  induction T as [|x T IH]; intros k n d H; cbn in H; [lia|].
  destruct k as [|k]; cbn; [reflexivity|]. apply IH. lia.
Qed.

Lemma rd1 : forall m t Tc k, bytes_at rsegs m t Tc -> length Tc = 460%nat -> 0 <= k < 460 ->
  ov_read_bytes rsegs m (wa (t + k)) 1 = Some [Z_to_bv 8 (tb Tc k)].
Proof.
  intros m t Tc k HB HL Hk. rewrite (bytes_at_read rsegs m t Tc k 1 HB) by lia.
  rewrite (firstn1_skipn_nth Tc _ (Z_to_bv 8 0)) by lia. unfold tb. rewrite Z_to_bv8_self. reflexivity.
Qed.

Lemma le4_bytes : forall u, 0 <= u < 4294967296 ->
  le4 (Z_to_bv 64 u) = [Z_to_bv 8 (u mod 256); Z_to_bv 8 ((u / 256) mod 256);
                        Z_to_bv 8 ((u / 65536) mod 256); Z_to_bv 8 (u / 16777216)].
Proof.
  intros u Hu. unfold le4. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  rewrite (Z.mod_small u) by (change (2 ^ Z.of_N 64) with 18446744073709551616; lia).
  cbn [Z_to_le_bytes]. rewrite !Z.shiftr_div_pow2 by lia. rewrite !Z.div_div by lia.
  change (2 ^ 8) with 256. change (256 * 256) with 65536. change (65536 * 256) with 16777216.
  f_equal; [apply Z_to_bv8_mod; rewrite Z.mod_mod by lia; reflexivity|].
  f_equal; [apply Z_to_bv8_mod; rewrite Z.mod_mod by lia; reflexivity|].
  f_equal. apply Z_to_bv8_mod; rewrite Z.mod_mod by lia; reflexivity.
Qed.

Lemma Z_to_bv8_tb : forall T k, Z_to_bv 8 (tb T k) = nth (Z.to_nat k) T (Z_to_bv 8 0).
Proof. intros. unfold tb. apply Z_to_bv8_self. Qed.

Lemma rd4 : forall m t Tc k, bytes_at rsegs m t Tc -> length Tc = 460%nat -> 0 <= k -> k + 4 <= 460 ->
  ov_read_bytes rsegs m (wa (t + k)) 4 = Some (le4 (Z_to_bv 64 (u32 Tc k))).
Proof.
  intros m t Tc k HB HL Hk Hk4. rewrite (bytes_at_read rsegs m t Tc k 4 HB) by lia. f_equal.
  rewrite le4_bytes by apply u32_range.
  rewrite (firstn_skipn_cons Tc _ 3 (Z_to_bv 8 0)) by lia.
  rewrite (firstn_skipn_cons Tc _ 2 (Z_to_bv 8 0)) by lia.
  rewrite (firstn_skipn_cons Tc _ 1 (Z_to_bv 8 0)) by lia.
  rewrite (firstn1_skipn_nth Tc _ (Z_to_bv 8 0)) by lia.
  pose proof (tb_range Tc k). pose proof (tb_range Tc (k + 1)).
  pose proof (tb_range Tc (k + 2)). pose proof (tb_range Tc (k + 3)).
  replace (S (Z.to_nat k)) with (Z.to_nat (k + 1)) by lia.
  replace (S (Z.to_nat (k + 1))) with (Z.to_nat (k + 2)) by lia.
  replace (S (Z.to_nat (k + 2))) with (Z.to_nat (k + 3)) by lia.
  rewrite <- !Z_to_bv8_tb. unfold u32.
  f_equal; [f_equal; Z.div_mod_to_equations; lia|].
  f_equal; [f_equal; Z.div_mod_to_equations; lia|].
  f_equal; [f_equal; Z.div_mod_to_equations; lia|].
  f_equal. f_equal. Z.div_mod_to_equations; lia.
Qed.

Lemma sx32_lit : forall u, 0 <= u < 2^32 -> sx32 (Z_to_bv 64 u) = Z_to_bv 64 (if u <? 2^31 then u else u - 2^32).
Proof.
  intros u Hu. unfold sx32. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  rewrite (Z.mod_small u) by (change (2 ^ Z.of_N 64) with 18446744073709551616; lia).
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
  change (4294967296 `div` 2) with 2147483648.
  destruct (Z.ltb_spec u (2^31)).
  - rewrite Z.mod_small by lia. lia.
  - rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma sx32_u32 : forall T k, sx32 (Z_to_bv 64 (u32 T k)) = Z_to_bv 64 (s32 T k).
Proof. intros. rewrite sx32_lit by (pose proof (u32_range T k); lia). reflexivity. Qed.


Lemma land255 : forall x, 0 <= x < 256 -> Z.land x 255 = x.
Proof. intros x Hx. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. change (2^8) with 256. lia. Qed.

Lemma div3_171 : forall i, 0 <= i < 144 -> ((Z.land i 255 * 171) mod 18446744073709551616) / 512 = i / 3.
Proof. intros i Hi. rewrite land255 by lia. rewrite Z.mod_small by lia. Z.div_mod_to_equations. lia. Qed.

Lemma div3_hi : forall j, 0 <= j < 1048576 -> (j * 1431655766) / 4294967296 = j / 3.
Proof. intros j Hj. Z.div_mod_to_equations. lia. Qed.

Lemma div3_sign : forall j, 0 <= j < 1048576 -> (j * 1431655766) / 9223372036854775808 = 0.
Proof. intros j Hj. apply Z.div_small. lia. Qed.

Lemma tb_upd_out : forall T k bs i, (k + length bs <= length T)%nat -> 0 <= i < Z.of_nat (length T) ->
  (i < Z.of_nat k \/ Z.of_nat (k + length bs) <= i) -> tb (upd_bytes T k bs) i = tb T i.
Proof.
  intros T k bs i Hk Hi Hout. unfold tb. rewrite !nth_as_error.
  rewrite upd_bytes_nth by lia.
  destruct (Nat.leb_spec k (Z.to_nat i)); destruct (Nat.ltb_spec (Z.to_nat i) (k + length bs)); cbn [andb];
    try reflexivity; lia.
Qed.

Lemma tb_setb_out : forall T k v i, length T = 460%nat -> 0 <= k < 460 -> 0 <= i < 460 -> i <> k ->
  tb (setb T k v) i = tb T i.
Proof. intros. unfold setb. apply tb_upd_out; rewrite ?length_le1; lia. Qed.

Lemma tb_set4_out : forall T k v i, length T = 460%nat -> 0 <= k -> k + 4 <= 460 -> 0 <= i < 460 ->
  (i < k \/ k + 4 <= i) -> tb (set4 T k v) i = tb T i.
Proof. intros. unfold set4. apply tb_upd_out; rewrite ?length_le4; lia. Qed.

Lemma len_setb : forall T k v, length T = 460%nat -> 0 <= k < 460 -> length (setb T k v) = 460%nat.
Proof. intros. unfold setb. rewrite upd_bytes_length; rewrite ?length_le1; lia. Qed.

Lemma len_set4 : forall T k v, length T = 460%nat -> 0 <= k -> k + 4 <= 460 -> length (set4 T k v) = 460%nat.
Proof. intros. unfold set4. rewrite upd_bytes_length; rewrite ?length_le4; lia. Qed.

Lemma tb_set4_in : forall T k v j, length T = 460%nat -> 0 <= k -> k + 4 <= 460 -> 0 <= v < 4294967296 -> 0 <= j < 4 ->
  tb (set4 T k v) (k + j) = nth (Z.to_nat j) [v mod 256; (v / 256) mod 256; (v / 65536) mod 256; v / 16777216] 0.
Proof.
  intros T k v j HL Hk Hk4 Hv Hj. unfold tb, set4. rewrite nth_as_error. rewrite upd_bytes_nth by (rewrite ?length_le4; lia).
  rewrite length_le4.
  replace (Nat.leb (Z.to_nat k) (Z.to_nat (k + j)) && Nat.ltb (Z.to_nat (k + j)) (Z.to_nat k + 4))%bool with true
    by (symmetry; apply andb_true_iff; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia).
  replace (Z.to_nat (k + j) - Z.to_nat k)%nat with (Z.to_nat j) by lia.
  rewrite le4_bytes by lia.
  assert (j = 0 \/ j = 1 \/ j = 2 \/ j = 3) as [-> | [-> | [-> | ->]]] by lia; simpl;
    rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 8) with 256;
    first [ apply Z.mod_mod; lia | apply Z.mod_small; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia ].
Qed.

Lemma u32_set4 : forall T k v, length T = 460%nat -> 0 <= k -> k + 4 <= 460 -> 0 <= v < 4294967296 ->
  u32 (set4 T k v) k = v.
Proof.
  intros T k v HL Hk Hk4 Hv. unfold u32.
  rewrite (tb_set4_in T k v 1), (tb_set4_in T k v 2), (tb_set4_in T k v 3) by lia.
  replace (tb (set4 T k v) k) with (tb (set4 T k v) (k + 0)) by (f_equal; lia).
  rewrite (tb_set4_in T k v 0) by lia. simpl.
  Z.div_mod_to_equations. lia.
Qed.

Lemma s32_set4 : forall T k v, length T = 460%nat -> 0 <= k -> k + 4 <= 460 -> 0 <= v < 2147483648 ->
  s32 (set4 T k v) k = v.
Proof. intros. unfold s32. rewrite u32_set4 by lia. rewrite (proj2 (Z.ltb_lt v 2147483648)) by lia. reflexivity. Qed.

Lemma bytes_at_struct : forall m c cs (k : Z) bs,
  bytes_at rsegs m c cs -> length cs = 460%nat -> 0 <= k -> k + Z.of_nat (length bs) <= 460 ->
  bytes_at rsegs (write_to_mem m (wa (c + k)) bs) c (upd_bytes cs (Z.to_nat k) bs).
Proof. intros. apply bytes_at_write_inside; [assumption | assumption | rewrite H0; lia]. Qed.

Lemma fd_step : forall T i n, first_dirty_from T i (S n) =
  if tb T (288 + i) =? 0 then first_dirty_from T (i + 1) n else Some i.
Proof. reflexivity. Qed.

Lemma walk_step : forall T t bs o total j n, walk T t bs o total j (S n) =
  let T1 := set4 T 440 (j + 1) in
  if carried T1 bs o j then emit_res T1 t (bs + j / 3) (j mod 3) j total
  else if j + 1 =? total then resweep (setb T1 437 0)
  else walk T1 t bs o total (j + 1) n.
Proof. reflexivity. Qed.

Lemma ub8_tb : forall T k, bv_unsigned (Z_to_bv 8 (tb T k)) = tb T k.
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap_small. pose proof (tb_range T k). unfold bv_modulus. lia. Qed.

Lemma s32_mod32 : forall T k, s32 T k mod 4294967296 = u32 T k.
Proof.
  intros. unfold s32. pose proof (u32_range T k). destruct (Z.ltb_spec (u32 T k) 2147483648).
  - apply Z.mod_small. lia.
  - rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma s32_zero : forall T k, s32 T k = 0 <-> u32 T k = 0.
Proof. intros. unfold s32. pose proof (u32_range T k). destruct (Z.ltb_spec (u32 T k) 2147483648); lia. Qed.

Lemma swrap32_range : forall z, -2147483648 <= bv_swrap 32 z < 2147483648.
Proof.
  intros. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with 4294967296. change (bv_half_modulus 32) with 2147483648.
  pose proof (Z.mod_pos_bound (z + 2147483648) 4294967296). lia.
Qed.

Lemma swrap32_mod32 : forall z, bv_swrap 32 z mod 4294967296 = z mod 4294967296.
Proof.
  intros. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with 4294967296. change (bv_half_modulus 32) with 2147483648.
  rewrite Zminus_mod, Z.mod_mod by lia. rewrite <- Zminus_mod.
  replace (z + 2147483648 - 2147483648) with z by lia. reflexivity.
Qed.

Lemma cmp32 : forall x y, -2147483648 <= x < 2147483648 -> -2147483648 <= y < 2147483648 ->
  (x mod 18446744073709551616 < y mod 18446744073709551616 <-> x mod 4294967296 < y mod 4294967296).
Proof. intros x y Hx Hy. Z.div_mod_to_equations. lia. Qed.

Lemma le4_eqm : forall a b, a mod 4294967296 = b mod 4294967296 -> le4 (Z_to_bv 64 a) = le4 (Z_to_bv 64 b).
Proof.
  intros a b H. unfold le4. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite <- (Z_to_le_bytes_mod 4 (a mod 18446744073709551616) 32) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 4 (b mod 18446744073709551616) 32) by (cbn; lia).
  change (2 ^ 32) with 4294967296.
  rewrite !mod64_mod32. rewrite H. reflexivity.
Qed.

Lemma le1_eqm : forall a b, a mod 256 = b mod 256 -> le1 (Z_to_bv 64 a) = le1 (Z_to_bv 64 b).
Proof.
  intros a b H. unfold le1. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite <- (Z_to_le_bytes_mod 1 (a mod 18446744073709551616) 8) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 1 (b mod 18446744073709551616) 8) by (cbn; lia).
  change (2 ^ 8) with 256.
  assert (Ea : (a mod 18446744073709551616) mod 256 = a mod 256)
    by (symmetry; apply Zmod_div_mod; [lia|lia|]; exists 72057594037927936; reflexivity).
  assert (Eb : (b mod 18446744073709551616) mod 256 = b mod 256)
    by (symmetry; apply Zmod_div_mod; [lia|lia|]; exists 72057594037927936; reflexivity).
  rewrite Ea, Eb, H. reflexivity.
Qed.

Lemma s32p1 : forall T k, (s32 T k + 1) mod 4294967296 = (u32 T k + 1) mod 4294967296.
Proof.
  intros. rewrite (Zplus_mod (s32 T k)). rewrite s32_mod32. rewrite (Zplus_mod (u32 T k)).
  rewrite (Z.mod_small (u32 T k)) by apply u32_range. reflexivity.
Qed.

Lemma land_mod256 : forall c, Z.land c 255 = c mod 256.
Proof. intros. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma land_mod64 : forall c, Z.land c 63 = c mod 64.
Proof. intros. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma dflt_range : forall p, 0 <= dflt p < 256.
Proof. intros. unfold dflt. destruct (p =? 2); lia. Qed.
