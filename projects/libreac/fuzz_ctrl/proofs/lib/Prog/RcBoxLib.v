From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox.
Import ListNotations.
Open Scope Z_scope.

Lemma rc_zxb_eqb0 : forall b : byte, bv_eqb (zxb b) (Z_to_bv 64 0) = (bv_unsigned b =? 0).
Proof. intros b. unfold zxb. pose proof (byte_range b). apply rc_eqb0. lia. Qed.

Lemma rc_eqb_lit : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma rc_ltu_lit : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma rd_le8 : forall segs m A v, bytes_at segs m A (le8 v) -> ov_read_bytes segs m (wa A) 8 = Some (le8 v).
Proof.
  intros segs m A v H. rewrite <- (Z.add_0_r A) at 1.
  rewrite (bytes_at_read segs m A (le8 v) 0 8 H) by (rewrite ?length_le8; lia).
  all: try (change (Z.to_nat 0) with 0%nat; cbn [skipn]; f_equal; apply firstn_all2; pose proof (length_le8 v) as L; lia).
Qed.

Lemma firstn_S_snoc : forall (l : list byte) i d, (i < length l)%nat -> firstn (S i) l = firstn i l ++ [nth i l d].
Proof.
  induction l as [|x l IH]; intros i d H; cbn [length] in H; [lia|].
  destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. rewrite (IH i d) by lia. reflexivity.
Qed.

Lemma takenz_stop : forall nb i, (i < length nb)%nat ->
  (forall j, (j < i)%nat -> bv_unsigned (nth j nb (Z_to_bv 8 0)) <> 0) ->
  bv_unsigned (nth i nb (Z_to_bv 8 0)) = 0 -> takenz nb = firstn i nb.
Proof.
  induction nb as [|b nb IH]; intros i Hi Hnz H0; cbn [length] in Hi; [lia|].
  destruct i as [|i].
  - cbn [nth] in H0. cbn [takenz firstn]. rewrite H0. reflexivity.
  - pose proof (Hnz 0%nat ltac:(lia)) as H. cbn [nth] in H.
    cbn [takenz firstn]. destruct (Z.eqb_spec (bv_unsigned b) 0) as [E|E]; [contradiction|].
    f_equal. apply IH; [lia | intros j Hj; apply (Hnz (S j)); lia | exact H0].
Qed.

Lemma takenz_all : forall nb, (forall j, (j < length nb)%nat -> bv_unsigned (nth j nb (Z_to_bv 8 0)) <> 0) ->
  takenz nb = nb.
Proof.
  induction nb as [|b nb IH]; intros Hnz; [reflexivity|].
  pose proof (Hnz 0%nat ltac:(cbn; lia)) as H. cbn [nth] in H.
  cbn [takenz]. destruct (Z.eqb_spec (bv_unsigned b) 0) as [E|E]; [contradiction|].
  f_equal. apply IH. intros j Hj. apply (Hnz (S j)). cbn. lia.
Qed.

Lemma nmf_stop : forall nb i, (i < length nb)%nat -> (i <= 16)%nat ->
  (forall j, (j < i)%nat -> bv_unsigned (nth j nb (Z_to_bv 8 0)) <> 0) ->
  bv_unsigned (nth i nb (Z_to_bv 8 0)) = 0 ->
  nmf nb = firstn i nb ++ repeat (Z_to_bv 8 0) (16 - i).
Proof.
  intros nb i Hi H16 Hnz H0. unfold nmf. rewrite (takenz_stop nb i Hi Hnz H0).
  rewrite firstn_length. replace (Nat.min i (length nb)) with i by lia. reflexivity.
Qed.

Lemma nmf_full : forall nb, length nb = 16%nat ->
  (forall j, (j < 16)%nat -> bv_unsigned (nth j nb (Z_to_bv 8 0)) <> 0) ->
  nmf nb = firstn 16 nb ++ repeat (Z_to_bv 8 0) (16 - 16).
Proof.
  intros nb L Hnz. unfold nmf. rewrite takenz_all by (intros j Hj; apply Hnz; lia).
  rewrite L, firstn_all2 by lia. reflexivity.
Qed.

Lemma nmf_nil : nmf [] = repeat (Z_to_bv 8 0) 16.
Proof. reflexivity. Qed.

Lemma name_ok_lt : forall nb i, name_ok nb -> (i < 16)%nat ->
  (forall j, (j < i)%nat -> bv_unsigned (nth j nb (Z_to_bv 8 0)) <> 0) -> (i < length nb)%nat.
Proof.
  intros nb i (L & Hnz & Hend) Hi Hall. destruct (Nat.lt_ge_cases i (length nb)) as [H|H]; [exact H|].
  exfalso. destruct Hend as [E|E]; [lia|]. apply (Hall (pred (length nb))); [lia | exact E].
Qed.

Lemma upd_prefix : forall nb i, (i < length nb)%nat -> (i < 16)%nat ->
  upd_bytes (firstn i nb ++ repeat (Z_to_bv 8 0) (16 - i)) i [nth i nb (Z_to_bv 8 0)] =
  firstn (S i) nb ++ repeat (Z_to_bv 8 0) (16 - S i).
Proof.
  intros nb i Hi H16. unfold upd_bytes.
  assert (L : length (firstn i nb) = i) by (rewrite firstn_length; lia).
  rewrite firstn_app, L, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 by lia.
  rewrite skipn_app, L, skipn_all2 by (cbn [length]; lia). cbn [length app].
  replace (i + 1 - i)%nat with 1%nat by lia.
  replace (16 - i)%nat with (S (16 - S i)) by lia. cbn [repeat skipn].
  rewrite (firstn_S_snoc nb i (Z_to_bv 8 0) Hi). rewrite <- app_assoc. reflexivity.
Qed.

Lemma bytes_at_sub : forall segs m A bs k j, bytes_at segs m A bs -> (k + j <= length bs)%nat ->
  bytes_at segs m (A + Z.of_nat k) (firstn j (skipn k bs)).
Proof.
  intros segs m A bs k j (HA & HL & H) Hkj.
  assert (Lf : length (firstn j (skipn k bs)) = j) by (rewrite firstn_length, skipn_length; lia).
  split; [lia|]. split; [rewrite Lf; lia|].
  intros i Hi. rewrite Lf in Hi.
  replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia.
  rewrite H by lia. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i j) as [_|C]; [|lia].
  rewrite nth_error_skipn. reflexivity.
Qed.

Lemma bytes_at_cat : forall segs m a b bs1 bs2, bytes_at segs m a bs1 -> bytes_at segs m b bs2 ->
  b = a + Z.of_nat (length bs1) -> bytes_at segs m a (bs1 ++ bs2).
Proof. intros segs m a b bs1 bs2 H1 H2 E. subst b. apply bytes_at_app. split; assumption. Qed.

Lemma bytes_at_addr : forall segs m a b bs, bytes_at segs m a bs -> a = b -> bytes_at segs m b bs.
Proof. intros; subst; assumption. Qed.

Lemma wr_at_sub : forall segs m A n k j, wr_at segs m A n -> 0 <= k -> 0 <= j -> k + j <= n -> wr_at segs m (A + k) j.
Proof.
  intros segs m A n k j (HA & Hn & H) Hk Hj Hkj. split; [lia|]. split; [lia|].
  intros i Hi. replace (A + k + i) with (A + (k + i)) by lia. apply H. lia.
Qed.

Lemma wr_at_prefix : forall segs m A n j, wr_at segs m A n -> 0 <= j <= n -> wr_at segs m A j.
Proof. intros segs m A n j (HA & Hn & H) Hj. split; [lia|]. split; [lia|]. intros i Hi. apply H. lia. Qed.

Lemma bytes_at_skip16 : forall segs m A (H D : list byte), length H = 20%nat ->
  bytes_at segs m A (H ++ D) -> bytes_at segs m (A + 16) (skipn 16 H ++ D).
Proof.
  intros segs m A H D LH HB.
  pose proof (bytes_at_sub segs m A (H ++ D) 16 (4 + length D) HB ltac:(rewrite length_app; lia)) as S.
  rewrite skipn_app, LH in S. change (16 - 20)%nat with 0%nat in S. rewrite skipn_O in S.
  rewrite firstn_all2 in S by (rewrite length_app, length_skipn; lia).
  exact S.
Qed.

Lemma rc_eqb_w : forall (x : word) X y, bv_unsigned x = X -> 0 <= y < 2^64 -> bv_eqb x (Z_to_bv 64 y) = (X =? y).
Proof. intros x X y H Hy. unfold bv_eqb. rewrite H, unsigned_lit by lia. reflexivity. Qed.

Lemma rc_eqb_w2 : forall (x y : word) X Y, bv_unsigned x = X -> bv_unsigned y = Y -> bv_eqb x y = (X =? Y).
Proof. intros x y X Y Hx Hy. unfold bv_eqb. rewrite Hx, Hy. reflexivity. Qed.

Lemma rc_wa_add0 : forall x : word, x = wa (bv_unsigned x + Z.of_nat 0).
Proof. intros x. unfold wa. cbn [Z.of_nat]. rewrite Z.add_0_r. symmetry. apply Z_to_bv_lit_self. Qed.

Lemma rc_zext32 : forall x : word, bv_unsigned x < 2^32 ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned x) 32))) 32) = x.
Proof.
  intros x Hx. pose proof (zr_word x) as R. unfold inr64 in R.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit by lia.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. apply Z_to_bv_lit_self.
Qed.

Lemma rc_cons_eq : forall (x y : byte) xs ys, x = y -> xs = ys -> x :: xs = y :: ys.
Proof. intros; subst; reflexivity. Qed.

Lemma rc_le1_lit : forall z, le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z. unfold le1. rewrite unsigned_lit_wrap. cbn [Z_to_le_bytes]. f_equal.
  apply Z_to_bv8_mod. apply mod_mod8_of_modw. lia.
Qed.

Lemma rc_swrap32_mod256 : forall x, bv_swrap 32 x mod 256 = x mod 256.
Proof.
  intros x. unfold bv_swrap. change (bv_half_modulus 32) with 2147483648.
  unfold bv_wrap. change (bv_modulus 32) with 4294967296.
  Z.div_mod_to_equations. lia.
Qed.

Lemma rc_le1_negw : forall s,
  le1 (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64 s)))) = [Z_to_bv 8 ((- s) mod 256)].
Proof.
  intros s. rewrite rc_le1_lit. f_equal. apply Z_to_bv8_mod. change (2^8) with 256.
  rewrite rc_swrap32_mod256, Z.mod_mod by lia. rewrite unsigned_lit_wrap.
  change (2^64) with 18446744073709551616. Z.div_mod_to_equations. lia.
Qed.

Lemma rc_swrap_small : forall x, 0 <= x < 2^31 -> bv_swrap 32 x = x.
Proof. intros x Hx. apply bv_swrap_small. change (bv_half_modulus 32) with 2147483648. lia. Qed.

Lemma psum_snoc : forall L x R, psum (L ++ x :: R) (S (length L)) = psum L (length L) + bv_unsigned x.
Proof.
  intros L x R. cbn [psum]. rewrite psum_app_l by lia. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma rc_byte_lit : forall v, 0 <= v < 256 -> bv_unsigned (Z_to_bv 8 v) = v.
Proof. intros v Hv. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hv. Qed.

Lemma dt1_hdr_length : forall n a, length (dt1_hdr n a) = 20%nat.
Proof. reflexivity. Qed.

Lemma dt1_s4_length : forall n a, length (skipn 16 (dt1_hdr n a)) = 4%nat.
Proof. reflexivity. Qed.

Lemma dt1_body_length : forall n a D ob, length D = n -> length ob = 32%nat -> (n <= 9)%nat ->
  length (dt1_body n a D ob) = 31%nat.
Proof.
  intros n a D ob LD Lob Hn. unfold dt1_body. rewrite !length_app, dt1_hdr_length, LD. cbn [length].
  rewrite firstn_length, skipn_length. lia.
Qed.

Lemma psum_skip_mid : forall (H D R : list byte) x, length H = 20%nat ->
  psum (skipn 16 (H ++ D ++ x :: R)) (length D + 5) = psum (skipn 16 H ++ D) (length D + 4) + bv_unsigned x.
Proof.
  intros H D R x LH. rewrite skipn_app, LH. change (16 - 20)%nat with 0%nat. rewrite skipn_O.
  rewrite app_assoc.
  assert (L4 : length (skipn 16 H) = 4%nat) by (rewrite skipn_length; lia).
  replace (length D + 5)%nat with (S (length (skipn 16 H ++ D))) by (rewrite length_app; lia).
  rewrite psum_snoc. rewrite length_app, L4.
  replace (4 + length D)%nat with (length D + 4)%nat by lia. reflexivity.
Qed.

Lemma dt1_so128 : forall n a D ob, length D = n ->
  psum (skipn 16 (dt1_out n a D ob)) (n + 5) mod 128 = 0.
Proof.
  intros n a D ob LD. subst n. unfold dt1_out, dt1_body. rewrite <- !app_assoc. cbn [app].
  rewrite psum_skip_mid by apply dt1_hdr_length.
  unfold dt1_ick.
  pose proof (Z.mod_pos_bound (- psum (skipn 16 (dt1_hdr (length D) a) ++ D) (length D + 4)) 128 ltac:(lia)) as M.
  rewrite rc_byte_lit by lia.
  Z.div_mod_to_equations. lia.
Qed.

Lemma dt1_so256 : forall n a D ob, length D = n -> length ob = 32%nat -> (n <= 9)%nat ->
  psum (dt1_out n a D ob) 32 mod 256 = 0.
Proof.
  intros n a D ob LD Lob Hn. unfold dt1_out.
  pose proof (dt1_body_length n a D ob LD Lob Hn) as LB.
  replace 32%nat with (S (length (dt1_body n a D ob))) by lia.
  rewrite psum_snoc. rewrite LB.
  pose proof (Z.mod_pos_bound (- psum (dt1_body n a D ob) 31) 256 ltac:(lia)) as M.
  rewrite rc_byte_lit by lia.
  Z.div_mod_to_equations. lia.
Qed.
