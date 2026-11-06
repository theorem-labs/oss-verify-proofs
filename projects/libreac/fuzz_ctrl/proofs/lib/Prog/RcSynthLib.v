From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib RcSynth.
Import ListNotations.
Open Scope Z_scope.

Lemma rs_rb_range : forall row i, 0 <= rb row i < 256.
Proof. intros row i. unfold rb. apply byte_range. Qed.

Lemma rs_rw16_range : forall row i, 0 <= rw16 row i < 65536.
Proof. intros row i. unfold rw16. pose proof (rs_rb_range row i). pose proof (rs_rb_range row (S i)). lia. Qed.

Lemma rs_rw32_range : forall row i, 0 <= rw32 row i < 4294967296.
Proof. intros row i. unfold rw32. pose proof (rs_rw16_range row i). pose proof (rs_rw16_range row (S (S i))). lia. Qed.

Lemma rs_rw64_range : forall row i, 0 <= rw64 row i < 2^64.
Proof. intros row i. unfold rw64. pose proof (rs_rw32_range row i). pose proof (rs_rw32_range row (4 + i)). lia. Qed.

Lemma rs_zle_cons : forall n (c : byte) z,
  Z_to_le_bytes (S n) (bv_unsigned c + 256 * z) = c :: Z_to_le_bytes n z.
Proof.
  intros n c z. cbn [Z_to_le_bytes]. pose proof (byte_range c) as Bc. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite (Z.mul_comm 256 z), Z_mod_plus_full. apply Z.mod_small. lia.
  - f_equal. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    rewrite (Z.mul_comm 256 z), Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma rs_firstn_skipn : forall (l : list byte) k n, (k < length l)%nat ->
  firstn (S n) (skipn k l) = nth k l (bz 0) :: firstn n (skipn (S k) l).
Proof.
  induction l as [|x l IH]; intros k n H; cbn [length] in H; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma rs_le2 : forall row k, (k + 2 <= length row)%nat ->
  le2 (Z_to_bv 64 (rw16 row k)) = firstn 2 (skipn k row).
Proof.
  intros row k H. unfold le2. pose proof (rs_rw16_range row k).
  rewrite unsigned_lit by lia. unfold rw16, rb.
  rewrite !rs_firstn_skipn by lia. cbn [firstn].
  set (b0 := nth k row (bz 0)). set (b1 := nth (S k) row (bz 0)).
  replace (bv_unsigned b0 + 256 * bv_unsigned b1) with (bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * 0)) by lia.
  rewrite !rs_zle_cons. reflexivity.
Qed.

Lemma rs_le4 : forall row k, (k + 4 <= length row)%nat ->
  le4 (Z_to_bv 64 (rw32 row k)) = firstn 4 (skipn k row).
Proof.
  intros row k H. unfold le4. pose proof (rs_rw32_range row k).
  rewrite unsigned_lit by lia. unfold rw32, rw16, rb.
  rewrite !rs_firstn_skipn by lia. cbn [firstn].
  set (b0 := nth k row (bz 0)). set (b1 := nth (S k) row (bz 0)).
  set (b2 := nth (S (S k)) row (bz 0)). set (b3 := nth (S (S (S k))) row (bz 0)).
  replace (bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * (bv_unsigned b2 + 256 * bv_unsigned b3))
    with (bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * 0))))
    by lia.
  rewrite !rs_zle_cons. reflexivity.
Qed.

Lemma rs_le8 : forall row k, (k + 8 <= length row)%nat ->
  le8 (Z_to_bv 64 (rw64 row k)) = firstn 8 (skipn k row).
Proof.
  intros row k H. change (le8 (Z_to_bv 64 (rw64 row k))) with (Z_to_le_bytes 8 (bv_unsigned (Z_to_bv 64 (rw64 row k)))).
  pose proof (rs_rw64_range row k).
  rewrite unsigned_lit by lia. unfold rw64, rw32, rw16, rb.
  rewrite !rs_firstn_skipn by lia. cbn [firstn].
  replace (4 + k)%nat with (S (S (S (S k)))) by lia.
  set (b0 := nth k row (bz 0)). set (b1 := nth (S k) row (bz 0)).
  set (b2 := nth (S (S k)) row (bz 0)). set (b3 := nth (S (S (S k))) row (bz 0)).
  set (b4 := nth (S (S (S (S k)))) row (bz 0)). set (b5 := nth (S (S (S (S (S k))))) row (bz 0)).
  set (b6 := nth (S (S (S (S (S (S k)))))) row (bz 0)).
  set (b7 := nth (S (S (S (S (S (S (S k))))))) row (bz 0)).
  match goal with |- Z_to_le_bytes 8 ?z = _ =>
    replace z with (bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 +
      256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * (bv_unsigned b7 + 256 * 0))))))))
      by lia end.
  rewrite !rs_zle_cons. reflexivity.
Qed.

Lemma rs_rd4 : forall segs m A row k, bytes_at segs m A row -> (k + 4 <= length row)%nat ->
  ov_read_bytes segs m (wa (A + Z.of_nat k)) 4 = Some (le4 (Z_to_bv 64 (rw32 row k))).
Proof.
  intros segs m A row k HB H. rewrite (bytes_at_read segs m A row (Z.of_nat k) 4 HB) by lia.
  rewrite Nat2Z.id, rs_le4 by lia. reflexivity.
Qed.

Lemma rs_rd2 : forall segs m A row k, bytes_at segs m A row -> (k + 2 <= length row)%nat ->
  ov_read_bytes segs m (wa (A + Z.of_nat k)) 2 = Some (le2 (Z_to_bv 64 (rw16 row k))).
Proof.
  intros segs m A row k HB H. rewrite (bytes_at_read segs m A row (Z.of_nat k) 2 HB) by lia.
  rewrite Nat2Z.id, rs_le2 by lia. reflexivity.
Qed.

Lemma rs_rd8 : forall segs m A row k, bytes_at segs m A row -> (k + 8 <= length row)%nat ->
  ov_read_bytes segs m (wa (A + Z.of_nat k)) 8 = Some (le8 (Z_to_bv 64 (rw64 row k))).
Proof.
  intros segs m A row k HB H. rewrite (bytes_at_read segs m A row (Z.of_nat k) 8 HB) by lia.
  rewrite Nat2Z.id, rs_le8 by lia. reflexivity.
Qed.

Lemma rs_psum_S : forall bs k, psum bs (S k) = psum bs k + bv_unsigned (nth k bs (Z_to_bv 8 0)).
Proof. reflexivity. Qed.

Lemma rs_chk_sum : forall x, length x = 31%nat -> psum (withchk x) 32 mod 256 = 0.
Proof.
  intros x L. unfold withchk, chk, bz. replace 32%nat with (S (length x)) by lia.
  rewrite psum_snoc, L. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  rewrite Z.mod_mod by lia. rewrite Zplus_mod_idemp_r. replace (psum x 31 + - psum x 31) with 0 by lia. reflexivity.
Qed.

Lemma rs_zeros_sum : forall n, psum (zeros 32) n = 0.
Proof.
  induction n as [|n IH]; [reflexivity|]. rewrite rs_psum_S, IH. unfold zeros.
  destruct (Nat.lt_ge_cases n 32) as [H|H].
  - rewrite nth_repeat_lt by exact H. reflexivity.
  - rewrite nth_overflow by (rewrite repeat_length; exact H). reflexivity.
Qed.

Lemma rs_slots_len : forall row, synok row = true -> length (slots row) = 12%nat.
Proof.
  intros row H. unfold synok in H. rewrite !andb_true_iff in H.
  destruct H as ((((H1 & H2) & H3) & H4) & H5).
  apply Z.leb_le in H1, H2, H5. apply Z.eqb_eq in H3, H4.
  assert (0 <= ic row / 4) by (apply Z.div_pos; lia).
  assert (0 <= oc row / 4) by (apply Z.div_pos; lia).
  unfold slots. destruct (lay row =? 1); rewrite !length_app, !repeat_length; lia.
Qed.

Lemma rs_gram31_len : forall row, length row = 296%nat -> synok row = true -> length (gram31 row) = 31%nat.
Proof.
  intros row L H. unfold gram31, tail. rewrite !length_app, rs_slots_len by exact H.
  rewrite length_firstn, length_skipn, L. reflexivity.
Qed.

Lemma rs_gram_sum : forall row, length row = 296%nat -> synok row = true -> psum (gram row) 32 mod 256 = 0.
Proof.
  intros row L H. pose proof (rs_gram31_len row L H) as G. unfold gram.
  replace 32%nat with (S (length (gram31 row))) by lia. rewrite psum_snoc, G.
  pose proof (Z.mod_pos_bound (256 - psum (gram31 row) 31 mod 256) 256 ltac:(lia)) as M.
  unfold bz. rewrite rc_byte_lit by lia. Z.div_mod_to_equations. lia.
Qed.

Lemma rs_takenz_len : forall bs, (length (takenz bs) <= length bs)%nat.
Proof. induction bs as [|x bs IH]; cbn [takenz length]; [lia|]. destruct (bv_unsigned x =? 0); cbn [length]; lia. Qed.

Lemma rs_nmf_len : forall nb, (16 <= length (nmf nb))%nat.
Proof. intros nb. unfold nmf. rewrite length_app, repeat_length. lia. Qed.

Lemma rs_nmr_len : forall row nb, (16 <= length (nmr row nb))%nat.
Proof. intros row nb. unfold nmr. destruct (rname row =? 0); [reflexivity | apply rs_nmf_len]. Qed.

Lemma rs_idf31_len : forall nm, (16 <= length nm)%nat -> length (idf31 nm) = 31%nat.
Proof. intros nm L. unfold idf31. rewrite length_app, length_firstn. cbn [length map]. lia. Qed.

Lemma rs_idl31_len : forall nm, (16 <= length nm)%nat -> length (idl31 nm) = 31%nat.
Proof.
  intros nm L. unfold idl31. rewrite !length_app, length_firstn, length_skipn. cbn [length map]. unfold zeros.
  rewrite repeat_length. lia.
Qed.

Lemma rs_dt1s_sum : forall a D, (length D <= 9)%nat -> psum (dt1s a D) 32 mod 256 = 0.
Proof. intros a D L. unfold dt1s, zeros. apply dt1_so256; [reflexivity | apply repeat_length | exact L]. Qed.

Lemma rs_synth_sum : forall row b nb, length row = 296%nat -> psum (synth row b nb) 32 mod 256 = 0.
Proof.
  intros row b nb L. unfold synth.
  destruct (6 <? b); [rewrite rs_zeros_sum; reflexivity|].
  destruct (b =? 0).
  { destruct (synok row) eqn:E; [apply rs_gram_sum; assumption | rewrite rs_zeros_sum; reflexivity]. }
  destruct (b =? 1); [reflexivity|].
  destruct (b =? 2); [reflexivity|].
  destruct (b =? 3).
  { destruct (fwm row <=? 9999); [apply rs_dt1s_sum; cbn; lia | rewrite rs_zeros_sum; reflexivity]. }
  destruct (b =? 4); [apply rs_dt1s_sum; cbn; lia|].
  destruct (has row =? 0); [rewrite rs_zeros_sum; reflexivity|].
  destruct (b =? 5); apply rs_chk_sum; [apply rs_idf31_len | apply rs_idl31_len]; apply rs_nmr_len.
Qed.

Lemma rs_dt1s_len : forall a D, (length D <= 9)%nat -> length (dt1s a D) = 32%nat.
Proof.
  intros a D L. unfold dt1s, dt1_out. rewrite length_app.
  rewrite (dt1_body_length (length D) a D (zeros 32)) by first [reflexivity | apply repeat_length | exact L].
  reflexivity.
Qed.

Lemma rs_synth_len : forall row b nb, length row = 296%nat -> length (synth row b nb) = 32%nat.
Proof.
  intros row b nb L. unfold synth.
  destruct (6 <? b); [reflexivity|].
  destruct (b =? 0).
  { destruct (synok row) eqn:E; [|reflexivity]. unfold gram. rewrite length_app, (rs_gram31_len row L E). reflexivity. }
  destruct (b =? 1); [reflexivity|].
  destruct (b =? 2); [reflexivity|].
  destruct (b =? 3).
  { destruct (fwm row <=? 9999); [apply rs_dt1s_len; cbn; lia | reflexivity]. }
  destruct (b =? 4); [apply rs_dt1s_len; cbn; lia|].
  destruct (has row =? 0); [reflexivity|].
  destruct (b =? 5); unfold idf, idl, withchk; rewrite length_app;
    [rewrite rs_idf31_len | rewrite rs_idl31_len]; try reflexivity; apply rs_nmr_len.
Qed.

Lemma rs_synth_gram : forall row nb, synok row = true -> rc row 0 = 1 /\ synth row 0 nb = gram row.
Proof. intros row nb H. unfold rc, synth. cbn [Z.ltb Z.compare Z.eqb]. rewrite H. split; reflexivity. Qed.

Lemma rs_ok_synok : forall row, ok row = true -> org row <> 0 -> synok row = true.
Proof.
  intros row H O. unfold ok in H. apply orb_true_iff in H. destruct H as [H|H]; [|exact H].
  apply Z.eqb_eq in H. contradiction.
Qed.

Lemma rs_synth_decl : forall row nb, synok row = true -> (org row = 0 -> cfg row = gram row) ->
  synth row 0 nb = decl row.
Proof.
  intros row nb H C. destruct (rs_synth_gram row nb H) as [_ E]. rewrite E. unfold decl.
  destruct (Z.eqb_spec (org row) 0) as [O|O]; [symmetry; apply C; exact O | reflexivity].
Qed.

Lemma rs_ic_range : forall row, -2^31 <= ic row < 2^31.
Proof.
  intros row. unfold ic, bv_swrap. change (bv_half_modulus 32) with 2147483648. unfold bv_wrap.
  change (bv_modulus 32) with 4294967296. pose proof (Z.mod_pos_bound (rw32 row 16 + 2147483648) 4294967296). lia.
Qed.

Lemma rs_oc_range : forall row, -2^31 <= oc row < 2^31.
Proof.
  intros row. unfold oc, bv_swrap. change (bv_half_modulus 32) with 2147483648. unfold bv_wrap.
  change (bv_modulus 32) with 4294967296. pose proof (Z.mod_pos_bound (rw32 row 20 + 2147483648) 4294967296). lia.
Qed.

Lemma rs_sx32_ic : forall row, sx32 (Z_to_bv 64 (rw32 row 16)) = Z_to_bv 64 (ic row).
Proof. intros row. unfold sx32, ic. rewrite unsigned_lit by (pose proof (rs_rw32_range row 16); lia). reflexivity. Qed.

Lemma rs_sx32_oc : forall row, sx32 (Z_to_bv 64 (rw32 row 20)) = Z_to_bv 64 (oc row).
Proof. intros row. unfold sx32, oc. rewrite unsigned_lit by (pose proof (rs_rw32_range row 20); lia). reflexivity. Qed.

Lemma rs_zx16 : forall row k, zx16 (Z_to_bv 64 (rw16 row k)) = Z_to_bv 64 (rw16 row k).
Proof.
  intros row k. pose proof (rs_rw16_range row k). unfold zx16. rewrite unsigned_lit by lia.
  rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma rs_lts0 : forall x, -2^63 <= x < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 0) = (x <? 0).
Proof.
  intros x Hx. rewrite bv_lts_zero_r, unsigned_lit_wrap.
  destruct (Z.ltb_spec x 0).
  - apply Z.leb_le. Z.div_mod_to_equations. lia.
  - apply Z.leb_gt. rewrite Z.mod_small by lia. lia.
Qed.

Lemma rs_or3 : forall x y, 0 <= x < 2^63 -> 0 <= y < 2^63 ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 y)) (bv_unsigned (Z_to_bv 64 x)))))
                              3)) (Z_to_bv 64 0)
  = (x mod 4 =? 0) && (y mod 4 =? 0).
Proof.
  intros x y Hx Hy. rewrite (unsigned_lit x), (unsigned_lit y) by lia. rewrite unsigned_lit_wrap.
  assert (E : Z.land (Z.lor y x mod 2^64) 3 = Z.lor (y mod 4) (x mod 4)).
  { change 3 with (Z.ones 2). rewrite Z.land_ones by lia.
    replace ((Z.lor y x mod 2^64) mod 2^2) with (Z.land (Z.lor y x) (Z.ones 2))
      by (rewrite Z.land_ones by lia; Z.div_mod_to_equations; lia).
    rewrite Z.land_lor_distr_l. rewrite !Z.land_ones by lia. reflexivity. }
  rewrite E. unfold bv_eqb. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  assert (X4 : x mod 4 = 0 \/ x mod 4 = 1 \/ x mod 4 = 2 \/ x mod 4 = 3) by lia.
  assert (Y4 : y mod 4 = 0 \/ y mod 4 = 1 \/ y mod 4 = 2 \/ y mod 4 = 3) by lia.
  destruct X4 as [X4|[X4|[X4|X4]]]; destruct Y4 as [Y4|[Y4|[Y4|Y4]]]; rewrite X4, Y4; reflexivity.
Qed.

Lemma rs_srliw2 : forall x, 0 <= x < 2^31 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64 x))) 2) = x / 4.
Proof.
  intros x Hx. rewrite unsigned_lit by lia. unfold bv_wrap. change (bv_modulus 32) with 4294967296.
  rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^2) with 4.
  apply bv_swrap_small. change (bv_half_modulus 32) with 2147483648.
  pose proof (Z.div_pos x 4 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound x 4 x ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma rs_zxb_eqb : forall (c : byte) z, 0 <= z < 2^64 -> bv_eqb (zxb c) (Z_to_bv 64 z) = (bv_unsigned c =? z).
Proof. intros c z Hz. unfold zxb. pose proof (byte_range c). apply rc_eqb_lit; lia. Qed.

Lemma rs_seqz : forall x, 1 <= x < 2^64 -> x + bv_unsigned (v_sltiu (Z_to_bv 64 x) 1) = x.
Proof.
  intros x Hx. unfold v_sltiu. rewrite unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  replace (x <? 1) with false by (symmetry; apply Z.ltb_ge; lia). change (bv_unsigned (Z_to_bv 64 0)) with 0. lia.
Qed.

Lemma rs_negw8 : forall s, Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64 s))))) =
  bz ((- s) mod 256).
Proof. intros s. exact (f_equal (hd (bz 0)) (rc_le1_negw s)). Qed.

Lemma rs_gram_chk : forall x, bz ((256 - (psum x 31 mod 256)) mod 256) = bz ((- psum x 31) mod 256).
Proof.
  intros x. unfold bz. apply Z_to_bv8_mod. change (2^8) with 256. rewrite !Z.mod_mod by lia.
  rewrite Zminus_mod_idemp_r. replace (256 - psum x 31) with (- psum x 31 + 1 * 256) by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma rs_psum_firstn : forall Y n k, (k <= n)%nat -> (k <= length Y)%nat -> psum (firstn n Y) k = psum Y k.
Proof.
  intros Y n k H1 H2. rewrite <- (firstn_skipn n Y) at 2. rewrite psum_app_l; [reflexivity|].
  rewrite length_firstn. lia.
Qed.

Lemma rs_sx16_u : forall w, 0 <= w < 65536 ->
  bv_unsigned (sx16 (Z_to_bv 64 w)) = if w <? 32768 then w else w + 18446744073709486080.
Proof.
  intros w Hw. unfold sx16. rewrite (unsigned_lit w) by lia. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 16) with 32768. change (bv_modulus 16) with 65536.
  destruct (Z.ltb_spec w 32768).
  - rewrite (Z.mod_small (w + 32768) 65536) by lia. replace (w + 32768 - 32768) with w by lia.
    apply Z.mod_small. lia.
  - replace (w + 32768) with ((w - 32768) + 1 * 65536) by lia. rewrite Z_mod_plus_full.
    rewrite (Z.mod_small (w - 32768)) by lia.
    replace (w - 32768 - 32768) with ((w + 18446744073709486080) + (-1) * 2^64) by lia.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma rs_lo16 : forall w, 0 <= w < 65536 -> Z_to_bv 8 (bv_unsigned (sx16 (Z_to_bv 64 w))) = wlo w.
Proof.
  intros w Hw. unfold wlo, bz. apply Z_to_bv8_mod. rewrite rs_sx16_u by exact Hw. change (2^8) with 256.
  rewrite Z.mod_mod by lia. destruct (w <? 32768); [reflexivity|].
  replace (w + 18446744073709486080) with (w + 72057594037927680 * 256) by lia. apply Z_mod_plus_full.
Qed.

Lemma rs_hi16 : forall w, 0 <= w < 65536 ->
  Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (sx16 (Z_to_bv 64 w))) 8))) = whi w.
Proof.
  intros w Hw. unfold whi, bz. apply Z_to_bv8_mod. rewrite unsigned_lit_wrap. rewrite mod_mod8_of_modw by lia.
  rewrite rs_sx16_u by exact Hw. rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256.
  rewrite Z.mod_mod by lia. destruct (w <? 32768); [reflexivity|].
  replace (w + 18446744073709486080) with (w + 72057594037927680 * 256) by lia. rewrite Z.div_add by lia.
  replace 72057594037927680 with (281474976710655 * 256) by lia. rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma rs_rw_take : forall segs m A cs k, rw_cells segs m A cs ->
  rw_cells segs m A (CB (cells_size (firstn k cs)) (cells_bytes (firstn k cs)) :: skipn k cs).
Proof.
  intros segs m A cs k [[Hwf HB] HW]. rewrite <- (firstn_skipn k cs) in Hwf, HB, HW.
  rewrite cells_wf_app in Hwf. rewrite cells_bytes_app in HB. rewrite cells_size_app in HW.
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [apply cells_bytes_length; tauto | tauto].
  - cbn [cells_bytes cbytes]. exact HB.
  - cbn [cells_size csize]. exact HW.
Qed.

Lemma rs_cell0_sub : forall segs m A N X cs k n, rw_cells segs m A (CB N X :: cs) -> (k + n <= N)%nat ->
  bytes_at segs m (A + Z.of_nat k) (firstn n (skipn k X)).
Proof.
  intros segs m A N X cs k n [[Hwf HB] _] Hkn. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [LX _].
  cbn [cells_bytes cbytes] in HB. apply bytes_at_app in HB. destruct HB as [HB _].
  apply bytes_at_sub; [exact HB | lia].
Qed.

Lemma rs_rw_sub : forall segs m A N X k n, rw_cells segs m A [CB N X] -> (k + n <= N)%nat ->
  rw_cells segs m (A + Z.of_nat k) [CB n (firstn n (skipn k X))].
Proof.
  intros segs m A N X k n HC Hkn. pose proof (rs_cell0_sub segs m A N X [] k n HC Hkn) as HB.
  destruct HC as [[Hwf _] HW]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [LX _].
  cbn [cells_size csize] in HW. rewrite Nat.add_0_r in HW.
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [rewrite length_firstn, length_skipn; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. apply (wr_at_sub segs m A (Z.of_nat N)); [exact HW | lia | lia | lia].
Qed.

Lemma rs_rw_upd : forall segs m m' A N X k n Y,
  rw_cells segs m A [CB N X] -> (k + n <= N)%nat ->
  munch [(A + Z.of_nat k, A + Z.of_nat k + Z.of_nat n)] m m' -> wmono segs m m' ->
  rw_cells segs m' (A + Z.of_nat k) [CB n Y] ->
  rw_cells segs m' A [CB N (upd_bytes X k Y)].
Proof.
  intros segs m m' A N X k n Y [[Hwf HB] HW] Hkn MU WM [[HwfY HBY] _].
  cbn [cells_wf cell_wf] in Hwf, HwfY. destruct Hwf as [LX _]. destruct HwfY as [LY _].
  cbn [cells_bytes cbytes] in HB, HBY. rewrite app_nil_r in HB, HBY.
  cbn [cells_size csize] in HW. rewrite Nat.add_0_r in HW.
  pose proof (bytes_at_sub segs m A X 0 k HB ltac:(lia)) as B1.
  change (skipn 0 X) with X in B1. cbn [Z.of_nat] in B1. rewrite Z.add_0_r in B1.
  pose proof (bytes_at_sub segs m A X (k + n) (N - (k + n)) HB ltac:(lia)) as B3.
  rewrite firstn_all2 in B3 by (rewrite length_skipn; lia).
  apply (bytes_at_transport segs [(A + Z.of_nat k, A + Z.of_nat k + Z.of_nat n)] m m') in B1;
    [|exact MU | cbn [disjoint_from]; rewrite length_firstn; lia].
  apply (bytes_at_transport segs [(A + Z.of_nat k, A + Z.of_nat k + Z.of_nat n)] m m') in B3;
    [|exact MU | cbn [disjoint_from]; lia].
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [rewrite upd_bytes_length; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold upd_bytes. apply bytes_at_app. split; [exact B1|].
    rewrite length_firstn. replace (Nat.min k (length X)) with k by lia.
    apply bytes_at_app. split; [exact HBY|]. rewrite LY.
    replace (A + Z.of_nat k + Z.of_nat n) with (A + Z.of_nat (k + n)) by lia. exact B3.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. eapply wr_at_transport; [exact HW | exact WM].
Qed.

Lemma rs_skipn_zeros : forall n r, skipn n (zeros r) = zeros (r - n).
Proof.
  unfold zeros. induction n as [|n IH]; intros r; [cbn; rewrite Nat.sub_0_r; reflexivity|].
  destruct r as [|r]; [reflexivity|]. cbn [repeat skipn]. rewrite IH. reflexivity.
Qed.

Lemma rs_upd_fill : forall (H P Y : list byte) r k, k = (length H + length P)%nat -> (length Y <= r)%nat ->
  upd_bytes (H ++ P ++ zeros r) k Y = H ++ (P ++ Y) ++ zeros (r - length Y).
Proof.
  intros H P Y r k -> L. unfold upd_bytes. rewrite (app_assoc H P (zeros r)).
  replace (length H + length P)%nat with (length (H ++ P)) by (rewrite length_app; reflexivity).
  rewrite firstn_app_exact. rewrite skipn_app. rewrite skipn_all2 by lia.
  replace (length (H ++ P) + length Y - length (H ++ P))%nat with (length Y) by lia.
  rewrite rs_skipn_zeros. cbn [app]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma rs_slots_1 : forall row, lay row = 1 ->
  slots row = repeat (bz 1) (Z.to_nat (oc row / 4)) ++ repeat (bz 0) (Z.to_nat (ic row / 4)) ++
              repeat (bz 3) (12 - Z.to_nat (ic row / 4) - Z.to_nat (oc row / 4)).
Proof. intros row L. unfold slots. rewrite L. reflexivity. Qed.

Lemma rs_slots_2 : forall row, lay row <> 1 ->
  slots row = repeat (bz 2) (Z.to_nat (ic row / 4)) ++ repeat (bz 1) (Z.to_nat (oc row / 4)) ++
              repeat (bz 3) (12 - Z.to_nat (ic row / 4) - Z.to_nat (oc row / 4)).
Proof. intros row L. unfold slots. replace (lay row =? 1) with false by (symmetry; apply Z.eqb_neq; exact L). reflexivity. Qed.

Fixpoint rs_allz (f g : Z -> Z) (n : nat) (z : Z) : bool :=
  match n with O => true | S n' => Z.eqb (f z mod 256) (g z mod 256) && rs_allz f g n' (z + 1) end.

Lemma rs_allz_ok : forall f g n z, rs_allz f g n z = true -> forall v, z <= v < z + Z.of_nat n -> f v mod 256 = g v mod 256.
Proof.
  induction n as [|n IH]; intros z H v Hv; [lia|].
  cbn [rs_allz] in H. apply andb_true_iff in H. destruct H as [H1 H2].
  destruct (Z.eq_dec v z) as [->|NE]; [apply Z.eqb_eq; exact H1|].
  apply (IH (z + 1) H2). lia.
Qed.

Lemma rs_brute : forall f g v, rs_allz f g 10000 0 = true -> 0 <= v < 10000 -> Z_to_bv 8 (f v) = Z_to_bv 8 (g v).
Proof.
  intros f g v H Hv. apply Z_to_bv8_mod. change (2^8) with 256. apply (rs_allz_ok f g 10000 0 H).
  replace (0 + Z.of_nat 10000) with 10000 by (vm_compute; reflexivity). lia.
Qed.

Ltac rs_brute_tac v :=
  match goal with |- Z_to_bv 8 ?l = Z_to_bv 8 ?r =>
    let F := eval pattern v in l in let G := eval pattern v in r in
    match F with ?f v => match G with ?g v => apply (rs_brute f g v); [vm_compute; reflexivity | lia] end end
  end.
