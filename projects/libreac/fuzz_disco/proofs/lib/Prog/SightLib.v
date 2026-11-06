From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Bytes ZBridge Step.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcModel RcLib CtrlParsed disco_classify_c SightModel.
Import ListNotations.
Open Scope Z_scope.

Lemma bytes_at_fld : forall segs m A (bs : list byte) k n, bytes_at segs m A bs -> (k + n <= length bs)%nat ->
  bytes_at segs m (A + Z.of_nat k) (fld bs k n).
Proof.
  intros segs m A bs k n H Hk. unfold fld.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length_le in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Lemma fld_length : forall (bs : list byte) k n, (k + n <= length bs)%nat -> length (fld bs k n) = n.
Proof. intros bs k n H. unfold fld. rewrite length_firstn, length_skipn. lia. Qed.

Lemma le4_fu : forall (bs : list byte) k, (k + 4 <= length bs)%nat -> le4 (Z_to_bv 64 (fu bs k 4)) = fld bs k 4.
Proof.
  intros bs k Hk. unfold fu, le4.
  pose proof (fld_length bs k 4 Hk) as L.
  pose proof (le_val_range _ (bytes_ok_map (fld bs k 4))) as R. rewrite length_map, L in R.
  rewrite <- bytes_le_to_Z_le_val in R. change (256 ^ Z.of_nat 4) with (2 ^ 32) in R.
  rewrite unsigned_lit by lia.
  pose proof (Z_to_le_bytes_to_Z (fld bs k 4)) as E. rewrite L in E. exact E.
Qed.

Lemma fu4_range : forall (bs : list byte) k, (k + 4 <= length bs)%nat -> 0 <= fu bs k 4 < 2 ^ 32.
Proof.
  intros bs k Hk. unfold fu.
  pose proof (fld_length bs k 4 Hk) as L.
  pose proof (le_val_range _ (bytes_ok_map (fld bs k 4))) as R. rewrite length_map, L in R.
  rewrite <- bytes_le_to_Z_le_val in R. change (256 ^ Z.of_nat 4) with (2 ^ 32) in R. exact R.
Qed.

Lemma rd_le4 : forall segs m A (bs : list byte) k, bytes_at segs m A bs -> (k + 4 <= length bs)%nat ->
  ov_read_bytes segs m (wa (A + Z.of_nat k)) 4 = Some (le4 (Z_to_bv 64 (fu bs k 4))).
Proof.
  intros segs m A bs k H Hk. rewrite (bytes_at_read segs m A bs (Z.of_nat k) 4 H) by lia.
  rewrite Nat2Z.id, le4_fu by exact Hk. reflexivity.
Qed.

Lemma bytes_eqb_true : forall a b, bytes_eqb a b = true -> map bv_unsigned a = map bv_unsigned b.
Proof. intros a b H. unfold bytes_eqb in H. destruct (list_eq_dec Z.eq_dec _ _); [assumption | discriminate]. Qed.

Lemma bytes_eqb_false : forall a b, bytes_eqb a b = false -> map bv_unsigned a <> map bv_unsigned b.
Proof. intros a b H. unfold bytes_eqb in H. destruct (list_eq_dec Z.eq_dec _ _); [discriminate | assumption]. Qed.

Lemma bv_eqb_nz : forall v, -256 < v < 256 -> v <> 0 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = false.
Proof.
  intros v R N. unfold bv_eqb. rewrite !unsigned_lit_wrap. apply Z.eqb_neq.
  change (2 ^ 64) with 18446744073709551616. Z.div_mod_to_equations. lia.
Qed.

Lemma kq_div : forall x, 0 <= x < 2 ^ 64 ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftr (x * 16397105843297379215) 64))) 5 = x / 36.
Proof.
  intros x Hx.
  assert (H0 : 0 <= Z.shiftr (x * 16397105843297379215) 64 < 2 ^ 64).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  rewrite unsigned_lit by exact H0.
  rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia.
  pose proof (Z.div_mod x 36 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 36 ltac:(lia)) as M.
  pose proof (Z.div_pos x 36 ltac:(lia) ltac:(lia)) as P.
  symmetry. apply Z.div_unique_pos with (r := 28 * (x / 36) + x mod 36 * 16397105843297379215); lia.
Qed.

Lemma uq_div : forall x, 0 <= x < 2 ^ 16 ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl x 48)) * 3817799680) 64))) 21 =
  x / 36.
Proof.
  intros x Hx.
  rewrite (Z.shiftl_mul_pow2 x 48) by lia.
  rewrite (unsigned_lit (x * 2 ^ 48)) by lia.
  replace (x * 2 ^ 48 * 3817799680) with (x * 58255 * 2 ^ 64) by lia.
  rewrite !Z.shiftr_div_pow2 by lia.
  rewrite Z.div_mul by lia.
  rewrite (unsigned_lit (x * 58255)) by lia.
  pose proof (Z.div_mod x 36 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 36 ltac:(lia)) as M.
  pose proof (Z.div_pos x 36 ltac:(lia) ltac:(lia)) as P.
  symmetry. apply Z.div_unique_pos with (r := 28 * (x / 36) + x mod 36 * 58255); lia.
Qed.

Lemma sw_u : forall a, 0 <= a < 2 ^ 32 ->
  bv_unsigned (Z_to_bv 64 (bv_swrap 32 a)) = a + (2 ^ 64 - 2 ^ 32) * (a / 2 ^ 31).
Proof. intros a Ha. rewrite unsigned_lit_wrap, bv_swrap32_eq. Z.div_mod_to_equations. lia. Qed.

Lemma sw_eqb : forall a b, 0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 ->
  bv_eqb (Z_to_bv 64 (bv_swrap 32 a)) (Z_to_bv 64 (bv_swrap 32 b)) = (a =? b).
Proof.
  intros a b Ha Hb. unfold bv_eqb. rewrite !sw_u by assumption.
  destruct (Z.eqb_spec a b) as [E|E]; [subst; apply Z.eqb_refl|].
  apply Z.eqb_neq. Z.div_mod_to_equations. lia.
Qed.

Lemma sw_ltu : forall a b, 0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 ->
  bv_ltu (Z_to_bv 64 (bv_swrap 32 a)) (Z_to_bv 64 (bv_swrap 32 b)) = (a <? b).
Proof.
  intros a b Ha Hb. unfold bv_ltu. rewrite !sw_u by assumption.
  destruct (Z.ltb_spec a b) as [E|E]; [apply Z.ltb_lt | apply Z.ltb_ge]; Z.div_mod_to_equations; lia.
Qed.

Lemma sw_mod : forall x, Z_to_bv 64 (bv_swrap 32 (x mod 2 ^ 32)) = Z_to_bv 64 (bv_swrap 32 x).
Proof. intros x. rewrite !bv_swrap32_eq. rewrite Z.add_mod_idemp_l by lia. reflexivity. Qed.

Lemma sw_small : forall v, 0 <= v < 2 ^ 31 -> Z_to_bv 64 (bv_swrap 32 v) = Z_to_bv 64 v.
Proof. intros v Hv. f_equal. rewrite bv_swrap32_eq. rewrite Z.mod_small by lia. lia. Qed.

Lemma sx32_sw : forall v, 0 <= v < 2 ^ 64 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 (bv_swrap 32 v).
Proof. intros v Hv. unfold sx32. rewrite unsigned_lit by exact Hv. reflexivity. Qed.

Lemma mask_sel : forall r q, 0 <= r < 2 ^ 64 -> 0 <= q < 2 ^ 64 ->
  Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 r)) + -1))) q =
  if r =? 0 then q else 0.
Proof.
  intros r q Hr Hq. rewrite v_sltu_b2z, (unsigned_lit r) by exact Hr.
  destruct (Z.eqb_spec r 0) as [E|E].
  - subst r.
    replace (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.b2z (bv_unsigned (Z_to_bv 64 0) <? 0))) + -1)))
      with (Z.ones 64) by reflexivity.
    rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. exact Hq.
  - replace (bv_unsigned (Z_to_bv 64 0) <? r) with true by (symmetry; apply Z.ltb_lt; change (bv_unsigned (Z_to_bv 64 0)) with 0; lia).
    replace (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.b2z true)) + -1))) with 0 by reflexivity.
    apply Z.land_0_l.
Qed.

Lemma geo_q : forall len, 52 <= len -> (len - 52) mod 36 = 0 -> geo len = ((len - 52) / 36) mod 2 ^ 32.
Proof.
  intros len H1 H2. unfold geo. replace (52 <=? len) with true by (symmetry; apply Z.leb_le; lia).
  rewrite H2. reflexivity.
Qed.

Lemma geo_0 : forall len, len < 52 \/ (len - 52) mod 36 <> 0 -> geo len = 0.
Proof.
  intros len H. unfold geo.
  destruct (Z.leb_spec 52 len); [|reflexivity].
  destruct (Z.eqb_spec ((len - 52) mod 36) 0); [lia | reflexivity].
Qed.

Lemma geo_range : forall len, 0 <= geo len < 2 ^ 32.
Proof.
  intros len. unfold geo. destruct (_ && _); [apply Z.mod_pos_bound; lia | lia].
Qed.

Lemma geo_sw : forall len, 52 <= len < 2 ^ 64 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (if (len - 52) mod 36 =? 0 then (len - 52) / 36 else 0)) + 0)) =
  Z_to_bv 64 (bv_swrap 32 (geo len)).
Proof.
  intros len H. rewrite Z.add_0_r.
  destruct (Z.eqb_spec ((len - 52) mod 36) 0) as [E|E].
  - rewrite (geo_q len) by lia. rewrite sw_mod. rewrite unsigned_lit; [reflexivity|]. Z.div_mod_to_equations. lia.
  - rewrite (geo_0 len) by lia. reflexivity.
Qed.

Lemma geo_qq : forall len, 52 <= len <= 65535 -> (len - 52) mod 36 = 0 ->
  Z_to_bv 64 ((len - 52) / 36) = Z_to_bv 64 (bv_swrap 32 (geo len)).
Proof.
  intros len H E. rewrite (geo_q len) by lia.
  rewrite (Z.mod_small ((len - 52) / 36) (2 ^ 32)) by (Z.div_mod_to_equations; lia).
  rewrite (sw_small ((len - 52) / 36)) by (Z.div_mod_to_equations; lia). reflexivity.
Qed.

Lemma geo_u : forall len, 52 <= len <= 65535 ->
  Z_to_bv 64 (if (len - 52) mod 36 =? 0 then (len - 52) / 36 else 0) = Z_to_bv 64 (bv_swrap 32 (geo len)).
Proof.
  intros len H.
  destruct (Z.eqb_spec ((len - 52) mod 36) 0) as [E|E].
  - apply geo_qq; assumption.
  - rewrite (geo_0 len) by lia. reflexivity.
Qed.

Lemma sh48_r : forall r, 0 <= r < 2 ^ 16 ->
  bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (bv_swrap 32 r))) 48)) = r * 2 ^ 48.
Proof.
  intros r Hr. rewrite (sw_small r) by lia. rewrite (unsigned_lit r) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. apply unsigned_lit. lia.
Qed.

Lemma land16 : forall r, 0 <= r < 2 ^ 16 -> Z.land (bv_unsigned (Z_to_bv 64 r)) 65535 = r.
Proof.
  intros r Hr. rewrite (unsigned_lit r) by lia. change 65535 with (Z.ones 16).
  rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma sltiu1_u : forall x : word, bv_unsigned (v_sltiu x 1) = if bv_unsigned x =? 0 then 1 else 0.
Proof.
  intros x. pose proof (bv_unsigned_in_range 64 x) as R. unfold v_sltiu. change (bv_wrap 64 1) with 1.
  destruct (Z.ltb_spec (bv_unsigned x) 1), (Z.eqb_spec (bv_unsigned x) 0); try lia; reflexivity.
Qed.

Lemma land255 : forall S, 0 <= S < 2 ^ 64 ->
  bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 S)) 255)) = S mod 256.
Proof.
  intros S HS. rewrite (unsigned_lit S) by exact HS.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
  apply unsigned_lit. pose proof (Z.mod_pos_bound S 256 ltac:(lia)). lia.
Qed.

Lemma lor_u : forall a b : word, bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned a) (bv_unsigned b))) = Z.lor (bv_unsigned a) (bv_unsigned b).
Proof. intros a b. rewrite <- bv_or_unsigned. rewrite Z_to_bv_lit_self. reflexivity. Qed.

Lemma lor_ne0 : forall a b : word, bv_unsigned a <> 0 \/ bv_unsigned b <> 0 ->
  bv_eqb (Z_to_bv 64 (Z.lor (bv_unsigned a) (bv_unsigned b))) (Z_to_bv 64 0) = false.
Proof.
  intros a b H. unfold bv_eqb. rewrite lor_u. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  apply Z.eqb_neq. intros E. apply Z.lor_eq_0_iff in E. lia.
Qed.

Lemma zxb_u : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof. intros b. unfold zxb. apply unsigned_lit. pose proof (byte_range b). lia. Qed.

Lemma role_small : forall r, 0 <= r < 2 ^ 32 -> 0 <= s32 r <= 2 -> 0 <= r <= 2.
Proof. intros r Hr H. unfold s32 in H. destruct (Z.ltb_spec r (2 ^ 31)); lia. Qed.
