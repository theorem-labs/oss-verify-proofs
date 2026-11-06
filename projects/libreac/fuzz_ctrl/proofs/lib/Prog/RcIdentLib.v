From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcIdentModel.
Import ListNotations.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Definition ivs (m0 m : word -> option byte) (id : Z) (idb : list byte) (p : Z) (pb : list byte) : Prop :=
  bytes_at segs m id idb /\ wr_at segs m id 38 /\ length idb = 38%nat /\
  bytes_at segs m p pb /\ (p + Z.of_nat (length pb) <= id \/ id + 38 <= p) /\
  munch [(id, id + 38)] m0 m /\ wmono segs m0 m /\ (mem_inv segs m0 -> mem_inv segs m).

Lemma ivs_start : forall m id idb p pb,
  rw_cells segs m id [CB 38 idb] -> bytes_at segs m p pb ->
  (p + Z.of_nat (length pb) <= id \/ id + 38 <= p) ->
  ivs m m id idb p pb.
Proof.
  intros m id idb p pb [[Hwf Hb] Hw] Hp Hd. destruct Hwf as [Hl _]. cbn [cell_wf] in Hl.
  change (cells_bytes [CB 38 idb]) with (idb ++ []) in Hb. rewrite app_nil_r in Hb.
  change (Z.of_nat (cells_size [CB 38 idb])) with 38 in Hw.
  unfold ivs. split; [exact Hb|]. split; [exact Hw|]. split; [exact Hl|]. split; [exact Hp|]. split; [exact Hd|].
  split; [apply munch_refl|]. split; [apply wmono_refl|]. exact (fun H => H).
Qed.

Lemma ivs_rw_cells : forall m0 m id idb p pb,
  ivs m0 m id idb p pb -> rw_cells segs m id [CB 38 idb].
Proof.
  intros m0 m id idb p pb (Hb & Hw & Hl & _). unfold rw_cells, cells_at. split; [split|].
  - cbn. split; [exact Hl|exact I].
  - change (cells_bytes [CB 38 idb]) with (idb ++ []). rewrite app_nil_r. exact Hb.
  - change (Z.of_nat (cells_size [CB 38 idb])) with 38. exact Hw.
Qed.

Lemma ivs_store_ok : forall m0 m id idb p pb (k : Z) (n : nat),
  ivs m0 m id idb p pb -> 0 <= k -> k + Z.of_nat n <= 38 -> store_ok segs m (wa (id + k)) n = true.
Proof. intros m0 m id idb p pb k n (Hb & Hw & _) Hk Hn. apply (wr_at_store_ok segs m id 38 k n Hw); lia. Qed.

Lemma ivs_store : forall m0 m id idb p pb (k : Z) (bs : list byte),
  ivs m0 m id idb p pb -> 0 <= k -> k + Z.of_nat (length bs) <= 38 ->
  ivs m0 (write_to_mem m (wa (id + k)) bs) id (upd idb (Z.to_nat k) bs) p pb.
Proof.
  intros m0 m id idb p pb k bs (Hb & Hw & Hl & Hp & Hd & MU & WM & MI) Hk Hkb.
  pose proof (bytes_at_bound segs m id idb Hb) as [B0 B1]. rewrite Hl in B1.
  pose proof (bytes_at_bound segs m p pb Hp) as [P0 P1].
  unfold ivs. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - exact (bytes_at_write_inside segs m id idb k bs Hb Hk ltac:(lia)).
  - apply wr_at_write. exact Hw.
  - unfold upd. rewrite !length_app, length_firstn, length_skipn. lia.
  - apply bytes_at_write_other; [exact Hp | lia | lia | lia].
  - exact Hd.
  - apply munch_write; [exact MU | lia | lia | cbn [inside]; lia].
  - apply wmono_write. exact WM.
  - intros MI0. apply mem_inv_store; [exact (MI MI0)|]. apply (wr_at_store_ok segs m id 38 k (length bs) Hw); lia.
Qed.

Lemma ivs_post : forall m0 m id idb p pb,
  ivs m0 m id idb p pb -> munch [(id, id + 38)] m0 m /\ wmono segs m0 m /\ (mem_inv segs m0 -> mem_inv segs m).
Proof. intros m0 m id idb p pb (_ & _ & _ & _ & _ & MU & WM & MI). repeat split; assumption. Qed.

Lemma ivs_rdb : forall m0 m id idb p pb (i : nat),
  ivs m0 m id idb p pb -> (i < length pb)%nat ->
  ov_read_bytes segs m (wa (p + Z.of_nat i)) 1 = Some [nth i pb (Z_to_bv 8 0)].
Proof. intros m0 m id idb p pb i (_ & _ & _ & Hp & _) Hi. exact (rd_byte segs m p pb i Hp Hi). Qed.

End WithSegs.

Lemma zxb_u : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof. intros b. pose proof (byte_range b). unfold zxb. apply unsigned_lit. lia. Qed.

Lemma ii_ltu_lit : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma ii_eqb_lit : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma ii_ltu_zxb : forall k (b : byte), 0 <= k < 2^64 -> bv_ltu (Z_to_bv 64 k) (zxb b) = (k <? bv_unsigned b).
Proof. intros k b Hk. unfold bv_ltu. rewrite unsigned_lit by lia. rewrite zxb_u. reflexivity. Qed.

Lemma ii_eqb_zxb0 : forall b : byte, bv_eqb (zxb b) (Z_to_bv 64 0) = (bv_unsigned b =? 0).
Proof. intros b. unfold bv_eqb. rewrite zxb_u. reflexivity. Qed.

Lemma ii_neg : forall x, Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 x)) = Z_to_bv 64 (- x).
Proof.
  intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zminus_mod_idemp_r. reflexivity.
Qed.

Lemma ii_eqb_neg : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  bv_eqb (Z_to_bv 64 (- x)) (Z_to_bv 64 (- y)) = (x =? y).
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec x y) as [E|E]; [subst; apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E'. apply E.
  change (2^64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia.
Qed.

Lemma ii_eqb_neg0 : forall x, 0 <= x < 2^64 -> bv_eqb (Z_to_bv 64 (- x)) (Z_to_bv 64 0) = (x =? 0).
Proof.
  intros x Hx. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec x 0) as [E|E]; [subst; reflexivity|].
  apply Z.eqb_neq. intros E'. apply E.
  change (2^64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia.
Qed.

Lemma ii_snez : forall x, 0 < x < 2^64 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 x) = Z_to_bv 64 1.
Proof.
  intros x Hx. unfold v_sltu, c_ltu. rewrite ii_ltu_lit by lia.
  replace (0 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma ii_seqz : forall x, 0 < x < 2^64 -> v_sltiu (Z_to_bv 64 x) 1 = Z_to_bv 64 0.
Proof.
  intros x Hx. unfold v_sltiu. rewrite unsigned_lit by lia.
  replace (x <? bv_wrap 64 1) with false by (symmetry; apply Z.ltb_ge; change (bv_wrap 64 1) with 1; lia).
  reflexivity.
Qed.

Lemma ii_land1 : forall x, 0 <= x < 2^64 -> x mod 2 = 0 -> Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 x)) 1) = Z_to_bv 64 0.
Proof.
  intros x Hx H2. rewrite unsigned_lit by lia. change 1 with (Z.ones 1). rewrite Z.land_ones by lia.
  change (2^1) with 2. rewrite H2. reflexivity.
Qed.

Lemma ii_mod_neg : forall c, -2^64 <= c < 0 -> c mod 2^64 = c + 2^64.
Proof. intros c Hc. change (2^64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia. Qed.

Lemma ii_ltu_neg_lit : forall c x, -2^64 <= c < 0 -> 0 <= x < 2^64 ->
  bv_ltu (Z_to_bv 64 c) (Z_to_bv 64 x) = (c + 2^64 <? x).
Proof.
  intros c x Hc Hx. unfold bv_ltu. rewrite (unsigned_lit x) by lia. rewrite unsigned_lit_wrap, ii_mod_neg by lia.
  reflexivity.
Qed.

Lemma ii_eqb_neg_lit : forall x c, 0 <= x < 2^64 -> -2^64 <= c < 0 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 c) = (x =? c + 2^64).
Proof.
  intros x c Hx Hc. unfold bv_eqb. rewrite (unsigned_lit x) by lia. rewrite unsigned_lit_wrap, ii_mod_neg by lia.
  reflexivity.
Qed.

Lemma ii_land_le : forall a m, 0 <= a -> Z.land a m <= a.
Proof.
  intros a m Ha. apply Z.ldiff_le; [lia|].
  apply Z.bits_inj'. intros k Hk. rewrite Z.ldiff_spec, Z.land_spec, Z.bits_0.
  destruct (Z.testbit a k), (Z.testbit m k); reflexivity.
Qed.

Lemma ii_land_m2_ne : forall p c, 0 <= p -> p + 8 <= 2^64 -> -7 <= c <= -2 ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 p)) 18446744073709551614)) (Z_to_bv 64 c) = false.
Proof.
  intros p c Hp H8 Hc. rewrite (unsigned_lit p) by lia.
  pose proof (ii_land_le p 18446744073709551614 ltac:(lia)) as L.
  assert (N : 0 <= Z.land p 18446744073709551614) by (apply Z.land_nonneg; left; lia).
  rewrite ii_eqb_neg_lit by lia. apply Z.eqb_neq. lia.
Qed.

Lemma ii_xor_ne1 : forall i p, 0 <= i < 2^64 -> 0 <= p < 2^64 -> i + p < 2^64 - 1 ->
  bv_eqb (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 i)) (bv_unsigned (Z_to_bv 64 p)))) (Z_to_bv 64 (-1)) = false.
Proof.
  intros i p Hi Hp H. rewrite (unsigned_lit i), (unsigned_lit p) by lia.
  pose proof (Z_lxor_range i p Hi Hp) as R.
  rewrite ii_eqb_neg_lit by lia. apply Z.eqb_neq. intros E.
  assert (Ep : p = Z.lxor i (Z.lxor i p)) by (rewrite <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l; reflexivity).
  replace (-1 + 2^64) with 18446744073709551615 in E by reflexivity.
  rewrite E, zb_lxor_ones in Ep by lia. lia.
Qed.

Lemma rc_lor_shl8 : forall x y, 0 <= x -> 0 <= y < 256 -> Z.lor (Z.shiftl x 8) y = x * 256 + y.
Proof.
  intros x y Hx Hy.
  assert (Lg : Z.log2 y < 8).
  { destruct (Z.eq_dec y 0) as [->|Hy0]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
  assert (L : Z.land (Z.shiftl x 8) y = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8).
    - rewrite Z.shiftl_spec_low by lia. reflexivity.
    - rewrite (Z.bits_above_log2 y i) by lia. apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact L. rewrite <- Z.add_nocarry_lxor by exact L.
  rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma le2_pair : forall (v : word) (b0 b1 : byte),
  bv_unsigned v mod 65536 = bv_unsigned b0 + 256 * bv_unsigned b1 -> le2 v = [b0; b1].
Proof.
  intros v b0 b1 H. pose proof (byte_range b0). pose proof (byte_range b1).
  unfold le2. cbn [Z_to_le_bytes]. f_equal; [|f_equal].
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?a) with (a mod 2^8). change (2^8) with 256.
    Z.div_mod_to_equations. lia.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?a) with (a mod 2^8). change (2^8) with 256.
    rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256. Z.div_mod_to_equations. lia.
Qed.

Lemma le16_pair : forall (s : Z) (b0 b1 : byte), 0 <= s ->
  s mod 65536 = bv_unsigned b0 + 256 * bv_unsigned b1 -> le16 s = [b0; b1].
Proof.
  intros s b0 b1 Hs H. pose proof (byte_range b0). pose proof (byte_range b1).
  unfold le16, zb. f_equal; [|f_equal]; apply bv_eq; rewrite Z_to_bv_unsigned;
    change (bv_wrap 8 ?a) with (a mod 2^8); change (2^8) with 256; rewrite Z.mod_mod by lia;
    Z.div_mod_to_equations; lia.
Qed.

Lemma le16_be16 : forall hi lo : byte, le16 (be16 hi lo) = [lo; hi].
Proof.
  intros hi lo. pose proof (byte_range hi). pose proof (byte_range lo).
  apply le16_pair; unfold be16, bz; [lia|]. rewrite Z.mod_small by lia. lia.
Qed.

Lemma le2_le16 : forall s, 0 <= s < 2^64 -> le2 (Z_to_bv 64 s) = le16 s.
Proof.
  intros s Hs. unfold le16. unfold zb. apply le2_pair. rewrite unsigned_lit by lia.
  rewrite !Z_to_bv_unsigned. change (bv_wrap 8 ?a) with (a mod 2^8). change (2^8) with 256.
  rewrite !Z.mod_mod by lia. Z.div_mod_to_equations. lia.
Qed.

Lemma le1_lit : forall z, 0 <= z < 256 -> le1 (Z_to_bv 64 z) = [zb z].
Proof. intros z Hz. unfold le1, zb. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma le2_orshl : forall hi lo : byte,
  le2 (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb hi)) 8))) (bv_unsigned (zxb lo))))
  = [lo; hi].
Proof.
  intros hi lo. pose proof (byte_range hi). pose proof (byte_range lo).
  apply le2_pair. rewrite !zxb_u.
  rewrite (unsigned_lit (Z.shiftl (bv_unsigned hi) 8)) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^8) with 256; lia).
  rewrite rc_lor_shl8 by lia. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma upd_nil : forall (l : list byte) k, (k <= length l)%nat -> upd l k [] = l.
Proof. intros l k H. unfold upd. cbn [length app]. rewrite Nat.add_0_r. apply firstn_skipn. Qed.

Lemma upd_cat : forall (l a b : list byte) (k k' : nat), k' = (k + length a)%nat -> (k <= length l)%nat ->
  upd (upd l k a) k' b = upd l k (a ++ b).
Proof.
  intros l a b k k' -> H. unfold upd.
  assert (Lf : length (firstn k l) = k) by (rewrite length_firstn; lia).
  rewrite firstn_app, Lf, firstn_all2 by lia.
  replace (k + length a - k)%nat with (length a) by lia.
  rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r.
  rewrite skipn_app, Lf, skipn_all2 by lia.
  replace (k + length a + length b - k)%nat with (length a + length b)%nat by lia.
  rewrite skipn_app, skipn_all2 by lia.
  replace (length a + length b - length a)%nat with (length b) by lia.
  cbn [app]. rewrite skipn_skipn, length_app, <- !app_assoc.
  replace (length b + (k + length a))%nat with (k + (length a + length b))%nat by lia. reflexivity.
Qed.

Lemma firstn_snoc : forall (l : list byte) i, (i < length l)%nat -> firstn (S i) l = firstn i l ++ [nthb l i].
Proof.
  induction l as [|x l IH]; intros i Hi; cbn in Hi; [lia|].
  destruct i as [|i]; [reflexivity|].
  cbn [firstn]. rewrite IH by lia. reflexivity.
Qed.

Lemma firstn_nths : forall (l : list byte) n, (n <= length l)%nat -> firstn n l = map (nthb l) (seq 0 n).
Proof.
  intros l n. induction n as [|n IH]; intros H; [reflexivity|].
  rewrite firstn_snoc by lia. rewrite IH by lia. rewrite seq_S, map_app. reflexivity.
Qed.

Lemma nthb_skipn1 : forall (l : list byte) i, nthb (skipn 1 l) i = nthb l (1 + i).
Proof. intros [|x l] i; [destruct i; reflexivity|reflexivity]. Qed.

Lemma nth_firstn_lt : forall (l : list byte) n j d, (j < n)%nat -> nth j (firstn n l) d = nth j l d.
Proof.
  induction l as [|x l IH]; intros n j d H; destruct n as [|n]; try lia.
  - destruct j; reflexivity.
  - destruct j as [|j]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.

Lemma first_zero_hit : forall (l : list byte) i, (i < length l)%nat -> bz (nthb l i) = 0 ->
  (forall j, (j < i)%nat -> bz (nthb l j) <> 0) -> first_zero l = i.
Proof.
  induction l as [|x l IH]; intros i Hi Hz Hnz; cbn in Hi; [lia|].
  cbn [first_zero]. destruct i as [|i].
  - change (bz (nthb (x :: l) 0)) with (bz x) in Hz. rewrite Hz. reflexivity.
  - rewrite (proj2 (Z.eqb_neq (bz x) 0) (Hnz 0%nat ltac:(lia))). f_equal.
    apply IH; [lia | exact Hz | ]. intros j Hj. exact (Hnz (S j) ltac:(lia)).
Qed.

Lemma first_zero_none : forall (l : list byte), (forall j, (j < length l)%nat -> bz (nthb l j) <> 0) ->
  first_zero l = length l.
Proof.
  induction l as [|x l IH]; intros Hnz; [reflexivity|].
  cbn [first_zero length]. rewrite (proj2 (Z.eqb_neq (bz x) 0) (Hnz 0%nat ltac:(cbn; lia))).
  f_equal. apply IH. intros j Hj. exact (Hnz (S j) ltac:(cbn; lia)).
Qed.

Lemma nthb_fs1 : forall (l : list byte) n j, (j < n)%nat -> nthb (firstn n (skipn 1 l)) j = nthb l (1 + j).
Proof. intros l n j H. unfold nthb at 1. rewrite nth_firstn_lt by exact H. apply nthb_skipn1. Qed.

Lemma name_len_hit : forall (pb : list byte) i, (2 <= length pb)%nat -> (i < Nat.min (length pb - 1) 16)%nat ->
  bz (nthb pb (1 + i)) = 0 -> (forall j, (j < i)%nat -> bz (nthb pb (1 + j)) <> 0) -> name_len pb = i.
Proof.
  intros pb i H2 Hi Hz Hnz. unfold name_len. cbv zeta. change (NAME_CAP - 1)%nat with 16%nat.
  rewrite (first_zero_hit (firstn (Nat.min (length pb - 1) 16) (skipn 1 pb)) i).
  - lia.
  - rewrite length_firstn, length_skipn. lia.
  - rewrite nthb_fs1 by lia. exact Hz.
  - intros j Hj. rewrite nthb_fs1 by lia. apply Hnz. lia.
Qed.

Lemma name_len_full : forall (pb : list byte), (2 <= length pb)%nat ->
  (forall j, (j < Nat.min (length pb - 1) 16)%nat -> bz (nthb pb (1 + j)) <> 0) ->
  name_len pb = Nat.min (length pb - 1) 16.
Proof.
  intros pb H2 Hnz. unfold name_len. cbv zeta. change (NAME_CAP - 1)%nat with 16%nat.
  rewrite first_zero_none.
  - rewrite length_firstn, length_skipn. lia.
  - intros j Hj. rewrite length_firstn, length_skipn in Hj. rewrite nthb_fs1 by lia. apply Hnz. lia.
Qed.

Lemma ING_0 : forall idb pb, ING idb 0 pb = ing_firmware idb pb.
Proof. reflexivity. Qed.
Lemma ING_1536 : forall idb pb, ING idb 1536 pb = ing_version idb pb.
Proof. reflexivity. Qed.
Lemma ING_4096 : forall idb pb, ING idb 4096 pb = ing_name idb pb.
Proof. reflexivity. Qed.

Lemma ING_fw : forall idb pb, (4 <= length pb)%nat ->
  ING idb 0 pb =
  if (bz (nthb pb 0) <=? 9) && ((bz (nthb pb 1) <=? 9) && ((bz (nthb pb 2) <=? 9) && ((bz (nthb pb 3) <=? 9) && true)))
  then (1, upd (upd idb OFF_FW (le16 (fw_value pb))) OFF_HAS_FW [zb 1]) else (0, idb).
Proof.
  intros idb pb H. rewrite ING_0. unfold ing_firmware, all_digits.
  rewrite (firstn_nths pb 4) by lia. cbn [map seq forallb].
  replace (4 <=? length pb)%nat with true by (symmetry; apply Nat.leb_le; lia). reflexivity.
Qed.

Lemma ING_fw_short : forall idb pb, (length pb < 4)%nat -> ING idb 0 pb = (0, idb).
Proof.
  intros idb pb H. rewrite ING_0. unfold ing_firmware.
  replace (4 <=? length pb)%nat with false by (symmetry; apply Nat.leb_gt; lia). reflexivity.
Qed.

Lemma fw_bad : forall idb pb i, (4 <= length pb)%nat -> (i < 4)%nat -> 9 < bz (nthb pb i) -> ING idb 0 pb = (0, idb).
Proof.
  intros idb pb i H Hi Hb. rewrite ING_fw by exact H.
  destruct i as [|[|[|[|i]]]]; [| | | | lia];
    rewrite (proj2 (Z.leb_gt _ _) Hb); cbn [andb]; rewrite ?andb_false_r; reflexivity.
Qed.

Lemma ING_ver : forall idb pb, (8 <= length pb)%nat ->
  ING idb 1536 pb =
  (1, upd (upd (upd (upd (upd idb OFF_RAW [nthb pb 0; nthb pb 1; nthb pb 2; nthb pb 3; nthb pb 4; nthb pb 5;
                                         nthb pb 6; nthb pb 7])
                          OFF_MAJOR (le16 (be16 (nthb pb 2) (nthb pb 3))))
                     OFF_MINOR (le16 (be16 (nthb pb 4) (nthb pb 5))))
                OFF_PATCH (le16 (be16 (nthb pb 6) (nthb pb 7))))
          OFF_HAS_VER [zb 1]).
Proof.
  intros idb pb H. rewrite ING_1536.
  unfold ing_version, REAC_VER_LEN.
  replace (8 <=? length pb)%nat with true by (symmetry; apply Nat.leb_le; lia).
  rewrite (firstn_nths pb 8) by lia. reflexivity.
Qed.

Lemma ING_ver_short : forall idb pb, (length pb < 8)%nat -> ING idb 1536 pb = (0, idb).
Proof.
  intros idb pb H. rewrite ING_1536.
  unfold ing_version, REAC_VER_LEN.
  replace (8 <=? length pb)%nat with false by (symmetry; apply Nat.leb_gt; lia). reflexivity.
Qed.

Lemma ING_name : forall idb pb, (2 <= length pb)%nat -> (1 <= name_len pb)%nat ->
  ING idb 4096 pb = (1, upd (upd idb OFF_NAME (firstn (name_len pb) (skipn 1 pb) ++ [zb 0])) OFF_HAS_NAME [zb 1]).
Proof.
  intros idb pb H1 H2. rewrite ING_4096. unfold ing_name. cbv zeta.
  replace (2 <=? length pb)%nat with true by (symmetry; apply Nat.leb_le; lia).
  replace (1 <=? name_len pb)%nat with true by (symmetry; apply Nat.leb_le; lia). reflexivity.
Qed.

Lemma ING_name_zero : forall idb pb, (length pb < 2 \/ name_len pb = 0)%nat -> ING idb 4096 pb = (0, idb).
Proof.
  intros idb pb H. rewrite ING_4096. unfold ing_name. cbv zeta.
  destruct H as [H|H].
  - replace (2 <=? length pb)%nat with false by (symmetry; apply Nat.leb_gt; lia). reflexivity.
  - rewrite H. destruct (2 <=? length pb)%nat; reflexivity.
Qed.

Lemma ING_other : forall idb ad pb, ad <> 0 -> ad <> 4096 -> ad <> 1536 -> ING idb ad pb = (0, idb).
Proof.
  intros idb ad pb H0 H1 H2. unfold ING, ADDR_FIRMWARE, ADDR_MODEL_NAME, ADDR_REAC_VERSION.
  rewrite (proj2 (Z.eqb_neq ad 0) H0), (proj2 (Z.eqb_neq ad 4096) H1), (proj2 (Z.eqb_neq ad 1536) H2).
  reflexivity.
Qed.

Lemma ver_eq : forall (idb : list byte) (q0 q1 q2 q3 q4 q5 q6 q7 : byte), length idb = 38%nat ->
  upd (upd (upd (upd (upd idb OFF_RAW [q0; q1; q2; q3; q4; q5; q6; q7]) OFF_MAJOR (le16 (be16 q2 q3)))
                OFF_MINOR (le16 (be16 q4 q5))) OFF_PATCH (le16 (be16 q6 q7))) OFF_HAS_VER [zb 1]
  = upd (upd (upd (upd (upd (upd (upd (upd idb (Z.to_nat 28) [q0; q1]) (Z.to_nat 30) [q2; q3]) (Z.to_nat 32) [q4; q5])
                                (Z.to_nat 34) [q6; q7]) (Z.to_nat 22) [q3; q2]) (Z.to_nat 24) [q5; q4])
                (Z.to_nat 26) [q7; q6]) (Z.to_nat 36) [zb 1].
Proof.
  intros idb q0 q1 q2 q3 q4 q5 q6 q7 H. rewrite !le16_be16.
  do 38 (destruct idb as [|? idb]; [cbn in H; lia|]). destruct idb; [|cbn in H; lia].
  reflexivity.
Qed.

Lemma nth_skipn_ii : forall (l : list byte) n k d, nth k (skipn n l) d = nth (n + k) l d.
Proof.
  induction l as [|x l IH]; intros n k d.
  - destruct n, k; reflexivity.
  - destruct n as [|n]; [reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.

Lemma upd_len_full : forall (l : list byte) off bs,
  length (upd l off bs) = (Nat.min off (length l) + length bs + (length l - (off + length bs)))%nat.
Proof. intros l off bs. unfold upd. rewrite !length_app, length_firstn, length_skipn. lia. Qed.

Lemma nthb_upd_lt : forall l off bs k, (k < off)%nat -> (off <= length l)%nat -> nthb (upd l off bs) k = nthb l k.
Proof.
  intros l off bs k Hk Ho. unfold upd, nthb. rewrite app_nth1 by (rewrite length_firstn; lia).
  apply nth_firstn_lt. exact Hk.
Qed.

Lemma nthb_upd_in : forall l off bs k, (off <= k < off + length bs)%nat -> (off <= length l)%nat ->
  nthb (upd l off bs) k = nthb bs (k - off).
Proof.
  intros l off bs k Hk Ho. unfold upd, nthb. rewrite app_nth2 by (rewrite length_firstn; lia).
  rewrite length_firstn. replace (Nat.min off (length l)) with off by lia.
  rewrite app_nth1 by lia. reflexivity.
Qed.

Lemma nthb_upd_ge : forall l off bs k, (off + length bs <= k)%nat -> (off <= length l)%nat ->
  nthb (upd l off bs) k = nthb l k.
Proof.
  intros l off bs k Hk Ho. unfold upd, nthb. rewrite app_nth2 by (rewrite length_firstn; lia).
  rewrite length_firstn. replace (Nat.min off (length l)) with off by lia.
  rewrite app_nth2 by lia. rewrite nth_skipn_ii. f_equal. lia.
Qed.

Lemma nthb_cons0 : forall (x : byte) l, nthb (x :: l) 0 = x.
Proof. reflexivity. Qed.

Lemma nthb_cons : forall (x : byte) l k, nthb (x :: l) (S k) = nthb l k.
Proof. reflexivity. Qed.

Lemma length_le16 : forall v, length (le16 v) = 2%nat.
Proof. reflexivity. Qed.

Lemma bz_zb : forall z, 0 <= z < 256 -> bz (zb z) = z.
Proof.
  intros z Hz. unfold bz, zb. rewrite Z_to_bv_unsigned. change (bv_wrap 8 z) with (z mod 2^8). change (2^8) with 256.
  apply Z.mod_small. exact Hz.
Qed.

Lemma nthb_name_in : forall pb w (x : byte) j, (w <= length pb - 1)%nat -> (j < w)%nat ->
  nthb (firstn w (skipn 1 pb) ++ [x]) j = nthb pb (1 + j).
Proof.
  intros pb w x j Hw Hj. unfold nthb at 1. rewrite app_nth1 by (rewrite length_firstn, length_skipn; lia).
  rewrite nth_firstn_lt by exact Hj. apply nthb_skipn1.
Qed.

Lemma nthb_name_end : forall pb w (x : byte), (w <= length pb - 1)%nat ->
  nthb (firstn w (skipn 1 pb) ++ [x]) w = x.
Proof.
  intros pb w x Hw. unfold nthb. rewrite app_nth2 by (rewrite length_firstn, length_skipn; lia).
  rewrite length_firstn, length_skipn. replace (w - Nat.min w (length pb - 1))%nat with 0%nat by lia. reflexivity.
Qed.

Lemma name_len_le : forall pb, (name_len pb <= Nat.min (length pb - 1) 16)%nat.
Proof. intros pb. unfold name_len. cbv zeta. change (NAME_CAP - 1)%nat with 16%nat. lia. Qed.

Lemma name_len_pos : forall pb, (2 <= length pb)%nat -> (1 <= name_len pb)%nat -> bz (nthb pb 1) <> 0.
Proof.
  intros pb H2 H1 Hz.
  assert (name_len pb = 0%nat) by (apply name_len_hit; [lia | lia | exact Hz | intros j Hj; lia]). lia.
Qed.

Lemma fw_ok : forall pb, (4 <= length pb)%nat -> all_digits (firstn 4 pb) = true -> 0 <= fw_value pb <= 9999.
Proof.
  intros pb H A. unfold all_digits in A. rewrite (firstn_nths pb 4 H) in A. cbn [map seq forallb] in A.
  rewrite !andb_true_iff, !Z.leb_le in A. destruct A as (A0 & A1 & A2 & A3 & _).
  pose proof (byte_range (nthb pb 0)). pose proof (byte_range (nthb pb 1)).
  pose proof (byte_range (nthb pb 2)). pose proof (byte_range (nthb pb 3)).
  unfold fw_value, bz in *. lia.
Qed.

Ltac len_ii := rewrite ?upd_len_full, ?length_app, ?length_firstn, ?length_skipn, ?length_le16; cbn [length]; lia.

Ltac nb_step :=
  match goal with
  | |- context [nthb (upd ?l ?off ?bs) ?k] =>
      first [ rewrite (nthb_upd_lt l off bs k) by len_ii
            | rewrite (nthb_upd_in l off bs k) by len_ii
            | rewrite (nthb_upd_ge l off bs k) by len_ii ]
  end.

Ltac cl_simp :=
  repeat nb_step; cbn [Nat.sub];
  rewrite ?nthb_name_end by len_ii; rewrite ?nthb_name_in by len_ii; cbn [Nat.add];
  rewrite ?le16_be16; try unfold le16; rewrite ?nthb_cons0, ?nthb_cons;
  rewrite ?bz_zb by (Z.div_mod_to_equations; lia).

Ltac cl_fin :=
  cl_simp; intros; cl_simp;
  first [ assumption | solve [tauto] | lia | solve [eauto] | (unfold be16 in *; lia)
        | (Z.div_mod_to_equations; lia) ].

Ltac conj_split := repeat match goal with |- _ /\ _ => split end.

Lemma ING_id_ok : forall idb ad pb, length idb = ID_SIZE -> id_ok idb -> id_ok (snd (ING idb ad pb)).
Proof.
  intros idb ad pb L OK. unfold ID_SIZE in L. unfold ING.
  destruct (ad =? ADDR_FIRMWARE); [|destruct (ad =? ADDR_MODEL_NAME); [|destruct (ad =? ADDR_REAC_VERSION)]].
  - unfold ing_firmware. destruct ((4 <=? length pb)%nat && all_digits (firstn 4 pb)) eqn:C; cbn [snd]; [|exact OK].
    apply andb_true_iff in C. destruct C as [C1 C2]. apply Nat.leb_le in C1.
    pose proof (fw_ok pb C1 C2) as FV.
    unfold id_ok, has_fw, has_model_name, has_reac_version, fw_milli, major, minor, patch,
      OFF_FW, OFF_HAS_FW, OFF_HAS_NAME, OFF_HAS_VER in *.
    destruct OK as (F1 & F2 & F3 & N16 & NZ & N0 & FW0 & FW1 & V0 & V1 & P21 & P37).
    conj_split; cl_fin.
  - unfold ing_name. cbv zeta.
    destruct ((2 <=? length pb)%nat && (1 <=? name_len pb)%nat) eqn:C; cbn [snd]; [|exact OK].
    apply andb_true_iff in C. destruct C as [C1 C2]. apply Nat.leb_le in C1, C2.
    pose proof (name_len_le pb) as WL. pose proof (name_len_pos pb C1 C2) as P1.
    unfold id_ok, has_fw, has_model_name, has_reac_version, fw_milli, major, minor, patch,
      OFF_NAME, OFF_HAS_FW, OFF_HAS_NAME, OFF_HAS_VER in *.
    destruct OK as (F1 & F2 & F3 & N16 & NZ & N0 & FW0 & FW1 & V0 & V1 & P21 & P37).
    destruct (Nat.eq_dec (name_len pb) 16) as [E16|E16]; [rewrite E16 in *|]; conj_split; cl_fin.
  - unfold ing_version, REAC_VER_LEN. destruct (8 <=? length pb)%nat eqn:C; cbn [snd]; [|exact OK].
    apply Nat.leb_le in C. rewrite (firstn_nths pb 8 C). cbn [map seq].
    unfold id_ok, has_fw, has_model_name, has_reac_version, fw_milli, major, minor, patch,
      OFF_RAW, OFF_MAJOR, OFF_MINOR, OFF_PATCH, OFF_HAS_FW, OFF_HAS_NAME, OFF_HAS_VER in *.
    destruct OK as (F1 & F2 & F3 & N16 & NZ & N0 & FW0 & FW1 & V0 & V1 & P21 & P37).
    conj_split; cl_fin.
  - exact OK.
Qed.

Ltac ivs_after IV k :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m ?a ?bs) ?ro) =>
    lazymatch type of IV with
    | ivs _ ?m0 m ?id ?idb ?p ?pb =>
      replace (write_to_mem m a bs) with (write_to_mem m (wa (id + k)) bs) by (f_equal; unfold wa; word_eq_tac);
      let IV' := fresh "IV" in
      pose proof (ivs_store segs m0 m id idb p pb k bs IV ltac:(lia)
                    ltac:(rewrite ?length_le2, ?length_le1; cbn [length]; lia)) as IV';
      clear IV;
      let m' := fresh "m" in
      remember (write_to_mem m (wa (id + k)) bs) as m' eqn:Heqm; clear Heqm;
      rename IV' into IV
    end
  end.

Ltac ivs_sok IV k n :=
  lazymatch type of IV with
  | ivs ?segs ?m0 ?m ?id ?idb ?p ?pb =>
      let SO := fresh "SO" in
      pose proof (ivs_store_ok segs m0 m id idb p pb k n IV ltac:(lia) ltac:(lia)) as SO
  end.
