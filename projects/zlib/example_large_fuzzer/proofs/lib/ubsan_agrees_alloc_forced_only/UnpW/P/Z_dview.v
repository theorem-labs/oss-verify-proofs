(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition zseq (n : Z) : list Z := map Z.of_nat (seq 0 (Z.to_nat n)).

Lemma zseq_length : forall n, length (zseq n) = Z.to_nat n.
Proof. intros. unfold zseq. rewrite length_map, length_seq. reflexivity. Qed.

Lemma zseq_nth : forall n i, 0 <= i < n -> nth_error (zseq n) (Z.to_nat i) = Some i.
Proof.
  intros n i H. unfold zseq. rewrite nth_error_map.
  rewrite (nth_error_nth' _ 0%nat) by (rewrite length_seq; lia).
  rewrite seq_nth by lia. cbn. f_equal. lia.
Qed.

Lemma map_zseq_nth : forall {X} (f : Z -> X) n i, 0 <= i < n -> nth_error (map f (zseq n)) (Z.to_nat i) = Some (f i).
Proof. intros X f n i H. rewrite nth_error_map, zseq_nth by exact H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma list_ext_nth : forall {X} (l1 l2 : list X), length l1 = length l2 ->
  (forall k, (k < length l1)%nat -> nth_error l1 k = nth_error l2 k) -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] HL H; cbn in HL; try lia; [reflexivity|].
  f_equal.
  - specialize (H 0%nat ltac:(cbn; lia)). cbn in H. congruence.
  - apply IH; [lia|]. intros k Hk. apply (H (S k)). cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma upd_map_zseq : forall {X} (f g : Z -> X) n i x, 0 <= i < n ->
  g i = x -> (forall j, 0 <= j < n -> j <> i -> g j = f j) ->
  upd (map f (zseq n)) (Z.to_nat i) x = map g (zseq n).
Proof.
  intros X f g n i x Hi Gi Gj. apply list_ext_nth.
  - rewrite upd_length, !length_map. reflexivity.
  - intros k Hk. rewrite upd_length, length_map, zseq_length in Hk.
    replace k with (Z.to_nat (Z.of_nat k)) by lia.
    rewrite (map_zseq_nth g n (Z.of_nat k)) by lia.
    destruct (Nat.eq_dec (Z.to_nat (Z.of_nat k)) (Z.to_nat i)) as [E|NE].
    + rewrite E, nth_error_upd_same by (rewrite length_map, zseq_length; lia).
      replace (Z.of_nat k) with i by lia. congruence.
    + rewrite nth_error_upd_other by (intros E; apply NE; symmetry; exact E).
      rewrite (map_zseq_nth f n (Z.of_nat k)) by lia. f_equal. symmetry. apply Gj; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma le2_wz_mod : forall (w : word) v, bv_unsigned w mod 2^16 = v mod 2^16 -> le2 w = le2 (wz v).
Proof.
  intros w v H. unfold le2. rewrite <- (Z_to_le_bytes_mod 2 (bv_unsigned w) 16), <- (Z_to_le_bytes_mod 2 (bv_unsigned (wz v)) 16) by (cbn; lia).
  f_equal. rewrite H. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^16 * 2^48). rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z.mod_add by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma le4_wz_mod : forall (w : word) v, bv_unsigned w mod 2^32 = v mod 2^32 -> le4 w = le4 (wz v).
Proof.
  intros w v H. unfold le4. rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned w) 32), <- (Z_to_le_bytes_mod 4 (bv_unsigned (wz v)) 32) by (cbn; lia).
  f_equal. rewrite H. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^32 * 2^32). rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z.mod_add by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma u16s_upd_le2 : forall ws i (w w' : word), le2 w = le2 w' -> u16s (upd ws i w) = u16s (upd ws i w').
Proof.
  induction ws as [|x ws IH]; intros [|i] w w' E; cbn [upd u16s]; try reflexivity.
  - rewrite E. reflexivity.
  - rewrite (IH i w w' E). reflexivity.
Qed.

Lemma u32s_upd_le4 : forall ws i (w w' : word), le4 w = le4 w' -> u32s (upd ws i w) = u32s (upd ws i w').
Proof.
  induction ws as [|x ws IH]; intros [|i] w w' E; cbn [upd u32s]; try reflexivity.
  - rewrite E. reflexivity.
  - rewrite (IH i w w' E). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition av8 (a : arr) (n : Z) : list byte := map (fun i => Z_to_bv 8 (arr_get a i)) (zseq n).
Definition av16 (a : arr) (n : Z) : list word := map (fun i => wz (arr_get a i)) (zseq n).
Definition av32 (a : arr) (n : Z) : list word := map (fun i => wz (arr_get a i)) (zseq n).
(* [comment removed for export] *)
Definition ctw (fc dl : arr) (k : Z) : word := wz (if Z.even k then arr_get fc (k / 2) else arr_get dl (k / 2)).
Definition avct (fc dl : arr) (n : Z) : list word := map (ctw fc dl) (zseq (2 * n)).

Lemma av8_length : forall a n, length (av8 a n) = Z.to_nat n.
Proof. intros. unfold av8. rewrite length_map. apply zseq_length. Qed.
Lemma av16_length : forall a n, length (av16 a n) = Z.to_nat n.
Proof. intros. unfold av16. rewrite length_map. apply zseq_length. Qed.
Lemma av32_length : forall a n, length (av32 a n) = Z.to_nat n.
Proof. intros. unfold av32. rewrite length_map. apply zseq_length. Qed.
Lemma avct_length : forall fc dl n, length (avct fc dl n) = Z.to_nat (2 * n).
Proof. intros. unfold avct. rewrite length_map. apply zseq_length. Qed.

(* [comment removed for export] *)
Lemma av8_zlength : forall a n, 0 <= n -> Z.of_nat (length (av8 a n)) = n.
Proof. intros. rewrite av8_length. lia. Qed.
Lemma av16_zlength : forall a n, 0 <= n -> Z.of_nat (length (u16s (av16 a n))) = 2 * n.
Proof. intros. rewrite u16s_length, av16_length. lia. Qed.
Lemma av32_zlength : forall a n, 0 <= n -> Z.of_nat (length (av32 a n)) = n.
Proof. intros. rewrite av32_length. lia. Qed.
Lemma avct_zlength : forall fc dl n, 0 <= n -> Z.of_nat (length (u16s (avct fc dl n))) = 4 * n.
Proof. intros. rewrite u16s_length, avct_length. lia. Qed.

Lemma av8_nth : forall a n i, 0 <= i < n -> nth_error (av8 a n) (Z.to_nat i) = Some (Z_to_bv 8 (arr_get a i)).
Proof. intros. unfold av8. apply (map_zseq_nth (fun i => Z_to_bv 8 (arr_get a i))). assumption. Qed.
Lemma av16_nth : forall a n i, 0 <= i < n -> nth_error (av16 a n) (Z.to_nat i) = Some (wz (arr_get a i)).
Proof. intros. unfold av16. apply (map_zseq_nth (fun i => wz (arr_get a i))). assumption. Qed.
Lemma av32_nth : forall a n i, 0 <= i < n -> nth_error (av32 a n) (Z.to_nat i) = Some (wz (arr_get a i)).
Proof. intros. unfold av32. apply (map_zseq_nth (fun i => wz (arr_get a i))). assumption. Qed.

Lemma ctw_fc : forall fc dl i, ctw fc dl (2 * i) = wz (arr_get fc i).
Proof.
  intros. unfold ctw. rewrite Z.even_mul. cbn [Z.even orb].
  replace (2 * i / 2) with i by (rewrite Z.mul_comm, Z.div_mul; lia). reflexivity.
Qed.
Lemma ctw_dl : forall fc dl i, ctw fc dl (2 * i + 1) = wz (arr_get dl i).
Proof.
  intros. unfold ctw. rewrite Z.even_add, Z.even_mul. cbn [Z.even orb Bool.eqb].
  replace ((2 * i + 1) / 2) with i by (rewrite Z.mul_comm, Z.div_add_l by lia; change (1 / 2) with 0; lia). reflexivity.
Qed.

Lemma avct_nth_fc : forall fc dl n i, 0 <= i < n ->
  nth_error (avct fc dl n) (Z.to_nat (2 * i)) = Some (wz (arr_get fc i)).
Proof. intros. unfold avct. rewrite (map_zseq_nth (ctw fc dl)) by lia. rewrite ctw_fc. reflexivity. Qed.
Lemma avct_nth_dl : forall fc dl n i, 0 <= i < n ->
  nth_error (avct fc dl n) (Z.to_nat (2 * i + 1)) = Some (wz (arr_get dl i)).
Proof. intros. unfold avct. rewrite (map_zseq_nth (ctw fc dl)) by lia. rewrite ctw_dl. reflexivity. Qed.

(* [comment removed for export] *)
Lemma av8_upd : forall a n i v, 0 <= i < n -> n <= arr_len a ->
  upd (av8 a n) (Z.to_nat i) (Z_to_bv 8 v) = av8 (arr_set a i v) n.
Proof.
  intros a n i v Hi Hn. unfold av8. apply upd_map_zseq; [exact Hi| |].
  - rewrite arr_get_set_same by lia. reflexivity.
  - intros j Hj Hne. rewrite arr_get_set_other by lia. reflexivity.
Qed.
Lemma av16_upd : forall a n i v, 0 <= i < n -> n <= arr_len a ->
  upd (av16 a n) (Z.to_nat i) (wz v) = av16 (arr_set a i v) n.
Proof.
  intros a n i v Hi Hn. unfold av16. apply upd_map_zseq; [exact Hi| |].
  - rewrite arr_get_set_same by lia. reflexivity.
  - intros j Hj Hne. rewrite arr_get_set_other by lia. reflexivity.
Qed.
Lemma av32_upd : forall a n i v, 0 <= i < n -> n <= arr_len a ->
  upd (av32 a n) (Z.to_nat i) (wz v) = av32 (arr_set a i v) n.
Proof. exact av16_upd. Qed.

Lemma even_div2_cases : forall j, 0 <= j -> (Z.even j = true /\ j = 2 * (j / 2)) \/ (Z.even j = false /\ j = 2 * (j / 2) + 1).
Proof.
  intros j Hj. pose proof (Z.div_mod j 2 ltac:(lia)) as D. pose proof (Z.mod_pos_bound j 2 ltac:(lia)) as R.
  rewrite Zeven_mod. destruct (Z.eqb_spec (j mod 2) 0); [left| right]; split; try reflexivity; lia.
Qed.

Lemma avct_upd_fc : forall fc dl n i v, 0 <= i < n -> n <= arr_len fc ->
  upd (avct fc dl n) (Z.to_nat (2 * i)) (wz v) = avct (arr_set fc i v) dl n.
Proof.
  intros fc dl n i v Hi Hn. unfold avct. apply upd_map_zseq; [lia| |].
  - rewrite ctw_fc, arr_get_set_same by lia. reflexivity.
  - intros j Hj Hne. unfold ctw. destruct (even_div2_cases j ltac:(lia)) as [[E D]|[E D]]; rewrite E; [|reflexivity].
    rewrite arr_get_set_other by lia. reflexivity.
Qed.
Lemma avct_upd_dl : forall fc dl n i v, 0 <= i < n -> n <= arr_len dl ->
  upd (avct fc dl n) (Z.to_nat (2 * i + 1)) (wz v) = avct fc (arr_set dl i v) n.
Proof.
  intros fc dl n i v Hi Hn. unfold avct. apply upd_map_zseq; [lia| |].
  - rewrite ctw_dl, arr_get_set_same by lia. reflexivity.
  - intros j Hj Hne. unfold ctw. destruct (even_div2_cases j ltac:(lia)) as [[E D]|[E D]]; rewrite E; [reflexivity|].
    rewrite arr_get_set_other by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma arr_slice_nat_nth_error : forall {X} n (a : parr X) ofs k, (k < n)%nat ->
  nth_error (arr_slice_nat a ofs n) k = Some (arr_get a (ofs + Z.of_nat k)).
Proof.
  induction n as [|n IH]; intros a ofs k Hk; [lia|]. cbn [arr_slice_nat]. destruct k as [|k]; cbn [nth_error].
  - f_equal. f_equal. lia.
  - rewrite IH by lia. f_equal. f_equal. lia.
Qed.

Lemma av8_slice : forall a N k n, 0 <= k -> 0 <= n -> k + n <= N ->
  firstn (Z.to_nat n) (skipn (Z.to_nat k) (av8 a N)) = map (Z_to_bv 8) (arr_slice a k n).
Proof.
  intros a N k n Hk Hn HN. apply list_ext_nth.
  - rewrite length_firstn, length_skipn, av8_length, length_map. unfold arr_slice. rewrite arr_slice_nat_length. lia.
  - intros j Hj. rewrite length_firstn, length_skipn, av8_length in Hj.
    rewrite nth_error_firstn. destruct (Nat.ltb_spec j (Z.to_nat n)) as [Hjn|]; [|lia].
    rewrite nth_error_skipn. replace (Z.to_nat k + j)%nat with (Z.to_nat (k + Z.of_nat j)) by lia.
    rewrite av8_nth by lia. rewrite nth_error_map. unfold arr_slice. rewrite arr_slice_nat_nth_error by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma av8_write : forall m A a n i (b : byte) v,
  u8arr psegs m A (av8 a n) -> 0 <= i < n -> n <= arr_len a -> b = Z_to_bv 8 v ->
  u8arr psegs (write_to_mem m (wa (A + i)) [b]) A (av8 (arr_set a i v) n).
Proof.
  intros m A a n i b v ARR Hi Hn ->. rewrite <- av8_upd by assumption.
  apply u8arr_write; [exact ARR|]. rewrite av8_length. lia.
Qed.

Lemma av16_write : forall m A a n i (w : word) v,
  u16arr psegs m A (av16 a n) -> 0 <= i < n -> n <= arr_len a -> le2 w = le2 (wz v) ->
  u16arr psegs (write_to_mem m (wa (A + 2 * i)) (le2 w)) A (av16 (arr_set a i v) n).
Proof.
  intros m A a n i w v ARR Hi Hn E. rewrite <- av16_upd by assumption.
  unfold u16arr. rewrite <- (u16s_upd_le2 _ _ w (wz v) E).
  apply (u16arr_write psegs); [exact ARR|]. rewrite av16_length. lia.
Qed.

Lemma av32_write : forall m A a n i (w : word) v,
  u32arr psegs m A (av32 a n) -> 0 <= i < n -> n <= arr_len a -> le4 w = le4 (wz v) ->
  u32arr psegs (write_to_mem m (wa (A + 4 * i)) (le4 w)) A (av32 (arr_set a i v) n).
Proof.
  intros m A a n i w v ARR Hi Hn E. rewrite <- av32_upd by assumption.
  pose proof (u32arr_write psegs m A (av32 a n) i w ARR ltac:(rewrite av32_length; lia)) as W.
  unfold u32arr in *. rewrite <- (u32s_upd_le4 _ _ w (wz v) E). rewrite upd_length in *. exact W.
Qed.

Lemma avct_write_fc : forall m A fc dl n i (w : word) v,
  u16arr psegs m A (avct fc dl n) -> 0 <= i < n -> n <= arr_len fc -> le2 w = le2 (wz v) ->
  u16arr psegs (write_to_mem m (wa (A + 2 * (2 * i))) (le2 w)) A (avct (arr_set fc i v) dl n).
Proof.
  intros m A fc dl n i w v ARR Hi Hn E. rewrite <- avct_upd_fc by assumption.
  unfold u16arr. rewrite <- (u16s_upd_le2 _ _ w (wz v) E).
  apply (u16arr_write psegs); [exact ARR|]. rewrite avct_length. lia.
Qed.

Lemma avct_write_dl : forall m A fc dl n i (w : word) v,
  u16arr psegs m A (avct fc dl n) -> 0 <= i < n -> n <= arr_len dl -> le2 w = le2 (wz v) ->
  u16arr psegs (write_to_mem m (wa (A + 2 * (2 * i + 1))) (le2 w)) A (avct fc (arr_set dl i v) n).
Proof.
  intros m A fc dl n i w v ARR Hi Hn E. rewrite <- avct_upd_dl by assumption.
  unfold u16arr. rewrite <- (u16s_upd_le2 _ _ w (wz v) E).
  apply (u16arr_write psegs); [exact ARR|]. rewrite avct_length. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition agree_on (lo hi : Z) (m m' : mem) : Prop :=
  forall a, lo <= a < hi -> m' (wa a) = m (wa a) /\ (wview psegs m (wa a) <> None -> wview psegs m' (wa a) <> None).

Lemma agree_on_sub : forall lo hi lo' hi' m m', agree_on lo hi m m' -> lo <= lo' -> hi' <= hi -> agree_on lo' hi' m m'.
Proof. intros lo hi lo' hi' m m' H H1 H2 a Ha. apply H. lia. Qed.

Lemma bytes_at_agree : forall m m' A bs, bytes_at psegs m A bs -> agree_on A (A + Z.of_nat (length bs)) m m' -> bytes_at psegs m' A bs.
Proof.
  intros m m' A bs (H1 & H2 & H) AG. split; [exact H1|]. split; [exact H2|].
  intros i Hi. rewrite <- (H i Hi). unfold mrd. destruct (AG (A + Z.of_nat i) ltac:(lia)) as [E _]. rewrite E. reflexivity.
Qed.

Lemma wr_at_agree : forall m m' A n, wr_at psegs m A n -> agree_on A (A + n) m m' -> wr_at psegs m' A n.
Proof.
  intros m m' A n (H1 & H2 & H) AG. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (AG (A + i) ltac:(lia)) as [_ W]. apply W, H, Hi.
Qed.

Lemma rw_cells_agree : forall m m' A cs, rw_cells psegs m A cs -> agree_on A (A + Z.of_nat (cells_size cs)) m m' -> rw_cells psegs m' A cs.
Proof.
  intros m m' A cs [[Hwf Hb] Hw] AG. split; [split; [exact Hwf|]|].
  - apply (bytes_at_agree m); [exact Hb|]. rewrite cells_bytes_length by exact Hwf. exact AG.
  - apply (wr_at_agree m); assumption.
Qed.

Lemma u8arr_agree : forall m m' A bs, u8arr psegs m A bs -> agree_on A (A + Z.of_nat (length bs)) m m' -> u8arr psegs m' A bs.
Proof. intros m m' A bs [Hb Hw] AG. split; [apply (bytes_at_agree m)| apply (wr_at_agree m)]; assumption. Qed.

Lemma u16arr_agree : forall m m' A ws, u16arr psegs m A ws -> agree_on A (A + 2 * Z.of_nat (length ws)) m m' -> u16arr psegs m' A ws.
Proof.
  intros m m' A ws H AG. unfold u16arr in *. apply (u8arr_agree m); [exact H|].
  rewrite u16s_length. replace (Z.of_nat (2 * length ws)) with (2 * Z.of_nat (length ws)) by lia. exact AG.
Qed.

Lemma u32arr_agree : forall m m' A ws, u32arr psegs m A ws -> agree_on A (A + 4 * Z.of_nat (length ws)) m m' -> u32arr psegs m' A ws.
Proof.
  intros m m' A ws [Hb Hw] AG. split.
  - apply (bytes_at_agree m); [exact Hb|]. rewrite u32s_length. replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws)) by lia. exact AG.
  - apply (wr_at_agree m); assumption.
Qed.

(* [comment removed for export] *)
Lemma agree_on_munch : forall W m m' lo hi, munch W m m' -> wmono psegs m m' -> 0 <= lo -> hi <= 2^64 ->
  disjoint_from W lo (hi - lo) -> agree_on lo hi m m'.
Proof.
  intros W m m' lo hi MU WM Hlo Hhi D a Ha. split; [|apply WM].
  apply MU. rewrite wa_unsigned by lia. eapply disjoint_outside; [exact D| lia].
Qed.

(* [comment removed for export] *)
Lemma u16arr_transport : forall W m m' A ws,
  u16arr psegs m A ws -> munch W m m' -> wmono psegs m m' ->
  disjoint_from W A (2 * Z.of_nat (length ws)) -> u16arr psegs m' A ws.
Proof.
  intros W m m' A ws H MU WM D. unfold u16arr in *. eapply u8arr_transport; eauto.
  rewrite u16s_length. replace (Z.of_nat (2 * length ws)) with (2 * Z.of_nat (length ws)) by lia. exact D.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wr_at_app : forall m a n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at psegs m a (n1 + n2) <-> wr_at psegs m a n1 /\ wr_at psegs m (a + n1) n2.
Proof.
  intros m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i) with (a + (n1 + i)) by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i) with (a + n1 + (i - n1)) by lia. apply HB. lia.
Qed.

Lemma u8arr_app : forall m A b1 b2,
  u8arr psegs m A (b1 ++ b2) <-> u8arr psegs m A b1 /\ u8arr psegs m (A + Z.of_nat (length b1)) b2.
Proof.
  intros m A b1 b2. unfold u8arr. rewrite bytes_at_app, length_app, Nat2Z.inj_add, wr_at_app by lia. tauto.
Qed.

(* [comment removed for export] *)
Lemma u8arr_sub_bytes : forall m A bs (k n : nat), u8arr psegs m A bs -> (k + n <= length bs)%nat ->
  bytes_at psegs m (A + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m A bs k n [Hb _] Hk.
  rewrite <- (firstn_skipn k bs) in Hb. apply bytes_at_app in Hb. destruct Hb as [_ Hb].
  rewrite length_firstn, Nat.min_l in Hb by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in Hb. apply bytes_at_app in Hb. exact (proj1 Hb).
Qed.

(* [comment removed for export] *)
Lemma u8arr_split3 : forall m A bs (k n : nat), u8arr psegs m A bs -> (k + n <= length bs)%nat ->
  u8arr psegs m A (firstn k bs)
  /\ rw_cells psegs m (A + Z.of_nat k) [CB n (firstn n (skipn k bs))]
  /\ u8arr psegs m (A + Z.of_nat k + Z.of_nat n) (skipn (k + n) bs).
Proof.
  intros m A bs k n H Hk.
  rewrite <- (firstn_skipn k bs) in H. apply u8arr_app in H. destruct H as [H1 H2].
  rewrite length_firstn, Nat.min_l in H2 by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H2. apply u8arr_app in H2. destruct H2 as [H2 H3].
  rewrite length_firstn, Nat.min_l in H3 by (rewrite length_skipn; lia). rewrite skipn_skipn in H3.
  replace (n + k)%nat with (k + n)%nat in H3 by lia.
  split; [exact H1|]. split; [|exact H3].
  apply rw_cells_of_u8arr in H2. rewrite length_firstn, Nat.min_l in H2 by (rewrite length_skipn; lia). exact H2.
Qed.

Lemma u8arr_join3 : forall m A (b1 b2 b3 : list byte) (n : nat),
  u8arr psegs m A b1 -> rw_cells psegs m (A + Z.of_nat (length b1)) [CB n b2] ->
  u8arr psegs m (A + Z.of_nat (length b1) + Z.of_nat n) b3 -> u8arr psegs m A (b1 ++ b2 ++ b3).
Proof.
  intros m A b1 b2 b3 n H1 H2 H3. apply u8arr_app. split; [exact H1|].
  assert (E : length b2 = n) by (destruct H2 as [[[E _] _] _]; exact E).
  apply u8arr_app. split; [apply (u8arr_of_rw_cells psegs _ _ n); exact H2|]. rewrite E. exact H3.
Qed.

Lemma u8arr_join3k : forall m A (b1 b2 b3 : list byte) (k n : nat), length b1 = k ->
  u8arr psegs m A b1 -> rw_cells psegs m (A + Z.of_nat k) [CB n b2] ->
  u8arr psegs m (A + Z.of_nat k + Z.of_nat n) b3 -> u8arr psegs m A (b1 ++ b2 ++ b3).
Proof. intros m A b1 b2 b3 k n <-. apply u8arr_join3. Qed.

(* [comment removed for export] *)
Global Opaque zseq.
