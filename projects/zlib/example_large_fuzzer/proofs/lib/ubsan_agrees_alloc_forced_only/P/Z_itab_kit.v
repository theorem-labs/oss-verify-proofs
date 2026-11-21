(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_ikit Zh_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState Inftrees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma upd_app_mid : forall {X} (pre : list X) y post x, upd (pre ++ y :: post) (length pre) x = pre ++ x :: post.
Proof. induction pre as [|p pre IH]; intros; cbn [app length upd]; [reflexivity| rewrite IH; reflexivity]. Qed.

Lemma upd_upd : forall {X} (l : list X) i x y, upd (upd l i x) i y = upd l i y.
Proof. induction l as [|a l IH]; intros [|i] x y; cbn [upd]; try reflexivity. rewrite IH. reflexivity. Qed.

Lemma u32arr_write_part : forall m A ws (i : Z) (w w' : word) (k : nat) (xs : list byte),
  u32arr psegs m A ws -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i ->
  (k + length xs <= 4)%nat ->
  le4 w' = firstn k (le4 w) ++ xs ++ skipn (k + length xs) (le4 w) ->
  u32arr psegs (write_to_mem m (wa (A + (4 * i + Z.of_nat k))) xs) A (upd ws (Z.to_nat i) w').
Proof.
  intros m A ws i w w' k xs [Hb Hw] Hn Hi Hk E.
  pose proof (nth_error_lt _ _ _ Hn) as Hlt.
  destruct (u32s_split _ _ _ Hn) as (pre & post & Ews & Hlen & Eu & Hlu).
  split.
  - eapply bytes_at_ext.
    { apply (bytes_at_write_inside psegs m A (u32s ws) (4 * i + Z.of_nat k) xs Hb); [lia|]. rewrite u32s_length. lia. }
    rewrite Ews at 2. rewrite <- Hlen, upd_app_mid, u32s_app. cbn [u32s]. rewrite E, Eu.
    pose proof (length_le4 w) as L4.
    set (b1 := firstn k (le4 w)). set (b3 := skipn (k + length xs) (le4 w)).
    set (b2 := firstn (length xs) (skipn k (le4 w))).
    assert (E4 : le4 w = b1 ++ b2 ++ b3).
    { subst b1 b2 b3. rewrite <- (firstn_skipn k (le4 w)) at 1. f_equal.
      rewrite <- (firstn_skipn (length xs) (skipn k (le4 w))) at 1. f_equal. rewrite skipn_skipn. f_equal. lia. }
    assert (L1 : length b1 = k) by (subst b1; rewrite length_firstn; lia).
    assert (L2 : length b2 = length xs) by (subst b2; rewrite length_firstn, length_skipn; lia).
    rewrite E4. replace (Z.to_nat (4 * i + Z.of_nat k)) with (length (u32s pre ++ b1)) by (rewrite length_app; lia).
    replace (u32s pre ++ (b1 ++ b2 ++ b3) ++ u32s post) with ((u32s pre ++ b1) ++ b2 ++ (b3 ++ u32s post)) by (rewrite <- !app_assoc; reflexivity).
    rewrite upd_bytes_mid by (symmetry; exact L2). rewrite <- !app_assoc. reflexivity.
  - rewrite upd_length. apply wr_at_write. exact Hw.
Qed.

Definition put_b0 (c v : Z) : Z := c - c mod 256 + v mod 256.
Definition put_b1 (c v : Z) : Z := c - (c / 256 mod 256) * 256 + (v mod 256) * 256.
Definition put_h1 (c v : Z) : Z := c mod 65536 + (v mod 65536) * 65536.
Definition put_h0 (c v : Z) : Z := c - c mod 65536 + v mod 65536.

Lemma put_b0_range : forall c v, 0 <= c < 2^32 -> 0 <= put_b0 c v < 2^32.
Proof. intros c v H. unfold put_b0. change (2^32) with 4294967296 in *. Z.div_mod_to_equations. lia. Qed.
Lemma put_b1_range : forall c v, 0 <= c < 2^32 -> 0 <= put_b1 c v < 2^32.
Proof. intros c v H. unfold put_b1. change (2^32) with 4294967296 in *. Z.div_mod_to_equations. lia. Qed.
Lemma put_h1_range : forall c v, 0 <= put_h1 c v < 2^32.
Proof. intros c v. unfold put_h1. change (2^32) with 4294967296 in *. Z.div_mod_to_equations. lia. Qed.
Lemma put_h0_range : forall c v, 0 <= c < 2^32 -> 0 <= put_h0 c v < 2^32.
Proof. intros c v H. unfold put_h0. change (2^32) with 4294967296 in *. Z.div_mod_to_equations. lia. Qed.

Lemma put3_pack : forall c op bits val, put_h1 (put_b1 (put_b0 c op) bits) val = code_pack op bits val.
Proof.
  intros. unfold put_h1, put_b1, put_b0, code_pack. rewrite !wrap8_mod, wrap16_mod.
  change (2^8) with 256. change (2^16) with 65536. Z.div_mod_to_equations. lia.
Qed.
Lemma put2_pack : forall c lo val, 0 <= lo < 65536 -> put_h1 (put_h0 c lo) val = code_pack (lo mod 256) (lo / 256) val.
Proof.
  intros. unfold put_h1, put_h0, code_pack. rewrite !wrap8_mod, wrap16_mod.
  change (2^8) with 256. change (2^16) with 65536. Z.div_mod_to_equations. lia.
Qed.

Lemma Z8_eqm' : forall x y, x mod 256 = y mod 256 -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof. intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. exact H. Qed.

Lemma le4_wz_bytes : forall c, 0 <= c < 2^32 ->
  le4 (wz c) = [Z_to_bv 8 c; Z_to_bv 8 (c / 256); Z_to_bv 8 (c / 65536); Z_to_bv 8 (c / 16777216)].
Proof.
  intros c Hc. unfold le4. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  rewrite !Z.shiftr_shiftr by lia. rewrite !Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma le1_bytes : forall w : word, le1 w = [Z_to_bv 8 (bv_unsigned w)].
Proof. reflexivity. Qed.
Lemma le2_bytes : forall w : word, le2 w = [Z_to_bv 8 (bv_unsigned w); Z_to_bv 8 (bv_unsigned w / 256)].
Proof. intros. unfold le2. cbn [Z_to_le_bytes]. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma le4_put_b0 : forall c v (w : word), 0 <= c < 2^32 -> bv_unsigned w mod 256 = v mod 256 ->
  le4 (wz (put_b0 c v)) = firstn 0 (le4 (wz c)) ++ le1 w ++ skipn (0 + length (le1 w)) (le4 (wz c)).
Proof.
  intros c v w Hc E. rewrite (le4_wz_bytes c Hc), (le4_wz_bytes _ (put_b0_range c v Hc)), le1_bytes. cbn [firstn skipn app length Nat.add].
  unfold put_b0. change (2^32) with 4294967296 in Hc.
  f_equal; [|f_equal; [|f_equal; [|f_equal]]]; apply Z8_eqm'; rewrite ?E; Z.div_mod_to_equations; lia.
Qed.
Lemma le4_put_b1 : forall c v (w : word), 0 <= c < 2^32 -> bv_unsigned w mod 256 = v mod 256 ->
  le4 (wz (put_b1 c v)) = firstn 1 (le4 (wz c)) ++ le1 w ++ skipn (1 + length (le1 w)) (le4 (wz c)).
Proof.
  intros c v w Hc E. rewrite (le4_wz_bytes c Hc), (le4_wz_bytes _ (put_b1_range c v Hc)), le1_bytes. cbn [firstn skipn app length Nat.add].
  unfold put_b1. change (2^32) with 4294967296 in Hc.
  f_equal; [|f_equal; [|f_equal; [|f_equal]]]; apply Z8_eqm'; rewrite ?E; Z.div_mod_to_equations; lia.
Qed.
Lemma le4_put_h1 : forall c v (w : word), 0 <= c < 2^32 -> bv_unsigned w mod 65536 = v mod 65536 ->
  le4 (wz (put_h1 c v)) = firstn 2 (le4 (wz c)) ++ le2 w ++ skipn (2 + length (le2 w)) (le4 (wz c)).
Proof.
  intros c v w Hc E. rewrite (le4_wz_bytes c Hc), (le4_wz_bytes _ (put_h1_range c v)), le2_bytes. cbn [firstn skipn app length Nat.add].
  unfold put_h1. change (2^32) with 4294967296 in Hc.
  f_equal; [|f_equal; [|f_equal; [|f_equal]]]; apply Z8_eqm'; Z.div_mod_to_equations; lia.
Qed.
Lemma le4_put_h0 : forall c v (w : word), 0 <= c < 2^32 -> bv_unsigned w mod 65536 = v mod 65536 ->
  le4 (wz (put_h0 c v)) = firstn 0 (le4 (wz c)) ++ le2 w ++ skipn (0 + length (le2 w)) (le4 (wz c)).
Proof.
  intros c v w Hc E. rewrite (le4_wz_bytes c Hc), (le4_wz_bytes _ (put_h0_range c v Hc)), le2_bytes. cbn [firstn skipn app length Nat.add].
  unfold put_h0. change (2^32) with 4294967296 in Hc.
  f_equal; [|f_equal; [|f_equal; [|f_equal]]]; apply Z8_eqm'; Z.div_mod_to_equations; lia.
Qed.

Lemma av32_put_first : forall m A a n i (k : nat) (xs : list byte) c',
  u32arr psegs m A (av32 a n) -> 0 <= i < n -> n <= arr_len a -> (k + length xs <= 4)%nat ->
  le4 (wz c') = firstn k (le4 (wz (arr_get a i))) ++ xs ++ skipn (k + length xs) (le4 (wz (arr_get a i))) ->
  u32arr psegs (write_to_mem m (wa (A + (4 * i + Z.of_nat k))) xs) A (av32 (arr_set a i c') n).
Proof.
  intros m A a n i k xs c' ARR Hi Hn Hk E. rewrite <- av32_upd by assumption.
  eapply u32arr_write_part; [exact ARR| apply av32_nth; exact Hi| lia| exact Hk| exact E].
Qed.

Lemma av32_put_next : forall m A a n i c (k : nat) (xs : list byte) c',
  u32arr psegs m A (av32 (arr_set a i c) n) -> 0 <= i < n -> n <= arr_len a -> (k + length xs <= 4)%nat ->
  le4 (wz c') = firstn k (le4 (wz c)) ++ xs ++ skipn (k + length xs) (le4 (wz c)) ->
  u32arr psegs (write_to_mem m (wa (A + (4 * i + Z.of_nat k))) xs) A (av32 (arr_set a i c') n).
Proof.
  intros m A a n i c k xs c' ARR Hi Hn Hk E.
  rewrite <- (av32_upd a n i c') by assumption. rewrite <- (upd_upd (av32 a n) (Z.to_nat i) (wz c) (wz c')).
  rewrite <- (av32_upd a n i c) in ARR by assumption.
  eapply u32arr_write_part; [exact ARR| apply nth_error_upd_same; rewrite av32_length; lia| lia| exact Hk| exact E].
Qed.

Lemma av32_put_b0 : forall m A a n i (w : word) v,
  u32arr psegs m A (av32 a n) -> 0 <= i < n -> n <= arr_len a -> 0 <= arr_get a i < 2^32 -> bv_unsigned w mod 256 = v mod 256 ->
  u32arr psegs (write_to_mem m (wa (A + 4 * i)) (le1 w)) A (av32 (arr_set a i (put_b0 (arr_get a i) v)) n).
Proof.
  intros m A a n i w v ARR Hi Hn Hc E. replace (A + 4 * i) with (A + (4 * i + Z.of_nat 0)) by lia.
  apply av32_put_first; [exact ARR| exact Hi| exact Hn| cbn; lia| apply le4_put_b0; assumption].
Qed.
Lemma av32_put_h0 : forall m A a n i (w : word) v,
  u32arr psegs m A (av32 a n) -> 0 <= i < n -> n <= arr_len a -> 0 <= arr_get a i < 2^32 -> bv_unsigned w mod 65536 = v mod 65536 ->
  u32arr psegs (write_to_mem m (wa (A + 4 * i)) (le2 w)) A (av32 (arr_set a i (put_h0 (arr_get a i) v)) n).
Proof.
  intros m A a n i w v ARR Hi Hn Hc E. replace (A + 4 * i) with (A + (4 * i + Z.of_nat 0)) by lia.
  apply av32_put_first; [exact ARR| exact Hi| exact Hn| cbn; lia| apply le4_put_h0; assumption].
Qed.
Lemma av32_put_b1 : forall m A a n i c (w : word) v,
  u32arr psegs m A (av32 (arr_set a i c) n) -> 0 <= i < n -> n <= arr_len a -> 0 <= c < 2^32 -> bv_unsigned w mod 256 = v mod 256 ->
  u32arr psegs (write_to_mem m (wa (A + 4 * i + 1)) (le1 w)) A (av32 (arr_set a i (put_b1 c v)) n).
Proof.
  intros m A a n i c w v ARR Hi Hn Hc E. replace (A + 4 * i + 1) with (A + (4 * i + Z.of_nat 1)) by lia.
  eapply av32_put_next; [exact ARR| exact Hi| exact Hn| cbn; lia| apply le4_put_b1; assumption].
Qed.
Lemma av32_put_h1 : forall m A a n i c (w : word) v,
  u32arr psegs m A (av32 (arr_set a i c) n) -> 0 <= i < n -> n <= arr_len a -> 0 <= c < 2^32 -> bv_unsigned w mod 65536 = v mod 65536 ->
  u32arr psegs (write_to_mem m (wa (A + 4 * i + 2)) (le2 w)) A (av32 (arr_set a i (put_h1 c v)) n).
Proof.
  intros m A a n i c w v ARR Hi Hn Hc E. replace (A + 4 * i + 2) with (A + (4 * i + Z.of_nat 2)) by lia.
  eapply av32_put_next; [exact ARR| exact Hi| exact Hn| cbn; lia| apply le4_put_h1; assumption].
Qed.

Lemma u16ro_read : forall m A ws (i : Z) w a,
  bytes_at psegs m A (u16s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> a = wa (A + 2 * i) ->
  ov_read_bytes psegs m a 2 = Some (le2 w).
Proof.
  intros m A ws i w a Hb Hn Hi ->.
  destruct (u16s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (2 * i) with (Z.of_nat (2 * Z.to_nat i)) by lia.
  rewrite (bytes_at_ov_read psegs m A _ (2 * Z.to_nat i) 2 Hb).
  2:{ rewrite Eu, !length_app, length_le2, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le2; lia).
  rewrite length_le2, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Lemma u16_lo_read : forall m A ws (i : Z) w a,
  bytes_at psegs m A (u16s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> a = wa (A + 2 * i) ->
  ov_read_bytes psegs m a 1 = Some [Z_to_bv 8 (bv_unsigned w)].
Proof.
  intros m A ws i w a Hb Hn Hi ->.
  destruct (u16s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (2 * i) with (Z.of_nat (2 * Z.to_nat i)) by lia.
  rewrite (bytes_at_ov_read psegs m A _ (2 * Z.to_nat i) 1 Hb).
  2:{ rewrite Eu, !length_app, length_le2, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite le2_bytes. reflexivity.
Qed.

Definition av16s (a : arr) (k n : Z) : list word := map (fun i => wz (arr_get a (k + i))) (zseq n).

Lemma av16s_length : forall a k n, length (av16s a k n) = Z.to_nat n.
Proof. intros. unfold av16s. rewrite length_map. apply zseq_length. Qed.
Lemma av16s_zlength : forall a k n, 0 <= n -> Z.of_nat (length (u16s (av16s a k n))) = 2 * n.
Proof. intros. rewrite u16s_length, av16s_length. lia. Qed.
Lemma av16s_nth : forall a k n i, 0 <= i < n -> nth_error (av16s a k n) (Z.to_nat i) = Some (wz (arr_get a (k + i))).
Proof. intros. unfold av16s. apply (map_zseq_nth (fun i => wz (arr_get a (k + i)))). assumption. Qed.
Lemma av16s_upd : forall a k n i v, 0 <= i < n -> 0 <= k -> k + n <= arr_len a ->
  upd (av16s a k n) (Z.to_nat i) (wz v) = av16s (arr_set a (k + i) v) k n.
Proof.
  intros a k n i v Hi Hk Hn. unfold av16s. apply upd_map_zseq; [exact Hi| |].
  - rewrite arr_get_set_same by lia. reflexivity.
  - intros j Hj Hne. rewrite arr_get_set_other by lia. reflexivity.
Qed.
Lemma av16s_write : forall m A a k n i (w : word) v,
  u16arr psegs m A (av16s a k n) -> 0 <= i < n -> 0 <= k -> k + n <= arr_len a -> le2 w = le2 (wz v) ->
  u16arr psegs (write_to_mem m (wa (A + 2 * i)) (le2 w)) A (av16s (arr_set a (k + i) v) k n).
Proof.
  intros m A a k n i w v ARR Hi Hk Hn E. rewrite <- av16s_upd by assumption.
  unfold u16arr. rewrite <- (u16s_upd_le2 _ _ w (wz v) E).
  apply (u16arr_write psegs); [exact ARR|]. rewrite av16s_length. lia.
Qed.

Definition cnt_cells (c : arr) : list cell :=
  [C2 (wz (arr_get c 0)); C2 (wz (arr_get c 1)); C2 (wz (arr_get c 2)); C2 (wz (arr_get c 3)); C2 (wz (arr_get c 4));
   C2 (wz (arr_get c 5)); C2 (wz (arr_get c 6)); C2 (wz (arr_get c 7)); C2 (wz (arr_get c 8)); C2 (wz (arr_get c 9));
   C2 (wz (arr_get c 10)); C2 (wz (arr_get c 11)); C2 (wz (arr_get c 12)); C2 (wz (arr_get c 13)); C2 (wz (arr_get c 14));
   C2 (wz (arr_get c 15))].
Definition ofs_cells (o : arr) : list cell :=
  [C2 (wz (arr_get o 1)); C2 (wz (arr_get o 2)); C2 (wz (arr_get o 3)); C2 (wz (arr_get o 4));
   C2 (wz (arr_get o 5)); C2 (wz (arr_get o 6)); C2 (wz (arr_get o 7)); C2 (wz (arr_get o 8)); C2 (wz (arr_get o 9));
   C2 (wz (arr_get o 10)); C2 (wz (arr_get o 11)); C2 (wz (arr_get o 12)); C2 (wz (arr_get o 13)); C2 (wz (arr_get o 14));
   C2 (wz (arr_get o 15))].

Lemma cnt_cells_bytes : forall c, cells_bytes (cnt_cells c) = u16s (av16 c 16).
Proof. intros. reflexivity. Qed.
Lemma ofs_cells_bytes : forall o, cells_bytes (ofs_cells o) = u16s (av16s o 1 15).
Proof. intros. reflexivity. Qed.

Lemma cnt_cells_of_arr : forall m A c, u8arr psegs m A (u16s (av16 c 16)) -> rw_cells psegs m A (cnt_cells c).
Proof.
  intros m A c H. apply rw_cells_of_u8arr in H.
  apply (rw_cells_recast m A _ _ H); [cbn; tauto| cbn [cells_bytes cbytes]; rewrite app_nil_r; apply cnt_cells_bytes].
Qed.
Lemma ofs_arr_of_cells : forall m A o, rw_cells psegs m A (ofs_cells o) -> u8arr psegs m A (u16s (av16s o 1 15)).
Proof.
  intros m A o H. apply (u8arr_of_rw_cells psegs m A 30).
  apply (rw_cells_recast m A _ _ H); [cbn; split; [reflexivity| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; symmetry; apply ofs_cells_bytes].
Qed.

Definition Z_LBASE : Z := 0x125e2.
Definition Z_LEXT : Z := 0x12620.
Definition Z_DBASE : Z := 0x1265e.
Definition Z_DEXT : Z := 0x1269e.

Lemma rod_lbase : forall m, mem_inv psegs m -> bytes_at psegs m Z_LBASE (u16s (av16 lbase_a 31)).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold Z_LBASE; lia | vm_compute; intros; discriminate | apply ro_bytes_b_sound; vm_compute; reflexivity].
Qed.
Lemma rod_lext : forall m, mem_inv psegs m -> bytes_at psegs m Z_LEXT (u16s (av16 lext_a 29)).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold Z_LEXT; lia | vm_compute; intros; discriminate | apply ro_bytes_b_sound; vm_compute; reflexivity].
Qed.
Lemma rod_dbase : forall m, mem_inv psegs m -> bytes_at psegs m Z_DBASE (u16s (av16 dbase_a 32)).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold Z_DBASE; lia | vm_compute; intros; discriminate | apply ro_bytes_b_sound; vm_compute; reflexivity].
Qed.
Lemma rod_dext : forall m, mem_inv psegs m -> bytes_at psegs m Z_DEXT (u16s (av16 dext_a 32)).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold Z_DEXT; lia | vm_compute; intros; discriminate | apply ro_bytes_b_sound; vm_compute; reflexivity].
Qed.
