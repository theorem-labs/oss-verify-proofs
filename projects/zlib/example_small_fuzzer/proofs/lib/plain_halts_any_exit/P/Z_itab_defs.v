(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_ikit Zh_kit Z_infl_iface.

Module Z_itab_kit.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Import Z_ikit Zh_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface InflateState Inftrees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
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

Lemma cnt_arr_of_cells : forall m A c, rw_cells psegs m A (cnt_cells c) -> u8arr psegs m A (u16s (av16 c 16)).
Proof.
  intros m A c H. apply (u8arr_of_rw_cells psegs m A 32).
  apply (rw_cells_recast m A _ _ H); [cbn; split; [reflexivity| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; symmetry; apply cnt_cells_bytes].
Qed.
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


Definition Z_LBASE : Z := 0x12582.
Definition Z_LEXT : Z := 0x125c0.
Definition Z_DBASE : Z := 0x125fe.
Definition Z_DEXT : Z := 0x1263e.

Lemma rod_lbase : forall m, mem_inv psegs m -> bytes_at psegs m Z_LBASE (u16s (av16 lbase_a 31)).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold Z_LBASE; lia | vm_compute; intros; discriminate | apply ro_bytes_b_sound; vm_compute; reflexivity].
Qed.
(* 1.4: lext[29] is 71 here and 203 in the model, so only the 29 length-code entries (symbols 257..285) are read. *)
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
End Z_itab_kit.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_infl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_itab_defs.Z_itab_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface InflateState Inftrees ItableModel RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Step.simpl_sizes ::=
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end; cbn [length].

Definition PC_IT_CNT : Z := 0x1eee0.
Definition PC_IT_CNTX : Z := 0x1ef00.
Definition PC_IT_MAX0 : Z := 0x1ef14.
Definition PC_IT_MAXJ : Z := 0x1f018.
Definition PC_IT_MINL : Z := 0x1f030.
Definition PC_IT_MINJ : Z := 0x1f04c.
Definition PC_IT_KRAFT : Z := 0x1f054.
Definition PC_IT_MAX1 : Z := 0x1f534.
Definition PC_IT_OFFS : Z := 0x1f15c.
Definition PC_IT_SORT : Z := 0x1f1f4.
Definition PC_IT_SORTN : Z := 0x1f1e8.
Definition PC_IT_TYPE : Z := 0x1f220.
Definition PC_IT_INIT : Z := 0x1f2bc.
Definition PC_IT_SUBJ : Z := 0x1f2e8.
Definition PC_IT_TRIP : Z := 0x1f2f0.
Definition PC_IT_FILL : Z := 0x1f350.
Definition PC_IT_INCR : Z := 0x1f380.
Definition PC_IT_NEXT : Z := 0x1f3f8.
Definition PC_IT_SUB : Z := 0x1f404.
Definition PC_IT_LEFT : Z := 0x1f424.
Definition PC_IT_USED : Z := 0x1f454.
Definition PC_IT_DONE : Z := 0x1f4b8.
Definition PC_IT_TAIL : Z := 0x1f4ec.
Definition PC_IT_EPI : Z := 0x1f4f4.
Definition PC_IT_NOSYM : Z := 0x1f558.

Record itx : Type := mkITX {
  tx_L : ilay; tx_s : inflate_state; tx_ty : codetype; tx_dsel : bool; tx_lofs : Z; tx_codes : Z; tx_lo : Z; tx_m0 : mem;
  tx_sp : word; tx_ra : word; tx_gp : word; tx_tp : word;
  tx_s0 : word; tx_s1 : word; tx_s2 : word; tx_s3 : word; tx_s4 : word; tx_s5 : word;
  tx_s6 : word; tx_s7 : word; tx_s8 : word; tx_s9 : word; tx_s10 : word; tx_s11 : word;
  tx_F : bvmap 5 word; tx_fc : bv 32
}.

Definition tx_W (X : itx) : list ivl :=
  [(tx_lo X, bv_unsigned (tx_sp X)); (il_As (tx_L X), il_As (tx_L X) + ZI_SIZE)].
Definition tx_W1 (X : itx) : list ivl :=
  [(tx_lo X, bv_unsigned (tx_sp X)); (il_As (tx_L X) + 808, il_As (tx_L X) + 7160)].

Lemma tx_W1_sub : forall X, sub_fp (tx_W1 X) (tx_W X).
Proof.
  intros X x. unfold tx_W1, tx_W. cbn [outside inside fst snd]. intros H. lia.
Qed.

Definition it_saved (X : itx) : list cell :=
  [C8 (tx_s11 X); C8 (tx_s10 X); C8 (tx_s9 X); C8 (tx_s8 X); C8 (tx_s7 X); C8 (tx_s6 X); C8 (tx_s5 X); C8 (tx_s4 X);
   C8 (tx_s3 X); C8 (tx_s2 X); C8 (tx_s1 X); C8 (tx_s0 X); C8 (tx_ra X)].

Definition tx_lens (X : itx) : arr := is_lens (tx_s X).
Definition tx_bits (X : itx) : Z := it_bits_get (tx_dsel X) (tx_s X).
Definition tx_table (X : itx) : Z := is_next (tx_s X).
Definition tx_lensA (X : itx) : Z := il_As (tx_L X) + 168 + 2 * tx_lofs X.
Definition tx_bitsA (X : itx) : Z := il_As (tx_L X) + (if tx_dsel X then 140 else 136).

Record itx_ok (X : itx) : Prop := mkITXok {
  xo_lo : tx_lo X <= bv_unsigned (tx_sp X) - Z_ITABLE_STACK;
  xo_As : 0 < il_As (tx_L X) /\ il_As (tx_L X) + ZI_SIZE <= tx_lo X /\ il_As (tx_L X) + ZI_SIZE < 2^62;
  xo_win : is_window_blk (tx_s X) <> None -> il_Aw (tx_L X) + ZI_WIN <= tx_lo X;
  xo_codes : 0 <= tx_lofs X /\ 0 <= tx_codes X /\ tx_lofs X + tx_codes X <= 320;
  xo_arrs : iarrs (tx_s X);
  xo_lay : ilay_ok (tx_L X) (tx_s X)
}.

Definition itab_post (X : itx) : machine_state -> Prop :=
  inflate_table_post (tx_ra X) (tx_sp X) (tx_gp X) (tx_tp X) (tx_s0 X) (tx_s1 X) (tx_s2 X) (tx_s3 X) (tx_s4 X) (tx_s5 X) (tx_s6 X)
    (tx_s7 X) (tx_s8 X) (tx_s9 X) (tx_s10 X) (tx_s11 X) (tx_F X) (tx_fc X) (tx_L X) (tx_s X) (tx_ty X) (tx_dsel X) (tx_lofs X)
    (tx_codes X) (tx_lo X) (tx_m0 X).

Definition it_res_state (s : inflate_state) (dsel : bool) (tb : arr) (nxt bts : Z) (wk : arr) : inflate_state :=
  iset_work (it_bits_set dsel (iset_next (iset_codes s tb) nxt) bts) wk.

Definition tx_call (X : itx) : Z * arr * Z * Z * arr :=
  inflate_table (tx_ty X) (tx_lens X) (tx_lofs X) (tx_codes X) (is_codes (tx_s X)) (tx_table X) (tx_bits X) (is_work (tx_s X)).

Lemma it_result_eq : forall X ret tb nxt bts wk, tx_call X = (ret, tb, nxt, bts, wk) ->
  it_result (tx_ty X) (tx_dsel X) (tx_lofs X) (tx_codes X) (tx_s X) = (ret, it_res_state (tx_s X) (tx_dsel X) tb nxt bts wk).
Proof. intros X ret tb nxt bts wk H. unfold it_result. unfold tx_call, tx_lens, tx_table, tx_bits in H. rewrite H. reflexivity. Qed.

Record ITM (X : itx) (low : list cell) (cnt ofs wk tb : arr) (m : mem) : Prop := mkITM {
  tm_low : rw_cells psegs m (bv_unsigned (tx_sp X) + -192) low;
  tm_ofs : u8arr psegs m (bv_unsigned (tx_sp X) + -166) (u16s (av16s ofs 1 15));
  tm_cnt : u8arr psegs m (bv_unsigned (tx_sp X) + -136) (u16s (av16 cnt 16));
  tm_sav : rw_cells psegs m (bv_unsigned (tx_sp X) + -104) (it_saved X);
  tm_stk : stk psegs m (tx_lo X) (bv_unsigned (tx_sp X) + -192);
  tm_work : u16arr psegs m (il_As (tx_L X) + 808) (av16 wk 288);
  tm_codes : u32arr psegs m (il_As (tx_L X) + 1384) (av32 tb 1444);
  tm_mi : mem_inv psegs m;
  tm_mu : munch (tx_W1 X) (tx_m0 X) m;
  tm_wm : wmono psegs (tx_m0 X) m
}.

Lemma ITM_isA : forall X low cnt ofs wk tb m, itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) -> ITM X low cnt ofs wk tb m -> isA m (tx_L X) (tx_s X).
Proof.
  intros X low cnt ofs wk tb m XO ST TM. apply (isA_munch (tx_m0 X) m _ _ (tx_W1 X)); [exact (ist_A _ _ _ ST)| exact (tm_mu _ _ _ _ _ _ _ TM)| exact (tm_wm _ _ _ _ _ _ _ TM)|].
  pose proof (xo_As X XO) as HA. unfold tx_W1. cbn [disjoint_from]. split; [lia| split; [lia| exact I]].
Qed.
Lemma ITM_isT : forall X low cnt ofs wk tb m, itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) -> ITM X low cnt ofs wk tb m -> isT m (tx_L X) (tx_s X).
Proof.
  intros X low cnt ofs wk tb m XO ST TM. apply (isT_munch (tx_m0 X) m _ _ (tx_W1 X)); [exact (ist_T _ _ _ ST)| exact (tm_mu _ _ _ _ _ _ _ TM)| exact (tm_wm _ _ _ _ _ _ _ TM)|].
  pose proof (xo_As X XO) as HA. unfold tx_W1. cbn [disjoint_from]. split; [lia| split; [lia| exact I]].
Qed.
Lemma ITM_ilens : forall X low cnt ofs wk tb m, itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) -> ITM X low cnt ofs wk tb m -> ilens m (tx_L X) (tx_s X).
Proof.
  intros X low cnt ofs wk tb m XO ST TM. apply (ilens_munch (tx_m0 X) m _ _ (tx_W1 X)); [exact (ist_lens _ _ _ ST)| exact (tm_mu _ _ _ _ _ _ _ TM)| exact (tm_wm _ _ _ _ _ _ _ TM)|].
  pose proof (xo_As X XO) as HA. unfold tx_W1. cbn [disjoint_from]. split; [lia| split; [lia| exact I]].
Qed.
Lemma ITM_iwin : forall X low cnt ofs wk tb m, itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) -> ITM X low cnt ofs wk tb m -> iwin m (tx_L X) (tx_s X).
Proof.
  intros X low cnt ofs wk tb m XO ST TM. apply (iwin_munch (tx_m0 X) m _ _ (tx_W1 X)); [exact (ist_win _ _ _ ST)| exact (tm_mu _ _ _ _ _ _ _ TM)| exact (tm_wm _ _ _ _ _ _ _ TM)|].
  intros NE. pose proof (xo_win X XO NE) as W1. destruct (ist_lay _ _ _ ST) as [_ LW]. destruct (LW NE) as [_ AP].
  pose proof (xo_As X XO) as HA. unfold apart in AP. unfold tx_W1. cbn [disjoint_from]. split; [lia| split; [lia| exact I]].
Qed.

Lemma IST_result : forall X m tb nxt bts wk,
  itx_ok X -> isA m (tx_L X) (it_res_state (tx_s X) (tx_dsel X) tb nxt bts wk) ->
  isT m (tx_L X) (tx_s X) -> ilens m (tx_L X) (tx_s X) ->
  u16arr psegs m (il_As (tx_L X) + 808) (av16 wk 288) -> u32arr psegs m (il_As (tx_L X) + 1384) (av32 tb 1444) ->
  iwin m (tx_L X) (tx_s X) -> arr_len wk = 288 -> arr_len tb = 1444 ->
  IST m (tx_L X) (it_res_state (tx_s X) (tx_dsel X) tb nxt bts wk).
Proof.
  intros X m tb nxt bts wk XO GA GT Gl Gw Gc Gwin LW LT. destruct XO as [_ _ _ _ ARRS LAY].
  unfold it_res_state, it_bits_set in *. destruct (tx_dsel X).
  - constructor; [exact GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| | exact LAY].
    unfold iarrs in *. ired. tauto.
  - constructor; [exact GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| | exact LAY].
    unfold iarrs in *. ired. tauto.
Qed.

Lemma isA_result_same : forall X m tb wk, isA m (tx_L X) (tx_s X) ->
  isA m (tx_L X) (it_res_state (tx_s X) (tx_dsel X) tb (tx_table X) (tx_bits X) wk).
Proof.
  intros X m tb wk GA. unfold it_res_state, it_bits_set, tx_bits, tx_table, it_bits_get. destruct (tx_dsel X); exact GA.
Qed.

Lemma itab_epilogue : forall X ret s' (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (m : mem) (j : list byte),
  itx_ok X ->
  rw_cells psegs m (bv_unsigned (tx_sp X) + -192) (CB 88 j :: it_saved X) ->
  stk psegs m (tx_lo X) (bv_unsigned (tx_sp X) + -192) ->
  IST m (tx_L X) s' -> mem_inv psegs m -> munch (tx_W X) (tx_m0 X) m -> wmono psegs (tx_m0 X) m ->
  it_result (tx_ty X) (tx_dsel X) (tx_lofs X) (tx_codes X) (tx_s X) = (ret, s') ->
  evt psegs (itab_post X)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (wz ret) x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (tx_F X) (wz PC_IT_EPI) (tx_fc X) None m (seg_rom psegs)).
Proof.
  intros until j. intros XO FR ST HIST MI MU WM ER.
  destruct XO as [XLO _ _ _ _ _]. unfold Z_ITABLE_STACK in XLO. unfold it_saved in FR. unfold tx_W in MU.
  unfold PC_IT_EPI. do 15 zs.
  release_frame FR ST (bv_unsigned (tx_sp X)). zs.
  apply evt_done. unfold itab_post, inflate_table_post. rewrite ER. cbn [fst snd].
  do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [|exact HIST].
  symmetry. apply Z_to_bv_mod64.
Qed.
