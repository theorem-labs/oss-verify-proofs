(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA Arr Walk Image SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Start Require Import AsanSortModel AsanSortStmt.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow R_arrkit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_ibase R_small R_cache_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma Z_to_le_bytes_app : forall n k z, Z_to_le_bytes (n + k) z = Z_to_le_bytes n z ++ Z_to_le_bytes k (Z.shiftr z (8 * Z.of_nat n)).
Proof.
  induction n as [|n IH]; intros k z.
  - cbn [Nat.add Z_to_le_bytes app]. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [Nat.add Z_to_le_bytes app]. rewrite IH. rewrite Z.shiftr_shiftr by lia. do 3 f_equal. f_equal. lia.
Qed.

Definition lo32 (z : Z) : Z := z mod 2 ^ 32.
Definition hi32 (z : Z) : Z := (z / 2 ^ 32) mod 2 ^ 32.

(* [comment removed for export] *)
Lemma le8_halves : forall w : word, le8 w = le4 w ++ le4 (Z_to_bv 64 (hi32 (bv_unsigned w))).
Proof.
  intros w. rewrite <- store_bytes_8'. unfold le4. change 8%nat with (4 + 4)%nat. rewrite Z_to_le_bytes_app. f_equal.
  change (8 * Z.of_nat 4) with 32. rewrite Z.shiftr_div_pow2 by lia.
  rewrite unsigned_lit by (unfold hi32; pose proof (Z.mod_pos_bound (bv_unsigned w / 2 ^ 32) (2 ^ 32) ltac:(lia)); lia).
  unfold hi32. rewrite (Z_to_le_bytes_mod 4 _ 32) by (cbn; lia). reflexivity.
Qed.

Lemma le8_of_halves : forall a b, 0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 -> le8 (Z_to_bv 64 (a + 2 ^ 32 * b)) = le4 (Z_to_bv 64 a) ++ le4 (Z_to_bv 64 b).
Proof.
  intros a b Ha Hb. rewrite le8_halves. rewrite unsigned_lit by lia. unfold le4. rewrite !unsigned_lit by (unfold hi32; try lia; pose proof (Z.mod_pos_bound ((a + 2 ^ 32 * b) / 2 ^ 32) (2 ^ 32) ltac:(lia)); lia).
  f_equal.
  - rewrite <- (Z_to_le_bytes_mod 4 (a + 2 ^ 32 * b) 32) by (cbn; lia). f_equal. rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia.
  - f_equal. unfold hi32. rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma u64arr_read4 : forall (m : mem) A ws (k : Z) (off : nat) w a, u64arr asegs m A ws -> nth_error ws (Z.to_nat k) = Some w -> 0 <= k ->
  (off <= 4)%nat -> a = wa (A + 8 * k + Z.of_nat off) ->
  ov_read_bytes asegs m a 4 = Some (firstn 4 (skipn off (le8 w))).
Proof.
  intros m A ws k off w a [Hb _] Hn Hk Hoff ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (A + 8 * k + Z.of_nat off) with (A + Z.of_nat (8 * Z.to_nat k + off)) by lia.
  rewrite (bytes_at_ov_read asegs m A (u64s ws) (8 * Z.to_nat k + off) 4 Hb).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu. rewrite <- Hlu. rewrite (Nat.add_comm (length (u64s pre)) off). rewrite <- skipn_skipn. rewrite skipn_app, skipn_all, Nat.sub_diag, skipn_O, app_nil_l.
  rewrite skipn_app. rewrite firstn_app. rewrite length_skipn, length_le8.
  replace (4 - (8 - off))%nat with 0%nat by lia. rewrite firstn_O, app_nil_r. reflexivity.
Qed.

Lemma u64arr_store_ok4 : forall (m : mem) A ws (k : Z) (off : Z) a, u64arr asegs m A ws -> 0 <= k < Z.of_nat (length ws) ->
  0 <= off <= 4 -> a = wa (A + 8 * k + off) -> store_ok asegs m a 4 = true.
Proof.
  intros m A ws k off a [_ Hw] Hk Hoff ->. replace (A + 8 * k + off) with (A + (8 * k + off)) by lia.
  eapply wr_at_store_ok; [exact Hw | lia | lia].
Qed.

(* [comment removed for export] *)
Lemma u64arr_write4 : forall (m : mem) A ws (k : Z) (off : nat) (v w w' : word), u64arr asegs m A ws ->
  nth_error ws (Z.to_nat k) = Some w -> 0 <= k -> (off <= 4)%nat ->
  le8 w' = firstn off (le8 w) ++ le4 v ++ skipn (off + 4) (le8 w) ->
  u64arr asegs (write_to_mem m (wa (A + 8 * k + Z.of_nat off)) (le4 v)) A (upd ws (Z.to_nat k) w').
Proof.
  intros m A ws k off v w w' [Hb Hw] Hn Hk Hoff E.
  destruct (u64s_split _ _ _ Hn) as (pre & post & Ews & Hlen & Eu & Hlu).
  assert (HL : (Z.to_nat k < length ws)%nat) by (apply nth_error_Some; rewrite Hn; discriminate).
  split; [| rewrite upd_length; apply wr_at_write; exact Hw].
  replace (A + 8 * k + Z.of_nat off) with (A + (8 * k + Z.of_nat off)) by lia.
  eapply bytes_at_ext.
  { apply (bytes_at_write_inside asegs m A (u64s ws) (8 * k + Z.of_nat off) (le4 v) Hb); [lia|].
    rewrite length_le4, u64s_length. lia. }
  rewrite Ews. rewrite <- Hlen. rewrite upd_app_len. rewrite !u64s_app. cbn [u64s]. rewrite E.
  rewrite <- (firstn_skipn off (le8 w)) at 1.
  rewrite <- (firstn_skipn 4 (skipn off (le8 w))). rewrite skipn_skipn.
  rewrite <- !app_assoc. rewrite (app_assoc (u64s pre)).
  replace (Z.to_nat (8 * k + Z.of_nat off)) with (length (u64s pre ++ firstn off (le8 w))).
  2:{ rewrite length_app, Hlu, length_firstn, length_le8. lia. }
  rewrite (upd_bytes_mid (u64s pre ++ firstn off (le8 w)) (firstn 4 (skipn off (le8 w))) _ (le4 v)).
  2:{ rewrite length_le4, length_firstn, length_skipn, length_le8. lia. }
  rewrite <- !app_assoc. rewrite (Nat.add_comm 4 off). reflexivity.
Qed.

Lemma lo32_range : forall z, 0 <= lo32 z < 2 ^ 32. Proof. intros z. unfold lo32. apply Z.mod_pos_bound. lia. Qed.
Lemma hi32_range : forall z, 0 <= hi32 z < 2 ^ 32. Proof. intros z. unfold hi32. apply Z.mod_pos_bound. lia. Qed.

Lemma le4_lo32 : forall v : word, le4 v = le4 (Z_to_bv 64 (lo32 (bv_unsigned v))).
Proof.
  intros v. unfold le4. pose proof (lo32_range (bv_unsigned v)). rewrite unsigned_lit by lia. unfold lo32.
  rewrite (Z_to_le_bytes_mod 4 _ 32) by (cbn; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma u64arr_write_lo : forall (m : mem) A ws (k : Z) (v w : word), u64arr asegs m A ws -> nth_error ws (Z.to_nat k) = Some w -> 0 <= k ->
  u64arr asegs (write_to_mem m (wa (A + 8 * k)) (le4 v)) A (upd ws (Z.to_nat k) (Z_to_bv 64 (lo32 (bv_unsigned v) + 2 ^ 32 * hi32 (bv_unsigned w)))).
Proof.
  intros m A ws k v w ARR Hn Hk.
  pose proof (u64arr_write4 m A ws k 0 v w (Z_to_bv 64 (lo32 (bv_unsigned v) + 2 ^ 32 * hi32 (bv_unsigned w))) ARR Hn Hk ltac:(lia)) as X.
  cbn [Z.of_nat] in X. rewrite Z.add_0_r in X. apply X. clear X.
  rewrite le8_of_halves by (apply lo32_range || apply hi32_range).
  change (firstn 0 (le8 w)) with (@nil byte). change (0 + 4)%nat with 4%nat. cbn [app].
  rewrite <- le4_lo32. f_equal. rewrite (le8_halves w), skipn_app, length_le4. rewrite skipn_all2 by (rewrite length_le4; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma u64arr_write_hi : forall (m : mem) A ws (k : Z) (v w : word), u64arr asegs m A ws -> nth_error ws (Z.to_nat k) = Some w -> 0 <= k ->
  u64arr asegs (write_to_mem m (wa (A + 8 * k + 4)) (le4 v)) A (upd ws (Z.to_nat k) (Z_to_bv 64 (lo32 (bv_unsigned w) + 2 ^ 32 * lo32 (bv_unsigned v)))).
Proof.
  intros m A ws k v w ARR Hn Hk.
  pose proof (u64arr_write4 m A ws k 4 v w (Z_to_bv 64 (lo32 (bv_unsigned w) + 2 ^ 32 * lo32 (bv_unsigned v))) ARR Hn Hk ltac:(lia)) as X.
  apply X. clear X.
  rewrite le8_of_halves by (apply lo32_range). rewrite <- !le4_lo32.
  rewrite (le8_halves w). rewrite firstn_app, length_le4. rewrite firstn_all2 by (rewrite length_le4; lia). cbn [Nat.sub firstn]. rewrite app_nil_r.
  f_equal. all: try (rewrite skipn_all2 by (rewrite length_app, !length_le4; lia); rewrite app_nil_r; reflexivity).
Qed.

Lemma halves_eq : forall z, 0 <= z < 2 ^ 64 -> lo32 z + 2 ^ 32 * hi32 z = z.
Proof. intros z Hz. unfold lo32, hi32. rewrite (Z.mod_small (z / 2 ^ 32)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). pose proof (Z.div_mod z (2 ^ 32) ltac:(lia)). lia. Qed.

Lemma lo32_add_hi : forall a b, 0 <= a < 2 ^ 32 -> lo32 (a + 2 ^ 32 * b) = a.
Proof. intros a b Ha. unfold lo32. rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia. Qed.

Lemma lo32_sx32 : forall v : word, lo32 (bv_unsigned (sx32 v)) = lo32 (bv_unsigned v).
Proof.
  intros v. unfold sx32, lo32. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 32 / 2) with (2 ^ 31).
  pose proof (bv_unsigned_in_range 64 v) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2 ^ 64) in R.
  Z.div_mod_to_equations. lia.
Qed.

Lemma lo32_key : forall e, lo32 (HSM.key e) = lo32 (fst e).
Proof.
  intros e. unfold HSM.key, lo32. destruct (Z.ltb_spec (fst e mod 2 ^ 32) (2 ^ 31)).
  - apply Z.mod_mod. lia.
  - replace (fst e mod 2 ^ 32 + (2 ^ 64 - 2 ^ 32)) with (fst e mod 2 ^ 32 + (2 ^ 32 - 1) * 2 ^ 32) by lia. rewrite Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Notation W z := (Z_to_bv 64 z) (only parsing).

Definition ws_of (es : list HSM.rec) : list word := flat_map (fun e => [W (fst e); W (snd e)]) es.
(* [comment removed for export] *)
Definition setrec (ws : list word) (i : nat) (v : HSM.rec) : list word := upd (upd ws (2 * i) (W (fst v))) (2 * i + 1) (W (snd v)).

Lemma ws_of_length : forall es, length (ws_of es) = (2 * length es)%nat.
Proof. induction es as [|e es IH]; [reflexivity|]. cbn [ws_of flat_map length app] in *. unfold ws_of in IH. rewrite IH. lia. Qed.

Lemma ws_of_nth : forall es j, (j < length es)%nat ->
  nth_error (ws_of es) (2 * j) = Some (W (fst (nth j es HSM.dflt))) /\ nth_error (ws_of es) (2 * j + 1) = Some (W (snd (nth j es HSM.dflt))).
Proof.
  induction es as [|e es IH]; intros j Hj; [cbn in Hj; lia|].
  destruct j as [|j]; [split; reflexivity|].
  cbn [length] in Hj. destruct (IH j ltac:(lia)) as [H0 H1].
  replace (2 * S j)%nat with (S (S (2 * j))) by lia. replace (S (S (2 * j)) + 1)%nat with (S (S (2 * j + 1))) by lia.
  cbn [ws_of flat_map app nth_error nth]. split; [exact H0 | exact H1].
Qed.

Lemma ws_of_upd : forall es i v, (i < length es)%nat -> ws_of (HSM.upd es i v) = setrec (ws_of es) i v.
Proof.
  induction es as [|e es IH]; intros i v Hi; [cbn in Hi; lia|].
  destruct i as [|i]; [reflexivity|].
  cbn [length] in Hi. cbn [HSM.upd ws_of flat_map app]. unfold ws_of in IH. rewrite (IH i v ltac:(lia)). unfold setrec.
  replace (2 * S i)%nat with (S (S (2 * i))) by lia. replace (S (S (2 * i)) + 1)%nat with (S (S (2 * i + 1))) by lia. reflexivity.
Qed.

Lemma upd_upd_same : forall {X} (l : list X) i x y, upd (upd l i x) i y = upd l i y.
Proof. induction l as [|z l IH]; intros [|i] x y; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

Lemma upd_comm : forall {X} (l : list X) i j x y, i <> j -> upd (upd l i x) j y = upd (upd l j y) i x.
Proof.
  induction l as [|z l IH]; intros i j x y Hij; [destruct i, j; reflexivity|].
  destruct i as [|i], j as [|j]; cbn; try reflexivity; [lia|]. rewrite IH by lia. reflexivity.
Qed.

Lemma setrec_comm : forall ws i j u v, i <> j -> setrec (setrec ws i u) j v = setrec (setrec ws j v) i u.
Proof.
  intros ws i j u v Hij. unfold setrec.
  rewrite (upd_comm (upd ws (2 * i) _) (2 * i + 1) (2 * j)) by lia. rewrite (upd_comm ws (2 * i) (2 * j)) by lia.
  rewrite (upd_comm (upd (upd ws (2 * j) _) (2 * i) _) (2 * i + 1) (2 * j + 1)) by lia.
  rewrite (upd_comm (upd ws (2 * j) _) (2 * i) (2 * j + 1)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ws_of_swap : forall es i j, 0 <= i < Z.of_nat (length es) -> 0 <= j < Z.of_nat (length es) ->
  ws_of (HSM.swap es i j) = setrec (setrec (ws_of es) (Z.to_nat i) (HSM.get es j)) (Z.to_nat j) (HSM.get es i).
Proof.
  intros es i j Hi Hj. unfold HSM.swap. rewrite ws_of_upd by (rewrite HSM.upd_length; lia). rewrite ws_of_upd by lia. reflexivity.
Qed.

Lemma get_upd_same : forall es i v, (i < length es)%nat -> HSM.get (HSM.upd es i v) (Z.of_nat i) = v.
Proof.
  unfold HSM.get. intros es i v Hi. rewrite Nat2Z.id. revert i Hi. induction es as [|e es IH]; intros i Hi; [cbn in Hi; lia|].
  destruct i as [|i]; [reflexivity|]. cbn [HSM.upd nth]. apply IH. cbn in Hi. lia.
Qed.
Lemma get_upd_other : forall es i j v, i <> j -> HSM.get (HSM.upd es i v) (Z.of_nat j) = HSM.get es (Z.of_nat j).
Proof.
  unfold HSM.get. intros es i j v Hij. rewrite Nat2Z.id. revert i j Hij. induction es as [|e es IH]; intros i j Hij; [destruct i, j; reflexivity|].
  destruct i as [|i], j as [|j]; cbn [HSM.upd nth]; try reflexivity; [lia|]. apply IH. lia.
Qed.

Lemma u64arr_read_lo : forall (m : mem) A ws (k : Z) w a, u64arr asegs m A ws -> nth_error ws (Z.to_nat k) = Some w -> 0 <= k ->
  a = wa (A + 8 * k) -> ov_read_bytes asegs m a 4 = Some (le4 w).
Proof.
  intros m A ws k w a ARR Hn Hk ->.
  rewrite (u64arr_read4 m A ws k 0 w (wa (A + 8 * k)) ARR Hn Hk ltac:(lia) ltac:(f_equal; cbn; lia)).
  cbn [skipn]. rewrite le8_halves, firstn_app, length_le4. cbn [Nat.sub firstn]. rewrite app_nil_r. rewrite firstn_all2 by (rewrite length_le4; lia). reflexivity.
Qed.

Lemma u64arr_read_hi : forall (m : mem) A ws (k : Z) w a, u64arr asegs m A ws -> nth_error ws (Z.to_nat k) = Some w -> 0 <= k ->
  a = wa (A + 8 * k + 4) -> ov_read_bytes asegs m a 4 = Some (le4 (W (hi32 (bv_unsigned w)))).
Proof.
  intros m A ws k w a ARR Hn Hk ->.
  rewrite (u64arr_read4 m A ws k 4 w (wa (A + 8 * k + 4)) ARR Hn Hk ltac:(lia) ltac:(reflexivity)).
  rewrite le8_halves, skipn_app, length_le4. rewrite skipn_all2 by (rewrite length_le4; lia). cbn [Nat.sub skipn app].
  rewrite firstn_all2 by (rewrite length_le4; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma key_range : forall e, 0 <= HSM.key e < 2 ^ 64.
Proof.
  intros e. unfold HSM.key. pose proof (Z.mod_pos_bound (fst e) (2 ^ 32) ltac:(lia)) as R.
  destruct (Z.ltb_spec (fst e mod 2 ^ 32) (2 ^ 31)); lia.
Qed.

Lemma key_sx32 : forall e, 0 <= fst e < 2 ^ 64 -> sx32 (W (fst e)) = W (HSM.key e).
Proof.
  intros e He. unfold sx32. rewrite unsigned_lit by lia. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold HSM.key, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ Z.of_N 64) with (2 ^ 64).
  change (2 ^ 32 / 2) with (2 ^ 31).
  pose proof (Z.mod_pos_bound (fst e) (2 ^ 32) ltac:(lia)) as R.
  destruct (Z.ltb_spec (fst e mod 2 ^ 32) (2 ^ 31)) as [L|L].
  - Z.div_mod_to_equations. lia.
  - Z.div_mod_to_equations. lia.
Qed.

Lemma Forall_hupd : forall (P : HSM.rec -> Prop) a i v, Forall P a -> P v -> Forall P (HSM.upd a i v).
Proof.
  intros P a. induction a as [|e a IH]; intros i v HF Hv; [constructor|].
  inversion HF as [|? ? He Ha]; subst. destruct i as [|i]; cbn [HSM.upd]; constructor; auto.
Qed.

Lemma get_in : forall (P : HSM.rec -> Prop) a i, Forall P a -> 0 <= i < Z.of_nat (length a) -> P (HSM.get a i).
Proof. intros P a i HF Hi. apply (proj1 (Forall_forall _ _) HF). apply nth_In. lia. Qed.

Lemma swap_ok : forall (P : HSM.rec -> Prop) a i j, Forall P a -> 0 <= i < Z.of_nat (length a) -> 0 <= j < Z.of_nat (length a) -> Forall P (HSM.swap a i j).
Proof. intros P a i j HF Hi Hj. unfold HSM.swap. apply Forall_hupd; [apply Forall_hupd; [exact HF|]|]; apply get_in; assumption. Qed.

Lemma nth_hupd_same : forall es i v, (i < length es)%nat -> nth i (HSM.upd es i v) HSM.dflt = v.
Proof. induction es as [|e es IH]; intros i v Hi; [cbn in Hi; lia|]. destruct i as [|i]; [reflexivity|]. cbn [HSM.upd nth]. apply IH. cbn in Hi. lia. Qed.
Lemma nth_hupd_other : forall es i j v, i <> j -> nth j (HSM.upd es i v) HSM.dflt = nth j es HSM.dflt.
Proof.
  induction es as [|e es IH]; intros i j v Hij; [destruct i, j; reflexivity|].
  destruct i as [|i], j as [|j]; cbn [HSM.upd nth]; try reflexivity; [lia|]. apply IH. lia.
Qed.

Lemma get_swap_l : forall a i j, 0 <= i < Z.of_nat (length a) -> 0 <= j < Z.of_nat (length a) -> i <> j -> HSM.get (HSM.swap a i j) i = HSM.get a j.
Proof.
  intros a i j Hi Hj Hij. unfold HSM.swap, HSM.get. rewrite nth_hupd_other by lia. apply nth_hupd_same. lia.
Qed.
Lemma get_swap_r : forall a i j, 0 <= i < Z.of_nat (length a) -> 0 <= j < Z.of_nat (length a) -> HSM.get (HSM.swap a i j) j = HSM.get a i.
Proof.
  intros a i j Hi Hj. unfold HSM.swap, HSM.get. apply nth_hupd_same. rewrite HSM.upd_length. lia.
Qed.

(* [comment removed for export] *)
Lemma setrec_swap : forall a i j, 0 <= i < Z.of_nat (length a) -> 0 <= j < Z.of_nat (length a) -> i <> j ->
  setrec (setrec (ws_of a) (Z.to_nat j) (HSM.get a i)) (Z.to_nat i) (HSM.get a j) = ws_of (HSM.swap a i j).
Proof. intros a i j Hi Hj Hij. rewrite ws_of_swap by assumption. apply setrec_comm. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section IS.
Variables (tab n : Z).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variable Q : machine_state -> Prop.
Hypothesis Hn : 2 <= n <= 2 ^ 16.
Hypothesis T0 : 0 < tab.
Hypothesis T1 : tab + 16 * n <= 2 ^ 47.

Definition recs_ok (a : list HSM.rec) : Prop := Z.of_nat (length a) = n /\ Forall (fun e => 0 <= fst e < 2 ^ 64 /\ 0 <= snd e < 2 ^ 64) a.

(* [comment removed for export] *)
Lemma sift_up_loop : forall (fuel : nat) (a : list HSM.rec) (i j k : Z) (m0 m : mem) (t0 t1 t2 a5 a6 t3 : word),
  recs_ok a -> 1 <= j <= i -> i < n -> Z.of_nat fuel >= j -> k = HSM.key (HSM.get a j) ->
  u64arr asegs m tab (ws_of a) -> mem_inv asegs m -> munch [(tab, tab + 16 * n)] m0 m -> wmono asegs m0 m ->
  (forall (m' : mem) (t0' t1' t2' a4' a5' a6' a7' t3' : word),
     recs_ok (HSM.sift_up fuel a j k) ->
     u64arr asegs m' tab (ws_of (HSM.sift_up fuel a j k)) -> mem_inv asegs m' -> munch [(tab, tab + 16 * n)] m0 m' -> wmono asegs m0 m' ->
     evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (W tab) (W n) (W i) (W 1) a4' a5' a6' a7'
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6) F (W 0x1c125c) fc None m' (seg_rom asegs))) ->
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (W tab) (W n) (W i) (W 1) (W k) a5 a6 (W j)
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (W 0x1c1274) fc None m (seg_rom asegs)).
Proof.
  induction fuel as [|fuel IH]; intros a i j k m0 m t0 t1 t2 a5 a6 t3 OK Hj Hi HF Ek ARR MI MU WM K; [cbn in HF; lia|].
  cbn [HSM.sift_up] in K. cbv zeta in K.
  destruct OK as (LEN & RNG).
  set (p := (j - 1) / 2) in *.
  assert (Hp : 0 <= p < j) by (unfold p; Z.div_mod_to_equations; lia).
  assert (EUj : bv_unsigned (W j) = j) by (apply unsigned_lit; lia).
  zstep. zstep.
  replace ((j + -1) ≫ 1) with p by (unfold p; rewrite Z.shiftr_div_pow2 by lia; f_equal; lia).
  zstep. replace (p ≪ 4) with (16 * p) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep.
  assert (LENn : length a = Z.to_nat n) by lia.
  destruct (ws_of_nth a (Z.to_nat p) ltac:(lia)) as (Np0 & Np1).
  destruct (ws_of_nth a (Z.to_nat j) ltac:(lia)) as (Nj0 & Nj1).
  fold (HSM.get a p) in Np0, Np1. fold (HSM.get a j) in Nj0, Nj1.
  replace (2 * Z.to_nat p)%nat with (Z.to_nat (2 * p)) in Np0 by lia. replace (2 * Z.to_nat p + 1)%nat with (Z.to_nat (2 * p + 1)) in Np1 by lia.
  replace (2 * Z.to_nat j)%nat with (Z.to_nat (2 * j)) in Nj0 by lia. replace (2 * Z.to_nat j + 1)%nat with (Z.to_nat (2 * j + 1)) in Nj1 by lia.
  pose proof (u64arr_read_lo m tab _ (2 * p) _ (W (tab + 16 * p)) ARR Np0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. clear RD.
  assert (Rp : 0 <= fst (HSM.get a p) < 2 ^ 64 /\ 0 <= snd (HSM.get a p) < 2 ^ 64) by (apply (proj1 (Forall_forall _ _) RNG); apply nth_In; lia).
  assert (Rj : 0 <= fst (HSM.get a j) < 2 ^ 64 /\ 0 <= snd (HSM.get a j) < 2 ^ 64) by (apply (proj1 (Forall_forall _ _) RNG); apply nth_In; lia).
  rewrite (key_sx32 (HSM.get a p)) by lia.
  pose proof (key_range (HSM.get a p)) as KRp. pose proof (key_range (HSM.get a j)) as KRj. rewrite <- Ek in KRj.
  assert (EUkp : bv_unsigned (W (HSM.key (HSM.get a p))) = HSM.key (HSM.get a p)) by (apply unsigned_lit; lia).
  assert (EUk : bv_unsigned (W k) = k) by (apply unsigned_lit; lia).
  zstep. rewrite bv_ltu_Z, EUkp, EUk.
  revert K. destruct (Z.geb_spec (HSM.key (HSM.get a p)) k) as [GE|LT]; intros K.
  - (* [comment removed for export] *)
    rewrite (proj2 (Z.ltb_ge (HSM.key (HSM.get a p)) k) GE). cbn [negb].
    eapply K; try eassumption. split; assumption.
  - rewrite (proj2 (Z.ltb_lt (HSM.key (HSM.get a p)) k) LT). cbn [negb].
    (* [comment removed for export] *)
    pose proof (u64arr_read asegs m tab _ (2 * p) _ (W (tab + 16 * p)) ARR Np0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD.
    zstep. replace (j ≪ 4) with (16 * j) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep.
    pose proof (u64arr_read_hi m tab _ (2 * j) _ (W (tab + 16 * j + 4)) ARR Nj0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD.
    assert (LW : length (ws_of a) = (2 * Z.to_nat n)%nat) by (rewrite ws_of_length; lia).
    pose proof (u64arr_bound asegs m tab _ ARR) as BND. rewrite LW in BND.
    (* [comment removed for export] *)
    pose proof (u64arr_store_ok asegs m tab _ (2 * j) (wa (tab + 8 * (2 * j))) ARR ltac:(rewrite LW; lia) eq_refl) as SOK.
    pose proof (u64arr_write asegs m tab _ (2 * j) (W (fst (HSM.get a p))) ARR ltac:(rewrite LW; lia)) as ARR1.
    replace (tab + 8 * (2 * j)) with (tab + 16 * j) in SOK, ARR1 by lia.
    zstep. clear ARR. store_done.
    (* [comment removed for export] *)
    assert (N1 : nth_error (upd (ws_of a) (Z.to_nat (2 * j)) (W (fst (HSM.get a p)))) (Z.to_nat (2 * p + 1)) = Some (W (snd (HSM.get a p))))
      by (rewrite nth_error_upd_other by lia; exact Np1).
    pose proof (u64arr_read asegs m1 tab _ (2 * p + 1) _ (W (tab + 16 * p + 8)) ARR1 N1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD N1.
    assert (N1 : nth_error (upd (ws_of a) (Z.to_nat (2 * j)) (W (fst (HSM.get a p)))) (Z.to_nat (2 * j + 1)) = Some (W (snd (HSM.get a j))))
      by (rewrite nth_error_upd_other by lia; exact Nj1).
    pose proof (u64arr_read asegs m1 tab _ (2 * j + 1) _ (W (tab + 16 * j + 8)) ARR1 N1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD N1.
    (* [comment removed for export] *)
    pose proof (u64arr_store_ok asegs m1 tab _ (2 * j + 1) (wa (tab + 8 * (2 * j + 1))) ARR1 ltac:(rewrite upd_length, LW; lia) eq_refl) as SOK.
    pose proof (u64arr_write asegs m1 tab _ (2 * j + 1) (W (snd (HSM.get a p))) ARR1 ltac:(rewrite upd_length, LW; lia)) as ARR2.
    replace (tab + 8 * (2 * j + 1)) with (tab + 16 * j + 8) in SOK, ARR2 by lia.
    zstep. clear ARR1. store_done.
    (* [comment removed for export] *)
    set (wsA := upd (upd (ws_of a) (Z.to_nat (2 * j)) (W (fst (HSM.get a p)))) (Z.to_nat (2 * j + 1)) (W (snd (HSM.get a p)))) in *.
    assert (LA : length wsA = (2 * Z.to_nat n)%nat) by (unfold wsA; rewrite !upd_length; exact LW).
    assert (NA0 : nth_error wsA (Z.to_nat (2 * p)) = Some (W (fst (HSM.get a p)))) by (unfold wsA; rewrite !nth_error_upd_other by lia; exact Np0).
    pose proof (u64arr_store_ok4 m tab wsA (2 * p) 0 (wa (tab + 16 * p)) ARR2 ltac:(rewrite LA; lia) ltac:(lia) ltac:(f_equal; lia)) as SOK.
    pose proof (u64arr_write_lo m tab wsA (2 * p) (W k) _ ARR2 NA0 ltac:(lia)) as ARR3.
    replace (tab + 8 * (2 * p)) with (tab + 16 * p) in ARR3 by lia.
    zstep.
    clear ARR2. store_done.
    set (w1' := W (lo32 (bv_unsigned (W k)) + 2 ^ 32 * hi32 (bv_unsigned (W (fst (HSM.get a p)))))) in *.
    assert (NB0 : nth_error (upd wsA (Z.to_nat (2 * p)) w1') (Z.to_nat (2 * p)) = Some w1') by (apply nth_error_upd_same; rewrite LA; lia).
    lazymatch goal with ARRx : u64arr asegs ?mm tab (upd wsA _ w1') |- _ =>
      pose proof (u64arr_store_ok4 mm tab _ (2 * p) 4 (wa (tab + 16 * p + 4)) ARRx ltac:(rewrite upd_length, LA; lia) ltac:(lia) ltac:(f_equal; lia)) as SOK;
      pose proof (u64arr_write_hi mm tab _ (2 * p) (sx32 (W (hi32 (fst (HSM.get a j))))) _ ARRx NB0 ltac:(lia)) as ARR4 end.
    replace (tab + 8 * (2 * p) + 4) with (tab + 16 * p + 4) in ARR4 by lia.
    zstep. clear ARR3. store_done.
    rewrite upd_upd_same in ARR4.
    assert (EW2 : W (lo32 (bv_unsigned w1') + 2 ^ 32 * lo32 (bv_unsigned (sx32 (W (hi32 (fst (HSM.get a j))))))) = W (fst (HSM.get a j))).
    { f_equal. unfold w1'. pose proof (lo32_range k) as Lk. pose proof (hi32_range (fst (HSM.get a p))) as Hhp. pose proof (hi32_range (fst (HSM.get a j))) as Hhj.
      rewrite lo32_sx32. rewrite (unsigned_lit k) by lia. rewrite (unsigned_lit (fst (HSM.get a p))) by lia.
      rewrite (unsigned_lit (hi32 (fst (HSM.get a j)))) by lia. rewrite (unsigned_lit (lo32 k + 2 ^ 32 * hi32 (fst (HSM.get a p)))) by lia.
      rewrite lo32_add_hi by lia.
      rewrite Ek, lo32_key. unfold lo32 at 2. rewrite (Z.mod_small (hi32 _)) by lia. apply halves_eq. lia. }
    rewrite EW2 in ARR4. clear EW2 NB0. clearbody w1'.
    (* [comment removed for export] *)
    lazymatch goal with ARRx : u64arr asegs ?mm tab ?l |- _ =>
      pose proof (u64arr_store_ok asegs mm tab _ (2 * p + 1) (wa (tab + 8 * (2 * p + 1))) ARRx ltac:(rewrite upd_length, LA; lia) eq_refl) as SOK;
      pose proof (u64arr_write asegs mm tab _ (2 * p + 1) (W (snd (HSM.get a j))) ARRx ltac:(rewrite upd_length, LA; lia)) as ARR5 end.
    replace (tab + 8 * (2 * p + 1)) with (tab + 16 * p + 8) in SOK, ARR5 by lia.
    zstep. clear ARR4. store_done.
    zstep.
    (* [comment removed for export] *)
    assert (ESW : upd (upd wsA (Z.to_nat (2 * p)) (W (fst (HSM.get a j)))) (Z.to_nat (2 * p + 1)) (W (snd (HSM.get a j))) = ws_of (HSM.swap a p j)).
    { rewrite <- (setrec_swap a p j) by lia. unfold setrec, wsA.
      replace (2 * Z.to_nat j)%nat with (Z.to_nat (2 * j)) by lia. replace (Z.to_nat (2 * j) + 1)%nat with (Z.to_nat (2 * j + 1)) by lia.
      replace (2 * Z.to_nat p)%nat with (Z.to_nat (2 * p)) by lia. replace (Z.to_nat (2 * p) + 1)%nat with (Z.to_nat (2 * p + 1)) by lia. reflexivity. }
    rewrite ESW in ARR5. clear ESW.
    assert (OK' : recs_ok (HSM.swap a p j)) by (split; [rewrite HSM.swap_length; exact LEN | apply swap_ok; [exact RNG | lia | lia]]).
    assert (EUj1 : bv_unsigned (W (j + -1)) = j + -1) by (apply unsigned_lit; lia).
    zstep. rewrite bv_ltu_Z, EUj1. change (bv_unsigned (W 1)) with 1.
    revert K. replace (j - 1) with (j + -1) by lia. destruct (Z.ltb_spec 1 (j + -1)) as [GT|LE]; intros K.
    + (* [comment removed for export] *)
      apply (IH (HSM.swap a p j) i p k m0 m1 _ _ _ _ _ _ OK' ltac:(lia) Hi ltac:(lia)
               ltac:(rewrite get_swap_l by lia; exact Ek) ARR5 ltac:(assumption) ltac:(assumption) ltac:(assumption) K).
    + zstep. eapply K; eassumption.
Qed.

(* [comment removed for export] *)
Lemma build_loop : forall (cnt : nat) (a : list HSM.rec) (i : Z) (m0 m : mem) (t0 t1 t2 a4 a5 a6 a7 t3 : word),
  Z.of_nat cnt = n - i -> 1 <= i < n -> recs_ok a ->
  u64arr asegs m tab (ws_of a) -> mem_inv asegs m -> munch [(tab, tab + 16 * n)] m0 m -> wmono asegs m0 m ->
  (forall (m' : mem) (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' : word),
     recs_ok (HSM.build cnt a i) ->
     u64arr asegs m' tab (ws_of (HSM.build cnt a i)) -> mem_inv asegs m' -> munch [(tab, tab + 16 * n)] m0 m' -> wmono asegs m0 m' ->
     evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (W tab) (W n) a2' a3' a4' a5' a6' a7'
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6) F (W 0x1c1398) fc None m' (seg_rom asegs))) ->
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (W tab) (W n) (W i) (W 1) a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (W 0x1c1264) fc None m (seg_rom asegs)).
Proof.
  induction cnt as [|cnt IH]; intros a i m0 m t0 t1 t2 a4 a5 a6 a7 t3 Hc Hi OK ARR MI MU WM K; [lia|].
  cbn [HSM.build] in K.
  pose proof OK as (LEN & RNG).
  assert (EUi : bv_unsigned (W i) = i) by (apply unsigned_lit; lia).
  zstep. replace (i ≪ 4) with (16 * i) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep.
  destruct (ws_of_nth a (Z.to_nat i) ltac:(lia)) as (Ni0 & _). fold (HSM.get a i) in Ni0.
  replace (2 * Z.to_nat i)%nat with (Z.to_nat (2 * i)) in Ni0 by lia.
  pose proof (u64arr_read_lo m tab _ (2 * i) _ (W (tab + 16 * i)) ARR Ni0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. clear RD.
  assert (Ri : 0 <= fst (HSM.get a i) < 2 ^ 64 /\ 0 <= snd (HSM.get a i) < 2 ^ 64) by (apply (get_in _ a i RNG); lia).
  rewrite (key_sx32 (HSM.get a i)) by lia.
  zstep.
  apply (sift_up_loop (Z.to_nat i + 1) a i i (HSM.key (HSM.get a i)) m0 m _ _ _ _ _ _ OK ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ARR MI MU WM).
  intros m' t0' t1' t2' a4' a5' a6' a7' t3' OK' ARR' MI' MU' WM'.
  zstep.
  assert (EUi1 : bv_unsigned (W (i + 1)) = i + 1) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (W n) = n) by (apply unsigned_lit; lia).
  zstep. rewrite bv_eqb_Z, EUi1, EUn.
  destruct (Z.eqb_spec (i + 1) n) as [E|NE].
  - (* [comment removed for export] *)
    assert (Ec : cnt = 0%nat) by lia. subst cnt. cbn [HSM.build] in K.
    eapply K; eassumption.
  - apply (IH _ (i + 1) m0 m' _ _ _ _ _ _ _ _ ltac:(lia) ltac:(lia) OK' ARR' MI' MU' WM' K).
Qed.

(* [comment removed for export] *)
Lemma sd_swap : forall (a : list HSM.rec) (cur b size : Z) (m0 m : mem) (t0 t1 t2 a5 a6 a7 t3 : word),
  recs_ok a -> 0 <= cur < size -> 0 <= b < size -> size <= n -> b <> cur ->
  u64arr asegs m tab (ws_of a) -> mem_inv asegs m -> munch [(tab, tab + 16 * n)] m0 m -> wmono asegs m0 m ->
  (forall (m' : mem) (a4' a5' a6' a7' : word),
     recs_ok (HSM.swap a b cur) ->
     u64arr asegs m' tab (ws_of (HSM.swap a b cur)) -> mem_inv asegs m' -> munch [(tab, tab + 16 * n)] m0 m' -> wmono asegs m0 m' ->
     evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (W tab) (W size) (W b) (W b) a4' a5' a6' a7'
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (W 0x1c12f4) fc None m' (seg_rom asegs))) ->
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (W tab) (W size) (W cur) (W b) (W (16 * cur)) a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (W 0x1c1364) fc None m (seg_rom asegs)).
Proof.
  intros a cur b size m0 m t0 t1 t2 a5 a6 a7 t3 OK Hcur Hb Hsz Hne ARR MI MU WM K.
  pose proof OK as (LEN & RNG).
  assert (EUb : bv_unsigned (W b) = b) by (apply unsigned_lit; lia).
  assert (LW : length (ws_of a) = (2 * Z.to_nat n)%nat) by (rewrite ws_of_length; lia).
  pose proof (u64arr_bound asegs m tab _ ARR) as BND. rewrite LW in BND.
  destruct (ws_of_nth a (Z.to_nat b) ltac:(lia)) as (Nb0 & Nb1). destruct (ws_of_nth a (Z.to_nat cur) ltac:(lia)) as (Nc0 & Nc1).
  fold (HSM.get a b) in Nb0, Nb1. fold (HSM.get a cur) in Nc0, Nc1.
  replace (2 * Z.to_nat b)%nat with (Z.to_nat (2 * b)) in Nb0 by lia. replace (2 * Z.to_nat b + 1)%nat with (Z.to_nat (2 * b + 1)) in Nb1 by lia.
  replace (2 * Z.to_nat cur)%nat with (Z.to_nat (2 * cur)) in Nc0 by lia. replace (2 * Z.to_nat cur + 1)%nat with (Z.to_nat (2 * cur + 1)) in Nc1 by lia.
  zstep. replace (b ≪ 4) with (16 * b) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep.
  pose proof (u64arr_read asegs m tab _ (2 * b) _ (W (tab + 16 * b)) ARR Nb0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. clear RD.
  zstep.
  pose proof (u64arr_read asegs m tab _ (2 * cur) _ (W (tab + 16 * cur)) ARR Nc0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. clear RD.
  pose proof (u64arr_read asegs m tab _ (2 * cur + 1) _ (W (tab + 16 * cur + 8)) ARR Nc1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. clear RD.
  (* [comment removed for export] *)
  pose proof (u64arr_store_ok asegs m tab _ (2 * cur) (wa (tab + 8 * (2 * cur))) ARR ltac:(rewrite LW; lia) eq_refl) as SOK.
  pose proof (u64arr_write asegs m tab _ (2 * cur) (W (fst (HSM.get a b))) ARR ltac:(rewrite LW; lia)) as ARR1.
  replace (tab + 8 * (2 * cur)) with (tab + 16 * cur) in SOK, ARR1 by lia.
  zstep. clear ARR. store_done.
  (* [comment removed for export] *)
  assert (N1 : nth_error (upd (ws_of a) (Z.to_nat (2 * cur)) (W (fst (HSM.get a b)))) (Z.to_nat (2 * b + 1)) = Some (W (snd (HSM.get a b))))
    by (rewrite nth_error_upd_other by lia; exact Nb1).
  lazymatch goal with ARRx : u64arr asegs ?mm tab _ |- _ =>
    pose proof (u64arr_read asegs mm tab _ (2 * b + 1) _ (W (tab + 16 * b + 8)) ARRx N1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
  zstep. clear RD N1.
  (* [comment removed for export] *)
  lazymatch goal with ARRx : u64arr asegs ?mm tab _ |- _ =>
    pose proof (u64arr_store_ok asegs mm tab _ (2 * cur + 1) (wa (tab + 8 * (2 * cur + 1))) ARRx ltac:(rewrite upd_length, LW; lia) eq_refl) as SOK;
    pose proof (u64arr_write asegs mm tab _ (2 * cur + 1) (W (snd (HSM.get a b))) ARRx ltac:(rewrite upd_length, LW; lia)) as ARR2 end.
  replace (tab + 8 * (2 * cur + 1)) with (tab + 16 * cur + 8) in SOK, ARR2 by lia.
  zstep. clear ARR1. store_done.
  (* [comment removed for export] *)
  lazymatch goal with ARRx : u64arr asegs ?mm tab _ |- _ =>
    pose proof (u64arr_store_ok asegs mm tab _ (2 * b) (wa (tab + 8 * (2 * b))) ARRx ltac:(rewrite !upd_length, LW; lia) eq_refl) as SOK;
    pose proof (u64arr_write asegs mm tab _ (2 * b) (W (fst (HSM.get a cur))) ARRx ltac:(rewrite !upd_length, LW; lia)) as ARR3 end.
  replace (tab + 8 * (2 * b)) with (tab + 16 * b) in SOK, ARR3 by lia.
  zstep. clear ARR2. store_done.
  (* [comment removed for export] *)
  lazymatch goal with ARRx : u64arr asegs ?mm tab _ |- _ =>
    pose proof (u64arr_store_ok asegs mm tab _ (2 * b + 1) (wa (tab + 8 * (2 * b + 1))) ARRx ltac:(rewrite !upd_length, LW; lia) eq_refl) as SOK;
    pose proof (u64arr_write asegs mm tab _ (2 * b + 1) (W (snd (HSM.get a cur))) ARRx ltac:(rewrite !upd_length, LW; lia)) as ARR4 end.
  replace (tab + 8 * (2 * b + 1)) with (tab + 16 * b + 8) in SOK, ARR4 by lia.
  zstep. clear ARR3. store_done.
  assert (ESW : upd (upd (upd (upd (ws_of a) (Z.to_nat (2 * cur)) (W (fst (HSM.get a b)))) (Z.to_nat (2 * cur + 1)) (W (snd (HSM.get a b))))
                      (Z.to_nat (2 * b)) (W (fst (HSM.get a cur)))) (Z.to_nat (2 * b + 1)) (W (snd (HSM.get a cur))) = ws_of (HSM.swap a b cur)).
  { rewrite <- (setrec_swap a b cur) by lia. unfold setrec.
    replace (2 * Z.to_nat cur)%nat with (Z.to_nat (2 * cur)) by lia. replace (Z.to_nat (2 * cur) + 1)%nat with (Z.to_nat (2 * cur + 1)) by lia.
    replace (2 * Z.to_nat b)%nat with (Z.to_nat (2 * b)) by lia. replace (Z.to_nat (2 * b) + 1)%nat with (Z.to_nat (2 * b + 1)) by lia. reflexivity. }
  rewrite ESW in ARR4. clear ESW.
  assert (OK' : recs_ok (HSM.swap a b cur)) by (split; [rewrite HSM.swap_length; exact LEN | apply swap_ok; [exact RNG | lia | lia]]).
  assert (EUs : bv_unsigned (W size) = size) by (apply unsigned_lit; lia).
  zstep. zstep. rewrite bv_ltu_Z, EUb, EUs. rewrite (proj2 (Z.ltb_lt b size) ltac:(lia)).
  eapply K; eassumption.
Qed.

(* [comment removed for export] *)
Lemma sift_down_loop : forall (fuel : nat) (a : list HSM.rec) (cur size : Z) (m0 m : mem) (t0 t1 t2 a4 a5 a6 a7 t3 : word),
  recs_ok a -> 0 <= cur < size -> size <= n -> Z.of_nat fuel >= size - cur ->
  u64arr asegs m tab (ws_of a) -> mem_inv asegs m -> munch [(tab, tab + 16 * n)] m0 m -> wmono asegs m0 m ->
  (forall (m' : mem) (a2' a3' a4' a5' a6' a7' : word),
     recs_ok (HSM.sift_down fuel a cur size) ->
     u64arr asegs m' tab (ws_of (HSM.sift_down fuel a cur size)) -> mem_inv asegs m' -> munch [(tab, tab + 16 * n)] m0 m' -> wmono asegs m0 m' ->
     evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (W tab) (W size) a2' a3' a4' a5' a6' a7'
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (W 0x1c1398) fc None m' (seg_rom asegs))) ->
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (W tab) (W size) (W cur) (W cur) a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (W 0x1c12f4) fc None m (seg_rom asegs)).
Proof.
  induction fuel as [|fuel IH]; intros a cur size m0 m t0 t1 t2 a4 a5 a6 a7 t3 OK Hcur Hsz HF ARR MI MU WM K; [cbn in HF; lia|].
  cbn [HSM.sift_down] in K. cbv zeta in K.
  pose proof OK as (LEN & RNG).
  set (l := 2 * cur + 1) in *. set (r := 2 * cur + 2) in *.
  remember (if (l <? size) && (HSM.key (HSM.get a cur) <? HSM.key (HSM.get a l)) then l else cur) as b1 eqn:Eb1 in K.
  remember (if (r <? size) && (HSM.key (HSM.get a b1) <? HSM.key (HSM.get a r)) then r else b1) as b eqn:Eb in K.
  assert (EUc : bv_unsigned (W cur) = cur) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (W size) = size) by (apply unsigned_lit; lia).
  zstep. zstep. zstep.
  replace (cur ≪ 1) with (2 * cur) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  replace (cur ≪ 4) with (16 * cur) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  fold l.
  assert (EUl : bv_unsigned (W l) = l) by (apply unsigned_lit; unfold l; lia).
  assert (EUr : bv_unsigned (W r) = r) by (apply unsigned_lit; unfold r; lia).
  assert (LW : length (ws_of a) = (2 * Z.to_nat n)%nat) by (rewrite ws_of_length; lia).
  (* [comment removed for export] *)
  assert (KEY : forall (x : Z) (mm : mem), 0 <= x < n -> u64arr asegs mm tab (ws_of a) ->
            ov_read_bytes asegs mm (W (tab + 16 * x)) 4 = Some (le4 (W (fst (HSM.get a x)))) /\ sx32 (W (fst (HSM.get a x))) = W (HSM.key (HSM.get a x))
            /\ bv_unsigned (W (HSM.key (HSM.get a x))) = HSM.key (HSM.get a x)).
  { intros x mm Hx ARRx. destruct (ws_of_nth a (Z.to_nat x) ltac:(lia)) as (N0 & _). fold (HSM.get a x) in N0.
    replace (2 * Z.to_nat x)%nat with (Z.to_nat (2 * x)) in N0 by lia.
    split; [exact (u64arr_read_lo mm tab _ (2 * x) _ (W (tab + 16 * x)) ARRx N0 ltac:(lia) ltac:(unfold wa; f_equal; lia))|].
    pose proof (get_in _ a x RNG ltac:(lia)) as Rx. cbv beta in Rx.
    split; [apply key_sx32; lia | apply unsigned_lit; apply key_range]. }
  zstep. rewrite bv_ltu_Z, EUl, EUs.
  destruct (Z.lt_ge_cases l size) as [Ll|Ll].
  2:{ (* [comment removed for export] *)
    rewrite (proj2 (Z.ltb_ge l size) Ll).
    zstep. replace (2 * cur + 2) with r by reflexivity.
    zstep. rewrite bv_ltu_Z, EUr, EUs. rewrite (proj2 (Z.ltb_ge r size) ltac:(unfold r, l in *; lia)).
    zstep. rewrite bv_eqb_Z, EUc, Z.eqb_refl. cbn [negb].
    zstep.
    rewrite (proj2 (Z.ltb_ge l size) Ll) in Eb1. cbn [andb] in Eb1. subst b1.
    rewrite (proj2 (Z.ltb_ge r size) ltac:(unfold r, l in *; lia)) in Eb. cbn [andb] in Eb. subst b.
    rewrite Z.eqb_refl in K. eapply K; eassumption. }
  rewrite (proj2 (Z.ltb_lt l size) Ll). rewrite (proj2 (Z.ltb_lt l size) Ll) in Eb1. cbn [andb] in Eb1.
  (* [comment removed for export] *)
  destruct (KEY cur m ltac:(lia) ARR) as (RDc & SXc & EUkc). destruct (KEY l m ltac:(unfold l in *; lia) ARR) as (RDl & SXl & EUkl).
  zstep. zstep. replace (l ≪ 4) with (16 * l) by (rewrite Z.shiftl_mul_pow2 by (unfold l; lia); lia).
  zstep. zstep. rewrite SXc. zstep. rewrite SXl. clear RDc RDl.
  zstep. rewrite bv_ltu_Z, EUkc, EUkl.
  assert (Hb1 : (b1 = l \/ b1 = cur) /\ 0 <= b1 < size) by (rewrite Eb1; destruct (HSM.key (HSM.get a cur) <? HSM.key (HSM.get a l)); unfold l in *; lia).
  assert (REST : evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (W tab) (W size) (W cur) (W (HSM.key (HSM.get a cur))) (W (16 * cur)) (W (2 * cur)) (W b1)
                                    (W (HSM.key (HSM.get a l))) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (W 0x1c1330) fc None m (seg_rom asegs))).
  2:{ destruct (Z.ltb_spec (HSM.key (HSM.get a cur)) (HSM.key (HSM.get a l))) as [C1|C1].
      - rewrite Eb1 in REST. exact REST.
      - zstep. rewrite Eb1 in REST. exact REST. }
  clear Eb1.
  assert (EUb1 : bv_unsigned (W b1) = b1) by (apply unsigned_lit; lia).
  zstep. zstep. replace (2 * cur + 2) with r by reflexivity.
  zstep. rewrite bv_ltu_Z, EUr, EUs.
  assert (Hbv : b = r \/ b = b1) by (rewrite Eb; destruct ((r <? size) && (HSM.key (HSM.get a b1) <? HSM.key (HSM.get a r))); [left | right]; reflexivity).
  (* [comment removed for export] *)
  assert (TAIL : forall (bb : Z) (x5 x6 x7 : word), b = bb -> 0 <= bb < size -> bb <> cur ->
            evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (W tab) (W size) (W cur) (W bb) (W (16 * cur)) x5 x6 x7
                                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (W 0x1c1364) fc None m (seg_rom asegs))).
  { intros bb x5 x6 x7 Ebb Hbb Nbb. subst bb. rewrite (proj2 (Z.eqb_neq b cur) Nbb) in K.
    apply (sd_swap a cur b size m0 m _ _ _ _ _ _ _ OK Hcur Hbb Hsz Nbb ARR MI MU WM).
    intros m' a4' a5' a6' a7' OK' ARR' MI' MU' WM'.
    apply (IH (HSM.swap a b cur) b size m0 m' _ _ _ _ _ _ _ _ OK' Hbb Hsz ltac:(rewrite Nat2Z.inj_succ in HF; destruct Hb1 as ([E1| E1] & _); destruct Hbv as [E2|E2]; unfold l, r in *; lia) ARR' MI' MU' WM' K). }
  destruct (Z.lt_ge_cases r size) as [Lr|Lr].
  2:{ (* [comment removed for export] *)
    rewrite (proj2 (Z.ltb_ge r size) Lr). cbn [negb].
    rewrite (proj2 (Z.ltb_ge r size) Lr) in Eb. cbn [andb] in Eb.
    zstep. rewrite bv_eqb_Z, EUb1, EUc.
    destruct (Z.eqb_spec b1 cur) as [E1|N1]; cbn [negb].
    - zstep. rewrite Eb, E1, Z.eqb_refl in K. eapply K; eassumption.
    - apply (TAIL b1); [exact Eb | lia | exact N1]. }
  rewrite (proj2 (Z.ltb_lt r size) Lr). cbn [negb]. rewrite (proj2 (Z.ltb_lt r size) Lr) in Eb. cbn [andb] in Eb.
  (* [comment removed for export] *)
  destruct (KEY b1 m ltac:(lia) ARR) as (RDb & SXb & EUkb). destruct (KEY r m ltac:(unfold r in *; lia) ARR) as (RDr & SXr & EUkr).
  zstep. replace (b1 ≪ 4) with (16 * b1) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep. replace (r ≪ 4) with (16 * r) by (rewrite Z.shiftl_mul_pow2 by (unfold r; lia); lia).
  zstep. zstep. zstep. rewrite SXb. zstep. rewrite SXr. clear RDb RDr.
  zstep. rewrite bv_ltu_Z, EUkb, EUkr.
  assert (Hbr : 0 <= b < size) by (destruct Hbv as [-> | ->]; unfold r in *; lia).
  assert (REST2 : evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (W tab) (W size) (W cur) (W b1) (W (16 * cur)) (W b) (W (HSM.key (HSM.get a b1)))
                                    (W (HSM.key (HSM.get a r))) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (W 0x1c135c) fc None m (seg_rom asegs))).
  2:{ destruct (Z.ltb_spec (HSM.key (HSM.get a b1)) (HSM.key (HSM.get a r))) as [C2|C2].
      - rewrite Eb in REST2. exact REST2.
      - zstep. rewrite Eb in REST2. exact REST2. }
  clear Eb.
  assert (EUb : bv_unsigned (W b) = b) by (apply unsigned_lit; lia).
  zstep. zstep. rewrite bv_eqb_Z, EUb, EUc.
  destruct (Z.eqb_spec b cur) as [E1|N1].
  - eapply K; eassumption.
  - apply (TAIL b); [reflexivity | exact Hbr | exact N1].
Qed.

(* [comment removed for export] *)
Lemma drain_loop : forall (cnt : nat) (a : list HSM.rec) (L : Z) (m0 m : mem) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 : word),
  Z.of_nat cnt = L - 1 -> 1 <= L <= n -> recs_ok a ->
  u64arr asegs m tab (ws_of a) -> mem_inv asegs m -> munch [(tab, tab + 16 * n)] m0 m -> wmono asegs m0 m ->
  (forall (m' : mem) (a2' a3' a4' a5' a6' a7' : word),
     recs_ok (HSM.drain cnt a (L - 1)) ->
     u64arr asegs m' tab (ws_of (HSM.drain cnt a (L - 1))) -> mem_inv asegs m' -> munch [(tab, tab + 16 * n)] m0 m' -> wmono asegs m0 m' ->
     evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (W tab) (W 0) a2' a3' a4' a5' a6' a7'
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (W 0x1c13a0) fc None m' (seg_rom asegs))) ->
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (W tab) (W L) a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (W 0x1c1398) fc None m (seg_rom asegs)).
Proof.
  induction cnt as [|cnt IH]; intros a L m0 m t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 Hc HL OK ARR MI MU WM K.
  - assert (L = 1) by lia. subst L. cbn [HSM.drain] in K.
    zstep. zstep. ifF. eapply K; eassumption.
  - cbn [HSM.drain] in K. set (last := L - 1) in *.
    pose proof OK as (LEN & RNG).
    assert (Hlast : 1 <= last < n) by (unfold last; lia).
    assert (EUlast : bv_unsigned (W last) = last) by (apply unsigned_lit; lia).
    zstep. replace (L + -1) with last by (unfold last; lia).
    zstep. ifT.
    zstep. zstep. replace (last ≪ 4) with (16 * last) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep.
    assert (LW : length (ws_of a) = (2 * Z.to_nat n)%nat) by (rewrite ws_of_length; lia).
    pose proof (u64arr_bound asegs m tab _ ARR) as BND. rewrite LW in BND.
    destruct (ws_of_nth a (Z.to_nat last) ltac:(lia)) as (Nl0 & Nl1). destruct (ws_of_nth a 0%nat ltac:(lia)) as (N00 & N01).
    fold (HSM.get a last) in Nl0, Nl1. change (nth 0 a HSM.dflt) with (HSM.get a 0) in N00, N01.
    replace (2 * Z.to_nat last)%nat with (Z.to_nat (2 * last)) in Nl0 by lia. replace (2 * Z.to_nat last + 1)%nat with (Z.to_nat (2 * last + 1)) in Nl1 by lia.
    change (2 * 0)%nat with (Z.to_nat 0) in N00. change (2 * 0 + 1)%nat with (Z.to_nat 1) in N01.
    pose proof (u64arr_read asegs m tab _ (2 * last) _ (W (tab + 16 * last)) ARR Nl0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD.
    pose proof (u64arr_read asegs m tab _ (2 * last + 1) _ (W (tab + 16 * last + 8)) ARR Nl1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD.
    pose proof (u64arr_read asegs m tab _ 0 _ (W tab) ARR N00 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep.
    clear RD.
    pose proof (u64arr_read asegs m tab _ 1 _ (W (tab + 8)) ARR N01 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD.
    (* [comment removed for export] *)
    pose proof (u64arr_store_ok asegs m tab _ 0 (wa (tab + 8 * 0)) ARR ltac:(rewrite LW; lia) eq_refl) as SOK.
    pose proof (u64arr_write asegs m tab _ 0 (W (fst (HSM.get a last))) ARR ltac:(rewrite LW; lia)) as ARR1.
    replace (tab + 8 * 0) with tab in SOK, ARR1 by lia.
    zstep.
    clear ARR. store_done.
    lazymatch goal with ARRx : u64arr asegs ?mm tab _ |- _ =>
      pose proof (u64arr_store_ok asegs mm tab _ 1 (wa (tab + 8 * 1)) ARRx ltac:(rewrite upd_length, LW; lia) eq_refl) as SOK;
      pose proof (u64arr_write asegs mm tab _ 1 (W (snd (HSM.get a last))) ARRx ltac:(rewrite upd_length, LW; lia)) as ARR2 end.
    replace (tab + 8 * 1) with (tab + 8) in SOK, ARR2 by lia.
    zstep. clear ARR1. store_done.
    (* [comment removed for export] *)
    lazymatch goal with ARRx : u64arr asegs ?mm tab _ |- _ =>
      pose proof (u64arr_store_ok asegs mm tab _ (2 * last) (wa (tab + 8 * (2 * last))) ARRx ltac:(rewrite !upd_length, LW; lia) eq_refl) as SOK;
      pose proof (u64arr_write asegs mm tab _ (2 * last) (W (fst (HSM.get a 0))) ARRx ltac:(rewrite !upd_length, LW; lia)) as ARR3 end.
    replace (tab + 8 * (2 * last)) with (tab + 16 * last) in SOK, ARR3 by lia.
    zstep. clear ARR2. store_done.
    lazymatch goal with ARRx : u64arr asegs ?mm tab _ |- _ =>
      pose proof (u64arr_store_ok asegs mm tab _ (2 * last + 1) (wa (tab + 8 * (2 * last + 1))) ARRx ltac:(rewrite !upd_length, LW; lia) eq_refl) as SOK;
      pose proof (u64arr_write asegs mm tab _ (2 * last + 1) (W (snd (HSM.get a 0))) ARRx ltac:(rewrite !upd_length, LW; lia)) as ARR4 end.
    replace (tab + 8 * (2 * last + 1)) with (tab + 16 * last + 8) in SOK, ARR4 by lia.
    zstep. clear ARR3. store_done.
    assert (ESW : upd (upd (upd (upd (ws_of a) (Z.to_nat 0) (W (fst (HSM.get a last)))) (Z.to_nat 1) (W (snd (HSM.get a last))))
                        (Z.to_nat (2 * last)) (W (fst (HSM.get a 0)))) (Z.to_nat (2 * last + 1)) (W (snd (HSM.get a 0))) = ws_of (HSM.swap a 0 last)).
    { rewrite (ws_of_swap a 0 last) by lia. unfold setrec. change (2 * Z.to_nat 0)%nat with (Z.to_nat 0). change (Z.to_nat 0 + 1)%nat with (Z.to_nat 1).
      replace (2 * Z.to_nat last)%nat with (Z.to_nat (2 * last)) by lia. replace (Z.to_nat (2 * last) + 1)%nat with (Z.to_nat (2 * last + 1)) by lia. reflexivity. }
    rewrite ESW in ARR4. clear ESW.
    assert (OK' : recs_ok (HSM.swap a 0 last)) by (split; [rewrite HSM.swap_length; exact LEN | apply swap_ok; [exact RNG | lia | lia]]).
    zstep.
    apply (sift_down_loop (Z.to_nat last + 1) (HSM.swap a 0 last) 0 last m0 _ _ _ _ _ _ _ _ _ OK' ltac:(lia) ltac:(lia) ltac:(lia) ARR4
             ltac:(assumption) ltac:(assumption) ltac:(assumption)).
    intros m' a2' a3' a4' a5' a6' a7' OK2 ARR' MI' MU' WM'.
    apply (IH _ last m0 m' _ _ _ _ _ _ _ _ _ _ ltac:(unfold last; lia) ltac:(lia) OK2 ARR' MI' MU' WM').
    exact K.
Qed.

End IS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma get_cons : forall e es j, 0 <= j -> HSM.get (e :: es) (j + 1) = HSM.get es j.
Proof. intros e es j Hj. unfold HSM.get. replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia. reflexivity. Qed.

Lemma u64arr_of_recs : forall (m : mem) es tab, 0 <= tab -> tab + 16 * Z.of_nat (length es) <= 2 ^ 64 ->
  (forall j, 0 <= j < Z.of_nat (length es) -> HSS.rec_at asegs m tab es j) -> u64arr asegs m tab (ws_of es).
Proof.
  intros m es. induction es as [|e es IH]; intros tab T0 T1 H.
  - split; [split; [lia | split; [cbn; lia | intros i Hi; cbn in Hi; lia]] | split; [lia | split; [cbn; lia | intros i Hi; cbn in Hi; lia]]].
  - cbn [length] in T1, H. rewrite Nat2Z.inj_succ in T1, H.
    pose proof (H 0 ltac:(lia)) as R0. unfold HSS.rec_at in R0. change (HSM.get (e :: es) 0) with e in R0. rewrite Z.mul_0_r, Z.add_0_r in R0.
    assert (IHt : u64arr asegs m (tab + 16) (ws_of es)).
    { apply IH; [lia | lia |]. intros j Hj. pose proof (H (j + 1) ltac:(lia)) as Rj. unfold HSS.rec_at in *. rewrite get_cons in Rj by lia.
      replace (tab + 16 * (j + 1)) with (tab + 16 + 16 * j) in Rj by lia. exact Rj. }
    destruct R0 as [[_ Hb] Hw]. destruct IHt as [Hb2 Hw2]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. cbn [cells_size csize] in Hw.
    change (ws_of (e :: es)) with (W (fst e) :: W (snd e) :: ws_of es). split.
    + cbn [u64s]. rewrite app_assoc. apply bytes_at_app. split; [exact Hb|]. rewrite length_app, !length_le8. exact Hb2.
    + cbn [length]. destruct Hw as (A0 & A1 & A2). destruct Hw2 as (B0 & B1 & B2). split; [lia|]. split; [lia|].
      intros i Hi. destruct (Z.lt_ge_cases i 16) as [Li|Li]; [apply A2; lia|].
      replace (tab + i) with (tab + 16 + (i - 16)) by lia. apply B2. lia.
Qed.

Lemma rec_of_u64arr : forall (m : mem) es tab j, u64arr asegs m tab (ws_of es) -> 0 <= j < Z.of_nat (length es) -> HSS.rec_at asegs m tab es j.
Proof.
  intros m es tab j [Hb Hw] Hj. unfold HSS.rec_at.
  destruct (ws_of_nth es (Z.to_nat j) ltac:(lia)) as (N0 & N1). fold (HSM.get es j) in N0, N1.
  destruct (u64s_split _ _ _ N0) as (pre & post & E & Hlen & Eu & Hlu).
  assert (Ep : exists post', post = W (snd (HSM.get es j)) :: post').
  { rewrite E in N1. rewrite nth_error_app2 in N1 by lia. replace (2 * Z.to_nat j + 1 - length pre)%nat with 1%nat in N1 by lia.
    destruct post as [|x post']; [discriminate|]. cbn in N1. injection N1 as ->. exists post'. reflexivity. }
  destruct Ep as (post' & ->). cbn [u64s] in Eu.
  rewrite Eu in Hb. apply bytes_at_app in Hb as [_ Hb]. rewrite Hlu in Hb.
  rewrite app_assoc in Hb. apply bytes_at_app in Hb as [Hb _].
  replace (tab + Z.of_nat (8 * (2 * Z.to_nat j))) with (tab + 16 * j) in Hb by lia.
  pose proof (ws_of_length es) as LW.
  split; [split; [exact (conj I (conj I I)) | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Hb]|].
  cbn [cells_size csize]. destruct Hw as (W0 & W1 & W2). rewrite LW in W1, W2. split; [lia|]. split; [lia|].
  intros k Hk. replace (tab + 16 * j + k) with (tab + (16 * j + k)) by lia. apply W2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem xr_isort_spec : HSS.walk_stmt asegs 0x1c1248.
Proof.
  unfold HSS.walk_stmt.
  intros tab n es RA sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    LEN Hn RNG RECS T0 T1 T8 HRA HRA2 MI.
  assert (ARR : u64arr asegs m tab (ws_of es)) by (apply u64arr_of_recs; [lia | lia | rewrite LEN; exact RECS]).
  pose proof (munch_refl [(tab, tab + 16 * n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (OK : recs_ok n es) by (split; assumption).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  zstep. zstep. rewrite bv_ltu_Z, EUn. change (bv_unsigned (Z_to_bv 64 2)) with 2. rewrite (proj2 (Z.ltb_ge n 2) ltac:(lia)).
  zstep. zstep. zstep.
  lazymatch goal with |- evt asegs ?QQ _ =>
    apply (build_loop tab n (Z_to_bv 64 RA) sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 F fc QQ Hn T0 T1
             (Z.to_nat (n - 1)) es 1 m m _ _ _ _ _ _ _ _ ltac:(lia) ltac:(lia) OK ARR MI MU WM) end.
  intros m1 t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' OK1 ARR1 MI1 MU1 WM1.
  lazymatch goal with |- evt asegs ?QQ _ =>
    apply (drain_loop tab n (Z_to_bv 64 RA) sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 F fc QQ Hn T0 T1
             (Z.to_nat (n - 1)) _ n m m1 _ _ _ _ _ _ _ _ _ _ ltac:(lia) ltac:(lia) OK1 ARR1 MI1 MU1 WM1) end.
  intros m2 a2'' a3'' a4'' a5'' a6'' a7'' OK2 ARR2 MI2 MU2 WM2.
  zstep. rewrite (ret_pc_even RA) by lia.
  apply evt_done.
  exists (Z_to_bv 64 0), a2'', a3'', a4'', a5'', a6'', a7'', t0', t1', t2', t3', m2.
  split; [reflexivity|]. split; [exact MU2|]. split; [exact WM2|]. split; [exact MI2|].
  intros j Hj.
  assert (EH : HSM.hsort es = HSM.drain (Z.to_nat (n - 1)) (HSM.build (Z.to_nat (n - 1)) es 1) (n - 1)).
  { unfold HSM.hsort. rewrite LEN. rewrite (proj2 (Z.ltb_ge n 2) ltac:(lia)). reflexivity. }
  rewrite EH. apply rec_of_u64arr; [exact ARR2|]. destruct OK2 as (L2 & _). rewrite L2. exact Hj.
Qed.
