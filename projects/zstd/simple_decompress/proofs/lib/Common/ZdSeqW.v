(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXSound KXBridge KXMem.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma flat_map_seqsym_skipn : forall (l : list seqsym) (n : nat), (n < length l)%nat ->
  firstn 8 (skipn (8 * n) (flat_map seqsym_bytes l)) = seqsym_bytes (nth n l ss0).
Proof.
  induction l as [|c l IH]; intros n Hn; cbn [length] in Hn; [lia|].
  destruct n as [|n].
  - change (8 * 0)%nat with 0%nat. rewrite skipn_O. cbn [nth flat_map]. rewrite firstn_app, seqsym_bytes_length.
    change (8 - 8)%nat with 0%nat. rewrite firstn_O, app_nil_r. apply firstn_all2. rewrite seqsym_bytes_length. lia.
  - replace (8 * S n)%nat with (8 * n + 8)%nat by lia. cbn [flat_map nth].
    rewrite <- skipn_skipn. rewrite (skipn_app 8), seqsym_bytes_length. change (8 - 8)%nat with 0%nat. rewrite skipn_O.
    rewrite (skipn_all2 (seqsym_bytes c)) by (rewrite seqsym_bytes_length; lia). cbn [app]. apply IH. lia.
Qed.

(* [comment removed for export] *)
Lemma seq_table_bytes_cell : forall t state, 0 <= state < FseNCount.Zlength (st_cells t) ->
  firstn 8 (skipn (Z.to_nat (8 + 8 * state)) (seq_table_bytes t)) = seqsym_bytes (st_cell t state).
Proof.
  intros t state H. unfold seq_table_bytes, st_cell.
  replace (Z.to_nat (8 + 8 * state)) with (8 * Z.to_nat state + 8)%nat by lia.
  rewrite <- skipn_skipn.
  assert (E : skipn 8 (zle4 (st_fast t) ++ zle4 (st_log t) ++ flat_map seqsym_bytes (st_cells t)) = flat_map seqsym_bytes (st_cells t)) by reflexivity.
  rewrite E. apply flat_map_seqsym_skipn. unfold FseNCount.Zlength in H. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma b8_lit : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. intros c H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. lia. Qed.

Lemma lor_shl8 : forall x y, 0 <= x < 256 -> 0 <= y -> Z.lor x (Z.shiftl y 8) = x + 256 * y.
Proof.
  intros x y Hx Hy. rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256.
  rewrite Z.lor_comm. rewrite <- Z.lxor_lor.
  - rewrite <- Z.add_nocarry_lxor; [lia|].
    apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.ltb_spec n 8).
    + replace (y * 256) with (y * 2^8) by reflexivity. rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    + destruct (Z.eq_dec x 0) as [->|NZ]; [rewrite Z.bits_0; apply andb_false_r|].
      rewrite (Z.bits_above_log2 x n); [apply andb_false_r|lia|]. apply Z.lt_le_trans with 8; [|lia]. apply Z.log2_lt_pow2; lia.
  - apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.ltb_spec n 8).
    + replace (y * 256) with (y * 2^8) by reflexivity. rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    + destruct (Z.eq_dec x 0) as [->|NZ]; [rewrite Z.bits_0; apply andb_false_r|].
      rewrite (Z.bits_above_log2 x n); [apply andb_false_r|lia|]. apply Z.lt_le_trans with 8; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma le_val1 : forall v, 0 <= v < 256 -> bytes_le_to_Z (map (Z_to_bv 8) [v]) = v.
Proof. intros v H. cbn [map bytes_le_to_Z]. rewrite b8_lit by lia. rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity. Qed.

Lemma le_val2 : forall v, 0 <= v < 2^16 -> bytes_le_to_Z (map (Z_to_bv 8) (zle2 v)) = v.
Proof.
  intros v H. change (2^16) with 65536 in H. unfold zle2. cbn [map bytes_le_to_Z].
  pose proof (Z.mod_pos_bound v 256 ltac:(lia)). pose proof (Z.mod_pos_bound (v / 256) 256 ltac:(lia)).
  rewrite !b8_lit by lia. rewrite Z.shiftl_0_l, Z.lor_0_r. rewrite lor_shl8 by lia.
  rewrite (Z.mod_small (v / 256) 256) by (split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]).
  pose proof (Z.div_mod v 256 ltac:(lia)). lia.
Qed.

Lemma le_val4 : forall v, 0 <= v < 2^32 -> bytes_le_to_Z (map (Z_to_bv 8) (zle4 v)) = v.
Proof.
  intros v H. change (2^32) with 4294967296 in H. unfold zle4. cbn [map bytes_le_to_Z].
  pose proof (Z.mod_pos_bound v 256 ltac:(lia)). pose proof (Z.mod_pos_bound (v / 256) 256 ltac:(lia)).
  pose proof (Z.mod_pos_bound (v / 65536) 256 ltac:(lia)). pose proof (Z.mod_pos_bound (v / 16777216) 256 ltac:(lia)).
  rewrite !b8_lit by lia. rewrite Z.shiftl_0_l, Z.lor_0_r.
  rewrite (lor_shl8 ((v / 65536) mod 256) ((v / 16777216) mod 256)) by lia.
  rewrite (lor_shl8 ((v / 256) mod 256)) by lia. rewrite (lor_shl8 (v mod 256)) by lia.
  rewrite (Z.mod_small (v / 16777216) 256) by (split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]).
  assert (E1 : v / 65536 = v / 256 / 256) by (rewrite Z.div_div by lia; reflexivity).
  assert (E2 : v / 16777216 = v / 256 / 256 / 256) by (rewrite !Z.div_div by lia; reflexivity).
  rewrite E1, E2 in *.
  pose proof (Z.div_mod v 256 ltac:(lia)). pose proof (Z.div_mod (v / 256) 256 ltac:(lia)).
  pose proof (Z.div_mod (v / 256 / 256) 256 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Rd.
  Variable segs : list Segment.
  Variables (m : word -> option byte) (T : Z) (k : seq_kind) (t : seq_table).
  Hypothesis TB : bytes_at segs m T (map (Z_to_bv 8) (seq_table_bytes t)).
  Hypothesis OK : seq_table_ok k t.

  Lemma seq_tl_range : 0 <= st_log t <= 9.
  Proof. destruct OK as (H & _). destruct k; cbn [kind_maxLog] in H; lia. Qed.

  Lemma seq_cells_len : FseNCount.Zlength (st_cells t) = 2^(st_log t).
  Proof. destruct OK as (_ & H & _). exact H. Qed.

  Lemma seq_img_len : length (map (Z_to_bv 8) (seq_table_bytes t)) = Z.to_nat (8 * (1 + 2^(st_log t))).
  Proof.
    rewrite length_map. pose proof (seq_table_bytes_length t) as L. unfold FseNCount.Zlength in L.
    pose proof seq_cells_len as C. unfold FseNCount.Zlength in C. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma seq_rd_log : rdval segs m (wa (T + 4)) 4 false = Z_to_bv 64 (st_log t).
  Proof.
    pose proof seq_tl_range as R. assert (P : 0 < 2^(st_log t)) by (apply Z.pow_pos_nonneg; lia).
    rewrite (rdval_bytes_at segs m T _ 4 4 false TB ltac:(lia)) by (rewrite seq_img_len; lia).
    cbn [extz]. rewrite skipn_map, firstn_map. f_equal.
    unfold seq_table_bytes. change (Z.to_nat 4) with 4%nat.
    change (firstn 4 (skipn 4 (zle4 (st_fast t) ++ zle4 (st_log t) ++ flat_map seqsym_bytes (st_cells t)))) with (zle4 (st_log t)).
    apply le_val4. change (2^32) with 4294967296. lia.
  Qed.

  Section Cell.
    Variable state : Z.
    Hypothesis ST : 0 <= state < 2^(st_log t).

    Lemma seq_cell_facts : cell_ok k (st_log t) (st_cell t state).
    Proof. apply (st_cell_ok k t state OK ST). Qed.

    Lemma seq_cell_img : forall (i : Z) (n : nat), 0 <= i -> (Z.to_nat i + n <= 8)%nat ->
      firstn n (skipn (Z.to_nat (8 + 8 * state + i)) (seq_table_bytes t)) = firstn n (skipn (Z.to_nat i) (seqsym_bytes (st_cell t state))).
    Proof.
      intros i n Hi Hn. rewrite <- (seq_table_bytes_cell t state) by (rewrite seq_cells_len; exact ST).
      replace (Z.to_nat (8 + 8 * state + i)) with (Z.to_nat i + Z.to_nat (8 + 8 * state))%nat by lia.
      rewrite <- skipn_skipn. rewrite skipn_firstn_comm. rewrite firstn_firstn. f_equal. lia.
    Qed.

    Lemma seq_rd_field : forall (i : Z) (n : nat), 0 <= i -> (Z.to_nat i + n <= 8)%nat ->
      rdval segs m (wa (T + (8 + 8 * state + i))) n false =
      Z_to_bv 64 (bytes_le_to_Z (map (Z_to_bv 8) (firstn n (skipn (Z.to_nat i) (seqsym_bytes (st_cell t state)))))).
    Proof.
      intros i n Hi Hn. pose proof seq_tl_range as R.
      rewrite (rdval_bytes_at segs m T _ (8 + 8 * state + i) n false TB ltac:(lia)) by (rewrite seq_img_len; lia).
      cbn [extz]. rewrite skipn_map, firstn_map. rewrite seq_cell_img by assumption. reflexivity.
    Qed.

    (* [comment removed for export] *)
    Lemma seq_rd_next : rdval segs m (wa (T + (8 + 8 * state + 0))) 2 false = Z_to_bv 64 (ss_next (st_cell t state)).
    Proof.
      rewrite seq_rd_field by (cbn; lia). f_equal. change (firstn 2 (skipn (Z.to_nat 0) (seqsym_bytes (st_cell t state)))) with (zle2 (ss_next (st_cell t state))).
      apply le_val2. pose proof seq_cell_facts as (B1 & B2 & B3 & _). pose proof seq_tl_range.
      assert (2^(st_log t) <= 2^9) by (apply Z.pow_le_mono_r; lia). assert (0 < 2^(ss_nbBits (st_cell t state))) by (apply Z.pow_pos_nonneg; lia).
      change (2^9) with 512 in *. change (2^16) with 65536. lia.
    Qed.

    Lemma seq_rd_nbAdd : rdval segs m (wa (T + (8 + 8 * state + 2))) 1 false = Z_to_bv 64 (ss_nbAdd (st_cell t state)).
    Proof.
      rewrite seq_rd_field by (cbn; lia). f_equal. change (firstn 1 (skipn (Z.to_nat 2) (seqsym_bytes (st_cell t state)))) with [ss_nbAdd (st_cell t state)].
      apply le_val1. pose proof seq_cell_facts as (_ & _ & _ & SY). pose proof (sym_ok_kind_bounds k _ SY) as (B & _). destruct k; lia.
    Qed.

    Lemma seq_rd_nbBits : rdval segs m (wa (T + (8 + 8 * state + 3))) 1 false = Z_to_bv 64 (ss_nbBits (st_cell t state)).
    Proof.
      rewrite seq_rd_field by (cbn; lia). f_equal. change (firstn 1 (skipn (Z.to_nat 3) (seqsym_bytes (st_cell t state)))) with [ss_nbBits (st_cell t state)].
      apply le_val1. pose proof seq_cell_facts as (B1 & _). pose proof seq_tl_range. lia.
    Qed.

    Lemma seq_rd_base : rdval segs m (wa (T + (8 + 8 * state + 4))) 4 false = Z_to_bv 64 (ss_base (st_cell t state)).
    Proof.
      rewrite seq_rd_field by (cbn; lia). f_equal. change (firstn 4 (skipn (Z.to_nat 4) (seqsym_bytes (st_cell t state)))) with (zle4 (ss_base (st_cell t state))).
      apply le_val4. pose proof seq_cell_facts as (_ & _ & _ & SY). pose proof (sym_ok_kind_bounds k _ SY) as (_ & B0 & B1 & _).
      assert (0 < 2^(ss_nbAdd (st_cell t state))) by (apply Z.pow_pos_nonneg; pose proof (sym_ok_kind_bounds k _ SY) as (B & _); lia).
      change (2^32) with 4294967296 in *. change (2^17) with 131072 in *. destruct k; lia.
    Qed.
  End Cell.
End Rd.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma b8_mod : forall z, Z_to_bv 8 (z mod 256) = Z_to_bv 8 z.
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  apply Z.mod_mod. lia.
Qed.

Lemma wle1 : forall v, 0 <= v < 2^64 -> word_to_le_bytes 1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
Proof.
  intros v H. unfold word_to_le_bytes. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; exact H). reflexivity.
Qed.

Lemma wle2 : forall v, 0 <= v < 2^64 -> word_to_le_bytes 2 (Z_to_bv 64 v) = map (Z_to_bv 8) (zle2 v).
Proof.
  intros v H. unfold word_to_le_bytes, zle2. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; exact H).
  cbn [Z_to_le_bytes map]. rewrite !b8_mod, !Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma wle4 : forall v, 0 <= v < 2^64 -> word_to_le_bytes 4 (Z_to_bv 64 v) = map (Z_to_bv 8) (zle4 v).
Proof.
  intros v H. unfold word_to_le_bytes, zle4. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; exact H).
  cbn [Z_to_le_bytes map]. rewrite !b8_mod, !Z.shiftr_div_pow2 by lia. rewrite !Z.div_div by lia. reflexivity.
Qed.

Section Rdn.
  Variable segs : list Segment.
  Variables (m : word -> option byte) (T : Z) (k : seq_kind) (t : seq_table).
  Hypothesis TB : bytes_at segs m T (map (Z_to_bv 8) (seq_table_bytes t)).
  Hypothesis OK : seq_table_ok k t.

  Lemma seq_rdn_at : forall (i : Z) (n : nat), 0 <= i -> i + Z.of_nat n <= 8 * (1 + 2^(st_log t)) ->
    rdn segs m (wa (T + i)) n = Some (map (Z_to_bv 8) (firstn n (skipn (Z.to_nat i) (seq_table_bytes t)))).
  Proof.
    intros i n Hi Hn. replace (T + i) with (T + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (bytes_at_rdn segs m T _ (Z.to_nat i) n TB) by (rewrite (seq_img_len k t OK); lia).
    rewrite skipn_map, firstn_map. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma seq_rdn_log : rdn segs m (wa (T + 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (st_log t))).
  Proof.
    pose proof (seq_tl_range k t OK) as R. assert (P : 0 < 2^(st_log t)) by (apply Z.pow_pos_nonneg; lia).
    rewrite seq_rdn_at by lia. rewrite wle4 by lia. reflexivity.
  Qed.

  Section Cell.
    Variable state : Z.
    Hypothesis ST : 0 <= state < 2^(st_log t).

    Lemma seq_rdn_cell : forall (i : Z) (n : nat), 0 <= i -> (Z.to_nat i + n <= 8)%nat ->
      rdn segs m (wa (T + 8 * state + (8 + i))) n = Some (map (Z_to_bv 8) (firstn n (skipn (Z.to_nat i) (seqsym_bytes (st_cell t state))))).
    Proof.
      intros i n Hi Hn. replace (T + 8 * state + (8 + i)) with (T + (8 + 8 * state + i)) by lia.
      rewrite seq_rdn_at by lia. rewrite (seq_cell_img k t OK state ST) by assumption. reflexivity.
    Qed.

    (* [comment removed for export] *)
    Lemma seq_cell_know :
      let c := st_cell t state in
      rdn segs m (wa (T + 8 * state + 8)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (ss_next c))) /\
      rdn segs m (wa (T + 8 * state + 10)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 (ss_nbAdd c))) /\
      rdn segs m (wa (T + 8 * state + 11)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 (ss_nbBits c))) /\
      rdn segs m (wa (T + 8 * state + 12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (ss_base c))) /\
      cell_ok k (st_log t) c.
    Proof.
      intros c. pose proof (seq_cell_facts k t OK state ST) as CO. fold c in CO.
      pose proof CO as (B1 & B2 & B3 & SY). pose proof (sym_ok_kind_bounds k _ SY) as (A1 & A2 & A3 & _).
      pose proof (seq_tl_range k t OK) as R.
      assert (P9 : 2^(st_log t) <= 2^9) by (apply Z.pow_le_mono_r; lia).
      assert (PB : 0 < 2^(ss_nbBits c)) by (apply Z.pow_pos_nonneg; lia).
      assert (PA : 0 < 2^(ss_nbAdd c)) by (apply Z.pow_pos_nonneg; lia).
      change (2^9) with 512 in P9. change (2^32) with 4294967296 in *. change (2^17) with 131072 in *.
      split; [|split; [|split; [|split; [|exact CO]]]].
      - replace (T + 8 * state + 8) with (T + 8 * state + (8 + 0)) by lia. rewrite seq_rdn_cell by (cbn; lia).
        rewrite wle2 by lia. reflexivity.
      - replace (T + 8 * state + 10) with (T + 8 * state + (8 + 2)) by lia. rewrite seq_rdn_cell by (cbn; lia).
        rewrite wle1 by (destruct k; lia). reflexivity.
      - replace (T + 8 * state + 11) with (T + 8 * state + (8 + 3)) by lia. rewrite seq_rdn_cell by (cbn; lia).
        rewrite wle1 by lia. reflexivity.
      - replace (T + 8 * state + 12) with (T + 8 * state + (8 + 4)) by lia. rewrite seq_rdn_cell by (cbn; lia).
        rewrite wle4 by (destruct k; lia). reflexivity.
    Qed.
  End Cell.
End Rdn.
