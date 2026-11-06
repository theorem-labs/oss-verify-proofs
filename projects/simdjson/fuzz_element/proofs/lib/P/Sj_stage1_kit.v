(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Notation mem := (word -> option byte).
Definition wz (z : Z) : word := Z_to_bv 64 z.
Definition S1_LEN_MAX : Z := 1048512.

Definition zbytes (l : list Z) : list byte := map (Z_to_bv 8) l.
Definition TABLE_BYTES : list byte := zbytes char_table.

Definition padded_bytes (bs : list Z) : list byte := zbytes bs ++ repeat (Z_to_bv 8 0) 64.

Lemma zbytes_length : forall l, length (zbytes l) = length l.
Proof. intros. unfold zbytes. apply length_map. Qed.
Lemma padded_bytes_length : forall bs, length (padded_bytes bs) = (length bs + 64)%nat.
Proof. intros. unfold padded_bytes. rewrite length_app, zbytes_length, repeat_length. reflexivity. Qed.

Lemma padded_bytes_blen : forall bs, Z.of_nat (length (padded_bytes bs)) = (blen bs + 64)%Z.
Proof. intros. rewrite padded_bytes_length. unfold blen. lia. Qed.

Lemma table_length : length TABLE_BYTES = 256%nat. Proof. reflexivity. Qed.

Lemma nth_error_zbytes : forall l i, (i < length l)%nat -> nth_error (zbytes l) i = Some (Z_to_bv 8 (nth i l 0%Z)).
Proof.
  intros l i H. unfold zbytes. rewrite nth_error_map.
  rewrite (nth_error_nth' l 0%Z H). reflexivity.
Qed.

Lemma nth_error_padded : forall bs i, (0 <= i < blen bs + 64)%Z ->
  nth_error (padded_bytes bs) (Z.to_nat i) = Some (Z_to_bv 8 (B bs i)).
Proof.
  intros bs i H. unfold padded_bytes, B, blen in *.
  destruct (Nat.lt_ge_cases (Z.to_nat i) (length bs)) as [L|L].
  - rewrite nth_error_app1 by (rewrite zbytes_length; exact L). apply nth_error_zbytes. exact L.
  - rewrite nth_error_app2 by (rewrite zbytes_length; exact L). rewrite zbytes_length.
    rewrite (nth_overflow bs 0%Z L).
    rewrite nth_error_repeat by lia. reflexivity.
Qed.

Lemma buf_read_g : forall segs (m : mem) A bs i,
  bytes_at segs m A (padded_bytes bs) -> (0 <= i < blen bs + 64)%Z ->
  ov_read_bytes segs m (wa (A + i)) 1 = Some [Z_to_bv 8 (B bs i)].
Proof.
  intros segs m A bs i H Hi. eapply (u8ro_read segs m A (padded_bytes bs) i); [exact H| apply nth_error_padded; exact Hi | lia | reflexivity].
Qed.

Lemma tbl_read_g : forall segs (m : mem) A c,
  bytes_at segs m A TABLE_BYTES -> (0 <= c < 256)%Z ->
  ov_read_bytes segs m (wa (A + c)) 1 = Some [Z_to_bv 8 (tbl c)].
Proof.
  intros segs m A c H Hc. eapply (u8ro_read segs m A TABLE_BYTES c); [exact H| | lia | reflexivity].
  unfold TABLE_BYTES, tbl. apply nth_error_zbytes. change (length char_table) with 256%nat. lia.
Qed.

Lemma table_at_g : forall segs addr m, ro_bytes_b segs addr TABLE_BYTES = true -> (0 <= addr)%Z -> (addr + 256 <= 2^64)%Z ->
  mem_inv segs m -> bytes_at segs m addr TABLE_BYTES.
Proof.
  intros segs addr m TI A0 A1 MI. apply ro_bytes_at; [exact MI| exact A0 | rewrite table_length; exact A1 |].
  apply ro_bytes_b_sound. exact TI.
Qed.

Lemma tbl_range : forall c, (0 <= tbl c < 16)%Z.
Proof.
  intros c. unfold tbl.
  destruct (Nat.lt_ge_cases (Z.to_nat c) 256) as [L|L].
  - assert (F : Forall (fun x => 0 <= x < 16)%Z char_table) by (repeat constructor; lia).
    rewrite Forall_forall in F. apply F. apply nth_In. exact L.
  - rewrite nth_overflow by exact L. lia.
Qed.

Lemma zxb_small : forall x, (0 <= x < 256)%Z -> zxb (Z_to_bv 8 x) = Z_to_bv 64 x.
Proof.
  intros x H. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.
Lemma sxb_small : forall x, (0 <= x < 256)%Z ->
  sxb (Z_to_bv 8 x) = Z_to_bv 64 (if (x <? 128)%Z then x else x - 256)%Z.
Proof.
  intros x H. unfold sxb. f_equal. unfold bv_signed. rewrite Z_to_bv_unsigned.
  rewrite (bv_wrap_small 8 x) by (unfold bv_modulus; cbn; lia).
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 8)%Z with 256%Z. change (256 / 2)%Z with 128%Z.
  destruct (Z.ltb_spec x 128).
  - rewrite Z.mod_small by lia. lia.
  - replace (x + 128)%Z with ((x - 128) + 1 * 256)%Z by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Definition memcpy_post_g (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (src : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ rw_cells segs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
    /\ bytes_at segs m' (bv_unsigned a1) src.

Definition memcpy_stmt_g (segs : list Segment) (entry : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (src junk : list byte),
  bytes_at segs m (bv_unsigned a1) src ->
  length src = Z.to_nat (bv_unsigned a2) ->
  rw_cells segs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  (bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
  mem_inv segs m ->
  evt segs (memcpy_post_g segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Lemma rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] WR].
    pose proof (cells_bytes_length cs1 W1) as L1. rewrite L1 in B2.
    destruct WR as (HA & HN & HW).
    split; [split; [split; assumption|] | split; [split; assumption|]].
    + split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i)%Z with (A + (Z.of_nat (cells_size cs1) + i))%Z by lia. apply HW. lia.
  - intros [[[W1 B1] (HA1 & HN1 & HW1)] [[W2 B2] (HA2 & HN2 & HW2)]].
    pose proof (cells_bytes_length cs1 W1) as L1.
    split; [split; [split; assumption|] |].
    + split; [exact B1|]. rewrite L1. exact B2.
    + split; [lia|]. split; [lia|]. intros i Hi. destruct (Z_lt_dec i (Z.of_nat (cells_size cs1))).
      * apply HW1. lia.
      * replace (A + i)%Z with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1)))%Z by lia. apply HW2. lia.
Qed.

Lemma rw_cells_forget_C8 : forall segs m A pre v post,
  rw_cells segs m A (pre ++ C8 v :: post) -> rw_cells segs m A (pre ++ CB 8 (le8 v) :: post).
Proof.
  intros segs m A pre v post H.
  pose proof (rw_cells_merge segs m A pre [C8 v] post H) as M.
  cbn [cells_size cells_bytes csize cbytes Nat.add] in M. rewrite app_nil_r in M. exact M.
Qed.

Lemma swrap32_small : forall x, (-2147483648 <= x < 2147483648)%Z -> bv_swrap 32 x = x.
Proof.
  intros x H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 / 2)%Z with 2147483648%Z.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma u8_small : forall c, (0 <= c < 256)%Z -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. intros c H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.
Lemma s8_small : forall c, (0 <= c < 256)%Z -> bv_signed (Z_to_bv 8 c) = (if (c <? 128)%Z then c else c - 256)%Z.
Proof.
  intros c H. pose proof (sxb_small c H) as S. unfold sxb in S.
  apply (f_equal bv_unsigned) in S. rewrite !Z_to_bv_unsigned in S.
  pose proof (bv_signed_in_range 8 (Z_to_bv 8 c) ltac:(lia)) as R. unfold bv_half_modulus, bv_modulus in R.
  change (2 ^ Z.of_N 8 / 2)%Z with 128%Z in R.
  destruct (Z.ltb_spec c 128).
  - unfold bv_wrap, bv_modulus in S. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in S.
    destruct (Z.lt_ge_cases (bv_signed (Z_to_bv 8 c)) 0).
    + rewrite <- (Z.mod_add _ 1) in S by lia. rewrite !Z.mod_small in S by lia. lia.
    + rewrite !Z.mod_small in S by lia. exact S.
  - unfold bv_wrap, bv_modulus in S. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in S.
    rewrite <- (Z.mod_add (c - 256) 1) in S by lia.
    destruct (Z.lt_ge_cases (bv_signed (Z_to_bv 8 c)) 0).
    + rewrite <- (Z.mod_add (bv_signed _) 1) in S by lia. rewrite !Z.mod_small in S by lia. lia.
    + rewrite !Z.mod_small in S by lia. lia.
Qed.

Ltac s1norm :=
  cbv beta;
  repeat match goal with
  | |- context [zxb (Z_to_bv 8 ?c)] => rewrite (zxb_small c) by lia
  | |- context [sxb (Z_to_bv 8 ?c)] => rewrite (sxb_small c) by lia
  | |- context [bv_unsigned (Z_to_bv 8 ?c)] => rewrite (u8_small c) by lia
  | |- context [bv_signed (Z_to_bv 8 ?c)] => rewrite (s8_small c) by lia
  | |- context [bv_swrap 32 ?x] => rewrite (swrap32_small x) by lia
  | |- context [Z.modulo ?x 4294967296] => rewrite (Z.mod_small x 4294967296) by lia
  end.

Record s1env : Type := mkS1Env {
  e_ra : word; e_sp : word; e_gp : word; e_tp : word;
  e_s0 : word; e_s1 : word; e_s2 : word; e_s3 : word; e_s4 : word; e_s5 : word;
  e_s6 : word; e_s7 : word; e_s8 : word; e_s9 : word; e_s10 : word; e_s11 : word;
  e_F : bvmap 5 word; e_fc : bv 32;
  e_lo : Z; e_THIS : Z; e_BUF : Z; e_IDX : Z;
  e_bs : list Z; e_cap : nat;
  e_vptr : word; e_p12 : list byte; e_mid : list byte; e_docj : list byte;
  e_m0 : mem
}.

Notation e_len E := (blen (e_bs E)).

Record env_ok_g (FS GTOP : Z) (E : s1env) : Prop := mkEnvOk {
  ok_bytes : bytes_ok (e_bs E);
  ok_len : (e_len E <= S1_LEN_MAX)%Z;
  ok_glo : (GTOP <= e_lo E)%Z;
  ok_room : (e_lo E + FS <= bv_unsigned (e_sp E))%Z;
  ok_this : (0 <= e_THIS E /\ e_THIS E + 96 <= e_lo E)%Z;
  ok_idx : (0 <= e_IDX E /\ e_IDX E + 4 * Z.of_nat (e_cap E) <= e_lo E)%Z;
  ok_buf : (0 <= e_BUF E /\ e_BUF E + e_len E + 64 <= e_lo E)%Z;
  ok_cap : (e_len E + 3 <= Z.of_nat (e_cap E))%Z;
  ok_this_idx : (e_THIS E + 96 <= e_IDX E \/ e_IDX E + 4 * Z.of_nat (e_cap E) <= e_THIS E)%Z;
  ok_this_buf : (e_THIS E + 96 <= e_BUF E \/ e_BUF E + e_len E + 64 <= e_THIS E)%Z;
  ok_idx_buf : (e_IDX E + 4 * Z.of_nat (e_cap E) <= e_BUF E \/ e_BUF E + e_len E + 64 <= e_IDX E)%Z
}.

Definition s1_W_g (FS : Z) (E : s1env) : list ivl :=
  [ (bv_unsigned (e_sp E) + - FS, bv_unsigned (e_sp E));
    (e_THIS E, e_THIS E + 96);
    (e_IDX E, e_IDX E + 4 * Z.of_nat (e_cap E)) ]%Z.

Definition parser_cells (E : s1env) (nsi nxt bufv lenv : word) : list cell :=
  [C8 (e_vptr E); C4 nsi; CB 4 (e_p12 E); C8 (wz (e_IDX E)); C4 nxt; CB 44 (e_mid E); C8 bufv; C8 lenv; CB 8 (e_docj E)].

Lemma rw_cells_CB_bytes_at : forall segs m A n bs, rw_cells segs m A [CB n bs] -> bytes_at segs m A bs.
Proof. intros segs m A n bs [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Lemma frlo_forget : forall segs m A c0 c1,
  rw_cells segs m A [c0; c1] -> csize c0 = 8%nat -> csize c1 = 8%nat ->
  exists j0 j8, rw_cells segs m A [CB 8 j0; CB 8 j8].
Proof.
  intros segs m A c0 c1 H E0 E1.
  pose proof (rw_cells_merge segs m A [] [c0] [c1] H) as M. cbn [app cells_size cells_bytes] in M.
  rewrite E0, app_nil_r in M. cbn [Nat.add] in M.
  pose proof (rw_cells_merge segs m A [CB 8 (cbytes c0)] [c1] [] M) as M2. cbn [app cells_size cells_bytes] in M2.
  rewrite E1, app_nil_r in M2. cbn [Nat.add] in M2.
  eexists _, _. exact M2.
Qed.

Lemma rw_cells_C8_read1_g : forall segs m A v rest,
  rw_cells segs m A (C8 v :: rest) -> ov_read_bytes segs m (wa A) 1 = Some [Z_to_bv 8 (bv_unsigned v)].
Proof.
  intros segs m A v rest [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb.
  pose proof (bytes_at_read segs m A _ 0 1 Hb ltac:(lia)) as R.
  rewrite Z.add_0_r in R. rewrite R.
  - reflexivity.
  - rewrite length_app, length_le8. cbn. lia.
Qed.

Definition sbyte (c : Z) : Z := if (c <? 128)%Z then c else (c - 256)%Z.

Lemma sbyte_signed : forall c, (0 <= c < 256)%Z ->
  bv_signed (Z_to_bv 64 (if (c <? 128)%Z then c else (c - 256)%Z)) = sbyte c.
Proof.
  intros c H. unfold sbyte. set (s := if (c <? 128)%Z then c else (c - 256)%Z).
  assert (R : (-256 <= s < 256)%Z) by (subst s; destruct (c <? 128)%Z; lia).
  unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z. change (18446744073709551616 / 2)%Z with 9223372036854775808%Z.
  rewrite Zplus_mod_idemp_l. rewrite Z.mod_small by lia. lia.
Qed.

Lemma not_cont_of_gt : forall c, (0 <= c < 256)%Z -> (-65 < sbyte c)%Z -> negb (is_cont c) = true.
Proof.
  intros c H G. unfold sbyte in G. unfold is_cont.
  destruct (Z.ltb_spec c 128); destruct (Z.leb_spec 128 c); destruct (Z.leb_spec c 191); cbn; try reflexivity; lia.
Qed.
Lemma cont_of_le : forall c, (0 <= c < 256)%Z -> (sbyte c <= -65)%Z -> negb (is_cont c) = false.
Proof.
  intros c H G. unfold sbyte in G. unfold is_cont.
  destruct (Z.ltb_spec c 128); destruct (Z.leb_spec 128 c); destruct (Z.leb_spec c 191); cbn; try reflexivity; lia.
Qed.
Lemma cont_range : forall c, (0 <= c < 256)%Z -> (sbyte c <= -65)%Z -> (128 <= c <= 191)%Z.
Proof. intros c H G. unfold sbyte in G. destruct (Z.ltb_spec c 128); lia. Qed.

Lemma spill_byte : forall c, (0 <= c < 256)%Z ->
  Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (if (c <? 128)%Z then c else (c - 256)%Z))) = Z_to_bv 8 c.
Proof.
  intros c H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z. change (2 ^ Z.of_N 8)%Z with 256%Z.
  destruct (Z.ltb_spec c 128).
  - rewrite (Z.mod_small c 18446744073709551616) by lia. reflexivity.
  - replace (c - 256)%Z with (c + (-1) * 256)%Z by lia.
    rewrite <- (Z.mod_add (c + -1 * 256) 1 18446744073709551616) by lia.
    rewrite (Z.mod_small (c + -1 * 256 + 1 * 18446744073709551616)) by lia.
    replace (c + -1 * 256 + 1 * 18446744073709551616)%Z with (c + 72057594037927935 * 256)%Z by lia.
    rewrite Z.mod_add by lia. reflexivity.
Qed.

Ltac s1_cur_mem k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => k m end.

Lemma spill_byte_land : forall c, (0 <= c < 256)%Z ->
  Z.land (bv_unsigned (Z_to_bv 64 (if (c <? 128)%Z then c else (c - 256)%Z))) 255 = c.
Proof.
  intros c H. pose proof (spill_byte c H) as S. apply (f_equal bv_unsigned) in S.
  rewrite !Z_to_bv_unsigned in S. unfold bv_wrap at 1 3 in S. unfold bv_modulus in S. change (2 ^ Z.of_N 8)%Z with 256%Z in S.
  rewrite (Z.mod_small c 256) in S by lia.
  change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8)%Z with 256%Z.
  rewrite Z_to_bv_unsigned. exact S.
Qed.

Lemma bit7_set : forall b, (0 <= b < 256)%Z -> (9223372036854775808 <= Z.shiftl b 56 mod 18446744073709551616)%Z -> (128 <= b)%Z.
Proof.
  intros b H K. rewrite Z.shiftl_mul_pow2 in K by lia. change (2 ^ 56)%Z with 72057594037927936%Z in K.
  rewrite Z.mod_small in K by lia. lia.
Qed.
Lemma bit7_clear : forall b, (0 <= b < 256)%Z -> (Z.shiftl b 56 mod 18446744073709551616 < 9223372036854775808)%Z -> (b < 128)%Z.
Proof.
  intros b H K. rewrite Z.shiftl_mul_pow2 in K by lia. change (2 ^ 56)%Z with 72057594037927936%Z in K.
  rewrite Z.mod_small in K by lia. lia.
Qed.

Lemma firstn_upd_push : forall {X} (l : list X) n v, (n < length l)%nat ->
  firstn (S n) (upd l n v) = firstn n l ++ [v].
Proof.
  intros X l. induction l as [|y l IH]; intros [|n] v H; cbn in H |- *; try lia; [reflexivity|].
  rewrite IH by lia. reflexivity.
Qed.

Lemma arr_push : forall (ws : list word) (out : list Z) (v : Z),
  firstn (length out) ws = map wz out -> (length out < length ws)%nat ->
  firstn (length (out ++ [v])) (upd ws (length out) (wz v)) = map wz (out ++ [v]).
Proof.
  intros ws out v F L. rewrite length_app. cbn [length]. rewrite Nat.add_1_r.
  rewrite firstn_upd_push by exact L. rewrite F, map_app. reflexivity.
Qed.

Definition s1_post_g (segs : list Segment) (FS : Z) (E : s1env) (code : Z) (out : list Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m' : mem) (ws' : list word) (nxt' : word),
    ms' = MS (mkR (e_ra E) (e_sp E) (e_gp E) (e_tp E) t0 t1 t2 (e_s0 E) (e_s1 E) (wz code) a1 a2 a3 a4 a5 a6 a7
                  (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E) t3 t4 t5 t6)
             (e_F E) (ret_pc (e_ra E)) (e_fc E) None m' (seg_rom segs)
    /\ munch (s1_W_g FS E) (e_m0 E) m' /\ wmono segs (e_m0 E) m' /\ mem_inv segs m'
    /\ stk segs m' (e_lo E) (bv_unsigned (e_sp E))
    /\ rw_cells segs m' (e_THIS E) (parser_cells E (wz (Z.of_nat (length out))) nxt' (wz (e_BUF E)) (wz (e_len E)))
    /\ (code <> 13%Z -> nxt' = wz 0)
    /\ u32arr segs m' (e_IDX E) ws' /\ length ws' = e_cap E
    /\ firstn (length out + 3) ws' = map wz (out ++ [e_len E; e_len E; 0%Z])
    /\ bytes_at segs m' (e_BUF E) (padded_bytes (e_bs E)).

Lemma firstn_upd_above : forall {X} (l : list X) k n v, (k <= n)%nat -> firstn k (upd l n v) = firstn k l.
Proof.
  intros X l. induction l as [|y l IH]; intros k n v H; [destruct n; reflexivity|].
  destruct n as [|n]; destruct k as [|k]; cbn; try reflexivity; try lia.
  rewrite IH by lia. reflexivity.
Qed.

Lemma arr_push3 : forall (ws : list word) (out : list Z) (a b c : Z),
  firstn (length out) ws = map wz out -> (length out + 3 <= length ws)%nat ->
  firstn (length out + 3) (upd (upd (upd ws (length out) (wz a)) (length out + 1) (wz b)) (length out + 2) (wz c))
  = map wz (out ++ [a; b; c]).
Proof.
  intros ws out a b c F L.
  replace (length out + 3)%nat with (S (length out + 2)) by lia.
  rewrite firstn_upd_push by (rewrite !upd_length; lia).
  replace (length out + 2)%nat with (S (length out + 1)) by lia.
  rewrite firstn_upd_push by (rewrite !upd_length; lia).
  replace (length out + 1)%nat with (S (length out)) by lia.
  rewrite firstn_upd_push by lia.
  rewrite F, map_app. cbn [map]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma sx32_small : forall x, (0 <= x < 2147483648)%Z -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
  intros x H. unfold sx32. rewrite Z_to_bv_unsigned, (bv_wrap_small 64 x) by (unfold bv_modulus; cbn; lia).
  rewrite swrap32_small by lia. reflexivity.
Qed.

Lemma lor_b2z : forall a b : bool, Z.lor (Z.b2z a) (Z.b2z b) = Z.b2z (a || b).
Proof. intros [] []; reflexivity. Qed.

Ltac s1_st_eq_leaf :=
  lazymatch goal with
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; rewrite ?length_app; cbn [length app s_idx s_out s_err s_unclosed]; lia]
  | |- _ => reflexivity
  end.
Ltac s1_st_eq_tree :=
  lazymatch goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal; s1_st_eq_tree
  | |- Some _ = Some _ => f_equal; s1_st_eq_leaf
  | |- _ => reflexivity
  end.
Ltac s1_st_eq :=
  unfold wz; cbv delta [mkR];
  lazymatch goal with
  | |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => f_equal; s1_st_eq_tree
  end.

Lemma rw_cells_C8_read1_at : forall segs m A pre v rest,
  rw_cells segs m A (pre ++ C8 v :: rest) ->
  ov_read_bytes segs m (wa (A + Z.of_nat (cells_size pre))) 1 = Some [Z_to_bv 8 (bv_unsigned v)].
Proof.
  intros segs m A pre v rest H. apply rw_cells_app in H. destruct H as [_ H].
  eapply rw_cells_C8_read1_g. exact H.
Qed.
