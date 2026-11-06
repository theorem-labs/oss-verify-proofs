(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Lemma byte_cases : forall (f : Z -> bool), forallb f (zseq 0 256) = true -> forall b, 0 <= b < 256 -> f b = true.
Proof. intros f H b Hb. eapply forallb_forall in H; [exact H|]. apply zseq_in. cbn. lia. Qed.

Definition sext8 (b : Z) : Z := if b <? 128 then b else b - 256.

Lemma hdr_posfix : forall b, 0 <= b < 256 -> (0 <= sext8 b <-> b <= 127).
Proof. intros b Hb. unfold sext8. destruct (Z.ltb_spec b 128); lia. Qed.
Lemma hdr_negfix : forall b, 0 <= b < 256 -> sext8 b < 0 -> 224 <= b -> -32 <= sext8 b <= -1.
Proof. intros b Hb Hs Hc. unfold sext8 in *. destruct (Z.ltb_spec b 128); lia. Qed.

Lemma mask_fixstr : forall b, 0 <= b < 256 -> (Z.land b 224 =? 160) = ((160 <=? b) && (b <=? 191)).
Proof. intros b Hb. apply eqb_prop. revert b Hb. apply (byte_cases (fun b => Bool.eqb (Z.land b 224 =? 160) ((160 <=? b) && (b <=? 191)))). vm_compute. reflexivity. Qed.
Lemma mask_fixarray : forall b, 0 <= b < 256 -> (Z.land b 240 =? 144) = ((144 <=? b) && (b <=? 159)).
Proof. intros b Hb. apply eqb_prop. revert b Hb. apply (byte_cases (fun b => Bool.eqb (Z.land b 240 =? 144) ((144 <=? b) && (b <=? 159)))). vm_compute. reflexivity. Qed.
Lemma mask_low5 : forall b, 0 <= b < 256 -> Z.land b 31 = b mod 32.
Proof. intros b Hb. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma mask_low4 : forall b, 0 <= b < 256 -> Z.land b 15 = b mod 16.
Proof. intros b Hb. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma fixstr_len : forall b, 160 <= b <= 191 -> Z.land b 31 = b - 160 /\ 0 <= b - 160 <= 31.
Proof. intros b Hb. rewrite mask_low5 by lia. split; [|lia]. rewrite <- (Z.mod_add _ (-5)) by lia. rewrite Z.mod_small; lia. Qed.
Lemma fixarray_cnt : forall b, 144 <= b <= 159 -> Z.land b 15 = b - 144 /\ 0 <= b - 144 <= 15.
Proof. intros b Hb. rewrite mask_low4 by lia. split; [|lia]. rewrite <- (Z.mod_add _ (-9)) by lia. rewrite Z.mod_small; lia. Qed.
Lemma fixmap_cnt : forall b, 128 <= b <= 143 -> Z.land b 15 = b - 128 /\ 0 <= b - 128 <= 15.
Proof. intros b Hb. rewrite mask_low4 by lia. split; [|lia]. rewrite <- (Z.mod_add _ (-8)) by lia. rewrite Z.mod_small; lia. Qed.

Lemma trail_index : forall b, 196 <= b <= 223 -> 0 <= b - 196 < 28 /\ 4 * (b - 196) + 4 <= 112.
Proof. intros; lia. Qed.
Lemma cs_of_hdr : forall b, 196 <= b <= 223 -> Z.land b 31 = b - 192 /\ 4 <= b - 192 <= 31.
Proof. intros b Hb. rewrite mask_low5 by lia. split; [|lia]. rewrite <- (Z.mod_add _ (-6)) by lia. rewrite Z.mod_small; lia. Qed.
Lemma cs_jump_index : forall cs, (4 <= cs <= 31 \/ cs = 32 \/ cs = 33 \/ cs = 34) -> 0 <= cs - 4 <= 30.
Proof. intros; lia. Qed.

Definition trail_of (b : Z) : Z :=
  nth (Z.to_nat (b - 196)) [1;2;4;1;2;4;4;8;1;2;4;8;1;2;4;8;2;3;5;9;17;1;2;4;2;4;2;4] 0.
Lemma trail_of_range : forall b, 196 <= b <= 223 -> 1 <= trail_of b <= 17.
Proof.
  intros b Hb. unfold trail_of.
  assert (E : exists k, (k < 28)%nat /\ Z.to_nat (b - 196) = k) by (exists (Z.to_nat (b - 196)); split; [lia|reflexivity]).
  destruct E as (k & Hk & ->). do 28 (destruct k as [|k]; [cbn; lia|]). lia.
Qed.

Lemma avail_test : forall cur pe trail, 0 <= cur <= pe -> pe < 2^64 -> 0 <= trail ->
  ((pe - cur) mod 2^64 <? trail) = (pe - cur <? trail).
Proof. intros. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma advance_ok : forall cur pe trail, 0 <= cur <= pe -> pe < 2^64 -> 1 <= trail -> trail <= pe - cur ->
  cur + (trail - 1) < pe /\ (cur + (trail - 1)) mod 2^64 = cur + (trail - 1) /\ (cur + (trail - 1) + 1) mod 2^64 = cur + trail.
Proof. intros. rewrite !Z.mod_small by lia. lia. Qed.

Lemma trail_u32_exact : forall cur pe trail, 0 <= cur <= pe -> pe - cur < 2^26 -> 0 <= trail <= pe - cur -> trail mod 2^32 = trail.
Proof. intros. apply Z.mod_small. lia. Qed.

Lemma ext_plus1 : forall tmp, 0 <= tmp < 2^32 -> 1 <= tmp + 1 <= 2^32 /\ (tmp + 1) mod 2^64 = tmp + 1.
Proof. intros. rewrite Z.mod_small by lia. lia. Qed.

Lemma noff_minus1 : forall d, 0 <= d < 2^26 -> -2^63 <= d - 1 /\ d - 1 < d.
Proof. intros; lia. Qed.

Lemma measure_decreases : forall cur cur' pe, cur < cur' <= pe -> 0 <= pe - cur' < pe - cur.
Proof. intros; lia. Qed.

Lemma lor_disjoint_add : forall a b k, 0 <= k -> 0 <= a < 2^k -> 0 <= b -> Z.lor a (Z.shiftl b k) = a + b * 2^k.
Proof.
  intros a b k Hk Ha Hb. rewrite Z.shiftl_mul_pow2 by lia.
  assert (D : Z.land a (b * 2^k) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i k) as [L|L].
    - rewrite (Z.mul_pow2_bits_low b k i) by lia. apply Bool.andb_false_r.
    - replace (Z.testbit a i) with false; [reflexivity|]. symmetry.
      destruct (Z.eq_dec a 0) as [->|Hnz]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; [lia|].
      eapply Z.lt_le_trans; [apply (proj2 Ha)|]. apply Z.pow_le_mono_r; lia. }
  rewrite <- Z.lxor_lor by exact D. symmetry. apply Z.add_nocarry_lxor. exact D.
Qed.

Definition be16 (b0 b1 : Z) : Z := b0 * 256 + b1.
Definition be32 (b0 b1 b2 b3 : Z) : Z := ((b0 * 256 + b1) * 256 + b2) * 256 + b3.
Lemma gather16 : forall b0 b1, 0 <= b0 < 256 -> 0 <= b1 < 256 -> Z.lor (Z.shiftl b1 8) b0 = b0 + 256 * b1.
Proof. intros. rewrite Z.lor_comm, (lor_disjoint_add b0 b1 8) by lia. lia. Qed.

Definition bswap16 (x : Z) : Z := Z.lor (Z.shiftl (Z.land x 255) 8) (Z.shiftr x 8).
Lemma bswap16_be : forall b0 b1, 0 <= b0 < 256 -> 0 <= b1 < 256 -> bswap16 (b0 + 256 * b1) = be16 b0 b1.
Proof.
  intros b0 b1 H0 H1. unfold bswap16, be16.
  replace (Z.land (b0 + 256 * b1) 255) with b0.
  2:{ change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2^8) with 256.
      rewrite Z.mul_comm, Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
  replace (Z.shiftr (b0 + 256 * b1) 8) with b1.
  2:{ rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256. rewrite Z.mul_comm, Z.div_add by lia.
      rewrite Z.div_small by lia. lia. }
  rewrite Z.lor_comm, (lor_disjoint_add b1 b0 8) by lia. change (2^8) with 256. lia.
Qed.
Lemma gather32 : forall b0 b1 b2 b3, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  Z.lor (Z.lor (Z.shiftl b3 24) (Z.shiftl b2 16)) (Z.lor (Z.shiftl b1 8) b0) = b0 + 256 * b1 + 65536 * b2 + 16777216 * b3.
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3.
  rewrite (Z.lor_comm (Z.shiftl b1 8) b0), (lor_disjoint_add b0 b1 8) by lia.
  rewrite (Z.lor_comm (Z.shiftl b3 24) (Z.shiftl b2 16)).
  rewrite (Z.lor_comm (Z.lor (Z.shiftl b2 16) (Z.shiftl b3 24)) (b0 + b1 * 2^8)).
  rewrite Z.lor_assoc.
  change (2^8) with 256.
  rewrite (lor_disjoint_add (b0 + b1 * 256) b2 16) by (change (2^16) with 65536; lia). change (2^16) with 65536.
  rewrite (lor_disjoint_add (b0 + b1 * 256 + b2 * 65536) b3 24) by (change (2^24) with 16777216; lia). change (2^24) with 16777216.
  lia.
Qed.
Lemma be_range16 : forall b0 b1, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= be16 b0 b1 < 2^16.
Proof. intros. unfold be16. lia. Qed.
Lemma be_range32 : forall b0 b1 b2 b3, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 -> 0 <= be32 b0 b1 b2 b3 < 2^32.
Proof. intros. unfold be32. lia. Qed.

Lemma limit_check : forall size, 0 <= size < 2^32 -> ((LIMIT <? size) = false <-> size <= LIMIT).
Proof. intros. unfold LIMIT. rewrite Z.ltb_ge. lia. Qed.

Lemma depth_check : forall b e, 0 <= b <= e -> (e - b) mod 8 = 0 -> Z.shiftr (e - b) 3 = (e - b) / 8.
Proof. intros. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma mul24_shift : forall n, 0 <= n -> Z.shiftl n 5 - Z.shiftl n 3 = OBJ_SIZE * n.
Proof. intros. rewrite !Z.shiftl_mul_pow2 by lia. unfold OBJ_SIZE. change (2^5) with 32. change (2^3) with 8. lia. Qed.
Lemma array_bytes_bound : forall n, 0 <= n <= LIMIT -> 0 <= OBJ_SIZE * n <= 24000 /\ 0 <= KV_SIZE * n <= 48000.
Proof. intros. unfold OBJ_SIZE, KV_SIZE, LIMIT in *. lia. Qed.

Definition align8 (p : Z) : Z := Z.land (p + 7) (-8).
Lemma land_m8 : forall x, 0 <= x -> Z.land x (-8) = x - x mod 8.
Proof.
  intros x Hx. change (-8) with (Z.lnot (Z.ones 3)). rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite (Z.div_mod x 8) at 2 by lia. lia.
Qed.
Lemma align8_spec : forall p, 0 <= p -> p <= align8 p <= p + 7 /\ align8 p mod 8 = 0 /\ (p mod 8 = 0 -> align8 p = p).
Proof.
  intros p Hp. unfold align8. rewrite land_m8 by lia.
  pose proof (Z.mod_pos_bound (p + 7) 8). repeat split; try lia.
  - rewrite Zminus_mod, Z.mod_mod by lia. rewrite Z.sub_diag. reflexivity.
  - intros H0. rewrite <- Zplus_mod_idemp_l, H0. cbn. lia.
Qed.

Lemma alloc_fits : forall ptr free size, 0 <= ptr -> 0 <= size -> 0 <= free ->
  let aligned := align8 ptr in let adjusted := size + (aligned - ptr) in
  adjusted <= free -> aligned + size <= ptr + free /\ ptr <= aligned /\ aligned mod 8 = 0 /\ 0 <= free - adjusted.
Proof. intros ptr free size Hp Hs Hf aligned adjusted Hle. pose proof (align8_spec ptr Hp). subst aligned adjusted. lia. Qed.

Lemma alloc_fresh : forall c sz size, 0 <= c -> c mod 16 = 0 -> 0 <= size -> size + 7 <= sz ->
  align8 (c + 8) = c + 8 /\ c + 8 + size <= c + 8 + sz /\ 0 <= sz - size.
Proof.
  intros c sz size Hc Hm Hs Hsz. pose proof (align8_spec (c + 8) ltac:(lia)) as (A & B & C).
  split; [apply C|lia]. rewrite <- Zplus_mod_idemp_l. replace (c mod 8) with 0; [reflexivity|].
  symmetry. rewrite (Z.div_mod c 16) by lia. rewrite Hm, Z.add_0_r.
  replace (16 * (c / 16)) with ((2 * (c / 16)) * 8) by lia. apply Z_mod_mult.
Qed.

Fixpoint zdouble (fuel : nat) (sz need : Z) : Z :=
  match fuel with
  | O => sz
  | S f => if sz <? need then (if 2 * sz <=? sz then need else zdouble f (2 * sz) need) else sz
  end.
Lemma zdouble_ge : forall fuel sz need, 0 < sz -> sz * 2 ^ Z.of_nat fuel >= need -> need <= zdouble fuel sz need.
Proof.
  induction fuel as [|f IH]; intros sz need Hsz Hf; cbn [zdouble].
  - cbn in Hf. lia.
  - destruct (Z.ltb_spec sz need); [|lia]. destruct (Z.leb_spec (2 * sz) sz); [lia|].
    apply IH; [lia|]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hf by lia. lia.
Qed.
Lemma zdouble_shape : forall fuel sz need, 0 < sz -> sz < 2^62 -> need <= 2^62 ->
  exists k, 0 <= k /\ zdouble fuel sz need = sz * 2^k /\ (zdouble fuel sz need < 2 * need \/ zdouble fuel sz need = sz).
Proof.
  induction fuel as [|f IH]; intros sz need Hsz Hb Hn; cbn [zdouble].
  - exists 0. rewrite Z.pow_0_r. lia.
  - destruct (Z.ltb_spec sz need).
    + destruct (Z.leb_spec (2 * sz) sz); [lia|].
      destruct (Z.lt_ge_cases (2 * sz) (2^62)) as [L|L].
      * destruct (IH (2 * sz) need ltac:(lia) L Hn) as (k & Hk & E & C). exists (k + 1).
        rewrite Z.pow_add_r, Z.pow_1_r by lia. split; [lia|]. split; [lia|]. destruct C; [left; lia| left]. rewrite H1. lia.
      *
        exists 1. rewrite Z.pow_1_r. destruct f; cbn [zdouble]; [split; [lia|split; [lia|left; lia]]|].
        destruct (Z.ltb_spec (2 * sz) need); [lia|]. split; [lia|]. split; [lia|]. left. lia.
    + exists 0. rewrite Z.pow_0_r. lia.
Qed.
Lemma zdouble_lt : forall f sz need, 0 < sz -> sz < need -> zdouble (S f) sz need = zdouble f (2 * sz) need.
Proof.
  intros f sz need Hsz Hlt. cbn [zdouble]. destruct (Z.ltb_spec sz need); [|lia]. destruct (Z.leb_spec (2 * sz) sz); [lia|reflexivity].
Qed.
Lemma zdouble_ge' : forall f sz need, need <= sz -> zdouble f sz need = sz.
Proof. intros [|f] sz need H; cbn [zdouble]; [reflexivity|]. destruct (Z.ltb_spec sz need); [lia|reflexivity]. Qed.

Lemma zdouble_start_array : forall n, 1 <= n <= LIMIT ->
  let sz := zdouble 8 CHUNK_SIZE0 (OBJ_SIZE * n + 7) in OBJ_SIZE * n + 7 <= sz /\ (sz = 8192 \/ sz = 16384 \/ sz = 32768).
Proof.
  intros n Hn sz. subst sz. unfold CHUNK_SIZE0, OBJ_SIZE, LIMIT in *.
  destruct (Z.le_gt_cases (24 * n + 7) 8192). { rewrite zdouble_ge' by lia. lia. }
  change 8%nat with (S 7). rewrite zdouble_lt by lia.
  destruct (Z.le_gt_cases (24 * n + 7) 16384). { rewrite zdouble_ge' by lia. lia. }
  change 7%nat with (S 6). rewrite zdouble_lt by lia. rewrite zdouble_ge' by lia. lia.
Qed.
Lemma zdouble_start_map : forall n, 1 <= n <= LIMIT ->
  let sz := zdouble 8 CHUNK_SIZE0 (KV_SIZE * n + 7) in KV_SIZE * n + 7 <= sz /\ (sz = 8192 \/ sz = 16384 \/ sz = 32768 \/ sz = 65536).
Proof.
  intros n Hn sz. subst sz. unfold CHUNK_SIZE0, KV_SIZE, LIMIT in *.
  destruct (Z.le_gt_cases (48 * n + 7) 8192). { rewrite zdouble_ge' by lia. lia. }
  change 8%nat with (S 7). rewrite zdouble_lt by lia.
  destruct (Z.le_gt_cases (48 * n + 7) 16384). { rewrite zdouble_ge' by lia. lia. }
  change 7%nat with (S 6). rewrite zdouble_lt by lia.
  destruct (Z.le_gt_cases (48 * n + 7) 32768). { rewrite zdouble_ge' by lia. lia. }
  change 6%nat with (S 5). rewrite zdouble_lt by lia. rewrite zdouble_ge' by lia. lia.
Qed.
Lemma zdouble_visit : forall size, 0 <= size <= LIMIT + 1 -> zdouble 8 CHUNK_SIZE0 size = CHUNK_SIZE0.
Proof. intros size Hs. unfold CHUNK_SIZE0, LIMIT in *. apply zdouble_ge'. lia. Qed.

Lemma vec_grow : forall cap size, EMBED_STACK <= cap -> cap <= 1024 -> 0 <= size <= cap ->
  let newcap := Z.max (2 * cap) (size + 1) in newcap = 2 * cap /\ 8 * newcap < 2^61 /\ newcap <= 2048.
Proof. intros. unfold EMBED_STACK in *. subst newcap. lia. Qed.
Lemma cap32_double : forall c, (EMBED_STACK <=? c) && (c mod EMBED_STACK =? 0) && pow2_b (c / EMBED_STACK) = true -> c < 2^40 ->
  (EMBED_STACK <=? 2 * c) && ((2 * c) mod EMBED_STACK =? 0) && pow2_b (2 * c / EMBED_STACK) = true.
Proof.
  intros c H Hc. unfold EMBED_STACK in *.
  apply andb_prop in H. destruct H as [H Hp]. apply andb_prop in H. destruct H as [H1 H2].
  apply Z.leb_le in H1. apply Z.eqb_eq in H2.
  assert (E : c = (c / 32) * 32) by (rewrite (Z.div_mod c 32) at 1 by lia; lia).
  set (q := c / 32) in *.
  replace (2 * c / 32) with (2 * q) by (rewrite E; rewrite Z.mul_assoc, Z.div_mul; lia).
  rewrite (pow2_b_double q Hp) by lia.
  replace ((2 * c) mod 32 =? 0) with true by (symmetry; apply Z.eqb_eq; rewrite E, Z.mul_assoc; apply Z_mod_mult).
  replace (32 <=? 2 * c) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

Lemma evec_grow : forall cap, 0 <= cap <= 1024 -> let newcap := Z.max (2 * cap) (cap + 1) in 1 <= newcap /\ ELEM_SIZE * newcap < 2^20.
Proof. intros. unfold ELEM_SIZE. subst newcap. lia. Qed.

Lemma sbuf_room_test : forall alloc size len, 0 <= size <= alloc -> alloc < 2^64 -> 0 <= len ->
  ((alloc - size) mod 2^64 <? len) = (alloc - size <? len).
Proof. intros. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma sbuf_expand : forall alloc size len, SBUF_INIT <= alloc -> 0 <= size <= alloc -> 0 <= len <= LIMIT + 1 -> alloc < 2^62 ->
  let nsize := 2 * alloc in size + len <= nsize /\ (nsize <? size + len) = false /\ nsize < 2^63 /\ 0 < alloc.
Proof. intros. unfold SBUF_INIT, LIMIT in *. subst nsize. rewrite Z.ltb_ge. lia. Qed.
Lemma sbuf_after_write : forall alloc size len, 0 <= size -> 0 <= len -> size + len <= alloc -> 0 <= size + len <= alloc.
Proof. intros; lia. Qed.
Lemma sbuf_alloc_pow2 : forall alloc, pow2_b (alloc / SBUF_INIT) = true -> alloc mod SBUF_INIT = 0 -> SBUF_INIT <= alloc -> alloc < 2^61 ->
  pow2_b (2 * alloc / SBUF_INIT) = true /\ (2 * alloc) mod SBUF_INIT = 0.
Proof.
  intros alloc Hp Hm Hge Hlt. unfold SBUF_INIT in *.
  assert (E : alloc = (alloc / 8192) * 8192) by (rewrite (Z.div_mod alloc 8192) at 1 by lia; lia).
  set (q := alloc / 8192) in *. split.
  - replace (2 * alloc / 8192) with (2 * q) by (rewrite E; rewrite Z.mul_assoc, Z.div_mul; lia). apply pow2_b_double; [exact Hp| lia].
  - rewrite E, Z.mul_assoc. apply Z_mod_mult.
Qed.

Definition uint_class (d : Z) : Z := if d <? 2^7 then 1 else if d <? 2^8 then 2 else if d <? 2^16 then 3 else if d <? 2^32 then 5 else 9.
Definition int_class (d : Z) : Z :=
  if d <? -32 then (if d <? -32768 then (if d <? -2147483648 then 9 else 5) else (if d <? -128 then 3 else 2))
  else if d <? 128 then 1 else uint_class d.
Definition str_hdr (l : Z) : Z := if l <? 32 then 1 else if l <? 256 then 2 else if l <? 65536 then 3 else 5.
Definition bin_hdr (l : Z) : Z := if l <? 256 then 2 else if l <? 65536 then 3 else 5.
Definition ext_hdr (l : Z) : Z := if (l =? 1) || (l =? 2) || (l =? 4) || (l =? 8) || (l =? 16) then 2 else if l <? 256 then 3 else if l <? 65536 then 4 else 6.
Definition arr_hdr (n : Z) : Z := if n <? 16 then 1 else if n <? 65536 then 3 else 5.
Lemma hdr_small : forall l n d, 0 <= l <= LIMIT -> 0 <= n <= LIMIT ->
  str_hdr l <= 3 /\ bin_hdr l <= 3 /\ ext_hdr l <= 4 /\ arr_hdr n <= 3 /\ 1 <= uint_class d <= 9 /\ 1 <= int_class d <= 9.
Proof.
  intros l n d Hl Hn. unfold str_hdr, bin_hdr, ext_hdr, arr_hdr, int_class, uint_class, LIMIT in *.
  repeat match goal with
         | |- context [if ?a <? ?b then _ else _] => destruct (Z.ltb_spec a b)
         | |- context [if ?c then _ else _] => destruct c end; lia.
Qed.

Lemma write_len_bound : forall l, 0 <= l <= LIMIT -> l <= LIMIT + 1. Proof. intros; lia. Qed.

Lemma ext_size_plus1 : forall n, 0 <= n <= LIMIT - 1 -> (n + 1) mod 2^32 = n + 1 /\ n + 1 <= LIMIT.
Proof. intros. unfold LIMIT in *. rewrite Z.mod_small by lia. lia. Qed.

Lemma pelem_step_array : forall Q N rest, 1 < rest <= N ->
  Q + OBJ_SIZE * 1 * (N - rest) + OBJ_SIZE = Q + OBJ_SIZE * 1 * (N - (rest - 1)).
Proof. intros. unfold OBJ_SIZE. lia. Qed.
Lemma pelem_step_map : forall Q N rest, 1 < rest <= N ->
  Q + OBJ_SIZE * 2 * (N - rest) + KV_SIZE = Q + OBJ_SIZE * 2 * (N - (rest - 1)).
Proof. intros. unfold OBJ_SIZE, KV_SIZE. lia. Qed.
Lemma slot_in_array : forall P n k per, 0 <= k < per * n -> 0 < per -> P <= P + OBJ_SIZE * k /\ P + OBJ_SIZE * k + OBJ_SIZE <= P + OBJ_SIZE * per * n.
Proof. intros. unfold OBJ_SIZE. nia. Qed.
