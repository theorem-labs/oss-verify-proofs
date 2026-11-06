From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Bytes.
Import ListNotations.
Open Scope Z_scope.

(** ---- arithmetic ---- *)

Lemma ta_u64 : forall x : word, 0 <= bv_unsigned x < 2^64.
Proof. intros x. exact (bv_unsigned_in_range 64 x). Qed.

Lemma ta_u8 : forall x : byte, 0 <= bv_unsigned x < 256.
Proof. intros x. exact (bv_unsigned_in_range 8 x). Qed.

(** The compiler's `v % 65` for a 16-bit v: q = (v * 4033) >> 18 is v / 65 (4033 * 65 = 2^18 + 1, and
    q + 4033 * (v mod 65) < 2^18 when v < 2^16), so v - q - 64 q = v mod 65. *)
Lemma ta_mod65_magic : forall v, 0 <= v < 65536 -> (v * 4033) / 2^18 = v / 65.
Proof.
  intros v Hv.
  pose proof (Z.div_mod v 65 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound v 65 ltac:(lia)) as Hr.
  assert (Hq : 0 <= v / 65 <= 1008) by lia.
  symmetry. apply (Z.div_unique (v * 4033) (2^18) (v / 65) (v / 65 + 4033 * (v mod 65))).
  - left. change (2^18) with 262144. lia.
  - change (2^18) with 262144. lia.
Qed.

Lemma ta_lor_byte : forall x0 x1, 0 <= x0 < 256 -> 0 <= x1 ->
  Z.lor (Z.shiftl x1 8) x0 = x0 + 256 * x1.
Proof. intros x0 x1 H0 H1. rewrite Z.lor_comm. apply lor_shiftl8_add; lia. Qed.

(** The register value the plain and ubsan images compute for `v % 65` from the two input bytes x0 (low)
    and x1 (high): or, mul by 4033, srli 18, slli 6, two subw, slli 48 / srli 48. *)
Lemma ta_mod65_seq : forall x0 x1, 0 <= x0 < 256 -> 0 <= x1 < 256 ->
  (Z.modulo (Z.modulo (bv_swrap 32 (Z.sub (Z.modulo (bv_swrap 32 (Z.sub (Z.lor (Z.modulo (Z.shiftl x1 8) 18446744073709551616) x0) (Z.shiftr (Z.modulo (Z.mul (Z.lor (Z.modulo (Z.shiftl x1 8) 18446744073709551616) x0) 4033) 18446744073709551616) 18))) 18446744073709551616) (Z.modulo (Z.shiftl (Z.shiftr (Z.modulo (Z.mul (Z.lor (Z.modulo (Z.shiftl x1 8) 18446744073709551616) x0) 4033) 18446744073709551616) 18) 6) 18446744073709551616))) 18446744073709551616) 65536) = (x0 + 256 * x1) mod 65.
Proof.
  intros x0 x1 H0 H1.
  assert (S8 : Z.modulo (Z.shiftl x1 8) 18446744073709551616 = Z.shiftl x1 8).
  { apply Z.mod_small. rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256. lia. }
  rewrite S8, (ta_lor_byte x0 x1 H0 ltac:(lia)).
  remember (x0 + 256 * x1) as v eqn:Hv.
  assert (Rv : 0 <= v < 65536) by lia.
  rewrite (Z.mod_small (v * 4033) 18446744073709551616) by lia.
  rewrite Z.shiftr_div_pow2 by lia. rewrite ta_mod65_magic by exact Rv.
  pose proof (Z.div_mod v 65 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound v 65 ltac:(lia)) as Hr.
  assert (Hq : 0 <= v / 65 <= 1008) by lia.
  rewrite (bv_swrap_small 32 (v - v / 65)) by (change (bv_half_modulus 32) with 2147483648; lia).
  rewrite (Z.mod_small (v - v / 65) 18446744073709551616) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. change (2^6) with 64.
  rewrite (Z.mod_small (v / 65 * 64) 18446744073709551616) by lia.
  rewrite (bv_swrap_small 32 (v - v / 65 - v / 65 * 64)) by (change (bv_half_modulus 32) with 2147483648; lia).
  rewrite (Z.mod_small (v - v / 65 - v / 65 * 64) 18446744073709551616) by lia.
  rewrite (Z.mod_small (v - v / 65 - v / 65 * 64) 65536) by lia. lia.
Qed.

(** ---- the cursor bytes ---- *)

(** One input byte p[k] (k < n) as the load sees it. *)
Lemma ta_byte : forall segs m a (bs : list byte) (k : Z),
  bytes_at segs m a bs -> 0 <= k < Z.of_nat (length bs) ->
  ov_read_bytes segs m (wa (a + k)) 1 = Some [nth (Z.to_nat k) bs (Z_to_bv 8 0)].
Proof.
  intros segs m a bs k H Hk.
  rewrite (bytes_at_read segs m a bs k 1 H) by lia.
  f_equal. remember (Z.to_nat k) as j. assert (j < length bs)%nat by lia. clear Heqj Hk H.
  revert j H0. induction bs as [|x bs IH]; intros j Hj; cbn in *; [lia|].
  destruct j as [|j]; [reflexivity|]. apply IH. lia.
Qed.

(** The k bytes from p + c, at the address the 64-bit register p + c names (when k = 0 the address may be
    any word). *)
Lemma ta_bytes_sub : forall segs m p (data : list byte) (c : Z) (k : nat),
  0 <= c -> (Z.to_nat c + k <= length data)%nat ->
  bytes_at segs m p data ->
  bytes_at segs m (bv_unsigned (Z_to_bv 64 (p + c))) (firstn k (skipn (Z.to_nat c) data)).
Proof.
  intros segs m p data c k Hc Hck HD.
  pose proof (bytes_at_bound segs m p data HD) as Bd.
  destruct k as [|k].
  - cbn [firstn]. apply bytes_at_nil. pose proof (ta_u64 (Z_to_bv 64 (p + c))). lia.
  - rewrite unsigned_lit by lia.
    rewrite <- (firstn_skipn (Z.to_nat c) data) in HD. apply bytes_at_app in HD. destruct HD as [_ HD].
    rewrite firstn_length_le in HD by lia. rewrite Z2Nat.id in HD by lia.
    rewrite <- (firstn_skipn (S k) (skipn (Z.to_nat c) data)) in HD. apply bytes_at_app in HD.
    destruct HD as [HD _]. exact HD.
Qed.

(** ---- the text buffer ---- *)

Lemma ta_rw_split : forall segs m A (k n : nat) bs, (k <= n)%nat ->
  rw_cells segs m A [CB n bs] ->
  rw_cells segs m A [CB k (firstn k bs)] /\ rw_cells segs m (A + Z.of_nat k) [CB (n - k) (skipn k bs)].
Proof.
  intros segs m A k n bs Hk [[Hwf Hb] Hw].
  cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw.
  destruct Hw as (Hw0 & Hwn & Hw).
  rewrite <- (firstn_skipn k bs) in Hb. apply bytes_at_app in Hb. destruct Hb as [Hb1 Hb2].
  rewrite firstn_length_le in Hb2 by lia.
  split; split; [split | | split | ].
  - cbn [cells_wf cell_wf]. split; [rewrite firstn_length_le; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb1.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - cbn [cells_wf cell_wf]. split; [rewrite length_skipn; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb2.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat k + i) with (A + (Z.of_nat k + i)) by lia. apply Hw. lia.
Qed.

Lemma ta_rw_join : forall segs m A n1 bs1 n2 bs2,
  rw_cells segs m A [CB n1 bs1] -> rw_cells segs m (A + Z.of_nat n1) [CB n2 bs2] ->
  rw_cells segs m A [CB (n1 + n2) (bs1 ++ bs2)].
Proof.
  intros segs m A n1 bs1 n2 bs2 [[Hwf1 Hb1] Hw1] [[Hwf2 Hb2] Hw2].
  cbn [cells_wf cell_wf] in Hwf1, Hwf2. destruct Hwf1 as [Hl1 _]. destruct Hwf2 as [Hl2 _].
  cbn [cells_bytes cbytes] in Hb1, Hb2. rewrite app_nil_r in Hb1, Hb2.
  cbn [cells_size csize] in Hw1, Hw2. rewrite Nat.add_0_r in Hw1, Hw2.
  destruct Hw1 as (W10 & W11 & W1). destruct Hw2 as (W20 & W21 & W2).
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [rewrite length_app; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact Hb1|]. rewrite Hl1. exact Hb2.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec0 i (Z.of_nat n1)).
    + apply W1. lia.
    + replace (A + i) with (A + Z.of_nat n1 + (i - Z.of_nat n1)) by lia. apply W2. lia.
Qed.

Lemma ta_rw_c1 : forall segs m A b, rw_cells segs m A [C1 b] -> rw_cells segs m A [CB 1 [b]].
Proof.
  intros segs m A b [[_ Hb] Hw]. split; [split|].
  - cbn [cells_wf cell_wf]. split; [reflexivity | exact I].
  - exact Hb.
  - exact Hw.
Qed.

Lemma ta_rw_cb_eq : forall segs m A k k' bs, rw_cells segs m A [CB k bs] -> k = k' -> rw_cells segs m A [CB k' bs].
Proof. intros; subst; assumption. Qed.

Lemma ta_rw_c8_eq : forall segs m A v0 v1 w0 w1,
  rw_cells segs m A [C8 v0; C8 v1] -> v0 = w0 -> v1 = w1 -> rw_cells segs m A [C8 w0; C8 w1].
Proof. intros; subst; assumption. Qed.

(** The 65 bytes after text_arg: the k copied bytes, the stored 0 byte, the rest as it was. *)
Lemma ta_text_final : forall segs m A (k : nat) src T b rest (n : nat) out,
  rw_cells segs m A [CB k src] ->
  rw_cells segs m T [C1 b] ->
  rw_cells segs m (T + 1) [CB n rest] ->
  T = A + Z.of_nat k -> (k + 1 + n = 65)%nat -> out = src ++ [b] ++ rest ->
  rw_cells segs m A [CB 65 out].
Proof.
  intros segs m A k src T b rest n out H1 H2 H3 HT Hs ->.
  apply ta_rw_c1 in H2.
  pose proof (ta_rw_join segs m T 1 [b] n rest H2) as H23.
  replace (T + Z.of_nat 1) with (T + 1) in H23 by lia.
  specialize (H23 H3). subst T.
  pose proof (ta_rw_join segs m A k src (1 + n) ([b] ++ rest) H1 H23) as H.
  replace (k + (1 + n))%nat with 65%nat in H by lia. exact H.
Qed.
