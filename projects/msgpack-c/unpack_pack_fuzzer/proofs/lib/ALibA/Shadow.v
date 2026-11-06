(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Step Frame Arr Bytes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Export AsanEmbed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition KLOW  : Z := 0x7fff8000.
Definition KHIGH : Z := 0x10007fff8000.
Definition KEND  : Z := 0x800000000000.

Definition LSH_LO : Z := 0x7fff8000.     Definition LSH_HI : Z := 0x8fff7000.
Definition HSH_LO : Z := 0x2008fff7000.  Definition HSH_HI : Z := 0x10007fff8000.

Lemma shad_div : forall a, shad a = ASHOFF + a / 8.
Proof. intros a. unfold shad. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Definition blockf (p n : Z) (s : Z) : Z :=
  let g := s - shad p in if 8 * g + 8 <=? n then 0 else n - 8 * g.

Definition nshad (n : Z) : Z := Z.shiftr (n + 7) 3.

Lemma nshad_div : forall n, nshad n = (n + 7) / 8.
Proof. intros. unfold nshad. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma shad_mono : forall a b, a <= b -> shad a <= shad b.
Proof. intros a b H. rewrite !shad_div. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. Qed.

Lemma shad_aligned : forall p g, p mod 8 = 0 -> shad (p + 8 * g) = shad p + g.
Proof. intros p g Hp. rewrite !shad_div. Z.div_mod_to_equations. nia. Qed.

Lemma shad_aligned' : forall p k, p mod 8 = 0 -> 0 <= k < 8 -> shad (p + k) = shad p.
Proof. intros p k Hp Hk. rewrite !shad_div. Z.div_mod_to_equations. nia. Qed.

Lemma shad_granule : forall a, shad a = ASHOFF + a / 8. Proof. exact shad_div. Qed.

Lemma shad_low : forall a, 0 <= a < KLOW -> LSH_LO <= shad a < LSH_HI.
Proof. intros a H. rewrite shad_div. unfold ASHOFF, KLOW, LSH_LO, LSH_HI in *. Z.div_mod_to_equations. lia. Qed.

Lemma shad_high : forall a, KHIGH <= a < KEND -> HSH_LO <= shad a < HSH_HI.
Proof. intros a H. rewrite shad_div. unfold ASHOFF, KHIGH, KEND, HSH_LO, HSH_HI in *. Z.div_mod_to_equations. lia. Qed.

Definition app_blk (lo hi : Z) : Prop :=
  lo <= hi /\ ((0 <= lo /\ hi + 8 <= KLOW) \/ (KHIGH <= lo /\ hi + 8 <= KEND)).

Lemma app_blk_sub : forall lo hi lo' hi', app_blk lo hi -> lo <= lo' -> lo' <= hi' -> hi' <= hi -> app_blk lo' hi'.
Proof. intros lo hi lo' hi' [H1 H2] A B C. split; [lia|]. unfold KLOW, KHIGH, KEND in *. lia. Qed.

Lemma app_blk_shad : forall lo hi a, app_blk lo hi -> lo <= a < hi + 8 ->
  (LSH_LO <= shad a < LSH_HI) \/ (HSH_LO <= shad a < HSH_HI).
Proof.
  intros lo hi a [H1 H2] Ha. rewrite shad_div.
  unfold ASHOFF, KLOW, KHIGH, KEND, LSH_LO, LSH_HI, HSH_LO, HSH_HI in *. Z.div_mod_to_equations. lia.
Qed.

Definition sval (b : byte) : Z := bv_signed b.

Definition gran_ok (need : Z) (b : byte) : Prop := sval b = 0 \/ need <= sval b <= 7.

Lemma gran_ok_mono : forall n n' b, gran_ok n b -> n' <= n -> gran_ok n' b.
Proof. intros n n' b [H|H] Hle; [left; exact H| right; lia]. Qed.

Lemma gran_ok_full : forall n b, gran_ok n b -> 8 <= n -> b = Z_to_bv 8 0.
Proof.
  intros n b [H|H] Hn; [|lia]. unfold sval in H. apply bv_eq_signed. rewrite H. reflexivity.
Qed.

Lemma sval_zero : sval (Z_to_bv 8 0) = 0. Proof. reflexivity. Qed.
Lemma sval_lit : forall k, 0 <= k <= 127 -> sval (Z_to_bv 8 k) = k.
Proof.
  intros k Hk. unfold sval. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. change (Z.of_N 8 - 1) with 7. change (2^7) with 128. rewrite Z.mod_small by lia. lia.
Qed.

Lemma sval_range : forall b : byte, -128 <= sval b <= 127.
Proof.
  intros b. unfold sval, bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. change (Z.of_N 8 - 1) with 7. change (2^7) with 128.
  pose proof (Z.mod_pos_bound (bv_unsigned b + 128) 256 ltac:(lia)). lia.
Qed.

Lemma land7_mod : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma signed_lit_small64 : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). change (2 ^ (Z.of_N 64 - 1)) with (2^63).
  Z.div_mod_to_equations. lia.
Qed.

Lemma sxb_sval : forall b : byte, sxb b = Z_to_bv 64 (sval b).
Proof. reflexivity. Qed.

Lemma unsigned_sval : forall b : byte, bv_unsigned (Z_to_bv 64 (sval b)) = (sval b) mod 2^64.
Proof. intros b. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma sval_zero_iff : forall b : byte, (sval b) mod 2^64 = 0 <-> sval b = 0.
Proof. intros b. pose proof (sval_range b). Z.div_mod_to_equations. lia. Qed.

Lemma rng_shad_sub : forall RNG RLO RHI lo hi,
  rng RNG (shad RLO) (shad RHI - shad RLO) -> RLO <= lo -> lo < hi -> hi <= RHI -> 0 <= RLO -> RHI mod 8 = 0 ->
  rng RNG (shad lo) (shad (hi - 1) + 1 - shad lo).
Proof.
  intros RNG RLO RHI lo hi R H1 H2 H3 H0 H8. eapply rng_sub'; [exact R|].
  rewrite !shad_div. Z.div_mod_to_equations. lia.
Qed.

Lemma shad_span_aligned : forall A k, A mod 8 = 0 -> shad (A + 8 * k) - shad A = k.
Proof. intros A k HA. rewrite !shad_div. Z.div_mod_to_equations. nia. Qed.

Lemma nshad_span : forall A n, A mod 8 = 0 -> 0 <= n -> shad (A + n - 1) + 1 - shad A <= nshad n.
Proof. intros A n HA Hn. rewrite !shad_div, nshad_div. Z.div_mod_to_equations. nia. Qed.

Lemma rng_shad_block : forall RNG A n lo hi,
  rng RNG (shad A) (nshad n) -> A mod 8 = 0 -> 0 <= A -> A <= lo -> lo < hi -> hi <= A + n ->
  rng RNG (shad lo) (shad (hi - 1) + 1 - shad lo).
Proof.
  intros RNG A n lo hi R HA A0 H1 H2 H3. eapply rng_sub'; [exact R|].
  rewrite !shad_div, nshad_div. Z.div_mod_to_equations. nia.
Qed.

Section WithSegs.
Variable segs : list Segment.

Definition shadow_bytes (m : word -> option byte) (s1 s2 : Z) (f : Z -> Z) : Prop :=
  0 <= s1 /\ s2 <= 2^64 /\ forall s, s1 <= s < s2 -> m (wa s) = Some (Z_to_bv 8 (f s)).

Lemma shadow_bytes_nil : forall m s f, 0 <= s <= 2^64 -> shadow_bytes m s s f.
Proof. intros m s f H. split; [lia|]. split; [lia|]. intros; lia. Qed.

Lemma shadow_bytes_sub : forall m s1 s2 f s1' s2',
  shadow_bytes m s1 s2 f -> s1 <= s1' -> s2' <= s2 -> shadow_bytes m s1' s2' f.
Proof. intros m s1 s2 f s1' s2' (A & B & H) H1 H2. split; [lia|]. split; [lia|]. intros s Hs. apply H. lia. Qed.

Lemma shadow_bytes_app : forall m s1 s2 s3 f,
  shadow_bytes m s1 s2 f -> shadow_bytes m s2 s3 f -> shadow_bytes m s1 s3 f.
Proof.
  intros m s1 s2 s3 f (A & B & H) (A' & B' & H'). split; [lia|]. split; [lia|].
  intros s Hs. destruct (Z.ltb_spec0 s s2); [apply H | apply H']; lia.
Qed.

Lemma shadow_bytes_ext : forall m s1 s2 f g,
  shadow_bytes m s1 s2 f -> (forall s, s1 <= s < s2 -> Z_to_bv 8 (f s) = Z_to_bv 8 (g s)) -> shadow_bytes m s1 s2 g.
Proof. intros m s1 s2 f g (A & B & H) E. split; [lia|]. split; [lia|]. intros s Hs. rewrite H, E by lia. reflexivity. Qed.

Lemma shadow_bytes_agree : forall m m' s1 s2 f,
  shadow_bytes m s1 s2 f -> (forall s, s1 <= s < s2 -> m' (wa s) = m (wa s)) -> shadow_bytes m' s1 s2 f.
Proof. intros m m' s1 s2 f (A & B & H) E. split; [lia|]. split; [lia|]. intros s Hs. rewrite E by lia. apply H. lia. Qed.

Lemma shadow_bytes_munch : forall W m m' s1 s2 f,
  shadow_bytes m s1 s2 f -> munch W m m' -> disjoint_from W s1 (s2 - s1) -> shadow_bytes m' s1 s2 f.
Proof.
  intros W m m' s1 s2 f SB MU D. pose proof SB as (A & B & _). eapply shadow_bytes_agree; [exact SB|].
  intros s Hs. apply MU. eapply disjoint_outside; [exact D|]. rewrite wa_unsigned by lia. lia.
Qed.

Lemma shadow_bytes_write_other : forall m s1 s2 f a bs,
  shadow_bytes m s1 s2 f -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  (s2 <= a \/ a + Z.of_nat (length bs) <= s1) ->
  shadow_bytes (write_to_mem m (wa a) bs) s1 s2 f.
Proof.
  intros m s1 s2 f a bs SB Ha Hal Hd. pose proof SB as (A & B & _). eapply shadow_bytes_agree; [exact SB|].
  intros s Hs. rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
  destruct (Z.leb_spec0 a s); destruct (Z.ltb_spec0 s (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity. exfalso; lia.
Qed.

Definition no_image (s1 s2 : Z) : Prop := forall z, s1 <= z < s2 -> find_segment segs z 1 = None.

Lemma mrd_no_image : forall m s1 s2 s, no_image s1 s2 -> s1 <= s < s2 -> 0 <= s1 -> s2 <= 2^64 ->
  mrd segs m (wa s) = m (wa s).
Proof.
  intros m s1 s2 s NI Hs A B. unfold mrd. destruct (m (wa s)); [reflexivity|].
  unfold seg_rom, memory_read. rewrite wa_unsigned by lia. change (Z.of_N 1) with 1. rewrite (NI s) by lia. reflexivity.
Qed.

Lemma wview_no_image : forall m s1 s2 s, no_image s1 s2 -> s1 <= s < s2 -> 0 <= s1 -> s2 <= 2^64 ->
  wview segs m (wa s) = m (wa s).
Proof.
  intros m s1 s2 s NI Hs A B. unfold wview. destruct (m (wa s)); [reflexivity|].
  rewrite wa_unsigned by lia. rewrite (NI s) by lia. reflexivity.
Qed.

Lemma shadow_bytes_of_bytes_at : forall m s bs (f : Z -> Z),
  bytes_at segs m s bs -> no_image s (s + Z.of_nat (length bs)) ->
  (forall i, (i < length bs)%nat -> nth_error bs i = Some (Z_to_bv 8 (f (s + Z.of_nat i)))) ->
  shadow_bytes m s (s + Z.of_nat (length bs)) f.
Proof.
  intros m s bs f (A & B & H) NI Hf. split; [lia|]. split; [lia|]. intros s' Hs'.
  specialize (H (Z.to_nat (s' - s)) ltac:(lia)). rewrite Hf in H by lia.
  replace (s + Z.of_nat (Z.to_nat (s' - s))) with s' in H by lia.
  rewrite (mrd_no_image m s (s + Z.of_nat (length bs))) in H by (auto; lia). exact H.
Qed.

Lemma shadow_bytes_of_rw_cells_repeat : forall m s k v,
  rw_cells segs m s [CB (Z.to_nat k) (repeat (Z_to_bv 8 v) (Z.to_nat k))] -> 0 <= k -> no_image s (s + k) ->
  shadow_bytes m s (s + k) (fun _ => v).
Proof.
  intros m s k v [[_ Hb] _] Hk NI. cbn [cells_bytes cbytes app] in Hb. rewrite app_nil_r in Hb.
  pose proof (shadow_bytes_of_bytes_at m s _ (fun _ => v) Hb) as SB. rewrite repeat_length in SB.
  replace (s + Z.of_nat (Z.to_nat k)) with (s + k) in SB by lia.
  apply SB; [exact NI|]. intros i Hi. rewrite nth_error_repeat by lia. reflexivity.
Qed.

Lemma shadow_bytes_of_rw_cells_C1 : forall m s v,
  rw_cells segs m s [C1 (Z_to_bv 8 v)] -> no_image s (s + 1) -> shadow_bytes m s (s + 1) (fun _ => v).
Proof.
  intros m s v [[_ Hb] _] NI. cbn [cells_bytes cbytes app] in Hb.
  pose proof (shadow_bytes_of_bytes_at m s [Z_to_bv 8 v] (fun _ => v) Hb) as SB. cbn [length Z.of_nat Pos.of_succ_nat] in SB.
  apply SB; [exact NI|]. intros [|i] Hi; cbn in Hi |- *; [reflexivity| lia].
Qed.

Definition shadow_list (s : Z) (n : nat) (f : Z -> Z) : list byte :=
  map (fun i => Z_to_bv 8 (f (s + Z.of_nat i))) (seq 0 n).

Lemma shadow_list_length : forall s n f, length (shadow_list s n f) = n.
Proof. intros. unfold shadow_list. rewrite length_map, length_seq. reflexivity. Qed.

Lemma shadow_list_nth : forall s n f i, (i < n)%nat ->
  nth_error (shadow_list s n f) i = Some (Z_to_bv 8 (f (s + Z.of_nat i))).
Proof.
  intros s n f i Hi. unfold shadow_list. rewrite nth_error_map, nth_error_seq. destruct (PeanoNat.Nat.ltb_spec0 i n); [reflexivity| lia].
Qed.

Lemma bytes_at_of_shadow_bytes : forall m s1 s2 f,
  shadow_bytes m s1 s2 f -> s1 <= s2 -> bytes_at segs m s1 (shadow_list s1 (Z.to_nat (s2 - s1)) f).
Proof.
  intros m s1 s2 f (A & B & H) Hle. split; [lia|]. split. { rewrite shadow_list_length. lia. }
  intros i Hi. rewrite shadow_list_length in Hi. rewrite shadow_list_nth by lia.
  unfold mrd. rewrite H by lia. reflexivity.
Qed.

Lemma wr_at_of_shadow_bytes : forall m s1 s2 f,
  shadow_bytes m s1 s2 f -> wr_at segs m s1 (s2 - s1).
Proof.
  intros m s1 s2 f (A & B & H). split; [lia|]. split; [lia|]. intros i Hi.
  unfold wview. rewrite H by lia. discriminate.
Qed.

Lemma u8arr_of_shadow_bytes : forall m s1 s2 f,
  shadow_bytes m s1 s2 f -> s1 <= s2 -> u8arr segs m s1 (shadow_list s1 (Z.to_nat (s2 - s1)) f).
Proof.
  intros m s1 s2 f SB Hle. split. { apply bytes_at_of_shadow_bytes; assumption. }
  rewrite shadow_list_length. replace (Z.of_nat (Z.to_nat (s2 - s1))) with (s2 - s1) by lia.
  eapply wr_at_of_shadow_bytes; eauto.
Qed.

Lemma rw_cells_of_shadow_bytes : forall m s1 s2 f,
  shadow_bytes m s1 s2 f -> s1 <= s2 ->
  rw_cells segs m s1 [CB (Z.to_nat (s2 - s1)) (shadow_list s1 (Z.to_nat (s2 - s1)) f)].
Proof.
  intros m s1 s2 f SB Hle. pose proof (u8arr_of_shadow_bytes m s1 s2 f SB Hle) as U.
  apply rw_cells_of_u8arr in U. rewrite shadow_list_length in U. exact U.
Qed.

Lemma rw_cells_C1_of_shadow_bytes : forall m s1 s2 f s,
  shadow_bytes m s1 s2 f -> s1 <= s < s2 -> rw_cells segs m s [C1 (Z_to_bv 8 (f s))].
Proof.
  intros m s1 s2 f s (A & B & H) Hs. split; [split|].
  - cbn. split; exact I.
  - cbn [cells_bytes cbytes app]. split; [lia|]. split; [cbn; lia|].
    intros [|i] Hi; cbn in Hi; [|lia]. cbn [nth_error]. rewrite Z.add_0_r. unfold mrd. rewrite H by lia. reflexivity.
  - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. replace (s + i) with s by lia.
    unfold wview. rewrite H by lia. discriminate.
Qed.

Lemma rw_cells_C1_of_byte : forall m s b, 0 <= s -> s + 1 <= 2^64 -> m (wa s) = Some b -> rw_cells segs m s [C1 b].
Proof.
  intros m s b A B H. split; [split|].
  - cbn. split; exact I.
  - cbn [cells_bytes cbytes app]. split; [lia|]. split; [cbn; lia|].
    intros [|i] Hi; cbn in Hi; [|lia]. cbn [nth_error]. rewrite Z.add_0_r. unfold mrd. rewrite H. reflexivity.
  - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. replace (s + i) with s by lia.
    unfold wview. rewrite H. discriminate.
Qed.

Lemma wr_at_some : forall m s n i, wr_at segs m s n -> no_image s (s + n) -> 0 <= i < n ->
  exists b, m (wa (s + i)) = Some b.
Proof.
  intros m s n i (A & B & H) NI Hi. specialize (H i Hi).
  rewrite (wview_no_image m s (s + n)) in H by (auto; lia).
  destruct (m (wa (s + i))) as [b|]; [exists b; reflexivity| congruence].
Qed.

Lemma rw_cells_of_wr_at : forall m s n, wr_at segs m s n -> no_image s (s + n) -> 0 <= n ->
  exists bs, length bs = Z.to_nat n /\ rw_cells segs m s [CB (Z.to_nat n) bs].
Proof.
  intros m s n W NI Hn. pose proof W as (A & B & _).
  assert (G : forall k : nat, (Z.of_nat k <= n) -> exists bs, length bs = k /\
            forall i, (i < k)%nat -> mrd segs m (wa (s + Z.of_nat i)) = nth_error bs i).
  { induction k as [|k IH]; intros Hk.
    - exists []. split; [reflexivity|]. intros i Hi; lia.
    - destruct (IH ltac:(lia)) as (bs & Hlen & Hbs).
      destruct (wr_at_some m s n (Z.of_nat k) W NI ltac:(lia)) as [b Hb].
      exists (bs ++ [b]). split. { rewrite length_app; cbn; lia. }
      intros i Hi. destruct (Nat.eqb_spec i k).
      + subst i. rewrite nth_error_app2 by lia. rewrite Hlen, Nat.sub_diag. cbn.
        rewrite (mrd_no_image m s (s + n)) by (auto; lia). exact Hb.
      + rewrite nth_error_app1 by lia. apply Hbs. lia. }
  destruct (G (Z.to_nat n) ltac:(lia)) as (bs & Hlen & Hbs). exists bs. split; [exact Hlen|].
  split; [split|].
  - cbn. rewrite Hlen. split; [reflexivity| exact I].
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. split; [lia|]. split; [rewrite Hlen; lia|].
    intros i Hi. apply Hbs. lia.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. replace (Z.of_nat (Z.to_nat n)) with n by lia. exact W.
Qed.

Lemma Z_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with 256 in Hb.
  pose proof (bytes_le_to_Z_nonneg bs) as HR.
  rewrite lor_shiftl8_add by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8). change (2^8) with 256.
    Z.div_mod_to_equations. nia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    replace ((bv_unsigned b + 256 * bytes_le_to_Z bs) / 256) with (bytes_le_to_Z bs) by (Z.div_mod_to_equations; nia).
    apply IH.
Qed.

Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (bytes_le_to_Z_bound bs) as HR. pose proof (bytes_le_to_Z_nonneg bs) as H0. rewrite HL in HR.
  change (2 ^ (8 * Z.of_nat 8)) with (2^64) in HR.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia). rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.

Lemma rw_cells_C8_of_wr_at : forall m s, wr_at segs m s 8 -> no_image s (s + 8) ->
  exists w : word, rw_cells segs m s [C8 w].
Proof.
  intros m s W NI. destruct (rw_cells_of_wr_at m s 8 W NI ltac:(lia)) as (bs & Hlen & R).
  exists (le_bytes_to_word bs).
  destruct R as [[_ Hb] Hw]. split; [split|].
  - cbn. split; [reflexivity| exact I].
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. cbn [cells_bytes cbytes app] in Hb. rewrite app_nil_r in Hb.
    rewrite le8_of_bytes by exact Hlen. exact Hb.
  - exact Hw.
Qed.

Definition unpoisoned (m : word -> option byte) (lo hi : Z) : Prop :=
  0 <= lo /\ hi <= 2^64 /\
  forall G, lo < hi -> lo <= 8 * G + 7 -> 8 * G < hi ->
    exists b, m (wa (ASHOFF + G)) = Some b /\ gran_ok (Z.min (8 * G + 8) hi - 8 * G) b.

Lemma unpoisoned_sub : forall m lo hi lo' hi',
  unpoisoned m lo hi -> lo <= lo' -> hi' <= hi -> unpoisoned m lo' hi'.
Proof.
  intros m lo hi lo' hi' (A & B & H) H1 H2. split; [lia|]. split; [lia|].
  intros G HG0 HG1 HG2. destruct (H G ltac:(lia) ltac:(lia) ltac:(lia)) as (b & Hb & Hok).
  exists b. split; [exact Hb|]. eapply gran_ok_mono; [exact Hok|]. lia.
Qed.

Lemma unpoisoned_nil : forall m lo, 0 <= lo <= 2^64 -> unpoisoned m lo lo.
Proof. intros m lo A. split; [lia|]. split; [lia|]. intros G H0 H1 H2. lia. Qed.

Lemma unpoisoned_agree : forall m m' lo hi,
  unpoisoned m lo hi -> (forall s, shad lo <= s <= shad (hi - 1) -> m' (wa s) = m (wa s)) -> unpoisoned m' lo hi.
Proof.
  intros m m' lo hi (A & B & H) E. split; [lia|]. split; [lia|]. intros G H0 H1 H2.
  destruct (H G H0 H1 H2) as (b & Hb & Hok). exists b. split; [|exact Hok].
  rewrite E; [exact Hb|]. rewrite !shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia.
Qed.

Lemma unpoisoned_munch : forall W m m' lo hi,
  unpoisoned m lo hi -> munch W m m' -> disjoint_from W (shad lo) (shad (hi - 1) + 1 - shad lo) -> unpoisoned m' lo hi.
Proof.
  intros W m m' lo hi U MU D. pose proof U as (A & B & _). eapply unpoisoned_agree; [exact U|].
  intros s Hs. apply MU. eapply disjoint_outside; [exact D|].
  rewrite !shad_div in *. unfold ASHOFF in *.
  rewrite wa_unsigned by (Z.div_mod_to_equations; lia). lia.
Qed.

Lemma unpoisoned_write_other : forall m lo hi a bs,
  unpoisoned m lo hi -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  (shad (hi - 1) + 1 <= a \/ a + Z.of_nat (length bs) <= shad lo) ->
  unpoisoned (write_to_mem m (wa a) bs) lo hi.
Proof.
  intros m lo hi a bs U Ha Hal Hd. pose proof U as (A & B & _). eapply unpoisoned_agree; [exact U|].
  intros s Hs. rewrite !shad_div in *. unfold ASHOFF in *.
  rewrite write_to_mem_spec by lia. rewrite wa_unsigned by (Z.div_mod_to_equations; lia).
  destruct (Z.leb_spec0 a s); destruct (Z.ltb_spec0 s (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity. exfalso; lia.
Qed.

Lemma granule_of : forall a, 0 <= a -> 8 * (a / 8) <= a < 8 * (a / 8) + 8 /\ a mod 8 = a - 8 * (a / 8).
Proof. intros a Ha. Z.div_mod_to_equations. lia. Qed.

Lemma unpoisoned_byte : forall m lo hi a,
  unpoisoned m lo hi -> lo <= a < hi ->
  exists b, m (wa (shad a)) = Some b /\ gran_ok (Z.min (8 * (a / 8) + 8) hi - 8 * (a / 8)) b.
Proof.
  intros m lo hi a (A & B & H) Ha. rewrite shad_div.
  apply (H (a / 8)); Z.div_mod_to_equations; lia.
Qed.

Lemma unpoisoned_check : forall m lo hi a N,
  unpoisoned m lo hi -> lo <= a -> a + N <= hi -> 1 <= N -> a mod 8 + N <= 8 ->
  exists b, rw_cells segs m (shad a) [C1 b] /\ (sval b = 0 \/ (0 < sval b <= 7 /\ a mod 8 + N - 1 < sval b)).
Proof.
  intros m lo hi a N U H1 H2 H3 H4. pose proof U as (A & B & _).
  destruct (unpoisoned_byte m lo hi a U ltac:(lia)) as (b & Hb & Hok).
  exists b. split.
  - apply rw_cells_C1_of_byte; [| |exact Hb]; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia.
  - destruct Hok as [Z0|Hk]; [left; exact Z0| right]. Z.div_mod_to_equations. lia.
Qed.

Lemma unpoisoned_full : forall m lo hi G,
  unpoisoned m lo hi -> lo <= 8 * G + 7 -> 8 * G + 8 <= hi -> m (wa (ASHOFF + G)) = Some (Z_to_bv 8 0).
Proof.
  intros m lo hi G (A & B & H) H1 H2. destruct (H G ltac:(lia) ltac:(lia) ltac:(lia)) as (b & Hb & Hok).
  rewrite Hb. f_equal. eapply gran_ok_full; [exact Hok|]. lia.
Qed.

Lemma unpoisoned_core_zero : forall m lo hi lo' hi',
  unpoisoned m lo hi -> lo <= lo' -> hi' <= hi -> lo' mod 8 = 0 -> hi' mod 8 = 0 -> lo' <= hi' ->
  shadow_bytes m (shad lo') (shad hi') (fun _ => 0).
Proof.
  intros m lo hi lo' hi' U H1 H2 A1 A2 LE. pose proof U as (A & B & _).
  rewrite !shad_div. split. { unfold ASHOFF; Z.div_mod_to_equations; lia. } split. { unfold ASHOFF; Z.div_mod_to_equations; lia. }
  intros s Hs. replace s with (ASHOFF + (s - ASHOFF)) at 1 by lia.
  apply (unpoisoned_full m lo hi (s - ASHOFF) U); Z.div_mod_to_equations; lia.
Qed.

Lemma rw_cells_C8_zero : forall m s f,
  shadow_bytes m s (s + 8) f -> (forall s', s <= s' < s + 8 -> Z_to_bv 8 (f s') = Z_to_bv 8 0) ->
  rw_cells segs m s [C8 (Z_to_bv 64 0)].
Proof.
  intros m s f SB E. pose proof (shadow_bytes_ext m s (s + 8) f (fun _ => 0) SB E) as SB0.
  pose proof (rw_cells_of_shadow_bytes m s (s + 8) (fun _ => 0) SB0 ltac:(lia)) as R.
  replace (s + 8 - s) with 8 in R by lia.
  destruct R as [[_ Hb] Hw]. split; [split; [cbn; split; exact I|]|].
  - change (cells_bytes [C8 (Z_to_bv 64 0)]) with (cells_bytes [CB (Z.to_nat 8) (shadow_list s (Z.to_nat 8) (fun _ => 0))]). exact Hb.
  - exact Hw.
Qed.

Definition shadow_block (m : word -> option byte) (p n : Z) : Prop :=
  p mod 8 = 0 /\ 0 <= p /\ 0 <= n /\ p + n <= 2^64 /\ shadow_bytes m (shad p) (shad p + nshad n) (blockf p n).

Lemma shadow_block_unpoisoned : forall m p n, shadow_block m p n -> unpoisoned m p (p + n).
Proof.
  intros m p n (AL & P0 & N0 & PN & (A & B & H)). split; [lia|]. split; [lia|].
  intros G H0 H1 H2. rewrite nshad_div, shad_div in *.
  assert (R : ASHOFF + p / 8 <= ASHOFF + G < ASHOFF + p / 8 + (n + 7) / 8) by (Z.div_mod_to_equations; lia).
  exists (Z_to_bv 8 (blockf p n (ASHOFF + G))). split. { apply H. exact R. }
  unfold blockf. rewrite shad_div. cbn zeta.
  replace (ASHOFF + G - (ASHOFF + p / 8)) with (G - p / 8) by lia.
  destruct (Z.leb_spec0 (8 * (G - p / 8) + 8) n).
  - left. apply sval_zero.
  - right. rewrite sval_lit by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia.
Qed.

Lemma shadow_block_frame : forall m m' p n,
  shadow_block m p n -> (forall s, shad p <= s < shad p + nshad n -> m' (wa s) = m (wa s)) -> shadow_block m' p n.
Proof.
  intros m m' p n (AL & P0 & N0 & PN & SB) E. repeat (split; [assumption|]).
  eapply shadow_bytes_agree; eauto.
Qed.

Lemma shadow_block_munch : forall W m m' p n,
  shadow_block m p n -> munch W m m' -> disjoint_from W (shad p) (nshad n) -> shadow_block m' p n.
Proof.
  intros W m m' p n (AL & P0 & N0 & PN & SB) MU D. repeat (split; [assumption|]).
  eapply shadow_bytes_munch; eauto. replace (shad p + nshad n - shad p) with (nshad n) by lia. exact D.
Qed.

Lemma shadow_block_intro_full : forall m p n f,
  p mod 8 = 0 -> 0 <= p -> 0 <= n -> p + n <= 2^64 -> n mod 8 = 0 ->
  shadow_bytes m (shad p) (shad p + n / 8) f -> (forall s, shad p <= s < shad p + n / 8 -> (f s) mod 256 = 0) ->
  shadow_block m p n.
Proof.
  intros m p n f AL P0 N0 PN N8 SB Z0. repeat (split; [assumption|]).
  assert (E : nshad n = n / 8) by (rewrite nshad_div; Z.div_mod_to_equations; lia). rewrite E.
  eapply shadow_bytes_ext; [exact SB|]. intros s Hs. unfold blockf. cbn zeta.
  destruct (Z.leb_spec0 (8 * (s - shad p) + 8) n); [| exfalso; Z.div_mod_to_equations; lia].
  apply bv_eq. rewrite !Z_to_bv_unsigned. change (bv_wrap 8 ?x) with (x mod 256). rewrite Z0 by lia. reflexivity.
Qed.

Lemma shadow_block_intro_partial : forall m p n f k,
  p mod 8 = 0 -> 0 <= p -> 0 <= n -> p + n <= 2^64 -> n mod 8 <> 0 -> k = n mod 8 ->
  shadow_bytes m (shad p) (shad p + n / 8) f -> (forall s, shad p <= s < shad p + n / 8 -> (f s) mod 256 = 0) ->
  m (wa (shad p + n / 8)) = Some (Z_to_bv 8 k) ->
  shadow_block m p n.
Proof.
  intros m p n f k AL P0 N0 PN N8 K SB Z0 LAST. repeat (split; [assumption|]).
  assert (E : nshad n = n / 8 + 1) by (rewrite nshad_div; Z.div_mod_to_equations; lia). rewrite E.
  pose proof SB as (A & B & _).
  apply (shadow_bytes_app m (shad p) (shad p + n / 8)).
  - eapply shadow_bytes_ext; [exact SB|]. intros s Hs. unfold blockf. cbn zeta.
    destruct (Z.leb_spec0 (8 * (s - shad p) + 8) n); [| exfalso; Z.div_mod_to_equations; lia].
    apply bv_eq. rewrite !Z_to_bv_unsigned. change (bv_wrap 8 ?x) with (x mod 256). rewrite Z0 by lia. reflexivity.
  - split; [lia|]. split. { rewrite shad_div in *. unfold ASHOFF in *. Z.div_mod_to_equations; lia. }
    intros s Hs. assert (s = shad p + n / 8) by lia. subst s. rewrite LAST. f_equal. unfold blockf. cbn zeta.
    replace (shad p + n / 8 - shad p) with (n / 8) by lia.
    destruct (Z.leb_spec0 (8 * (n / 8) + 8) n); [exfalso; Z.div_mod_to_equations; lia|].
    f_equal. Z.div_mod_to_equations; lia.
Qed.

Lemma shadow_block_of_memset0 : forall m p n,
  p mod 8 = 0 -> 0 <= p -> 0 <= n -> p + n <= 2^64 -> n mod 8 = 0 -> no_image (shad p) (shad p + n / 8) ->
  rw_cells segs m (shad p) [CB (Z.to_nat (n / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (n / 8)))] ->
  shadow_block m p n.
Proof.
  intros m p n AL P0 N0 PN N8 NI R.
  apply (shadow_block_intro_full m p n (fun _ => 0)); try assumption.
  - apply shadow_bytes_of_rw_cells_repeat; [exact R | Z.div_mod_to_equations; lia | exact NI].
  - intros; reflexivity.
Qed.

Lemma shadow_block_of_memset0_partial : forall m p n k,
  p mod 8 = 0 -> 0 <= p -> 0 <= n -> p + n <= 2^64 -> n mod 8 <> 0 -> k = n mod 8 ->
  no_image (shad p) (shad p + n / 8 + 1) ->
  rw_cells segs m (shad p) [CB (Z.to_nat (n / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (n / 8))); C1 (Z_to_bv 8 k)] ->
  shadow_block m p n.
Proof.
  intros m p n k AL P0 N0 PN N8 K NI R.
  pose proof R as [[Hwf Hb] Hw]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  destruct Hb as (A & B & H). rewrite length_app, repeat_length in B, H. cbn [length] in B, H.
  assert (SHP : 0 <= shad p) by lia.
  apply (shadow_block_intro_partial m p n (fun _ => 0) k); try assumption.
  - split; [lia|]. split; [lia|]. intros s Hs.
    specialize (H (Z.to_nat (s - shad p)) ltac:(lia)).
    rewrite nth_error_app1, nth_error_repeat in H by (rewrite ?repeat_length; lia).
    replace (shad p + Z.of_nat (Z.to_nat (s - shad p))) with s in H by lia.
    rewrite (mrd_no_image m (shad p) (shad p + n / 8 + 1)) in H by (auto; lia). exact H.
  - intros; reflexivity.
  - specialize (H (Z.to_nat (n / 8)) ltac:(lia)).
    rewrite nth_error_app2 in H by (rewrite repeat_length; lia). rewrite repeat_length, Nat.sub_diag in H. cbn [nth_error] in H.
    replace (Z.of_nat (Z.to_nat (n / 8))) with (n / 8) in H by (Z.div_mod_to_equations; lia).
    rewrite (mrd_no_image m (shad p) (shad p + n / 8 + 1)) in H by (auto; Z.div_mod_to_equations; lia). exact H.
Qed.

Lemma ov_read_of_bytes_at : forall m a bs,
  bytes_at segs m a bs -> ov_read_bytes segs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_ov_read segs m a bs 0 (length bs) H ltac:(lia)) as R.
  rewrite Z.add_0_r in R. cbn [skipn] in R. rewrite firstn_all in R. exact R.
Qed.

Lemma ov_read1_of_byte : forall m s b, 0 <= s -> s + 1 <= 2^64 -> m (wa s) = Some b ->
  ov_read_bytes segs m (wa s) 1 = Some [b].
Proof.
  intros m s b A B H. apply (ov_read_of_bytes_at m s [b]). split; [lia|]. split; [cbn; lia|].
  intros [|i] Hi; cbn in Hi; [|lia]. cbn [nth_error]. rewrite Z.add_0_r. unfold mrd. rewrite H. reflexivity.
Qed.

Lemma ov_read1_of_shadow_bytes : forall m s1 s2 f s,
  shadow_bytes m s1 s2 f -> s1 <= s < s2 -> ov_read_bytes segs m (wa s) 1 = Some [Z_to_bv 8 (f s)].
Proof. intros m s1 s2 f s (A & B & H) Hs. apply ov_read1_of_byte; [lia|lia|]. apply H. lia. Qed.

Lemma ov_read8_of_shadow_bytes : forall m s1 s2 f s,
  shadow_bytes m s1 s2 f -> s1 <= s -> s + 8 <= s2 -> ov_read_bytes segs m (wa s) 8 = Some (shadow_list s 8 f).
Proof.
  intros m s1 s2 f s SB H1 H2.
  pose proof (bytes_at_of_shadow_bytes m s (s + 8) f (shadow_bytes_sub m s1 s2 f s (s + 8) SB H1 H2) ltac:(lia)) as BA.
  replace (s + 8 - s) with 8 in BA by lia.
  rewrite <- (shadow_list_length s 8 f) at 1. apply ov_read_of_bytes_at. exact BA.
Qed.

Lemma ov_read8_zero : forall m s1 s2 f s,
  shadow_bytes m s1 s2 f -> s1 <= s -> s + 8 <= s2 -> (forall s', s <= s' < s + 8 -> Z_to_bv 8 (f s') = Z_to_bv 8 0) ->
  ov_read_bytes segs m (wa s) 8 = Some (le8 (Z_to_bv 64 0)).
Proof.
  intros m s1 s2 f s SB H1 H2 E.
  pose proof (shadow_bytes_ext m s (s + 8) f (fun _ => 0) (shadow_bytes_sub m s1 s2 f s (s + 8) SB H1 H2) E) as SB0.
  rewrite (ov_read8_of_shadow_bytes m s (s + 8) (fun _ => 0) s SB0) by lia.
  reflexivity.
Qed.

Lemma ov_read1_of_wr_at : forall m s n i, wr_at segs m s n -> no_image s (s + n) -> 0 <= i < n ->
  exists b, ov_read_bytes segs m (wa (s + i)) 1 = Some [b].
Proof.
  intros m s n i W NI Hi. pose proof W as (A & B & _). destruct (wr_at_some m s n i W NI Hi) as [b Hb].
  exists b. apply ov_read1_of_byte; [lia|lia|exact Hb].
Qed.

Lemma ov_read8_of_wr_at : forall m s, wr_at segs m s 8 -> no_image s (s + 8) ->
  exists w : word, ov_read_bytes segs m (wa s) 8 = Some (le8 w).
Proof.
  intros m s W NI. destruct (rw_cells_C8_of_wr_at m s W NI) as [w R]. exists w.
  pose proof (rw_cells_read segs m s [C8 w] 0 (C8 w) R eq_refl) as RD. rewrite Z.add_0_r in RD. exact RD.
Qed.

Lemma unpoisoned_full_rd : forall m lo hi c,
  unpoisoned m lo hi -> shad lo <= c -> 8 * (c - ASHOFF) + 8 <= hi ->
  ov_read_bytes segs m (wa c) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m lo hi c U H1 H2. pose proof U as (A & B & _). rewrite shad_div in H1.
  apply ov_read1_of_byte; [unfold ASHOFF in *; Z.div_mod_to_equations; lia | unfold ASHOFF in *; Z.div_mod_to_equations; lia |].
  replace c with (ASHOFF + (c - ASHOFF)) at 1 by lia.
  apply (unpoisoned_full m lo hi (c - ASHOFF) U); Z.div_mod_to_equations; lia.
Qed.

Lemma unpoisoned_check_rd : forall m lo hi a N,
  unpoisoned m lo hi -> lo <= a -> a + N <= hi -> 1 <= N -> a mod 8 + N <= 8 ->
  exists b, ov_read_bytes segs m (wa (shad a)) 1 = Some [b] /\ (sval b = 0 \/ (0 < sval b <= 7 /\ a mod 8 + N - 1 < sval b)).
Proof.
  intros m lo hi a N U H1 H2 H3 H4. destruct (unpoisoned_check m lo hi a N U H1 H2 H3 H4) as (b & R & Hb).
  exists b. split; [|exact Hb].
  pose proof (rw_cells_read segs m (shad a) [C1 b] 0 (C1 b) R eq_refl) as RD. rewrite Z.add_0_r in RD. exact RD.
Qed.

Lemma wr_at_sub : forall m a n a' n', wr_at segs m a n -> a <= a' -> a' + n' <= a + n -> wr_at segs m a' n'.
Proof. intros m a n a' n' (A & B & H) H1 H2. split; [lia|]. split; [lia|]. intros i Hi. replace (a' + i) with (a + (a' + i - a)) by lia. apply H. lia. Qed.

Lemma shadow_probe8 : forall m RLO RHI x,
  wr_at segs m (shad RLO) (shad RHI - shad RLO) -> no_image (shad RLO) (shad RHI) ->
  RLO mod 64 = 0 -> RHI mod 64 = 0 -> 0 <= RLO -> RLO <= x < RHI -> RHI <= 2^64 ->
  exists w : word, ov_read_bytes segs m (wa (ASHOFF + Z.shiftr x 3 - (ASHOFF + Z.shiftr x 3) mod 8)) 8 = Some (le8 w).
Proof.
  intros m RLO RHI x W NI A1 A2 A0 Hx HR.
  rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite !shad_div in W, NI. unfold ASHOFF in *.
  set (P := 2147450880 + x / 8 - (2147450880 + x / 8) mod 8).
  assert (HP : 2147450880 + RLO / 8 <= P /\ P + 8 <= 2147450880 + RHI / 8) by (subst P; Z.div_mod_to_equations; lia).
  apply ov_read8_of_wr_at.
  - eapply wr_at_sub; [exact W| lia | lia].
  - intros z Hz. apply NI. lia.
Qed.

Lemma shadow_probe1 : forall m RLO RHI x,
  wr_at segs m (shad RLO) (shad RHI - shad RLO) -> no_image (shad RLO) (shad RHI) ->
  0 <= RLO -> RLO <= x < RHI -> RHI <= 2^64 -> RHI mod 64 = 0 ->
  exists b : byte, ov_read_bytes segs m (wa (ASHOFF + Z.shiftr x 3)) 1 = Some [b].
Proof.
  intros m RLO RHI x W NI A0 Hx HR A2.
  rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite !shad_div in W, NI. unfold ASHOFF in *.
  destruct (ov_read1_of_wr_at m (2147450880 + RLO / 8) (2147450880 + RHI / 8 - (2147450880 + RLO / 8)) (x / 8 - RLO / 8) W) as [b Hb].
  - intros z Hz. apply NI. lia.
  - Z.div_mod_to_equations; lia.
  - exists b. replace (2147450880 + x / 8) with (2147450880 + RLO / 8 + (x / 8 - RLO / 8)) by lia. exact Hb.
Qed.

Lemma shadow_bytes_of_pointwise : forall m a n c,
  (forall i, 0 <= i < n -> m (wa (a + i)) = Some (Z_to_bv 8 c)) -> 0 <= a -> a + n <= 2^64 ->
  shadow_bytes m a (a + n) (fun _ => c).
Proof.
  intros m a n c H A B. split; [lia|]. split; [lia|]. intros s Hs.
  replace s with (a + (s - a)) by lia. apply H. lia.
Qed.

Lemma unpoisoned_of_zero : forall m s1 s2 f lo hi,
  shadow_bytes m s1 s2 f -> (forall s, s1 <= s < s2 -> Z_to_bv 8 (f s) = Z_to_bv 8 0) ->
  s1 <= shad lo -> shad (hi - 1) + 1 <= s2 -> 0 <= lo -> hi <= 2^64 ->
  unpoisoned m lo hi.
Proof.
  intros m s1 s2 f lo hi (A & B & H) Z0 H1 H2 L0 Hh. split; [lia|]. split; [lia|].
  intros G G0 G1 G2. rewrite !shad_div in *. unfold ASHOFF in *.
  assert (R : s1 <= 2147450880 + G < s2) by (Z.div_mod_to_equations; lia).
  exists (Z_to_bv 8 0). split. { rewrite <- (Z0 (2147450880 + G)) by lia. apply H. lia. }
  left. apply sval_zero.
Qed.

End WithSegs.
