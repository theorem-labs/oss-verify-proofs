(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes FP.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Notation mem := (word -> option byte).

Lemma u64s_of_bytes : forall (n : nat) (bs : list byte), length bs = (8 * n)%nat -> exists ws, length ws = n /\ u64s ws = bs.
Proof.
  induction n as [|n IH]; intros bs L.
  - exists []. destruct bs; [split; reflexivity| cbn in L; lia].
  - destruct (IH (skipn 8 bs)) as (ws & LW & EW). { rewrite length_skipn. lia. }
    exists (le_bytes_to_word (firstn 8 bs) :: ws). split; [cbn; lia|].
    cbn [u64s]. rewrite le8_le_bytes_to_word by (rewrite length_firstn; lia). rewrite EW. apply firstn_skipn.
Qed.

Lemma u64arr_of_rw_cells : forall segs (m : mem) A (n : nat) bs,
  rw_cells segs m A [CB (8 * n) bs] -> exists ws, length ws = n /\ u64arr segs m A ws.
Proof.
  intros segs m A n bs H. pose proof (u8arr_of_rw_cells segs m A _ bs H) as [HB HW].
  destruct H as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [HL _].
  destruct (u64s_of_bytes n bs HL) as (ws & LW & EW). exists ws. split; [exact LW|].
  split; [rewrite EW; exact HB|]. rewrite HL in HW. rewrite LW. replace (8 * Z.of_nat n)%Z with (Z.of_nat (8 * n)) by lia. exact HW.
Qed.

Lemma rw_cells_of_u64arr : forall segs (m : mem) A ws,
  u64arr segs m A ws -> rw_cells segs m A [CB (8 * length ws) (u64s ws)].
Proof.
  intros segs m A ws [HB HW]. rewrite <- u64s_length. apply rw_cells_of_u8arr. split; [exact HB|].
  rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws))%Z by lia. exact HW.
Qed.

Lemma num_rw_cells_app : forall segs (m : mem) A cs1 cs2,
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

Lemma num_cb8_c8 : forall segs (m : mem) A pre post bs,
  rw_cells segs m A (pre ++ CB 8 bs :: post) -> rw_cells segs m A (pre ++ C8 (le_bytes_to_word bs) :: post).
Proof.
  intros segs m A pre post bs [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn in H2.
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. split; [exact I | exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb |- *. rewrite le8_le_bytes_to_word by exact H2. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in Hw |- *. exact Hw.
Qed.

Lemma num_cb2_c2 : forall segs (m : mem) A (v : word), rw_cells segs m A [CB 2 (le2 v)] -> rw_cells segs m A [C2 v].
Proof.
  intros segs m A v [[Hwf Hb] Hw]. split; [split|].
  - cbn. split; exact I.
  - exact Hb.
  - exact Hw.
Qed.

Lemma wr_at_split : forall segs (m : mem) A n k, wr_at segs m A n -> (0 <= k <= n)%Z ->
  wr_at segs m A k /\ wr_at segs m (A + k) (n - k).
Proof.
  intros segs m A n k (H0 & H1 & H) Hk. split; (split; [lia|]; split; [lia|]); intros i Hi.
  - apply H. lia.
  - replace (A + k + i)%Z with (A + (k + i))%Z by lia. apply H. lia.
Qed.
Lemma wr_at_join : forall segs (m : mem) A k n2, wr_at segs m A k -> wr_at segs m (A + k) n2 -> (0 <= k)%Z -> (0 <= n2)%Z ->
  wr_at segs m A (k + n2).
Proof.
  intros segs m A k n2 (H0 & H1 & H) (G0 & G1 & G) Hk Hn. split; [lia|]. split; [lia|]. intros i Hi.
  destruct (Z_lt_dec i k); [apply H; lia|]. replace (A + i)%Z with (A + k + (i - k))%Z by lia. apply G. lia.
Qed.

Lemma u64arr_range_split : forall segs (m : mem) A ws (a b : nat),
  u64arr segs m A ws -> (a <= b)%nat -> (b <= length ws)%nat ->
  exists w1 mid w3, length w1 = a /\ length mid = (8 * (b - a))%nat /\ length w3 = (length ws - b)%nat /\
    u64arr segs m A w1 /\ rw_cells segs m (A + 8 * Z.of_nat a) [CB (8 * (b - a)) mid] /\ u64arr segs m (A + 8 * Z.of_nat b) w3.
Proof.
  intros segs m A ws a b [HB HW] Hab Hb.
  set (w1 := firstn a ws). set (w2 := firstn (b - a) (skipn a ws)). set (w3 := skipn b ws).
  assert (E : ws = w1 ++ w2 ++ w3).
  { unfold w1, w2, w3. rewrite <- (firstn_skipn a ws) at 1. f_equal.
    rewrite <- (firstn_skipn (b - a) (skipn a ws)) at 1. f_equal. rewrite skipn_skipn. f_equal. lia. }
  assert (L1 : length w1 = a) by (unfold w1; rewrite length_firstn; lia).
  assert (L2 : length w2 = (b - a)%nat) by (unfold w2; rewrite length_firstn, length_skipn; lia).
  assert (L3 : length w3 = (length ws - b)%nat) by (unfold w3; rewrite length_skipn; lia).
  exists w1, (u64s w2), w3. rewrite u64s_length, L2. repeat (split; [first [exact L1 | exact L3 | reflexivity]|]).
  rewrite E, !u64s_app in HB. apply bytes_at_app in HB. destruct HB as [B1 B23]. apply bytes_at_app in B23. destruct B23 as [B2 B3].
  rewrite !u64s_length, ?L1, ?L2 in *.
  destruct (wr_at_split segs m A _ (8 * Z.of_nat a) HW ltac:(lia)) as [W1 W23].
  destruct (wr_at_split segs m _ _ (8 * Z.of_nat (b - a)) W23 ltac:(lia)) as [W2 W3].
  replace (A + Z.of_nat (8 * a))%Z with (A + 8 * Z.of_nat a)%Z in * by lia.
  replace (A + 8 * Z.of_nat a + Z.of_nat (8 * (b - a)))%Z with (A + 8 * Z.of_nat b)%Z in * by lia.
  replace (A + 8 * Z.of_nat a + 8 * Z.of_nat (b - a))%Z with (A + 8 * Z.of_nat b)%Z in * by lia.
  split; [split; [exact B1| rewrite L1; exact W1]|]. split.
  - split; [split; [cbn; rewrite u64s_length, L2; split; [reflexivity|exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact B2]|].
    cbn [cells_size csize]. rewrite Nat.add_0_r. replace (Z.of_nat (8 * (b - a))) with (8 * Z.of_nat (b - a))%Z by lia. exact W2.
  - split; [exact B3|]. rewrite L3. replace (8 * Z.of_nat (length ws - b))%Z with (8 * Z.of_nat (length ws) - 8 * Z.of_nat a - 8 * Z.of_nat (b - a))%Z by lia. exact W3.
Qed.

Lemma u64arr_range_join : forall segs (m : mem) A w1 (k : nat) bs w3,
  u64arr segs m A w1 -> rw_cells segs m (A + 8 * Z.of_nat (length w1)) [CB (8 * k) bs] ->
  u64arr segs m (A + 8 * Z.of_nat (length w1) + 8 * Z.of_nat k) w3 ->
  exists ws, length ws = (length w1 + k + length w3)%nat /\ u64arr segs m A ws.
Proof.
  intros segs m A w1 k bs w3 [B1 W1] H2 [B3 W3].
  destruct (u64arr_of_rw_cells segs m _ k bs H2) as (w2 & L2 & [B2 W2]).
  exists (w1 ++ w2 ++ w3). split; [rewrite !length_app; lia|]. split.
  - rewrite !u64s_app. apply bytes_at_app. split; [exact B1|]. rewrite u64s_length.
    replace (A + Z.of_nat (8 * length w1))%Z with (A + 8 * Z.of_nat (length w1))%Z by lia.
    apply bytes_at_app. split; [exact B2|]. rewrite u64s_length, L2.
    replace (A + 8 * Z.of_nat (length w1) + Z.of_nat (8 * k))%Z with (A + 8 * Z.of_nat (length w1) + 8 * Z.of_nat k)%Z by lia. exact B3.
  - rewrite !length_app, L2.
    replace (8 * Z.of_nat (length w1 + (k + length w3)))%Z with (8 * Z.of_nat (length w1) + (8 * Z.of_nat k + 8 * Z.of_nat (length w3)))%Z by lia.
    apply wr_at_join; [exact W1| | lia | lia]. rewrite L2 in W2. apply wr_at_join; [exact W2| exact W3 | lia | lia].
Qed.

Lemma u64arr_prefix_bytes : forall segs (m : mem) A ws (k : nat),
  u64arr segs m A ws -> (k <= length ws)%nat -> bytes_at segs m A (u64s (firstn k ws)).
Proof.
  intros segs m A ws k [HB _] Hk. rewrite <- (firstn_skipn k ws), u64s_app in HB. apply bytes_at_app in HB. tauto.
Qed.

Lemma image_readable : forall segs (m : mem) n A bs0,
  image_bytes segs A n = Some bs0 -> (0 <= A)%Z -> (A + Z.of_nat n <= 2^64)%Z ->
  exists bs, length bs = n /\ bytes_at segs m A bs.
Proof.
  intros segs m n. induction n as [|n IH]; intros A bs0 H HA HB.
  - exists []. split; [reflexivity|]. apply bytes_at_nil. lia.
  - cbn [image_bytes] in H. destruct (seg_rom segs (wa A)) as [b|] eqn:E; [|discriminate].
    destruct (image_bytes segs (A + 1) n) as [bs1|] eqn:E2; [|discriminate].
    destruct (IH (A + 1)%Z bs1 E2 ltac:(lia) ltac:(lia)) as (bs & L & BA).
    assert (exists b', mrd segs m (wa A) = Some b') as [b' Hb'].
    { unfold mrd. destruct (m (wa A)); [eexists; reflexivity| exists b; exact E]. }
    exists (b' :: bs). split; [cbn; congruence|].
    destruct BA as (B1 & B2 & B3). split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i]; cbn [nth_error].
    + rewrite Z.add_0_r. exact Hb'.
    + replace (A + Z.of_nat (S i))%Z with (A + 1 + Z.of_nat i)%Z by lia. apply B3. cbn [length] in Hi. lia.
Qed.

Lemma bytes_u64_read : forall segs (m : mem) A bs k,
  bytes_at segs m A bs -> (0 <= k)%Z -> (k + 8 <= Z.of_nat (length bs))%Z ->
  exists w, ov_read_bytes segs m (wa (A + k)) 8 = Some (le8 w).
Proof.
  intros segs m A bs k H Hk Hl.
  exists (le_bytes_to_word (firstn 8 (skipn (Z.to_nat k) bs))).
  rewrite le8_le_bytes_to_word by (rewrite length_firstn, length_skipn; lia).
  apply bytes_at_read; [exact H | lia | lia].
Qed.

Fixpoint image_covered_b (segs : list Segment) (A : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => match seg_rom segs (wa A) with Some _ => image_covered_b segs (A + 1) n' | None => false end
  end.
Lemma image_covered_bytes : forall segs n A, image_covered_b segs A n = true -> exists bs, image_bytes segs A n = Some bs.
Proof.
  intros segs n. induction n as [|n IH]; intros A H; cbn [image_covered_b image_bytes] in *; [eexists; reflexivity|].
  destruct (seg_rom segs (wa A)); [|discriminate]. destruct (IH _ H) as [bs ->]. eexists; reflexivity.
Qed.
Lemma image_readable_b : forall segs (m : mem) n A,
  image_covered_b segs A n = true -> (0 <= A)%Z -> (A + Z.of_nat n <= 2^64)%Z ->
  exists bs, length bs = n /\ bytes_at segs m A bs.
Proof. intros segs m n A H HA HB. destruct (image_covered_bytes segs n A H) as [bs0 E]. eapply image_readable; eassumption. Qed.

Lemma bytes_at_sub : forall segs (m : mem) A bs (k n : nat),
  bytes_at segs m A bs -> (k + n <= length bs)%nat -> bytes_at segs m (A + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros segs m A bs k n H Hk.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length bs)) with k in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply bytes_at_app in H. tauto.
Qed.

Lemma u8arr_range_split : forall segs (m : mem) A bs (a b : nat),
  u8arr segs m A bs -> (a <= b)%nat -> (b <= length bs)%nat ->
  exists b1 mid b3, length b1 = a /\ length mid = (b - a)%nat /\ length b3 = (length bs - b)%nat /\
    u8arr segs m A b1 /\ rw_cells segs m (A + Z.of_nat a) [CB (b - a) mid] /\ u8arr segs m (A + Z.of_nat b) b3.
Proof.
  intros segs m A bs a b [HB HW] Hab Hb.
  set (b1 := firstn a bs). set (b2 := firstn (b - a) (skipn a bs)). set (b3 := skipn b bs).
  assert (E : bs = b1 ++ b2 ++ b3).
  { unfold b1, b2, b3. rewrite <- (firstn_skipn a bs) at 1. f_equal.
    rewrite <- (firstn_skipn (b - a) (skipn a bs)) at 1. f_equal. rewrite skipn_skipn. f_equal. lia. }
  assert (L1 : length b1 = a) by (unfold b1; rewrite length_firstn; lia).
  assert (L2 : length b2 = (b - a)%nat) by (unfold b2; rewrite length_firstn, length_skipn; lia).
  assert (L3 : length b3 = (length bs - b)%nat) by (unfold b3; rewrite length_skipn; lia).
  exists b1, b2, b3. repeat (split; [first [exact L1 | exact L2 | exact L3]|]).
  rewrite E in HB. apply bytes_at_app in HB. destruct HB as [B1 B23]. apply bytes_at_app in B23. destruct B23 as [B2 B3].
  rewrite ?L1, ?L2 in *.
  destruct (wr_at_split segs m A _ (Z.of_nat a) HW ltac:(lia)) as [W1 W23].
  destruct (wr_at_split segs m _ _ (Z.of_nat (b - a)) W23 ltac:(lia)) as [W2 W3].
  replace (A + Z.of_nat a + Z.of_nat (b - a))%Z with (A + Z.of_nat b)%Z in * by lia.
  split; [split; [exact B1| rewrite L1; exact W1]|]. split.
  - split; [split; [cbn; rewrite L2; split; [reflexivity|exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact B2]|].
    cbn [cells_size csize]. rewrite Nat.add_0_r. exact W2.
  - split; [exact B3|]. rewrite L3. replace (Z.of_nat (length bs - b)) with (Z.of_nat (length bs) - Z.of_nat a - Z.of_nat (b - a))%Z by lia. exact W3.
Qed.

Lemma u8arr_range_join : forall segs (m : mem) A b1 (k : nat) mid b3,
  u8arr segs m A b1 -> rw_cells segs m (A + Z.of_nat (length b1)) [CB k mid] ->
  u8arr segs m (A + Z.of_nat (length b1) + Z.of_nat k) b3 ->
  exists bs, length bs = (length b1 + k + length b3)%nat /\ u8arr segs m A bs.
Proof.
  intros segs m A b1 k mid b3 [B1 W1] H2 [B3 W3].
  pose proof (u8arr_of_rw_cells segs m _ k mid H2) as [B2 W2].
  destruct H2 as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [L2 _].
  exists (b1 ++ mid ++ b3). split; [rewrite !length_app; lia|]. split.
  - apply bytes_at_app. split; [exact B1|]. apply bytes_at_app. split; [exact B2|]. rewrite L2. exact B3.
  - rewrite !length_app, L2.
    replace (Z.of_nat (length b1 + (k + length b3))) with (Z.of_nat (length b1) + (Z.of_nat k + Z.of_nat (length b3)))%Z by lia.
    apply wr_at_join; [exact W1| | lia | lia]. rewrite L2 in W2. apply wr_at_join; [exact W2| exact W3 | lia | lia].
Qed.

Lemma u8arr_app : forall segs (m : mem) A b1 b2,
  u8arr segs m A b1 -> u8arr segs m (A + Z.of_nat (length b1)) b2 -> u8arr segs m A (b1 ++ b2).
Proof.
  intros segs m A b1 b2 [B1 W1] [B2 W2]. split.
  - apply bytes_at_app. split; assumption.
  - rewrite length_app. replace (Z.of_nat (length b1 + length b2)) with (Z.of_nat (length b1) + Z.of_nat (length b2))%Z by lia.
    apply wr_at_join; [exact W1 | exact W2 | lia | lia].
Qed.

Lemma u8arr_read1 : forall segs (m : mem) A bs k, u8arr segs m A bs -> (0 <= k < Z.of_nat (length bs))%Z ->
  exists b, ov_read_bytes segs m (wa (A + k)) 1 = Some [b].
Proof.
  intros segs m A bs k H Hk. destruct (nth_error bs (Z.to_nat k)) as [b|] eqn:E; [|apply nth_error_None in E; lia].
  exists b. eapply u8arr_read; [exact H | exact E | lia | reflexivity].
Qed.

Lemma u8arr_read8 : forall segs (m : mem) A bs k, u8arr segs m A bs -> (0 <= k)%Z -> (k + 8 <= Z.of_nat (length bs))%Z ->
  exists w, ov_read_bytes segs m (wa (A + k)) 8 = Some (le8 w).
Proof. intros segs m A bs k [H _] Hk Hl. eapply bytes_u64_read; eassumption. Qed.

Lemma u8arr_storeN_ok : forall segs (m : mem) A bs k (n : nat) a, u8arr segs m A bs -> (0 <= k)%Z -> (k + Z.of_nat n <= Z.of_nat (length bs))%Z ->
  a = wa (A + k) -> store_ok segs m a n = true.
Proof. intros segs m A bs k n a [_ Hw] Hk Hl ->. eapply wr_at_store_ok; eauto. Qed.

Lemma u8arr_writeN : forall segs (m : mem) A bs k (xs : list byte), u8arr segs m A bs -> (0 <= k)%Z -> (k + Z.of_nat (length xs) <= Z.of_nat (length bs))%Z ->
  u8arr segs (write_to_mem m (wa (A + k)) xs) A (upd_bytes bs (Z.to_nat k) xs).
Proof.
  intros segs m A bs k xs [Hb Hw] Hk Hl. split.
  - apply bytes_at_write_inside; [exact Hb | lia | lia].
  - rewrite upd_bytes_length by lia. apply wr_at_write. exact Hw.
Qed.

Lemma zx16_small : forall x, (0 <= x < 65536)%Z -> zx16 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x H. unfold zx16. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma sx16_small : forall x, (0 <= x < 32768)%Z -> sx16 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
  intros x H. unfold sx16. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 16)%Z with 65536%Z. change (65536 / 2)%Z with 32768%Z.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma swrap32_id : forall x, (-2147483648 <= x < 2147483648)%Z -> bv_swrap 32 x = x.
Proof.
  intros x H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 / 2)%Z with 2147483648%Z.
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma swrap32_Z : forall x, bv_swrap 32 x = ((x + 2147483648) mod 4294967296 - 2147483648)%Z.
Proof. intros x. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. reflexivity. Qed.

Lemma bv_swrap32 : forall x, bv_swrap 32 x = swrap32 x.
Proof. intros x. rewrite swrap32_Z. reflexivity. Qed.

Lemma shl3 : forall x, Z.shiftl x 3 = (8 * x)%Z.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.
Lemma shl1 : forall x, Z.shiftl x 1 = (2 * x)%Z.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.
Lemma shl2 : forall x, Z.shiftl x 2 = (4 * x)%Z.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.
Lemma shl4 : forall x, Z.shiftl x 4 = (16 * x)%Z.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.

Ltac num_simple_expr x :=
  lazymatch x with
  | context [Z.shiftl _ _] => fail | context [Z.shiftr _ _] => fail | context [Z.lor _ _] => fail
  | context [Z.land _ _] => fail | context [Z.lxor _ _] => fail
  | context [bv_unsigned ?v] => is_var v; fail
  | _ => idtac
  end.

Ltac num_strip_mods t :=
  lazymatch t with
  | Z.modulo ?a 18446744073709551616 => num_strip_mods a
  | Z.add ?a ?b => let a' := num_strip_mods a in let b' := num_strip_mods b in constr:(Z.add a' b')
  | Z.sub ?a ?b => let a' := num_strip_mods a in let b' := num_strip_mods b in constr:(Z.sub a' b')
  | Z.mul ?a ?b => let a' := num_strip_mods a in let b' := num_strip_mods b in constr:(Z.mul a' b')
  | Z.opp ?a => let a' := num_strip_mods a in constr:(Z.opp a')
  | _ => t
  end.

Ltac nnorm :=
  cbv beta;
  repeat match goal with
  | |- context [Z.shiftl ?x 3] => rewrite (shl3 x)
  | |- context [Z.shiftl ?x 1] => rewrite (shl1 x)
  | |- context [Z.shiftl ?x 2] => rewrite (shl2 x)
  | |- context [Z.shiftl ?x 4] => rewrite (shl4 x)
  | |- context [bv_swrap 32 ?t] =>
      num_simple_expr t;
      let t' := num_strip_mods t in
      replace (bv_swrap 32 t) with t' by (rewrite bv_swrap32; unfold swrap32; Z.div_mod_to_equations; lia)
  | |- context [zx16 (Z_to_bv 64 ?x)] => rewrite (zx16_small x) by lia
  | |- context [sx16 (Z_to_bv 64 ?x)] => rewrite (sx16_small x) by lia
  | |- context [Z.modulo ?x 65536] => rewrite (Z.mod_small x 65536) by lia
  | |- context [Z.modulo ?x 18446744073709551616] => num_simple_expr x; rewrite (Z.mod_small x 18446744073709551616) by lia
  | |- context [Z_to_bv 64 ?t] =>
      lazymatch t with context [Z.modulo ?x 18446744073709551616] => num_simple_expr x end;
      let t' := num_strip_mods t in
      lazymatch t' with context [Z.modulo _ 18446744073709551616] => fail | _ => idtac end;
      replace (Z_to_bv 64 t) with (Z_to_bv 64 t') by (apply Z_to_bv_eqm; Z.div_mod_to_equations; lia)
  | |- context [Z.shiftr (Z.shiftl ?k 48 mod 18446744073709551616) 48] => rewrite (shl48_shr48 k) by lia
  | |- context [Z.shiftr (Z.shiftl ?k 48 mod 18446744073709551616) 45] => rewrite (shl48_shr45 k) by lia
  | |- context [Z.shiftr (Z.shiftl ?k 51 mod 18446744073709551616) 48] => rewrite (shl51_shr48 k) by lia
  end.

Ltac num_cur_mem k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => k m end.

Ltac num_st_eq_leaf :=
  lazymatch goal with
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; lia | word_eq_tac]
  | |- _ => reflexivity
  end.
Ltac num_st_eq_tree :=
  lazymatch goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal; num_st_eq_tree
  | |- Some _ = Some _ => f_equal; num_st_eq_leaf
  | |- _ => reflexivity
  end.
Ltac num_st_eq :=
  cbv delta [mkR];
  lazymatch goal with
  | |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => f_equal; num_st_eq_tree
  end.

Ltac u64_read XA i w :=
  lazymatch type of XA with
  | u64arr ?segs ?m ?X ?ws =>
      let EW := fresh "EW" in
      destruct (nth_error ws (Z.to_nat i)) as [w|] eqn:EW; [|apply nth_error_None in EW; lia];
      let RD := fresh "RD" in
      pose proof (u64arr_read segs m X ws i w _ XA EW ltac:(lia) eq_refl) as RD
  end.

Ltac u64_store XA i :=
  lazymatch type of XA with
  | u64arr ?segs ?m ?X ?ws =>
      let SOK := fresh "SOK" in
      pose proof (u64arr_store_ok segs m X ws i _ XA ltac:(lia) eq_refl) as SOK;
      step;
      let XA' := fresh "XA" in
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le8 ?v)) _) =>
          pose proof (u64arr_write segs m X ws i v XA ltac:(lia)) as XA'
      end;
      store_done;
      try clear XA; rename XA' into XA
  end.

Ltac u64_store_lit XA i V :=
  lazymatch type of XA with
  | u64arr ?segs ?m ?X ?ws =>
      let SOK := fresh "SOK" in
      pose proof (u64arr_store_ok segs m X ws i _ XA ltac:(lia) eq_refl) as SOK;
      step;
      let XA' := fresh "XA" in
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bs) _) =>
          change bs with (le8 V);
          pose proof (u64arr_write segs m X ws i V XA ltac:(lia)) as XA'
      end;
      store_done;
      try clear XA; rename XA' into XA
  end.

Ltac u8_store UA k n :=
  lazymatch type of UA with
  | u8arr ?segs ?m ?A ?bs =>
      let SOK := fresh "SOK" in
      pose proof (u8arr_storeN_ok segs m A bs k n _ UA ltac:(lia) ltac:(lia) eq_refl) as SOK;
      step;
      let UA' := fresh "UA" in
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?a ?xs) _) =>
          pose proof (u8arr_writeN segs m A bs k xs UA ltac:(lia)
                        ltac:(rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1; cbn [length]; lia)) as UA';
          lazymatch a with
          | wa (A + k) => idtac
          | Z_to_bv 64 ?E => replace (wa (A + k)) with (wa E) in UA' by (f_equal; lia)
          | wa ?E => replace (wa (A + k)) with (wa E) in UA' by (f_equal; lia)
          end
      end;
      store_done;
      try clear UA; rename UA' into UA
  end.

Definition BIG_CAP : Z := 62.
Definition bigint_at (segs : list Segment) (m : mem) (X : Z) (ws : list word) (len : Z) : Prop :=
  u64arr segs m X ws /\ length ws = 62%nat /\ rw_cells segs m (X + 496) [C2 (Z_to_bv 64 len)] /\ (0 <= len <= 62)%Z.

Lemma u8arr_of_u64arr : forall segs (m : mem) X ws, u64arr segs m X ws -> length ws = 62%nat ->
  exists bs, length bs = 496%nat /\ u8arr segs m X bs.
Proof.
  intros segs m X ws H L. exists (u64s ws). split; [rewrite u64s_length, L; reflexivity|].
  destruct H as [HB HW]. split; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws))%Z by lia. exact HW.
Qed.
Lemma u64arr_of_u8arr : forall segs (m : mem) X bs, u8arr segs m X bs -> length bs = 496%nat ->
  exists ws, length ws = 62%nat /\ u64arr segs m X ws.
Proof.
  intros segs m X bs H L. apply rw_cells_of_u8arr in H. rewrite L in H. change 496%nat with (8 * 62)%nat in H.
  exact (u64arr_of_rw_cells segs m X 62 bs H).
Qed.

Definition LM_STACK : Z := 1136.
Definition lm_post_g (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' ws' len',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(bv_unsigned sp - LM_STACK, bv_unsigned sp); (X, X + 498)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ bigint_at segs m' X ws' len' /\ stk segs m' lo (bv_unsigned sp).

Definition lm_stmt_g (segs : list Segment) (entry : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (X Y ny lo : Z) ws len (ybs : list byte),
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> (lo + LM_STACK <= bv_unsigned sp)%Z ->
  bigint_at segs m X ws len -> (bv_unsigned sp <= X)%Z ->
  bytes_at segs m Y ybs -> Z.of_nat (length ybs) = (8 * ny)%Z -> (Y + 8 * ny <= lo)%Z ->
  evt segs (lm_post_g segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 ny) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Definition P5_STACK : Z := 48 + LM_STACK.
Definition p5_post_g (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' ws' len',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(bv_unsigned sp - P5_STACK, bv_unsigned sp); (X, X + 498)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ bigint_at segs m' X ws' len' /\ stk segs m' lo (bv_unsigned sp).

Definition p5_stmt_g (segs : list Segment) (entry gtop : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (X e lo : Z) ws len,
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> (lo + P5_STACK <= bv_unsigned sp)%Z -> (gtop <= lo)%Z ->
  bigint_at segs m X ws len -> (bv_unsigned sp <= X)%Z ->
  (-2147483648 <= e < 2147483648)%Z ->
  evt segs (p5_post_g segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Definition memcpyZ_post_g (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Dst Src N : Z) (src : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(Dst, Dst + N)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ rw_cells segs m' Dst [CB (Z.to_nat N) src]
    /\ bytes_at segs m' Src src.
Definition memcpyZ_stmt_g (segs : list Segment) (entry : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Dst Src N : Z) (src junk : list byte),
  bytes_at segs m Src src -> length src = Z.to_nat N -> rw_cells segs m Dst [CB (Z.to_nat N) junk] ->
  (Src + N <= Dst \/ Dst + N <= Src)%Z -> (0 <= N < 2^64)%Z -> (0 <= Src < 2^64)%Z -> (0 <= Dst < 2^64)%Z -> mem_inv segs m ->
  evt segs (memcpyZ_post_g segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Definition memsetZ_post_g (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D C N : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(D, D + N)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ rw_cells segs m' D [CB (Z.to_nat N) (repeat (Z_to_bv 8 (C mod 256)) (Z.to_nat N))].
Definition memsetZ_stmt_g (segs : list Segment) (entry : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (D C N : Z) (junk : list byte),
  rw_cells segs m D [CB (Z.to_nat N) junk] ->
  mem_inv segs m ->
  (0 <= D)%Z -> (0 <= N < 2^64)%Z -> (D + N <= 2^64)%Z -> (0 <= C < 2^64)%Z ->
  evt segs (memsetZ_post_g segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D C N m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Definition memmove_post_g (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D N U : Z) (L : nat) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m' bs',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(D, D + N)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m' /\ u8arr segs m' U bs' /\ length bs' = L.
Definition memmove_stmt_g (segs : list Segment) (entry : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (D S N U : Z) (bs : list byte),
  u8arr segs m U bs -> (U <= S)%Z -> (S <= D < 2^64)%Z -> (D + N <= U + Z.of_nat (length bs))%Z -> (0 <= N < 2^62)%Z ->
  ((D - S) mod 8 = 0)%Z -> mem_inv segs m ->
  evt segs (memmove_post_g segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D N U (length bs) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Definition PM_STACK : Z := 96.
Definition PM_MAXD : Z := 769.
Definition NUM_TXT_MAX : Z := 2147483648.
Definition pm_spans_ok (A : Z) (txt : list byte) (IP IL FPT FL : Z) : Prop :=
  (A <= IP /\ 0 <= IL /\ IP + IL <= A + Z.of_nat (length txt) /\
   (FPT = 0 \/ (A <= FPT /\ 0 <= FL /\ FPT + FL <= A + Z.of_nat (length txt))))%Z.
Definition pm_post_g (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X IP IL FPT FL lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' ws' len' dg',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(bv_unsigned sp - PM_STACK, bv_unsigned sp); (X, X + 498); (X + 504, X + 512)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ bigint_at segs m' X ws' len' /\ rw_cells segs m' (X + 504) [C8 (Z_to_bv 64 dg')]
    /\ rw_cells segs m' (X - 40) [C8 (Z_to_bv 64 IP); C8 (Z_to_bv 64 IL); C8 (Z_to_bv 64 FPT); C8 (Z_to_bv 64 FL)]
    /\ stk segs m' lo (bv_unsigned sp).
Definition pm_stmt_g (segs : list Segment) (entry gtop : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (X A IP IL FPT FL lo : Z) ws len (txt jd : list byte),
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> (lo + PM_STACK <= bv_unsigned sp)%Z -> (gtop <= lo)%Z ->
  bigint_at segs m X ws len -> (bv_unsigned sp <= X - 40)%Z ->
  rw_cells segs m (X + 504) [CB 8 jd] ->
  rw_cells segs m (X - 40) [C8 (Z_to_bv 64 IP); C8 (Z_to_bv 64 IL); C8 (Z_to_bv 64 FPT); C8 (Z_to_bv 64 FL)] ->
  bytes_at segs m A txt -> (A + Z.of_nat (length txt) <= lo)%Z -> (Z.of_nat (length txt) < NUM_TXT_MAX)%Z ->
  pm_spans_ok A txt IP IL FPT FL ->
  evt segs (pm_post_g segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X IP IL FPT FL lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 (X - 72)) (Z_to_bv 64 PM_MAXD) (Z_to_bv 64 (X + 504)) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Definition PDC_STACK : Z := 32 + P5_STACK.
Definition pdc_post_g (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' ws' len',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(bv_unsigned sp - PDC_STACK, bv_unsigned sp); (X, X + 498)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ bigint_at segs m' X ws' len' /\ stk segs m' lo (bv_unsigned sp).
Definition pdc_stmt_g (segs : list Segment) (entry gtop : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (X e lo : Z) ws len,
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> (lo + PDC_STACK <= bv_unsigned sp)%Z -> (gtop <= lo)%Z ->
  bigint_at segs m X ws len -> (bv_unsigned sp <= X)%Z ->
  (-2147483648 <= e < 2147483648)%Z ->
  evt segs (pdc_post_g segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Definition NDC_STACK : Z := 576 + P5_STACK.
Definition ndc_post_g (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' ws' len',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(bv_unsigned sp - NDC_STACK, bv_unsigned sp); (X, X + 498)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ bigint_at segs m' X ws' len' /\ stk segs m' lo (bv_unsigned sp).
Definition ndc_stmt_g (segs : list Segment) (entry gtop : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (X e lo : Z) ws len,
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> (lo + NDC_STACK <= bv_unsigned sp)%Z -> (gtop <= lo)%Z ->
  bigint_at segs m X ws len -> (bv_unsigned sp <= X)%Z ->
  (-2147483648 <= e < 2147483648)%Z ->
  evt segs (ndc_post_g segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) a1 a2 (Z_to_bv 64 e) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Definition SPATH_STACK : Z := 688 + NDC_STACK.
Definition SPATH_A4 : Z := 42949673006.
Definition spath_post_g (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (OUT lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (v : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom segs)
    /\ frm0 fc'
    /\ munch [(bv_unsigned sp - SPATH_STACK, bv_unsigned sp); (OUT, OUT + 8)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ rw_cells segs m' OUT [C8 v] /\ stk segs m' lo (bv_unsigned sp).
Definition spath_stmt_g (segs : list Segment) (entry gtop : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (A FIRST LAST OUT lo : Z) (txt : list byte) (v0 : word),
  mem_inv segs m -> frm0 fc ->
  stk segs m lo (bv_unsigned sp) -> (lo + SPATH_STACK <= bv_unsigned sp)%Z -> (gtop <= lo)%Z ->
  bytes_at segs m A txt -> (A + Z.of_nat (length txt) <= lo)%Z -> (Z.of_nat (length txt) < NUM_TXT_MAX)%Z ->
  (A <= FIRST < LAST)%Z -> (LAST <= A + Z.of_nat (length txt))%Z ->
  rw_cells segs m OUT [C8 v0] -> (bv_unsigned sp <= OUT)%Z ->
  evt segs (spath_post_g segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 OUT lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) (Z_to_bv 64 OUT) (Z_to_bv 64 53) (Z_to_bv 64 SPATH_A4) (Z_to_bv 64 1)
             a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Definition FF_STACK : Z := 96 + SPATH_STACK.
Definition ff_post_g (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom segs)
    /\ frm0 fc'
    /\ munch [(bv_unsigned sp - FF_STACK, bv_unsigned sp)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ stk segs m' lo (bv_unsigned sp).
Definition ff_stmt_g (segs : list Segment) (entry gtop : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (A FIRST LAST lo : Z) (txt : list byte),
  mem_inv segs m -> frm0 fc ->
  stk segs m lo (bv_unsigned sp) -> (lo + FF_STACK <= bv_unsigned sp)%Z -> (gtop <= lo)%Z ->
  bytes_at segs m A txt -> (A + Z.of_nat (length txt) <= lo)%Z -> (Z.of_nat (length txt) < NUM_TXT_MAX)%Z ->
  (A <= FIRST <= LAST)%Z -> (LAST <= A + Z.of_nat (length txt))%Z ->
  evt segs (ff_post_g segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom segs)).
