(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame Hoare.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Export FastLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Abbreviation W z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Wu : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (W z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hz. Qed.

Lemma Wu_mod : forall z, bv_unsigned (W z) = z mod 2 ^ 64.
Proof. intros z. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma W_u : forall x : word, W (bv_unsigned x) = x.
Proof. intros x. apply Z_to_bv_bv_unsigned. Qed.

Lemma W_eq_mod : forall a b, a mod 2 ^ 64 = b mod 2 ^ 64 -> W a = W b.
Proof. intros a b H. apply bv_eq. rewrite !Wu_mod. exact H. Qed.

Lemma Ws : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> bv_signed (W z) = z.
Proof.
  intros z Hz. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
  rewrite Zplus_mod_idemp_l. rewrite Z.mod_small by lia. lia.
Qed.

Lemma Ws_pos : forall z, 0 <= z < 2 ^ 63 -> bv_signed (W z) = z.
Proof. intros. apply Ws. lia. Qed.

(* [comment removed for export] *)
Lemma addi_W : forall a k, v_addi (W a) k = W (a + k).
Proof. intros. unfold v_addi. apply W_eq_mod. rewrite Wu_mod. apply Zplus_mod_idemp_l. Qed.

Lemma add_W : forall a b, v_add (W a) (W b) = W (a + b).
Proof. intros. unfold v_add. apply W_eq_mod. rewrite !Wu_mod. symmetry. apply Zplus_mod. Qed.

Lemma sub_W : forall a b, v_sub (W a) (W b) = W (a - b).
Proof. intros. unfold v_sub. apply W_eq_mod. rewrite !Wu_mod. symmetry. apply Zminus_mod. Qed.

Lemma mul_W : forall a b, v_mul (W a) (W b) = W (a * b).
Proof. intros. unfold v_mul. apply W_eq_mod. rewrite !Wu_mod. symmetry. apply Zmult_mod. Qed.

Lemma slli_W : forall a k, 0 <= k -> v_slli (W a) k = W (a * 2 ^ k).
Proof.
  intros a k Hk. unfold v_slli. apply W_eq_mod. rewrite Wu_mod, Z.shiftl_mul_pow2 by lia.
  rewrite Zmult_mod_idemp_l. reflexivity.
Qed.

Lemma addi_0 : forall x : word, v_addi x 0 = x.
Proof. intros. unfold v_addi. rewrite Z.add_0_r. apply W_u. Qed.

(* [comment removed for export] *)
Lemma u_and : forall x y : word, bv_unsigned (v_and x y) = Z.land (bv_unsigned x) (bv_unsigned y).
Proof.
  intros x y. unfold v_and. apply Wu. pose proof (u64_range x). pose proof (u64_range y).
  apply Z_land_range; lia.
Qed.
Lemma u_or : forall x y : word, bv_unsigned (v_or x y) = Z.lor (bv_unsigned x) (bv_unsigned y).
Proof.
  intros x y. unfold v_or. apply Wu. pose proof (u64_range x). pose proof (u64_range y).
  apply Z_lor_range; lia.
Qed.
Lemma u_xor : forall x y : word, bv_unsigned (v_xor x y) = Z.lxor (bv_unsigned x) (bv_unsigned y).
Proof.
  intros x y. unfold v_xor. apply Wu. pose proof (u64_range x). pose proof (u64_range y).
  apply Z_lxor_range; lia.
Qed.

Lemma u_andi_ones : forall (x : word) k, 0 <= k < 64 ->
  bv_unsigned (v_andi x (Z.ones k)) = bv_unsigned x mod 2 ^ k.
Proof.
  intros x k Hk. unfold v_andi. pose proof (u64_range x).
  assert (Ho : 0 <= Z.ones k < 2 ^ 64).
  { rewrite Z.ones_equiv. assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
    assert (2 ^ k <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia). lia. }
  rewrite (bv_wrap_small 64 (Z.ones k)) by exact Ho.
  rewrite Z.land_ones by lia. apply Wu.
  pose proof (Z.mod_pos_bound (bv_unsigned x) (2 ^ k) ltac:(apply Z.pow_pos_nonneg; lia)).
  assert (2 ^ k <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma xor_W : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> v_xor (W a) (W b) = W (Z.lxor a b).
Proof. intros a b Ha Hb. unfold v_xor. rewrite !Wu by lia. reflexivity. Qed.
Lemma or_W : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> v_or (W a) (W b) = W (Z.lor a b).
Proof. intros a b Ha Hb. unfold v_or. rewrite !Wu by lia. reflexivity. Qed.
Lemma and_W : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> v_and (W a) (W b) = W (Z.land a b).
Proof. intros a b Ha Hb. unfold v_and. rewrite !Wu by lia. reflexivity. Qed.

Lemma and_m1_l : forall x : word, v_and (W (-1)) x = x.
Proof.
  intros x. unfold v_and. rewrite Wu_mod. change ((-1) mod 2 ^ 64) with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. pose proof (u64_range x).
  rewrite Z.mod_small by lia. apply W_u.
Qed.
Lemma and_0_l : forall x : word, v_and (W 0) x = W 0.
Proof. intros x. unfold v_and. change (bv_unsigned (W 0)) with 0. rewrite Z.land_0_l. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sub_zero_eq : forall x y, - 2 ^ 63 < x - y < 2 ^ 63 -> bv_unsigned (W (x - y)) = 0 -> x = y.
Proof.
  intros x y Hr H. rewrite Wu_mod in H.
  pose proof (Z.div_mod (x - y) (2 ^ 64) ltac:(lia)) as E. rewrite H in E. lia.
Qed.

Lemma andi255_byte : forall b : Z, 0 <= b < 256 -> v_andi (W b) 255 = W b.
Proof.
  intros b Hb. rewrite <- (W_u (v_andi (W b) 255)). f_equal. change 255 with (Z.ones 8).
  rewrite u_andi_ones by lia. rewrite Wu by lia. apply Z.mod_small. change (2 ^ 8) with 256. lia.
Qed.

(* [comment removed for export] *)
Lemma sltu0_W0 : v_sltu (W 0) (W 0) = W 0.
Proof. reflexivity. Qed.

Lemma sltu0_nz : forall x : word, bv_unsigned x <> 0 -> v_sltu (W 0) x = W 1.
Proof.
  intros x Hx. unfold v_sltu, c_ltu, bv_ltu. change (bv_unsigned (W 0)) with 0.
  pose proof (u64_range x). destruct (Z.ltb_spec 0 (bv_unsigned x)); [reflexivity | lia].
Qed.

Lemma u_sltu0 : forall x : word, bv_unsigned (v_sltu (W 0) x) = if Z.eqb (bv_unsigned x) 0 then 0 else 1.
Proof.
  intros x. destruct (Z.eqb_spec (bv_unsigned x) 0) as [E|E].
  - replace x with (W 0) by (rewrite <- (W_u x), E; reflexivity). reflexivity.
  - rewrite sltu0_nz by exact E. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma land_pow2 : forall u b, 0 <= b -> Z.land u (2 ^ b) = if Z.testbit u b then 2 ^ b else 0.
Proof.
  intros u b Hb. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec b i) as [->|Hne].
  - destruct (Z.testbit u i) eqn:E; [rewrite Z.pow2_bits_eqb, Z.eqb_refl by lia; reflexivity | rewrite Z.bits_0; reflexivity].
  - rewrite andb_false_r. destruct (Z.testbit u b); [rewrite Z.pow2_bits_eqb by lia; symmetry; apply Z.eqb_neq; exact Hne | rewrite Z.bits_0; reflexivity].
Qed.

Lemma bit_test : forall m b k, k = 2 ^ b -> 0 <= m < 2 ^ 64 -> 0 <= b < 63 ->
  (bv_unsigned (v_andi (W m) k) <> 0 -> m mod (2 * k) = k + m mod k)
  /\ (bv_unsigned (v_andi (W m) k) = 0 -> m mod (2 * k) = m mod k).
Proof.
  intros m b k -> Hm Hb. unfold v_andi. rewrite (Wu m) by lia.
  assert (Hp : 0 < 2 ^ b) by (apply Z.pow_pos_nonneg; lia).
  assert (Hp63 : 2 ^ b <= 4611686018427387904) by (change 4611686018427387904 with (2 ^ 62); apply Z.pow_le_mono_r; lia).
  rewrite (bv_wrap_small 64 (2 ^ b)) by (change (bv_modulus 64) with (2 ^ 64); lia).
  rewrite land_pow2 by lia.
  replace (2 * 2 ^ b) with (2 ^ b * 2) by lia. rewrite Z.rem_mul_r by lia.
  destruct (Z.testbit m b) eqn:E.
  - apply Z.testbit_true in E; [|lia]. rewrite E. rewrite Wu by lia. split; intros; lia.
  - apply Z.testbit_false in E; [|lia]. rewrite E. change (bv_unsigned (W 0)) with 0. split; intros; lia.
Qed.

(* [comment removed for export] *)
Lemma lxor_land7_zero : forall a b, 0 <= a -> 0 <= b -> Z.land (Z.lxor a b) 7 = 0 -> a mod 8 = b mod 8.
Proof.
  intros a b Ha Hb H. change 7 with (Z.ones 3) in H. rewrite Z.land_ones in H by lia.
  change 8 with (2 ^ 3). apply Z.bits_inj'. intros i Hi.
  destruct (Z.lt_ge_cases i 3).
  - rewrite !Z.mod_pow2_bits_low by lia.
    pose proof (f_equal (fun z => Z.testbit z i) H) as E. cbv beta in E.
    rewrite Z.mod_pow2_bits_low, Z.lxor_spec, Z.bits_0 in E by lia.
    destruct (Z.testbit a i), (Z.testbit b i); cbn in E; congruence.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma lxor_mod8_zero : forall a b, 0 <= a -> 0 <= b -> (Z.lxor a b) mod 8 = 0 -> a mod 8 = b mod 8.
Proof.
  intros a b Ha Hb H. apply lxor_land7_zero; [assumption | assumption |].
  change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H.
Qed.

Lemma mod_neg64 : forall x, 0 < x < 2 ^ 64 -> (- x) mod 2 ^ 64 = 2 ^ 64 - x.
Proof. intros x Hx. symmetry. apply Z.mod_unique with (-1); lia. Qed.

(* [comment removed for export] *)
Lemma word_is_W : forall x : word, exists z, 0 <= z < 2 ^ 64 /\ x = W z.
Proof. intros x. exists (bv_unsigned x). split; [apply u64_range | symmetry; apply W_u]. Qed.

(* [comment removed for export] *)
Lemma swrap32_small : forall z, - 2 ^ 31 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31).
  change (bv_modulus 32) with (2 ^ 32). rewrite Z.mod_small by lia. lia.
Qed.

Lemma addiw_W : forall a k, 0 <= a < 2 ^ 64 -> - 2 ^ 31 <= a + k < 2 ^ 31 -> v_addiw (W a) k = W (a + k).
Proof. intros a k Ha H. unfold v_addiw. rewrite Wu by lia. rewrite swrap32_small by lia. reflexivity. Qed.

Lemma lw_W : forall a, 0 <= a < 2 ^ 31 -> v_lw (W a) = W a.
Proof. intros a Ha. unfold v_lw. rewrite Wu by lia. rewrite swrap32_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma v_jalr_even : forall k : word, bv_unsigned k mod 2 = 0 -> v_jalr k 0 = k.
Proof.
  intros k Hk. unfold v_jalr, jalr_tgtZ. rewrite Z.add_0_r.
  rewrite Hoare.land_m2_even by exact Hk. apply W_u.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Mem.
Variable SEGS : list Segment.

Definition rd_ok (M : mem) (a n : Z) : Prop :=
  forall i, 0 <= i < n -> M (W (a + i)) <> None.

Definition wr_ok (M : mem) (a n : Z) : Prop :=
  forall x (m : nat), a <= x -> x + Z.of_nat m <= a + n -> store_ok SEGS M (W x) m = true.

Definition cell (M : mem) (a : Z) (n : nat) (v : word) : Prop :=
  rdn SEGS M (W a) n = Some (word_to_le_bytes n v).

Definition unch (M0 M : mem) (P : word -> Prop) : Prop :=
  forall x, ~ P x -> M x = M0 x.

Definition inr (x : word) (a n : Z) : Prop := a <= bv_unsigned x < a + n.

(* [comment removed for export] *)
Lemma rd_ok_grows : forall M M' a n, mem_grows M M' -> rd_ok M a n -> rd_ok M' a n.
Proof. intros M M' a n Hg H i Hi. apply Hg, H, Hi. Qed.

Lemma wr_ok_grows : forall M M' a n, mem_grows M M' -> wr_ok M a n -> wr_ok M' a n.
Proof. intros M M' a n Hg H x m H1 H2. eapply store_ok_mono; [exact Hg | apply H; assumption]. Qed.

Lemma rd_ok_sub : forall M a n a' n', rd_ok M a n -> a <= a' -> a' + n' <= a + n -> rd_ok M a' n'.
Proof.
  intros M a n a' n' H H1 H2 i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia.
Qed.

Lemma wr_ok_sub : forall M a n a' n', wr_ok M a n -> a <= a' -> a' + n' <= a + n -> wr_ok M a' n'.
Proof. intros M a n a' n' H H1 H2 x m Hx Hm. apply H; lia. Qed.

(* [comment removed for export] *)
Lemma rdn_rd_ok : forall M (n : nat) a, 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  rd_ok M a (Z.of_nat n) -> exists bs, rdn SEGS M (W a) n = Some bs.
Proof.
  intros M n. induction n as [|n IH]; intros a Ha Hn H; [exists []; reflexivity|].
  cbn [rdn]. pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
  destruct (M (W a)) as [b|] eqn:Eb; [|congruence].
  assert (E1 : (W a + 1)%bv = W (a + 1)).
  { apply bv_eq. rewrite bv_add_unsigned. change (bv_unsigned (1 : word)) with 1.
    rewrite !Wu_mod. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite Zplus_mod_idemp_l. reflexivity. }
  rewrite E1.
  destruct n as [|n'].
  - cbn [rdn]. exists [b]. reflexivity.
  - destruct (IH (a + 1)) as (bs & Hbs); [lia | lia | | rewrite Hbs; exists (b :: bs); reflexivity].
    intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply H. lia.
Qed.

Lemma load_rd : forall M a n x (k : nat),
  rd_ok M a n -> 0 <= a -> a + n < 2 ^ 64 -> a <= x -> x + Z.of_nat k <= a + n -> (k <= 8)%nat ->
  exists v, load_ok SEGS M (W x) k v.
Proof.
  intros M a n x k H Ha Hn Hx Hk Hk8.
  destruct (rdn_rd_ok M k x) as (bs & Hbs); [lia | lia | eapply rd_ok_sub; [exact H | lia | lia] |].
  exists (W (bytes_le_to_Z bs)). exists bs. split; [exact Hbs|].
  pose proof (rdn_length _ _ _ _ _ Hbs) as Hl. pose proof (bytes_le_to_Z_bound bs) as Hb.
  pose proof (bytes_le_to_Z_nonneg bs). rewrite Hl in Hb.
  assert (2 ^ (8 * Z.of_nat k) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  rewrite Wu by lia. reflexivity.
Qed.

Lemma load_cell8 : forall M a v, cell M a 8 v -> load_ok SEGS M (W a) 8 v.
Proof. intros M a v H. exists (word_to_le_bytes 8 v). split; [exact H | apply bytes_le_to_Z_8]. Qed.

Lemma load_cell : forall M a (n : nat) v, cell M a n v -> (n <= 8)%nat ->
  load_ok SEGS M (W a) n (W (bv_unsigned v mod 2 ^ (8 * Z.of_nat n))).
Proof.
  intros M a n v H Hn. exists (word_to_le_bytes n v). split; [exact H|].
  rewrite bytes_le_N. pose proof (u64_range v).
  assert (0 < 2 ^ (8 * Z.of_nat n)) by (apply Z.pow_pos_nonneg; lia).
  assert (2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  pose proof (Z.mod_pos_bound (bv_unsigned v) (2 ^ (8 * Z.of_nat n)) ltac:(lia)).
  rewrite Wu by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma wr_ok_store : forall M a n x (k : nat),
  wr_ok M a n -> a <= x -> x + Z.of_nat k <= a + n -> store_ok SEGS M (W x) k = true.
Proof. intros M a n x k H H1 H2. apply H; assumption. Qed.

Lemma cell_store_same : forall M a (n : nat) v, 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  cell (wbytes M (W a) (word_to_le_bytes n v)) a n v.
Proof.
  intros M a n v Ha Hn. unfold cell.
  pose proof (rdn_wbytes_hit SEGS (word_to_le_bytes n v) M (W a)) as H.
  rewrite length_N_to_le_bytes in H. apply H. rewrite Wu by lia. lia.
Qed.

Lemma cell_agree : forall M M' a (n : nat) v, 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  (forall x, inr x a (Z.of_nat n) -> M' x = M x) -> cell M a n v -> cell M' a n v.
Proof.
  intros M M' a n v Ha Hn Hag H. unfold cell in *. rewrite <- H.
  apply rdn_ext; [rewrite Wu by lia; lia|].
  intros x Hx. rewrite Wu in Hx by lia. apply Hag. exact Hx.
Qed.

Lemma cell_store_same' : forall M a a' (n : nat) v, a = a' -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  cell (wbytes M (W a') (word_to_le_bytes n v)) a n v.
Proof. intros M a a' n v <- Ha Hn. apply cell_store_same; assumption. Qed.

Lemma wbytes_out : forall M b bs x, 0 <= b -> b + Z.of_nat (length bs) < 2 ^ 64 ->
  ~ inr x b (Z.of_nat (length bs)) -> wbytes M (W b) bs x = M x.
Proof.
  intros M b bs x Hb Hn Hx. apply Frame.wbytes_outside.
  - unfold in_rng. rewrite Wu by lia. exact Hx.
  - rewrite Wu by lia. lia.
Qed.

Lemma cell_store_other : forall M a (n : nat) v b bs,
  0 <= a -> a + Z.of_nat n < 2 ^ 64 -> 0 <= b -> b + Z.of_nat (length bs) < 2 ^ 64 ->
  (a + Z.of_nat n <= b \/ b + Z.of_nat (length bs) <= a) ->
  cell M a n v -> cell (wbytes M (W b) bs) a n v.
Proof.
  intros M a n v b bs Ha Hn Hb Hbn Hd H. eapply cell_agree; [exact Ha | exact Hn | | exact H].
  intros x Hx. apply wbytes_out; [exact Hb | exact Hbn|]. unfold inr in *. lia.
Qed.

Lemma unch_refl : forall M P, unch M M P.
Proof. intros M P x _. reflexivity. Qed.

Lemma unch_store : forall M0 M (P : word -> Prop) b bs,
  unch M0 M P -> 0 <= b -> b + Z.of_nat (length bs) < 2 ^ 64 ->
  (forall x, inr x b (Z.of_nat (length bs)) -> P x) ->
  unch M0 (wbytes M (W b) bs) P.
Proof.
  intros M0 M P b bs H Hb Hn HP x Hx. rewrite wbytes_out; [apply H, Hx | exact Hb | exact Hn|].
  intros Hin. apply Hx, HP, Hin.
Qed.

Lemma unch_weaken : forall M0 M (P P' : word -> Prop),
  unch M0 M P -> (forall x, P x -> P' x) -> unch M0 M P'.
Proof. intros M0 M P P' H HP x Hx. apply H. intros HPx. apply Hx, HP, HPx. Qed.

Lemma unch_trans : forall M0 M1 M2 (P : word -> Prop),
  unch M0 M1 P -> unch M1 M2 P -> unch M0 M2 P.
Proof. intros M0 M1 M2 P H1 H2 x Hx. rewrite (H2 x Hx). apply H1, Hx. Qed.

Lemma cell_unch : forall M0 M (P : word -> Prop) a (n : nat) v,
  unch M0 M P -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  (forall x, inr x a (Z.of_nat n) -> ~ P x) -> cell M0 a n v -> cell M a n v.
Proof.
  intros M0 M P a n v H Ha Hn HP Hc. eapply cell_agree; [exact Ha | exact Hn | | exact Hc].
  intros x Hx. apply H, HP, Hx.
Qed.

(* [comment removed for export] *)
Definition img_ok (M : mem) (lo hi : Z) : Prop := forall i, lo <= i < hi -> M (W i) = None.

Lemma img_unch : forall M0 M (P : word -> Prop) lo hi,
  unch M0 M P -> 0 <= lo -> hi < 2 ^ 64 -> (forall x, inr x lo (hi - lo) -> ~ P x) ->
  img_ok M0 lo hi -> img_ok M lo hi.
Proof.
  intros M0 M P lo hi H Hlo Hhi HP Hi i Hr. rewrite H; [apply Hi, Hr|].
  apply HP. unfold inr. rewrite Wu by lia. lia.
Qed.

Lemma load_img : forall M lo hi a (n : nat) bs v,
  img_ok M lo hi -> lo <= a -> a + Z.of_nat n <= hi -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  rdn SEGS (fun _ => None) (W a) n = Some bs -> bytes_le_to_Z bs = bv_unsigned v ->
  load_ok SEGS M (W a) n v.
Proof.
  intros M lo hi a n bs v Hi Hlo Hhi Ha Hn Hr Hv. exists bs. split; [|exact Hv].
  rewrite <- Hr. apply rdn_ext; [rewrite Wu by lia; lia|].
  intros x Hx. rewrite Wu in Hx by lia. rewrite <- (W_u x). apply Hi. lia.
Qed.

End Mem.
