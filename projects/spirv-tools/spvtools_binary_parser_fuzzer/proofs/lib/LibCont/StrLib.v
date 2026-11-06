(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec SeqExec StepTac StoreOk MemSplit Hoare RefMemcpyLib RefReadLib LibIface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition str_bytes (cs : list Z) : list byte := map (fun c => Z_to_bv 8 c) cs.

Lemma str_bytes_length : forall cs, length (str_bytes cs) = length cs.
Proof. intros. unfold str_bytes. apply length_map. Qed.

Lemma str_bytes_app : forall xs ys, str_bytes (xs ++ ys) = str_bytes xs ++ str_bytes ys.
Proof. intros. unfold str_bytes. apply map_app. Qed.

Lemma u8_of_Z : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned, bv_wrap8_mod. apply Z.mod_small. exact Hz. Qed.

Lemma Z_to_bv8_mod : forall z, Z_to_bv 8 z = Z_to_bv 8 (z mod 256).
Proof. intros z. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod. change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. reflexivity. Qed.

Lemma w1_bytes : forall c, word_to_le_bytes 1 (Z_to_bv 64 c) = [Z_to_bv 8 (c mod 256)].
Proof.
  intros c. unfold word_to_le_bytes. cbn [Z_to_le_bytes]. f_equal.
  rewrite Z_to_bv_unsigned, bv_wrap64_mod. rewrite (Z_to_bv8_mod (c mod 2 ^ 64)).
  f_equal. change (2 ^ 64) with (256 * 2 ^ 56). rewrite Z.rem_mul_r by lia.
  rewrite (Z.mul_comm 256), Z_mod_plus_full. apply Z.mod_mod. lia.
Qed.

Lemma w1_bytes_small : forall c, 0 <= c < 256 -> word_to_le_bytes 1 (Z_to_bv 64 c) = [Z_to_bv 8 c].
Proof. intros c Hc. rewrite w1_bytes, Z.mod_small by lia. reflexivity. Qed.

Lemma sb_byte_w1 : forall c, [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 c))] = word_to_le_bytes 1 (Z_to_bv 64 (c mod 256)).
Proof.
  intros c. rewrite w1_bytes. rewrite Z.mod_mod by lia. rewrite <- w1_bytes. reflexivity.
Qed.

Lemma w8_first_byte : forall v, firstn 1 (word_to_le_bytes 8 (Z_to_bv 64 v)) = [Z_to_bv 8 (v mod 256)].
Proof.
  intros v. unfold word_to_le_bytes. cbn [Z_to_le_bytes firstn]. rewrite <- (w1_bytes v). reflexivity.
Qed.

Section SB.
Variable SEGS : list Segment.

Lemma fld1_rdn : forall M a c, fld SEGS M a 1 c ->
  rdn SEGS M (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 (c mod 256)].
Proof using SEGS. intros M a c H. unfold fld in H. rewrite w1_bytes in H. exact H. Qed.

Lemma fld8_byte0 : forall M a v, fld SEGS M a 8 v ->
  rdn SEGS M (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 (v mod 256)].
Proof using SEGS.
  intros M a v H. unfold fld in H.
  pose proof (SeqExec.rdn_firstn SEGS M _ (Z_to_bv 64 a) _ 1 H ltac:(lia)) as H1.
  rewrite w8_first_byte in H1. exact H1.
Qed.

Lemma fld_str_rdn : forall M d cs,
  0 <= d -> d + Zlen cs < 2 ^ 64 ->
  (forall i, 0 <= i < Zlen cs -> 0 <= Znth i cs < 256 /\ fld SEGS M (d + i) 1 (Znth i cs)) ->
  rdn SEGS M (Z_to_bv 64 d) (length cs) = Some (str_bytes cs).
Proof using SEGS.
  intros M d cs. revert d. induction cs as [|c cs IH]; intros d Hd Hn HF; [reflexivity|].
  unfold Zlen in *. cbn [length str_bytes map] in *.
  change (S (length cs)) with (1 + length cs)%nat.
  change (Z_to_bv 8 c :: map (fun c0 : Z => Z_to_bv 8 c0) cs) with ([Z_to_bv 8 c] ++ str_bytes cs). apply rdn_app.
  - destruct (HF 0 ltac:(lia)) as [Hr H0]. unfold Znth in *. cbn [Z.to_nat nth] in *.
    rewrite Z.add_0_r in H0. unfold fld in H0. rewrite w1_bytes_small in H0 by lia. exact H0.
  - replace (Z_to_bv 64 d + nat_to_word 1)%bv with (Z_to_bv 64 (d + 1)).
    2:{ apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
        change (Z.of_nat 1) with 1. rewrite <- Zplus_mod. reflexivity. }
    apply IH; [lia | lia |].
    intros i Hi. specialize (HF (i + 1) ltac:(lia)).
    replace (d + (i + 1)) with (d + 1 + i) in HF by lia.
    unfold Znth in *. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) in HF by lia. cbn [nth] in HF. exact HF.
Qed.

Lemma rdn_str_fld : forall M d cs,
  0 <= d -> d + Zlen cs < 2 ^ 64 ->
  (forall i, 0 <= i < Zlen cs -> 0 <= Znth i cs < 256) ->
  rdn SEGS M (Z_to_bv 64 d) (length cs) = Some (str_bytes cs) ->
  forall i, 0 <= i < Zlen cs -> fld SEGS M (d + i) 1 (Znth i cs).
Proof using SEGS.
  intros M d cs. revert d. induction cs as [|c cs IH]; intros d Hd Hn HR HRD i Hi.
  - unfold Zlen in Hi. cbn in Hi. lia.
  - unfold Zlen in *. cbn [length str_bytes map] in *.
    pose proof (SeqExec.rdn_firstn SEGS M _ (Z_to_bv 64 d) _ 1 HRD ltac:(lia)) as H1.
    pose proof (SeqExec.rdn_skipn SEGS M _ (Z_to_bv 64 d) _ 1 HRD ltac:(lia)) as H2.
    cbn [firstn skipn Nat.sub] in H1, H2.
    replace (Z_to_bv 64 d + nat_to_word 1)%bv with (Z_to_bv 64 (d + 1)) in H2.
    2:{ apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
        change (Z.of_nat 1) with 1. rewrite <- Zplus_mod. reflexivity. }
    replace (length cs - 0)%nat with (length cs) in H2 by lia.
    destruct (Z.eq_dec i 0) as [->|Hne].
    + destruct (HR 0 ltac:(lia)) as [H0a H0b]. unfold Znth in *. cbn [Z.to_nat nth] in *.
      unfold fld. rewrite Z.add_0_r. rewrite w1_bytes_small by lia. exact H1.
    + fold (str_bytes cs) in H2.
      specialize (IH (d + 1) ltac:(lia) ltac:(lia)).
      assert (HR' : forall i, 0 <= i < Z.of_nat (length cs) -> 0 <= Znth i cs < 256).
      { intros j Hj. specialize (HR (j + 1) ltac:(lia)). unfold Znth in *.
        replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) in HR by lia. cbn [nth] in HR. exact HR. }
      specialize (IH HR' H2 (i - 1) ltac:(lia)).
      replace (d + 1 + (i - 1)) with (d + i) in IH by lia.
      unfold Znth in *. replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia. cbn [nth]. exact IH.
Qed.

End SB.

Lemma land_1_mod : forall a, 0 <= a -> Z.land a 1 = a mod 2.
Proof. intros a Ha. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma land_m2_64 : forall a, 0 <= a < 2 ^ 64 -> Z.land a (2 ^ 64 - 2) = a - a mod 2.
Proof.
  intros a Ha.
  change (2 ^ 64 - 2) with (Z.land (Z.lnot 1) (Z.ones 64)).
  rewrite Z.land_assoc, Z.land_ones by lia. rewrite <- Z.ldiff_land.
  change 1 with (Z.ones 1) at 1. rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
  rewrite Z.mod_small; [| split; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia |]].
  - pose proof (Z.div_mod a 2 ltac:(lia)). lia.
  - pose proof (Z.div_mod a 2 ltac:(lia)). pose proof (Z.mod_pos_bound a 2 ltac:(lia)). lia.
Qed.

Lemma lor_disjoint : forall a b, Z.land a b = 0 -> Z.lor a b = a + b.
Proof. intros a b H. rewrite <- Z.lxor_lor by exact H. symmetry. apply Z.add_nocarry_lxor. exact H. Qed.

Lemma land_8m_low : forall m r, 0 <= m -> 0 <= r < 8 -> Z.land (8 * m) r = 0.
Proof.
  intros m r Hm Hr.
  assert (H7 : Z.land (8 * m) 7 = 0).
  { change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
    rewrite Z.mul_comm. apply Z_mod_mult. }
  assert (Hr7 : Z.land 7 r = r).
  { rewrite Z.land_comm. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 3) with 8. lia. }
  rewrite <- Hr7. rewrite Z.land_assoc, H7. apply Z.land_0_l.
Qed.

Lemma lor_8m6_7 : forall m, 0 <= m -> Z.lor (8 * m + 6) 7 = 8 * m + 7.
Proof.
  intros m Hm.
  rewrite <- (lor_disjoint (8 * m) 6) by (apply land_8m_low; lia).
  rewrite <- Z.lor_assoc. change (Z.lor 6 7) with 7.
  apply lor_disjoint. apply land_8m_low; lia.
Qed.

Lemma str_grow_arith : forall asz, 8 <= asz -> asz mod 8 = 0 -> Z.lor (2 * (asz - 1)) 7 = 2 * asz - 1.
Proof.
  intros asz H8 Hm. pose proof (Z.div_mod asz 8 ltac:(lia)) as Hd.
  set (k := asz / 8) in *.
  replace (2 * (asz - 1)) with (8 * (2 * k - 1) + 6) by lia.
  rewrite lor_8m6_7 by lia. lia.
Qed.

Lemma lor_even_1 : forall a, 0 <= a -> a mod 2 = 0 -> Z.lor a 1 = a + 1.
Proof. intros a Ha He. apply lor_disjoint. rewrite land_1_mod by lia. exact He. Qed.

Lemma odd_byte0 : forall asz, 0 <= asz -> asz mod 8 = 0 -> Z.land ((asz + 1) mod 256) 1 = 1.
Proof.
  intros asz H Hm. rewrite land_1_mod by (apply Z.mod_pos_bound; lia).
  pose proof (Z.div_mod asz 8 ltac:(lia)) as Hd. set (k := asz / 8) in *.
  pose proof (Z.div_mod (asz + 1) 256 ltac:(lia)) as Hd2. pose proof (Z.mod_pos_bound (asz + 1) 256 ltac:(lia)).
  set (r := (asz + 1) mod 256) in *. set (q := (asz + 1) / 256) in *.
  assert (Hr : r = 2 * (4 * k - 128 * q) + 1) by lia. rewrite Hr.
  rewrite Z.add_comm, Z.mul_comm, Z_mod_plus_full. reflexivity.
Qed.

Lemma even_land_1 : forall n, 0 <= n -> Z.land (2 * n) 1 = 0.
Proof. intros n Hn. rewrite land_1_mod by lia. rewrite Z.mul_comm. apply Z_mod_mult. Qed.

Lemma Znth_firstn : forall i n xs, 0 <= i < n -> Znth i (firstn (Z.to_nat n) xs) = Znth i xs.
Proof.
  intros i n xs Hi. unfold Znth.
  assert (Hk : (Z.to_nat i < Z.to_nat n)%nat) by lia. revert Hk. generalize (Z.to_nat n) as N. generalize (Z.to_nat i) as k.
  intros k N Hk. revert k N Hk. induction xs as [|x xs IH]; intros k N Hk.
  - rewrite firstn_nil. reflexivity.
  - destruct N as [|N]; [lia|]. cbn [firstn]. destruct k as [|k]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.

Lemma Znth_app_r : forall i xs ys, Zlen xs <= i -> Znth i (xs ++ ys) = Znth (i - Zlen xs) ys.
Proof.
  intros i xs ys Hi. unfold Znth, Zlen in *. rewrite app_nth2 by lia. f_equal. lia.
Qed.

Lemma Zlen_app : forall {T} (xs ys : list T), Zlen (xs ++ ys) = Zlen xs + Zlen ys.
Proof. intros. unfold Zlen. rewrite length_app. lia. Qed.

Lemma land_low_high8 : forall a m, 0 <= a < 256 -> 0 <= m -> Z.land a (m * 2 ^ 8) = 0.
Proof.
  intros a m Ha Hm. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8).
  - rewrite <- Z.shiftl_mul_pow2, Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
  - rewrite (Z_testbit_high 8 a i) by lia. reflexivity.
Qed.

Lemma bytes_le_to_Z_cons : forall (b : byte) rest,
  bytes_le_to_Z (b :: rest) = bv_unsigned b + 256 * bytes_le_to_Z rest.
Proof.
  intros b rest. cbn [bytes_le_to_Z]. rewrite Z.shiftl_mul_pow2 by lia.
  pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256 in Hb.
  pose proof (bytes_le_to_Z_nonneg rest).
  rewrite lor_disjoint by (apply land_low_high8; lia). change (2 ^ 8) with 256. lia.
Qed.

Lemma lez8_val : forall bs, length bs = 8%nat -> bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bs)).
Proof.
  intros bs Hl. pose proof (bytes_le_to_Z_bound bs) as Hb. rewrite Hl in Hb.
  pose proof (bytes_le_to_Z_nonneg bs). rewrite u64_of_Z; [reflexivity|]. cbn in Hb. lia.
Qed.

Lemma shl56_low_byte : forall b x, 0 <= b -> 0 <= x ->
  Z_to_bv 64 ((b + 256 * x) * 2 ^ 56) = Z_to_bv 64 (b * 2 ^ 56).
Proof.
  intros b x Hb Hx. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  replace ((b + 256 * x) * 2 ^ 56) with (b * 2 ^ 56 + x * 2 ^ 64) by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma rdn_repeat_sub : forall segs M (b : byte) (p : Z) (N : nat) (d : Z) (k : nat),
  0 <= p -> p + Z.of_nat N < 2 ^ 64 -> 0 <= d -> d + Z.of_nat k <= Z.of_nat N ->
  rdn segs (wbytes M (Z_to_bv 64 p) (repeat b N)) (Z_to_bv 64 (p + d)) k = Some (repeat b k).
Proof.
  intros segs M b p N d k Hp HN Hd Hk.
  pose proof (RefReadLib.rdn_wbytes_self segs M (Z_to_bv 64 p) (repeat b N)) as H.
  rewrite repeat_length in H. specialize (H ltac:(rewrite u64_of_Z by lia; lia)).
  pose proof (rdn_sub segs _ N (Z_to_bv 64 p) _ (Z.to_nat d) k H ltac:(lia)) as H2.
  unfold Hoare.at_ in H2. rewrite u64_of_Z in H2 by lia. replace (p + Z.of_nat (Z.to_nat d)) with (p + d) in H2 by lia.
  rewrite H2. unfold sub. rewrite skipn_repeat', firstn_repeat' by lia. reflexivity.
Qed.

Section Bytes.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma land_255 : forall x, 0 <= x -> Z.land x 255 = x mod 256.
Proof. intros x Hx. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma land_byte_shifted : forall x s, 0 <= x -> 0 <= s ->
  Z.land x (Z.shiftl (Z.ones 8) s) = 2 ^ s * ((x / 2 ^ s) mod 2 ^ 8).
Proof.
  intros x s Hx Hs.
  apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec.
  replace (2 ^ s * ((x / 2 ^ s) mod 2 ^ 8)) with (Z.shiftl ((x / 2 ^ s) mod 2 ^ 8) s)
    by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  destruct (Z.lt_ge_cases k s) as [Hl|Hg].
  - rewrite !Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
  - rewrite !Z.shiftl_spec_high by lia.
    destruct (Z.lt_ge_cases (k - s) 8) as [Hl8|Hg8].
    + rewrite Z.ones_spec_low, Bool.andb_true_r by lia.
      rewrite <- Z.land_ones by lia. rewrite Z.land_spec, Z.ones_spec_low, Bool.andb_true_r by lia.
      rewrite !Z.div_pow2_bits by lia. f_equal. lia.
    + rewrite Z.ones_spec_high, Bool.andb_false_r by lia.
      rewrite <- Z.land_ones by lia. rewrite Z.land_spec, Z.ones_spec_high, Bool.andb_false_r by lia. reflexivity.
Qed.

Lemma land_ff00 : forall x, 0 <= x -> Z.land x 65280 = 256 * ((x / 256) mod 256).
Proof. intros x Hx. change 65280 with (Z.shiftl (Z.ones 8) 8). rewrite land_byte_shifted by lia. reflexivity. Qed.

Lemma land_ff0000 : forall x, 0 <= x -> Z.land x 16711680 = 65536 * ((x / 256 / 256) mod 256).
Proof.
  intros x Hx. change 16711680 with (Z.shiftl (Z.ones 8) 16). rewrite land_byte_shifted by lia.
  rewrite Zdiv_Zdiv by lia. reflexivity.
Qed.

Lemma shl_mod64 : forall x s, 0 <= x -> 0 <= s <= 64 ->
  Z_to_bv 64 (x * 2 ^ s) = Z_to_bv 64 ((x mod 2 ^ (64 - s)) * 2 ^ s).
Proof.
  intros x s Hx Hs. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.div_mod x (2 ^ (64 - s))) at 1 by lia.
  rewrite Z.mul_add_distr_r.
  replace (2 ^ (64 - s) * (x / 2 ^ (64 - s)) * 2 ^ s) with ((x / 2 ^ (64 - s)) * 2 ^ 64).
  2:{ replace (2 ^ 64) with (2 ^ (64 - s) * 2 ^ s) by (rewrite <- Z.pow_add_r by lia; f_equal; lia). lia. }
  rewrite Z.add_comm, Z_mod_plus_full. reflexivity.
Qed.

Lemma byte1_via_shifts : forall x, 0 <= x < 2 ^ 32 -> (x mod 2 ^ 16) * 2 ^ 48 / 2 ^ 56 = (x / 256) mod 256.
Proof.
  intros x Hx. change (2 ^ 56) with (2 ^ 48 * 2 ^ 8). rewrite <- Zdiv_Zdiv by lia. rewrite Z.div_mul by lia.
  change (2 ^ 16) with (256 * 256). change (2 ^ 8) with 256. rewrite Z.rem_mul_r by lia.
  rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma byte2_via_shifts : forall x, 0 <= x < 2 ^ 32 -> (x mod 2 ^ 24) * 2 ^ 40 / 2 ^ 56 = (x / 256 / 256) mod 256.
Proof.
  intros x Hx. change (2 ^ 56) with (2 ^ 40 * 2 ^ 16). rewrite <- Zdiv_Zdiv by lia. rewrite Z.div_mul by lia.
  rewrite Zdiv_Zdiv by lia. change (256 * 256) with 65536.
  change (2 ^ 24) with (65536 * 256). change (2 ^ 16) with 65536. rewrite Z.rem_mul_r by lia.
  rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma byte3_val : forall x, 0 <= x < 2 ^ 32 -> x / 2 ^ 24 = (x / 256 / 256 / 256) mod 256.
Proof.
  intros x Hx. rewrite !Zdiv_Zdiv by lia. change (256 * 256 * 256) with (2 ^ 24).
  rewrite Z.mod_small; [reflexivity|]. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.

End Bytes.

From Stdlib Require Import Permutation.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma count_class_f_app : forall cls big l1 l2 c,
  count_class_f cls big (l1 ++ l2) c = count_class_f cls big l1 c + count_class_f cls big l2 c.
Proof. intros cls big l1 l2 c. induction l1 as [|[q k] l1 IH]; [reflexivity|]. cbn [count_class_f app]. rewrite IH. lia. Qed.

Lemma big_bytes_f_app : forall rb big l1 l2,
  big_bytes_f rb big (l1 ++ l2) = big_bytes_f rb big l1 + big_bytes_f rb big l2.
Proof. intros rb big l1 l2. induction l1 as [|[q k] l1 IH]; [reflexivity|]. cbn [big_bytes_f app]. rewrite IH. lia. Qed.

Lemma count_class_f_perm : forall cls big l1 l2 c,
  Permutation l1 l2 -> count_class_f cls big l1 c = count_class_f cls big l2 c.
Proof.
  intros cls big l1 l2 c HP. induction HP as [| [q k] l1 l2 HP IH | [q k] [q' k'] l | l1 l2 l3 H1 IH1 H2 IH2].
  - reflexivity.
  - cbn [count_class_f]. rewrite IH. reflexivity.
  - cbn [count_class_f]. lia.
  - lia.
Qed.

Lemma big_bytes_f_perm : forall rb big l1 l2,
  Permutation l1 l2 -> big_bytes_f rb big l1 = big_bytes_f rb big l2.
Proof.
  intros rb big l1 l2 HP. induction HP as [| [q k] l1 l2 HP IH | [q k] [q' k'] l | l1 l2 l3 H1 IH1 H2 IH2].
  - reflexivity.
  - cbn [big_bytes_f]. rewrite IH. reflexivity.
  - cbn [big_bytes_f]. lia.
  - lia.
Qed.
