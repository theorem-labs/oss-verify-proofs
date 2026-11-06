(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim StoreOk StreamSim BigLinkGlue L5Defs L5Core.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5B.
Section WithSegs.
Variable segs : list Segment.

Abbreviation byte_of M a := (match M a with Some b => Some b | None => seg_rom segs a end).

Lemma rdn_S M a n : rdn segs M a (S n) = match byte_of M a with Some b => match rdn segs M (a + 1)%bv n with Some r => Some (b :: r) | None => None end | None => None end.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rdn_split M : forall n m a bs, 0 <= a -> a + Z.of_nat (n + m) <= 2 ^ 64 ->
  rdn segs M (Z_to_bv 64 a) (n + m) = Some bs ->
  rdn segs M (Z_to_bv 64 a) n = Some (firstn n bs) /\ rdn segs M (Z_to_bv 64 (a + Z.of_nat n)) m = Some (skipn n bs).
Proof.
  induction n as [|n IH]; intros m a bs Ha Hn HR.
  - cbn [firstn skipn Nat.add] in *. rewrite Z.add_0_r. split. reflexivity. exact HR.
  - cbn [Nat.add] in HR. rewrite rdn_S in HR. rewrite rdn_S.
    destruct (byte_of M (Z_to_bv 64 a)) as [b|]; [|discriminate].
    rewrite (L5C.add1_lit a) in HR |- *.
    destruct (rdn segs M (Z_to_bv 64 (a + 1)) (n + m)) as [r|] eqn:ER; [|discriminate]. injection HR as <-.
    destruct (IH m (a + 1) r ltac:(lia) ltac:(lia) ER) as [H1 H2].
    rewrite H1. split. reflexivity. replace (a + Z.of_nat (S n)) with (a + 1 + Z.of_nat n) by lia. exact H2.
Qed.
Lemma rdn_join M : forall n m a bs1 bs2, 0 <= a -> a + Z.of_nat (n + m) <= 2 ^ 64 ->
  rdn segs M (Z_to_bv 64 a) n = Some bs1 -> rdn segs M (Z_to_bv 64 (a + Z.of_nat n)) m = Some bs2 ->
  rdn segs M (Z_to_bv 64 a) (n + m) = Some (bs1 ++ bs2).
Proof.
  induction n as [|n IH]; intros m a bs1 bs2 Ha Hn H1 H2.
  - cbn in H1. injection H1 as <-. rewrite Z.add_0_r in H2. exact H2.
  - rewrite rdn_S in H1. cbn [Nat.add]. rewrite rdn_S.
    destruct (byte_of M (Z_to_bv 64 a)) as [b|]; [|discriminate]. rewrite (L5C.add1_lit a) in H1 |- *.
    destruct (rdn segs M (Z_to_bv 64 (a + 1)) n) as [r|] eqn:ER; [|discriminate]. injection H1 as <-.
    rewrite (IH m (a + 1) r bs2 ltac:(lia) ltac:(lia) ER). reflexivity.
    replace (a + 1 + Z.of_nat n) with (a + Z.of_nat (S n)) by lia. exact H2.
Qed.

(* [comment removed for export] *)
Lemma Z_to_le_bytes_app n m z : Z_to_le_bytes (n + m) z = Z_to_le_bytes n z ++ Z_to_le_bytes m (Z.shiftr z (8 * Z.of_nat n)).
Proof.
  revert z. induction n as [|n IH]; intros z. cbn. rewrite Z.shiftr_0_r. reflexivity.
  cbn [Nat.add Z_to_le_bytes app]. f_equal. rewrite IH. f_equal. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.
Lemma word_to_le_bytes_app n m v : 0 <= v < 2 ^ 64 ->
  word_to_le_bytes (n + m) (Z_to_bv 64 v) = word_to_le_bytes n (Z_to_bv 64 v) ++ word_to_le_bytes m (Z_to_bv 64 (Z.shiftr v (8 * Z.of_nat n))).
Proof.
  intros Hv. unfold word_to_le_bytes. rewrite !BG.unsigned_lit. apply Z_to_le_bytes_app.
  split. apply Z.shiftr_nonneg. lia. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_lt_upper_bound. apply Z.pow_pos_nonneg; lia.
  eapply Z.lt_le_trans. apply (proj2 Hv). rewrite <- (Z.mul_1_l (2 ^ 64)) at 1. apply Z.mul_le_mono_nonneg_r. lia. pose proof (Z.pow_pos_nonneg 2 (8 * Z.of_nat n)); lia. lia.
Qed.

(* [comment removed for export] *)
Lemma uw_split (n m : nat) M a v : 0 <= a -> a + Z.of_nat (n + m) <= 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  rdn segs M (Z_to_bv 64 a) (n + m) = Some (word_to_le_bytes (n + m) (Z_to_bv 64 v)) ->
  rdn segs M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)) /\
  rdn segs M (Z_to_bv 64 (a + Z.of_nat n)) m = Some (word_to_le_bytes m (Z_to_bv 64 (Z.shiftr v (8 * Z.of_nat n)))).
Proof.
  intros Ha Hn Hv HR. destruct (rdn_split M n m a _ Ha Hn HR) as [H1 H2].
  rewrite (word_to_le_bytes_app n m v Hv) in H1, H2.
  assert (LN: length (word_to_le_bytes n (Z_to_bv 64 v)) = n) by (unfold word_to_le_bytes; apply length_Z_to_le_bytes).
  rewrite firstn_app, LN, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 in H1 by lia.
  rewrite skipn_app, LN, Nat.sub_diag, skipn_O, skipn_all2 in H2 by lia. cbn [app] in H2. split; assumption.
Qed.
Lemma uw_join (n m : nat) M a v : 0 <= a -> a + Z.of_nat (n + m) <= 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  rdn segs M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)) ->
  rdn segs M (Z_to_bv 64 (a + Z.of_nat n)) m = Some (word_to_le_bytes m (Z_to_bv 64 (Z.shiftr v (8 * Z.of_nat n)))) ->
  rdn segs M (Z_to_bv 64 a) (n + m) = Some (word_to_le_bytes (n + m) (Z_to_bv 64 v)).
Proof.
  intros Ha Hn Hv H1 H2. rewrite (word_to_le_bytes_app n m v Hv). apply rdn_join; assumption.
Qed.


(* [comment removed for export] *)
Lemma bytes_le_to_Z_bound (bs : list byte) : 0 <= bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
  induction bs as [|b r IH]. cbn. lia.
  cbn [bytes_le_to_Z length]. pose proof (bv_unsigned_in_range _ b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with 256 in Hb.
  rewrite Z.shiftl_mul_pow2 by lia.
  assert (LOR: Z.lor (bv_unsigned b) (bytes_le_to_Z r * 2 ^ 8) = bv_unsigned b + bytes_le_to_Z r * 2 ^ 8).
  { rewrite <- Z.lxor_lor. rewrite <- Z.add_nocarry_lxor. reflexivity.
    all: apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0;
         destruct (Z_lt_le_dec i 8) as [Hl|Hg]; [rewrite (Z.mul_pow2_bits_low _ 8 i) by lia; apply Bool.andb_false_r
                                               | rewrite (Z.bits_above_log2 (bv_unsigned b) i); [reflexivity| lia |
                                                 destruct (Z.eq_dec (bv_unsigned b) 0) as [->|NZ]; [cbn; lia| pose proof (Z.log2_lt_pow2 (bv_unsigned b) 8 ltac:(lia)); lia]]]. }
  rewrite LOR. replace (8 * Z.of_nat (S (length r))) with (8 + 8 * Z.of_nat (length r)) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256. nia.
Qed.

Lemma le_bytes_roundtrip (bs : list byte) : Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b r IH]. reflexivity.
  cbn [bytes_le_to_Z length Z_to_le_bytes]. pose proof (bv_unsigned_in_range _ b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with 256 in Hb.
  pose proof (bytes_le_to_Z_bound r) as Hr.
  rewrite Z.shiftl_mul_pow2 by lia.
  assert (LOR: Z.lor (bv_unsigned b) (bytes_le_to_Z r * 2 ^ 8) = bv_unsigned b + bytes_le_to_Z r * 2 ^ 8).
  { rewrite <- Z.lxor_lor. rewrite <- Z.add_nocarry_lxor. reflexivity.
    all: apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0;
         destruct (Z_lt_le_dec i 8) as [Hl|Hg]; [rewrite (Z.mul_pow2_bits_low _ 8 i) by lia; apply Bool.andb_false_r
                                               | rewrite (Z.bits_above_log2 (bv_unsigned b) i); [reflexivity| lia |
                                                 destruct (Z.eq_dec (bv_unsigned b) 0) as [->|NZ]; [cbn; lia| pose proof (Z.log2_lt_pow2 (bv_unsigned b) 8 ltac:(lia)); lia]]]. }
  rewrite LOR. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8). change (2 ^ 8) with 256.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. rewrite Z.div_add by lia.
    rewrite Z.div_small by lia. rewrite Z.add_0_l. exact IH.
Qed.

(* [comment removed for export] *)
Lemma rdn_len M : forall n a bs, rdn segs M a n = Some bs -> length bs = n.
Proof.
  induction n as [|n IH]; intros a bs HR. cbn in HR. injection HR as <-. reflexivity.
  rewrite rdn_S in HR. destruct (byte_of M a) as [b|]; [|discriminate]. destruct (rdn segs M (a + 1)%bv n) as [r|] eqn:ER; [|discriminate].
  injection HR as <-. cbn. f_equal. eapply IH. exact ER.
Qed.
Lemma rdn_word M a (n : nat) bs : 0 <= a -> (n <= 8)%nat ->
  rdn segs M (Z_to_bv 64 a) n = Some bs ->
  exists v, 0 <= v < 2 ^ (8 * Z.of_nat n) /\ rdn segs M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).
Proof.
  intros Ha Hn HR. exists (bytes_le_to_Z bs). pose proof (rdn_len M n _ bs HR) as LN. pose proof (bytes_le_to_Z_bound bs) as B. rewrite LN in B.
  split. exact B. rewrite HR. f_equal. unfold word_to_le_bytes. rewrite BG.unsigned_lit. rewrite <- LN. symmetry. apply le_bytes_roundtrip.
  split. lia. eapply Z.lt_le_trans. apply (proj2 B). apply Z.pow_le_mono_r. lia. lia.
Qed.
(* [comment removed for export] *)
Lemma rdn_some M : forall n a, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> byte_of M (Z_to_bv 64 (a + i)) <> None) -> exists bs, rdn segs M (Z_to_bv 64 a) n = Some bs.
Proof.
  induction n as [|n IH]; intros a Ha Hn HB. exists []. reflexivity.
  rewrite rdn_S. pose proof (HB 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
  destruct (byte_of M (Z_to_bv 64 a)) as [b|]; [|exfalso; apply H0; reflexivity].
  rewrite (L5C.add1_lit a). destruct (IH (a + 1) ltac:(lia) ltac:(lia)) as [r Hr]. { intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply HB. lia. }
  rewrite Hr. eexists. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma u64_of_defined M a : 0 <= a -> a + 8 <= 2 ^ 64 -> L5.defined M a 8 -> exists v, 0 <= v < 2 ^ 64 /\ L5.u64_at segs M a v.
Proof.
  intros Ha Hn D. destruct (rdn_some M 8 a Ha ltac:(cbn; lia)) as [bs Hbs].
  { intros i Hi. pose proof (D i ltac:(cbn in Hi; lia)) as Di. destruct (M (Z_to_bv 64 (a + i))); [discriminate| exfalso; apply Di; reflexivity]. }
  destruct (rdn_word M a 8 bs Ha ltac:(lia) Hbs) as (v & Hv & HR). exists v. split. cbn in Hv. lia. exact HR.
Qed.
(* [comment removed for export] *)
Definition rom_ok (a : Z) (n : nat) : bool :=
  forallb (fun i => match seg_rom segs (Z_to_bv 64 (a + Z.of_nat i)) with Some _ => true | None => false end) (seq 0 n).
Lemma rom_ok_bytes a n M : rom_ok a n = true -> forall i, 0 <= i < Z.of_nat n -> byte_of M (Z_to_bv 64 (a + i)) <> None.
Proof.
  intros H i Hi. unfold rom_ok in H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat i) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
  destruct (M (Z_to_bv 64 (a + i))). discriminate. destruct (seg_rom segs (Z_to_bv 64 (a + i))). discriminate. discriminate H.
Qed.
Lemma u32_of_rom M a : rom_ok a 4 = true -> 0 <= a -> a + 4 <= 2 ^ 64 -> exists v, 0 <= v < 2 ^ 32 /\ L5.u32_at segs M a v.
Proof.
  intros H Ha Hn. destruct (rdn_some M 4 a Ha ltac:(cbn; lia) (rom_ok_bytes a 4 M H)) as [bs Hbs].
  destruct (rdn_word M a 4 bs Ha ltac:(lia) Hbs) as (v & Hv & HR). exists v. split. cbn in Hv. lia. exact HR.
Qed.
Lemma u64_of_rom M a : rom_ok a 8 = true -> 0 <= a -> a + 8 <= 2 ^ 64 -> exists v, 0 <= v < 2 ^ 64 /\ L5.u64_at segs M a v.
Proof.
  intros H Ha Hn. destruct (rdn_some M 8 a Ha ltac:(cbn; lia) (rom_ok_bytes a 8 M H)) as [bs Hbs].
  destruct (rdn_word M a 8 bs Ha ltac:(lia) Hbs) as (v & Hv & HR). exists v. split. cbn in Hv. lia. exact HR.
Qed.

(* [comment removed for export] *)
Definition byte_k (v : Z) (k : Z) : Z := (Z.shiftr v (8 * k)) mod 256.
Lemma u8_of_u64 M a v (k : nat) : 0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 -> (k < 8)%nat ->
  L5.u64_at segs M a v -> L5.u8_at segs M (a + Z.of_nat k) (byte_k v (Z.of_nat k)).
Proof.
  intros Ha Hn Hv Hk HU. unfold L5.u64_at in HU.
  replace 8%nat with (k + (1 + (7 - k)))%nat in HU by lia.
  destruct (uw_split k (1 + (7 - k)) M a v Ha ltac:(lia) Hv HU) as [_ H2].
  destruct (uw_split 1 (7 - k) M (a + Z.of_nat k) (Z.shiftr v (8 * Z.of_nat k)) ltac:(lia) ltac:(lia)) as [H3 _].
  { split. apply Z.shiftr_nonneg. lia. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_lt_upper_bound. apply Z.pow_pos_nonneg; lia.
    eapply Z.lt_le_trans. apply (proj2 Hv). rewrite <- (Z.mul_1_l (2 ^ 64)) at 1. apply Z.mul_le_mono_nonneg_r. lia. pose proof (Z.pow_pos_nonneg 2 (8 * Z.of_nat k)); lia. }
  exact H2.
  unfold L5.u8_at. rewrite H3. f_equal. unfold word_to_le_bytes. rewrite BG.unsigned_lit. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap, byte_k. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
  split. apply Z.shiftr_nonneg. lia. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_lt_upper_bound. apply Z.pow_pos_nonneg; lia.
  eapply Z.lt_le_trans. apply (proj2 Hv). rewrite <- (Z.mul_1_l (2 ^ 64)) at 1. apply Z.mul_le_mono_nonneg_r. lia. pose proof (Z.pow_pos_nonneg 2 (8 * Z.of_nat k)); lia.
Qed.
End WithSegs.

(* [comment removed for export] *)
Lemma list_bv_eq (l1 l2 : list byte) : map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  revert l2. induction l1 as [|b l1 IH]; intros [|c l2] H; cbn in H; try discriminate. reflexivity.
  injection H as Hb Hl. f_equal. apply bv_eq. exact Hb. apply IH. exact Hl.
Qed.

End L5B.
