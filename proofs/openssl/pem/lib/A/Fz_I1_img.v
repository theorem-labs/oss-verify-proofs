(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface I_ut.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition img_okb (a : Z) : bool := match seg_rom asegs (wa a) with Some _ => true | None => false end.
Fixpoint rng_okb (n : nat) (a : Z) : bool := match n with O => true | S n' => img_okb a && rng_okb n' (a + 1) end.

Lemma rng_okb_spec : forall n a, rng_okb n a = true -> forall x, a <= x < a + Z.of_nat n -> img_okb x = true.
Proof.
  induction n as [|n IH]; intros a H x Hx; [lia|]. cbn [rng_okb] in H. apply andb_prop in H. destruct H as [H1 H2].
  destruct (Z.eq_dec x a) as [->|NE]; [exact H1|]. apply (IH (a + 1) H2). lia.
Qed.

(* [comment removed for export] *)
Lemma ut_img_ok : rng_okb (Z.to_nat (IMG_UT_HI - IMG_UT_LO)) IMG_UT_LO = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma ut_img_byte : forall a, IMG_UT_LO <= a < IMG_UT_HI -> exists b, seg_rom asegs (wa a) = Some b.
Proof.
  intros a Ha. pose proof (rng_okb_spec _ _ ut_img_ok a ltac:(rewrite Z2Nat.id by (unfold IMG_UT_LO, IMG_UT_HI; lia); lia)) as H.
  unfold img_okb in H. destruct (seg_rom asegs (wa a)) as [b|]; [exists b; reflexivity| discriminate].
Qed.

(* [comment removed for export] *)
Lemma ut_bytes_any : forall (m : mem) (n : nat) a, img_untouched m -> IMG_UT_LO <= a -> a + Z.of_nat n <= IMG_UT_HI ->
  exists bs, length bs = n /\ bytes_at asegs m a bs.
Proof.
  intros m n. induction n as [|n IH]; intros a U LO HI.
  - exists []. split; [reflexivity|]. split; [unfold IMG_UT_LO in *; lia|]. split; [unfold IMG_UT_HI in *; cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (ut_img_byte a ltac:(lia)) as (b & Hb).
    destruct (IH (a + 1) U ltac:(lia) ltac:(lia)) as (bs & L & (B0 & B1 & B2)).
    exists (b :: bs). split; [cbn; lia|]. split; [unfold IMG_UT_LO in *; lia|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i].
    + cbn [nth_error]. rewrite Z.add_0_r. unfold mrd. rewrite (U (wa a)); [exact Hb|].
      unfold wa. rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); unfold IMG_UT_LO, IMG_UT_HI in *; lia). lia.
    + cbn [nth_error]. replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. apply B2. cbn [length] in Hi. lia.
Qed.

(* [comment removed for export] *)
Lemma img_ble_range : forall bs : list byte, 0 <= bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [cbn; lia|].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with (2 ^ 8) in Hb.
  assert (Hs : 0 <= Z.shiftl (bytes_le_to_Z bs) 8) by (apply Z.shiftl_nonneg; lia).
  split. { apply Z.lor_nonneg. lia. }
  pose proof (Z.add_lor_land (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as E.
  pose proof (Z.land_nonneg (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as L.
  rewrite Z.shiftl_mul_pow2 in * by lia.
  replace (2 ^ (8 * Z.of_nat (S (length bs)))) with (2 ^ 8 * 2 ^ (8 * Z.of_nat (length bs))).
  2:{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  nia.
Qed.
Lemma img_le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (img_ble_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.

Lemma ut_ro_C8_any : forall (m : mem) a, img_untouched m -> IMG_UT_LO <= a -> a + 8 <= IMG_UT_HI -> exists v : word, ro_cells asegs m a [C8 v].
Proof.
  intros m a U LO HI. destruct (ut_bytes_any m 8 a U LO ltac:(cbn; lia)) as (bs & L & B).
  exists (le_bytes_to_word bs). split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
  rewrite img_le8_of_bytes by exact L. exact B.
Qed.
