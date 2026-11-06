(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import PropExec CatExec SeqExec StepTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Lemma Z_to_le_bytes_of_bytes : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bytes_le_to_Z_nonneg bs) as Hn. pose proof (u8_range b) as Hb.
  assert (Hs : Z.shiftr (Z.lor (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) 8 = bytes_le_to_Z bs).
  { rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
    rewrite (Z.shiftr_eq_0 (bv_unsigned b) 8); [apply Z.lor_0_l | lia |].
    destruct (Z.eq_dec (bv_unsigned b) 0) as [-> | Hne]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
  rewrite Hs, IH. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8)%Z with (2 ^ 8)%Z.
  rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.lor_spec, Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec i 8).
  - rewrite Z.shiftl_spec_low by lia. rewrite Bool.orb_false_r, Bool.andb_true_r. reflexivity.
  - rewrite Bool.andb_false_r. symmetry. apply (Z_testbit_high 8 (bv_unsigned b) i); lia.
Qed.

(* [comment removed for export] *)
Lemma bytes_le_to_Z_small64 : forall bs, (length bs <= 8)%nat ->
  bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bs)).
Proof.
  intros bs Hlen. pose proof (bytes_le_to_Z_nonneg bs). pose proof (bytes_le_to_Z_bound bs).
  assert (2 ^ (8 * Z.of_nat (length bs)) <= 2 ^ 64)%Z by (apply Z.pow_le_mono_r; lia).
  symmetry. apply u_Z2bv; lia.
Qed.

(* [comment removed for export] *)
Lemma w8_of_bytes : forall bs, length bs = 8%nat ->
  word_to_le_bytes 8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs Hlen. unfold word_to_le_bytes.
  rewrite <- (bytes_le_to_Z_small64 bs) by lia.
  rewrite <- Hlen. apply Z_to_le_bytes_of_bytes.
Qed.

Lemma bv_wrap_bv_swrap : forall n z, bv_wrap n (bv_swrap n z) = bv_wrap n z.
Proof.
  intros n z. unfold bv_swrap, bv_wrap.
  rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma w4_lw_of_bytes : forall bs, length bs = 4%nat ->
  word_to_le_bytes 4 (v_lw (Z_to_bv 64 (bytes_le_to_Z bs))) = bs.
Proof.
  intros bs Hlen. unfold word_to_le_bytes, v_lw.
  rewrite Z_to_bv_unsigned.
  rewrite (Z_to_le_bytes_wrap 4 64) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_wrap 4 32 (bv_swrap 32 _)) by (cbn; lia).
  rewrite bv_wrap_bv_swrap.
  rewrite (Z_to_le_bytes_wrap 4 32) by (cbn; lia).
  rewrite <- (bytes_le_to_Z_small64 bs) by lia.
  rewrite <- Hlen. apply Z_to_le_bytes_of_bytes.
Qed.

(* [comment removed for export] *)
Lemma rdn_guard8 : forall segs (D : word -> option byte) (a : Z) (lo hi : list byte) (z : byte),
  length lo = 4%nat -> length hi = 4%nat -> (0 <= a)%Z -> (a + 8 <= 2^64)%Z ->
  rdn segs (wbytes (wbytes (wbytes D (Z_to_bv 64 a) lo) (Z_to_bv 64 (a + 4)) hi) (Z_to_bv 64 (a + 1)) [z])
      (Z_to_bv 64 a) 8
  = Some (firstn 1 lo ++ [z] ++ skipn 2 lo ++ hi).
Proof.
  intros segs D a lo hi z Hlo Hhi Ha0 Ha8.
  set (m := wbytes (wbytes (wbytes D (Z_to_bv 64 a) lo) (Z_to_bv 64 (a + 4)) hi) (Z_to_bv 64 (a + 1)) [z]).
  assert (Hlo4 : rdn segs (wbytes D (Z_to_bv 64 a) lo) (Z_to_bv 64 a) 4 = Some lo).
  { rewrite <- Hlo. apply rdn_wbytes_hit. rewrite Hlo, u_Z2bv by lia. lia. }
  assert (H0 : rdn segs m (Z_to_bv 64 a) 1 = Some (firstn 1 lo)).
  { unfold m. rewrite (rdn_wbytes_out segs [z]) by (cbn [length]; rewrite ?Hhi, ?Hlo; rewrite ?u_Z2bv by lia; lia).
    rewrite (rdn_wbytes_out segs hi) by (cbn [length]; rewrite ?Hhi, ?Hlo; rewrite ?u_Z2bv by lia; lia).
    eapply rdn_firstn; [exact Hlo4 | lia]. }
  assert (H1 : rdn segs m (Z_to_bv 64 (a + 1)) 1 = Some [z]).
  { unfold m. apply (rdn_wbytes_hit segs [z]). cbn [length]. rewrite u_Z2bv by lia. lia. }
  assert (H2 : rdn segs m (Z_to_bv 64 (a + 2)) 2 = Some (skipn 2 lo)).
  { unfold m. rewrite (rdn_wbytes_out segs [z]) by (cbn [length]; rewrite ?Hhi, ?Hlo; rewrite ?u_Z2bv by lia; lia).
    rewrite (rdn_wbytes_out segs hi) by (cbn [length]; rewrite ?Hhi, ?Hlo; rewrite ?u_Z2bv by lia; lia).
    replace (Z_to_bv 64 (a + 2)) with (Z_to_bv 64 a + nat_to_word 2)
      by (rewrite word_add_nat, (u_Z2bv a) by lia; f_equal; lia).
    replace 2%nat with (4 - 2)%nat at 2 by reflexivity.
    eapply rdn_skipn; [exact Hlo4 | lia]. }
  assert (H4 : rdn segs m (Z_to_bv 64 (a + 4)) 4 = Some hi).
  { unfold m. rewrite (rdn_wbytes_out segs [z]) by (cbn [length]; rewrite ?Hhi, ?Hlo; rewrite ?u_Z2bv by lia; lia).
    rewrite <- Hhi. apply rdn_wbytes_hit. rewrite Hhi, u_Z2bv by lia. lia. }
  change 8%nat with (1 + (1 + (2 + 4)))%nat.
  apply rdn_app; [exact H0|].
  rewrite word_add_nat, u_Z2bv by lia. replace (a + Z.of_nat 1)%Z with (a + 1)%Z by lia.
  apply rdn_app; [exact H1|].
  rewrite word_add_nat, u_Z2bv by lia. replace (a + 1 + Z.of_nat 1)%Z with (a + 2)%Z by lia.
  apply rdn_app; [exact H2|].
  rewrite word_add_nat, u_Z2bv by lia. replace (a + 2 + Z.of_nat 2)%Z with (a + 4)%Z by lia.
  exact H4.
Qed.
