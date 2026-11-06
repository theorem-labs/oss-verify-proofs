(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit HasZero.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Str.
Variable SEGS : list Segment.

(* [comment removed for export] *)
Definition bytes_at (M : mem) (p N : Z) (B : Z -> byte) : Prop :=
  forall i, 0 <= i < N -> M (W (p + i)) = Some (B i).

Lemma bytes_at_unch : forall M0 M (P : word -> Prop) p N B,
  unch M0 M P -> 0 <= p -> p + N < 2 ^ 64 -> (forall x, inr x p N -> ~ P x) ->
  bytes_at M0 p N B -> bytes_at M p N B.
Proof.
  intros M0 M P p N B H Hp HN HP Hb i Hi. rewrite H; [apply Hb, Hi|].
  apply HP. unfold inr. rewrite Wu by lia. lia.
Qed.

Lemma bytes_at_rd_ok : forall M p N B, bytes_at M p N B -> rd_ok M p N.
Proof. intros M p N B H i Hi. rewrite (H i Hi). discriminate. Qed.

Lemma W_succ : forall a, (W a + 1)%bv = W (a + 1).
Proof.
  intros a. apply bv_eq. rewrite bv_add_unsigned. change (bv_unsigned (1 : word)) with 1.
  rewrite !Wu_mod. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdn_bytes_at : forall M p N B (n : nat) i,
  bytes_at M p N B -> 0 <= i -> i + Z.of_nat n <= N ->
  rdn SEGS M (W (p + i)) n = Some (map (fun j => B (i + Z.of_nat j)) (seq 0 n)).
Proof.
  intros M p N B n. induction n as [|n IH]; intros i H Hi Hn; [reflexivity|].
  cbn [rdn]. rewrite (H i) by lia. rewrite W_succ.
  replace (p + i + 1) with (p + (i + 1)) by lia.
  rewrite IH by (try assumption; lia).
  cbn [seq map]. rewrite Z.add_0_r. do 2 f_equal.
  rewrite <- seq_shift, map_map. apply map_ext. intros j. f_equal. lia.
Qed.

Lemma bytes_le_V : forall bs, bytes_le_to_Z bs = V (map bv_unsigned bs).
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [bytes_le_to_Z map V]. rewrite <- IH.
  pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
  pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite <- Z.add_nocarry_lor; [lia|].
  apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases k 8).
  - replace (bytes_le_to_Z bs * 256) with (bytes_le_to_Z bs * 2 ^ 8) by reflexivity.
    rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
  - assert (Z.testbit (bv_unsigned b) k = false) as ->; [|reflexivity].
    destruct (Z.eq_dec (bv_unsigned b) 0) as [->|]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 8; [|lia].
    apply Z.log2_lt_pow2; [lia|]. change (2 ^ 8) with 256. lia.
Qed.

(* [comment removed for export] *)
Definition bl8 (B : Z -> byte) (i : Z) : list Z :=
  map (fun j => bv_unsigned (B (i + Z.of_nat j))) (seq 0 8).

Lemma bl8_ok : forall B i, bytes_ok (bl8 B i).
Proof.
  intros B i. unfold bl8, bytes_ok. apply Forall_forall. intros x Hx.
  apply in_map_iff in Hx as (j & <- & _).
  pose proof (bv_unsigned_in_range 8 (B (i + Z.of_nat j))) as H. change (bv_modulus 8) with 256 in H. exact H.
Qed.

Lemma bl8_len : forall B i, length (bl8 B i) = 8%nat.
Proof. reflexivity. Qed.

Lemma V_bl8_range : forall B i, 0 <= V (bl8 B i) < 2 ^ 64.
Proof.
  intros B i. pose proof (V_nonneg _ (bl8_ok B i)). pose proof (V_bound _ (bl8_ok B i)) as Hb.
  rewrite bl8_len in Hb. change (256 ^ Z.of_nat 8) with (2 ^ 64) in Hb. lia.
Qed.

Lemma load8_bytes_at : forall M p N B i,
  bytes_at M p N B -> 0 <= i -> i + 8 <= N ->
  load_ok SEGS M (W (p + i)) 8 (W (V (bl8 B i))).
Proof.
  intros M p N B i H Hi Hn.
  exists (map (fun j => B (i + Z.of_nat j)) (seq 0 8)). split.
  - apply (rdn_bytes_at M p N B 8 i H Hi). lia.
  - rewrite bytes_le_V, map_map. fold (bl8 B i). rewrite Wu by apply V_bl8_range. reflexivity.
Qed.

Lemma load1_bytes_at : forall M p N B i,
  bytes_at M p N B -> 0 <= i < N ->
  load_ok SEGS M (W (p + i)) 1 (W (bv_unsigned (B i))).
Proof.
  intros M p N B i H Hi. exists [B i]. split.
  - rewrite (rdn_bytes_at M p N B 1 i H) by lia. cbn [seq map]. rewrite Z.add_0_r. reflexivity.
  - rewrite bytes_le_1. pose proof (bv_unsigned_in_range 8 (B i)) as Hb. change (bv_modulus 8) with 256 in Hb.
    rewrite Wu by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma allnz_bl8 : forall B i, allnz (bl8 B i) = true ->
  forall j, 0 <= j < 8 -> bv_unsigned (B (i + j)) <> 0.
Proof.
  intros B i H j Hj. unfold bl8 in H. cbn [seq map allnz] in H.
  repeat (apply andb_prop in H; destruct H as [?H H]).
  repeat match goal with Hx : negb (_ =? 0) = true |- _ => apply negb_true_iff, Z.eqb_neq in Hx end.
  assert (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) as Hc by lia.
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; assumption.
Qed.

(* [comment removed for export] *)
Lemma hz_test : forall B i,
  Z.land (Z.lor ((0x0101010101010100 - V (bl8 B i)) mod 2 ^ 64) (V (bl8 B i) mod 2 ^ 64))
         (0x8080808080808080 mod 2 ^ 64) = 0x8080808080808080 mod 2 ^ 64 ->
  forall j, 0 <= j < 8 -> bv_unsigned (B (i + j)) <> 0.
Proof.
  intros B i H. apply allnz_bl8. apply (haszero_machine (bl8 B i) (bl8_ok B i) (bl8_len B i)).
  rewrite (Z.mod_small (V (bl8 B i))) in H by apply V_bl8_range. exact H.
Qed.

Lemma Forall_bl8 : forall (P : Z -> Prop) B i, Forall P (bl8 B i) ->
  forall j, 0 <= j < 8 -> P (bv_unsigned (B (i + j))).
Proof.
  intros P B i H j Hj. unfold bl8 in H. cbn [seq map] in H.
  repeat match goal with Hx : Forall _ (_ :: _) |- _ => inversion Hx; subst; clear Hx end.
  assert (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) as Hc by lia.
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; assumption.
Qed.

(* [comment removed for export] *)
Lemma hz_test_xor : forall B i c, 0 <= c < 256 ->
  Z.land (Z.lor ((0x0101010101010100 - Z.lxor (V (bl8 B i)) (c * 0x0101010101010101)) mod 2 ^ 64)
                (Z.lxor (V (bl8 B i)) (c * 0x0101010101010101)))
         0x8080808080808080 = 0x8080808080808080 ->
  forall j, 0 <= j < 8 -> bv_unsigned (B (i + j)) <> c.
Proof.
  intros B i c Hc H. apply (Forall_bl8 (fun b => b <> c)).
  apply (haszero_machine_xor (bl8 B i) c (bl8_ok B i) (bl8_len B i) Hc). exact H.
Qed.

(* [comment removed for export] *)
Lemma test_z_machine : forall B i,
  bv_unsigned (v_and (v_or (v_sub (W 0x0101010101010100) (W (V (bl8 B i)))) (W (V (bl8 B i))))
                     (W 0x8080808080808080)) = bv_unsigned (W 0x8080808080808080) ->
  forall j, 0 <= j < 8 -> bv_unsigned (B (i + j)) <> 0.
Proof.
  intros B i H. apply hz_test. rewrite sub_W, u_and, u_or, !Wu_mod in H. exact H.
Qed.

Lemma test_c_machine : forall B i c, 0 <= c < 256 ->
  bv_unsigned (v_and (v_or (v_sub (W 0x0101010101010100)
                                  (v_xor (W (V (bl8 B i))) (W (c * 0x0101010101010101))))
                           (v_xor (W (V (bl8 B i))) (W (c * 0x0101010101010101))))
                     (W 0x8080808080808080)) = bv_unsigned (W 0x8080808080808080) ->
  forall j, 0 <= j < 8 -> bv_unsigned (B (i + j)) <> c.
Proof.
  intros B i c Hc H. apply hz_test_xor; [exact Hc|].
  pose proof (V_bl8_range B i) as HV.
  assert (Hk : 0 <= c * 0x0101010101010101 < 2 ^ 64) by lia.
  pose proof (Z_lxor_range _ _ HV Hk) as HX.
  rewrite xor_W in H by assumption. rewrite sub_W, u_and, u_or in H.
  rewrite Wu_mod in H. rewrite (Wu (Z.lxor _ _)) in H by exact HX.
  rewrite (Wu 0x8080808080808080) in H by lia. exact H.
Qed.

End Str.
