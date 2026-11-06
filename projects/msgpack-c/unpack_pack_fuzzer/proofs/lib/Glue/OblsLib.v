(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val State Notation ValProofs.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val St ValP.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module OL.

Lemma u64_range : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range _ w). unfold bv_modulus in H. exact H. Qed.

Lemma Z_to_bv64_unsigned : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz. Qed.

Lemma wp_ok : forall i, w2Z (wp i) = to_Z i.
Proof. intros i. unfold w2Z. cbn [wt wl wp]. lia. Qed.

Lemma den_lit : forall E i, bv_unsigned (den E (VL (wp i))) = to_Z i.
Proof. intros E i. cbn [den]. rewrite wbv_unsigned. apply wp_ok. Qed.

Lemma den_VP : forall E k i, bv_unsigned (den E (VP k (wp i))) = (bv_unsigned (ev E k) + to_Z i) mod 2 ^ 64.
Proof. intros E k i. cbn [den]. rewrite bv_add_unsigned, wbv_unsigned, wp_ok. reflexivity. Qed.

Lemma den_add : forall E a b, bv_unsigned (den E (VAlu ALU_ADD a b)) = (bv_unsigned (den E a) + bv_unsigned (den E b)) mod 2 ^ 64.
Proof. intros. cbn [den alu64 alu]. rewrite bv_add_unsigned. reflexivity. Qed.

Lemma den_sub : forall E a b, bv_unsigned (den E (VAlu ALU_SUB a b)) = (bv_unsigned (den E a) - bv_unsigned (den E b)) mod 2 ^ 64.
Proof. intros. cbn [den alu64 alu]. rewrite bv_sub_unsigned. reflexivity. Qed.

Lemma bytes_val_le8 : forall z, 0 <= z < 2 ^ 64 ->
  bytes_val false 8 (blob_bytes (Z_to_le_bytes 8 z) 0 8) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold bytes_val, blob_bytes. change (Z.to_nat 8) with 8%nat. change (Z.to_nat 0) with 0%nat.
  rewrite skipn_O. rewrite firstn_all2 by (rewrite (length_Z_to_le_bytes 8%nat z); lia).
  rewrite bytes_le_to_Z_of_le_bytes by lia.
  change (8 * Z.of_nat 8) with 64. rewrite Z.mod_small by lia.
  rewrite ext_Z_id64; [reflexivity|]. unfold two64. lia.
Qed.

Lemma den_param8 : forall E j z, eb E j = Z_to_le_bytes 8 z -> 0 <= z < 2 ^ 64 ->
  den E (VBlob false j (VL (wp 0%uint63)) 8%uint63) = Z_to_bv 64 z.
Proof.
  intros E j z Hb Hz. cbn [den]. rewrite Hb. change (bv_unsigned (wbv (wp 0%uint63))) with 0. change (to_Z 8%uint63) with 8.
  apply bytes_val_le8. exact Hz.
Qed.

Lemma den_param8_u : forall E j z, eb E j = Z_to_le_bytes 8 z -> 0 <= z < 2 ^ 64 ->
  bv_unsigned (den E (VBlob false j (VL (wp 0%uint63)) 8%uint63)) = z.
Proof. intros E j z Hb Hz. rewrite (den_param8 E j z Hb Hz). apply Z_to_bv64_unsigned. exact Hz. Qed.

Lemma word_le8_is_le_bytes : forall w : word, word_le8 w = Z_to_le_bytes 8 (bv_unsigned w).
Proof.
  intros w. unfold word_le8. cbn [Z_to_le_bytes].
  rewrite !Z.shiftr_shiftr by lia.
  repeat (f_equal; [apply bv_eq; rewrite bv_extract_unsigned, Z_to_bv_unsigned; f_equal; cbn [Z.of_N Z.add Pos.add Pos.succ];
                    rewrite ?Z.shiftr_0_r; reflexivity |]). reflexivity.
Qed.

Lemma bytes_le_word_le8 : forall w : word, bytes_le_to_Z (word_le8 w) = bv_unsigned w.
Proof.
  intros w. rewrite word_le8_is_le_bytes, bytes_le_to_Z_of_le_bytes by (pose proof (u64_range w); lia).
  change (8 * Z.of_nat 8) with 64. apply Z.mod_small. apply u64_range.
Qed.

Lemma skipn_flat_map_le8 : forall (ws : list word) i, skipn (8 * i) (flat_map word_le8 ws) = flat_map word_le8 (skipn i ws).
Proof.
  induction ws as [|w ws IH]; intros i.
  - cbn [flat_map]. rewrite !skipn_nil. reflexivity.
  - destruct i as [|i]; [reflexivity|]. cbn [flat_map skipn].
    replace (8 * S i)%nat with (8 + 8 * i)%nat by lia.
    rewrite skipn_app. rewrite skipn_all2 by (cbn; lia). cbn [length word_le8 app].
    replace (8 + 8 * i - 8)%nat with (8 * i)%nat by lia. apply IH.
Qed.

Lemma den_word_at : forall E j off (ws : list word) (i : nat),
  eb E j = flat_map word_le8 ws -> bv_unsigned (den E off) = 8 * Z.of_nat i -> (i < length ws)%nat ->
  den E (VBlob false j off 8%uint63) = nth i ws (Z_to_bv 64 0).
Proof.
  intros E j off ws i Hb Hoff Hi. cbn [den]. rewrite Hb, Hoff. change (to_Z 8%uint63) with 8.
  unfold bytes_val, blob_bytes. change (Z.to_nat 8) with 8%nat.
  replace (Z.to_nat (8 * Z.of_nat i)) with (8 * i)%nat by lia.
  rewrite skipn_flat_map_le8.
  destruct (skipn i ws) as [|w rest] eqn:Hs.
  { exfalso. apply (f_equal (@length word)) in Hs. rewrite length_skipn in Hs. cbn in Hs. lia. }
  assert (Hw : nth i ws (Z_to_bv 64 0) = w).
  { rewrite <- (Nat.add_0_r i), <- nth_skipn, Hs. reflexivity. }
  rewrite Hw. cbn [flat_map]. rewrite firstn_app.
  replace (8 - length (word_le8 w))%nat with 0%nat by reflexivity. rewrite firstn_O, app_nil_r.
  rewrite firstn_all2 by (change (length (word_le8 w)) with 8%nat; lia).
  apply bv_eq. rewrite Z_to_bv_unsigned. rewrite bytes_le_word_le8.
  rewrite ext_Z_id64 by (unfold two64; apply u64_range). apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma den_byte_at : forall E j off (bs : list byte) (i : nat),
  eb E j = bs -> bv_unsigned (den E off) = Z.of_nat i -> (i < length bs)%nat ->
  den E (VBlob false j off 1%uint63) = Z_to_bv 64 (bv_unsigned (nth i bs (Z_to_bv 8 0))).
Proof.
  intros E j off bs i Hb Hoff Hi. cbn [den]. rewrite Hb, Hoff. change (to_Z 1%uint63) with 1.
  unfold bytes_val, blob_bytes. change (Z.to_nat 1) with 1%nat. rewrite Nat2Z.id.
  destruct (skipn i bs) as [|b rest] eqn:Hs.
  { exfalso. apply (f_equal (@length byte)) in Hs. rewrite length_skipn in Hs. cbn in Hs. lia. }
  assert (Hw : nth i bs (Z_to_bv 8 0) = b).
  { rewrite <- (Nat.add_0_r i), <- nth_skipn, Hs. reflexivity. }
  rewrite Hw. cbn [firstn bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r.
  f_equal. unfold ext_Z. change (2 ^ (8 * 0)) with 1. change (2 ^ (8 * 1)) with 256. rewrite Z.div_1_r.
  apply Z.mod_small. pose proof (bv_unsigned_in_range _ b). unfold bv_modulus in H. exact H.
Qed.

Lemma den_ext1_byte : forall E v b, den E v = Z_to_bv 64 b -> 0 <= b < 256 ->
  den E (VExt false 0%uint63 1%uint63 v) = Z_to_bv 64 b.
Proof.
  intros E v b Hv Hb. cbn [den]. rewrite Hv. unfold ext_word. rewrite Z_to_bv64_unsigned by lia.
  change (to_Z 0%uint63) with 0. change (to_Z 1%uint63) with 1.
  f_equal. unfold ext_Z. change (2 ^ (8 * 0)) with 1. change (2 ^ (8 * 1)) with 256. rewrite Z.div_1_r. apply Z.mod_small. exact Hb.
Qed.

Lemma facts_hold_cons : forall E f fs, facts_hold E (f :: fs) <-> fact_holds E f /\ facts_hold E fs.
Proof. intros. apply Forall_cons_iff. Qed.

End OL.
