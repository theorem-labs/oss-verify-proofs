(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma act_avail_lew : forall NFR k, 0 <= NFR <= 2^32-1 -> 0 <= k <= 255 ->
  word_to_le_bytes 4 (wa (Z.land (ext_Z true 0 4 NFR mod 2^64) (bv_swrap 32 (bv_swrap 32 (Z.shiftl 2 (k mod 32)) + -1) mod 2^64)))
  = word_to_le_bytes 4 (wa (Z.land NFR (2 ^ (Z.land k 31 + 1) - 1))).
Proof.
  intros NFR k HN Hk. apply le_wa_eqm; [|apply Nat.leb_le; reflexivity]. change (8 * Z.of_nat 4) with 32.
  rewrite !land_mod32, !mod64_32, ext4_swrap, !swrap32_mod, act_span_mod32 by exact Hk. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma act_a1 : forall NFR k, 0 <= NFR <= 2^32-1 -> 0 <= k <= 255 ->
  wa (Z.land (ext_Z true 0 4 NFR mod 2^64) (bv_swrap 32 (bv_swrap 32 (Z.shiftl 2 (k mod 32)) + -1) mod 2^64))
  = wa (ext_Z true 0 4 (Z.land NFR (2 ^ (Z.land k 31 + 1) - 1))).
Proof.
  intros NFR k HN Hk. rewrite !ext4_swrap. rewrite sx32_land. apply wa_eqm. rewrite !Z.mod_mod by lia. f_equal.
  apply swrap32_eqm. rewrite !land_mod32. f_equal. apply act_span_mod32. exact Hk.
Qed.

(* [comment removed for export] *)
Lemma scw_ext32 : forall W, 0 <= W <= 2^32-1 -> SCW (ext_Z true 0 4 W) = SCW W.
Proof.
  intros W HW. unfold SCW. f_equal. rewrite ext4_swrap.
  assert (E : bv_swrap 32 W = W - 2^32 * ((W + 2^31) / 2^32)).
  { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N]. change (2 ^ Z.pos 32 `div` 2) with (2^31).
    change (2 ^ Z.pos 32) with (2^32). rewrite Zmod_eq_full by lia. ring. }
  rewrite E. replace (4503599627370496 * (W - 2 ^ 32 * ((W + 2 ^ 31) / 2 ^ 32))) with (4503599627370496 * W + (- (2^20 * ((W + 2 ^ 31) / 2 ^ 32))) * 2^64) by ring.
  apply Z_mod_plus_full.
Qed.

(* [comment removed for export] *)
Lemma ext4_ne0 : forall a, 1 <= a <= 2^32-1 -> (ext_Z true 0 4 a mod 2^64 =? 0 mod 2^64) = false.
Proof.
  intros a Ha. apply Z.eqb_neq. rewrite ext4_swrap. intros E.
  assert (E2 : (bv_swrap 32 a mod 2^64) mod 2^32 = 0) by (rewrite E; reflexivity).
  rewrite mod64_32, swrap32_mod, Z.mod_small in E2 by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma land126_bound : forall x, 0 <= Z.land x 126 < 128.
Proof.
  intros x. assert (E : Z.land x 126 = Z.land (Z.land x 126) (Z.ones 7)) by (rewrite <- Z.land_assoc; reflexivity).
  rewrite E, Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.

Lemma land3_bound : forall x, 0 <= Z.land x 3 < 4.
Proof.
  intros x. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.

(* [comment removed for export] *)
Lemma nosmall_z : forall (x : word) b, bv_unsigned x = b -> 0 <= b <= 255 ->
  wa (bv_unsigned (alu64 ALU_XOR (alu64 ALU_SLTU x (Z_to_bv 64 100)) (Z_to_bv 64 1))) = wa (if b <? 100 then 0 else 1).
Proof.
  intros x b Hx Hb. rewrite u_xor64. cbn [alu64 alu]. unfold bv_ltu. rewrite Hx.
  change (bv_unsigned (Z_to_bv 64 100)) with 100. change (bv_unsigned (Z_to_bv 64 1)) with 1.
  destruct (b <? 100); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma divu_lit : forall (x : bv 64) v c, bv_unsigned x = v -> 1 <= v -> 0 <= c < 2^64 ->
  bv_unsigned (mul_div M_DIVU (Z_to_bv 64 c) x) = c / v.
Proof.
  intros x v c Hx Hv Hc. unfold mul_div. rewrite Hx. replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite bv_divu_unsigned. rewrite Z_to_bv_unsigned, Hx. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite (Z.mod_small c) by lia. first [reflexivity | (apply Z.mod_small; split; [apply Z.div_pos; lia|]; apply (Z.le_lt_trans _ c); [apply Z.div_le_upper_bound; nia | lia])].
Qed.

(* [comment removed for export] *)
Lemma shl2_pow : forall k, 0 <= k <= 31 -> Z.shiftl 2 (k mod 32) = 2 ^ (k + 1).
Proof. intros k Hk. rewrite Z.mod_small by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.pow_add_r by lia. ring. Qed.
Lemma ins_avail_le : forall aidx, 0 <= aidx <= 31 ->
  word_to_le_bytes 4 (wa (bv_swrap 32 (Z.shiftl 2 (aidx mod 32)) + -1)) = word_to_le_bytes 4 (wa (2 ^ (aidx + 1) - 1)).
Proof.
  intros aidx Ha. apply le_wa_eqm; [|lia]. change (8 * Z.of_nat 4) with 32.
  rewrite Zplus_mod, swrap32_mod, <- Zplus_mod, shl2_pow by lia. try (f_equal; ring).
Qed.
Lemma eqm_lin : forall a b a' b', a mod 2^32 = a' mod 2^32 -> b mod 2^32 = b' mod 2^32 ->
  (a + -1 * b + -1) mod 2^32 = (a' + -1 * b' + -1) mod 2^32.
Proof.
  intros a b a' b' Ea Eb.
  pose proof (Z.div_mod a (2^32) ltac:(lia)) as Da. pose proof (Z.div_mod a' (2^32) ltac:(lia)) as Da'.
  pose proof (Z.div_mod b (2^32) ltac:(lia)) as Db. pose proof (Z.div_mod b' (2^32) ltac:(lia)) as Db'.
  replace (a + -1 * b + -1) with ((a' + -1 * b' + -1) + ((a / 2^32 - a' / 2^32) - (b / 2^32 - b' / 2^32)) * 2^32) by lia.
  apply Z_mod_plus_full.
Qed.

Lemma ins_freed_le : forall cnt aidx, 1 <= cnt <= 32 -> 0 <= aidx <= 31 ->
  word_to_le_bytes 4 (wa (bv_swrap 32 (Z.shiftl 2 ((cnt + -1) mod 32)) + -1 * ext_Z true 0 4 ((bv_swrap 32 (Z.shiftl 2 (aidx mod 32)) + -1) mod 2^64) + -1))
  = word_to_le_bytes 4 (wa (2 ^ cnt - 1 - (2 ^ (aidx + 1) - 1))).
Proof.
  intros cnt aidx Hc Ha. apply le_wa_eqm; [|lia]. change (8 * Z.of_nat 4) with 32.
  rewrite ext4_swrap.
  assert (E1 : bv_swrap 32 (Z.shiftl 2 ((cnt + -1) mod 32)) mod 2^32 = 2 ^ cnt mod 2^32).
  { rewrite swrap32_mod, shl2_pow by lia. try (f_equal; f_equal; ring). }
  assert (E2 : bv_swrap 32 ((bv_swrap 32 (Z.shiftl 2 (aidx mod 32)) + -1) mod 2^64) mod 2^32 = (2 ^ (aidx + 1) - 1) mod 2^32).
  { rewrite swrap32_mod, mod64_32, Zplus_mod, swrap32_mod, <- Zplus_mod, shl2_pow by lia. try (f_equal; ring). }
  rewrite (eqm_lin _ _ (2 ^ cnt) (2 ^ (aidx + 1) - 1) E1 E2). f_equal. ring.
Qed.

(* [comment removed for export] *)
Lemma ext44_le : forall w, word_to_le_bytes 4 (wa (ext_Z true 4 4 w)) = word_to_le_bytes 4 (wa (Z.shiftr w 32)).
Proof.
  intros w. apply le_wa_eqm; [|lia]. change (8 * Z.of_nat 4) with 32. unfold ext_Z. cbn [Z.of_nat N.of_nat].
  change (2 ^ (8 * 4)) with (2^32). change (8 * N.pos 4)%N with 32%N. rewrite swrap32_mod, Z.mod_mod by lia.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
