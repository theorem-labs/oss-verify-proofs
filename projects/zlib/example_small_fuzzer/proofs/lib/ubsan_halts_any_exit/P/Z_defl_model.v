(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz DeflateBlk Deflate FillWinModel DeflateSafe.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Deflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma adler_b3 : forall a, 0 <= a < 2^64 -> (Z.shiftr a 24) mod 2^8 = wrap8 (Z.shiftr (wrap32 (Z.shiftr a 16)) 8) mod 2^8.
Proof.
  intros a Ha. rewrite wrap8_mod, wrap32_mod. rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.mod_mod by lia.
  change (2^32) with (2^8 * 2^24). change (2^24) with (2^16 * 2^8) at 1.
  rewrite <- Z.div_div by lia. 
  rewrite Z.rem_mul_r by lia.
  Z.div_mod_to_equations. lia.
Qed.

Lemma adler_b2 : forall a, 0 <= a < 2^64 -> (Z.shiftr a 16) mod 2^8 = wrap8 (Z.land (wrap32 (Z.shiftr a 16)) 255) mod 2^8.
Proof.
  intros a Ha. rewrite wrap8_mod, wrap32_mod. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  rewrite !Z.shiftr_div_pow2 by lia. rewrite !Z.mod_mod by lia.
  change (2^32) with (2^8 * 2^24). rewrite Z.rem_mul_r by lia. Z.div_mod_to_equations. lia.
Qed.

Lemma adler_b1 : forall a, 0 <= a < 2^64 -> (Z.shiftr a 8) mod 2^8 = wrap8 (Z.shiftr (Z.land a 65535) 8) mod 2^8.
Proof.
  intros a Ha. rewrite wrap8_mod. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
  rewrite !Z.shiftr_div_pow2 by lia. rewrite !Z.mod_mod by lia.
  change (2^16) with (2^8 * 2^8). rewrite Z.rem_mul_r by lia. Z.div_mod_to_equations. lia.
Qed.

Lemma adler_b0 : forall a, 0 <= a < 2^64 -> a mod 2^8 = wrap8 (Z.land (Z.land a 65535) 255) mod 2^8.
Proof.
  intros a Ha. rewrite wrap8_mod. change 65535 with (Z.ones 16). change 255 with (Z.ones 8). rewrite !Z.land_ones by lia.
  rewrite !Z.mod_mod by lia. change (2^16) with (2^8 * 2^8). rewrite Z.rem_mul_r by lia. Z.div_mod_to_equations. lia.
Qed.

Definition put_adler (s : deflate_state) : deflate_state :=
  let a := cs_adler (ds_strm s) in putShortMSB (putShortMSB s (wrap32 (Z.shiftr a 16))) (Z.land a 65535).

Lemma zhdr_eq : forall s, ds_w_bits s = 15 -> ds_level s = 6 -> ds_strategy s = 0 ->
  zhdr_st s =
  (let s2 := put_byte (put_byte s 120) (if ds_strstart s =? 0 then 156 else 187) in
   let s3 := if ds_strstart s =? 0 then s2 else put_adler s2 in
   set_status (set_strm s3 (cset_adler (ds_strm s3) adler32_init)) BUSY_STATE).
Proof.
  intros s WB LV SG. unfold zhdr_st. rewrite WB, LV, SG. cbv zeta.
  change ((Z_HUFFMAN_ONLY <=? 0) || (6 <? 2)) with false. change (6 <? 6) with false. change (6 =? 6) with true. cbv beta iota.
  change (Z.lor (Z.shiftl (Z_DEFLATED + Z.shiftl (15 - 8) 4) 8) (Z.shiftl 2 6)) with 30848.
  change (ds_strstart (putShortMSB s ?h)) with (ds_strstart s).
  destruct (ds_strstart s =? 0) eqn:E; cbn [negb]; cbv beta iota.
  - change (30848 + (31 - 30848 mod 31)) with 30876. unfold putShortMSB.
    change (Z.shiftr 30876 8) with 120. change (Z.land 30876 255) with 156. reflexivity.
  - change (Z.lor 30848 PRESET_DICT + (31 - Z.lor 30848 PRESET_DICT mod 31)) with 30907. unfold put_adler. unfold putShortMSB at 5.
    change (Z.shiftr 30907 8) with 120. change (Z.land 30907 255) with 187. reflexivity.
Qed.

Definition blk_s2 (X : deflate_state) (flush : Z) : deflate_state :=
  if block_state_eqb (snd (deflate_slow X flush)) finish_started || block_state_eqb (snd (deflate_slow X flush)) finish_done
  then set_status (fst (deflate_slow X flush)) FINISH_STATE else fst (deflate_slow X flush).

