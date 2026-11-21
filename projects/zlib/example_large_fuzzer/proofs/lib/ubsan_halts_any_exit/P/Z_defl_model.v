(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate FillWinModel DeflateSafe.
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


Definition blk_s2 (X : deflate_state) (flush : Z) : deflate_state :=
  if block_state_eqb (snd (deflate_slow X flush)) finish_started || block_state_eqb (snd (deflate_slow X flush)) finish_done
  then set_status (fst (deflate_slow X flush)) FINISH_STATE else fst (deflate_slow X flush).

