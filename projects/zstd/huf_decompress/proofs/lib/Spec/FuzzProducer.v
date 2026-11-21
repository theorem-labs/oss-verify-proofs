(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (7 recorded proofs replaced by written proofs (lor_byte, draw_loop_spec, uint32Range_spec and 4 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_FuzzProducer () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC46Stdlib6ZArith:ZArith_dec;Z_lt_le_decC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init6Specif7sumbool00K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1ZAmul_pow2_bits_lowC46Stdlib4Bool4Bool<andb_false_rK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z4log2C47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7pow_posC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z;lt_le_transC56Stdlib6ZArith6BinInt1Z?bits_above_log2C56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'C56Stdlib6ZArith6BinInt1Z@add_nocarry_lxorC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z8lxor_lorC47Corelib4Init5Logic6eq_indK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega;ZifyClasses6mkapp2K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums8positive00K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00C59OSSVerify5KrLib4Spec9FseLemmas9all_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natc59OSSVerify5KrLib4Spec<FuzzProducer9draw_loopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mul_0_rC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z7sub_0_rC56Stdlib6ZArith6BinInt1Z7pow_0_rK47Corelib4Init9Datatypes3nat02C46Stdlib9micromega;ZifyClasses6eq_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z9pow_add_rK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z8ltb_specC56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init9Datatypes8BoolSpec00I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib4Spec9FseNCount3u32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount4ZnthC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib4Spec9FseLemmas8pow2_posC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib7Numbers7BinNums8positive01c59OSSVerify5KrLib4Spec<FuzzProducer8lor_byteC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseLemmas6u32_idC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indK46Stdlib9micromega6VarMap1t03C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succK46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib4Init9Datatypes3nat01C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6moduloc59OSSVerify5KrLib4Spec<FuzzProducer>draw_loop_specC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z=mod_pos_boundc59OSSVerify5KrLib4Spec<FuzzProducer;uint32RangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega7EnvRing5PExpr06c59OSSVerify5KrLib4Spec<FuzzProducer@uint32Range_specC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<FuzzProducer:int32RangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<FuzzProducer>draw_loop_sizeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec<FuzzProducerAuint32Range_rangeC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint draw_loop (fuel : nat) (pl : list Z) (size rolling result : Z) : Z * Z :=
  match fuel with
  | O => (result, size)
  | S f =>
    if (0 <? rolling) && (0 <? size) then
      let next := Znth (size - 1) pl in
      draw_loop f pl (size - 1) (rolling / 2^8) (Z.lor (u32 (result * 2^8)) next)
    else (result, size)
  end.

(* [comment removed for export] *)
Definition uint32Range (pl : list Z) (size min max : Z) : Z * Z :=
  let range := u32 (max - min) in
  let '(result, size') := draw_loop 4%nat pl size range 0 in
  if range =? 2^32 - 1 then (result, size')
  else (u32 (min + result mod (range + 1)), size').

(* [comment removed for export] *)
Definition int32Range (pl : list Z) (size min max : Z) : Z * Z :=
  if min <? 0 then
    let '(r, size') := uint32Range pl size 0 (max - min) in (r + min, size')
  else uint32Range pl size min max.

Lemma lor_byte a b : 0 <= a -> 0 <= b < 256 -> Z.lor (a * 2^8) b = a * 2^8 + b.
Proof.
  intros. rewrite <- Z.lxor_lor.
  - symmetry. apply Z.add_nocarry_lxor.
    apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_le_dec n 8).
    + rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    + rewrite (Z.bits_above_log2 b); [apply andb_false_r|lia|].
      destruct (Z.eq_dec b 0). subst; simpl; lia. apply Z.log2_lt_pow2; [lia|].
      apply Z.lt_le_trans with (2^8); [simpl; lia|]. apply Z.pow_le_mono_r; lia.
  - apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_le_dec n 8).
    + rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    + rewrite (Z.bits_above_log2 b); [apply andb_false_r|lia|].
      destruct (Z.eq_dec b 0). subst; simpl; lia. apply Z.log2_lt_pow2; [lia|].
      apply Z.lt_le_trans with (2^8); [simpl; lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma draw_loop_spec fuel : forall pl size rolling result,
  all_bytes pl -> 0 <= size -> 0 <= rolling < 2^(8 * Z.of_nat fuel) ->
  8 * Z.of_nat fuel <= 32 -> 0 <= result < 2^(32 - 8 * Z.of_nat fuel) ->
  let '(r, size') := draw_loop fuel pl size rolling result in
  0 <= size' <= size /\ 0 <= r < 2^32 /\ (rolling = 0 -> r = result /\ size' = size).
Proof.
  induction fuel; intros pl size rolling result HB Hs Hr Hf Hres; cbn [draw_loop].
  - cbn [Z.of_nat] in *. rewrite Z.mul_0_r, Z.sub_0_r in Hres. rewrite Z.mul_0_r, Z.pow_0_r in Hr. lia.
  - assert (Hp : 2^(8 * Z.of_nat (S fuel)) = 2^8 * 2^(8 * Z.of_nat fuel)).
    { replace (8 * Z.of_nat (S fuel)) with (8 + 8 * Z.of_nat fuel) by lia. apply Z.pow_add_r; lia. }
    assert (Hq : 2^(32 - 8 * Z.of_nat fuel) = 2^8 * 2^(32 - 8 * Z.of_nat (S fuel))).
    { replace (32 - 8 * Z.of_nat fuel) with (8 + (32 - 8 * Z.of_nat (S fuel))) by lia. apply Z.pow_add_r; lia. }
    assert (2^(32 - 8 * Z.of_nat fuel) <= 2^32) by (apply Z.pow_le_mono_r; lia).
    destruct (Z.ltb_spec 0 rolling); destruct (Z.ltb_spec 0 size); cbn [andb]; try lia.
    pose proof (HB (size - 1)) as Hb.
    rewrite Hp in *.
    assert (0 < 2^(8 * Z.of_nat fuel)) by (apply pow2_pos; lia).
    rewrite (u32_id (result * 2^8)) by (change (2^8) with 256 in *; nia).
    rewrite lor_byte by lia.
    specialize (IHfuel pl (size - 1) (rolling / 2^8) (result * 2^8 + Znth (size - 1) pl) HB ltac:(lia)).
    destruct (draw_loop fuel pl (size - 1) (rolling / 2^8) (result * 2^8 + Znth (size - 1) pl)) as [r size'].
    assert (0 <= rolling / 2^8 < 2^(8 * Z.of_nat fuel)).
    { split. apply Z.div_pos; lia. apply Z.div_lt_upper_bound; [lia|]. lia. }
    change (2^8) with 256 in *.
    destruct IHfuel as (A & B & C); try nia.
Qed.

Lemma uint32Range_spec pl size min max :
  all_bytes pl -> 0 <= size -> 0 <= min <= max -> max < 2^32 ->
  let '(r, size') := uint32Range pl size min max in
  min <= r <= max /\ 0 <= size' <= size /\ (min = max -> size' = size).
Proof.
  intros HB Hs Hmm Hmax. unfold uint32Range.
  rewrite (u32_id (max - min)) by lia.
  pose proof (draw_loop_spec 4 pl size (max - min) 0 HB Hs) as DL.
  destruct (draw_loop 4 pl size (max - min) 0) as [r size'].
  destruct DL as (A & B & C); try (simpl; lia).
  destruct (Z.eqb_spec (max - min) (2^32 - 1)).
  - repeat split; try lia.
  - pose proof (Z.mod_pos_bound r (max - min + 1) ltac:(lia)).
    rewrite u32_id by lia. repeat split; try lia.
Qed.

Lemma int32Range_spec pl size min max :
  all_bytes pl -> 0 <= size -> -2^31 <= min <= max -> max < 2^31 ->
  let '(r, size') := int32Range pl size min max in
  min <= r <= max /\ 0 <= size' <= size.
Proof.
  intros HB Hs Hmm Hmax. change (2^31) with 2147483648 in *. unfold int32Range. destruct (Z.ltb_spec min 0).
  - pose proof (uint32Range_spec pl size 0 (max - min) HB Hs ltac:(lia) ltac:(change (2^32) with 4294967296; lia)) as U.
    destruct (uint32Range pl size 0 (max - min)) as [r size']. lia.
  - pose proof (uint32Range_spec pl size min max HB Hs ltac:(lia) ltac:(change (2^32) with 4294967296; lia)) as U.
    destruct (uint32Range pl size min max) as [r size']. lia.
Qed.

(* [comment removed for export] *)
Lemma draw_loop_size fuel : forall pl size rolling result,
  0 <= size -> let '(_, size') := draw_loop fuel pl size rolling result in 0 <= size' <= size.
Proof.
  induction fuel; intros pl size rolling result Hs; cbn [draw_loop]; [lia|].
  destruct (Z.ltb_spec 0 rolling); destruct (Z.ltb_spec 0 size); cbn [andb]; try lia.
  specialize (IHfuel pl (size - 1) (rolling / 2^8) (Z.lor (u32 (result * 2^8)) (Znth (size - 1) pl)) ltac:(lia)).
  destruct (draw_loop fuel pl (size - 1) (rolling / 2^8) (Z.lor (u32 (result * 2^8)) (Znth (size - 1) pl))) as [r size'].
  lia.
Qed.

Lemma uint32Range_range pl size min max :
  0 <= size -> 0 <= min <= max -> max < 2^32 -> max - min < 2^32 - 1 ->
  let '(r, size') := uint32Range pl size min max in
  min <= r <= max /\ 0 <= size' <= size.
Proof.
  intros Hs Hmm Hmax Hr. change (2^32) with 4294967296 in *. unfold uint32Range.
  rewrite (u32_id (max - min)) by (change (2^32) with 4294967296; lia).
  pose proof (draw_loop_size 4 pl size (max - min) 0 Hs) as DL.
  destruct (draw_loop 4 pl size (max - min) 0) as [r size'].
  change (2^32) with 4294967296.
  destruct (Z.eqb_spec (max - min) (4294967296 - 1)); [lia|].
  pose proof (Z.mod_pos_bound r (max - min + 1) ltac:(lia)).
  rewrite u32_id by (change (2^32) with 4294967296; lia). lia.
Qed.

Lemma int32Range_range pl size min max :
  0 <= size -> -2^31 <= min <= max -> max < 2^31 -> max - min < 2^32 - 1 ->
  let '(r, size') := int32Range pl size min max in
  min <= r <= max /\ 0 <= size' <= size.
Proof.
  intros Hs Hmm Hmax Hr. change (2^31) with 2147483648 in *. change (2^32) with 4294967296 in *.
  unfold int32Range. destruct (Z.ltb_spec min 0).
  - pose proof (uint32Range_range pl size 0 (max - min) Hs ltac:(lia) ltac:(change (2^32) with 4294967296; lia)
                  ltac:(change (2^32) with 4294967296; lia)) as U.
    destruct (uint32Range pl size 0 (max - min)) as [r size']. lia.
  - pose proof (uint32Range_range pl size min max Hs ltac:(lia) ltac:(change (2^32) with 4294967296; lia)
                  ltac:(change (2^32) with 4294967296; lia)) as U.
    destruct (uint32Range pl size min max) as [r size']. lia.
Qed.
