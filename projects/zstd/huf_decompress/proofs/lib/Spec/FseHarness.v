(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (22 recorded proofs replaced by written proofs (lor_byte, draw_loop_spec, uint32Range_spec and 19 more)). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas FseAbs FseWriterRT FseReaderRT FseNCountRT.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_FseHarness () := "C46Stdlib5Lists4List6nth_okC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC46Stdlib6ZArith:ZArith_dec;Z_lt_le_decC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init6Specif7sumbool00K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1ZAmul_pow2_bits_lowC46Stdlib4Bool4Bool<andb_false_rK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7pow_posC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z;lt_le_transC56Stdlib6ZArith6BinInt1Z?bits_above_log2C56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'C56Stdlib6ZArith6BinInt1Z@add_nocarry_lxorC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z8lxor_lorC47Corelib4Init5Logic6eq_indK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega;ZifyClasses6mkapp2K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums8positive00K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00C59OSSVerify5KrLib4Spec9FseLemmas9all_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natc59OSSVerify5KrLib4Spec:FseHarness9draw_loopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mul_0_rC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z7sub_0_rC56Stdlib6ZArith6BinInt1Z7pow_0_rK47Corelib4Init9Datatypes3nat02C46Stdlib9micromega;ZifyClasses6eq_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z9pow_add_rK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z8ltb_specC56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init9Datatypes8BoolSpec00I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib4Spec9FseNCount3u32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount4ZnthC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib4Spec9FseLemmas8pow2_posC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib7Numbers7BinNums8positive01c59OSSVerify5KrLib4Spec:FseHarness8lor_byteC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseLemmas6u32_idC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indK46Stdlib9micromega6VarMap1t03C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succK46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib4Init9Datatypes3nat01C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6moduloc59OSSVerify5KrLib4Spec:FseHarness>draw_loop_specC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z=mod_pos_boundc59OSSVerify5KrLib4Spec:FseHarness;uint32RangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega7EnvRing5PExpr06c59OSSVerify5KrLib4Spec:FseHarness@uint32Range_specC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:FseHarness:int32RangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:FseHarness>draw_loop_sizeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:FseHarnessAuint32Range_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natc59OSSVerify5KrLib4Spec:FseHarness8fse_fillC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC56Stdlib6ZArith6BinInt1Z3maxC59OSSVerify5KrLib4Spec9FseNCount4wsumC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib4Init5Logic2ex01c59OSSVerify5KrLib4Spec:FseHarness@int32Range_rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC46Stdlib5Lists4List:length_appC47Corelib4Init9Datatypes3appI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib4Spec;FseNCountRT8wsum_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount6weightC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic2ex00I47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI46Stdlib5Lists4List6Exists00c59OSSVerify5KrLib4Spec:FseHarness?fse_fill_inv_nbC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec9FseNCount<harness_fillC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z8leb_specK47Corelib4Init9Datatypes6option01c59OSSVerify5KrLib4Spec:FseHarnessCfse_fill_harness_nbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;FseWriterRT7hdrSizeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List:length_seqC59OSSVerify5KrLib4Spec6FseAbs6afinalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6FseAbs3a_NC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;FseWriterRT7byte_ofC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:length_mapc59OSSVerify5KrLib4Spec:FseHarness8fse_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount7ZlengthC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC57Corelib7BinNums6IntDef1Z6to_natC57Corelib7BinNums6IntDef1Z6of_natC47Corelib4Init5Logic8eq_transC47Corelib4Init5Peano2ltC46Stdlib5Lists4List7seq_nthC46Stdlib5Lists4List7map_nthC46Stdlib5Lists4List9nth_indepC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC59OSSVerify5KrLib4Spec6FseAbs2a0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6FseAbs5acondC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3absC59OSSVerify5KrLib4Spec6FseAbs4normC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6FseAbs4cvalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6FseAbs6cwidthC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6PosDef3Pos4succC56Stdlib6ZArith6BinInt1Z7pos_subK59OSSVerify5KrLib4Spec6FseAbs6astate01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6FseAbs4arunC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:FseHarness<fse_data_nthC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C46Stdlib5Lists4List<nth_overflowC56Stdlib6ZArith4Znat5Nat2Z6inj_leI59OSSVerify5KrLib4Spec6FseAbs6astate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount@FSE_MIN_TABLELOGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount4ZupdC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3subC59OSSVerify5KrLib4Spec9FseNCount<valid_ncountC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount;write_boundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_reflC59OSSVerify5KrLib4Spec9FseNCount>harness_ncountC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;FseNCountRTDharness_ncount_validC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6FseAbs;afinal_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6FseAbs4ainvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6FseAbs5a_symC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6FseAbs5a_remC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6FseAbs3a_TC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=repeat_lengthC59OSSVerify5KrLib4Spec;FseNCountRT?write_ncount_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec9FseNCount3res00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount<write_ncountC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec9FseNCount3res01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;FseNCountRTBwrite_bound_le_512C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:FseHarness?fse_data_lengthC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:FseHarness>fse_data_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:FseHarness4fseAC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatC47Corelib5Lists7ListDef6firstnC47Corelib4Init5Logic7and_indC59OSSVerify5KrLib4Spec9FseNCount@FSE_MAX_TABLELOGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:FseHarness=fseA_facts_nbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:FseHarness7fse_bszC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:FseHarness:fseA_factsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List@firstn_length_leC56Stdlib5Arith8PeanoNat3Nat3ltbC56Stdlib5Arith8PeanoNat3Nat8ltb_specC56Stdlib6ZArith4Znat5Nat2Z2idC46Stdlib5Lists4List:nth_firstnC46Stdlib5Lists4List7nth_extc59OSSVerify5KrLib4Spec:FseHarness>fseB_tail_loopC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano8plus_n_OC59OSSVerify5KrLib4Spec9FseNCount7to_byteC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:FseHarnessCfseB_tail_loop_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseLemmas@Forall_all_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:FseHarness9fseB_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseLemmas@all_bytes_ForallC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Z2Nat2idC46Stdlib5Lists4List8app_nth1C59OSSVerify5KrLib4Spec;FseNCountRT@stream_of_prefixC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;FseReaderRT>read_ncount_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount;read_ncountC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;FseNCountRTFvalid_stream_of_prefixC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;FseNCountRT<valid_streamC1?~~~~~~~~~~~~~~~".
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

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint fse_fill (fuel : nat) (pl : list Z) (size s maxSV rw : Z) (acc : list Z) : list Z * Z * Z :=
  match fuel with
  | O => (acc, rw, size)
  | S f =>
    if (s <? maxSV) && (0 <? rw) then
      let '(n, size') := int32Range pl size (-1) rw in
      let rw' := if n <? 0 then rw - 1 else rw - n in
      fse_fill f pl size' (s + 1) maxSV rw' (acc ++ [n])
    else (acc, rw, size)
  end.

(* [comment removed for export] *)
Definition fse_data (nc : list Z) (msv tl : Z) : list Z :=
  map (fun i => byte_of (a_N (afinal nc msv tl)) (Z.of_nat i)) (seq 0 (Z.to_nat (hdrSize nc msv tl))).

(* [comment removed for export] *)
Definition fseA (pl : list Z) (n : Z) : Z * Z * list Z * list Z * Z * Z * Z :=
  let '(tl, r1) := uint32Range pl n FSE_MIN_TABLELOG FSE_MAX_TABLELOG in
  let '(msv, r2) := uint32Range pl r1 0 255 in
  let '(pre, rw, r3) := fse_fill 256%nat pl r2 0 msv (2^tl - 1) [] in
  let nc0 := pre ++ repeat 0 (256 - length pre) in
  let v := rw + 1 in
  let '(v', r4) := (if v =? 1
                    then (let '(c, r4) := uint32Range pl r3 0 1 in ((if c =? 1 then -1 else v), r4))
                    else (v, r3)) in
  let nc := Zupd msv v' nc0 in
  let dsz := hdrSize nc msv tl in
  let data := fse_data nc msv tl in
  let '(bsz, r5) := uint32Range pl r4 dsz 512 in
  (tl, msv, nc, data, dsz, bsz, r5).

(* [comment removed for export] *)
Fixpoint fseB_tail_loop (fuel : nat) (pl : list Z) (size : Z) (acc : list Z) : list Z * Z :=
  match fuel with
  | O => (acc, size)
  | S f => let '(c, size') := uint32Range pl size 0 255 in fseB_tail_loop f pl size' (acc ++ [to_byte c])
  end.

Definition fseB_tail (pl : list Z) (rem dsz bsz : Z) : list Z * Z :=
  fseB_tail_loop (Z.to_nat (bsz - dsz)) pl rem [].

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fse_fill_inv_nb fuel : forall pl size s maxSV rw acc pre rw' size',
  0 <= size -> 0 <= s -> length acc = Z.to_nat s -> 0 <= rw <= 4095 ->
  Forall (fun c => -1 <= c) acc ->
  fse_fill fuel pl size s maxSV rw acc = (pre, rw', size') ->
  exists s', s <= s' <= Z.max s maxSV /\ length pre = Z.to_nat s' /\ 0 <= rw' <= rw /\
             Forall (fun c => -1 <= c) pre /\ wsum pre + rw' = wsum acc + rw /\ 0 <= size' <= size.
Proof.
  induction fuel; intros pl size s maxSV rw acc pre rw' size' Hsz Hs Hlen Hrw Hall E; cbn [fse_fill] in E.
  - injection E as <- <- <-. exists s. repeat split; auto; lia.
  - destruct (Z.ltb_spec s maxSV); destruct (Z.ltb_spec 0 rw); cbn [andb] in E;
      try (injection E as <- <- <-; exists s; repeat split; auto; lia).
    pose proof (int32Range_range pl size (-1) rw Hsz ltac:(change (2^31) with 2147483648; lia) ltac:(change (2^31) with 2147483648; lia) ltac:(change (2^32) with 4294967296; lia)) as IR.
    destruct (int32Range pl size (-1) rw) as [n size1].
    destruct IR as [IR1 IR2].
    match type of E with fse_fill _ _ ?sz ?s1 ?m ?r ?ac = _ =>
      destruct (IHfuel pl sz s1 m r ac pre rw' size') as (s' & A1 & A2 & A3 & A4 & A5 & A6) end.
    { lia. } { lia. } { rewrite length_app; simpl; rewrite Hlen; lia. }
    { destruct (Z.ltb_spec n 0); lia. } { apply Forall_app; split; auto. constructor; [lia|constructor]. } { exact E. }
    exists s'. rewrite wsum_app in A5. cbn [wsum] in A5.
    repeat split; auto; try lia.
    + destruct (Z.ltb_spec n 0); lia.
    + unfold weight in A5. destruct (Z.ltb_spec n 0); destruct (Z.eqb_spec n (-1)); lia.
Qed.

Lemma fse_fill_inv fuel : forall pl size s maxSV rw acc pre rw' size',
  all_bytes pl -> 0 <= size -> 0 <= s -> length acc = Z.to_nat s -> 0 <= rw <= 4095 ->
  Forall (fun c => -1 <= c) acc ->
  fse_fill fuel pl size s maxSV rw acc = (pre, rw', size') ->
  exists s', s <= s' <= Z.max s maxSV /\ length pre = Z.to_nat s' /\ 0 <= rw' <= rw /\
             Forall (fun c => -1 <= c) pre /\ wsum pre + rw' = wsum acc + rw /\ 0 <= size' <= size.
Proof. intros pl size s maxSV rw acc pre rw' size' _. apply fse_fill_inv_nb. Qed.

(* [comment removed for export] *)
Lemma fse_fill_harness_nb fuel : forall pl size s maxSV rw acc pre rw' size',
  0 <= size -> 0 <= rw <= 4095 ->
  fse_fill fuel pl size s maxSV rw acc = (pre, rw', size') ->
  exists ds, harness_fill fuel ds s maxSV rw acc = Some (pre, rw', []).
Proof.
  induction fuel; intros pl size s maxSV rw acc pre rw' size' Hsz Hrw E; cbn [fse_fill] in E.
  - injection E as <- <- <-. exists []. reflexivity.
  - cbn [harness_fill].
    destruct (Z.ltb_spec s maxSV); destruct (Z.ltb_spec 0 rw); cbn [andb] in E |- *;
      try (injection E as <- <- <-; exists []; reflexivity).
    pose proof (int32Range_range pl size (-1) rw Hsz ltac:(change (2^31) with 2147483648; lia) ltac:(change (2^31) with 2147483648; lia) ltac:(change (2^32) with 4294967296; lia)) as IR.
    destruct (int32Range pl size (-1) rw) as [n size1]. destruct IR as [IR1 IR2].
    destruct (IHfuel pl size1 (s+1) maxSV (if n <? 0 then rw - 1 else rw - n) (acc ++ [n]) pre rw' size') as (ds & Hds); auto.
    { lia. } { destruct (Z.ltb_spec n 0); lia. }
    exists (n :: ds). destruct (Z.leb_spec (-1) n); [|lia]. destruct (Z.leb_spec n rw); [|lia]. cbn [andb].
    exact Hds.
Qed.

Lemma fse_fill_harness fuel : forall pl size s maxSV rw acc pre rw' size',
  all_bytes pl -> 0 <= size -> 0 <= rw <= 4095 ->
  fse_fill fuel pl size s maxSV rw acc = (pre, rw', size') ->
  exists ds, harness_fill fuel ds s maxSV rw acc = Some (pre, rw', []).
Proof. intros pl size s maxSV rw acc pre rw' size' _. apply fse_fill_harness_nb. Qed.

Lemma fse_data_length nc msv tl : Zlength (fse_data nc msv tl) = Z.max 0 (hdrSize nc msv tl).
Proof. unfold fse_data, Zlength. rewrite length_map, length_seq. lia. Qed.

Lemma fse_data_nth nc msv tl i : 0 <= i < hdrSize nc msv tl ->
  Znth i (fse_data nc msv tl) = byte_of (a_N (afinal nc msv tl)) i.
Proof.
  intros. unfold fse_data, Znth.
  rewrite (nth_indep _ 0 (byte_of (a_N (afinal nc msv tl)) (Z.of_nat 0))) by (rewrite length_map, length_seq; lia).
  rewrite (map_nth (fun i0 : nat => byte_of (a_N (afinal nc msv tl)) (Z.of_nat i0))).
  rewrite seq_nth by lia. f_equal. lia.
Qed.

Lemma fse_data_bytes nc msv tl : all_bytes (fse_data nc msv tl).
Proof.
  intros i. destruct (Z_lt_le_dec i 0).
  { unfold Znth. replace (Z.to_nat i) with 0%nat by lia. unfold fse_data.
    destruct (Z.to_nat (hdrSize nc msv tl)); cbn. lia. unfold byte_of. apply Z.mod_pos_bound. lia. }
  destruct (Z_lt_le_dec i (hdrSize nc msv tl)).
  - rewrite fse_data_nth by lia. unfold byte_of. apply Z.mod_pos_bound. lia.
  - unfold Znth. rewrite nth_overflow. lia. unfold fse_data. rewrite length_map, length_seq. lia.
Qed.

(* [comment removed for export] *)
Theorem fseA_facts_nb pl n :
  0 <= n ->
  let '(tl, msv, nc, data, dsz, bsz, rem) := fseA pl n in
  FSE_MIN_TABLELOG <= tl <= FSE_MAX_TABLELOG /\ 0 <= msv <= 255 /\
  valid_ncount nc msv tl /\ length nc = 256%nat /\
  dsz = hdrSize nc msv tl /\ 2 <= dsz <= 481 /\ write_bound msv tl <= 512 /\
  data = fse_data nc msv tl /\ Zlength data = dsz /\ all_bytes data /\
  dsz <= bsz <= 512 /\ 0 <= rem <= n.
Proof.
  intros Hn. unfold fseA, FSE_MIN_TABLELOG, FSE_MAX_TABLELOG.
  pose proof (uint32Range_range pl n 5 12 Hn ltac:(lia) ltac:(change (2^32) with 4294967296; lia) ltac:(change (2^32) with 4294967296; lia)) as U1.
  destruct (uint32Range pl n 5 12) as [tl r1]. destruct U1 as (U1a & U1b).
  pose proof (uint32Range_range pl r1 0 255 ltac:(lia) ltac:(lia) ltac:(change (2^32) with 4294967296; lia) ltac:(change (2^32) with 4294967296; lia)) as U2.
  destruct (uint32Range pl r1 0 255) as [msv r2]. destruct U2 as (U2a & U2b).
  assert (HP : 1 <= 2^tl <= 2^12) by (split; [pose proof (pow2_pos tl); lia | apply Z.pow_le_mono_r; lia]).
  destruct (fse_fill 256 pl r2 0 msv (2^tl - 1) []) as [[pre rw] r3] eqn:EF.
  destruct (fse_fill_inv_nb 256 pl r2 0 msv (2^tl - 1) [] pre rw r3 ltac:(lia) ltac:(lia) eq_refl
              ltac:(change (2^12) with 4096 in HP; lia) ltac:(constructor) EF)
    as (s' & A1 & A2 & A3 & A4 & A5 & A6).
  cbn [wsum] in A5.
  (* [comment removed for export] *)
  match goal with |- context [let '(v', r4) := ?e in _] =>
    assert (HV : exists v' r4, e = (v', r4) /\ 0 <= r4 <= r3 /\
              (v' = (if (rw + 1 =? 1) && (match e with (v', _) => v' =? -1 end) then -1 else rw + 1)))
  end.
  { destruct (Z.eqb_spec (rw + 1) 1).
    - pose proof (uint32Range_range pl r3 0 1 ltac:(lia) ltac:(lia) ltac:(change (2^32) with 4294967296; lia) ltac:(change (2^32) with 4294967296; lia)) as U3.
      destruct (uint32Range pl r3 0 1) as [c r4]. eexists _, _. split; [reflexivity|].
      split; [lia|]. destruct (Z.eqb_spec c 1); cbn [andb]; rewrite ?Z.eqb_refl; auto.
      destruct (Z.eqb_spec (rw + 1) (-1)); lia.
    - eexists _, _. split; [reflexivity|]. split; [lia|]. reflexivity. }
  destruct HV as (v' & r4 & EV & R4 & HV'). rewrite EV. rewrite EV in HV'.
  set (coin := v' =? -1) in HV'.
  (* [comment removed for export] *)
  set (nc := Zupd msv v' (pre ++ repeat 0 (256 - length pre))).
  destruct (fse_fill_harness_nb 256 pl r2 0 msv (2^tl - 1) [] pre rw r3 ltac:(lia)
              ltac:(change (2^12) with 4096 in HP; lia) EF) as (ds & Hds).
  assert (V : valid_ncount nc msv tl).
  { apply (harness_ncount_valid tl msv ds coin nc); unfold FSE_MIN_TABLELOG, FSE_MAX_TABLELOG; try lia.
    cbv beta zeta delta [harness_ncount]. rewrite Hds. subst nc. rewrite <- HV'. reflexivity. }
  pose proof (afinal_spec nc msv tl V) as (IF & SYF & REMF & CF & TBF & NBF).
  (* [comment removed for export] *)
  destruct (write_ncount_ok nc msv tl (repeat 0 512) V) as (buf' & E' & W1 & W2 & W3 & W4 & W5 & _).
  { unfold Zlength. rewrite repeat_length. lia. }
  assert (Hdsz : 2 <= hdrSize nc msv tl <= 481) by lia.
  pose proof (uint32Range_range pl r4 (hdrSize nc msv tl) 512 ltac:(lia) ltac:(lia) ltac:(change (2^32) with 4294967296; lia) ltac:(change (2^32) with 4294967296; lia)) as U5.
  destruct (uint32Range pl r4 (hdrSize nc msv tl) 512) as [bsz r5].
  pose proof (write_bound_le_512 msv tl ltac:(lia) ltac:(lia)).
  pose proof (fse_data_length nc msv tl). pose proof (fse_data_bytes nc msv tl).
  assert (length nc = 256%nat) by (destruct V; tauto).
  split; [unfold FSE_MIN_TABLELOG, FSE_MAX_TABLELOG; lia|]. split; [lia|]. split; [exact V|].
  split; [auto|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [reflexivity|].
  split; [lia|]. split; [auto|]. lia.
Qed.

Theorem fseA_facts pl n :
  all_bytes pl -> 0 <= n ->
  let '(tl, msv, nc, data, dsz, bsz, rem) := fseA pl n in
  FSE_MIN_TABLELOG <= tl <= FSE_MAX_TABLELOG /\ 0 <= msv <= 255 /\
  valid_ncount nc msv tl /\ length nc = 256%nat /\
  dsz = hdrSize nc msv tl /\ 2 <= dsz <= 481 /\ write_bound msv tl <= 512 /\
  data = fse_data nc msv tl /\ Zlength data = dsz /\ all_bytes data /\
  dsz <= bsz <= 512 /\ 0 <= rem <= n.
Proof. intros _. apply fseA_facts_nb. Qed.

(* [comment removed for export] *)
Definition fse_bsz (pl : list Z) : Z :=
  let '(_, _, _, _, _, bsz, _) := fseA pl (Zlength pl) in bsz.

Lemma fse_bsz_range pl : 2 <= fse_bsz pl <= 512.
Proof.
  unfold fse_bsz. pose proof (fseA_facts_nb pl (Zlength pl) ltac:(unfold Zlength; lia)) as F.
  destruct (fseA pl (Zlength pl)) as [[[[[[tl msv] nc] data] dsz] bsz] rem].
  destruct F as (_ & _ & _ & _ & _ & F6 & _ & _ & _ & _ & F11 & _). lia.
Qed.

(* [comment removed for export] *)
Theorem fseA_write_ncount pl n data0 :
  all_bytes pl -> 0 <= n -> length data0 = 512%nat ->
  let '(tl, msv, nc, data, dsz, bsz, rem) := fseA pl n in
  exists buf', write_ncount data0 nc msv tl = Ok (buf', dsz) /\ length buf' = 512%nat /\
    firstn (Z.to_nat dsz) buf' = data /\
    (forall i, 0 <= i < dsz -> Znth i buf' = Znth i data) /\
    (forall i, dsz + 1 <= i -> Znth i buf' = Znth i data0).
Proof.
  intros HB Hn HL.
  pose proof (fseA_facts pl n HB Hn) as F.
  destruct (fseA pl n) as [[[[[[tl msv] nc] data] dsz] bsz] rem].
  destruct F as (F1 & F2 & V & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12).
  destruct (write_ncount_ok nc msv tl data0 V) as (buf' & E & W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9).
  { unfold Zlength. rewrite HL. lia. }
  rewrite <- F5 in *. exists buf'. split; [exact W1|]. split; [rewrite W2; exact HL|].
  assert (HZ : forall i, 0 <= i < dsz -> Znth i buf' = Znth i data).
  { intros i Hi. rewrite W8 by lia. rewrite F8. rewrite fse_data_nth by lia. reflexivity. }
  split; [|split; [exact HZ|intros; apply W9; lia]].
  apply (nth_ext _ _ 0 0).
  - rewrite firstn_length_le by (rewrite W2, HL; lia). unfold Zlength in F9. lia.
  - intros k Hk. rewrite firstn_length_le in Hk by (rewrite W2, HL; lia).
    rewrite nth_firstn. destruct (Nat.ltb_spec k (Z.to_nat dsz)); [|lia].
    specialize (HZ (Z.of_nat k) ltac:(lia)). unfold Znth in HZ. rewrite Nat2Z.id in HZ. exact HZ.
Qed.

Lemma fseB_tail_loop_spec fuel : forall pl size acc,
  all_bytes pl -> 0 <= size -> Forall (fun b => 0 <= b < 256) acc ->
  let '(junk, size') := fseB_tail_loop fuel pl size acc in
  length junk = (length acc + fuel)%nat /\ 0 <= size' <= size /\ Forall (fun b => 0 <= b < 256) junk.
Proof.
  induction fuel; intros pl size acc HB Hs Hacc; cbn [fseB_tail_loop].
  - repeat split; auto; lia.
  - pose proof (uint32Range_spec pl size 0 255 HB Hs ltac:(lia) ltac:(change (2^32) with 4294967296; lia)) as U.
    destruct (uint32Range pl size 0 255) as [c size1]. destruct U as (U1 & U2 & _).
    specialize (IHfuel pl size1 (acc ++ [to_byte c]) HB ltac:(lia)).
    destruct (fseB_tail_loop fuel pl size1 (acc ++ [to_byte c])) as [junk size'].
    destruct IHfuel as (A & B & C).
    { apply Forall_app. split; auto. constructor; [|constructor]. unfold to_byte. apply Z.mod_pos_bound. lia. }
    rewrite length_app in A. simpl in A. repeat split; auto; lia.
Qed.

(* [comment removed for export] *)
Theorem fseB_tail_spec pl rem dsz bsz :
  all_bytes pl -> 0 <= rem -> dsz <= bsz ->
  let '(junk, rem') := fseB_tail pl rem dsz bsz in
  Zlength junk = bsz - dsz /\ all_bytes junk /\ 0 <= rem' <= rem.
Proof.
  intros HB Hr Hd. unfold fseB_tail.
  pose proof (fseB_tail_loop_spec (Z.to_nat (bsz - dsz)) pl rem [] HB Hr ltac:(constructor)) as T.
  destruct (fseB_tail_loop (Z.to_nat (bsz - dsz)) pl rem []) as [junk rem'].
  destruct T as (A & B & C). simpl in A. unfold Zlength. repeat split; try lia.
  all: apply Forall_all_bytes in C; apply C.
Qed.

(* [comment removed for export] *)
Theorem fseB_round_trip pl n junk rt0 :
  all_bytes pl -> 0 <= n ->
  let '(tl, msv, nc, data, dsz, bsz, rem) := fseA pl n in
  all_bytes junk -> length rt0 = 256%nat ->
  exists rt, read_ncount rt0 255 (data ++ junk) = Ok (rt, msv, tl, dsz) /\ length rt = 256%nat /\
    (forall i, 0 <= i <= msv -> Znth i rt = Znth i nc) /\ (forall i, msv < i <= 255 -> Znth i rt = 0).
Proof.
  intros HB Hn.
  pose proof (fseA_facts pl n HB Hn) as F.
  destruct (fseA pl n) as [[[[[[tl msv] nc] data] dsz] bsz] rem].
  destruct F as (F1 & F2 & V & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12).
  intros HJ Hrt.
  pose proof (afinal_spec nc msv tl V) as (IF & SYF & REMF & CF & TBF & NBF).
  destruct (write_ncount_ok nc msv tl (repeat 0 512) V) as (buf' & E' & W1 & W2 & W3 & W4 & W5 & _).
  { unfold Zlength. rewrite repeat_length. lia. }
  assert (HBB : all_bytes (data ++ junk)).
  { apply Forall_all_bytes. apply Forall_app. split; apply all_bytes_Forall; auto. }
  assert (HLen : dsz <= Zlength (data ++ junk)).
  { unfold Zlength in *. rewrite length_app. lia. }
  destruct (read_ncount_ok nc msv tl (data ++ junk) rt0 255 V HBB ltac:(lia) ltac:(unfold Zlength; rewrite Hrt; lia))
    as (rt & R1 & R2 & R3 & R4 & R5).
  { unfold hdrSize in F5. rewrite <- F5. exact HLen. }
  { apply (stream_of_prefix (data ++ junk) _ _ (Z.to_nat dsz)); auto.
    - unfold Zlength in HLen. lia.
    - rewrite Z2Nat.id by lia. rewrite F5. lia.
    - intros i Hi. rewrite Z2Nat.id in Hi by lia. unfold Znth. rewrite app_nth1 by (unfold Zlength in F9; lia).
      fold (Znth i data). rewrite F8. apply fse_data_nth. lia. }
  exists rt. unfold hdrSize in F5. rewrite <- F5 in R1. rewrite R1. repeat split; auto. rewrite R2. exact Hrt.
Qed.

(* [comment removed for export] *)
Theorem fseA_valid_stream pl n junk :
  all_bytes pl -> 0 <= n ->
  let '(tl, msv, nc, data, dsz, bsz, rem) := fseA pl n in
  all_bytes junk -> valid_stream nc msv tl (data ++ junk).
Proof.
  intros HB Hn.
  pose proof (fseA_facts pl n HB Hn) as F.
  destruct (fseA pl n) as [[[[[[tl msv] nc] data] dsz] bsz] rem].
  destruct F as (F1 & F2 & V & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12).
  intros HJ. apply valid_stream_of_prefix; auto.
  - apply Forall_all_bytes. apply Forall_app. split; apply all_bytes_Forall; auto.
  - unfold Zlength in *. rewrite length_app. rewrite <- F5. lia.
  - intros i Hi. rewrite <- F5 in Hi. unfold Znth. rewrite app_nth1 by (unfold Zlength in F9; lia).
    fold (Znth i data). rewrite F8. apply fse_data_nth. rewrite <- F5. lia.
Qed.
