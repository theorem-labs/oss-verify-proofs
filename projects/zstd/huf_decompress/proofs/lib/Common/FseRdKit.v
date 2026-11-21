(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (20 recorded proofs replaced by written proofs (byte_lit, sxb_lit, swrap32_u32_cases and 17 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_FseRdKit () := "C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7bv_wrapI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedC47Corelib4Init5Logic8eq_ind_rK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C45stdpp9bitvector;definitions9bv_signedC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z9mod_smallK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z7mod_addC47Corelib4Init5Logic6eq_indC45stdpp9bitvector;definitions>Z_to_bv_signedK47Corelib7Numbers7BinNums1Z03C59OSSVerify5KrLib3Lib3Mem3sxbC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib6Common:FseWalkKit:swrap32_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common8FseRdKitAswrap32_u32_casesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landc59OSSVerify5KrLib6Common8FseRdKitAswrap32_u32_mod32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Bytes?land_mod_pow2_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9land_commC56Stdlib6ZArith6BinInt1Z3oppK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03C56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7mod_0_lC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z>mod_unique_posC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z7mod_mulC59OSSVerify5KrLib6Common:FseWalkKit;swrap32_eqmC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_mulK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC59OSSVerify5KrLib4Spec9FseNCount8to_shortC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6mod_eqK47Corelib4Init5Logic2ex01C56Stdlib6ZArith4Zdiv1Z>mod_mod_divideC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib3Lib3MemAZ_to_le_bytes_modC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le2C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appc59OSSVerify5KrLib6Common8FseRdKit<le2_to_shortC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib3Lib3Arr3updC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:FseWalkKit4u16sC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount7upd_natC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z6ltb_geC59OSSVerify5KrLib3Lib7ZBridgeBzb_lxor_pow2_smallC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith6BinInt1Z3b2zC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC46Stdlib6ZArith:ZArith_dec;Z_lt_le_decC56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1ZAmod_pow2_bits_lowC46Stdlib4Bool4Bool<andb_false_rC59OSSVerify5KrLib3Lib5BytesBtestbit_high_falseC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'C56Stdlib6ZArith8Zbitwise1Z<add_lor_landC56Stdlib6ZArith6BinInt1Z3lorK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib6Common:FseWalkKit9wrap32_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common8FseRdKit@lor_add_disjointC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8lor_commC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common8FseRdKit7sxb_litC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common8FseRdKit8byte_litC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C59OSSVerify5KrLib4Spec9FseLemmas7land_31C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natc59OSSVerify5KrLib6Common8FseRdKit8all_fromC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC46Stdlib9micromega8ZifyInst7Inj_Z_ZC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes?andb_true_introI59OSSVerify5KrLib4Spec9FseNCount3res00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount4ZnthC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec9FseNCount3res01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec9FseNCount3res03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount8readLE32C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common8FseRdKit4le32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseLemmas9all_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount;r_bitStreamC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount;r_thresholdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount;r_remainingC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount3u32C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec9FseNCount4flow00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec9FseNCount:r_bitCountC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount8r_nbBitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount4r_ncC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount9r_charnumC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount5storeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec9FseNCount9highbit32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount6assertC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec9FseNCount4bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount4r_ipC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec9FseNCount6rstate01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount6reloadC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec9FseNCount4flow01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount<rcount_blockC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common8FseRdKit=rcount_decodeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common8FseRdKit;rcount_restC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C56Stdlib6ZArith6BinInt1Z3eqbK59OSSVerify5KrLib4Spec9FseNCount4flow02C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI59OSSVerify5KrLib4Spec9FseNCount6rstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount;r_previous0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount5shr32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount7ZlengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseLemmas6land_7C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_posC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC59OSSVerify5KrLib4Spec9FseLemmas8shr32_okC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic9False_indK46Stdlib9micromega5Tauto8GFormula01c59OSSVerify5KrLib6Common8FseRdKit:reload_posC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbK46Stdlib9micromega5Tauto8GFormula0:K46Stdlib9micromega5Tauto4kind02C59OSSVerify5KrLib4Spec<FseReadSound3CTLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<FseReadSound3POSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<FseReadSound3pwsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z=pow_le_mono_r".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma byte_lit : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. intros c Hc. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

(* [comment removed for export] *)
Lemma sxb_lit : forall c, 0 <= c < 256 ->
  bv_unsigned (sxb (Z_to_bv 8 c)) = if c <? 128 then c else c + (2^64 - 256).
Proof.
  intros c Hc. unfold sxb. rewrite Z_to_bv_unsigned.
  assert (S : bv_signed (Z_to_bv 8 c) = if c <? 128 then c else c - 256).
  { rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 8) with 256. change (256 / 2) with 128.
    destruct (Z.ltb_spec c 128).
    - rewrite Z.mod_small by lia. lia.
    - replace (c + 128) with ((c - 128) + 1 * 256) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia. }
  rewrite S. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  destruct (Z.ltb_spec c 128).
  - apply Z.mod_small. lia.
  - replace (c - 256) with ((c + (2^64 - 256)) + (-1) * 2^64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma swrap32_u32_cases : forall bs, 0 <= bs < 2^32 ->
  bv_swrap 32 bs mod 18446744073709551616 = (if bs <? 2^31 then bs else bs + (2^64 - 2^32)).
Proof.
  intros bs Hb. rewrite swrap32_eq. change 18446744073709551616 with (2^64).
  change 2147483648 with (2^31). change 4294967296 with (2^32).
  destruct (Z.ltb_spec bs (2^31)).
  - rewrite (Z.mod_small (bs + 2^31)) by lia. rewrite Z.mod_small by lia. lia.
  - replace (bs + 2^31) with ((bs - 2^31) + 1 * 2^32) by lia. rewrite Z.mod_add by lia.
    rewrite (Z.mod_small (bs - 2^31)) by lia.
    replace (bs - 2^31 - 2^31) with ((bs + (2^64 - 2^32)) + (-1) * 2^64) by lia. rewrite Z.mod_add by lia.
    apply Z.mod_small. lia.
Qed.

Lemma swrap32_u32_mod32 : forall bs, 0 <= bs < 2^32 -> (bv_swrap 32 bs mod 18446744073709551616) mod 2^32 = bs.
Proof.
  intros bs Hb. rewrite swrap32_u32_cases by lia. destruct (bs <? 2^31).
  - apply Z.mod_small. lia.
  - replace (bs + (2^64 - 2^32)) with (bs + (2^32 - 1) * 2^32) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma land_swrap32 : forall bs k, 0 <= bs < 2^32 -> 0 <= k < 2^32 ->
  Z.land (bv_swrap 32 bs mod 18446744073709551616) k = Z.land bs k.
Proof.
  intros bs k Hb Hk. rewrite (Z.land_comm _ k), (Z.land_comm bs k).
  rewrite <- (land_mod_pow2_r k (bv_swrap 32 bs mod 18446744073709551616) 32) by lia.
  rewrite swrap32_u32_mod32 by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma addw_neg : forall d r, - 2^31 <= d <= 0 -> 0 <= r < 2^31 -> 0 <= r + d ->
  bv_swrap 32 (d mod 18446744073709551616 + r) = r + d.
Proof.
  intros d r Hd Hr Hs. apply swrap32_eqm; [lia|].
  change 18446744073709551616 with (2^64). change 4294967296 with (2^32).
  destruct (Z.eq_dec d 0) as [->|N].
  - rewrite Z.mod_0_l by lia. replace (0 + r - (r + 0)) with 0 by lia. reflexivity.
  - assert (E : d mod 2^64 = d + 2^64) by (symmetry; apply (Z.mod_unique_pos d (2^64) (-1) (d + 2^64)); lia).
    rewrite E. replace (d + 2^64 + r - (r + d)) with (2^32 * 2^32) by lia. apply Z.mod_mul. lia.
Qed.

(* [comment removed for export] *)
Lemma shl32_shr31 : forall c, 0 <= c < 2^31 -> (c ≪ 32 mod 18446744073709551616) ≫ 31 = 2 * c.
Proof.
  intros c Hc. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change 18446744073709551616 with (2^64).
  rewrite Z.mod_small by lia. replace (c * 2^32) with ((2 * c) * 2^31) by lia. apply Z.div_mul. lia.
Qed.

(* [comment removed for export] *)
Lemma le2_to_short : forall v, le2 (Z_to_bv 64 v) = le2 (Z_to_bv 64 (to_short v)).
Proof.
  intros v. unfold le2.
  rewrite <- (Z_to_le_bytes_mod 2 (bv_unsigned (Z_to_bv 64 v)) 16) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 2 (bv_unsigned (Z_to_bv 64 (to_short v))) 16) by (cbn; lia).
  f_equal. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  rewrite !(Z.mod_mod_divide _ (2^64) (2^16)) by (exists (2^48); reflexivity).
  unfold to_short. rewrite (Z.mod_eq (v + 2^15) (2^16)) by lia.
  replace (v + 2^15 - 2^16 * ((v + 2^15) / 2^16) - 2^15) with (v + (- ((v + 2^15) / 2^16)) * 2^16) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma u16s_upd_short : forall nc i v,
  u16s (upd (map (Z_to_bv 64) nc) i (Z_to_bv 64 v)) = u16s (map (Z_to_bv 64) (upd_nat i (to_short v) nc)).
Proof.
  induction nc as [|a nc IH]; intros [|i] v; cbn -[le2]; try reflexivity.
  - rewrite le2_to_short. reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma slt_small : forall a b, 0 <= a < 2^63 -> 0 <= b < 2^63 ->
  (Z.lxor a 9223372036854775808 <? Z.lxor b 9223372036854775808) = (a <? b).
Proof.
  intros a b Ha Hb. change 9223372036854775808 with (2^63).
  rewrite !zb_lxor_pow2_small by lia.
  destruct (Z.ltb_spec a b); [apply Z.ltb_lt| apply Z.ltb_ge]; lia.
Qed.

(* [comment removed for export] *)
Lemma mask_sel : forall (b : bool) mx, 0 <= mx < 2^64 ->
  Z.land ((Z.b2z b + -1) mod 18446744073709551616) mx = if b then 0 else mx.
Proof.
  intros b mx Hm. destruct b; cbn [Z.b2z].
  - reflexivity.
  - change ((0 + -1) mod 18446744073709551616) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
    apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lor_add_disjoint : forall a b n, 0 <= n -> 0 <= a < 2^n -> b mod 2^n = 0 -> Z.lor a b = a + b.
Proof.
  intros a b n Hn Ha Hb.
  assert (L0 : Z.land a b = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_le_dec i n) as [Lt|Ge].
    - assert (Z.testbit b i = false).
      { rewrite <- (Z.mod_pow2_bits_low b n i) by lia. rewrite Hb. apply Z.bits_0. }
      rewrite H. apply andb_false_r.
    - assert (Z.testbit a i = false) by (apply (testbit_high_false a n i); lia).
      rewrite H. reflexivity. }
  pose proof (Z.add_lor_land a b) as E. rewrite L0 in E. lia.
Qed.

(* [comment removed for export] *)
Lemma le32_lb_raw : forall b0 b1 b2 b3, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  bv_wrap 32 (Z.lor (Z.lor (bv_unsigned (sxb (Z_to_bv 8 b3)) ≪ 24 mod 18446744073709551616)
                          (bv_unsigned (Z_to_bv 8 b2) ≪ 16 mod 18446744073709551616))
                   (Z.lor (bv_unsigned (Z_to_bv 8 b1) ≪ 8 mod 18446744073709551616) (bv_unsigned (Z_to_bv 8 b0))))
  = b0 + 2^8 * b1 + 2^16 * b2 + 2^24 * b3.
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3.
  rewrite !byte_lit, sxb_lit by assumption. rewrite !Z.shiftl_mul_pow2 by lia.
  change 18446744073709551616 with (2^64).
  rewrite (Z.mod_small (b2 * 2^16)) by lia. rewrite (Z.mod_small (b1 * 2^8)) by lia.
  set (S3 := ((if b3 <? 128 then b3 else b3 + (2^64 - 256)) * 2^24) mod 2^64).
  assert (ES3 : S3 = b3 * 2^24 + (if b3 <? 128 then 0 else 2^64 - 2^32)).
  { subst S3. destruct (b3 <? 128).
    - rewrite Z.mod_small by lia. lia.
    - replace ((b3 + (2^64 - 256)) * 2^24) with ((b3 * 2^24 + (2^64 - 2^32)) + (2^24 - 1) * 2^64) by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (M3 : S3 mod 2^24 = 0).
  { rewrite ES3. destruct (b3 <? 128).
    - rewrite Z.add_0_r. apply Z.mod_mul. lia.
    - replace (b3 * 2^24 + (2^64 - 2^32)) with ((b3 + (2^40 - 2^8)) * 2^24) by lia. apply Z.mod_mul. lia. }
  rewrite (Z.lor_comm (b1 * 2^8) b0). rewrite (lor_add_disjoint b0 (b1 * 2^8) 8) by (try lia; apply Z.mod_mul; lia).
  rewrite (Z.lor_comm S3 (b2 * 2^16)). rewrite (lor_add_disjoint (b2 * 2^16) S3 24) by (try lia; exact M3).
  rewrite Z.lor_comm. rewrite (lor_add_disjoint (b0 + b1 * 2^8) (b2 * 2^16 + S3) 16).
  2: lia. 2: lia.
  2:{ rewrite ES3. destruct (b3 <? 128).
      - replace (b2 * 2^16 + (b3 * 2^24 + 0)) with ((b2 + b3 * 2^8) * 2^16) by lia. apply Z.mod_mul. lia.
      - replace (b2 * 2^16 + (b3 * 2^24 + (2^64 - 2^32))) with ((b2 + b3 * 2^8 + (2^48 - 2^16)) * 2^16) by lia. apply Z.mod_mul. lia. }
  rewrite wrap32_eq. change 4294967296 with (2^32). rewrite ES3. destruct (b3 <? 128).
  - rewrite Z.mod_small by lia. lia.
  - replace (b0 + b1 * 2^8 + (b2 * 2^16 + (b3 * 2^24 + (2^64 - 2^32)))) with ((b0 + b1 * 2^8 + b2 * 2^16 + b3 * 2^24) + (2^32 - 1) * 2^32) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma clamp_bc : forall bc d, -16 <= d <= 0 -> 0 <= bc < 2^31 ->
  Z.land ((bc + (d mod 18446744073709551616) ≪ 3) mod 18446744073709551616) 31 = (bc + 8 * d) mod 32.
Proof.
  intros bc d Hd Hbc. rewrite land_31. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
  change 18446744073709551616 with (2^64).
  rewrite (Z.mod_mod_divide _ (2^64) 32) by (exists (2^59); reflexivity).
  destruct (Z.eq_dec d 0) as [->|N].
  - rewrite Z.mod_0_l by lia. f_equal; lia.
  - assert (E : d mod 2^64 = d + 2^64).
    { symmetry. apply (Z.mod_unique_pos d (2^64) (-1) (d + 2^64)); lia. }
    rewrite E. replace (bc + (d + 2^64) * 8) with ((bc + 8 * d) + 2^62 * 32) by lia.
    rewrite Z.mod_add by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint all_from (P : Z -> bool) (x : Z) (n : nat) : bool :=
  match n with O => true | S k => P x && all_from P (x + 1) k end.

Lemma brute_range : forall (P : Z -> bool) lo (n : Z),
  all_from P lo (Z.to_nat n) = true -> forall r, lo <= r < lo + n -> P r = true.
Proof.
  intros P lo n H r Hr.
  assert (G : forall k x, all_from P x k = true -> forall y, x <= y < x + Z.of_nat k -> P y = true).
  { induction k as [|k IH]; intros x Hk y Hy; [lia|]. cbn [all_from] in Hk. apply andb_true_iff in Hk. destruct Hk as [H1 H2].
    destruct (Z.eq_dec y x) as [->|N]; [exact H1| apply (IH (x + 1) H2); lia]. }
  apply (G _ _ H). lia.
Qed.

Ltac brute_reg n r lo cnt g :=
  let w := getreg n in
  lazymatch w with
  | Z_to_bv 64 ?e =>
      let F := eval pattern r in e in
      lazymatch F with
      | ?f r =>
          let H := fresh "BR" in
          assert (H : forall r0, lo <= r0 < lo + cnt -> (f r0 =? g r0) = true)
            by (apply (brute_range (fun r0 => f r0 =? g r0) lo cnt); vm_compute; reflexivity);
          replace e with (g r) by (symmetry; apply Z.eqb_eq; apply H; lia);
          clear H
      end
  | _ => fail "brute_reg: register" n "holds" w
  end.

(* [comment removed for export] *)
Definition sm1 (r : Z) : Z := Z.lor r (r ≫ 1).
Definition sm2 (r : Z) : Z := Z.lor (sm1 r) (sm1 r ≫ 2).
Definition sm3 (r : Z) : Z := Z.lor (sm2 r) (sm2 r ≫ 4).
Definition sm4 (r : Z) : Z := Z.lor (sm3 r) (sm3 r ≫ 8).
Definition sm5 (r : Z) : Z := Z.lor (sm4 r) (sm4 r ≫ 16).

(* [comment removed for export] *)
(* [comment removed for export] *)

Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
Definition le32 (buf : list Z) (ip : Z) : Z :=
  Znth ip buf + 2^8 * Znth (ip+1) buf + 2^16 * Znth (ip+2) buf + 2^24 * Znth (ip+3) buf.

Lemma readLE32_le32 : forall buf ip, 0 <= ip -> ip + 4 <= zlen buf -> readLE32 buf ip = Ok (le32 buf ip).
Proof.
  intros buf ip H1 H2. unfold readLE32, le32, FseNCount.Zlength.
  replace ((0 <=? ip) && (ip + 4 <=? zlen buf)) with true; [reflexivity|].
  symmetry. apply andb_true_intro. split; [apply Z.leb_le| apply Z.leb_le]; lia.
Qed.

Lemma le32_range : forall buf ip, all_bytes buf -> 0 <= le32 buf ip < 2^32.
Proof.
  intros buf ip HB. unfold le32.
  pose proof (HB ip). pose proof (HB (ip+1)). pose proof (HB (ip+2)). pose proof (HB (ip+3)).
  change (2^8) with 256. change (2^16) with 65536. change (2^24) with 16777216. change (2^32) with 4294967296. lia.
Qed.

Section RdModel.
  Variable buf : list Z.
  Variable maxSV1 : Z.
  Let h : Z := FseNCount.Zlength buf.

  (* [comment removed for export] *)
  Definition rcount_decode (s : rstate) : Z * Z :=
    let threshold := r_threshold s in
    let max := 2 * threshold - 1 - r_remaining s in
    let bs := r_bitStream s in
    if Z.land bs (threshold - 1) <? u32 max
    then (Z.land bs (threshold - 1), r_bitCount s + (r_nbBits s - 1))
    else (let c := Z.land bs (2 * threshold - 1) in
          ((if threshold <=? c then c - max else c), r_bitCount s + r_nbBits s)).

  Definition rcount_rest (s : rstate) (count0 bc : Z) : res (flow rstate) :=
    let threshold := r_threshold s in
    let bs := r_bitStream s in
    let count := count0 - 1 in
    let remaining := if 0 <=? count then r_remaining s - count else r_remaining s + count in
    let! nc' := store (r_nc s) (r_charnum s) (to_short count) in
    let charnum := r_charnum s + 1 in
    let previous0 := (count =? 0) in
    let! upd := (if remaining <? threshold then
                   if remaining <=? 1 then Ok None
                   else let! hb := highbit32 remaining in
                        let nbBits := hb + 1 in
                        let! _ := assert ((0 <=? nbBits - 1) && (nbBits - 1 <? 31)) in
                        Ok (Some (2^(nbBits - 1), nbBits))
                 else Ok (Some (threshold, r_nbBits s))) in
    match upd with
    | None => Ok (Brk (FseNCount.mkR nc' (r_ip s) bs bc charnum remaining threshold (r_nbBits s) previous0))
    | Some (threshold', nbBits') =>
        let s1 := FseNCount.mkR nc' (r_ip s) bs bc charnum remaining threshold' nbBits' previous0 in
        if maxSV1 <=? charnum then Ok (Brk s1)
        else let! s2 := reload buf s1 in Ok (Cont s2)
    end.

  Lemma rcount_block_split : forall s,
    rcount_block buf maxSV1 s = rcount_rest s (fst (rcount_decode s)) (snd (rcount_decode s)).
  Proof.
    intros s. unfold rcount_block, rcount_rest, rcount_decode.
    destruct (Z.land (r_bitStream s) (r_threshold s - 1) <? u32 (2 * r_threshold s - 1 - r_remaining s)); reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition reload_pos (ip bc : Z) : Z * Z :=
    if (ip <=? h - 7) || (ip + Z.shiftr bc 3 <=? h - 4)
    then (ip + Z.shiftr bc 3, Z.land bc 7)
    else (h - 4, Z.land (bc - 8 * (h - 4 - ip)) 31).

  Lemma reload_inv : forall s s2, all_bytes buf -> reload buf s = Ok s2 ->
    0 <= r_ip s -> r_ip s + 4 <= h -> 0 <= r_bitCount s ->
    let ip' := fst (reload_pos (r_ip s) (r_bitCount s)) in
    let bc' := snd (reload_pos (r_ip s) (r_bitCount s)) in
    0 <= ip' /\ ip' + 4 <= h /\ 0 <= bc' < 32 /\
    s2 = FseNCount.mkR (r_nc s) ip' (le32 buf ip' / 2^bc') bc' (r_charnum s) (r_remaining s) (r_threshold s) (r_nbBits s) (r_previous0 s).
  Proof.
    intros s s2 HB E H1 H2 H3. unfold reload in E. fold h in E. unfold reload_pos. cbv zeta.
    rewrite Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *. rewrite land_7, land_31 in *.
    assert (Q : 0 <= r_bitCount s / 8) by (apply Z.div_pos; lia).
    destruct ((r_ip s <=? h - 7) || (r_ip s + r_bitCount s / 8 <=? h - 4)) eqn:EC; cbn [fst snd].
    - pose proof (Z.mod_pos_bound (r_bitCount s) 8 ltac:(lia)) as MB.
      unfold readLE32 in E. fold h in E.
      destruct ((0 <=? r_ip s + r_bitCount s / 8) && (r_ip s + r_bitCount s / 8 + 4 <=? h)) eqn:EB; cbn [bind] in E; [|discriminate].
      apply andb_true_iff in EB. destruct EB as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2.
      rewrite shr32_ok in E by lia. cbn [bind] in E. injection E as <-.
      split; [lia|]. split; [lia|]. split; [lia|]. reflexivity.
    - pose proof (Z.mod_pos_bound (r_bitCount s - 8 * (h - 4 - r_ip s)) 32 ltac:(lia)) as MB.
      unfold readLE32 in E. fold h in E.
      destruct ((0 <=? h - 4) && (h - 4 + 4 <=? h)) eqn:EB; cbn [bind] in E; [|discriminate].
      rewrite shr32_ok in E by lia. cbn [bind] in E. injection E as <-.
      apply andb_true_iff in EB. destruct EB as [B1 B2]. apply Z.leb_le in B1.
      split; [lia|]. split; [lia|]. split; [lia|]. reflexivity.
  Qed.
End RdModel.

(* [comment removed for export] *)
Lemma ctl_pos_ranges : forall buf msv1 nc0 tl s, 5 <= tl <= 15 -> CTL msv1 nc0 tl s -> POS buf s ->
  2 <= r_nbBits s <= 16 /\ r_threshold s = 2^(r_nbBits s - 1) /\ 2 <= r_threshold s <= 32768 /\
  r_threshold s <= r_remaining s < 2 * r_threshold s /\ r_remaining s <= 32769 /\
  0 <= r_charnum s < msv1 /\ length (r_nc s) = length nc0 /\
  0 <= r_ip s /\ r_ip s + 4 <= zlen buf /\ 0 <= r_bitCount s /\ 0 <= r_bitStream s < 2^32.
Proof.
  intros buf msv1 nc0 tl s Htl (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9) (P1 & P2 & P3 & P4 & P5 & P6).
  assert (T1 : 2 ^ tl <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia). change (2^15) with 32768 in T1.
  assert (T2 : 2 ^ 1 <= 2 ^ (r_nbBits s - 1) <= 2 ^ tl) by (split; apply Z.pow_le_mono_r; lia).
  change (2^1) with 2 in T2. unfold FseNCount.Zlength in P2.
  repeat split; try lia; try assumption.
Qed.
