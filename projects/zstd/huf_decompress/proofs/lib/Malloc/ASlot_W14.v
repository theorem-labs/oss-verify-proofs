(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (17 recorded proofs replaced by written proofs (land_high_low, lor_shl_small, lor_small_shl and 14 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr Bytes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp MallocKit_A2 F_malloc_bigw F_malloc_big.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_A3.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASlot_W14 () := "C47Corelib7Program6Basics4flipK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1ZAmul_pow2_bits_lowC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z6bits_0K46Stdlib9micromega7EnvRing5PExpr01C56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z;lt_le_transC56Stdlib6ZArith6BinInt1Z?bits_above_log2C47Corelib4Init5Logic6eq_symC46Stdlib4Bool4Bool<andb_false_rC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init5Logic4True00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00C35stdpp4base6LookupI35stdpp9countable9Countable00C35stdpp4base;RelDecisionc59OSSVerify5KrLib6Malloc9ASlot_W14=land_high_lowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7SFModel@lor_disjoint_addC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z3addc59OSSVerify5KrLib6Malloc9ASlot_W14=lor_shl_smallC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8lor_commK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03c59OSSVerify5KrLib6Malloc9ASlot_W14=lor_small_shlC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z;shiftl_landC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~I35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C35stdpp8fin_maps:map_eq_iffC35stdpp8fin_maps@lookup_insert_eqC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9Morphisms?eq_proper_proxyC56Stdlib6ZArith6BinInt1Z7land_wdC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z:land_assocC59OSSVerify5KrLib6Malloc<MallocKit_AB:land_upperC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib3Lib5Bytes;lor_lt_pow2C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z8land_0_rC56Stdlib6ZArith6BinInt1Z@land_lor_distr_lK47Corelib4Init5Logic3and01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04C47Corelib7Classes9Morphisms:respectfulC56Stdlib6ZArith6BinInt1Z6lor_wdK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05c59OSSVerify5KrLib6Malloc9ASlot_W14<land_pg_maskC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsNReflexive_partial_app_morphismI45stdpp9bitvector;definitions2bv00C47Corelib4Init3Nat3addC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC47Corelib5Lists7ListDef6firstnC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6shiftrC35stdpp7tactics<f_equal_helpC47Corelib4Init9Datatypes7nat_indI47Corelib4Init9Datatypes3nat00C47Corelib5Lists7ListDef5skipnC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z:shiftr_0_rC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z=shiftr_shiftrC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega8ZifyInst7Inj_Z_ZC45stdpp9bitvector;definitions;bv_unsignedC47Corelib4Init9Datatypes3appC59OSSVerify5KrLib3Lib3MemAZ_to_le_bytes_modC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_W14>skipn_le_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_W14?firstn_le_bytesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<firstn_skipnC59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C45stdpp9bitvector;definitions8bv_swrapC59OSSVerify5KrLib6Malloc=F_malloc_free3sxvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge=Z_to_bv_mod64C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9pow_add_rK47Corelib7Numbers7BinNums1Z03C59OSSVerify5KrLib6Malloc=F_malloc_free;swrap32_eq'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=F_malloc_free9sxv_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep;wz_unsignedC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof04I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC47Corelib4Init9Datatypes2idC59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C35stdpp6option;from_optionC59OSSVerify5KrLib4Spec6Malloc7hav_addC1?~~~~~~~~~~~~~~~C35stdpp4base6insertC59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6shadow01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8stale_pgC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6NArith6BinNat1N3ltbC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC45stdpp;list_basics4list;list_filterC46Stdlib4Bool4Bool7Is_trueC35stdpp9decidable;Is_true_decC35stdpp4base6filterC56Stdlib6NArith6BinNat1N6ltb_ltK47Corelib4Init5Logic2ex01C47Corelib4Init9Datatypes3orbC46Stdlib4Bool4Bool:orb_true_rC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc:set_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9hdr_havocC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec6Malloc5staleC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbI47Corelib7Numbers7BinNums1N00C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7shadow0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC59OSSVerify5KrLib4Spec6Malloc9mask_uptoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rc59OSSVerify5KrLib6Malloc9ASlot_W14?mask_upto_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=sub_le_mono_rC35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9set_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9m_set_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>m_set_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>m_set_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?m_set_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8put_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9put_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4iterC59OSSVerify5KrLib4Spec6Malloc9set_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_set_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_set_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_activeC1?~~~~~~~~~~~~~~~C35stdpp4base:decide_relC35stdpp4base6decideK59OSSVerify5KrLib4Spec6Malloc4meta01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_W14=rec_hdr_havocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_AB=rec_set_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_ABEget_meta_rec_put_sameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_W14=rec_put_groupC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_W14=rec_set_slotsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib6Malloc<MallocKit_ABFget_meta_rec_put_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_AB>rec_set_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9add_slotsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_W144recFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_W144recAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_W148st_modelC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_W145stFinC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Lemma land_high_low x k y : 0 <= x -> 0 <= k -> 0 <= y < 2^k -> Z.land (x * 2^k) y = 0.
Proof.
  intros Hx Hk Hy. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases n k) as [LT|GE].
  - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - replace (Z.testbit y n) with false; [apply Bool.andb_false_r|].
    symmetry. destruct (Z.eq_dec y 0) as [->|NZ]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ k); [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma lor_shl_small x k y : 0 <= x -> 0 <= k -> 0 <= y < 2^k -> Z.lor (x * 2^k) y = x * 2^k + y.
Proof. intros. apply lor_disjoint_add. apply land_high_low; assumption. Qed.

Lemma lor_small_shl x k y : 0 <= x -> 0 <= k -> 0 <= y < 2^k -> Z.lor y (x * 2^k) = x * 2^k + y.
Proof. intros. rewrite Z.lor_comm. apply lor_shl_small; assumption. Qed.

Lemma lor_32 c : 0 <= c < 32 -> Z.lor c 32 = c + 32.
Proof. intros. change 32 with (1 * 2^5) at 1. rewrite lor_small_shl by lia. lia. Qed.

Lemma land_pg_mask q : 0 <= q < 2^52 -> Z.land (4096 * q) 18446744073709547520 = 4096 * q.
Proof.
  intros Hq. replace (4096 * q) with (Z.shiftl q 12) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  change 18446744073709547520 with (Z.shiftl (Z.ones 52) 12).
  rewrite <- Z.shiftl_land. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma hdr_byte_facts x ai : 0 <= x < 256 -> 0 <= ai < 32 ->
  0 <= Z.lor (Z.land x 18446744073709551584) ai < 256 /\ Z.land (Z.lor (Z.land x 18446744073709551584) ai) 31 = ai.
Proof.
  intros Hx Hai.
  assert (E : Z.land x 18446744073709551584 = Z.land x 224).
  { replace x with (Z.land x 255) at 1 by (change 255 with (Z.ones 8); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
    rewrite <- !Z.land_assoc. reflexivity. }
  rewrite E. pose proof (land_upper x 224 ltac:(lia) ltac:(lia)).
  split.
  - change 256 with (2^8). apply lor_lt_pow2; lia.
  - rewrite Z.land_lor_distr_l. rewrite <- Z.land_assoc. change (Z.land 224 31) with 0. rewrite Z.land_0_r. rewrite Z.lor_0_l.
    change 31 with (Z.ones 5). rewrite Z.land_ones, Z.mod_small by lia. reflexivity.
Qed.

Lemma tail_low16 sc cnt q : 0 <= sc < 48 -> 1 <= cnt <= 32 -> 0 <= q < 16 ->
  Z.lor (Z.lor (Z.land sc 63 * 2^6) (Z.lor (Z.land (cnt - 1) 31) 32)) (Z.land (4096 * q) 18446744073709547520)
  = (cnt - 1) + 32 + 64 * sc + 4096 * q.
Proof.
  intros Hsc Hc Hq.
  replace (Z.land sc 63) with sc by (change 63 with (Z.ones 6); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
  replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
  rewrite land_pg_mask by lia.
  replace 32 with (1 * 2^5) at 1 by reflexivity. rewrite (lor_small_shl 1 5 (cnt - 1)) by lia.
  rewrite (lor_shl_small sc 6) by (cbn; lia).
  replace (4096 * q) with (q * 2^12) by (cbn; lia). rewrite (lor_small_shl q 12) by (cbn; lia). cbn. lia.
Qed.

Lemma firstn_le_bytes n k z : firstn n (Z_to_le_bytes (n + k) z) = Z_to_le_bytes n z.
Proof. revert z. induction n as [|n IH]; intros z; [reflexivity|]. cbn [Z_to_le_bytes Nat.add firstn]. f_equal. apply IH. Qed.

Lemma skipn_le_bytes n k z : skipn n (Z_to_le_bytes (n + k) z) = Z_to_le_bytes k (Z.shiftr z (8 * Z.of_nat n)).
Proof.
  revert z. induction n as [|n IH]; intros z.
  - cbn. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [Z_to_le_bytes Nat.add skipn]. rewrite IH. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma tail_word_bytes (s0r : word) (L W W' : Z) :
  0 <= W < 2^64 -> 0 <= W' < 2^64 -> 0 <= L < 65536 ->
  bv_unsigned s0r mod 65536 = L -> W' mod 65536 = L -> Z.shiftr W' 16 = Z.shiftr W 16 ->
  le2 s0r ++ skipn 2 (le8 (wz W)) = le8 (wz W').
Proof.
  intros HW HW' HL HS HM HH.
  unfold le2, le8, word_to_le_bytes, wz. rewrite !unsigned_lit by lia.
  change 8%nat with (2 + 6)%nat. rewrite skipn_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul].
  rewrite <- (firstn_skipn 2 (Z_to_le_bytes (2 + 6) W')). rewrite firstn_le_bytes, skipn_le_bytes.
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul]. rewrite HH. f_equal.
  rewrite <- (Z_to_le_bytes_mod 2 (bv_unsigned s0r) 16) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 2 W' 16) by (cbn; lia).
  change (2^16) with 65536. rewrite HS, HM. reflexivity.
Qed.

Lemma word_low16_bytes W : 0 <= W < 2^64 -> firstn 2 (le8 (wz W)) = le2 (wz (W mod 65536)).
Proof.
  intros HW. unfold le2, le8, word_to_le_bytes, wz. rewrite !unsigned_lit by (try lia; Z.div_mod_to_equations; lia).
  change 8%nat with (2 + 6)%nat. rewrite firstn_le_bytes.
  change 65536 with (2^16). rewrite Z_to_le_bytes_mod by (cbn; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sllw2_word i : 0 <= i < 32 -> Z_to_bv 64 (bv_swrap 32 (Z.shiftl 2 (i mod 32))) = wz (sxv (2 ^ (i + 1))).
Proof.
  intros Hi. rewrite Z.mod_small by lia. change 2 with (2^1) at 1. rewrite Z.shiftl_mul_pow2, <- Z.pow_add_r by lia.
  replace (1 + i) with (i + 1) by lia. unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma subw_sxv_word a b : Z_to_bv 64 (bv_swrap 32 (bv_unsigned (wz (sxv a)) - bv_unsigned (wz (sxv b)))) = wz (sxv (a - b)).
Proof.
  rewrite !wz_unsigned by (apply sxv_range). unfold wz, sxv.
  rewrite <- (Z_to_bv_mod64 (bv_swrap 32 (bv_swrap 32 a mod 2 ^ 64 - bv_swrap 32 b mod 2 ^ 64))). f_equal.
  rewrite !swrap32_eq'. mlia.
Qed.

(* [comment removed for export] *)
Lemma cell_read_hdr_havoc_old : forall st b o,
  snd b mod 16 = 0 -> 0 <= o < 12 ->
  (forall v t, (r_cells (get_shadow st (fst b))) !! (snd b + o) = Some (v, t) -> (t < s_tick st)%N) ->
  exists h, cell_read (get_shadow (hdr_havoc b st) (fst b)) (snd b + o) = Unknown h.
Proof.
  intros st b o B16 Ho OLD. unfold hdr_havoc, upd_shadow. unfold get_shadow at 1. cbn [s_shadow set_shadow].
  rewrite lookup_insert_eq. cbn [default from_option id].
  unfold cell_read. cbn [r_cells r_hav r_havp].
  replace ((snd b + o) / 16) with (snd b / 16) by (Z.div_mod_to_equations; lia).
  rewrite lookup_insert_eq. cbn [default from_option id].
  replace ((snd b + o) mod 16) with o by (Z.div_mod_to_equations; lia).
  unfold hav_add. unfold stale. cbn [existsb fst snd].
  replace (o <? 12) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
  destruct (r_cells (get_shadow st (fst b)) !! (snd b + o)) as [[v t]|] eqn:E.
  - specialize (OLD v t eq_refl). replace (t <? s_tick st)%N with true by (symmetry; apply N.ltb_lt; exact OLD).
    cbn [orb]. rewrite Bool.orb_true_r. eexists; reflexivity.
  - cbn [orb]. rewrite Bool.orb_true_r. eexists; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section TAIL.
Variables (stT : mstate) (sc cnt ai ml : Z) (mt p : aptr) (r : region).
Let G := conc stT mt.
Let P := conc stT p.
Let AV := mask_upto ai.
Let FR := mask_upto (cnt - 1) - mask_upto ai.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis AI : 0 <= ai <= cnt - 1.
Hypothesis ML : 0 <= ml < 2^52.
Hypothesis MST : meta_slot stT mt.
Hypothesis REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml.
Hypothesis Hr : (s_regions stT) !! (fst p) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis P0 : 0 <= snd p.
Hypothesis P16 : snd p mod 16 = 0.
Hypothesis PEND : snd p + 16 <= round_up_pg (r_len r).
Hypothesis GNONE : (s_groups stT) !! p = None.
Hypothesis NOGRP : forall b' gh, (s_groups stT) !! b' = Some gh -> fst b' = fst p -> snd b' + 9 <= snd p \/ snd p + 9 <= snd b'.
Hypothesis OLD12 : forall o v t, snd p <= o < snd p + 12 ->
  (r_cells (get_shadow stT (fst p))) !! o = Some (v, t) -> (t < s_tick stT)%N.
Hypothesis UR : 0 <= usage stT sc < 2^60.
Hypothesis ACT : active stT sc = None.
Hypothesis TK : ticks_ok stT.

(* [comment removed for export] *)
Definition stA : mstate := hdr_havoc p stT.
Definition stB : mstate := set_usage sc (usage stT sc + cnt) stA.
Definition recA : meta := mkMeta None None (Some p) AV FR 0 0 0 ml.
Definition stC : mstate := put_meta mt recA stB.
Definition stD : mstate := put_group p (Some mt) ai stC.
Definition recF : meta := mkMeta (Some mt) (Some mt) (Some p) (AV - 1) FR (cnt - 1) 1 sc ml.
Definition stE : mstate := put_meta mt recF stD.
Definition stFin : mstate := set_active sc (Some mt) stE.

(* [comment removed for export] *)
Definition st_model : mstate :=
  let st := hdr_havoc p stT in
  let st1 := set_usage sc (usage st sc + cnt) st in
  let avail := mask_upto ai in
  let freed := mask_upto (cnt - 1) - avail in
  let st2 := upd_meta mt (fun r =>
               m_set_sizeclass sc (m_set_freeable 1 (m_set_last_idx (cnt - 1)
               (m_set_mem (Some p) (m_set_freed freed (m_set_avail avail r)))))) st1 in
  let st3 := put_group p (Some mt) ai st2 in
  let st4 := add_slots mt p (get_stride (get_meta_rec st3 mt)) cnt st3 in
  let st5 := upd_meta mt (fun r => m_set_avail (m_avail r - 1) r) st4 in
  let st6 := upd_meta mt (fun r => m_set_prev (Some mt) (m_set_next (Some mt) r)) st5 in
  set_active sc (Some mt) st6.

Lemma mask_upto_range k : 0 <= k <= 31 -> 1 <= mask_upto k < 2^32 /\ 2^k <= mask_upto k.
Proof.
  intros Hkk. unfold mask_upto. rewrite Z.pow_add_r by lia. change (2^1) with 2.
  assert (1 <= 2^k) by (change 1 with (2^0); apply Z.pow_le_mono_r; lia).
  assert (2^k <= 2^31) by (apply Z.pow_le_mono_r; lia).
  change (2^32) with (2 * 2^31). lia.
Qed.

Lemma AV_FR_range : 1 <= AV < 2^32 /\ 0 <= FR < 2^32 /\ 0 <= AV - 1 < 2^32.
Proof.
  pose proof (mask_upto_range ai ltac:(lia)) as [A1 A2]. pose proof (mask_upto_range (cnt - 1) ltac:(lia)) as [C1 C2].
  assert (mask_upto ai <= mask_upto (cnt - 1)).
  { unfold mask_upto. apply Z.sub_le_mono_r. apply Z.pow_le_mono_r; lia. }
  unfold AV, FR. lia.
Qed.

Lemma rec_set_slots st v q : get_meta_rec (set_slots v st) q = get_meta_rec st q.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W14 ()) ["CANSEC1"; "TAIL"] "h01qh12sth21vp;4p;6p;2g02BIj45Tg02Bgj64Tg01_5j20Tg00f=j41Tg02CHj23Tg006Tj22Tg02<WR0g00`aR1g028WR2g02=PR3g00NRR4g0295R5C5P2P3g02=iP4P5g029NE41014C1R4g02DEf2R5f0R3'3'2X01X24X10P5f1P3O3X01W2W1o"). Qed.
Lemma rec_put_group st b g a q : get_meta_rec (put_group b g a st) q = get_meta_rec st q.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W14 ()) ["CANSEC1"; "TAIL"] "h01ah11bh21gh31qh42stp;2g02CHj21Tg006Tj20Tg02<WR0g00`aR1g00bAR2g00NRR3g02DEf4R4f0R5'1'0X31X03X22X11X40P4f3f2f1P5O5X31W0W2W1W4o"). Qed.
Lemma rec_hdr_havoc st b q : get_meta_rec (hdr_havoc b st) q = get_meta_rec st q.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W14 ()) ["CANSEC1"; "TAIL"] "h01bh11qh22stp;2g02CHj21Tg006Tj20Tg02<WR0g00`aR1g02DEf2R2f0R3'1'0X11X01X20P2f1P3O3X11W0W2o"). Qed.

Lemma st_model_eq_rec q : get_meta_rec st_model q = get_meta_rec stFin q.
Proof.
  unfold st_model, stFin, stE, stD, stC, stB, stA. cbv zeta. unfold upd_meta, add_slots.
  rewrite !rec_set_active.
  destruct (decide (q = mt)) as [->|NE].
  - rewrite !get_meta_rec_put_same, rec_set_slots, rec_put_group, get_meta_rec_put_same, rec_set_usage, rec_hdr_havoc, REC.
    unfold recF. cbv [m_set_prev m_set_next m_set_avail m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen].
    replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
    replace (Z.land sc 63) with sc by (change 63 with (Z.ones 6); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
    change (Z.land 1 1) with 1. reflexivity.
  - rewrite !get_meta_rec_put_other, rec_set_slots, !rec_put_group, !get_meta_rec_put_other by congruence. reflexivity.
Qed.

(* [comment removed for export] *)
Definition tailW : list (Z * Z) :=
  [(CTX + 464 + 8 * sc, CTX + 464 + 8 * sc + 8); (G, G + 40); (P, P + 9); (CTX + 80 + 8 * sc, CTX + 80 + 8 * sc + 8)]%Z.
End TAIL.


End CANSEC1.
