(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (21 recorded proofs replaced by written proofs (bounces_set, bouncess_set, sextw_sxv0 and 18 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast MallocTree MallocKit_A MallocKit_AB MallocKit_A2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MallocKit_A3 () := "C47Corelib7Program6Basics4flipC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC35stdpp8fin_maps@lookup_insert_eqC35stdpp4gmap;gmap_finmapC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC35stdpp8fin_maps@insert_delete_eqI35stdpp4gmap4gmap00I35stdpp9countable9Countable00C35stdpp4base;RelDecisionC35stdpp4base4fmapC35stdpp8fin_maps@lookup_insert_neC35stdpp4gmapBgmap_partial_alterC56Stdlib6ZArith6BinInt1Z8eqb_specC56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init9Datatypes7reflect00C47Corelib4Init9Datatypes2idC35stdpp8fin_maps:map_insertC59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9c_bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01K47Corelib4Init5Logic2eq01C47Corelib4Init5Logic3notC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic9False_indC59OSSVerify5KrLib4Spec6Malloc?set_bounces_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6mstate01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_bounceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7bouncesC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C35stdpp4base6insertC35stdpp4base6lookupC35stdpp6option;from_optionI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K47Corelib4Init9Datatypes6option02K47Corelib7Numbers7BinNums8positive01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib6Malloc9MallocRep2b8C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3seqC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib3Lib3Arr3updC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC56Stdlib5Arith8PeanoNat3Nat3eqbC56Stdlib5Arith8PeanoNat3Nat8eqb_specC46Stdlib9micromega;ZifyClasses9not_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegc59OSSVerify5KrLib6Malloc<MallocKit_A3;bounces_setC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01C59OSSVerify5KrLib6Malloc9MallocRep;map_seq_updC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib6Malloc9MallocRep8bouncessC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula07I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxK47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op203C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib6Malloc=F_malloc_free3sxvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC47Corelib7Classes?RelationClasses=eq_TransitiveC45stdpp9bitvector;definitions8bv_swrapC45stdpp9bitvector;definitions7Z_to_bvC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC46Stdlib;setoid_ring>Algebra_syntax8equalityC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC59OSSVerify5KrLib6Malloc=F_malloc_free9sxv_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep;wz_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=F_malloc_free9sextw_sxvC1?~~~~~~~~~~~~~~~C46Stdlib;setoid_ring6Ncring;eq_notationC46Stdlib;setoid_ring6Ncring>ring_plus_compC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3oppC46Stdlib;setoid_ring>Ncring_initial4ZopsC46Stdlib;setoid_ring>Ncring_initial2ZrI47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib6Malloc=F_malloc_free:sextw_sxv'C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega:ZMicromega;ZArithProof04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr06C59OSSVerify5KrLib6Malloc=F_malloc_free;swrap32_eq'C1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib3Lib7ZBridge=Z_to_bv_mod64C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05I47Corelib4Init9Datatypes:comparison00C59OSSVerify5KrLib4Spec6Malloc9get_groupC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_groupsC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps:map_deleteC35stdpp4base6deleteC59OSSVerify5KrLib4Spec6MallocDset_group_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9del_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9put_groupC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC59OSSVerify5KrLib6Malloc<MallocKit_AB5mw_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_wordC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_ABBmeta_word_last_idxC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=F_malloc_free9sxv_mod32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK47Corelib4Init5Logic3and01C59OSSVerify5KrLib4Spec6Malloc9mask_uptoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4lxorC47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z;lxor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z9log2_lxorC56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z;le_lt_transK46Stdlib9micromega5Tauto8GFormula09I47Corelib4Init5Logic4True00C59OSSVerify5KrLib6Malloc<MallocKit_AB<meta_word_scC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_AB?meta_word_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool<andb_false_rC56Stdlib6ZArith6BinInt1Z>testbit_even_0C56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith6BinInt1ZAtestbit_even_succC56Stdlib6ZArith6BinInt1Z;shiftr_specC56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib4Spec6Malloc9span_loopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith4Znat5Nat2Z8inj_succC47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith6BinInt1Z3lorC47Corelib4Init9Datatypes3orbC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6ltb_ltC46Stdlib4Bool4Bool;orb_false_lC46Stdlib4Bool4Bool;andb_true_rC56Stdlib6ZArith6BinInt1Z?shiftl_spec_lowC56Stdlib6ZArith6BinInt1Z<testbit_onesC56Stdlib6ZArith6BinInt1Z8lor_specC56Stdlib6ZArith6BinInt1Z@testbit_mod_pow2C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z7mod_modC56Stdlib6ZArith6BinInt1Z7mod_addC56Stdlib6ZArith6BinInt1Z8mul_commC56Stdlib6ZArith6BinInt1Z9rem_mul_rC45stdpp9bitvector;definitions@Z_to_bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC59OSSVerify5KrLib3Lib3Mem3le1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;land_nonnegK47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z5ldiffC56Stdlib6ZArith6BinInt1Z8ldiff_leC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z:ldiff_specc59OSSVerify5KrLib6Malloc<MallocKit_A3=swrap32_smallC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z4evenC56Stdlib6ZArith6BinInt1Z3oddC46Stdlib6ZArith4Zdiv8Zmod_oddC46Stdlib6ZArith5Zeven>Zeven_odd_boolc59OSSVerify5KrLib6Malloc<MallocKit_A3:land1_mod2C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma bounces_set st i v j :
  bounces (set_bounce i v st) j = if Z.eqb j i then v else bounces st j.
Proof.
  unfold bounces, set_bounce, upd_ctx. cbn [ctx s_ctx c_bounces set_bounces_map].
  destruct (Z.eqb_spec j i); subst.
  - rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma bouncess_set st i v : 0 <= i < 32 ->
  bouncess (set_bounce i v st) = upd (bouncess st) (Z.to_nat i) (b8 v).
Proof.
  intros Hi. unfold bouncess.
  replace (Z.to_nat i) with (Z.to_nat i - 0)%nat by lia.
  apply (map_seq_upd (fun j => b8 (bounces st (Z.of_nat j)))); [|lia].
  intros j Hj. rewrite bounces_set.
  destruct (Z.eqb_spec (Z.of_nat j) i); destruct (Nat.eqb_spec j (Z.to_nat i)); try reflexivity; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sextw_sxv0 v : Z_to_bv 64 (bv_swrap 32 (sxv v + 0)) = wz (sxv v).
Proof. rewrite <- (wz_unsigned (sxv v)) at 1 by (apply sxv_range). apply sextw_sxv. Qed.
Lemma sextw_sxv1 v : Z_to_bv 64 (bv_swrap 32 (sxv v)) = wz (sxv v).
Proof. rewrite <- (wz_unsigned (sxv v)) at 1 by (apply sxv_range). apply sextw_sxv'. Qed.

(* [comment removed for export] *)
Lemma addiw_small v c : 0 <= v < 2^31 -> -2^31 <= v + c < 2^31 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 v) + c)) = Z_to_bv 64 ((v + c) mod 2^64).
Proof.
  intros Hv Hc. rewrite unsigned_lit by lia. rewrite <- (Z_to_bv_mod64 (bv_swrap 32 (v + c))). f_equal.
  rewrite swrap32_eq'.
  change (2^64) with 18446744073709551616 in *. change (2^32) with 4294967296 in *. change (2^31) with 2147483648 in *.
  Z.div_mod_to_equations. lia.
Qed.

End CANSEC1.
Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Lemma set_group_ai_eq st b gh ai :
  get_group st b = Some gh -> set_group_active_idx b ai st = put_group b (g_meta gh) ai (del_group b st).
Proof.
  intros Hb. unfold set_group_active_idx, put_group, del_group. rewrite Hb. cbn [s_groups set_groups].
  rewrite insert_delete_eq. reflexivity.
Qed.

Lemma put_group_del st b mo ai : put_group b mo ai (del_group b st) = put_group b mo ai st.
Proof. unfold put_group, del_group. cbn [s_groups set_groups]. rewrite insert_delete_eq. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma meta_word_mod32 mr : mw_ok mr -> meta_word mr mod 32 = m_last_idx mr.
Proof. intros MW. rewrite <- (meta_word_last_idx mr MW). change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma sxv_inj a b : 0 <= a < 2^32 -> 0 <= b < 2^32 -> sxv a = sxv b -> a = b.
Proof.
  intros Ha Hb E. pose proof (sxv_mod32 a) as Ea. pose proof (sxv_mod32 b) as Eb. rewrite E in Ea. rewrite Ea in Eb.
  rewrite !Z.mod_small in Eb by lia. exact Eb.
Qed.

Lemma mask_upto_range k : 0 <= k <= 31 -> 0 < mask_upto k < 2^32.
Proof.
  intros Hk. unfold mask_upto. split.
  - assert (2 ^ 1 <= 2 ^ (k + 1)) by (apply Z.pow_le_mono_r; lia). change (2^1) with 2 in H. lia.
  - assert (2 ^ (k + 1) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia). lia.
Qed.


Lemma land_mask_31 x : 0 <= x -> x mod 32 = Z.land x 31.
Proof. intros. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma lxor_range31 a b : 0 <= a < 2^31 -> 0 <= b < 2^31 -> 0 <= Z.lxor a b < 2^31.
Proof.
  intros Ha Hb. split; [apply Z.lxor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lxor a b) 0) as [->|NE]; [lia|].
  assert (Ha' : Z.log2 a < 31) by (destruct (Z.eq_dec a 0) as [->|]; [cbn; lia| apply Z.log2_lt_pow2; lia]).
  assert (Hb' : Z.log2 b < 31) by (destruct (Z.eq_dec b 0) as [->|]; [cbn; lia| apply Z.log2_lt_pow2; lia]).
  apply Z.log2_lt_pow2; [pose proof (Z.lxor_nonneg a b); lia|].
  eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|]. apply Z.max_lub_lt; assumption.
Qed.


Lemma meta_word_sc2 mr : mw_ok mr -> Z.land (Z.shiftr (meta_word mr) 5) 126 = 2 * m_sizeclass mr.
Proof.
  intros MW. pose proof (meta_word_sc mr MW) as E. pose proof MW as (LI & FB & SCR & ML).
  pose proof (meta_word_range mr MW) as WR.
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.shiftr_spec by lia.
  destruct (Z.eq_dec n 0) as [->|NZ].
  - rewrite Z.testbit_even_0. replace (Z.testbit 126 0) with false by reflexivity. apply Bool.andb_false_r.
  - replace n with (Z.succ (n - 1)) by lia. rewrite Z.testbit_even_succ by lia.
    rewrite <- E. rewrite Z.land_spec, Z.shiftr_spec by lia.
    change 126 with (2 * 63). rewrite Z.testbit_even_succ by lia.
    replace (Z.succ (n - 1) + 5) with (n - 1 + 6) by lia. reflexivity.
Qed.

Lemma span_loop_bounds F : forall cnt span size, cnt <= span_loop F cnt span size <= cnt + Z.of_nat F.
Proof.
  induction F as [|F IH]; intros; cbn [span_loop]; [lia|].
  rewrite Nat2Z.inj_succ. destruct (_ <? _); [|lia]. pose proof (IH (cnt + 1) (span + size) size). lia.
Qed.

(* [comment removed for export] *)
Lemma ai_byte_land w v : 0 <= w -> 0 <= v ->
  Z.land ((Z.lor (Z.land w (2^64 - 32)) (Z.land v 31)) mod 256) 31 = Z.land v 31.
Proof.
  intros Hw Hv. apply Z.bits_inj'. intros n Hn.
  change 256 with (2^8). change 31 with (Z.ones 5).
  rewrite !Z.land_spec, Z.testbit_mod_pow2, Z.lor_spec, !Z.land_spec, !Z.testbit_ones by lia.
  replace (2^64 - 32) with (Z.shiftl (2^59 - 1) 5) by reflexivity.
  destruct (Z.ltb_spec n 5).
  - rewrite Z.shiftl_spec_low by lia. replace (0 <=? n) with true by (symmetry; apply Z.leb_le; lia).
    replace (n <? 8) with true by (symmetry; apply Z.ltb_lt; lia). rewrite ?Bool.andb_false_r, ?Bool.andb_true_r, ?Bool.orb_false_l. reflexivity.
  - replace (0 <=? n) with true by (symmetry; apply Z.leb_le; lia). cbn [andb]. rewrite !Bool.andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma le1_mod z : le1 (Z_to_bv 64 z) = [b8 (z mod 256)].
Proof.
  unfold le1, b8. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. change (2 ^ Z.of_N 64) with (256 * 2^56).
  rewrite Z.rem_mul_r by lia. rewrite (Z.mul_comm 256), Z.mod_add, Z.mod_mod by lia. reflexivity.
Qed.

Lemma land31_range x : 0 <= Z.land x 31 <= 31.
Proof.
  split; [apply Z.land_nonneg; right; lia|].
  apply Z.ldiff_le; [lia|].
  apply Z.bits_inj'. intros n Hn. rewrite Z.ldiff_spec, Z.land_spec, Z.bits_0.
  destruct (Z.testbit x n), (Z.testbit 31 n); reflexivity.
Qed.

Lemma swrap32_small z : - 2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
  intros. rewrite swrap32_eq'.
  change (2^32) with 4294967296 in *. change (2^31) with 2147483648 in *.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma sraiw1_small v : 0 <= v < 2^31 ->
  Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_swrap 32 (bv_unsigned (wz v))) 1)) = wz (Z.shiftr v 1).
Proof.
  intros Hv. rewrite wz_unsigned by lia. rewrite (swrap32_small v) by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  rewrite swrap32_small by (Z.div_mod_to_equations; lia). reflexivity.
Qed.

Lemma land1_mod2 a : Z.land a 1 = a mod 2.
Proof. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma even_of_land1 a : Z.even a = (Z.land a 1 =? 0).
Proof.
  rewrite land1_mod2, Zeven.Zeven_odd_bool, Zmod_odd. destruct (Z.odd a); reflexivity.
Qed.

End CANSEC2.
