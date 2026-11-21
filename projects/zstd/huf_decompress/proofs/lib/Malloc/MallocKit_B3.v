(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (21 recorded proofs replaced by written proofs (usage_set_usage, usages_set_usage, unmap_seq_set and 18 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free MallocTree MallocKit_B MallocModel_B.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MallocKit_B3 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1I35stdpp4gmap4gmap00I35stdpp9countable9Countable00C35stdpp4base;RelDecisionC35stdpp4base4fmapC35stdpp8fin_maps@lookup_insert_eqC47Corelib4Init5Logic8eq_ind_rC35stdpp8fin_maps@lookup_insert_neC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldC56Stdlib6ZArith6BinInt1Z8eqb_specC56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init9Datatypes7reflect00C47Corelib4Init9Datatypes2idC35stdpp8fin_maps:map_insertC59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7c_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01K47Corelib4Init5Logic2eq01C35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC47Corelib4Init5Logic3notC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic9False_indC59OSSVerify5KrLib4Spec6Malloc=set_usage_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6mstate01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9set_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C35stdpp4base6insertC35stdpp4base6lookupC35stdpp6option;from_optionI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3seqC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib3Lib3Arr3updC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC56Stdlib5Arith8PeanoNat3Nat3eqbC56Stdlib5Arith8PeanoNat3Nat8eqb_specC46Stdlib9micromega;ZifyClasses9not_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegc59OSSVerify5KrLib6Malloc<MallocKit_B3?usage_set_usageC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01C59OSSVerify5KrLib6Malloc9MallocRep;map_seq_updC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib6Malloc9MallocRep6usagesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula07I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxK47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op203C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib4Spec6Malloc;c_unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocAset_unmap_seq_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9unmap_seqC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2b8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc<MallocKit_B3=unmap_seq_setC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:unmap_seqsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C35stdpp4base5emptyC59OSSVerify5KrLib4Spec6Malloc7set_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8step_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?sc_in_seq_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2pwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5oconcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_slotC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc<MallocKit_B35mw_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib6Malloc9MallocRep9meta_wordC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z7mod_addC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z9div_smallC56Stdlib6ZArith6BinInt1Z7div_addC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2c59OSSVerify5KrLib6Malloc<MallocKit_B3?meta_word_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z5ldiffC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C56Stdlib6ZArith6BinInt1Z<ldiff_ones_rC59OSSVerify5KrLib6Malloc9MallocRep@land_ldiff_distrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7land_wdC47Corelib4Init5Logic3iffK46Stdlib9micromega5Tauto8GFormula09C59OSSVerify5KrLib6Malloc=F_malloc_free3sxvC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega:ZMicromega;ZArithProof04K46Stdlib9micromega7EnvRing5PExpr06C59OSSVerify5KrLib6Malloc=F_malloc_free;swrap32_eq'C1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib3Lib7ZBridge=Z_to_bv_mod64C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib6Malloc=F_malloc_free9sxv_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep;wz_unsignedC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02I47Corelib4Init9Datatypes:comparison00C56Stdlib6ZArith6BinInt1Z4lnotC56Stdlib6ZArith6BinInt1Z:ldiff_landC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes3orbC47Corelib4Init9Datatypes4negbC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z:ldiff_specC56Stdlib6ZArith6BinInt1Z8lor_specC56Stdlib6ZArith6BinInt1Z9bits_inj'C56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith8Zbitwise1Z<add_lor_landC56Stdlib6ZArith6BinInt1Z;land_nonnegC56Stdlib6ZArith6BinInt1Z<ldiff_nonnegK47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib6Malloc=F_malloc_free9sxv_mod32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=F_malloc_free9le4_congrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC59OSSVerify5KrLib3Lib3Mem3le1C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C56Stdlib6ZArith6BinInt1Z:shiftl_1_lC56Stdlib6ZArith6BinInt1Z<lor_eq_0_iffC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC59OSSVerify5KrLib6Malloc=F_malloc_free8sxv_zeroC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indC47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses?iff_equivalenceC47Corelib7Classes?RelationClasses=iff_Reflexive".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Lemma usage_set_usage st sc v i : usage (set_usage sc v st) i = if Z.eqb i sc then v else usage st i.
Proof.
  unfold usage, set_usage, upd_ctx. cbn [ctx s_ctx c_usage set_usage_map].
  destruct (Z.eqb_spec i sc); subst.
  - rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma usages_set_usage st sc v : 0 <= sc < 48 ->
  usages (set_usage sc v st) = upd (usages st) (Z.to_nat sc) (wz v).
Proof.
  intros Hsc. unfold usages.
  replace (Z.to_nat sc) with (Z.to_nat sc - 0)%nat by lia.
  apply (map_seq_upd (fun i => wz (usage st (Z.of_nat i))) (fun i => wz (usage (set_usage sc v st) (Z.of_nat i)))); [|lia].
  intros i Hi. rewrite usage_set_usage.
  destruct (Z.eqb_spec (Z.of_nat i) sc); destruct (Nat.eqb_spec i (Z.to_nat sc)); try reflexivity; lia.
Qed.

End CANSEC1.
Ltac ctx_same := intros lo' hi' [E|[]]; inversion E; subst; unfold CTX; lia.

Section CANSEC2. Context {rc : runConstT}.
Lemma unmap_seq_set st i v j :
  unmap_seq (upd_ctx (fun c => set_unmap_seq_map (<[i := v]> (c_unmap_seq c)) c) st) j = if Z.eqb j i then v else unmap_seq st j.
Proof.
  unfold unmap_seq, upd_ctx. cbn [ctx s_ctx c_unmap_seq set_unmap_seq_map].
  destruct (Z.eqb_spec j i); subst.
  - rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma unmap_seqs_set st i v : 0 <= i < 32 ->
  unmap_seqs (upd_ctx (fun c => set_unmap_seq_map (<[i := v]> (c_unmap_seq c)) c) st) = upd (unmap_seqs st) (Z.to_nat i) (b8 v).
Proof.
  intros Hi. unfold unmap_seqs.
  replace (Z.to_nat i) with (Z.to_nat i - 0)%nat by lia.
  apply (map_seq_upd (fun j => b8 (unmap_seq st (Z.of_nat j)))); [|lia].
  intros j Hj. rewrite unmap_seq_set.
  destruct (Z.eqb_spec (Z.of_nat j) i); destruct (Nat.eqb_spec j (Z.to_nat i)); try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Lemma step_seq_eq st :
  step_seq st = if c_seq (ctx st) =? 255
                then upd_ctx (set_seq 1) (upd_ctx (fun c => set_unmap_seq_map ∅ c) st)
                else upd_ctx (set_seq (c_seq (ctx st) + 1)) st.
Proof. unfold step_seq. destruct (c_seq (ctx st) =? 255); reflexivity. Qed.

Lemma record_seq_eq sc st :
  record_seq sc st = if sc_in_seq_range sc
                     then upd_ctx (fun c => set_unmap_seq_map (<[sc - 7 := c_seq c]> (c_unmap_seq c)) c) st
                     else st.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma conc_upd_ctx st f q : conc (upd_ctx f st) q = conc st q.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B3 ()) ["CANSEC2"] "h01fh11qh22stp;2g01P3j21Tg00=<j20Tg00P:R0g01HDR1P1[R1g01PhR2g00O>f2R3f0R4'1'0X12X01X20P3f1P4O3W1W0W2o"). Qed.
Lemma rec_upd_ctx st f q : get_meta_rec (upd_ctx f st) q = get_meta_rec st q.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B3 ()) ["CANSEC2"] "h01fh11qh22stp;2g01Q]j21Tg00=<j20Tg00P:R0g01HDR1P1[R1g01PhR2g01RZf2R3f0R4'1'0X12X01X20P3f1P4O3W1W0W2o"). Qed.
Lemma pw_upd_ctx st f q : pw (upd_ctx f st) q = pw st q.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B3 ()) ["CANSEC2"] "p'0h01fh11qh22sth31ai001ai011op;1p;2p;3g00SLj10Tg00cfj18Tg00dDj14Tg01FRj23Tg01SQj21Tg00Maj37Tg00<Zj26Tg00=<j22Tg00`:j15Tg00P:R0g01HDR1P1[R1g01TIR2g00<8g01PhR3g01CO#0#0#0#0#0#0#8#4R4f2R5f3R6'3f0R7'1116737P7f41637'1,24X33P7O1%53,15,24n10110100021010000X12X01X20P5f1P7O3W1W0W2o"). Qed.
Lemma oconc_upd_ctx st f q : oconc (upd_ctx f st) q = oconc st q.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B3 ()) ["CANSEC2"] "p'0h01fh11qh22sth31ai001ai011op;2p;3p;1g01FRj25Tg01U>j20Tg00Maj33Tg00<Zj22Tg00=<j21Tg00`:j14Tg00P:R0g01HDR1P1[R1g01TIR2g00<8g01PhR3g00O>R4f2R5f3R6'5f0R7'0106733P7f41237'0,14X33P7O1%43,05,14n10110100021010000X12X01X20P5f1P7O3W1W0W2o"). Qed.
Lemma conc_set_usage st sc v q : conc (set_usage sc v st) q = conc st q.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B3 ()) ["CANSEC2"] "h01qh12sch22sth31vp;2g01P3j21Tg00=<j20Tg00P:R0g00O>R1g01PhR2f3R3f0R4'1,01X02X31X11X20P3f2f1P4O4W0X31W1W2o"). Qed.
Lemma rec_set_usage st sc v q : get_meta_rec (set_usage sc v st) q = get_meta_rec st q.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B3 ()) ["CANSEC2"] "h01qh12sch22sth31vp;2g01Q]j21Tg00=<j20Tg00P:R0g00O>R1g01PhR2g01RZf3R3f0R4'1'0X02X31X11X20P3f2f1P4O4W0X31W1W2o"). Qed.
Lemma oconc_set_usage st sc v q : oconc (set_usage sc v st) q = oconc st q.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B3 ()) ["CANSEC2"] "p'0h01qh12sch22sth31vh41ai001ai011op;3p;2p;1g00L1j35Tg01U>j20Tg00Maj33Tg00<Zj22Tg00=<j21Tg00`:j14Tg00P:R0g00O>R1g01TIR2g00<8g01PhR3f3R4f2R5f4R635f0R7'01067531P7f51237'0,11X43P7O1%43,04,11n10110100021010000X02X31X11X20P4P5f1P7O4W0X31W1W2o"). Qed.
Lemma conc_set_active st sc v q : conc (set_active sc v st) q = conc st q.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B3 ()) ["CANSEC2"] "h01qh12sch22sth31vp;2g01P3j21Tg00=<j20Tg00P:R0g00O>R1g01TIR2g01PhR3f3R4f0R5'1,01X03X32X11X20P4f2f1P5O4W0W3W1W2o"). Qed.
Lemma rec_set_active st sc v q : get_meta_rec (set_active sc v st) q = get_meta_rec st q.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B3 ()) ["CANSEC2"] "h01qh12sch22sth31vp;2g01Q]j21Tg00=<j20Tg00P:R0g00O>R1g01TIR2g01PhR3g01RZf3R4f0R5'1'0X03X32X11X20P4f2f1P5O4W0W3W1W2o"). Qed.
Lemma oconc_set_active st sc v q : oconc (set_active sc v st) q = oconc st q.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B3 ()) ["CANSEC2"] "p'0h01qh12sch22sth31vh41ai001ai011op;3p;2p;1g01V4j35Tg01U>j20Tg00Maj33Tg00<Zj22Tg00=<j21Tg00`:j14Tg00P:R0g00O>R1g01TIR2g00<8g01PhR3f3R4f2R5f4R635f0R7'01067531P7f51237'0,11X43P7O1%43,04,11n10110100021010000X02X32X11X20P4P5f1P7O4X02W3W1W2o"). Qed.
Lemma meta_slot_upd_ctx st f q : meta_slot st q -> meta_slot (upd_ctx f st) q.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B3 ()) ["CANSEC2"] "h01fh11qh22sth31Hp;2g01Voj20Tg00P:R0g01HDR1P1[R1g01PhR2f2R3f0R4'0P4W3X12X01X20P3f1P4O3W1W0W2o"). Qed.
Lemma meta_slot_set_usage st sc v q : meta_slot st q -> meta_slot (set_usage sc v st) q.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B3 ()) ["CANSEC2"] "h01qh12sch22sth31vh41Hp;2g01Voj20Tg00P:R0g00O>R1g01PhR2f3R3f0R4'0P4W4X02X31X11X20P3f2f1P4O4W0X31W1W2o"). Qed.
Lemma meta_slot_set_active st sc v q : meta_slot st q -> meta_slot (set_active sc v st) q.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B3 ()) ["CANSEC2"] "h01qh12sch22sth31vh41Hp;2g01Voj20Tg00P:R0g00O>R1g01TIR2g01PhR3f3R4f0R5'0P5W4X03X32X11X20P4f2f1P5O4W0W3W1W2o"). Qed.

End CANSEC2.
Ltac ctx_norm H := rewrite ?conc_set_usage, ?rec_set_usage, ?oconc_set_usage, ?conc_set_active, ?rec_set_active, ?oconc_set_active,
                           ?conc_upd_ctx, ?rec_upd_ctx, ?oconc_upd_ctx in H.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC3. Context {rc : runConstT}.
Definition mw_ok (mr : meta) : Prop :=
  0 <= m_last_idx mr <= 31 /\ 0 <= m_freeable mr <= 1 /\ 0 <= m_sizeclass mr <= 63 /\ 0 <= m_maplen mr < 2^52.

Lemma meta_word_range mr : mw_ok mr -> 0 <= meta_word mr < 2^64.
Proof. intros (LI & FB & SCR & ML). unfold meta_word. lia. Qed.
Lemma meta_word_last_idx mr : mw_ok mr -> Z.land (meta_word mr) 31 = m_last_idx mr.
Proof.
  intros (LI & FB & SCR & ML).
  change 31 with (Z.ones 5). rewrite Z.land_ones by lia. unfold meta_word. change (2^5) with 32.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with (m_last_idx mr + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr) * 32) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma meta_word_sc mr : mw_ok mr -> Z.land (Z.shiftr (meta_word mr) 6) 63 = m_sizeclass mr.
Proof.
  intros (LI & FB & SCR & ML).
  change 63 with (Z.ones 6). rewrite Z.land_ones, Z.shiftr_div_pow2 by lia. unfold meta_word. change (2^6) with 64.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with ((m_last_idx mr + 32 * m_freeable mr) + (m_sizeclass mr + 64 * m_maplen mr) * 64) by lia.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia.
  replace (0 + (m_sizeclass mr + 64 * m_maplen mr)) with (m_sizeclass mr + m_maplen mr * 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma meta_word_shr6_range mr : mw_ok mr -> 0 <= Z.shiftr (meta_word mr) 6 < 2^64.
Proof. intros H. pose proof (meta_word_range mr H). destruct H as (LI & FB & SCR & ML). rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.
Lemma meta_word_freeable mr : mw_ok mr -> Z.land (meta_word mr) 32 = 32 * m_freeable mr.
Proof.
  intros (LI & FB & SCR & ML).
  assert (E : 32 = Z.ldiff (Z.ones 6) (Z.ones 5)) by reflexivity. rewrite E at 1. rewrite land_ldiff_distr.
  rewrite Z.land_ones, Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^6) with 64. change (2^5) with 32. unfold meta_word.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with ((m_last_idx mr + 32 * m_freeable mr) + (m_sizeclass mr + 64 * m_maplen mr) * 64) by lia.
  rewrite Z.mod_add, Z.mod_small by lia.
  replace (m_last_idx mr + 32 * m_freeable mr) with (m_last_idx mr + m_freeable mr * 32) by lia.
  rewrite Z.div_add, Z.div_small by lia. lia.
Qed.
Lemma meta_word_maplen mr : mw_ok mr -> Z.shiftr (meta_word mr) 12 = m_maplen mr.
Proof.
  intros (LI & FB & SCR & ML).
  rewrite Z.shiftr_div_pow2 by lia. unfold meta_word. change (2^12) with 4096.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) + m_maplen mr * 4096) by lia.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.
Lemma meta_word_lt4096 mr : mw_ok mr -> meta_word mr < 4096 <-> m_maplen mr = 0.
Proof. intros (LI & FB & SCR & ML). unfold meta_word. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma negw_word y : Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (wz (sxv y)))) = wz (sxv (- y)).
Proof.
  rewrite wz_unsigned by (apply sxv_range). unfold wz, sxv. rewrite <- (Z_to_bv_mod64 (bv_swrap 32 _)). f_equal.
  rewrite !swrap32_eq'. mlia.
Qed.

Lemma land_neg_pow2 f k : 0 <= f -> 0 <= k -> Z.land f (- 2 ^ k) = Z.ldiff f (2 ^ k - 1).
Proof.
  intros Hf Hk. replace (- 2 ^ k) with (Z.lnot (2 ^ k - 1)) by (unfold Z.lnot; lia).
  rewrite <- Z.ldiff_land. reflexivity.
Qed.



Lemma ldiff_le f a : 0 <= f -> 0 <= a -> Z.ldiff f a <= f.
Proof.
  intros Hf Ha.
  assert (E : f = Z.lor (Z.ldiff f a) (Z.land f a)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.ldiff_spec, Z.land_spec. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
  assert (D : Z.land (Z.ldiff f a) (Z.land f a) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
  pose proof (Z.add_lor_land (Z.ldiff f a) (Z.land f a)) as S. rewrite D, <- E in S.
  pose proof (Z.land_nonneg f a). pose proof (Z.ldiff_nonneg f a). lia.
Qed.



Lemma land_upper f a : 0 <= f -> 0 <= a -> 0 <= Z.land f a <= f.
Proof.
  intros Hf Ha. split; [apply Z.land_nonneg; lia|].
  assert (E : f = Z.lor (Z.ldiff f a) (Z.land f a)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.ldiff_spec, Z.land_spec. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
  assert (D : Z.land (Z.ldiff f a) (Z.land f a) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
  pose proof (Z.add_lor_land (Z.ldiff f a) (Z.land f a)) as S. rewrite D, <- E in S.
  pose proof (Z.land_nonneg f a). pose proof (Z.ldiff_nonneg f a). lia.
Qed.



Lemma le4_sxv v : 0 <= v < 2^32 -> le4 (Z_to_bv 64 (sxv v)) = le4 (wz v).
Proof.
  intros Hv. apply le4_congr. pose proof (sxv_range v). rewrite unsigned_lit by lia. rewrite wz_unsigned by lia.
  rewrite sxv_mod32. reflexivity.
Qed.

Lemma le1_lit z : 0 <= z < 256 -> le1 (Z_to_bv 64 z) = [b8 z].
Proof.
  intros Hz. unfold le1, b8. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned, (bv_wrap_small 64) by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.

Lemma sllw1_word i : 0 <= i < 32 -> Z_to_bv 64 (bv_swrap 32 (Z.shiftl 1 (i mod 32))) = wz (sxv (2 ^ i)).
Proof.
  intros Hi. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l.
  unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.

Lemma lor_sxv_zero f a : 0 <= f < 2^32 -> 0 <= a < 2^32 ->
  (Z.lor (sxv f) (sxv a) = 0 <-> Z.lor f a = 0).
Proof.
  intros Hf Ha. pose proof (sxv_range f). pose proof (sxv_range a).
  rewrite !Z.lor_eq_0_iff. rewrite !sxv_zero by lia. tauto.
Qed.

(* [comment removed for export] *)
End CANSEC3.
Ltac unmask64 K :=
  try (change 18446744073709551615 with (Z.ones 64) in K; rewrite !Z.land_ones in K by lia; rewrite !Z.mod_small in K by lia).


