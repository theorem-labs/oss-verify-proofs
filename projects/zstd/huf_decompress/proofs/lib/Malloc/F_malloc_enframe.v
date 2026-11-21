(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (17 recorded proofs replaced by written proofs (fold_off_eq, smear_nonneg, land_le_l and 14 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_malloc_enframe () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C56Stdlib6ZArith6BinInt1Z3ltbc59OSSVerify5KrLib6Malloc@F_malloc_enframe5smearC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init5Logic2eq01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4bool00K47Corelib7Numbers7BinNums8positive03C56Stdlib6ZArith6BinInt1Z3lorI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6shiftrK47Corelib7Numbers7BinNums8positive02K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z=shiftr_nonnegK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib4Init9Datatypes4bool01C56Stdlib6ZArith6BinInt1Z5ldiffC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClassesCPreOrder_TransitiveC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib7Classes?RelationClassesBPreOrder_ReflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC56Stdlib6ZArith6BinInt1Z=lor_ldiff_andC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z<ldiff_nonnegK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C56Stdlib6ZArith6BinInt1Z;land_nonnegC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z6bits_0C47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z:ldiff_specC56Stdlib6ZArith6BinInt1Z9bits_inj'C56Stdlib6ZArith6BinInt1Z4lxorK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z@add_nocarry_lxorC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z8lxor_lorK47Corelib4Init9Datatypes4bool02C47Corelib7Program6Basics4implC56Stdlib6ZArith6BinInt1Z;le_preorderc59OSSVerify5KrLib6Malloc@F_malloc_enframe4zseqC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbc59OSSVerify5KrLib6Malloc@F_malloc_enframe7fold_fnC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List2InC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC47Corelib5Lists7ListDef3mapI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List:in_map_iffC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums8positive01C46Stdlib9micromega;ZifyClasses;rew_iff_revI47Corelib4Init5Peano2le00C47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphK47Corelib4Init5Logic2ex01C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op205C46Stdlib5Lists4List8map_consK47Corelib4Init9Datatypes3nat01c59OSSVerify5KrLib6Malloc@F_malloc_enframe<smear_nonnegC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc@F_malloc_enframe9land_le_lC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;lt_ge_casesc59OSSVerify5KrLib6Malloc@F_malloc_enframe<forallb_zseqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc@F_malloc_enframe8fold_fn1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib4Bool4Bool8orb_propC46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z6leb_leK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr04c59OSSVerify5KrLib6Malloc@F_malloc_enframe?fold_check_trueC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree5sbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree;sbind_ret_lC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3retC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC35stdpp4gmap:gmap_emptyC59OSSVerify5KrLib4Spec6Malloc3rd8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4rd16C1?~~~~~~~~~~~~~~~C35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC59OSSVerify5KrLib4Spec6Malloc<enframe_fullC1?~~~~~~~~~~~~~~~C35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC59OSSVerify5KrLib4Spec6Malloc:alloc_slotC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps:map_eq_iffC35stdpp4gmap;gmap_finmapC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps@lookup_insert_eqI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6LookupC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeC35stdpp4base;RelDecisionI35stdpp4gmap4gmap00I35stdpp9countable9Countable00C35stdpp4base4fmapC35stdpp4gmap;gmap_lookupC35stdpp4gmapBgmap_partial_alterC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00c59OSSVerify5KrLib6Malloc@F_malloc_enframe>fold_assert_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8fold_offC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc@F_malloc_enframe;fold_off_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C46Stdlib4Bool4Bool<andb_false_rC56Stdlib6ZArith6BinInt1Z>testbit_even_0C56Stdlib6ZArith6BinInt1Z4succK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z;shiftr_specC56Stdlib6ZArith6BinInt1ZAtestbit_even_succI47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z=shiftr_shiftrc59OSSVerify5KrLib6Malloc@F_malloc_enframe8land_126C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05I47Corelib4Init9Datatypes:comparison00C59OSSVerify5KrLib4Spec:MallocCtrl4prunC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib6Malloc9MallocRep2b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib6Malloc9MallocRep;wz_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le1C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC35stdpp7tactics<f_equal_helpI47Corelib7Numbers7BinNums1N00c59OSSVerify5KrLib6Malloc@F_malloc_enframe:rd8_oracleC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc@F_malloc_enframe;rd16_oracleC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc@F_malloc_enframe3rdvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl4pselC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z4predC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z:ltb_irreflC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z<testbit_onesC56Stdlib6ZArith6BinInt1Z:ones_equivC56Stdlib6ZArith6BinInt1Z=pow2_bits_eqbC56Stdlib6ZArith6BinInt1Z8bits_oppC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z9log2_pow2c59OSSVerify5KrLib6Malloc@F_malloc_enframe>land_opp_pow2'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5ctz32C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C47Corelib4Init9Datatypes2idC35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C35stdpp4base6insertC59OSSVerify5KrLib4Spec6Malloc9set_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C35stdpp6option;from_optionC35stdpp4base6lookupI59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableC59OSSVerify5KrLib4Spec6Malloc=size_to_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>size_overflowsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6lowbitC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K59OSSVerify5KrLib4Spec6Malloc2ev02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;live_rangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>mmap_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:bad_answerC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6is_errC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:new_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8step_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3u32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@set_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9m_set_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>m_set_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>m_set_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?m_set_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<m_set_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@group_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6lh_hdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9put_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9add_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K59OSSVerify5KrLib4Spec6Malloc2ev03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@munmap_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;drop_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:alloc_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocAmalloc_small_ctrlC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_gtC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqc59OSSVerify5KrLib6Malloc@F_malloc_enframe;ctz32_pow2'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;malloc_coreC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4evenC59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8full_layC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4FUELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>MMAP_THRESHOLDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7PROT_RWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;MAP_PRIVATEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8MAP_ANONC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib7Numbers7BinNums1N01K59OSSVerify5KrLib4Spec6Malloc<undef_reason03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N4succC59OSSVerify5KrLib4Spec6Malloc8set_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:enframe_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eqb_eqc59OSSVerify5KrLib6Malloc@F_malloc_enframeEget_meta_rec_upd_sameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc@F_malloc_enframe@malloc_core_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5havocC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndK59OSSVerify5KrLib4Spec5STree5stree01C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Definition smear (s : Z) : Z :=
  let m1 := Z.lor s (Z.shiftr s 1) in
  let m2 := Z.lor m1 (Z.shiftr m1 2) in
  Z.lor m2 (Z.shiftr m2 4).

Lemma fold_off_eq off slack :
  fold_off off slack =
  (if slack <? off then
     let x := Z.land off (smear slack) in if slack <? x then x - (slack + 1) else x
   else off).
Proof. reflexivity. Qed.

Lemma smear_nonneg s : 0 <= s -> 0 <= smear s.
Proof.
  intros. unfold smear.
  repeat (apply Z.lor_nonneg; split); repeat apply Z.shiftr_nonneg; repeat (apply Z.lor_nonneg; split);
    repeat apply Z.shiftr_nonneg; try lia; repeat (apply Z.lor_nonneg; split); try apply Z.shiftr_nonneg; try lia.
  all: try (apply Z.lor_nonneg; split); try apply Z.shiftr_nonneg; try lia.
Qed.

Lemma land_le_l a b : 0 <= a -> 0 <= b -> Z.land a b <= a.
Proof.
  intros. rewrite <- (Z.lor_ldiff_and a b) at 2.
  assert (0 <= Z.ldiff a b) by (apply Z.ldiff_nonneg; lia).
  assert (0 <= Z.land a b) by (apply Z.land_nonneg; lia).
  assert (Z.land (Z.ldiff a b) (Z.land a b) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0.
    destruct (Z.testbit a n), (Z.testbit b n); reflexivity. }
  rewrite <- Z.lxor_lor, <- Z.add_nocarry_lxor by assumption. lia.
Qed.

(* [comment removed for export] *)
Definition zseq (a n : Z) : list Z := map Z.of_nat (seq (Z.to_nat a) (Z.to_nat n)).

(* [comment removed for export] *)
Definition fold_fn1 (s off : Z) : bool :=
  let x := Z.land off (smear s) in (negb (s <? x)) || (x - (s + 1) <=? s).
Definition fold_fn (s : Z) : bool := forallb (fold_fn1 s) (zseq 0 256).
Definition fold_check : bool := forallb fold_fn (zseq 0 128).

Lemma fold_check_true : forallb fold_fn (zseq 0 128) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma forallb_zseq (f : Z -> bool) a n x : forallb f (zseq a n) = true -> 0 <= a -> a <= x < a + n -> f x = true.
Proof.
  intros H Ha Hx. unfold zseq in H. rewrite forallb_forall in H. apply H.
  apply in_map_iff. exists (Z.to_nat x). split; [lia|]. apply in_seq. lia.
Qed.

Lemma fold_assert_ok off slack : 0 <= off < 256 -> 0 <= slack ->
  slack < Z.land off (smear slack) -> Z.land off (smear slack) - (slack + 1) <= slack.
Proof.
  intros Ho Hs Hlt.
  pose proof (smear_nonneg slack Hs) as Sm.
  assert (UB : Z.land off (smear slack) <= off) by (apply land_le_l; lia).
  destruct (Z.lt_ge_cases slack 128).
  - pose proof (forallb_zseq fold_fn 0 128 slack fold_check_true ltac:(lia) ltac:(lia)) as H1. unfold fold_fn in H1.
    pose proof (forallb_zseq (fold_fn1 slack) 0 256 off H1 ltac:(lia) ltac:(lia)) as H2. unfold fold_fn1 in H2. cbv zeta in H2.
    apply orb_prop in H2. destruct H2 as [H2|H2].
    + apply negb_true_iff in H2. apply Z.ltb_ge in H2. lia.
    + apply Z.leb_le in H2. exact H2.
  - lia.
Qed.

Lemma fold_off_range off slack : 0 <= off < 256 -> 0 <= slack -> 0 <= fold_off off slack <= Z.max slack off /\ fold_off off slack < 256.
Proof.
  intros Ho Hs. rewrite fold_off_eq. pose proof (smear_nonneg slack Hs) as Sm.
  assert (UB : Z.land off (smear slack) <= off) by (apply land_le_l; lia).
  assert (LB : 0 <= Z.land off (smear slack)) by (apply Z.land_nonneg; lia).
  destruct (Z.ltb_spec slack off); [|lia]. cbv zeta.
  destruct (Z.ltb_spec slack (Z.land off (smear slack))); [|lia].
  pose proof (fold_assert_ok off slack Ho Hs ltac:(lia)). lia.
Qed.

Lemma fold_off_le_slack off slack : 0 <= off < 256 -> 0 <= slack -> 0 <= fold_off off slack <= slack.
Proof.
  intros Ho Hs. rewrite fold_off_eq. pose proof (smear_nonneg slack Hs) as Sm.
  assert (UB : Z.land off (smear slack) <= off) by (apply land_le_l; lia).
  assert (LB : 0 <= Z.land off (smear slack)) by (apply Z.land_nonneg; lia).
  destruct (Z.ltb_spec slack off); [|lia]. cbv zeta.
  destruct (Z.ltb_spec slack (Z.land off (smear slack))); [|lia].
  pose proof (fold_assert_ok off slack Ho Hs ltac:(lia)). lia.
Qed.

Lemma land_126 y : Z.land y 126 = 2 * Z.land (Z.shiftr y 1) 63.
Proof.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.eq_dec i 0) as [->|].
  - rewrite Z.testbit_even_0. change 126 with (2 * 63). rewrite Z.testbit_even_0. apply andb_false_r.
  - replace i with (Z.succ (i - 1)) by lia. rewrite Z.testbit_even_succ by lia.
    change 126 with (2 * 63). rewrite Z.testbit_even_succ by lia. rewrite Z.land_spec, Z.shiftr_spec by lia.
    replace (i - 1 + 1) with i by lia. replace (Z.succ (i - 1)) with i by lia. reflexivity.
Qed.

Lemma mword_sc last_idx freeable sc maplen :
  0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen ->
  Z.land (Z.shiftr (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) 5) 126 = 2 * sc.
Proof.
  intros. rewrite land_126. rewrite Z.shiftr_shiftr, !Z.shiftr_div_pow2 by lia. change (2 ^ (5 + 1)) with 64.
  change 63 with (Z.ones 6). rewrite Z.land_ones by lia. change (2^6) with 64.
  replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) / 64) with (sc + 64 * maplen) by (Z.div_mod_to_equations; lia).
  replace ((sc + 64 * maplen) mod 64) with sc by (Z.div_mod_to_equations; lia). reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End CANSEC1.
Ltac sdk :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m ?a ?bs) ?ro) =>
    let E := addr_expr a in
    (lazymatch a with
     | wa _ => idtac
     | Z_to_bv 64 _ => change (write_to_mem m a bs) with (write_to_mem m (wa E) bs)
     | _ => replace (write_to_mem m a bs) with (write_to_mem m (wa E) bs) by (f_equal; addr_eq_tac)
     end);
    (try lazymatch goal with
     | HI : mem_inv segs m, HS : store_ok segs m ?a' ?n = true |- _ =>
        apply (mem_inv_store segs m (wa E) bs) in HI;
        [ | first [ exact HS
                  | replace (wa E) with a' by (first [reflexivity | addr_eq_tac | symmetry; addr_eq_tac]);
                    first [ exact HS | simpl_sizes; exact HS ] ] ]
     end);
    transport_chunks segs m E bs;
    repeat match goal with
    | STq : stk segs m ?loq ?hiq |- _ =>
        first [ apply (stk_write segs m loq hiq E bs) in STq; [ | lia | simpl_sizes; slia ]
              | fail 100 "sdk: cannot transport stk hypothesis" STq ]
    | MU : munch ?Wq ?mq m |- _ =>
        first [ apply (munch_write Wq mq m E bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
              | fail 100 "sdk: store outside the declared footprint" ]
    | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa E) bs) in WMo
    end;
    repeat match goal with
    | H : store_ok segs m _ _ = true |- _ => clear H
    | H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
    end;
    let m' := fresh "m" in let Eq := fresh "EQ" m' in
    remember (write_to_mem m (wa E) bs) as m' eqn:Eq
  end.

Section CANSEC2. Context {rc : runConstT}.
Lemma le1_wz v : 0 <= v < 256 -> le1 (wz v) = [b8 v].
Proof. intros. cbn. rewrite (wz_unsigned v) by lia. reflexivity. Qed.

Lemma le1_neg32 : le1 (Z_to_bv 64 (-32)) = [b8 224].
Proof. cbn. f_equal. apply bv_eq. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition enframe_tail_mem (m : word -> option byte) (P E n k q : Z) : word -> option byte :=
  let m1 := write_to_mem m (wa (P - 2)) (le2 (wz q)) in
  let m2 := write_to_mem m1 (wa (P - 3)) [b8 k] in
  let r := E - P - n in
  let m3 := if r =? 0 then m2 else write_to_mem m2 (wa (E - r)) [b8 0] in
  let '(m4, r') := if 5 <=? r then (write_to_mem (write_to_mem m3 (wa (E - 4)) (le4 (wz r))) (wa (E - 5)) [b8 0], 5) else (m3, r) in
  write_to_mem m4 (wa (P - 3)) [b8 (Z.land k 31 + Z.shiftl r' 5)].

(* [comment removed for export] *)
Definition enframe_off_mem (m : word -> option byte) (P0 off : Z) : word -> option byte :=
  if off =? 0 then m
  else write_to_mem (write_to_mem (write_to_mem m (wa (P0 - 2)) (le2 (wz off))) (wa (P0 - 3)) [b8 224])
                    (wa (P0 + 16 * off - 4)) [b8 0].

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FASTMODEL.
Context {O : Type}.
Variable pans : O -> aptr -> Z -> Z -> Z.
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.
Let pupd : O -> ev -> Z -> O := fun o _ _ => o.
Local Notation prun := (prun pans pupd).

(* [comment removed for export] *)
Definition rdv (o : O) (st : mstate) (q : aptr) : Z :=
  match cell_read (get_shadow st (fst q)) (snd q) with
  | Known v => v
  | Unknown h => pans o q (conc st q) h
  end.

Lemma rd8_oracle {R} o st q (k : Z -> M R) : prun o (rd8 st q k) = prun o (k (rdv o st q)).
Proof.
  unfold rd8, rdv. destruct (cell_read _ _) as [v|h]; [reflexivity|].
  unfold MallocCtrl.prun. cbn [eruns psel].
  pose proof (Hpans o q (conc st q) h).
  replace (peek_answer_ok (pans o q (conc st q) h)) with true.
  2:{ symmetry. unfold peek_answer_ok. apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
  reflexivity.
Qed.

Lemma rd16_oracle {R} o st q (k : Z -> M R) :
  prun o (rd16 st q k) = prun o (k (rdv o st q + 256 * rdv o st (aadd q 1))).
Proof. unfold rd16. rewrite rd8_oracle, rd8_oracle. reflexivity. Qed.

Lemma land_opp_pow2' k : 0 <= k -> Z.land (2 ^ k) (- 2 ^ k) = 2 ^ k.
Proof.
  intros Hk. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_opp, Z.pow2_bits_eqb by lia.
  rewrite <- Z.ones_equiv, Z.testbit_ones by lia.
  destruct (Z.eqb_spec k i); cbn [andb]; [|reflexivity].
  subst. replace (i <? i) with false by (symmetry; apply Z.ltb_irrefl). destruct (0 <=? i); reflexivity.
Qed.
Lemma ctz32_pow2' k : 0 <= k -> ctz32 (2 ^ k) = k.
Proof. intros. unfold ctz32, lowbit. rewrite land_opp_pow2' by lia. apply Z.log2_pow2. lia. Qed.

Lemma get_meta_rec_upd_same st g f : get_meta_rec (upd_meta g f st) g = f (get_meta_rec st g).
Proof. unfold get_meta_rec at 1. unfold upd_meta, put_meta. cbn. rewrite lookup_insert_eq. reflexivity. Qed.

(* [comment removed for export] *)
Lemma malloc_core_fast st n g k :
  let sc := size_to_class n in
  let mr := get_meta_rec st g in
  size_overflows n = false -> n < MMAP_THRESHOLD ->
  active st sc = Some g -> 0 < m_avail mr -> 0 <= k -> lowbit (m_avail mr) = 2 ^ k ->
  malloc_core full_lay st n = ret (upd_meta g (m_set_avail (m_avail mr - 2 ^ k)) st, Some (g, k)).
Proof.
  intros sc mr OV TH ACT AV K0 LB.
  unfold malloc_core. rewrite OV. replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia).
  unfold malloc_small_ctrl. fold sc. rewrite ACT. rewrite ACT. fold mr. rewrite LB.
  assert (P : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  replace (2 ^ k =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
  rewrite ctz32_pow2' by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma malloc_fast_model o st n g k :
  let sc := size_to_class n in
  let st1 := set_tick (N.succ (s_tick st)) st in
  let mr := get_meta_rec st1 g in
  let st2 := upd_meta g (m_set_avail (m_avail mr - 2 ^ k)) st1 in
  let stride := get_stride mr in
  let slack := (stride - IB - n) / UNIT in
  let p0 := slot_start' mr k in
  let ctr := c_mmap_counter (ctx st) in
  let b3 := rdv o st2 (aadd p0 (-3)) in
  let v16 := rdv o st2 (aadd p0 (-2)) + 256 * rdv o st2 (aadd (aadd p0 (-2)) 1) in
  let off0 := (if b3 =? 0 then Z.land ctr 255 else Z.land (v16 + 1) 255) in
  let off := fold_off off0 slack in
  size_overflows n = false -> n < MMAP_THRESHOLD ->
  active st sc = Some g -> 0 < m_avail mr -> 0 <= k -> lowbit (m_avail mr) = 2 ^ k ->
  prun o (malloc st n) = SRet (o, (havoc (snd (enframe_at st2 g k n off)) n (fst (enframe_at st2 g k n off)),
                                   Some (snd (enframe_at st2 g k n off)))).
Proof.
  intros sc st1 mr st2 stride slack p0 ctr b3 v16 off0 off OV TH ACT AV K0 LB.
  unfold malloc. fold st1.
  rewrite (malloc_core_fast st1 n g k OV TH ACT AV K0 LB). unfold Malloc.ret. rewrite sbind_ret_l.
  unfold enframe_full, enframe_read_off. fold st2. rewrite (get_meta_rec_upd_same st1 g). fold mr.
  set (K := fun off' : Z => let '(st3, p) := enframe_at st2 g k n off' in @SRet ev Z _ (havoc p n st3, Some p)).
  change (prun o (rd8 st2 (aadd p0 (-3)) (fun b => if negb (b =? 0)
             then rd16 st2 (aadd p0 (-2)) (fun o16 => K (fold_off (Z.land (o16 + 1) 255) slack))
             else K (fold_off (Z.land ctr 255) slack)))
          = SRet (o, (havoc (snd (enframe_at st2 g k n off)) n (fst (enframe_at st2 g k n off)), Some (snd (enframe_at st2 g k n off))))).
  rewrite rd8_oracle. cbv beta. fold b3.
  assert (FIN : forall off', off' = off -> prun o (K off') = SRet (o, (havoc (snd (enframe_at st2 g k n off)) n (fst (enframe_at st2 g k n off)), Some (snd (enframe_at st2 g k n off))))).
  { intros off' ->. unfold K. destruct (enframe_at st2 g k n off) as [st3 p]. reflexivity. }
  destruct (Z.eqb_spec b3 0) as [E|NE]; cbn [negb].
  - apply FIN. unfold off, off0. replace (b3 =? 0) with true by (symmetry; apply Z.eqb_eq; exact E). reflexivity.
  - rewrite rd16_oracle. cbv beta. apply FIN. unfold off, off0. replace (b3 =? 0) with false by (symmetry; apply Z.eqb_neq; exact NE). reflexivity.
Qed.
End FASTMODEL.

End CANSEC2.
