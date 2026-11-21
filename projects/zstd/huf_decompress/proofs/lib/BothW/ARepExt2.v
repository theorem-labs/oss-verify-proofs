(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (2 recorded proofs replaced by written proofs (pre_clear, AREP_frame_pre)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase ABytes AModelFacts ARep ALayout AHeapP ARepKit ARepFrame ARepExt.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ARepExt2 () := "C59OSSVerify5KrLib5BothW7ARepExt>filter_cons_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List6filterI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4al_tC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addI47Corelib5Lists7ListDef6Forall00K47Corelib4Init9Datatypes4list01K47Corelib5Lists7ListDef6Forall01K47Corelib4Init9Datatypes4list02c59OSSVerify5KrLib5BothW8ARepExt24apreC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7f_equalC59OSSVerify5KrLib5BothW7ARepExt8nonemptyC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8ltb_specC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init9Datatypes8BoolSpec00I47Corelib4Init5Logic3and00C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib5Lists7ListDef6Forall02C47Corelib4Init9Datatypes8list_indC59OSSVerify5KrLib5BothW7ARepExtDdisjoint_from_ForallC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I59OSSVerify5KrLib5BothW5ABase7alayout00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4bool00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4bool01C46Stdlib5Lists4List2InC46Stdlib5Lists4List7existsbK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I59OSSVerify5KrLib5BothW7ALayout:alayout_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep4AREPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARepExtEmunch_filter_nonemptyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout7ao_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7al_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout4aobjC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout8aobj_imgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4sclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4iclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst9ATOP_al16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout=alayout_spaceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_space_begC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib5BothW7ALayout4ao_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout6ao_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout6ao_resC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout6al_resC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout8ao_nodesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8al_nodesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout8ao_storeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8al_storeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout9ao_res_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout8ao_spaceC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARepExt29pre_clearC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout9ad_t_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout5adisjC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout;ad_ctx_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout;ad_fake_resC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout=ad_nodes_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout=ad_store_fakeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega=RingMicromega5Psatz07C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame8shad_divC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib5BothW9ARepFrame9shlen_divC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout8ad_t_resC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout8ad_t_ctxC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C59OSSVerify5KrLib5BothW4ARep3awfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7arep_rtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep9ainstanceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7athreadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<aslot_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep=ashadow_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7ah_quarC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6ah_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8ah_depotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6arelroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7get_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5x_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=size_of_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl@c_allocated_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=c_mapped_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;c_num_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlCc_mapped_free_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xc_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xc_cacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7c_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xb_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep4xb_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<rounded_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7rz_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_b1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib5BothW4ARep6xb_ctxC1?~~~~~~~~~~~~~~~I35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupC59OSSVerify5KrLib4Spec8AsanCtrl6a_liveC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6achunk01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib5BothW4ARep6x_busyC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib5BothW9ARepFrame8rt_hullsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame=arep_rt_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nresC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nsecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame?ainstance_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_botC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<acache_cellsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib5BothW4ARep7junk_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame;cells_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_cinitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep;acache_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrameBacache_cells_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame:junk_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame<u64arr_frameC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib5BothW4ARep=aregion_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:afreearrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6aslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrameCsize_of_class_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame;aregion_modC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7aregionC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib5BothW4ARep<aregion_infoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrameCaregion_cells_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8afreearrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame9shad_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame<shlen_nonnegC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03C59OSSVerify5KrLib5BothW9ARepFrame>shad_add_shlenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame@afreearray_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5ndistC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib5BothW9ARepFrame>slot_in_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:aslot_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7busy_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xb_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame7xb_fitsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4andbC46Stdlib5Lists4List9find_someC46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC59OSSVerify5KrLib5BothW9ARepFrame8awf_fitsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib5BothW4ARep:aslot_busyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame=aslots_updateC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame<slot_alignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame>mod16_of_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib5BothW4ARepAslot_shadow_bytesC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrameCaslot_shadow_updateC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xb_allocC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:in_app_iffC59OSSVerify5KrLib5BothW4ARep:busy_slotsC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:in_map_iffC46Stdlib5Lists4List9filter_InC56Stdlib6ZArith6BinInt1Z8eqb_reflK47Corelib4Init5Logic2or02C46Stdlib5Lists4List=Forall_forallC56Stdlib6ZArith6BinInt1Z6ltb_ltC59OSSVerify5KrLib5BothW6AHeapP>quar_untouchedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_qlocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<a_qloc_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_qglobC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=a_qglob_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP9quar_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP8hq_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout7al_dtlsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP=sec_untouchedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP=sec_same_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP8hs_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout:ad_t_nodesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout:ad_t_storeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP8hd_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame<arelro_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame>arep_rt2_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrameCashadow_avail_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame>arep_rt3_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula03I46Stdlib5Lists4List5NoDup00C59OSSVerify5KrLib4Spec8AsanCtrl9max_countC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC59OSSVerify5KrLib4Spec8AsanCtrl6a_nextC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltK59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<K_SPACE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_SPACE_EXTRAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7K_ALIGNC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib5BothW5ABase7AIMG_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_NUM_CLASSESC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_OFFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:K_USER_MAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAPC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6aclass00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7aclass0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5xbusy00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_BATCH_CLASSC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib5BothW4ARep<ASTATS_WORDSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8K_REGIONC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase3KLSC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5aconc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed6ASHOFFC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6xclass00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6bstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AREQMAXC1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC59OSSVerify5KrLib5BothW5ABase9AINSTANCEC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consI46Stdlib5Lists4List6Exists00I59OSSVerify5KrLib4Spec8AsanCtrl6abatch00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9ARELRO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9ARELRO_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame9rt3_hullsC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition apre (L : alayout) (iv : Z * Z) : Prop :=
  fst iv < snd iv -> ATOP <= fst iv \/ (fst iv = al_t L + 3168 /\ snd iv = al_t L + 3169).

(* [comment removed for export] *)
Lemma pre_clear : forall L W A k,
  Forall (apre L) W -> 0 <= k ->
  A + k <= ATOP -> (A + k <= al_t L + 3168 \/ al_t L + 3169 <= A) ->
  disjoint_from (List.filter nonempty W) A k.
Proof.
  intros L W A k EXT Hk D1 D2. apply disjoint_from_Forall.
  induction W as [|[lo hi] W IH]; [constructor|].
  inversion EXT as [| x l E1 E2]; subst.
  rewrite filter_cons_eq. unfold nonempty at 1. cbn [fst snd].
  destruct (Z.ltb_spec lo hi) as [LT|GE]; [| apply IH; exact E2].
  constructor; [| apply IH; exact E2]. cbn [fst snd].
  unfold apre in E1. cbn [fst snd] in E1. specialize (E1 LT).
  clear IH E2 EXT. lia.
Qed.

Section Ext2.
Variable H : aholes.
Hypothesis HL : ahole_laws H.

Theorem AREP_frame_pre : forall L st X m m' W,
  alayout_ok L -> AREP H L st X m -> munch W m m' -> wmono bsegs m m' ->
  Forall (apre L) W ->
  rw_cells bsegs m' (al_t L + 3168) [C1 (Z_to_bv 8 0)] ->
  AREP H L st X m'.
Proof.
  intros L st X m m' W ALO AR MU0 WM EXT UNW'.
  pose proof (munch_filter_nonempty W m m' MU0) as MU. clear MU0. set (W' := List.filter nonempty W) in *.
  (* [comment removed for export] *)
  pose proof (ao_fake L ALO) as FK. pose proof (aobj_img _ _ FK ltac:(lia)) as FKI. unfold aobj in FK. destruct FK as (FK3 & FK1 & FK2 & FKS & _).
  unfold sclr, KLS in FKS. unfold AIMG_HI in FKI. pose proof atop_range as ATR. pose proof ATOP_al16 as ATA.
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
  pose proof (ao_res_hi L ALO) as ORH.
  unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OT, OC, ORS, ON, OS. pose proof (ao_space L ALO) as RSP.
  pose proof (fun A k => pre_clear L W A k EXT) as KX. cbn beta in KX. fold W' in KX.
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_ctx_fake L ALO) as D_c_f. pose proof (ad_fake_res L ALO) as D_f_res.
  pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  unfold adisj in D_t_f, D_c_f, D_f_res, D_n_f, D_s_f.
  assert (SAT : 0x10006fef8000 <= shad ATOP <= 0x10007fef8000) by (rewrite shad_div; unfold ASHOFF; clear -ATR; Z.div_mod_to_equations; lia).
  assert (SHRES : 2201439137792 <= shad (al_res L) /\ shad (al_res L) + shlen 137439023104 = shad (al_res L + 137439023104)
                  /\ shad (al_res L + 137439023104) <= shad ATOP).
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -ORS ORH. Z.div_mod_to_equations. lia. }
  destruct SHRES as (SR1 & SR2 & SR3).
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_t_ctx L ALO) as D_t_c. unfold adisj in D_t_res, D_t_c.
  (* [comment removed for export] *)
  assert (Kimg : forall A k, 0x10000 <= A -> 0 <= k -> A + k <= AIMG_HI -> disjoint_from W' A k).
  { intros A k H1 H2 H3. unfold AIMG_HI in H3. apply KX; [exact H2| clear -H3 ATR; lia| clear -H1 H3 OT; lia]. }
  assert (Kres_sh : forall A k, shad (al_res L) <= A -> 0 <= k -> A + k <= shad (al_res L + 137439023104) -> disjoint_from W' A k).
  { intros A k H1 H2 H3. apply KX; [exact H2| clear -H3 SR3 SAT ATR; lia| clear -H1 H3 SR1 SR3 SAT OT; lia]. }
  assert (Kobj : forall A k, 0 <= k -> A + k <= ATOP -> (A + k <= al_t L + 3168 \/ al_t L + 3169 <= A) -> disjoint_from W' A k).
  { intros A k H2 H3 H4. apply KX; [exact H2| exact H3| exact H4]. }
  clear KX.
  assert (Kres : forall A k, al_res L <= A -> 0 <= k -> A + k <= al_res L + 137439023104 -> disjoint_from W' A k).
  { intros A k H1 H2 H3. apply Kobj; [exact H2 | clear -H3 ORS; lia | clear -H1 H3 D_t_res; lia]. }
  assert (Kt : forall A k, al_t L <= A -> 0 <= k -> A + k <= al_t L + 3168 -> disjoint_from W' A k).
  { intros A k H1 H2 H3. apply Kobj; [exact H2 | clear -H3 OT; lia | left; exact H3]. }
  assert (Kctx : forall A k, al_ctx L <= A -> 0 <= k -> A + k <= al_ctx L + 65536 -> disjoint_from W' A k).
  { intros A k H1 H2 H3. apply Kobj; [exact H2 | clear -H3 OC; lia | clear -H1 H3 D_t_c; lia]. }
  (* [comment removed for export] *)
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  split; [exact WF|].
  split. { eapply arep_rt_frame; [exact MU | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
           repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia] |]). apply Forall_nil. }
  split. { eapply ainstance_frame; [exact MU | exact WM | exact INST | reflexivity | reflexivity | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  split.
  { destruct THR as (T0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW). unfold athread.
    split; [eapply cells_frame; [exact T0 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
    split; [eapply cells_frame; [exact T40 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
    split. { intros c Hc. eapply acache_cells_frame; [exact MU | exact WM | exact (CACHES c Hc) | reflexivity | reflexivity | reflexivity |].
             unfold acache_addr. unfold K_NUM_CLASSES in Hc. apply Kt; clear -Hc; lia. }
    split; [eapply junk_frame; [exact CSTATS | exact MU | exact WM | intros _; apply Kt; clear; lia]|].
    split; [exists sj; split; [eapply u64arr_frame; [exact STATS | exact MU | exact WM | replace (8 * Z.of_nat (length sj)) with 368 by (rewrite LSJ; reflexivity); apply Kt; clear; lia] | exact LSJ]|].
    exact UNW'. }
  split.
  { intros c Hc. destruct (CLS c Hc) as (REG & FARR & SLOTS & SHADOW).
    destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QLENF & QLENC & QCNTB & QND & QRANGE).
    pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. unfold K_NUM_CLASSES in Hc.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
    destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MU | exact WM | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      apply Kres; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE; change (2^37) with 137438953472; clear -Hc RSP; lia.
    - eapply afreearray_frame; [exact MU | exact WM | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + apply Kres; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear -RI1; lia | clear -Q5 Q6; lia | clear -RI2 RI3 Q6; lia].
      + apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear -RI1; lia | apply shlen_nonneg; clear -Q5 Q6; lia |].
        rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
        unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -RI2 RI3 Q6. lia.
    - eapply (aslots_update L W' m m' MU WM st st X X c (-1)); [exact SLOTS | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia].
      + intros k Hk _. pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
        split; [reflexivity|]. split.
        * apply Kres; [clear -P5 RI1; lia | clear -QS; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
        * intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
          apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
          split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
      + intros POS. apply Kres; [clear -Q1 RI1; lia | clear -POS; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
    - eapply (aslot_shadow_update L W' m m' MU WM st st X X c (-1)); [exact SHADOW | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
      + intros k Hk _. pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
        pose proof (slot_aligned L c k SAL ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) as AL.
        split; [reflexivity|]. apply Kres_sh; [apply shad_mono; clear -P5 RI1; lia | apply shlen_nonneg; clear -QS; lia |].
        rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
      + intros POS. apply Kres_sh; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
        rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
        apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }
  (* [comment removed for export] *)
  assert (BB : forall b, In b (x_busy X) -> al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP. lia. }
  split.
  { eapply (hq_frame _ HL L st st X X m m' W'); [exact HQ | exact MU | exact WM | |].
    - unfold quar_untouched. apply Forall_forall. intros [lo hi] Hin. cbn [fst snd].
      unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin NE]. unfold nonempty in NE. cbn [fst snd] in NE. apply Z.ltb_lt in NE.
      pose proof (proj1 (Forall_forall _ _) EXT _ Hin) as E. unfold apre in E. cbn [fst snd] in E. specialize (E NE).
      unfold AINSTANCE in *.
      split; [clear -E OT ATR; lia|]. split; [clear -E OT ATR; lia|]. split; [clear -E OT ATR; lia|]. split; [clear -E OT ATR; lia|].
      intros b Hb. destruct (BB b Hb) as [B1 B2]. destruct (xb_st b); [exact I| |]; clear -E B1 B2 ORS D_t_res ATR; lia.
    - unfold quar_same. repeat (split; [reflexivity|]). split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
  split.
  { eapply (hs_frame _ HL L st st X X m m' W'); [exact HS | exact MU | exact WM | |].
    - unfold sec_untouched, aknown. apply Forall_forall. intros [lo hi] Hin a Ha. cbn [fst snd] in Ha.
      unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin NE].
      pose proof (proj1 (Forall_forall _ _) EXT _ Hin) as E. unfold apre in E. cbn [fst snd] in E. specialize (E ltac:(clear -Ha; lia)).
      clear -E Ha OT ATR. destruct E as [E|[E1 E2]]; [do 4 right; left; lia| do 5 right; left; lia].
    - apply sec_same_refl. }
  split.
  { eapply (hd_frame _ HL L m m' W'); [exact HD | exact MU | exact WM |].
    apply Forall_forall. intros [lo hi] Hin a Ha. cbn [fst snd] in Ha.
    unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin NE].
    pose proof (proj1 (Forall_forall _ _) EXT _ Hin) as E. unfold apre in E. cbn [fst snd] in E. specialize (E ltac:(clear -Ha; lia)).
    pose proof (ad_t_nodes L ALO) as D_t_n. pose proof (ad_t_store L ALO) as D_t_s. unfold adisj in D_t_n, D_t_s.
    clear -E Ha OT ON OS D_t_n D_t_s ATR. lia. }
  split; [eapply arelro_frame; [exact MU | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]|].
  split; [eapply arep_rt2_frame; [exact MU | exact WM | exact RT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia|].
  split; [| eapply arep_rt3_frame; [exact MU | exact WM | exact RT3 |]; unfold rt3_hulls;
            repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia |]); apply Forall_nil].
  intros c Hc. destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). unfold K_NUM_CLASSES in Hc.
  assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
               /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
  { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
  destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
  eapply (ashadow_avail_frame L W' m m' MU WM st); [exact (AVL c ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) | reflexivity | reflexivity | |].
  - intros POS. apply Kres_sh; [apply shad_mono; unfold aregion in *; clear -Q1 RI1; lia | clear -POS; lia |].
    rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
    apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
  - intros POS. apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
    rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
    apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia.
Qed.
End Ext2.
End CANSEC1.
