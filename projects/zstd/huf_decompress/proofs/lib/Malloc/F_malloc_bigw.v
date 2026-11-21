(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (7 recorded proofs replaced by written proofs (unmap_seqs_empty, big_ml_eq, cell_read_hdr_havoc_fresh and 4 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast MallocTree MallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_malloc_bigw () := "C35stdpp4base6LookupC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~I35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeK35stdpp8fin_maps6FinMap01C47Corelib4Init5Logic8eq_ind_rI35stdpp4gmap4gmap00C35stdpp8fin_maps:map_eq_iffC35stdpp8fin_maps@lookup_insert_eqC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib6Malloc9MallocRep5zerosC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes3nat02I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z9mod_smallC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z9land_onesc59OSSVerify5KrLib6Malloc=F_malloc_bigw6big_mlC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic4True00K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C35stdpp6option;from_optionC59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6shadow01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K59OSSVerify5KrLib4Spec6Malloc7cellval02C1?~~~~~~~~~~~~~~~C35stdpp4base5emptyC59OSSVerify5KrLib4Spec6Malloc8stale_pgC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5staleC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbC59OSSVerify5KrLib4Spec6Malloc7hav_addC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z6ltb_ltK46Stdlib9micromega5Tauto8GFormula03C47Corelib4Init5Logic6eq_symK47Corelib4Init5Logic2ex01K47Corelib4Init9Datatypes4prod01C45stdpp;list_basics4list;list_filterC47Corelib4Init9Datatypes3fstC46Stdlib4Bool4Bool7Is_trueC35stdpp9decidable;Is_true_decC35stdpp4base6filterC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC35stdpp8fin_maps<lookup_emptyC35stdpp4base6insertC59OSSVerify5KrLib4Spec6Malloc:set_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9hdr_havocC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableC59OSSVerify5KrLib4Spec6Malloc7shadow0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableK47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z3lorC45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib6Common6StrFun7lor_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2c59OSSVerify5KrLib6Malloc=F_malloc_bigw9big_ml_eqC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4meta01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc=F_malloc_bigw8big_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_wordC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=F_malloc_free3sxvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3u32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mod_modC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC59OSSVerify5KrLib6Malloc=F_malloc_free9sxv_mod32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=F_malloc_free9sxv_congrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=F_malloc_free9sxv_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep;wz_unsignedC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapC59OSSVerify5KrLib6Malloc=F_malloc_free9addw_wordC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib6Malloc9MallocRep<mod_mod_pow2C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedC59OSSVerify5KrLib6Malloc=F_malloc_free9le4_congrC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkapp".
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.

Section CANSEC1. Context {rc : runConstT}.
Lemma unmap_seqs_empty st : unmap_seqs (upd_ctx (fun c => set_unmap_seq_map ∅ c) st) = zeros 32.
Proof. reflexivity. Qed.
End CANSEC1.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_A2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require StrFun.

Section CANSEC2. Context {rc : runConstT}.
Definition big_ml (n : Z) : Z := Z.land ((n + IB + UNIT + 4095) / 4096) (2^52 - 1).
Definition big_meta (rid : N) (n : Z) : meta := mkMeta None None (Some (rid, 0)) 0 0 0 1 63 (big_ml n).
Definition big_metaA (rid : N) : meta := mkMeta None None (Some (rid, 0)) 0 0 0 0 0 0.
(* [comment removed for export] *)
Definition big_st (st : mstate) (g : aptr) (rid : N) (n v : Z) : mstate :=
  upd_ctx (set_mmap_counter v)
    (put_meta g (big_meta rid n)
      (put_group (rid, 0) (Some g) 0 (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st)))).

Lemma big_ml_eq n : 0 <= n < 2^32 -> big_ml n = (n + 4115) / 4096.
Proof.
  intros Hn. unfold big_ml, IB, UNIT. change (2^52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia.
  replace (n + 4 + 16 + 4095) with (n + 4115) by lia. apply Z.mod_small. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma cell_read_hdr_havoc_fresh : forall st b o,
  (s_shadow st) !! (fst b) = None -> snd b mod 16 = 0 -> 0 <= o < 12 ->
  exists h, cell_read (get_shadow (hdr_havoc b st) (fst b)) (snd b + o) = Unknown h.
Proof.
  intros st b o SH B16 Ho. unfold hdr_havoc, get_shadow, upd_shadow. cbn [s_shadow set_shadow].
  rewrite lookup_insert_eq. cbn [default from_option id]. unfold get_shadow. rewrite SH. cbn [default from_option id r_cells r_hav r_havp shadow0].
  unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite !lookup_empty.
  replace ((snd b + o) / 16) with (snd b / 16) by (Z.div_mod_to_equations; lia).
  rewrite lookup_insert_eq. cbn [default from_option id]. unfold hav_add. cbn.
  replace ((snd b + o) mod 16) with o by (Z.div_mod_to_equations; lia).
  replace (o <? 12) with true by (symmetry; apply Z.ltb_lt; lia). cbn. eexists. reflexivity.
Qed.

Lemma big_word_eq rid n : 0 <= n < 2^32 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (n + 4115))) 12))) 12))) 4064)
  = wz (meta_word (big_meta rid n)).
Proof.
  intros Hn. unfold meta_word, big_meta. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite big_ml_eq by lia.
  rewrite (unsigned_lit (n + 4115)) by lia. rewrite Z.shiftr_div_pow2 by lia.
  rewrite (unsigned_lit ((n + 4115) / 2 ^ 12)) by (Z.div_mod_to_equations; lia). rewrite Z.shiftl_mul_pow2 by lia.
  rewrite unsigned_lit by (Z.div_mod_to_equations; lia). change (2 ^ 12) with 4096.
  rewrite (StrFun.lor_add _ _ 12); [| lia| lia| change (2 ^ 12) with 4096; Z.div_mod_to_equations; lia].
  unfold wz. f_equal. lia.
Qed.

Lemma meta_word_big_range rid n : 0 <= n < 2^32 -> 0 <= meta_word (big_meta rid n) < 2^64.
Proof.
  intros Hn. unfold meta_word, big_meta. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite big_ml_eq by lia.
  Z.div_mod_to_equations. lia.
Qed.

Lemma ctr_word c : 0 <= c -> Z_to_bv 64 (bv_swrap 32 (bv_unsigned (wz (sxv c)) + 1)) = wz (sxv (u32 (c + 1))).
Proof.
  intros Hc. rewrite addw_word. rewrite wz_unsigned by apply sxv_range. f_equal. apply sxv_congr.
  unfold u32. rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma le4_sxv v : le4 (wz (sxv v)) = le4 (wz v).
Proof.
  apply le4_congr. rewrite wz_unsigned by apply sxv_range. rewrite sxv_mod32.
  unfold wz. rewrite Z_to_bv_unsigned. change (bv_modulus 64) with (2^64). symmetry. apply MallocRep.mod_mod_pow2. lia.
Qed.

Section SUCC.
Variables (st : mstate) (m : mem) (g : aptr) (rid : N) (x n c lo : Z).
Let G := conc st g.
Hypothesis TK : ticks_ok st.
Hypothesis G0 : get_meta_rec st g = meta0.
Hypothesis MSL : meta_slot st g.
Hypothesis RR : (s_regions st) !! rid = Some (mkRegion RKGroup x (n + IB + UNIT)).
Hypothesis GN : forall off, (s_groups st) !! (rid, off) = None.
Hypothesis AN : forall off, (s_areas st) !! (rid, off) = None.
Hypothesis SHN : (s_shadow st) !! rid = None.
Hypothesis HC : c_mmap_counter (ctx st) = c.
Hypothesis CR : 0 <= c < 2^32.
Hypothesis NR : MMAP_THRESHOLD <= n < 2^32.
Hypothesis CLO : ATOP <= lo.
End SUCC.

End CANSEC2.
