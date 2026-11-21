(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (15 recorded proofs replaced by written proofs (guard_true, size_class_28, guard16_arith and 12 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Shadow MI_Read MI_Pres1 MI_Pres2.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_WFree () := "I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC47Corelib4Init5Logic6eq_indI35stdpp9countable9Countable00C35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC59OSSVerify5KrLib4Spec6Malloc@get_nominal_sizeC1?~~~~~~~~~~~~~~~C35stdpp4base4fmapC35stdpp4base6LookupC59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5guardC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic8eq_transI35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List8map_consK47Corelib4Init5Logic2eq01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6to_natK47Corelib4Init9Datatypes3nat02C47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib4Init5Logic2ex01I47Corelib4Init5Logic2ex00K47Corelib7Numbers7BinNums1Z02K46Stdlib9micromega6VarMap1t01C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C47Corelib5Lists7ListDef3nthI47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib4Spec6Malloc<size_classesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succK47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_mulK46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega=RingMicromega5Psatz03I47Corelib4Init5Logic5False00C59OSSVerify5KrLib4Spec6MI_Inv3blkC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6in_mapI59OSSVerify5KrLib4Spec6MI_Inv5inv_R00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_A00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_G00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv6inv_SH00C1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib4Spec8MI_WFree9blk_facts00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib4Spec6MI_Inv9is_blocksC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6MI_Inv5bslotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupK47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6MI_Inv4boffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5bsizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv2MRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8is_validC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv:live_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5hostsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5ig_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6MI_Inv8group_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom9hosts_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6sstartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom>slot_start'_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv9g_presentC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib4Spec6MI_Inv8ia_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5mslotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8ia_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv;is_metakindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7a_checkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7is_partC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib4Spec6MI_Inv6x_pendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4one5C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4g_liC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib4Spec6MI_Inv4g_aiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Geom9stride_geC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7g_alignC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib4Spec6MI_Inv4g_scC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7in_listC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8g_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv6cnt_ofC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC47Corelib4Init9Datatypes4negbC47Corelib4Init9Datatypes4andbK47Corelib4Init5Logic2or01C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z7eqb_neqK47Corelib4Init5Logic2or02C59OSSVerify5KrLib4Spec6MI_Inv5g_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8g_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7ish_blkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv8ish_hdr0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2leC59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv9ish_ticksC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib4Spec7MI_Read:known_byteC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib4Spec8MI_WFree9blk_facts01C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4Spec6MI_Inv8frontierC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8a_nslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4tbitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indC59OSSVerify5KrLib4Spec6MI_Inv4gendC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableC45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WFree4bf_cC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC35stdpp6option;from_optionc59OSSVerify5KrLib4Spec8MI_WFree6bf_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv5gbaseC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01c59OSSVerify5KrLib4Spec8MI_WFree9bf_shadowC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3minC59OSSVerify5KrLib4Spec6MI_Inv7byte_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv7unknownC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WFree9bf_strideC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modK46Stdlib9micromega7EnvRing3Pol02C59OSSVerify5KrLib4Spec6MI_Inv5knownC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WFree8gbase_bmC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WFree5c_sndC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WFree6bf_b16C1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Zdiv:Z_mod_multc59OSSVerify5KrLib4Spec8MI_WFree5p_sndC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WFree6bf_fitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WFree4bf_nC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WFree;get_meta_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WFree:guard_trueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Read9rd8_knownC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8get_metaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WFree6ea_sndC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8MI_WFreeCget_nominal_size_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:slot_startC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3wr8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4wr16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3retC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8free_hdrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc<undef_reason03C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma guard_true {R} tag (c : bool) (k bail : M R) : c = true -> guard tag c k bail = k.
Proof. intros ->. reflexivity. Qed.

Lemma size_class_28 sc : 28 <= sc < 48 -> 292 <= size_class sc.
Proof.
  intros H. unfold size_class.
  assert (E : exists n, Z.to_nat sc = (28 + n)%nat /\ (n < 20)%nat) by (exists (Z.to_nat sc - 28)%nat; lia).
  destruct E as (n & -> & Hn).
  do 20 (destruct n as [|n]; [cbn; lia|]). lia.
Qed.

(* [comment removed for export] *)
Lemma guard16_arith S stride i off n q last :
  1 <= S -> 16 * q = stride * i + 16 * off -> 16 * off + n <= stride - 4 -> 0 <= n -> 0 <= off <= 255 -> 0 <= i <= last ->
  (stride = 16 * S \/ last = 0) -> (stride <= 16 * S \/ 292 <= S) ->
  S * i <= q < S * (i + 1).
Proof.
  intros HS Hq Hfit Hn Hoff Hi A B.
  destruct A as [E|L0].
  - subst stride. assert (q = S * i + off) by lia. subst q. nia.
  - assert (i = 0) by lia. subst i. assert (q = off) by lia. subst q. lia.
Qed.

Lemma guard17_arith stride i off n q last maplen :
  16 <= stride -> 16 * q = stride * i + 16 * off -> 16 * off + n <= stride - 4 -> 0 <= n -> 0 <= off -> 0 <= i <= last ->
  16 + stride * (last + 1) <= maplen * 4096 ->
  q <= maplen * 4096 / 16 - 1.
Proof.
  intros. replace (maplen * 4096 / 16) with (maplen * 256) by (rewrite <- (Z.div_mul (maplen * 256) 16) by lia; f_equal; lia).
  assert (stride * i + stride <= stride * (last + 1)) by nia. lia.
Qed.

(* [comment removed for export] *)
Section BLOCK.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Variables (c : cptr) (off n : Z).
Hypothesis Hk : In ((c, off), n) BL.

Local Notation R := (MR st).

Record blk_facts (m bm : aptr) (i ai : Z) (a : aptr) (ar : area) (ka : Z) : Prop := mkBF {
  bf_slot : s_slots st !! c = Some (m, i);
  bf_hosts : s_groups st !! bm = Some (mkGhdr (Some m) ai);
  bf_mem : m_mem (R m) = Some bm;
  bf_c : c = (fst bm, sstart (R m) i);
  bf_i : 0 <= i <= m_last_idx (R m);
  bf_li : m_last_idx (R m) <= 31;
  bf_ai : 0 <= ai <= m_last_idx (R m);
  bf_off : 0 <= off <= 255;
  bf_n : 0 <= n;
  bf_fit : UNIT * off + n <= get_stride (R m) - IB;
  bf_stride : UNIT <= get_stride (R m) /\ get_stride (R m) mod UNIT = 0;
  bf_b16 : 0 <= snd bm /\ snd bm mod UNIT = 0;
  bf_notA : tbit (m_avail (R m)) i = false;
  bf_notF : tbit (m_freed (R m)) i = false;
  bf_notH : s_groups st !! c = None;
  bf_sc : (0 <= m_sizeclass (R m) < 48 /\ (get_stride (R m) <= UNIT * size_class (m_sizeclass (R m)) \/ 28 <= m_sizeclass (R m))
            /\ (get_stride (R m) = UNIT * size_class (m_sizeclass (R m)) \/ (m_last_idx (R m) = 0 /\ m_maplen (R m) <> 0)))
          \/ m_sizeclass (R m) = 63;
  bf_top : m_maplen (R m) <> 0 -> snd bm = 0 /\ gend (R m) <= m_maplen (R m) * 4096;
  bf_maplen : 0 <= m_maplen (R m);
  bf_area : s_areas st !! a = Some ar /\ a_check ar = c_secret (s_ctx st) /\ snd a mod PGSZ = 0 /\ 0 <= ka < NSLOTS /\ m = mslot a ka;
  bf_shadow : blk_shadow_ok st ((c, off), n) m i;
  bf_hdr0 : known st (fst bm, sstart (R m) (i + 1) - IB) 0;
  bf_bytes : forall q v, cell_read (get_shadow st (fst q)) (snd q) = Known v -> 0 <= v < 256
}.

Lemma block_facts : exists m bm i ai a ar ka, blk_facts m bm i ai a ar ka.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (is_blocks _ _ _ IS _ Hk) as (m & i & Hs & Hoff & Hn & Hfit). cbn [bslot boff bsize fst snd] in Hs, Hoff, Hn, Hfit.
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bm Hm] & Hi & Ec).
  pose proof Hm as [ai Hm'].
  pose proof (ig_ok _ _ _ IG _ _ _ Hm') as GO.
  pose proof (hosts_mem _ _ _ IM _ _ Hm) as Hmem.
  rewrite (slot_start'_eq _ _ _ IM _ _ _ Hm) in Ec.
  pose proof (g_present _ _ _ _ _ _ GO) as Pr. destruct (s_metas st !! m) as [mr|] eqn:Em; [| congruence].
  destruct (ia_metas _ IA _ _ Em) as (a & ar & ka & Ha & Hka & Emk).
  destruct (ia_areas _ IA _ _ Ha) as ((r & Hr & Hmk & Hal & Hpg & Hfr) & Hck & Hns & _).
  exists m, bm, i, ai, a, ar, ka.
  pose proof (is_part _ _ _ IS _ _ _ _ Hm' Hi) as P. cbn zeta in P. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hm), <- Ec in P.
  assert (U : In c (map bslot BL)) by (change c with (bslot ((c, off), n)); apply in_map; exact Hk).
  unfold one5 in P.
  constructor; auto.
  - pose proof (g_li _ _ _ _ _ _ GO). lia.
  - exact (g_ai _ _ _ _ _ _ GO).
  - exact (stride_ge _ _ _ IG _ _ Hm).
  - exact (g_align _ _ _ _ _ _ GO).
  - destruct (tbit (m_avail (R m)) i) eqn:E; [exfalso; tauto| reflexivity].
  - destruct (tbit (m_freed (R m)) i) eqn:E; [exfalso; tauto| reflexivity].
  - destruct (s_groups st !! c) eqn:E; [| reflexivity]. exfalso. assert (s_groups st !! c <> None) by congruence. tauto.
  - destruct (g_sc _ _ _ _ _ _ GO) as [[Hsc Hml]|(Hsc & Hli & Hml & _)]; [left| right; exact Hsc].
    destruct (g_stride _ _ _ _ _ _ GO ltac:(lia)) as (S1 & S2 & S3).
    split; [exact Hsc|]. split; [exact S1|].
    unfold get_stride. destruct (m_last_idx (R m) =? 0) eqn:E0; destruct (m_maplen (R m) =? 0) eqn:EM; cbn [andb negb];
      first [left; reflexivity | right; split; [apply Z.eqb_eq; exact E0| apply Z.eqb_neq; exact EM]].
  - intros Hml. destruct (g_top _ _ _ _ _ _ GO Hml) as (H0 & r' & _ & _ & _ & Hge). auto.
  - exact (g_maplen _ _ _ _ _ _ GO).
  - exact (ish_blk _ _ ISH _ m i Hk Hs).
  - apply (ish_hdr0 _ _ ISH _ _ _ Hm). unfold cnt_of. lia.
  - intros q v Hq. eapply known_byte; [| exact Hq]. intros sh o' v' t Hsh Hc. exact (proj1 (proj1 (ish_ticks _ _ ISH _ _ Hsh) o' v' t Hc)).
Qed.
End BLOCK.

Section HDR.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off n : Z).
Variables (m bm : aptr) (i ai : Z) (a : aptr) (ar : area) (ka : Z).
Hypothesis BF : blk_facts st c off n m bm i ai a ar ka.
Local Notation R := (MR st).
Let p : aptr := aadd c (UNIT * off).
Let stride := get_stride (R m).
Let e : Z := snd c + stride - IB.
Let res : Z := e - snd p - n.
Let q : Z := (snd p - snd bm - UNIT) / UNIT.

Lemma p_snd : snd p = sstart (R m) i + UNIT * off.
Proof. subst p. rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). reflexivity. Qed.
Lemma p_fst : fst p = fst bm.
Proof. subst p. rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). reflexivity. Qed.
Lemma gbase_bm : gbase (R m) = bm.
Proof. unfold gbase. rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF). reflexivity. Qed.
Lemma c_snd : snd c = sstart (R m) i.
Proof. rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). reflexivity. Qed.

Lemma q16 : UNIT * q = stride * i + UNIT * off /\ 0 <= q < 2^16.
Proof.
  destruct (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as (_ & _ & _ & _ & Q & _). cbn [bslot boff fst snd] in Q.
  rewrite gbase_bm in Q. subst q p. cbn [snd aadd] in *. rewrite c_snd in *. unfold sstart in *. rewrite gbase_bm in *.
  destruct (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S1 S2]. subst stride.
  replace (snd bm + UNIT + get_stride (R m) * i + UNIT * off - snd bm - UNIT) with (get_stride (R m) * i + UNIT * off) in Q |- * by lia.
  split; [| exact Q].
  unfold UNIT in *. pose proof (Z.div_mod (get_stride (R m)) 16 ltac:(lia)). rewrite S2 in H.
  replace (get_stride (R m) * i + 16 * off) with ((get_stride (R m) / 16 * i + off) * 16) by lia.
  rewrite Z.div_mul by lia. lia.
Qed.

Let SH := bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF.

Lemma p_mod16 : snd p mod 16 = 0.
Proof.
  rewrite p_snd. unfold sstart. rewrite gbase_bm.
  destruct (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S1 S2]. destruct (bf_b16 _ _ _ _ _ _ _ _ _ _ _ BF) as [B1 B2]. unfold UNIT in *.
  pose proof (Z.div_mod (get_stride (R m)) 16 ltac:(lia)). pose proof (Z.div_mod (snd bm) 16 ltac:(lia)).
  rewrite S2 in H. rewrite B2 in H0.
  replace (snd bm + 16 + get_stride (R m) * i + 16 * off) with ((snd bm / 16 + 1 + get_stride (R m) / 16 * i + off) * 16) by lia.
  apply Z_mod_mult.
Qed.

Lemma res_nonneg : 0 <= res.
Proof.
  subst res e p stride. cbn [snd aadd]. pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF). pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF). unfold IB, UNIT in *. lia.
Qed.

Lemma get_meta_eq {T} (k : aptr -> Z -> Z -> M T) bail : get_meta st p k bail = k m q i.
Proof.
  pose proof SH as S. unfold blk_shadow_ok in S. cbn [bslot boff bsize fst snd] in S. rewrite gbase_bm in S.
  destruct S as (K4 & K3 & K2 & K1 & Q & K5 & Kr & KU).
  pose proof res_nonneg as RES. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi. pose proof (bf_li _ _ _ _ _ _ _ _ _ _ _ BF) as Hli.
  unfold get_meta.
  rewrite (guard_true 10) by (apply Z.eqb_eq; exact p_mod16).
  unfold rd16.
  rewrite (rd8_known st (aadd p (-2)) (byte_of q 0)) by (eapply known_at; [exact K2| cbn; lia| reflexivity]).
  rewrite (rd8_known st (aadd (aadd p (-2)) 1) (byte_of q 1)) by (eapply known_at; [exact K1| cbn; lia| reflexivity]).
  rewrite (rd8_known st (aadd p (-3)) (i + 32 * Z.min res 5)) by (eapply known_at; [exact K3| cbn; lia| reflexivity]).
  rewrite (rd8_known st (aadd p (-4)) 0) by (eapply known_at; [exact K4| cbn; lia| reflexivity]).
  cbn [Z.eqb negb].
  rewrite (u16_bytes q Q).
  assert (Ebase : aadd p (- (UNIT * q) - UNIT) = bm).
  { pose proof q16 as [Q1 _]. pose proof p_snd as PS. pose proof p_fst as PF. unfold sstart in PS. rewrite gbase_bm in PS.
    subst stride. unfold aadd. destruct bm as [br bo]. cbn [fst snd] in *. f_equal; [exact PF| lia]. }
  rewrite Ebase. unfold get_group. rewrite (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF). cbn [g_meta].
  rewrite (land31_idx i (Z.min res 5)) by lia. fold (MR st m).
  rewrite (guard_true 11) by (rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF); apply optr_eqb_refl).
  rewrite (guard_true 12) by (apply Z.leb_le; lia).
  rewrite (guard_true 13) by (unfold testbit; rewrite (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF : Z.testbit _ _ = false); reflexivity).
  rewrite (guard_true 14) by (unfold testbit; rewrite (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF : Z.testbit _ _ = false); reflexivity).
  destruct (bf_area _ _ _ _ _ _ _ _ _ _ _ BF) as (Ha & Hck & Hal & Hka & Em).
  rewrite (guard_true 15) by (rewrite Em, (area_of_mslot a ka Hal Hka), Ha; apply Z.eqb_eq; exact Hck).
  pose proof q16 as [Q1 _]. pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as FIT. pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as N0.
  pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as OFF. fold stride in FIT.
  unfold UNIT, IB in Q1, FIT. fold stride in FIT.
  rewrite (guard_true 16).
  2:{ clear K4 K3 K2 K1 K5 Kr KU RES Ebase.
      destruct (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as [(Hsc & Hle & Hst)| E63].
      - fold stride in Hle, Hst. unfold UNIT in Hle, Hst.
        pose proof (size_class_bound _ Hsc) as SB.
        assert (A : stride = 16 * size_class (m_sizeclass (R m)) \/ m_last_idx (R m) = 0) by tauto.
        assert (B : stride <= 16 * size_class (m_sizeclass (R m)) \/ 292 <= size_class (m_sizeclass (R m))).
        { destruct Hle as [Hle|H28]; [left; exact Hle| right; apply size_class_28; lia]. }
        clearbody p stride e res q. clear SH Hle Hst.
        pose proof (guard16_arith _ _ _ _ _ _ _ (proj1 SB) Q1 FIT N0 OFF Hi A B) as [G1 G2].
        destruct (Z.ltb_spec (m_sizeclass (R m)) 48); [|lia].
        apply Bool.andb_true_iff. split; [apply Z.leb_le; exact G1| apply Z.ltb_lt; exact G2].
      - clearbody p stride e res q. clear SH. destruct (Z.ltb_spec (m_sizeclass (R m)) 48); [lia|]. apply Z.eqb_eq. exact E63. }
  rewrite (guard_true 17).
  2:{ clear K4 K3 K2 K1 K5 Kr KU RES Ebase.
      destruct (Z.eqb_spec (m_maplen (R m)) 0) as [|NM]; cbn [negb]; [reflexivity|].
      destruct (bf_top _ _ _ _ _ _ _ _ _ _ _ BF NM) as [B0 GE]. apply Z.leb_le.
      unfold gend, cnt_of, sstart in GE. rewrite gbase_bm, B0 in GE. fold stride in GE. unfold UNIT in GE.
      pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S1 _]. fold stride in S1. unfold UNIT in S1.
      clearbody p stride e res q. clear SH.
      eapply (guard17_arith stride i off n q); try eassumption; lia. }
  reflexivity.
Qed.


(* [comment removed for export] *)
Let ea : aptr := aadd (aadd bm (UNIT + stride * i)) (stride - IB).

Lemma ea_fst : fst ea = fst bm.
Proof.
ltac2:(KReplay.run1 (kr_t_MI_WFree ()) ["HDR"] "p;3p;2p1001bp4p70p102abp605=111111111111000R0p8p1007ip4p70P0p8P0p102b`p6051000p8P0p102c]p4p710p8P0p1006Ap4p710p8P0p10073p4p710p8P0p102dXp4p710p8g029Rj31Tg00;Xj20Tg02DaR0g00<2p,2bm510'0o"). Qed.
Lemma ea_snd : snd ea = e.
Proof. subst ea e stride. cbn [snd aadd]. rewrite c_snd. unfold sstart. rewrite gbase_bm. lia. Qed.

Lemma ea_off d : snd (aadd ea d) = e + d.
Proof. pose proof ea_snd as EA. unfold aadd at 1. cbn [snd]. rewrite <- EA. reflexivity. Qed.

Lemma get_nominal_size_eq {T} (k : Z -> M T) bail : get_nominal_size st p ea k bail = k n.
Proof.
  pose proof SH as S. unfold blk_shadow_ok in S. cbn [bslot boff bsize fst snd] in S. rewrite gbase_bm in S.
  destruct S as (K4 & K3 & K2 & K1 & Q & K5 & Kr & KU).
  pose proof res_nonneg as RES. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi. pose proof (bf_li _ _ _ _ _ _ _ _ _ _ _ BF) as Hli.
  pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as N0.
  pose proof ea_snd as EA. pose proof p_fst as PF. pose proof c_snd as CS.
  assert (CF : fst c = fst bm) by (rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF); reflexivity).
  assert (Hres : res = e - snd p - n) by reflexivity.
  assert (He : e = snd c + stride - IB) by reflexivity.
  assert (Hst : stride = get_stride (R m)) by reflexivity.
  assert (Hp2 : snd p = snd c + UNIT * off) by reflexivity.
  pose proof (bf_hdr0 _ _ _ _ _ _ _ _ _ _ _ BF) as H0. rewrite sstart_succ, <- CS, <- Hst in H0.
  (* [comment removed for export] *)
  assert (OFF : forall d, snd (aadd ea d) = snd c + get_stride (R m) - IB + d) by (intros d; rewrite ea_off, He, Hst; reflexivity).
  clearbody q. clear SH.
  unfold get_nominal_size.
  rewrite (rd8_known st (aadd p (-3)) (i + 32 * Z.min res 5)) by (eapply known_at; [exact K3| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
  cbv beta. rewrite (shiftr5_res i (Z.min res 5)) by lia. cbv zeta.
  destruct (Z.leb_spec 5 (Z.min res 5)) as [R5|R5].
  - (* [comment removed for export] *)
    destruct (K5 ltac:(lia)) as (B0 & B1 & B2 & B3 & B5 & R32).
    rewrite (guard_true 20) by (apply Z.eqb_eq; lia).
    unfold rd32.
    rewrite (rd8_known st (aadd ea (-4)) (byte_of res 0)) by (eapply known_at; [exact B0| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (rd8_known st (aadd (aadd ea (-4)) 1) (byte_of res 1)) by (eapply known_at; [exact B1| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (rd8_known st (aadd (aadd ea (-4)) 2) (byte_of res 2)) by (eapply known_at; [exact B2| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (rd8_known st (aadd (aadd ea (-4)) 3) (byte_of res 3)) by (eapply known_at; [exact B3| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (u32_bytes res) by lia.
    rewrite (guard_true 21) by (apply Z.leb_le; lia).
    rewrite (rd8_known st (aadd ea (-5)) 0) by (eapply known_at; [exact B5| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (guard_true 25) by reflexivity.
    rewrite (guard_true 22) by (apply Z.leb_le; rewrite EA; lia).
    rewrite (rd8_known st (aadd ea (- res)) 0) by (eapply known_at; [apply Kr; lia| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (guard_true 23) by reflexivity.
    rewrite (rd8_known st ea 0) by (eapply known_at; [exact H0| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (guard_true 24) by reflexivity.
    f_equal. rewrite EA. lia.
  - (* [comment removed for export] *)
    replace (Z.min res 5) with res by lia.
    rewrite (guard_true 22) by (apply Z.leb_le; rewrite EA; lia).
    assert (Kr0 : known st (fst c, snd c + get_stride (R m) - IB - res) 0).
    { destruct (Z.eq_dec res 0) as [E0|NE]; [| apply Kr; lia]. rewrite E0, Z.sub_0_r, CF, <- Hst. exact H0. }
    rewrite (rd8_known st (aadd ea (- res)) 0) by (eapply known_at; [exact Kr0| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (guard_true 23) by reflexivity.
    rewrite (rd8_known st ea 0) by (eapply known_at; [exact H0| clear OFF; subst e stride res p; cbn [fst snd aadd]; unfold UNIT, IB in *; lia| cbn [fst aadd]; rewrite ?CF; first [reflexivity| exact PF| symmetry; exact PF]]).
    rewrite (guard_true 24) by reflexivity.
    f_equal. rewrite EA. lia.
Qed.

Lemma free_hdr_eq : free_hdr st p = SRet (Some (wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st), m, i)).
Proof.
  unfold free_hdr. rewrite get_meta_eq. cbv beta zeta.
  unfold slot_start. rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF). cbv beta zeta iota.
  match goal with |- get_nominal_size st p ?e ?k ?b = _ => change (get_nominal_size st p e k b) with (get_nominal_size st p ea k b) end.
  rewrite get_nominal_size_eq. reflexivity.
Qed.
End HDR.
