(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (15 recorded proofs replaced by written proofs (conc_b, sk_nonneg, actives_length and 12 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Malloc_fp () := "C35stdpp4base6LookupC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rI35stdpp4gmap4gmap00C46Stdlib5Lists4List8map_consC59OSSVerify5KrLib6Malloc9MallocRep<conc_region'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2eq00I47Corelib7Numbers7BinNums1Z00I47Corelib7Numbers7BinNums1N00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3mulK47Corelib4Init5Logic2eq01C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z3divI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C47Corelib5Lists7ListDef3seqC47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List:length_seqK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2pwC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib6Malloc9MallocRep7activesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z6to_natC46Stdlib5Lists4List9nth_errorC47Corelib4Init9Datatypes:option_mapK47Corelib4Init9Datatypes6option01C56Stdlib5Arith8PeanoNat3Nat3ltbC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC56Stdlib5Arith8PeanoNat3Nat6ltb_ltC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith4Znat5Z2Nat2idC46Stdlib5Lists4List=nth_error_seqC46Stdlib5Lists4List=nth_error_mapC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib4Spec6Malloc6lowbitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z>pow2_bits_trueC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z4landC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z9land_specC47Corelib4Init9Datatypes9andb_propC47Corelib4Init5Logic7and_indC59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3ltbC59OSSVerify5KrLib4Spec6Malloc5clz32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_ltC59OSSVerify5KrLib4Spec6Malloc=size_to_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9Malloc_fp;grp_hdr_covC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9Malloc_fp9unk_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree3memC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C47Corelib7Classes?RelationClassesBPreOrder_ReflexiveC59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses;reflexivityI47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib6Malloc9Malloc_fp4mrel01C1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2leC56Stdlib6NArith6BinNat1N;le_preorderi59OSSVerify5KrLib6Malloc9Malloc_fp4mrel00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegI47Corelib4Init5Logic2ex00C56Stdlib6ZArith4Znat3N2Z6inj_leC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr06K46Stdlib9micromega7EnvRing5PExpr05c59OSSVerify5KrLib6Malloc9Malloc_fp>round_up_pg_eqC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00c59OSSVerify5KrLib6Malloc9Malloc_fp9malloc_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree8alloc_fpC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9Malloc_fp<new_reg_addrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9Malloc_fp>free_slot_addrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib6Malloc9MallocRep5lr_loC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib4Init5Logic9False_indc59OSSVerify5KrLib6Malloc9Malloc_fp@round_up_pg_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9Malloc_fp<grp_hdr_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree:fresh_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep3CTXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc@F_malloc_enframeEget_meta_rec_upd_sameC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A9mf_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A;fact_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib6Malloc9Malloc_fp7slot_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A8mf_gmetaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A:fact_gmetaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A9sstart_ofC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9Malloc_fp>lowbit_testbitC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib6Malloc=F_malloc_fast;lowbit_pow2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A=mf_free_clearC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib6Malloc<MallocBlocks8blk_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks8blk_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks8blk_sizeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idK47Corelib4Init9Datatypes4prod01C35stdpp6option;from_optionC59OSSVerify5KrLib6Malloc=MallocFacts_A7mf_hdr0C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_lC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_AAmf_slots_completeC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib6Malloc9Malloc_fp7slot_ok01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=add_le_mono_rC47Corelib4Init9Datatypes3fstI59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep>agent_reservedC1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableC59OSSVerify5KrLib6Malloc<MallocBlocks5blockC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01c59OSSVerify5KrLib6Malloc9Malloc_fp@get_meta_rec_st2C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Section ENFRAME.
Variables (st2 : mstate) (m4 : mem) (g b : aptr) (r : region) (k n off : Z).
Let mr := get_meta_rec st2 g.
Let stride := get_stride mr.
Let B := conc st2 b.
Let P0 := B + 16 + stride * k.
Hypothesis TK : ticks_ok st2.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st2) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis K0 : 0 <= k < 32.
Hypothesis SPAN : snd b + 16 + stride * (k + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis S31 : stride - 4 - n < 2^31.
Hypothesis NOGRP : forall b' gh, (s_groups st2) !! b' = Some gh -> fst b' = fst b ->
  snd b' + 9 <= snd b + 16 + stride * k - 4 \/ snd b + 16 + stride * k + stride - 4 <= snd b'.
Hypothesis OFF0 : 0 <= off.
Hypothesis N0 : 0 <= n.
Hypothesis FIT : 16 * off + n + 4 <= stride.
Hypothesis Q16 : (stride * k + 16 * off) / 16 < 65536.

Lemma conc_b : B = r_base r + snd b.
Proof. unfold B. apply (conc_region' st2 b r Hr). Qed.

Lemma sk_nonneg : 0 <= stride * k.
Proof. apply Z.mul_nonneg_nonneg; lia. Qed.
End ENFRAME.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma actives_length : forall st, length (actives st) = 48%nat.
Proof. intros. unfold actives. rewrite length_map, length_seq. reflexivity. Qed.

Lemma actives_nth : forall st sc, 0 <= sc < 48 -> nth_error (actives st) (Z.to_nat sc) = Some (pw st (active st sc)).
Proof.
  intros st sc Hsc. unfold actives. rewrite nth_error_map, nth_error_seq.
  replace (Z.to_nat sc <? 48)%nat with true by (symmetry; apply Nat.ltb_lt; lia). cbn. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma lowbit_testbit : forall v k, 0 <= k -> lowbit v = 2 ^ k -> Z.testbit v k = true.
Proof.
  intros v k Hk E. unfold lowbit in E.
  assert (T : Z.testbit (Z.land v (- v)) k = true) by (rewrite E; apply Z.pow2_bits_true; lia).
  rewrite Z.land_spec in T. apply andb_prop in T. tauto.
Qed.

Lemma size_class_small : forall sc, 0 <= sc < 10 -> size_class sc = sc + 1.
Proof.
  intros sc H.
  assert (E : sc = 0 \/ sc = 1 \/ sc = 2 \/ sc = 3 \/ sc = 4 \/ sc = 5 \/ sc = 6 \/ sc = 7 \/ sc = 8 \/ sc = 9) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity.
Qed.

Lemma size_to_class_small : forall n, 0 <= n -> Z.shiftr (n + 3) 4 < 10 -> size_to_class n = Z.shiftr (n + 3) 4.
Proof.
  intros n Hn Hs. unfold size_to_class, IB. replace (n + 4 - 1) with (n + 3) by lia.
  replace (Z.shiftr (n + 3) 4 <? 10) with true by (symmetry; apply Z.ltb_lt; exact Hs). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition grp_hdr_cov (st : mstate) (rid : N) (off : Z) : Prop :=
  exists b gh, (s_groups st) !! b = Some gh /\ fst b = rid /\ snd b <= off < snd b + 12.

(* [comment removed for export] *)
Definition unk_agree (st : mstate) (o m1 : mem) : Prop :=
  forall rid r off h, (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
    0 <= off < round_up_pg (r_len r) ->
    cell_read (get_shadow st rid) off = Unknown h ->
    ~ grp_hdr_cov st rid off ->
    m1 (wa (r_base r + off)) = o (wa (r_base r + off)).

Lemma unk_agree_refl : forall st m, unk_agree st m m.
Proof. intros st m rid r off h _ _ _ _ _. reflexivity. Qed.

(* [comment removed for export] *)
Section SLOT.
Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx n : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P0 := B + 16 + stride * idx.
Hypothesis UA : unk_agree st o m1.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis IDX : 0 <= idx.
Hypothesis SPAN : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis B16 : snd b mod 16 = 0.
Hypothesis SMOD : stride mod 16 = 0.
Hypothesis NOGRP : forall b' gh, (s_groups st) !! b' = Some gh -> fst b' = fst b ->
  snd b' + 9 <= snd b + 16 + stride * idx - 4 \/ snd b + 16 + stride * idx + stride - 4 <= snd b'.
Hypothesis HDR0 : cell_read (get_shadow st (fst b)) (snd b + 16 + stride * idx - 4) = Known 0.
End SLOT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition expo_cond (st : mstate) (n : Z) : Prop := MMAP_THRESHOLD <= n \/ s_regions st = ∅.

Record slot_ok (st1 : mstate) (g b : aptr) (r : region) (idx n : Z) : Prop := mkSO {
  so_mem : m_mem (get_meta_rec st1 g) = Some b;
  so_reg : (s_regions st1) !! (fst b) = Some r;
  so_kind : r_kind r = RKGroup;
  so_b0 : 0 <= snd b;
  so_b16 : snd b mod 16 = 0;
  so_idx : 0 <= idx <= m_last_idx (get_meta_rec st1 g);
  so_li : m_last_idx (get_meta_rec st1 g) < 32;
  so_span : snd b + 16 + get_stride (get_meta_rec st1 g) * (m_last_idx (get_meta_rec st1 g) + 1) <= round_up_pg (r_len r);
  so_s16 : 16 <= get_stride (get_meta_rec st1 g);
  so_smod : get_stride (get_meta_rec st1 g) mod 16 = 0;
  so_s31 : get_stride (get_meta_rec st1 g) - 4 - n < 2^31;
  so_n : 0 <= n;
  so_fit : n + 4 <= get_stride (get_meta_rec st1 g);
  (* [comment removed for export] *)
  so_nogrp : forall b' gh, (s_groups st1) !! b' = Some gh -> fst b' = fst b ->
     snd b' + 9 <= snd b + 16 + get_stride (get_meta_rec st1 g) * idx - 4
     \/ snd b + 16 + get_stride (get_meta_rec st1 g) * idx + get_stride (get_meta_rec st1 g) - 4 <= snd b';
  (* [comment removed for export] *)
  so_hdr0 : cell_read (get_shadow st1 (fst b)) (snd b + 16 + get_stride (get_meta_rec st1 g) * idx - 4) = Known 0;
  (* [comment removed for export] *)
  so_q16 : forall off, 0 <= off -> 16 * off + n + 4 <= get_stride (get_meta_rec st1 g) ->
     (get_stride (get_meta_rec st1 g) * idx + 16 * off) / 16 < 65536;
  (* [comment removed for export] *)
  so_slot : (s_slots st1) !! (fst b, snd b + 16 + get_stride (get_meta_rec st1 g) * idx) = Some (g, idx);
  so_mslot : meta_slot st1 g;
  so_avail : 0 <= m_avail (get_meta_rec st1 g) < 2^32;
  so_freed : 0 <= m_freed (get_meta_rec st1 g) < 2^32;
  so_freeable : 0 <= m_freeable (get_meta_rec st1 g) < 2;
  so_maplen : 0 <= m_maplen (get_meta_rec st1 g) < 2^40;
  so_sc : 0 <= m_sizeclass (get_meta_rec st1 g) < 48
          \/ (m_sizeclass (get_meta_rec st1 g) = 63 /\ m_last_idx (get_meta_rec st1 g) = 0 /\ 0 < m_maplen (get_meta_rec st1 g))
}.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition free_slot_addr (st : mstate) (a : Z) : Prop :=
  exists g b r i, m_mem (get_meta_rec st g) = Some b /\ (s_regions st) !! (fst b) = Some r /\ r_kind r = RKGroup /\ 0 <= i /\
    (Z.testbit (m_avail (get_meta_rec st g)) i = true \/ Z.testbit (m_freed (get_meta_rec st g)) i = true) /\
    r_base r <= a < r_base r + round_up_pg (r_len r) /\
    r_base r + sstart_of (get_meta_rec st g) i - IB <= a
      < r_base r + sstart_of (get_meta_rec st g) i + get_stride (get_meta_rec st g) - IB.

(* [comment removed for export] *)
Definition grp_hdr_addr (st : mstate) (a : Z) : Prop :=
  exists b gh r, (s_groups st) !! b = Some gh /\ (s_regions st) !! (fst b) = Some r /\ r_kind r = RKGroup /\
    r_base r <= a < r_base r + round_up_pg (r_len r) /\
    r_base r + snd b <= a < r_base r + snd b + 16.

(* [comment removed for export] *)
Definition new_reg_addr (st st' : mstate) (a : Z) : Prop :=
  exists rid r, (s_regions st') !! rid = Some r /\ (s_regions st) !! rid = None /\
    lr_lo r <= a < r_base r + round_up_pg (r_len r).

(* [comment removed for export] *)
Definition malloc_fp (st st' : mstate) (lo sp : Z) (a : Z) : Prop :=
  alloc_fp (fun k => k <> RKGroup) st' lo sp a \/ new_reg_addr st st' a \/ free_slot_addr st a \/ grp_hdr_addr st a
  \/ fresh_addr st a.

Record mrel (st st' : mstate) : Prop := mkMREL {
  mrel_regions : forall rid r, (s_regions st) !! rid = Some r ->
     exists r', (s_regions st') !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r';
  mrel_next : (s_next_rid st <= s_next_rid st')%N;
  mrel_reserved : s_reserved st' = s_reserved st
}.

Lemma mrel_refl st : mrel st st.
Proof. split; [|reflexivity|reflexivity]. intros rid r H. exists r. repeat split; auto. lia. Qed.

Lemma mrel_trans st1 st2 st3 : mrel st1 st2 -> mrel st2 st3 -> mrel st1 st3.
Proof.
  intros [R1 N1 S1] [R2 N2 S2]. split; [| lia | congruence].
  intros rid r H. destruct (R1 rid r H) as (r' & H' & K' & B' & L'). destruct (R2 rid r' H') as (r'' & H'' & K'' & B'' & L'').
  exists r''. repeat split; auto; try congruence. lia.
Qed.

Lemma round_up_pg_eq x : round_up_pg x = x + (- x) mod 4096.
Proof. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma round_up_pg_mono x y : x <= y -> round_up_pg x <= round_up_pg y.
Proof. intros H. rewrite !round_up_pg_eq. Z.div_mod_to_equations. lia. Qed.

Lemma malloc_fp_mono st sta stb lo sp a :
  (forall rid r, (s_regions sta) !! rid = Some r ->
     exists r', (s_regions stb) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
  malloc_fp st sta lo sp a -> malloc_fp st stb lo sp a.
Proof.
  intros HR [H|[H|H]]; [| right; left | right; right; exact H].
  - destruct H as [H|[H|[H|(rid & r & Hr & Hk & Ha)]]]; [left; left; exact H| left; right; left; exact H| left; right; right; left; exact H|].
    destruct (HR rid r Hr) as (r' & Hr' & K' & B' & L').
    left. right. right. right. exists rid, r'. split; [exact Hr'|]. split; [congruence|].
    assert (LRE : lr_lo r' = lr_lo r) by (unfold lr_lo; rewrite K', B'; reflexivity).
    pose proof (round_up_pg_mono (r_len r) (r_len r') L'). lia.
  - destruct H as (rid & r & Hr & Hn & Ha). destruct (HR rid r Hr) as (r' & Hr' & K' & B' & L').
    exists rid, r'. split; [exact Hr'|]. split; [exact Hn|].
    assert (LRE : lr_lo r' = lr_lo r) by (unfold lr_lo; rewrite K', B'; reflexivity).
    pose proof (round_up_pg_mono (r_len r) (r_len r') L'). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FASTFACTS.
Variables (st : mstate) (LB : list block) (sc n : Z) (g : aptr) (k : Z) (t : N).
Let st1 := set_tick t st.
Let mr := get_meta_rec st g.
Let st2 := upd_meta g (m_set_avail (m_avail mr - 2 ^ k)) st1.
Hypothesis MF : MFACTS st LB.
Hypothesis ACT : active st sc = Some g.
Hypothesis AV : 0 < m_avail mr.
Hypothesis K0 : 0 <= k.
Hypothesis LBK : lowbit (m_avail mr) = 2 ^ k.
Hypothesis N0 : 0 <= n.
Hypothesis NFIT : n + 4 <= 16 * size_class sc.

Lemma get_meta_rec_st2 : get_meta_rec st2 g = m_set_avail (m_avail mr - 2 ^ k) mr.
Proof. unfold st2. rewrite get_meta_rec_upd_same. reflexivity. Qed.

Lemma fast_slot_ok : exists b r,
  slot_ok st2 g b r k n
  /\ (forall a, r_base r + snd b + 16 + get_stride mr * k - 4 <= a < r_base r + snd b + 16 + get_stride mr * k + get_stride mr - 4 ->
        free_slot_addr st a)
  /\ k < 32 /\ m_mem mr = Some b /\ (s_regions st) !! (fst b) = Some r.
Proof.
  pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
  destruct (FA sc g ACT) as (SC48 & GSC & MEMnn). change (get_meta_rec st g) with mr in GSC, MEMnn.
  destruct (m_mem mr) as [b|] eqn:Hmem; [|congruence]. clear MEMnn.
  pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
  specialize (FG g b Hmem). change (get_meta_rec st g) with mr in FG. cbv zeta in FG.
  destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh & AI & AVAI) & (r & Hr & Hk & B0 & B16 & SPAN) & S16 & SMOD & S31 & UND & S20).
  unfold UNIT, IB in *.
  assert (TBk : Z.testbit (m_avail mr) k = true) by (apply lowbit_testbit; assumption).
  pose proof (AVAI k K0 TBk) as KAI.
  assert (K32 : k < 32) by lia.
  assert (P2k : 0 < 2 ^ k <= m_avail mr).
  { split; [apply Z.pow_pos_nonneg; lia|]. destruct (lowbit_pow2 (m_avail mr) AV) as (k' & _ & E' & LE'). unfold lowbit in LBK.
    rewrite LBK in E'. rewrite E'. exact LE'. }
  assert (GSC48 : m_sizeclass mr < 48) by lia. specialize (S31 GSC48).
  destruct SCr as [[GS0 MPL]|[E63 _]]; [|lia].
  pose proof (mf_free_clear _ _ MF g b k Hmem K0 (or_introl TBk)) as FC. cbv zeta in FC. destruct FC as [NOGRP _].
  change (get_meta_rec (strip st) g) with mr in NOGRP. change (s_groups (strip st)) with (s_groups st) in NOGRP.
  unfold sstart_of in NOGRP. rewrite Hmem in NOGRP. cbn [default from_option id snd] in NOGRP. unfold UNIT, IB in NOGRP.
  pose proof (mf_hdr0 _ _ MF g b k Hmem ltac:(change (get_meta_rec st g) with mr; lia)) as K4.
  unfold sstart_of in K4. rewrite Hmem in K4. cbn [default from_option id fst snd] in K4.
  change (get_meta_rec st g) with mr in K4. unfold IB, UNIT in K4.
  unfold sstart_of in SPAN. rewrite Hmem in SPAN. cbn [default from_option id snd] in SPAN. unfold UNIT, IB in SPAN.
  exists b, r. pose proof get_meta_rec_st2 as E2.
  split; [|split; [|split; [exact K32| split; [reflexivity| exact Hr]]]].
  - pose proof (UND GSC48 k K0 TBk) as U. rewrite GSC in U. specialize (S20 GSC48).
    constructor; rewrite ?E2; cbn [m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen m_set_avail];
      try change (get_stride (m_set_avail (m_avail mr - 2 ^ k) mr)) with (get_stride mr);
      first [ exact Hmem | exact Hr | exact Hk | exact MSL | exact K4 | exact NOGRP | exact N0 | exact SMOD
            | (pose proof (mf_slots_complete _ _ MF g b k Hmem ltac:(change (get_meta_rec (strip st) g) with mr; lia)) as SC;
               change (get_meta_rec (strip st) g) with mr in SC; unfold sstart_of in SC; rewrite Hmem in SC;
               cbn [default from_option id snd] in SC; unfold UNIT in SC; exact SC)
            | (intros off O0 OF;
               assert (get_stride mr * k + 16 * off < get_stride mr * (k + 1)) by lia;
               assert (get_stride mr * (k + 1) <= get_stride mr * (m_last_idx mr + 1)) by (apply Z.mul_le_mono_nonneg_l; lia);
               apply Z.div_lt_upper_bound; lia)
            | lia ].
  - intros a Ha. exists g, b, r, k. split; [exact Hmem|]. split; [exact Hr|]. split; [exact Hk|]. split; [exact K0|]. split; [left; exact TBk|].
    unfold sstart_of. rewrite Hmem. cbn [default from_option id snd]. unfold UNIT, IB. fold mr.
    assert (get_stride mr * k + get_stride mr <= get_stride mr * m_last_idx mr + get_stride mr) by (apply Z.add_le_mono_r; apply Z.mul_le_mono_nonneg_l; lia).
    assert (0 <= get_stride mr * k) by (apply Z.mul_nonneg_nonneg; lia).
    lia.
Qed.
End FASTFACTS.


End CANSEC1.
