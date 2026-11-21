(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (7 recorded proofs replaced by written proofs (malloc_fp_widen, slot_ok_N, outside_app' and 4 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A F_mm_syscalls.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp MallocKit_A2 AllocSlot_iface F_malloc_join Malloc_iface F_malloc_bigw F_malloc_big.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W1 ASlot_W9 ASlot_W10 ASlot_W12 ASlot_W13 ASlot_W14 ASlot_W18 ASlot_I ASlot_M0 ASlot_M2 ASlot_M3 ASlot_M4P ASlot_M4 ASlot_M5P.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASlot_M5D () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC35stdpp4base7is_SomeC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init9Datatypes6option00I35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib6Malloc9Malloc_fp9malloc_fpC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib6Malloc:MallocTree8alloc_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp<new_reg_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp>free_slot_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp<grp_hdr_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree:fresh_addrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib6Malloc9MallocRep5lr_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C59OSSVerify5KrLib6Malloc9Malloc_fp>malloc_fp_monoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib6Malloc9MallocRep3CTXC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01I59OSSVerify5KrLib6Malloc9Malloc_fp7slot_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init9Datatypes4prod00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr05K59OSSVerify5KrLib6Malloc9Malloc_fp7slot_ok01C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega3Op201I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffK47Corelib4Init5Logic3and01C47Corelib4Init5Logic7and_indC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib4Init5Logic9False_indC47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes3appC59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC47Corelib7Classes?RelationClasses=iff_ReflexiveI47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z7add_0_rC46Stdlib6ZArith:ZArith_dec8Z_le_decK47Corelib4Init5Logic2ex01C56Stdlib6ZArith6BinInt1Z2gtC46Stdlib6ZArith4Zdiv:Z_div_multC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing3Pol03C46Stdlib6ZArith4Zdiv:Z_mod_multK46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega3Op206I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9META_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8AREA_HDRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep@size_class_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5D4nreqC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz03C59OSSVerify5KrLib6Malloc9ASlot_W128stc_q_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=size_to_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc>F_malloc_entry5stc_qC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_M5D4nclsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_M0@nest_class_propsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decK46Stdlib9micromega7EnvRing3Pol02C59OSSVerify5KrLib6Malloc8ASlot_M0?size_class_monoC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma malloc_fp_widen st0 stA stB lo sp sp' a :
  sp' <= sp ->
  (forall rid r, (s_regions stA) !! rid = Some r ->
     exists r', (s_regions stB) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
  malloc_fp st0 stA lo sp' a -> malloc_fp st0 stB lo sp a.
Proof.
  intros LE HR H. apply (malloc_fp_mono st0 stA stB lo sp a HR).
  destruct H as [[X|X]|X]; [left; left; lia| left; right; exact X| right; exact X].
Qed.

(* [comment removed for export] *)
Lemma slot_ok_N st g b r idx n N :
  slot_ok st g b r idx n -> get_stride (get_meta_rec st g) = N + 4 -> 0 <= N -> slot_ok st g b r idx N.
Proof.
  intros SO STR N0. destruct SO. constructor; try assumption; try lia.
  intros off O0 OF. apply so_q16; lia.
Qed.

Lemma outside_app' W1 W2 a : outside (W1 ++ W2) a <-> outside W1 a /\ outside W2 a.
Proof. induction W1 as [|[lo hi] W1 IH]; cbn; [tauto|]. rewrite IH. tauto. Qed.

Lemma arith_prog_dec a c s n : 0 < s ->
  (exists j, 0 <= j <= n /\ a = c + s * j) \/ (forall j, 0 <= j <= n -> a <> c + s * j).
Proof.
  intros Hs. destruct (Z.eq_dec ((a - c) mod s) 0) as [M0|M1].
  - pose proof (Z.div_mod (a - c) s ltac:(lia)) as DM. rewrite M0, Z.add_0_r in DM.
    destruct (Z_le_dec 0 ((a - c) / s)) as [L0|L0]; [destruct (Z_le_dec ((a - c) / s) n) as [L1|L1]|].
    + left. exists ((a - c) / s). split; [lia|]. lia.
    + right. intros j Hj E. assert ((a - c) / s = j) by (subst a; replace (c + s * j - c) with (j * s) by lia; rewrite Z_div_mult by lia; lia). lia.
    + right. intros j Hj E. assert ((a - c) / s = j) by (subst a; replace (c + s * j - c) with (j * s) by lia; rewrite Z_div_mult by lia; lia). lia.
  - right. intros j Hj E. apply M1. subst a. replace (c + s * j - c) with (j * s) by lia. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
Lemma errno_lit5 (tp : word) : tp = Z_to_bv 64 0x1a620 -> errno_addr tp = 107900.
Proof. intros ->. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma meta_slot_mono stA stB g :
  (forall a, is_Some ((s_areas stA) !! a) -> is_Some ((s_areas stB) !! a)) -> meta_slot stA g -> meta_slot stB g.
Proof.
  intros HA (ar & arr & kk & Ha & Hk & E). destruct (HA ar ltac:(rewrite Ha; eexists; reflexivity)) as [arr' Ha'].
  exists ar, arr', kk. auto.
Qed.

(* [comment removed for export] *)
Definition nreq (sc cnt1 : Z) : Z := UNIT + cnt1 * (UNIT * size_class sc) - IB.
Definition ncls (sc cnt1 : Z) : Z := size_to_class (nreq sc cnt1).

Lemma nest_class sc (SC : 0 <= sc < 48) cnt1 : 1 <= cnt1 <= 32 -> size_class sc * UNIT * cnt1 + UNIT <= 2048 ->
  nreq sc cnt1 = size_class sc * 16 * cnt1 + 12 /\ 0 <= ncls sc cnt1 <= 26 /\ 16 * size_class sc * cnt1 + 16 <= UNIT * size_class (ncls sc cnt1)
  /\ sc < ncls sc cnt1 /\ 0 <= nreq sc cnt1 < 2^32 /\ nreq sc cnt1 + 4 <= 16 * size_class (ncls sc cnt1).
Proof.
  intros C1 SM. pose proof (size_class_range sc SC) as SZR.
  assert (E : nreq sc cnt1 = size_class sc * 16 * cnt1 + 12) by (unfold nreq, UNIT, IB; lia).
  assert (QR : 1 <= size_class sc * cnt1 <= 127) by (unfold UNIT in SM; nia).
  pose proof (stc_q_eq (size_class sc) cnt1 SZR C1 ltac:(unfold UNIT in SM; lia)) as EJ.
  assert (EJ' : ncls sc cnt1 = stc_q (size_class sc * cnt1)) by (unfold ncls; rewrite E; exact EJ).
  destruct (nest_class_props (size_class sc * cnt1) QR) as [J1 J2]. rewrite <- EJ' in J1, J2.
  split; [exact E|]. split; [exact J1|]. split; [unfold UNIT; nia|].
  split.
  { destruct (Z_lt_le_dec sc (ncls sc cnt1)) as [L|GE]; [exact L|]. exfalso.
    destruct (Z.eq_dec (ncls sc cnt1) sc) as [EQ|NE]; [rewrite EQ in J2; nia|].
    pose proof (size_class_mono (ncls sc cnt1) sc ltac:(lia) ltac:(lia)). nia. }
  split; [lia|]. nia.
Qed.

(* [comment removed for export] *)
Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : AREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis CLO : ATOP <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK (S f).
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.


End LEVEL.


End CANSEC1.
