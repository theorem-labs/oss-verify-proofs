(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (20 recorded proofs replaced by written proofs (ticks_ok_upd_meta, ticks_ok_upd_ctx, ticks_ok_wr16 and 17 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MallocKit_A () := "C47Corelib7Program6Basics4flipC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C47Corelib4Init9Datatypes3fstC35stdpp4base;RelDecisionC35stdpp4base4fmapC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8ticks_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3wr8C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z6shiftrC59OSSVerify5KrLib6Malloc9MallocRep<ticks_ok_wr8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4wr16C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib4Spec6Malloc4wr32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3lebI47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z3oppK47Corelib4Init9Datatypes4prod01C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4Spec6Malloc8set_sizeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndI47Corelib7Numbers7BinNums1N00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~I35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;havoc_unitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;havoc_pagesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6shadow01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:upd_shadowC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib4Spec6Malloc5havocC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C35stdpp6option;from_optionC59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc;MallocKit_A=conc_set_sizeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc:enframe_atC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC59OSSVerify5KrLib3Lib3Mem<Z_to_bv8_modC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismK46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z=shiftr_shiftrC45stdpp9bitvector;definitions;bv_unsignedK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2b8C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib6Malloc=F_malloc_fast;lowbit_pow2C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec6Malloc6lowbitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;lt_ge_casesI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions:bv_modulus".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Lemma ticks_ok_upd_meta st g f : ticks_ok st -> ticks_ok (upd_meta g f st).
Proof. intros T; exact T. Qed.
Lemma ticks_ok_upd_ctx st f : ticks_ok st -> ticks_ok (upd_ctx f st).
Proof. intros T; exact T. Qed.
Lemma ticks_ok_wr16 st p v : ticks_ok st -> ticks_ok (wr16 p v st).
Proof. intros T. unfold wr16. apply ticks_ok_wr8, ticks_ok_wr8, T. Qed.
Lemma ticks_ok_wr32 st p v : ticks_ok st -> ticks_ok (wr32 p v st).
Proof. intros T. unfold wr32. repeat apply ticks_ok_wr8. exact T. Qed.
Lemma ticks_ok_set_size p e n b st : ticks_ok st -> ticks_ok (set_size p e n b st).
Proof.
  intros T. unfold set_size.
  destruct (5 <=? _); destruct (negb _); repeat first [apply ticks_ok_wr8 | apply ticks_ok_wr32]; exact T.
Qed.

Lemma get_shadow_set_tick st t rid : get_shadow (set_tick t st) rid = get_shadow st rid.
Proof. reflexivity. Qed.
Lemma get_shadow_upd_meta st g f rid : get_shadow (upd_meta g f st) rid = get_shadow st rid.
Proof. reflexivity. Qed.
Lemma s_regions_wr8 st p v : s_regions (wr8 p v st) = s_regions st.
Proof. reflexivity. Qed.
Lemma s_groups_wr8 st p v : s_groups (wr8 p v st) = s_groups st.
Proof. reflexivity. Qed.
Lemma conc_wr8 st p v q : conc (wr8 p v st) q = conc st q.
Proof. reflexivity. Qed.
Lemma conc_wr16 st p v q : conc (wr16 p v st) q = conc st q.
Proof. reflexivity. Qed.
Lemma conc_set_tick st t q : conc (set_tick t st) q = conc st q.
Proof. reflexivity. Qed.
Lemma conc_upd_meta st g f q : conc (upd_meta g f st) q = conc st q.
Proof. reflexivity. Qed.
Lemma conc_havoc st p n q : conc (havoc p n st) q = conc st q.
Proof. unfold havoc. destruct (n <=? 0); reflexivity. Qed.
Lemma conc_set_size p e n b st q : conc (set_size p e n b st) q = conc st q.
Proof. unfold set_size. destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma conc_enframe_at st g k n off q : conc (fst (enframe_at st g k n off)) q = conc st q.
Proof. unfold enframe_at. destruct (negb (off =? 0)); cbn [fst]; rewrite conc_set_size; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma le4_bytes : forall v, 0 <= v < 2^32 ->
  le4 (wz v) = [b8 (v mod 256); b8 ((v / 256) mod 256); b8 ((v / 65536) mod 256); b8 (v / 16777216)].
Proof.
  intros v Hv. unfold le4, wz, b8. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  rewrite !Z.shiftr_shiftr by lia.
  rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256. change (2^(8+8)) with 65536. change (2^(8+8+8)) with 16777216.
  assert (E : forall x, Z_to_bv 8 x = Z_to_bv 8 (x mod 256)).
  { intros x. apply Z_to_bv8_mod. change (2^8) with 256. rewrite Z.mod_mod by lia. reflexivity. }
  rewrite (E v) at 1. rewrite (E (v / 256)) at 1. rewrite (E (v / 65536)) at 1. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lowbit_facts : forall v, 0 < v < 2^32 -> exists k, 0 <= k < 32 /\ lowbit v = 2 ^ k.
Proof.
  intros v Hv. destruct (lowbit_pow2 v ltac:(lia)) as (k & Hk & E & Hle). exists k.
  split; [|unfold lowbit; exact E]. split; [exact Hk|].
  destruct (Z.lt_ge_cases k 32) as [?|GE]; [assumption|].
  assert (2 ^ 32 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma b8_of_byte : forall x : byte, b8 (bv_unsigned x) = x.
Proof. intros x. unfold b8. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma byte_range : forall x : byte, 0 <= bv_unsigned x < 256.
Proof. intros x. pose proof (bv_unsigned_in_range 8 x) as H. unfold bv_modulus in H. cbn in H. lia. Qed.


End CANSEC1.
