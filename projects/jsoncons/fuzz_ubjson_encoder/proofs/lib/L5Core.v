(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs replaced by tactic proofs. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_L5Core () := "C46Stdlib5Lists4List6nth_okC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List:firstn_nilC46Stdlib5Lists4List=repeat_lengthI45stdpp9bitvector;definitions2bv00I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions:bv_modulusC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions?bv_add_unsignedI47Corelib7Numbers7BinNums1Z00I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L55rangeC13~~~C47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufI47Corelib4Init9Datatypes6option00c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Core3L5C3stkC13~~~C56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L57definedC13~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega6VarMap1t01K47Corelib4Init5Logic3and01I47Corelib4Init9Datatypes4prod00c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Core3L5C5hpresC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Core3L5C4keptC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface;client_addrC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface8in_errnoC13~~~C47Corelib4Init5Logic3notI79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface;heap_layout00C13~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L5;defined_subC13~~~K46Stdlib9micromega=RingMicromega3Op201C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7StoreOk9mem_growsC13~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L5=defined_growsC13~~~C56Stdlib6ZArith6BinInt1Z6of_natC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L5<unsigned_litC13~~~C46Stdlib9micromega;ZifyClasses9and_morphC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeK47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atC47Corelib4Init5Logic9False_indC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7StoreOk?store_ok_of_allC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L58writableC13~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succK46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega8ZifyInst7Inj_Z_ZI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib4Init5Logic5False00c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Core3L5CCwritable_of_definedC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Core3L5C8agree_onC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec3rdnC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Core3L5C8add1_litC13~~~C47Corelib4Init9Datatypes7nat_indC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L56u64_atC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Core3L5C9rdn_agreeC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L55u8_atC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L58bytes_atC13~~~C47Corelib4Init5Peano2ltC47Corelib5Lists7ListDef3nthc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Core3L5C;u8_at_agreeC13~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith6BinInt1Z3mulC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L58limbs_atC13~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega:ZMicromega;ZArithProof03c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Core3L5C<u64_at_agreeC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Core3L5C;wview_agreeC13~~~K47Corelib4Init9Datatypes4bool02c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Core3L5C>store_ok_agreeC13~~~C47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z4succC46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Core3L5C:store_ok_SC13~~~C47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L56big_atC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L55bo_fbC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L56bo_lenC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L55bo_stC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L5:hull_apartC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Core3L5C<agree_on_subC13~~~I47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses6eq_iffC56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith4Znat5Nat2Z6inj_leI89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L56bigobj00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L56bstore00C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L5:lstr_shortC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Core3L5C>bytes_at_agreeC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface8hl_sptopC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface8hl_errnoC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L57outsideC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface8in_blockC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface9hl_img_loC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface9hl_img_hiC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface?hl_alloc_staticC13~~~I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K46Stdlib9micromega5Tauto8GFormula07c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Core3L5C:kept_stackC13~~~K47Corelib4Init9Datatypes4prod01C46Stdlib5Lists4List2InC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK47Corelib4Init5Logic2ex01K46Stdlib9micromega5Tauto8GFormula06C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface<blocks_apartC13~~~I47Corelib4Init5Logic2ex00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L56in_rngC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L59frame_butC13~~~C47Corelib4Init9Datatypes3appC47Corelib4Init3Nat3addC46Stdlib5Lists4List:length_appC56Stdlib5Arith8PeanoNat3Nat;lt_ge_casesC46Stdlib5Lists4List8app_nth1C47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z8max_specC47Corelib4Init5Peano2geC56Stdlib6ZArith6BinInt1Z2geC46Stdlib5Lists4List8app_nth2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z6inj_geK46Stdlib9micromega=RingMicromega3Op204C46Stdlib5Lists4List:nth_repeatC47Corelib5Lists7ListDef6repeatC47Corelib5Lists7ListDef6firstnC47Corelib4Init3Nat3minC46Stdlib5Lists4List=length_firstnC56Stdlib5Arith8PeanoNat3Nat3ltbC56Stdlib5Arith8PeanoNat3Nat8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specC46Stdlib5Lists4List:nth_firstnC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minC35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List=firstn_firstnC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Core3L5C;fresh_blockC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface;block_rangeC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L57hull_loC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L57hull_hiC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface<model_but_vmC13~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5Model01K4ELinuxProcessSemantics?LinuxProcessSem5State7VmState01C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State7VmState00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedI79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface=heap_iface_ok00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface7hi_heapC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface;hl_alloc_roC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface=alloc_privateC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface7definedC13~~~C47Corelib5Lists7ListDef3mapI35stdpp4base5NoDup00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface6hio_wfC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface9hio_frameC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface9lb_removeC13~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run;SpuriousCfg00I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface:heap_iface00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface6creditC13~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib4Init5Logic7f_equalC47Corelib4Init9Datatypes8list_indC56Stdlib6ZArith6BinInt1Z7add_0_rC56Stdlib6ZArith6BinInt1Z9mod_smallC47Corelib4Init5Logic6eq_symC46Stdlib5Lists4List:length_map". Local Ltac lia := L5FastLia.plia.

Module L5C.

Section WithSegs.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)

Lemma add1_lit (z : Z) : (Z_to_bv 64 z + 1)%bv = Z_to_bv 64 (z + 1).
Proof.
  apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_unsigned (1%bv : bv 64)) with 1. apply Zplus_mod_idemp_l.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition stk (sptop : Z) (M : word -> option byte) (sp scr : Z) : Prop :=
  sp mod 16 = 0 /\ sptop - 2 ^ 23 + scr <= sp /\ sp <= sptop /\ (0x7fff80000000 <= sptop <= 2 ^ 47) /\ L5.defined M (sp - scr) scr.
(* [comment removed for export] *)
Lemma stk_floor sptop M sp scr : stk sptop M sp scr -> 0x7fff7f800000 + scr <= sp.
Proof. intros (_ & B & _ & D & _). lia. Qed.
Lemma stk_window sptop M sp scr : stk sptop M sp scr -> sptop - 2 ^ 23 + scr <= sp /\ sp <= sptop /\ 0x7fff80000000 <= sptop <= 2 ^ 47.
Proof. intros (_ & B & C & D & _). repeat split; lia. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kept (L : heap_layout) (LB : list (Z * Z)) (sp scr : Z) (W : list L5.range) (a : Z) : Prop :=
  0 <= a < 2 ^ 64 /\ client_addr L LB sp scr a /\ ~ in_errno L a /\ L5.outside W a.

Definition hpres (L : heap_layout) (LB : list (Z * Z)) (sp scr : Z) (W : list L5.range) (M M' : word -> option byte) : Prop :=
  (forall a, kept L LB sp scr W a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
  /\ L5.defined M' (sp - scr) scr
  (* [comment removed for export] *)
  /\ (forall a, 0 <= a < 2 ^ 64 -> client_addr L LB sp scr a -> ~ in_errno L a -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None).


(* [comment removed for export] *)
Lemma hpres_kept L LB sp scr W M M' a : hpres L LB sp scr W M M' -> kept L LB sp scr W a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof. intros [P _] K. apply P. exact K. Qed.
Lemma hpres_defined L LB sp scr W M M' : hpres L LB sp scr W M M' -> L5.defined M' (sp - scr) scr.
Proof. intros (_ & D & _). exact D. Qed.
Lemma hpres_cdef L LB sp scr W M M' a :
  hpres L LB sp scr W M M' -> 0 <= a < 2 ^ 64 -> client_addr L LB sp scr a -> ~ in_errno L a ->
  M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None.
Proof. intros (_ & _ & C). apply C. Qed.
Lemma hpres_intro L LB sp scr W M M' :
  (forall a, kept L LB sp scr W a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  L5.defined M' (sp - scr) scr ->
  (forall a, 0 <= a < 2 ^ 64 -> client_addr L LB sp scr a -> ~ in_errno L a -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None) ->
  hpres L LB sp scr W M M'.
Proof. intros P D C. exact (conj P (conj D C)). Qed.

Lemma stk_weaken sptop M sp scr scr' : stk sptop M sp scr -> 0 <= scr' <= scr -> stk sptop M sp scr'.
Proof.
  intros (A & B & C & D & W) Hs. repeat split; try lia.
  eapply L5.defined_sub. exact W. lia. lia.
Qed.

Lemma stk_grows sptop M M' sp scr : mem_grows M M' -> stk sptop M sp scr -> stk sptop M' sp scr.
Proof. intros G (A & B & C & D & W). repeat split; try lia. eapply L5.defined_grows; eauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma writable_of_defined M a n : L5.defined M a n -> 0 <= a -> a + n <= 2 ^ 64 -> L5.writable segs M a n.
Proof.
  intros D Ha Hn d k Hd Hk. destruct k as [|k]. reflexivity. apply store_ok_of_all.
  - rewrite L5.unsigned_lit by lia. lia.
  - intros x Hx. rewrite L5.unsigned_lit in Hx by lia. unfold wview.
    assert (E : x = Z_to_bv 64 (a + (bv_unsigned x - a))) by (apply bv_eq; rewrite L5.unsigned_lit; [lia| pose proof (bv_unsigned_in_range _ x); cbn in *; lia]).
    pose proof (D (bv_unsigned x - a) ltac:(lia)) as Dx. rewrite <- E in Dx.
    destruct (M x); [discriminate | exfalso; apply Dx; reflexivity].
Qed.

Lemma stk_writable sptop M sp scr : stk sptop M sp scr -> L5.writable segs M (sp - scr) scr.
Proof. intros (A & B & C & D & W). apply writable_of_defined. exact W. lia. lia. Qed.

(* [comment removed for export] *)
Definition agree_on (M M' : word -> option byte) (a n : Z) : Prop :=
  forall i, a <= i < a + n -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i).

Lemma rdn_agree (M M' : word -> option byte) : forall n a, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  agree_on M M' a (Z.of_nat n) -> rdn segs M' (Z_to_bv 64 a) n = rdn segs M (Z_to_bv 64 a) n.
Proof.
  induction n as [|n IH]; intros a Ha Hn Hag. reflexivity.
  cbn [rdn]. rewrite (Hag a) by lia.
  rewrite (add1_lit a).
  rewrite (IH (a + 1)); [reflexivity | lia | lia | intros i Hi; apply Hag; lia].
Qed.

Lemma u64_at_agree M M' a v : agree_on M M' a 8 -> 0 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at segs M a v -> L5.u64_at segs M' a v.
Proof. intros Hag Ha H8 Hu. unfold L5.u64_at. rewrite (rdn_agree M M' 8%nat a Ha ltac:(cbn; lia)). exact Hu. intros i Hi; apply Hag; cbn in Hi; lia. Qed.
Lemma u8_at_agree M M' a b : agree_on M M' a 1 -> 0 <= a -> a + 1 <= 2 ^ 64 -> L5.u8_at segs M a b -> L5.u8_at segs M' a b.
Proof. intros Hag Ha H1 Hu. unfold L5.u8_at. rewrite (rdn_agree M M' 1%nat a Ha ltac:(cbn; lia)). exact Hu. intros i Hi; apply Hag; cbn in Hi; lia. Qed.
Lemma bytes_at_agree M M' p bs : agree_on M M' p (Z.of_nat (length bs)) -> 0 <= p -> p + Z.of_nat (length bs) <= 2 ^ 64 ->
  L5.bytes_at segs M p bs -> L5.bytes_at segs M' p bs.
Proof. intros Hag Hp Hn HB i Hi. eapply u8_at_agree. intros j Hj; apply Hag; lia. lia. lia. apply HB. exact Hi. Qed.
Lemma limbs_at_agree M M' q ws : agree_on M M' q (8 * Z.of_nat (length ws)) -> 0 <= q -> q + 8 * Z.of_nat (length ws) <= 2 ^ 64 ->
  L5.limbs_at segs M q ws -> L5.limbs_at segs M' q ws.
Proof. intros Hag Hq Hn HL i Hi. eapply u64_at_agree. intros j Hj; apply Hag; lia. lia. lia. apply HL. exact Hi. Qed.
Lemma defined_agree M M' a n : agree_on M M' a n -> L5.defined M a n -> L5.defined M' a n.
Proof. intros Hag D i Hi. rewrite (Hag (a + i)) by lia. apply D. exact Hi. Qed.

Lemma wview_agree (M M' : word -> option byte) (x : word) : M' x = M x -> wview segs M' x = wview segs M x.
Proof. intros E. unfold wview. rewrite E. reflexivity. Qed.

Lemma store_ok_agree (M M' : word -> option byte) : forall (k : nat) a, 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  agree_on M M' a (Z.of_nat k) -> store_ok segs M' (Z_to_bv 64 a) k = store_ok segs M (Z_to_bv 64 a) k.
Proof.
  induction k as [|k IH]; intros a Ha Hk Hag. reflexivity.
  cbn [store_ok]. rewrite (wview_agree M M') by (apply Hag; lia).
  rewrite (add1_lit a).
  rewrite (IH (a + 1)); [reflexivity | lia | lia | intros i Hi; apply Hag; lia].
Qed.

Lemma writable_agree M M' a n : agree_on M M' a n -> 0 <= a -> a + n <= 2 ^ 64 -> L5.writable segs M a n -> L5.writable segs M' a n.
Proof.
  intros Hag Ha Hn W d k Hd Hk. rewrite (store_ok_agree M M' k (a + d)); [apply W; lia | lia | lia |].
  intros i Hi. apply Hag. lia.
Qed.

(* [comment removed for export] *)
Lemma store_ok_S M (a : word) k : store_ok segs M a (S k) = true <-> wview segs M a <> None /\ store_ok segs M (a + 1)%bv k = true.
Proof.
  cbn [store_ok]. destruct (wview segs M a) as [b|].
  - split. intros H; split; [discriminate | exact H]. intros [_ H]; exact H.
  - split. intros H; discriminate. intros [H _]; exfalso; apply H; reflexivity.
Qed.

Lemma writable_app M a n m : 0 <= a -> 0 <= n -> 0 <= m -> a + n + m <= 2 ^ 64 ->
  L5.writable segs M a n -> L5.writable segs M (a + n) m -> L5.writable segs M a (n + m).
Proof.
  intros Ha Hn Hm Htop W1 W2 d k. revert d. induction k as [|k IH]; intros d Hd Hk. reflexivity.
  rewrite Nat2Z.inj_succ in Hk.
  destruct (Z_lt_le_dec d n) as [Hlt|Hge].
  -
    apply (proj2 (store_ok_S M (Z_to_bv 64 (a + d)) k)). split.
    + pose proof (W1 d 1%nat Hd ltac:(cbn; lia)) as W. apply (proj1 (store_ok_S M _ 0%nat)) in W. exact (proj1 W).
    + rewrite (add1_lit (a + d)). replace (a + d + 1) with (a + (d + 1)) by lia.
      apply IH. lia. lia.
  - replace (a + d) with (a + n + (d - n)) by lia. apply W2. lia. lia.
Qed.

Lemma agree_on_sub M M' a n a' n' : agree_on M M' a n -> a <= a' -> a' + n' <= a + n -> agree_on M M' a' n'.
Proof. intros H H1 H2 i Hi. apply H. lia. Qed.

(* [comment removed for export] *)
Lemma big_at_agree M M' o b : agree_on M M' o 32 -> 0 <= o -> o + 32 <= 2 ^ 64 -> L5.big_at segs M o b -> L5.big_at segs M' o b.
Proof.
  intros Hag Ho H32 (B0 & Bfb & B8 & BS).
  split. { eapply u8_at_agree; [eapply agree_on_sub; [exact Hag|lia|lia] | lia | lia | exact B0]. }
  split. exact Bfb.
  split. { eapply u64_at_agree; [eapply agree_on_sub; [exact Hag|lia|lia] | lia | lia | exact B8]. }
  destruct (L5.bo_st b) as [v0 v1|cap q].
  - destruct BS as (T & B16 & B24 & R). split. exact T.
    split. { eapply u64_at_agree; [eapply agree_on_sub; [exact Hag|lia|lia] | lia | lia | exact B16]. }
    split. { eapply u64_at_agree; [eapply agree_on_sub; [exact Hag|lia|lia] | lia | lia | exact B24]. } exact R.
  - destruct BS as (T & B16 & B24 & R). split. exact T.
    split. { eapply u64_at_agree; [eapply agree_on_sub; [exact Hag|lia|lia] | lia | lia | exact B16]. }
    split. { eapply u64_at_agree; [eapply agree_on_sub; [exact Hag|lia|lia] | lia | lia | exact B24]. } exact R.
Qed.

Lemma lstr_short_agree M M' o s : agree_on M M' o 24 -> 0 <= o -> o + 24 <= 2 ^ 64 -> L5.lstr_short segs M o s -> L5.lstr_short segs M' o s.
Proof.
  intros Hag Ho H24 (L22 & B0 & BS & BN). split. exact L22.
  split. { eapply u8_at_agree; [eapply agree_on_sub; [exact Hag|lia|lia] | lia | lia | exact B0]. }
  split. { eapply bytes_at_agree; [eapply agree_on_sub; [exact Hag|lia|lia] | lia | lia | exact BS]. }
  eapply u8_at_agree; [eapply agree_on_sub; [exact Hag|lia|lia] | lia | lia | exact BN].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma frame_agree L LB sp scr W M M' a n :
  hpres L LB sp scr W M M' -> (forall i, a <= i < a + n -> kept L LB sp scr W i) -> agree_on M M' a n.
Proof. intros [HP _] HK i Hi. apply HP. apply HK. exact Hi. Qed.

(* [comment removed for export] *)
Lemma kept_stack L LB sp scr W a :
  hl_sptop L - 2 ^ 23 + scr <= sp -> 0 <= scr -> sp <= a < 2 ^ 64 -> hl_errno L + 4 <= 0x7fff7f800000 -> 0x7fff80000000 <= hl_sptop L ->
  L5.outside W a -> kept L LB sp scr W a.
Proof.
  intros Hsp Hscr Ha He Hlo HW. split. lia. split.
  { right. left. lia. }
  split. { unfold in_errno. lia. } exact HW.
Qed.
Lemma kept_stack_stk L LB M sp scr W a :
  stk (hl_sptop L) M sp scr -> 0 <= scr -> sp <= a < 2 ^ 64 -> hl_errno L + 4 <= 0x7fff7f800000 ->
  L5.outside W a -> kept L LB sp scr W a.
Proof. intros (_ & B & _ & D & _) Hscr Ha He HW. apply kept_stack; try assumption; lia. Qed.
(* [comment removed for export] *)
Lemma kept_below L LB sp scr W a :
  hl_sptop L - 2 ^ 23 <= a < sp - scr -> 0 <= scr -> sp <= 2 ^ 47 -> hl_errno L + 4 <= 0x7fff7f800000 -> 0x7fff80000000 <= hl_sptop L ->
  L5.outside W a -> kept L LB sp scr W a.
Proof.
  intros Ha Hscr Hsp He Hlo HW. split. lia. split.
  { right. left. lia. }
  split. { unfold in_errno. lia. } exact HW.
Qed.
(* [comment removed for export] *)
Lemma kept_block L LB sp scr W A n a :
  In (A, n) LB -> A <= a < A + n -> 0 <= A -> A + n <= 2 ^ 64 -> (a < hl_errno L \/ hl_errno L + 4 <= a) ->
  L5.outside W a -> kept L LB sp scr W a.
Proof.
  intros Hin Ha HA HAn He HW. split. lia. split.
  { left. exists (A, n). split. exact Hin. cbn. lia. }
  split. { unfold in_errno. lia. } exact HW.
Qed.
(* [comment removed for export] *)
Lemma kept_static L LB sp scr W a :
  hl_img_lo L <= a < hl_img_hi L -> ~ hl_alloc_static L a -> 0 <= hl_img_lo L -> hl_img_hi L <= 2 ^ 64 ->
  (a < hl_errno L \/ hl_errno L + 4 <= a) -> L5.outside W a -> kept L LB sp scr W a.
Proof.
  intros Ha Hs Hlo Hhi He HW. split. lia. split. { right. right. split. exact Ha. exact Hs. }
  split. { unfold in_errno. lia. } exact HW.
Qed.

(* [comment removed for export] *)
Lemma kept_inner L LB sp scr W sp' scr' W' a :
  kept L LB sp scr W a -> sp - scr <= sp' - scr' -> sp' <= sp ->
  (L5.outside W a -> L5.outside W' a) -> kept L LB sp' scr' W' a.
Proof.
  intros (Ha & CA & NE & OW) H1 H2 HW. split. exact Ha. split.
  - destruct CA as [IB|[[S1 S2]|IM]]. left; exact IB. right; left; split; [exact S1|lia]. right; right; exact IM.
  - split. exact NE. apply HW. exact OW.
Qed.

(* [comment removed for export] *)
Lemma kept_not_fresh L LB sp scr W a A n :
  kept L LB sp scr W a -> blocks_apart A n LB -> (A + n <= hl_img_lo L \/ hl_img_hi L <= A) -> A + n <= hl_ceil L ->
  (forall b, In b LB -> fst b + snd b <= hl_ceil L) ->
  ~ (A <= a < A + n).
Proof.
  intros (Ha & CA & NE & OW) BA Hlo Hhi HLB Hin.
  destruct CA as [(b & Hb & Hr)|[[S1 S2]|[IM _]]].
  - pose proof (BA b Hb). pose proof (HLB b Hb). lia.
  - lia.
  - lia.
Qed.

Lemma defined_app M a n m : L5.defined M a n -> L5.defined M (a + n) m -> 0 <= n -> L5.defined M a (n + m).
Proof.
  intros D1 D2 Hn i Hi. destruct (Z_lt_le_dec i n) as [Hlt|Hge]. apply D1. lia.
  replace (a + i) with (a + n + (i - n)) by lia. apply D2. lia.
Qed.

Lemma outside_nil a : L5.outside [] a.
Proof. intros r Hr. destruct Hr. Qed.
Lemma outside_cons r W a : ~ L5.in_rng r a -> L5.outside W a -> L5.outside (r :: W) a.
Proof. intros H1 H2 r' [<-|Hr']. exact H1. apply H2. exact Hr'. Qed.
Lemma outside_cons_inv r W a : L5.outside (r :: W) a -> ~ L5.in_rng r a /\ L5.outside W a.
Proof. intros H. split. apply H. left; reflexivity. intros r' Hr'. apply H. right. exact Hr'. Qed.

(* [comment removed for export] *)
Lemma agree_on_trans M1 M2 M3 a n : agree_on M1 M2 a n -> agree_on M2 M3 a n -> agree_on M1 M3 a n.
Proof. intros A B i Hi. rewrite (B i Hi). apply A. exact Hi. Qed.
Lemma agree_on_refl M a n : agree_on M M a n.
Proof. intros i Hi. reflexivity. Qed.
(* [comment removed for export] *)
Lemma agree_of_frame_but F M M' a n :
  L5.frame_but F M M' -> 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> L5.outside F i) -> agree_on M M' a n.
Proof. intros HF Ha Hn Ho i Hi. apply HF. rewrite L5.unsigned_lit by lia. apply Ho. exact Hi. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition obj_limbs (M : word -> option byte) (b : L5.bigobj) (ws : list Z) : Prop :=
  length ws = L5.bo_len b /\ Forall (fun w => 0 <= w < 2 ^ 64) ws /\
  match L5.bo_st b with
  | L5.BInl v0 v1 => ws = firstn (L5.bo_len b) [v0; v1]
  | L5.BDyn cap q => L5.limbs_at segs M q ws
  end.

Lemma limbs_at_app M q ws1 ws2 :
  L5.limbs_at segs M q ws1 -> L5.limbs_at segs M (q + 8 * Z.of_nat (length ws1)) ws2 -> L5.limbs_at segs M q (ws1 ++ ws2).
Proof.
  intros H1 H2 i Hi. rewrite length_app in Hi.
  destruct (Nat.lt_ge_cases i (length ws1)) as [Hl|Hg].
  - rewrite app_nth1 by lia. apply H1. exact Hl.
  - rewrite app_nth2 by lia. replace (q + 8 * Z.of_nat i) with (q + 8 * Z.of_nat (length ws1) + 8 * Z.of_nat (i - length ws1)) by lia.
    apply H2. lia.
Qed.
Lemma limbs_at_zeros M q k : (forall i, (i < k)%nat -> L5.u64_at segs M (q + 8 * Z.of_nat i) 0) -> L5.limbs_at segs M q (repeat 0 k).
Proof. intros H i Hi. rewrite repeat_length in Hi. rewrite nth_repeat. apply H. exact Hi. Qed.
Lemma limbs_at_firstn M q ws n : L5.limbs_at segs M q ws -> L5.limbs_at segs M q (firstn n ws).
Proof.
  intros H i Hi. rewrite length_firstn in Hi. rewrite nth_firstn. destruct (Nat.ltb_spec i n); [|lia]. apply H. lia.
Qed.
Lemma limbs_at_nil M q : L5.limbs_at segs M q [].
Proof. intros i Hi. cbn in Hi. lia. Qed.
Lemma firstn_firstn_le {A} (l : list A) n m : (n <= m)%nat -> firstn n (firstn m l) = firstn n l.
Proof. intros H. rewrite firstn_firstn. f_equal. lia. Qed.

(* [comment removed for export] *)
Definition fresh_block (L : heap_layout) (LB : list (Z * Z)) (M' : word -> option byte) (A n : Z) : Prop :=
  block_range L A n /\ blocks_apart A n LB /\ L5.defined M' A n.

(* [comment removed for export] *)
Lemma fresh_block_bounds L LB M' A n : fresh_block L LB M' A n ->
  4096 <= A /\ (A + n <= hl_img_lo L \/ hl_img_hi L <= A) /\ A mod 16 = 0 /\ 0 < n /\ A + n <= hl_ceil L.
Proof. intros [[H0 [H1 [H2 [H3 H4]]]] _]. repeat split; assumption. Qed.
(* [comment removed for export] *)
Lemma fresh_block_hull L LB M' A n : fresh_block L LB M' A n ->
  hl_img_lo L = L5.hull_lo segs -> hl_img_hi L = L5.hull_hi segs -> L5.hull_apart segs A n.
Proof. intros [[H0 [H1 _]] _] Elo Ehi. unfold L5.hull_apart. rewrite <- Elo, <- Ehi. exact H1. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma model_but_vm_refl m : model_but_vm m m.
Proof. destruct m as [fd [maps lazy mat] io fs pr li ti sc sg]. reflexivity. Qed.
Lemma model_but_vm_trans m m' m'' : model_but_vm m m' -> model_but_vm m' m'' -> model_but_vm m m''.
Proof.
  unfold model_but_vm. intros A B. set (X := m_vmmaps m'') in *. set (Y := m_vmmaps m') in *.
  rewrite B. rewrite A. destruct m as [fd [maps lazy mat] io fs pr li ti sc sg]. reflexivity.
Qed.
Lemma halted_but_vm m m' : model_but_vm m m' -> m_halted m' = m_halted m.
Proof. unfold model_but_vm. intros ->. reflexivity. Qed.
Lemma lazy_but_vm m m' : model_but_vm m m' -> m_vm_lazy m' = m_vm_lazy m.
Proof. unfold model_but_vm. intros ->. reflexivity. Qed.
Lemma materialized_but_vm m m' : model_but_vm m m' -> m_vm_materialized m' = m_vm_materialized m.
Proof. unfold model_but_vm. intros ->. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hi_heap_client L scfg HI LB cr M M' VM :
  heap_iface_ok L scfg HI -> hi_heap HI LB cr M VM ->
  (forall a, hl_alloc_ro L a -> (hl_img_lo L <= a < hl_img_hi L) \/ hl_sptop L <= a) ->
  hl_img_hi L <= 0x7fff7f800000 -> 0x7fff80000000 <= hl_sptop L ->
  (forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a) \/ (hl_ceil L <= a < hl_sptop L) \/ in_block LB a) ->
  mem_grows M M' -> hi_heap HI LB cr M' VM.
Proof.
  intros HIok HH Hro Hhi Hsp Hchg Hgr. eapply (hio_frame L scfg HI HIok). exact HH.
  - intros a Ha Hpriv. destruct (Hchg a Ha) as [E|[S|B]]. exact E.
    + exfalso. destruct Hpriv as [(P1 & P2 & P3)|P]. lia. apply Hro in P. lia.
    + exfalso. destruct Hpriv as [(P1 & P2 & P3)|P]. exact (P2 B). apply Hro in P.
      destruct B as (b & Hb & Hin). pose proof (proj1 (hio_wf L scfg HI HIok LB cr M VM HH) b Hb) as ((R0 & R1 & R2 & R3 & R4) & _).
      lia.
  - intros x Hx. apply Hgr. exact Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma in_lb_remove_neq A B n LB : In (B, n) LB -> B <> A -> In (B, n) (lb_remove A LB).
Proof.
  induction LB as [|[c m] LB IH]; intros Hin Hne. destruct Hin.
  cbn [lb_remove fst]. destruct (Z.eqb c A) eqn:E.
  - apply Z.eqb_eq in E. subst c. destruct Hin as [H|H]. injection H; intros; subst; contradiction. exact H.
  - destruct Hin as [H|H]. left; exact H. right. apply IH; assumption.
Qed.
Lemma in_lb_remove A b LB : In b (lb_remove A LB) -> In b LB.
Proof.
  induction LB as [|[c m] LB IH]; intros Hin. destruct Hin.
  cbn [lb_remove fst] in Hin. destruct (Z.eqb c A). right; exact Hin. destruct Hin as [H|H]. left; exact H. right; apply IH; exact H.
Qed.
Lemma blocks_apart_in A n LB B m : blocks_apart A n LB -> In (B, m) LB -> A + n <= B \/ B + m <= A.
Proof. intros H Hin. exact (H (B, m) Hin). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bytes_at_rdn M : forall bs p, 0 <= p -> p + Z.of_nat (length bs) <= 2 ^ 64 ->
  L5.bytes_at segs M p bs -> rdn segs M (Z_to_bv 64 p) (length bs) = Some (map (fun z => Z_to_bv 8 z) bs).
Proof.
  induction bs as [|b bs IH]; intros p Hp Hn HB. reflexivity.
  cbn [length] in Hn |- *. pose proof (HB 0%nat ltac:(cbn; lia)) as H0. cbn [nth] in H0. unfold L5.u8_at in H0. rewrite Z.add_0_r in H0.
  cbn [rdn] in H0 |- *.
  destruct (match M (Z_to_bv 64 p) with Some b0 => Some b0 | None => seg_rom segs (Z_to_bv 64 p) end) as [b0|]; [|discriminate].
  injection H0 as E0. subst b0.
  rewrite (add1_lit p).
  rewrite (IH (p + 1)). reflexivity. lia. lia.
  intros i Hi. replace (p + 1 + Z.of_nat i) with (p + Z.of_nat (S i)) by lia.
  change (nth i bs 0) with (nth (S i) (b :: bs) 0). apply HB. cbn; lia.
Qed.

Lemma rdn_bytes_at M : forall (bs : list byte) p, 0 <= p -> p + Z.of_nat (length bs) <= 2 ^ 64 ->
  rdn segs M (Z_to_bv 64 p) (length bs) = Some bs -> L5.bytes_at segs M p (map bv_unsigned bs).
Proof.
  induction bs as [|b bs IH]; intros p Hp Hn HR i Hi. cbn in Hi; lia.
  cbn [length] in Hn, HR. cbn [rdn] in HR.
  destruct (match M (Z_to_bv 64 p) with Some b0 => Some b0 | None => seg_rom segs (Z_to_bv 64 p) end) as [b0|] eqn:E0; [|discriminate].
  rewrite (add1_lit p) in HR.
  destruct (rdn segs M (Z_to_bv 64 (p + 1)) (length bs)) as [rest|] eqn:ER; [|discriminate].
  injection HR as E1 E2. subst b0 rest.
  destruct i as [|i].
  - cbn [nth map]. unfold L5.u8_at. rewrite Z.add_0_r. cbn [rdn]. rewrite E0. f_equal. f_equal. symmetry. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite Z.mod_small. reflexivity. pose proof (bv_unsigned_in_range _ b); cbn in *; lia.
  - cbn [nth map]. replace (p + Z.of_nat (S i)) with (p + 1 + Z.of_nat i) by lia.
    change (nth i (map bv_unsigned bs) 0) with (nth i (map bv_unsigned bs) 0).
    apply (IH (p + 1)). lia. lia. exact ER. cbn [map length] in Hi. rewrite length_map in Hi |- *. lia.
Qed.

(* [comment removed for export] *)

End WithSegs.
End L5C.
