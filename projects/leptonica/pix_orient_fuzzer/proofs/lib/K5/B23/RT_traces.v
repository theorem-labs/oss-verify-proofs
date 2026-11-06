(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_RT_traces () := "I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01I47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes3nat02I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01I47Corelib7Numbers7BinNums1Z00c69OSSVerify5KrLib2K53B239RT_traces=CLIENT_TRACESC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B239RT_traces6T_MAINC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List8flat_mapC56Stdlib5Arith8PeanoNat3Nat3lebC47Corelib4Init9Datatypes4andbK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib5Lists4List7existsbC47Corelib4Init9Datatypes4negbC46Stdlib5Lists4List7forallbI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums8positive03c69OSSVerify5KrLib2K53B239RT_traces9ALLOC_PCSC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Peano2le00C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List2InI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List:in_map_iffC47Corelib5Lists7ListDef3seqC47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z2leC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr04K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib5Lists7ListDef6firstnC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_transC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqK47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init5Logic2ex01c69OSSVerify5KrLib2K53B239RT_traces8prefixesC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib5Lists4List8map_consK46Stdlib9micromega=RingMicromega3Op205C46Stdlib5Lists4List;in_flat_mapc69OSSVerify5KrLib2K53B239RT_traces;prefixes_inC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC47Corelib4Init9Datatypes9andb_propC56Stdlib5Arith8PeanoNat3Nat6leb_lec69OSSVerify5KrLib2K53B239RT_traces9t_main_wfC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List=Forall_forallC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07I46Stdlib5Lists4List6Exists00I47Corelib4Init5Logic4True00C47Corelib4Init5Logic3notC46Stdlib4Bool4Bool=negb_true_iffC46Stdlib5Lists4List>existsb_existsC56Stdlib6ZArith6BinInt1Z8eqb_reflC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indK47Corelib4Init9Datatypes4bool02c69OSSVerify5KrLib2K53B239RT_traces@client_traces_wfC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition PC_MALLOC : Z := 0xcb708.     (* [comment removed for export] *)
Definition PC_FREE : Z := 0xcb5a8.       (* [comment removed for export] *)
Definition PC_CALLOC : Z := 0xcb93c.     (* [comment removed for export] *)
Definition ALLOC_PCS : list Z := [PC_MALLOC; PC_FREE; PC_CALLOC].

Definition RA_TOP : Z := 0xf9eb4.        (* [comment removed for export] *)
Definition RA_FUZZ_DESER : Z := 0xfa118. (* [comment removed for export] *)
Definition RA_FUZZ_DESTROY : Z := 0xfa158.
Definition BI_FUZZ_DESTROY_RAS : list Z := [0xfa150; 0xfa158]. (* [comment removed for export] *)
(* [comment removed for export] *)
Definition DESER_DESTROY_RAS : list Z := [0x163b5c; 0x163bc8; 0x163d5c; 0x163d9c].
(* [comment removed for export] *)
Definition DESTROY_FREE_RAS : list Z := [0x10ed74; 0x10eddc].

Definition CLIENT_TRACES : list (list Z) :=
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  [ [0xf9b60]; [0xf9bb4]; [0xf9bd8]; [0xf9d0c]; [0xf9e48]; [0xf9ee0]
  (* [comment removed for export] *)
  ; [0x10e8f4]   (* [comment removed for export] *)
  ; [0x10ed74; 0x163b5c; 0xfa118; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x11a194]   (* [comment removed for export] *)
  ; [0x11a19c]   (* [comment removed for export] *)
  ; [0x10eddc; 0x163b5c; 0xfa118; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10e34c; 0x10e0d0]   (* [comment removed for export] *)
  ; [0x11c678]   (* [comment removed for export] *)
  ; [0x11c6c8]   (* [comment removed for export] *)
  ; [0x10ed74; 0x163bc8; 0xfa118; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0x163bc8; 0xfa118; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10ed74; 0x163d5c; 0xfa118; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0x163d5c; 0xfa118; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10ed74; 0x163d9c; 0xfa118; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0x163d9c; 0xfa118; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x16d3a8]   (* [comment removed for export] *)
  ; [0x16d640]   (* [comment removed for export] *)
  ; [0x16d668]   (* [comment removed for export] *)
  ; [0x10319c]   (* [comment removed for export] *)
  ; [0x1031b0]   (* [comment removed for export] *)
  ; [0xfae88]   (* [comment removed for export] *)
  ; [0xfbc6c]   (* [comment removed for export] *)
  ; [0x103bcc; 0x1702c0; 0x182dc0; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x16fab8; 0x1702d4; 0x182dc0; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0xfbf28]   (* [comment removed for export] *)
  ; [0x10e34c; 0x10f124]   (* [comment removed for export] *)
  ; [0x119768; 0x10f2c0]   (* [comment removed for export] *)
  ; [0x119798]   (* [comment removed for export] *)
  ; [0x119768; 0x110c58]   (* [comment removed for export] *)
  ; [0x16d1fc]   (* [comment removed for export] *)
  ; [0x16d238]   (* [comment removed for export] *)
  ; [0x16d260]   (* [comment removed for export] *)
  ; [0x119768; 0x115958; 0x16cedc; 0x1705fc; 0x182dc0; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10ed74; 0x16d034; 0x1705fc; 0x182dc0; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0x16d034; 0x1705fc; 0x182dc0; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x119768; 0x115f40; 0x16d040; 0x1705fc; 0x182dc0; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10ed74; 0x16d04c; 0x1705fc; 0x182dc0; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0x16d04c; 0x1705fc; 0x182dc0; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10ed74; 0x16d054; 0x1705fc; 0x182dc0; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0x16d054; 0x1705fc; 0x182dc0; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10ed74; 0x16d06c; 0x1705fc; 0x182dc0; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0x16d06c; 0x1705fc; 0x182dc0; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x17072c; 0x182dc0; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x103414]   (* [comment removed for export] *)
  ; [0x1034b8]   (* [comment removed for export] *)
  ; [0x1034c0]   (* [comment removed for export] *)
  ; [0x170d0c; 0x183084; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10ed74; 0x170fa0; 0x183084; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0x170fa0; 0x183084; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x171054; 0x183084; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x12de24; 0x183094; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x12df14; 0x183094; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10ed74; 0x1830b4; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0x1830b4; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10ed74; 0x1830bc; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0x1830bc; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10ed74; 0x1830c4; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0x1830c4; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x170d0c; 0x183140; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10ed74; 0x170fa0; 0x183140; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0x170fa0; 0x183140; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x171054; 0x183140; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x12de24; 0x183150; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x12df14; 0x183150; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10ed74; 0x183174; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0x183174; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10ed74; 0x18317c; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0x18317c; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10ed74; 0x183184; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0x183184; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10ed74; 0x183290; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0x183290; 0x1826ac; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x119768; 0x1535d4; 0x1826b8; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x103bcc; 0x1702c0; 0x182dc0; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x16fab8; 0x1702d4; 0x182dc0; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x119768; 0x115958; 0x16cedc; 0x1705fc; 0x182dc0; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10ed74; 0x16d034; 0x1705fc; 0x182dc0; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0x16d034; 0x1705fc; 0x182dc0; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x119768; 0x115f40; 0x16d040; 0x1705fc; 0x182dc0; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10ed74; 0x16d04c; 0x1705fc; 0x182dc0; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0x16d04c; 0x1705fc; 0x182dc0; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10ed74; 0x16d054; 0x1705fc; 0x182dc0; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0x16d054; 0x1705fc; 0x182dc0; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10ed74; 0x16d06c; 0x1705fc; 0x182dc0; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0x16d06c; 0x1705fc; 0x182dc0; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x17072c; 0x182dc0; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x170d0c; 0x183084; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10ed74; 0x170fa0; 0x183084; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0x170fa0; 0x183084; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x171054; 0x183084; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x12de24; 0x183094; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x12df14; 0x183094; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10ed74; 0x1830b4; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0x1830b4; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10ed74; 0x1830bc; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0x1830bc; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10ed74; 0x1830c4; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0x1830c4; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x170d0c; 0x183140; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10ed74; 0x170fa0; 0x183140; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0x170fa0; 0x183140; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x171054; 0x183140; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x12de24; 0x183150; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x12df14; 0x183150; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10ed74; 0x183174; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0x183174; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10ed74; 0x18317c; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0x18317c; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10ed74; 0x183184; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0x183184; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10ed74; 0x183290; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0x183290; 0x1826d0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10ed74; 0x1826d8; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0x1826d8; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x1559a4; 0x155684]   (* [comment removed for export] *)
  ; [0x155c20; 0x155684]   (* [comment removed for export] *)
  ; [0x1567e0; 0x155684]   (* [comment removed for export] *)
  ; [0x1567ec; 0x155684]   (* [comment removed for export] *)
  ; [0x156b24; 0x155690]   (* [comment removed for export] *)
  ; [0x156c84; 0x155690]   (* [comment removed for export] *)
  ; [0x119768; 0x1535d4; 0x1828f0; 0xfa144; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10ed74; 0xfa150; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0xfa150; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10ed74; 0xfa158; 0xf9eb4]   (* [comment removed for export] *)
  ; [0x10eddc; 0xfa158; 0xf9eb4]   (* [comment removed for export] *)
  ].
(* [comment removed for export] *)
Definition ALLOC_RAS : list Z := flat_map (fun t => match t with [ra] => [ra] | _ => [] end) CLIENT_TRACES.

(* [comment removed for export] *)
Definition prefixes (l : list Z) : list (list Z) := map (fun k => firstn (S k) l) (seq 0 (length l)).

(* [comment removed for export] *)
Definition T_MAIN : list (list Z) :=
  flat_map (fun t => flat_map (fun pc => prefixes (pc :: t)) ALLOC_PCS) CLIENT_TRACES.

(* [comment removed for export] *)
Lemma client_traces_count : length CLIENT_TRACES = 130%nat /\ length T_MAIN = 2052%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_traces ()) [] "p;3p;2p;4p;1g0000j32Tg000Jj23Tg000dj48Tg001?j17Tg001_j24Tg002?j26Tg002Zj11Tf0R0#1#1p=5%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g0039R0g003X#5#0#0#0#0R1;21%51#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0R2=20213011302C8g0047#7R3g004U'4=201g005X,43=202'6do"). Qed.

Lemma client_traces_wf :
  forallb (fun t => (Nat.leb 1 (length t) && Nat.leb (length t) 8
                     && forallb (fun x => (4096 <=? x) && (x <? 2^64) && negb (existsb (Z.eqb x) ALLOC_PCS)) t)%bool) CLIENT_TRACES = true.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_traces ()) [] "h01th11xp;2p;1p;3p-1R0p1006Tp4p710p9P0p1007@p4p710p8g000Jj2@Tg001?j1?Tg002Zj10Tg001_j27Tg007]j26Tg008=j23Tg008[j12Tg009@j14Tg009^j2;Tg00:;j28Tg00:Xj29Tg00;5j1:Tg00;Rj3>Tg00;nj1=Tg00<Lj35Tg0000j3<Tf0R0#2#2p=1g00<hR1g00=HR2'@g0047R3#?R4g003X#0R51730R6'6%05#0#0#0#0#0#0,66'3g00=h#2R6#2#1#1R5#1#1#1#4/;0%46%45'8,90'3%:0g00>M5>3#='3X13=530'3X04g004U35=<12do"). Qed.

Lemma t_main_wf : forallb (fun t => (Nat.leb 1 (length t) && Nat.leb (length t) 9 && forallb (fun x => (0 <=? x) && (x <? 2^64)) t)%bool) T_MAIN = true.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_traces ()) [] "h01th11xp;2p;1p;3g000Jj2<Tg001?j1;Tg002Zj10Tg001_j26Tg007]j25Tg008=j22Tg009^j2:Tg008[j11Tg009@j13Tg00:;j27Tg00:Xj28Tg00<Lj34Tg0000j39Tg00<hR0g00=HR1'<g0047R2#;R3g003X#0R4f0R5,62R6'5%04#0#0#0#0#0#0#0,56'2g00?L/:5g00=h#1R6#3%16#1#1#1#1#3'7,85'2X12=425'2X03g005X34=901do"). Qed.

Lemma prefixes_in : forall l j, (1 <= j <= length l)%nat -> In (firstn j l) (prefixes l).
Proof.
ltac2:(KReplay.run1 (kr_t_RT_traces ()) [] "h01Hh11xh24__p1h34__x1h44__x2h51fh61lh71nh82H1h91yh:1Ah;1Bh<3Hj0h=7__arithh>4__ffh?4__p2h@8__varmaphA5__withB4__x3hC4cstrhD5cstr0hE3lenhF5starthG2z1hH2H0hI2HjhJ1jhK1khL1mp&0p;1p;2p;4p;3p;5p;<p;6p;Bp;7p;8g001?j1RTg002ZR0j16Tg00?jR1j29Tg001_j2FTg002?R2j20Tg00@Dj4QTg00@`j34Tg0000j31j1XTg00A7j2^Tg00AQj5iTg00B0j2ATg00BLj2@Tg000Jj27Tg00BcR3j15Tg009@k108Tg00CCj2<Tg00C`j2JTg00D=R4j2DTg00DZj2sTg00E=j3qTg00EZl<GTg00F?R5j22Tg00F[j6`Tg00GDj4gTg00Gkj1TTg00HPj2fTg00I2R6j2CTg00INj2MTg00Ihj2ETg00JQj1eTg00Joj2dTg00KPj3STg00L9k10;Tg00LYj2cTg00M7k10:Tg00MUj4aTg00N3k109Tg00NQk107Tg00O<j2PTg008[j1~Tg00O_j2\Tg00PBj3[Tg00Pej1}Tg00QGj3YTg00Qjj2{Tg00RLj2zTg00S8j3yTg00SWj4xTg00TIj4WTg00U4j2Uj1rj3|Tg00USj6LTg00V0j6VTg00VNj2OTg00VeR7j2NTg00W=j3oTg00WXj1wTg00X=j4HTg000dj4mTg00Xhj4lTg00YBj1kTg00Z@lBbTg00Zfl<jTg00[Kk300Tg00\4k201Tg00\`j3hTg00]@k602Tg00]dk703Tg00^Hk704Tg00^lk705Tg00_Pk806Tg0047R8f1R9f0R:3|p=>A189:p=?g0039R;P;P;P8P8P8g00`4P3P3P3f6R<g00`Tf5R=f4R>f3R?f2R@P9P:MBbp=pP;P;P8P8P0P3P3P?g00a;P@P9P:M<jp=nP;P8P1P3P5g00a_R0P=P>P?P@P9P:M<Gp=_B0089:p=8g00bA-01:p==g00bmRA?h9:p=;P9g00cYRBg00d8RCPCg00dXRDP:J02p=]P8P9g00e8P:CHp=KP9PBPCPCPDP:g00e_K03p=3P@PBPCPCPDP9P:K04p=:P8P9g00f?P:CHp=BP@PBPCPCPDP9P:K05p=ZP?PBPCPCPDP@P9P:L06p=IP;P8P1P3P5P0g003XR0g00?LR5P?P@P9P:M<Gp=tP;P;P;P8P8P8g00ffP3P3P3P4g00gFP0P5P?P@P9P:MBbp=uP;P8P7P3P6g00giP=P>P?P@P9P:M<Gp=v%R8R6%60R7/9:1F89,9:'0g00hKR4p4p710R1P4p4p7210R4P9\9RB%R@REP2P>P?P@P9CQ94?:P>P:O1=1=@A4<:?'0X1=,^=RF[P?P:O1=1>9A4=:@'0X1>,^>P=P>P?P@CQ94>9[RGP<P=P>P?CQ94=@\FP>P?P@P9P:DiP:n2001000000120000000X9@W6W5W;W:PG^9@^6E^5B^;4^:1P:P;P6%6:/>>R1XK;1F8?,A0R41>@?RBP;1>?>91611F8>R1,A094;:'0X1;1@@7RE%6E/>?=16BA4;E4176?A16??1@?7RE#6R4=1;?RB%5?RGg00=hRF$08RH'<,J5RI/DHRJ/?GP;P8%X;P3%X8%59%5:'?A1;9:1s9:3qX9;X1;P4PJ1D:HX18PEPI1<9:,J5XL8X78P?PG178GRJP7PH178HR4FpR3CnP?PGPJM<G197?RK19?1RL'012HGRM%51RN,2GRO'0RPPKPLPMPOP7PHP4P?PGPJE_P?PGPJP1PN178NRJE_E`P@CgRGPP%T>R4%5>,25RO1F8<RM#TRL%5M,25RM%5</<HRK,f5RQ1C5K1J5KRR/?K'012K5A18R5'0'MRRf7#5/<H,J5RKP8p-0RS%67RT,E8RU1E871E80RV'8RW'8RX#=%6TRT,E8RY%eF,d8RZ=S8U/8VRU'8#=%=U&0;ARU';';';%RARAP81c8@R[P9&0:8Ca&098R\&078R]1]]>1P8FR^%~F,P8R_1\8HR`5[8Ra'K,3]5:]1\85Rb,Ba,3]1K^b,3]Ra5:]5Z]%}CRCP]1B`_,3]1]]=Rc5:]PCAY8^`/K_,3]CICI1{]DRDP:P@g00<hRdg00=HRe'71z:@=1dedAy859CxReb>b@bAX38X48X2SW?1<9HRd,?:,0@12d5A18:5Rd'0'M12H@/0>1D@H/??[[^38^48^2S^?SP:f9Rf#5Rgf:Rh,F8#5Ri'21<gHRj,C5PgP9P@P=O6b=bGb8bDbCb<CWPBp-1RB/78A1B88RB1@<7#6=1;<f8R<=16<P61@<7#6Rk/>f1><fRlPlP6^66RlP6P:PhO1X5l1U8kRh1U8<RmPlPhPhPmPl^7;RhPlP:1@f7#6O1X5h%r8R7P717h7ELP;PlP7PkP<P9ELEVELP6P6PmPfPf176fELEVW8WHX0BP:O1b0P:O1b0P:O1b0P21A9@94;:19@91O@?,N9'0R2[199:1O9@,N:'01A@?94;9[RB1A?>94;@\2Ao@9:P:n2001000000120000000X7;XF;XE;PB^7;^F;^E;P:P1P0PE190ERB1O01R0,NER2'0125IR>1D5NRf,CIRm'0PBP2P>Pm1785RmPEPIP3CtPEPIP3P0PfPmP1PNPJCuEvE`PGPPP4POPLPMPQPRPKP818YX#=AS8ZY/8VRV#=%6T,E8/8V#=18YW#=/;U';';';PAP8P[P91c8?CaP\P]P8Pbg00hhR\%wF,P8RF=[8`R[CH,3]1K^[,3]5:]A:]ca5Z]PCP]1B`F,3]1BF_,3]5:]PC1Bb^,3]P8P^P\AY8b_CH,3]5:]CICIPDPeb>b@bAX38X48XB8X2S1<@HRe,C51?:e'010?d'M12H?12?@'0125@1D5?,C@'0[[^38^48^B8^2SP:12j5PgPiP9P@P=O6b=bGb8bDbCb<CWO4b0CmClO6b01>9@%k@546eWIXJ;W6o"). Qed.

(* [comment removed for export] *)
Lemma t_main_prefix : forall pc t j, In pc ALLOC_PCS -> In t CLIENT_TRACES -> (1 <= j <= S (length t))%nat ->
  In (firstn j (pc :: t)) T_MAIN.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_traces ()) [] "h02pch11xh21Ah31Bh41Hh51fh61lh71th81yh92Hjh:3Hpch;2Hth<1jp;1p;3p;2p;4p;5g001?j17Tg00@`j30Tg002Zj19Tg00?jj25Tg001_j2;Tg002?R0j22Tg007@R1j43Tg00A7j2:Tg00iOj5>Tg00YBj14Tg00U4j36Tg00ioj3@Tg000dj4=Tg00Xhj4<Tg00\`j3?Tg0047R2f0R3g00>MR430p=8f1R5=?23p=1%72R6g0039f2R7#8g004UR89067g003X#9R9/57f3R:,;2#9,57'2P1p4p710R;P1p4p7210R1%75\5R<%77R=P0f4R0P:P7P5C390:3f5R>f6R??03:P0P3O190>7'2X1>':R@[A0>37P:P3O19005'2X10,:0P>P0P:P7C39005[RAP?P>P0P:C390>7\@P0P:P7P5P3D>P3n2001000000120000000X87W6W5W3W2R@PA^87^6=^5<^31^2;R;P3P6P6P2P61135#4X02P4C3R5X76P811?>9620R1P6A0638f7R</1?R=962>RA=065'2X16P>A06>8P2P6113?#4X02P4C39061P7P@P;P3P2P6113<#4R;X02P4PAP2%83f8/1<962?=06;'2X12P<%8<%4=906AP0P7159>1;2=,5>'2e9@=>C=C<O6b4C=C<O6b411>0962:g005X506eW9W;W:W<W7X02o"). Qed.

Lemma t_main_length : forall tr, In tr T_MAIN -> (1 <= length tr <= 9)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_traces ()) [] "h01Wh12H0h22W0h32W1h42W2h54__x1h61mh71nh81xh91Hh:2_Hh;7__arithh<4__ffh=8__varmaph>5__with?4cstrh@5lemmahA1thB2trp;1p;3p;2p;6p;4p;7p;<p;8g001?j1DTg00@`j3`Tg002Zj14Tg007]j20Tg008=j25Tg009^j2RTg008[j18Tg009@j1;Tg00:;j2LTg00:Xj2HTg00<Lj39Tg00k0j2_Tg00kIj3UTg00l:j3TTg00l]j3ATg002?R0j27Tg00?jR1j23Tg00m@j2QTg00BcR2j1<Tg00F?R3j26Tg00WXj1PTg000Jj2:Tg00F[j6OTg00GDj4?Tg00Gkj1NTg00L9j1KTg00LYj2ITg00N3j1JTg00NQj1GTg00O_j2>Tg00O<j2MTg00X=j4BTg00Pej1FTg00^Hj7ETg00Qjj2STg00RLj2^Tg00S8j3]Tg00SWj4\Tg00TIj4VTg001_j2WTg0000j3XTg00EZl<YTg00]dj7ZTg00_Pj8[Tg0047R4f0R5'Wp=2g00<hR6g00=HR77X5p=1g0039R8P4P1P2P3g00a_f5R3f4R2f3R1f2R9f1R:P5M<Yp==P:g00cYR;g00d8R<P<g00dXR=P5g00e_FZp=@P1P;P<P<P=P9P:P5G[p=C%D4R>g005XR?9`>5R@g00mcg003X#4RA%25RB'0%4A#4#4#4#4#4#4#4RC,0B'5g00?LRB/R5g00=hRD#8RE#;%8ERE#8#8#8#8#;'L,H5'5X84RF=945'5XA>RG=9>?#1RHPGP:O1#1\@^8>R@,_HAUH@5W@AT>G?P5O2P@P5P1P9O2%21R@,0A10@C'5A94F1'5#1%22R@,0A10@C'5R@A94F2R2;A5%1@%12'7P0%23R2,0A102C'5#1A94F3#1f6#2R3,3A133C'7P5f7#2R3,0A103C'5#1f8994F#1f9#2RF,0AR310FCRF;A:%13%1F'7P0f:#2RF,0A#110FC#1f;#2RF,3A13FC'7P5f<#2,0A#1f=#2/0C#1P010:5#1139:[R013:5109:#1RF[1319\F1Q:5P:n2001000000120000000X68X78RFP0^68^78R8P5PAf?#2R0P9O313A0PFP8P5fA#2R8PCP1O3138CfB#2R8,3ARF138CR0'7%;DR3%<8R2'6R@%PE#;RE,62RG'7PFP0P@PGPAP31:43R@P8P21:42RFE=P8P2PFPCPE1:4EE=RCEOP0PGPCP5C?PGfC#2RG,3A%<GRC,63R0PAP3P@PGPC1:4CE=P1C?P0fD#2R0#N%<0,6Bg00bmR0#K%D01I4:%J4%G4R0P41>43g00f?RC1M4DRDCB,@0RG%F<R@P0P4PDPC1>4ECB,@0RCP@P0P;P<P<P=PGPCFECCCC1S0=P5P91:671^59#1dA]4B:C\b<b=b>X54163516:E1639169E'7[[^54P5fF#2#<P9P1O3b;b?b2b2CVb4b1b3b1W4W3P:P5O2n2001000000121000000b0W:W0P:P5O2n2001000000121000000b0b0b0b0W9WBo"). Qed.

Lemma t_main_range : forall tr, In tr T_MAIN -> Forall (fun x => 0 <= x < 2 ^ 64) tr.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_traces ()) [] "h01Wh11xh21mh31nh42H0h51Ah62Hah71Ph82W1h92W2h:4__x1h;1lh<5lemmah=1Hh>2Hxh?2_Hh@7__arithhA4__ffhB6__sat3hC6__sat4hD8__varmaphE5__withF1thG2trp;1p;3p;2p;4p;7p;8g001?j1?Tg00@`j3:Tg002Zj14Tg001_j2;Tg007]j21Tg008=j22Tg009^j27Tg008[j19Tg009@j1DTg00:;j2RTg00:Xj28Tg00<Lj3@Tg00k0j2GTg00kIj3HTg00l:j3FTg00l]j3ETg002?R0j2<Tg00I2j23Tg00nbj3>Tg00oCj3XTg00F?j2=Tg00oej2WTg010Ej2VTg010ej2UTg011Mj3TTg00L9j1QTg00LYj2PTg00N3j1NTg00NQj1MTg00O<j2LTg00O_j2ATg0121j1KTg012Oj3OTg00X=j4BTg00Pej1JTg00^Hj7STg00Qjj2`Tg000Jj2_Tg00RLj2^Tg00S8j3]Tg00SWj4\Tg0000j3YTg00]dj7ZTg00_Pj8[Tg0047R1f1R2f0R33@p=6g00<hR4g00=HR57Y3p=0g00?LR6/=3p=5P2g00cYR7g00d8R8P8g00dXR9P3g00e_FZp=Cf3R:P7P8P8P9f2R;P2P3G[p=I%?1R<g005XR=9:<3R>g00mcg003X#4R?1;13R@'1%4?#4#4#4#4#4#4#4RA,1@'21763g00=hR@#9RB#DRC%9B#9#9#9#9RB#DRD'RRE,83'2X11RF/63'2XF<RG=@<=#0RHPGP2O1#0\>^1<R>,GHAHH>3W<AF<G=P3O2P>P3P:P;O21;1:R>,1?11>A'216F:'2#0f4R>,;1RG,1?11GA'2RG16F>R=;E3%0G%0='<P0f5R=,;1RG,1?11GA'2#016F=#0%53133ERG'<X11R<f6RH5>1P3f7,;1RI,1?11IA'2#0f8RI,6F#0f9RA,6F#0f:R?9:13PFP2O1#0RJ[^11RK'G16F?#0f;RL9:13PJ[^11;H3W<AF1FAP3O2PKg0132p4p710RKp-0\3RA%?2RFP0A>;23A:>3;P>P2O1[^1:RJ[A::32P:P2O1[^1;A>:;2[RMA>>:;\JAX;23P3n2001000000120000000W;W7W5PM^;F^7A^5KP3P1P<PLf<9:13P:P2P3O21762182E'2#0176;RL18;ER<;E3%0L%0<'<P0176:#018:E#0%5>13>E'<P3176=#018HE#0P01723#01=;2[RH1=2317;2#0R>[1=:;\>1W23P2n2001000000120000000X21X31PH^21^31P3P6PIP;O3%5IP01823#013;2[R0132318;2#0RI[13:;\I1V23P2n2001000000120000000X21X31P0^21^31P3P?PEP:O313?E1UCD136C%5D136E[[%5CR?g013OR0ATCD2UW6%5E\0^6?g00bmR?#Q%??1P12%N1%M1R?P11L1@R@g00hh1A1C%KB5O1CB,C?RB%J8RCP?P11A16g00f?P@CB,C?R@PCP?P7P8P8P9P@PBFSCICI1`?9P3P;1_451^3;#0dA]162C\bAbDbEX:1%52%5;13;E'<[\G^:1P3f>P:P=O3b@bBbCb9b4b8b4W9W8P2P3O2n2001000000121000000b0b0W>X11O4b4b0W0W?P2P3O2n2001000000121000000b0b0b0b0W=WGo"). Qed.

Lemma client_trace_facts : forall t, In t CLIENT_TRACES ->
  (1 <= length t <= 8)%nat /\ Forall (fun x => 4096 <= x < 2 ^ 64 /\ ~ In x ALLOC_PCS) t.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_traces ()) [] "p'0h01xh12H0h21Wh32W3h41mh51nh61Ah72W0h84__x1h91lh:2W4h;1bi001bh<2Hah=1Ph>2W1h?2W2h@2WahA2WbhB7__arithhC4__ffhD8__varmaphE5__withF4cstrhG1fhH5lemmahI1thJ1EhK1HhL3HinhM2HxhN6__sat5hO6__sat6hP1ep;1p;3p;2p;6p;4p;<p;7p;8g001?j1RTg00@`j3@Tg002Zj1<Tg007]j24Tg008=j25Tg008[j1JTg009@j1FTg009^j28Tg00:;j2dTg00:Xj29Tg00;5j1:j2[Tg00;nj1?Tg00<Lj3\Tg00k0j2YTg00kIj3XTg00l:j3VTg00l]j3KTg002?R0j22Tg00?jR1j26Tg00F?R2j21Tg00I2j27Tg013kj1ITg00nbj3ATg00m@j2eTg00BcR3j1=Tg00F[j6cTg00GDj4HTg00Gkj1TTg00L9j1bTg00LYj2aTg00N3j1`Tg00NQj1_Tg00O_j2OTg00O<j2}Tg00Pej1|Tg00Qjj2{Tg000Jj2]Tg00RLj2zTg00S8j3yTg00SWj4xTg00TIj4uTg00oCj3tTg00oej2sTg010Ej2rTg010ej2qTg011Mj3pTg0121j1oTg012Oj3nTg00X=j4WTg014Dj1mTg00;RR4j3LTg00A7j2UTg014ej3lTg015Hj1kTg000dj4QTg00Xhj4jTg015jj6ZTg0000j3PTg016Fj2iTg001_j2hTg00EZl<vTg00]dj7wTg00^Hj7gTg00_Pj8fTg0047R5f0R6'hp=3%J6#Jp=Dg00>MR79L56p=;f1R8=\56p=>g00<hR9g00=HR:7P6p=0A@567p=E1]56p=Bg0039R;P5P1P3P2g00a_f5R2f4R3f3R1f2R<P8P6M<vp=CP5P8g00f?P6CWp=SP8g00cYR=g00d8R>P>g00dXR?P6g00e_Fwp=NP<P=P>P>P?P8P6Fgp=^P1P=P>P>P?P<P8P6Gfp=Mg016eR=9P96p=G%R5R@g004URA9@@6RBg017Eg003X#<RC%36RD'4%<C#<#<#<#<#<#<RE,4D'5g00=hRD#JRF#DRG#J#DRH#D#D#D#FRI/86%FFRF%FHRJ'dRK,96'5%:6#;#?'5X05RL/>6'5XI@RM=\@A#0RNPMP8O1#0\B^0@RB,YNAXNB6WHAV@MAP6O2PBP6P1P<O2%31RB,4C14BE'51>L1'5#0%33RB,4C14BE'5RB1>L3RM;K6%0B%0M'2P0%32RM,4C14ME'5#01>L2#0f6RM#3RB,6C16BE'211I6176KRB'2%E6RA#I'2X05R@=A5M'2P6f7RN#3RO,4C14OE'5#0f8RO,>L#0f9RP#3RQ,4CRR14QERQ;K8%0R%0Q'2P0f:RQ#3RR,4C#014RE#0f;RR#3RS,6C16SE'2AA5@R'2P6f<#3,4C#0f=RS#3/4E#0P01486#016<8[RT168614<8#0RU[161<\U1e86P8n2001000000120000000X4;X5;RUPT^4;^5;R;P6PCf?RT#3RVP<O316CVPUP;P6fA#3R;PEP1O316;EfBR;#3RU,6CRV16UERW'2RXAA5@;PX%FDRX%=URY'1RZ%FGRG,1YR['2PVPWPZP[PCPX%BXRZPUPY%BYRVECPUPYPVPEPG%BGRVECRYEcPWP[PYP6CHP[fCR[#3RY,6C%=YRW,1XRUPCPXPZPYPW%BWECP1CHPUfDRU#3RW#Tg00?LRY%=W'1g00bmRW#bR\%RWRW1a58R]%`5R^%_5R_1O5X1}5DRD'S,N_R`%|>R>P_1O5G,SD,N_RaP>A^_`aCMCM1{_?R?P6P<1]9:1z6<#0dAy5Y8CxRabCbDbEX8511X6118G11X<11<G'2[[^85P6fFR`#3#=P<P1O3bBbFb7b7Cu1>L;#0A@56[PLP8O1#0Rb[^05Rc'Y1>L[#0A@56UPb[^05;X6WHAV5L;PPO2Pcg0132p4p710Rcp-0RL\6Rb%R8RdP0AA<86A@36<ReP3P8O1[^01Rf[A@168RgP1P8O1[^0<AA1<8[RhAA31<\fAt<86P6n2001000000120000000W9W=W6Ph^9d^=b^6cP6P5P@PUfER@9@56P1P8P6O218I8198K'5%:8#;#?'5#018I<19<K'5Rc%:<#;#?Rb;K6%0c%0b'2P018I1191K'5#0%:1#;#?#011I3173K'2%E3#I'2P618I2192K'5#0%:M#;#?#018INR219NKRN;K8%02%0N'2P018IO#019OK#011IP17PK'2%EP#I'2P618IQ#019RK#0P01886#011<8[RQ118618<8#0RP[111<\P1s86P8n2001000000120000000X45X55PQ^45^55P6PIPSP<O311ISP01986#017<8[RS178619<8#0RQ[171<\Q1r86P8n2001000000120000000X45X55PS^45^55P6PTPKP1O317TKf@RT,1I17TK'2%ETRT#IRSfU#3RQ/6E%=QRP/1GRNPQPP%BPPEPGPVECP[CHPNfV#3RN,6C%=NRV,1XRGPCPXPZPNPV%BVECP`CHPGfW#3RG#T%=G,1Y1qFJ17YF11YJ17YK[[11YFRGg013ORVApFJ8UW<11YK\V^<GP\PWP]P^P_P5PDg00hh1O5F%oH5n5CW,N_RHP>P_1O5I/SD,N_RDP>A^_DHCMCMP?PabCbDbEX8511I811I<17<K'2[\B^85P6P`PMPOO3bBbNbObFb7b7P0%?6#0%G8[RO%G6RM%?8#0R`[%G<\`%m6P8n2001000000120000000X;9PO^;9P6%:;#;R;PRO2%G;P4p4p710R4P9\6R;P0AL<86#0P1P6O1#0,2eX01,U1Re[P<P6O1#0,2gX0<,U<AL1<8#0[RgAL31<#0\eAl<86P6n2001000000120000000X9dWGW6Pg^9d^G;^64P6P5%:UR4P7P51[@6#0,2AX05PU%EU1[UU#0P1%kUCQCjO4b1%:[#;#0P9%;4PMX;9P8P:P6EZAP9:=P9P:P9PLP6PVg018KRVn0110000020000XP9g018hP=P6EZPV1iV6b1b:bJb:b1XLTPSeCQbAb1b@b1WAW@P8P6O2n2001000000121000000b3W:W3P8P6O2n2001000000121000000b3b3WMX05O4b1b3CQb?b1b>b1W?W>P8P6O2n2001000000121000000b2W3W2P8P6O2n2001000000121000000b2b2b2b2WKWIo"). Qed.
