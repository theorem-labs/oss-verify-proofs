(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg MmapSim SymExec MemSplit RefMemcpyLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import SymExec2 SymExec2Sound SymRun SymDrive.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_SymDriveX () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List9nth_errorC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List2InC46Stdlib5Lists4List=Forall_forallC46Stdlib5Lists4List<nth_error_InC47Corelib4Init5Logic5proj1I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C46Stdlib5Lists4List:Forall_appC47Corelib4Init9Datatypes3appI47Corelib4Init5Logic3and00C47Corelib4Init5Logic3iffK47Corelib5Lists7ListDef6Forall02C47Corelib4Init5Peano2ltC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init5Logic6eq_indC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z7add_0_rC45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addK47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib6Common8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC46Stdlib6ZArith:ZArith_dec;Z_lt_le_decC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init6Specif7sumbool00C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr07C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib6Common8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedC46Stdlib6ZArith4Zdiv?Z_mod_same_fullC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7w_add_1C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C56Stdlib6ZArith4Znat5Nat2Z5inj_0K47Corelib4Init5Logic4True01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00I47Corelib7Numbers7BinNums1N00K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02c69OSSVerify5KrLib6Common9CliDriver9SymDriveX9rdn_agreeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver9SymDriveX8know_nthC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver9SymDriveX=rdn_untouchedC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26adenotC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6v_addiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25a_offC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S6estartC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okI79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver9SymDriveX<kwr_store_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_lC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22evC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init5Logic9False_indK47Corelib7Numbers7BinNums1Z03K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib5Arith8PeanoNat3Nat6eqb_eqK46Stdlib9micromega7EnvRing5PExpr06K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver9SymDriveX=entry_below_bC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7compareI47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison03K47Corelib4Init9Datatypes4bool02I47Corelib7Numbers7BinNums8positive00I47Corelib4Init5Logic5False00I4ELinuxProcessSemantics5Riscv5Instr5aluop00I4ELinuxProcessSemantics5Riscv5Instr5mulop00C46Stdlib5Lists4List7forallbc69OSSVerify5KrLib6Common9CliDriver9SymDriveXAentry_below_soundC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC59OSSVerify5KrLib6Common7CatExec6wbytesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib6Common7CatExecDlength_N_to_le_bytesC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or02C59OSSVerify5KrLib6Common8MemSplit>wbytes_outsideC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indc69OSSVerify5KrLib6Common9CliDriver9SymDriveX;log_below_bC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver9SymDriveX?mem_denot_aboveC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28expr_eqbC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S;expr_eqb_eqC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver9SymDriveX4esubC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem7mul_divC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27ext_valC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22ebC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28blob_valC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28expr_indC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symc69OSSVerify5KrLib6Common9CliDriver9SymDriveX4asubC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver9SymDriveX:esub_soundC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C47Corelib4Init5Logic7and_indc69OSSVerify5KrLib6Common9CliDriver9SymDriveX;asub_estartC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms5flip2C47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismc69OSSVerify5KrLib6Common9CliDriver9SymDriveX9flat_asubC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver9SymDriveX:asub_soundC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry02C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S5elenZC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3nthK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver9SymDriveX4ksubC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC47Corelib7Classes?RelationClasses=iff_ReflexiveC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:Forall_mapc69OSSVerify5KrLib6Common9CliDriver9SymDriveX:ksub_soundC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List;Forall_implC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_getC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24ridxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat;lt_ge_casesC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib5Lists4List<nth_overflowC56Stdlib6ZArith4Znat5Nat2Z6inj_leC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List:length_seqC46Stdlib5Lists4List:length_mapC69OSSVerify5KrLib6Common9CliDriver8SymDrive9junk_valsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8app_nth1C69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC46Stdlib5Lists4List=app_nth2_plusC69OSSVerify5KrLib6Common9CliDriver6SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun>vals_app_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun=know_ok_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun=regs_ok_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun<expr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun<edenot_agreeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfC47Corelib4Init5Logic3notI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List:in_map_iffC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S:ridx_rangeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S>ridx_roundtripC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S8ridx_injC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive?regs_after_callC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consI47Corelib4Init9Datatypes4prod00C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25carryC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S8log_flatC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C69OSSVerify5KrLib6Common9CliDriver6SymRun;carry_afterC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec5v_addC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4ZdivAZplus_mod_idemp_rC59OSSVerify5KrLib6Common8PropExec7alu_addC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01C47Corelib4Init5Logic7f_equalC59OSSVerify5KrLib6Common<RefMemcpyLib;callee_keptC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6leb_gtC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z6ltb_geC59OSSVerify5KrLib6Common7MmapSim6unfillC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC59OSSVerify5KrLib6Common7StoreOk<store_ok_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver9SymDriveX9wview_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk?store_ok_of_allC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S6flat_uC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver9SymDriveX9kn_unfillC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver9SymDriveX>unfill_outsideC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver9SymDriveX>kentry_apart_bC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6filterC46Stdlib5Lists4List9filter_InC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX2<ranges_apartC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2SBranges_apart_soundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_ltc69OSSVerify5KrLib6Common9CliDriver9SymDriveX;unfill_noneC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphc69OSSVerify5KrLib6Common9CliDriver9SymDriveX>store_ok_agreeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06I46Stdlib5Lists4List6Exists00C46Stdlib5Lists4List7existsb".
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section VP1. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma know_nth : forall segs E M kn i K,
  know_ok segs E M kn -> nth_error kn i = Some K -> kentry_ok segs E M K.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP1"] "h01xh11Eh22HKh32Hnh41Kh51Mh61ih72knh84segsp;1p;4p;3p;2p;5p;6p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9g002PR0p4p710p1002np4p710p8g003Lj13Tg003lj10Tg004Qj12Tg004oj11Tg005Rj18Tg0064j4<TP0j3;Tg007Dj2:Tg007fj39Tg008@j36j47Tg009Rj34Tg00:3j35Tg00:Jj3?Tg00:lj5>Tg00;Mj6=Tg00;h#3g00<gg00=o#0#0#0R0#0#0#0#2#1%20#1#8[g00>TR0#3g00?_f5R1f4R2f3R3f2R4C<%80A;034f1R5,:039f7R6f6R7;61R8=402f0R9=507f:f9R:f8R;P5C7[^00[A5091P:P;P6P5C7[^00A6;67=401[A?082P5P4P0P2P3P4P9D>E=W3W2X40W6W7W5W1W8o"). Qed.
End VP1.

Section VP2. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma know_ok_app : forall segs E M k1 k2,
  know_ok segs E M (k1 ++ k2) <-> know_ok segs E M k1 /\ know_ok segs E M k2.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP2"] "h01Eh11Mh22k1h32k2h44segsp;1p;3p;4p;2g003Lj14Tg003lj10Tg004Qj13Tg004oj12Tg005Rj1:Tg008@j39Tg00@>j48Tg00@]j36Tg0064j41Tg00A:j27Tg00AUj25Tg00;h#4g00<gg00=o#0#0#0R0#0#0#0#3#2%30#2#:[g00>TR0#4R1P0f4R2f3R3f2R439f1R5f0R6C8P2P3P4A6056C1P2P3P4P5C1P2P3P4P6C1'7'5eX31W2W1W0W4o"). Qed.
End VP2.

Section VP3. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma know_ok_cons : forall segs E M K kn,
  kentry_ok segs E M K -> know_ok segs E M kn -> know_ok segs E M (K :: kn).
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP3"] "h01Eh11Kh21Mh32knh44segsp;1p;4p;3p;6g003Lj13Tg003lj10Tg004Qj12Tg004oj11Tg005Rj18Tg008@j47j34Tg0064j46Tg00Anj65Tg00;h#3g00<gg00=o#0#0#0R0#0#0#0#2#1%20#1#8[g00>TR0%30f4R1f3R2f2R3f1R4C7f5R5P1P2P4C6P0f6?451P2P3P4f0E5UUW3W1W2W0W4o"). Qed.
End VP3.

(* [comment removed for export] *)
Fixpoint kindex (p : kentry -> bool) (kn : list kentry) (i : nat) : option nat :=
  match kn with
  | [] => None
  | K :: r => if p K then Some i else kindex p r (S i)
  end.

(* [comment removed for export] *)
Definition is_krange (e : expr) (K : kentry) : bool :=
  match K with KRange e' _ _ => expr_eqb e e' | _ => false end.
Definition is_kalign (e : expr) (K : kentry) : bool :=
  match K with KAlign e' _ => expr_eqb e e' | _ => false end.
Definition is_kdisj (b1 : expr) (b2 : expr) (K : kentry) : bool :=
  match K with
  | KDisj (SA c1 _) _ (SA c2 _) _ => expr_eqb b1 c1 && expr_eqb b2 c2
  | _ => false
  end.
(* [comment removed for export] *)
Definition is_kwr_cov (b : expr) (k m : Z) (K : kentry) : bool :=
  match K with
  | KWr (SA c kk) len => expr_eqb b c && Z.leb kk k && Z.leb (k + m) (kk + len)
  | _ => false
  end.
(* [comment removed for export] *)
Definition is_kimg_cov (a n : Z) (K : kentry) : bool :=
  match K with
  | KImg lo hi => Z.leb lo a && Z.leb (a + n) hi
  | _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section VP4. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma rdn_agree : forall segs M M' n (a : word),
  (forall j, (j < n)%nat -> M (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = M' (Z_to_bv 64 (bv_unsigned a + Z.of_nat j))) ->
  rdn segs M a n = rdn segs M' a n.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP4"] "p'0h01zh14__x1h21Hh37__arithh44__ffh54__p1h68__varmaph75__with84__x2h94cstrh:1nh;3Hagh<3Hj0h=6__sat1h>6__sat2h?5cstr0h@1xi001xhA2H0hB1bi011bhC1jhD2HahE1ahF2b1hG2b2hH1ohI3HgehJ2HjhK3HlthL2IHhM1MhN2M'hO1mhP1si021shQ4segshR1yi031li044restp%0p&0p;1p;2p;3p;4p;6p;<p;7p;8p;Bg003Lj1YTg003lj1HTg004Qj1^Tg004oj1@Tg005RR0j1eTg00BOR1j2>Tg00Bgj22Tg00CQR2j13Tg007fj31k100Tg00D1j4<Tg00Dij2JTg00ECR3j1DTg00Ebj1ZTg00F@R4j20Tg00F]R5j25Tg00G9j1BTg00G^j1wTg00H>j2]Tg00H\j1rTg00I:j1pTg00Iej2TTg00JHj2`Tg00Jkj1bTg00KMj2iTg00Koj2hTg00L[j3gTg00M:j4fTg00Mlj4MTg00NWj6CTg00O3j28Tg00OYk10:Tg00P:k209Tg007Dj2dTg00Plj2cTg00Qhk308Tg00RKj3XTg00S0k307Tg00SPk106Tg00TNk204Tg00A:S00j2LTg00Tkk202Tg00URj2GTg00UnR6k201Tg00VNj1}Tg00Vlj4zTg00WOl<PTg00X4j4VTg00X[j2yTg00YCj3xTg00Ygj1vTg00ZEj4uTg00Zcj3sTg00[Fj2qTg00\Vj3tTg00]:j2ATg00]`j2=Tg00^@j1OTg00_Bj2QTg00`1j1oTg002nj6ITg00`Vj3nTg00a=j1{Tg00bMj4|Tg00bnl<aTg00cSj4WTg00d>j7mTg00dbj3lTg00eEj8kTg00eimB03Tg00fOj6jTg00g3k705Tf2R7f1R8f0R9'0'8p=:g00gWR:/J9p=7g00?_R;P;P:P:P3P2P2f3R3g00h5P7P8P9M<ap=KP;P:P1P2P5g00hYR<g00i;R=g00iZR>P3P7P8P9M<Pp=~1G>9p=6P:P8g00j8P9CWp=RP8g00j_R?g00k>R@P@g00k^RAP9g00l>Fmp=9Al:89p=FP:P8g00l^P9CWp=EP3P?P@P@PAP7P8P9Gkp=?A1:89p=4P;P:P:P:P2P2f5RBf4RCP3P7P8P9M<ap=[P:P:P:P:P:P:P4P9P8P7P4P3PCPBf6R4f7RDf8REf9RFNB03p=_P;P:P1P2P5P<PBPCP3P7P8P9M<Pp=NP:P8g00mEP9CWp=UP8P?P@P@PAP9Ejp=\P7P?P@P@PAP8P9K05p=SP:PCP3P7P8P9EIp=;g00;h#Yg00=oR?#HR<#H#HR5#H#H#HR2#^R1#@RG%^5#@R5#eRH]@RI1>97P41217RJ%385:1RKO1RLPBPKO1RM51H[^C;%Y5RN#eROP4PBP8P7C<P4PCP8P7C<31[^EGRPX:;1>9=PCPKO191HM[^C;PBP3P8P=C<,JOW;XEG%D3RM,>9PDPKO1=1HL[^C;P9P=1>=M%33RL%Z?RK'0RQ,5>1J:>PMPQ109KRQX@:RRP3PL%7LCKC~%B3%6Lg00mlRL#wRS%YLRL1]:8RT%r:RU%p:RV1T:>RW1`:?R?'R,9VRX%b@R@1T:KRY,F?RZ,EW,9VC?1iVARAP9P7g00nXR[g00o8R\'J1h97=1[\dAg:>8CfR\b4b6b7X1:%69108KR[,5>[^1:P9%3BR]P8O2b3b9CMO2P41218%3=R=5:1R^O1PBP^O151HP:P=PE1213R==:19R^O1PDP^O151HX0:P9P>g00oXECPDA:1J>RJO1P4PJO151HP:10=>PF1819RJO1PEPJO151HX0:P9P=&0:=ECPE181=R=O1PDP=O151HPG121C,81f:R=P9O1PFP9O151HXBGP9PC2091CECPFPCO1PEPCO151HPHPFPBO1R^P0P5POP0P5PHP91d59R_f<R`/c4Ran10110000021010100P0PNPOf=RbP`g0109:081KRc9X1DRdPFC<B07589,dNRe%bNRfn10110000021010400Pfn10110000021010100P0P5POP0P5PHP=P4O1P_Pan10110000021010100RaP0PNPOPbf;RgPdPFC<PePfn10110000021010400Pfn10110000021010100Rh51OXHHPOPgPFAX1BcRiPDC<P0P5POPaP0PNPOP8PePfn10110000021010400Pfn10110000021010100=1OhXHOP0P5POP0P5PHP^P_1cgBn10110000021010100P0PNPOP`P=AX14cPEC<PePfn10110000021010400Pfn10110000021010100,JOPgP=PiPDC<P4Pi1>9EPG121DRi=:1KPb1219Rf%375:1ReO1P`PeO151HXBG&06D%6i%Z<Re%Z2R2+04Rc,5i'L121E/0KRi002c15ic1Gci+01P6121F/0KR6/5c1Gc6f?R6121=/0KRi,81,21%3C5:1RNO1f>R0PNO151HP915ic121gRN/0KR_fAR^%34R59:19RhO1f@RaPhO151HX0:%DBRh#3Rj,0NRk10_]Rl'4Rm10]KRn,0NRo/4lP:P:&00:RpP9X@:RqPp1489#}XR:X@:S01PkPoPqPqPqP:P:g010U1089Cz#7XO:X::S02PNPN%7NPjPnPqPq%39#7X@;S03PhPnPRPBP]%7]RnCKE[M:_PlPl%7lM<P1>Bb%3bRl,5]RhPBP]PnPbPl%7lENPCCVRnPh%B4R]%65Rj%B6RN%36Ro#6Rk1ye2Rr15>e%6215>c[[Rs%6eRtg0119RuAxe28UWDR2%6c\u^DtRtPSPLP:1]:7P8%v:CuRuPU1`:<R</FYRY,F?1FZ<'U,9VPAP\b4b6b7X1:X8:109[10Q8'4^1:^8:P9%3gRv121^RwO2b3b=b>b?b9b<CMPmP:121`Rm%D4Rx#3'0RyfBRzPJO1P^PJO151HX0:PgPx%D0R{,>x105KR|%30R}/0KR~'5PxP|PRP4P5%75R|CKP{P~PRP0P}%7}R~CKEN1>40155}R{P4P5P|P0P}P~ENPBCVS04P{%BDS05%3DR~#6S06%BaS07%3a#6R}PrPsP2PtPSPLPuPUPV1E?<,9VP@1EZY,9VC?PAP\b4b6b7X1:X8:1598107KR|,5[[^1:^8:P9fDRx#3%3`PBO3b3b=b>b?b9b<CMO2R`10mKRm/05P9ECb2181_R5,21PnPhP]PjPNPkPrPsP2Ptp-0RkPSPLPTPUPV1T:e=s:1Re,EZ,9VRNP@PV1\V3Rj9SVXP@1RWZ,9V=SVNC?C?PAP\b4b6b7X1:W515Qc%68/L7%6|15|c'L[[^1:^5kP915wcPwP4PFO4b3b=b>b?b9b<,q_D;WKP9O11Gcig011URi%@9R_%@8RwQ00%@7?18912371238'4RN[12781279'4%@3?178[RW%@C?137\NAt789P9n2001000000120000000WGWFW:RNPW^Gw^F_^:iRiP9P1181>R_181mRw1A1>RW121bRb/0KRX,81,21,49X0:1A1mR]14W9X0:1=>cRh1A1X,49X0:1=mc14h9X0:Q04P{Q05Q06Q07P}PrPsP2PtPSPLPTPUPV1ReZ,9VP@PV1E?e,9V9SVjP@1UeZ,9VC?C?PAP\b4b6b7X1:X5k1GcQ158c,L714c|[[^1:^5kP9121zRQ#6PQPDP=O4b3b=b>b?b9b<14cmP:Pc1=9c,4hX0:1=ccRh#7PXP9ECb2P]%OmD;PW%O>D;121w1Q1mD;121_1Q1>D;O4b2A1G_5PGP_PzA:1f~RfO1P^PfO151HXBGP`P^181yRyO1PaPyO151H10c~Ry%DDRa#3R`,0bRf'4R_10~KRK,0bR5,4yP:P:PpPqPpQ01PyPy%7yPfP5PqPqPqQ02PbPb%7bP`PKPqPqQ03PaPKPRPDP~%7~RRCKE[M:_M<P1>D615~oRKPDP~PRP6Po%7oENP4CVPK%BE%3ERK#6%B^%3^#6PrPsP2PtPSPLPuPUPV1ReY,9VP@PV1\VC1E<e,9V5SVP@1Fe?1F<Z'U,9VC?C?PAP\b4b6b7X1:X8:X5k1Gc[157c,L310c7103|'4[[^1:^8:^5kP9fCRk,21R|#6P|PlPEPgO5b3b=b>b?b9b<CMP_1210%DE#3'0PxPJO1PkPJO151HX0:P810cKRKP9D;Pk181KRKO1PzPKO151HPNPiP9P1%3=Ri,0>RN,81RK10ciRz,81Rk1A1NRJ10cvRE,81,21,49X0:1A1zR010>vR_,A1/49X0:1=NcRg1A1E,49X0:1=zcRE1=_cR_/49X0:RlP:10hi/=cPlP:P>109v/=c,4_X0:%7gPh%ocEIPEAncicECP0%OzD;PJ%OND;121k1Q1zD;121K1Q1ND;O4b2%3FRF9:1>A:1cF51GPGPkfFP9O1fERkP9O151HXBGP8PKP9EIPkPKO1PxPKO151HP9b;b2b;b2b;PwP9ECb2WIP9O1n200110200021110311103bPbDPd%{DEIWJXC;O2EIP=PBO1P9EIbAbAbAbAPDP4P8PMC<PDPBP8PMC<51OeW;XEGXLPX:;P9C|X:;XNIWMWQo"). Qed.
End VP4.

(* [comment removed for export] *)
Section VP5. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma rdn_untouched : forall segs M (a : Z) n,
  (0 <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z ->
  (forall i, (a <= i < a + Z.of_nat n)%Z -> M (Z_to_bv 64 i) = None) ->
  rdn segs M (Z_to_bv 64 a) n = rdn segs (fun _ => None) (Z_to_bv 64 a) n.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP5"] "h04__x1h14__x2h24__x3h32Hah43Hj0h57__arithh64__ffh76__sat1h86__sat2h98__varmaph:5__with;4cstrh<5cstr0h=2H0h>2Hjh?5Hnoneh@3HnwhA1MhB1ahC1ihD1jhE1nhF1ohG4segshH1xhI1zp;1p;2p;3p;4p;6p;<p;7p;8g003Lj1NTg003lj13Tg004Qj1GTg004oj1CTg005Rj1gTg00CQR0j15Tg00F@j24Tg00Ebj1ETg00TNj2QTg00URj27Tg00F]R1j22Tg00A:j2@Tg00O3j28Tg00Jkj1KTg007fj3>Tg00BOR2j2LTg00Dij2=Tg00X4j4ZTg00G9j1HTg00X[j2YTg00YCj3XTg00G^j1WTg00H>j2FTg00ZEj4VTg00H\j1UTg00I:j1TTg00Iej2DTg00JHj2ATg0123j1PTg00dbj3BTg00KMj2OTg00Koj2RTg00L[j3STg00M:j4fTg002nj6MTg00Bgj2eTg00ECj1<Tg012Xj2;Tg013Aj3?Tg013jj2dTg00S0j3cTg00Zcj3`Tg00[Fj2^Tg014Vj6]Tg00WOl<_Tg00cSj4JTg00d>j7\Tg00g3j7aTg00eEj8bTg00iZR3f0R4'7p=0g00?_R5g00gWR6P2P0P1g00hYf5R1f4R0f3R2f2R7f1R8P4M<_p=[P6P8g00j8P4CJp=9P8g00j_R9g00k>R:P:g00k^R;P4g00l>F\p=1P6P8g00l^P4CJp=:P7P9P:P:P;P8P4Fap=IP2P9P:P:P;P7P8P4Gbp=6g00;h#Ng00=oR9#3R<#3#3R=#3#3#3R>#GR?#CR@%G=#CR=#gRA]H%08RB%58RC,47%E<RD%E>R>'QRE'71704%52,40,24'@f6RF18?8O1%K=R=5>A[^C6PFP1P=V@P218?01L40P6PFf8%57R@,44,8?O1=>A=XI6PAP=A>A4=XFA1=A=f7R=14FCRA,8?O1P7PA1L81%51RA,2CRGP8PC1=6CP1PA1=6AE[P4CZRAPG%H7RC%0@R@%H=RH%5=R=#0RI1YD>RJ123D%0>123E[[RK%0DRLg0119RMAXD>8UW3R>%0E\M^3LRLg00mlRM#WRN%NMROP61F67P81F62CVRP%U6RQ%T6RR1D63RS1A6<R<'9,1R%K:R:PR%P9,A6RT,:<,1RP:1A69R9AB69<RU'9,1RAB69T,:U,1R5IRC6C61OR;R;P4P7g00nXRVg00o8RW'=1R47=>VWdAS638CfR8b6b9b:X06X16X2612721472R3,771470,23'@[\B^06^16^26P4f;#5RBP=f<RWP0P1O5b5b7b8b<b;b4O2EM18?F,e?PAPGPCP@PHPIPJPKP>PLg00i;RL#<#<R>#<RK#<,;61;6K1;6>1;6L5?65?65?6g015_'d=cMNPOPPPQPR19ST,1RP:PR1:T<,1RP:PR1D6D=`6?R?,9U,1RP:PR19S9,1RRSP:1:9?,1R9IRSC6C6C6C6P;P8b6b9b:X06X16X26%071227173E%02%00120E'@[[[[^06^16^26P4P=PBPWP0P1f9f:O7b5b7b8b<b;b4,^FEMW>XD5E]W?W@W=XE5XB6WAWGo"). Qed.
End VP5.

Section VP6. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma kimg_rdn : forall segs E M kn i lo hi (a : Z) n,
  know_ok segs E M kn -> nth_error kn i = Some (KImg lo hi) ->
  (lo <= a)%Z -> (a + Z.of_nat n <= hi)%Z ->
  rdn segs M (Z_to_bv 64 a) n = rdn segs (fun _ => None) (Z_to_bv 64 a) n.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP6"] "h04__x1h14__x2h21ih34__x3h47__arithh54__ffh67__sat65h77__sat66h88__varmaph95__with:4cstrh;1Hh<2Hah=4__x4h>4__x5h?1Eh@2H0hA3H64hB2HKhC3HhihD2HjhE3HlohF2HnhG5HnonehH1MhI1ahJ2hihK1jhL2knhM2lohN1nhO4segsp;1p;4p;3p;2p;8p;7g003Lj1>Tg003lj17Tg004Qj1KTg004oj1HTg005Rj1FTg0064j4]Tg002Pj3ZTg016Kj2ITg007Dj2XTg007fj35Tg00URj20Tg00CQj18Tg00F@j29Tg017Vj8iTg008@j4fTg00Ebj1OTg00TNj2\Tg00F]j23Tg00O3j2DTg00Jkj1MTg00D1j4@Tg00G9j1JTg00X[j2YTg00YCj3WTg00ECj1?Tg012Xj2=Tg013Aj3<Tg013jj2CTg00G^j1VTg00S0j3BTg00H>j2ATg00Ygj1UTg00H\j1TTg00I:j1STg00Iej2GTg00JHj2;Tg00KMj2hTg00Dij2gTg00Koj2eTg00L[j3cTg00M:j4bTg00Zcj3^Tg00dbj3PTg0123j1LTg00cSj4ETg018^j7_Tg00A:R0j2`Tg00ZEj4aTg00d>j7RTg00eEj8[Tg00g3j7dTg00iZR1f0R2'0p=2f2R3f1R4'0/`2p=4g00gWR5P3P4P2Cap=:P3g00j_R6g00k>R7P7g00k^R8P5P4g00j8P2CEg00l>R9FRp=1f3R:P6P7P7P8P3P4P2G[p=6P4P6P7P7P8P2P9FRp=QP3P6P7P7P8P4P2Fdp=Ng00;h#>g00<gg00=oR6#7R9#7R;#7R<#7#7#7R=#KR>#HR?%K<#HR<#FR@[g00>TRA#>g00?_RBf8RCf7RDf6REf5RFC]%FAAZAEFf4RG/I:,XA3510F:%8:,9G/0Ff<RAf;RHf:RIf9RJPC1IDERKP:P3GiPAPHPIPKCfP0%2C%O9RK%O=R='\RL132C94J2f=RC1D>4RMO1%M<RN55@[^2554D%><#FR<f>ROPA1D>DRDPEC@POPNV?R?PDPEC@35P2%2I132H94A2f@REPMO1=5@N[^2594ILP010HL132A94C2fARAPMO1=5@N[^25fBR0PE1D>HRHPIC@P0P?PHPIC@55<P210CLf?R<,3294E2fDRIPMO1=5@N[^25fERNfCR@POPC%JCRM%8C#2RH1YK=R?131K%2=131L[[RD%2KRPg0119RQAWK=4UW<R=%2L\Q^<PRPg00mlRQg00i;RR#?RS#?RT,=5RU1=5S1=5RRR5<5RS5<5g015_RV'C%VQRW3BRX%>QRY1A53%U5RZ7:4%T5R[%S5R\1G51R]1;59R^51\%M7R7P\1;56R_91\^P7A1\]_C6C61h\8R8P2P3g00nXR]g00o8R`'g1e23=5]`dAc514CbR1b5b8b9X05X15%241034%23[[^05^15P2PIP0PJPOO4b4b6b7b:PMPHP?PDP=PPPXPY1A5:?:3Z?:4ZP[P\1;5;R;1G5K=^5>R>51\P7P\AP5_^RK=1\;P7A1\K>C6C6P8P1b5b8b9X05X15X35103L1943/0:193:/0L[[^05^15^35P2P@%8AP0PFPCO5b4b6b7b:%8O,9<,3294<2P3P4%J<%8<#2P?PDP=PP%?TRT,=5A<5UR5<5/CV%?T,=5=<5S/CV=BQW5BQPY1A5G?:3Z1A5F?::Z7:4P[P\A1\;^P5P^g00l^R[%L9,;59P5;R9CE,Q\5N\P7P\%L6,;5R691\9P7P\A1\_;P7A1\_^P5P^P[P6CE,Q\5N\C6C6C6P8P1b5b8b9X05X15X35X=5X>519:G,3494:419GF/0:103F13GF94:G[[[^05^15^35^=5^>5P2%8@PIPNPFfFPGP<PEO8b4b6b7b:O2WDXK5F_WGWAP4P2O2n2001000000121000000W;W@P4P2O2n2001000000121000000b;WCWEWFWBXNBXI5XJ5XM5W2WLWHW?WOo"). Qed.
End VP6.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section VP7. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma kwr_store_ok : forall segs E M kn i b kk len (k : Z) (m : nat),
  know_ok segs E M kn -> nth_error kn i = Some (KWr (SA b kk) len) ->
  (kk <= k)%Z -> (k + Z.of_nat m <= kk + len)%Z ->
  store_ok segs M (adenot E (SA b k)) m = true.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP7"] "h04__x1h14__x2h21Hh34__x3h43Hsth57__arithh64__ffh76__sat5h86__sat6h98__varmaph:5__with;4cstrh<1mh=2Hah>4__x4h?1dh@1EhA2F1hB2F2hC2F3hD2F4hE2H1hF2H2hG2HKhH3HflhI2HnhJ1MhK1bhL1ihM1khN2kkhO2knhP3lenhQ4segshR1zp;1p;4p;3p;2p;8p;6p;7g003Lj1GTg003lj1:Tg004Qj1MTg004oj1HTg005Rj1RTg0064j4dTg002Pj3]Tg019kj26Tg01;5j2JTg007Dj2YTg007fj3@Tg00URj27Tg00CQj1=Tg00F@j20Tg017Vj8lTg008@j4cTg01<@j3OTg00O3j2>Tg01=Mj2LTg00Ebj1KTg00TNj2ZTg00F]j29Tg00A:R0j2;Tg01>Vj23Tg01?_j28Tg01@Zj2BTg00G9j1ITg00X[j2XTg00YCj3WTg00G^j1VTg00H>j2FTg00Ygj1UTg00ZEj4ATg00H\j1TTg00I:j1STg00JHj2DTg00Jkj1nTg00Iej2mTg01A7j3PTg00KMj2kTg00Dij2jTg00Koj2hTg00L[j3aTg00M:j4`Tg0123j1_Tg00dbj3?Tg00Bgj2CTg00cSj4QTg002nj6^Tg01AZj1eTg01Bcj1\Tg01Ckj2fTg01E:j4gTg00d>j7[Tg00eEj8iTf2R1f1R2'0f0R3'7p=4g00iZR4/73p=11623,f1p=5g00nXR5f3R6P1P2P3Cgg00o8R73@p=2g00gWR8P2g00j8P3CQp=EP2g00j_R9g00k>R:P:g00k^R;P3g00l>F[p=<P6P9P:P:P;P1P2P3Gip=NA@537p=bg00;h#Gg00<gg00=oR9#:R<#:R=#:R>#:#:#:R?#MR@#H%M>#H#R[g00>TR>#Gg00?_RAg01F:f9RBf8RCf7RDf6RECd%R>A]>DEf5RFf4RG'6/J6,Y>3@17F6%=610EF54Gf=RFf<R>f;RHf:RIPB16CD/JERJP6P1GlPFP>PHPJCcP016BC=OFD%12RC%=2,01RJ/7IfBRKf@RLfARM?5F>RN/06,>@P1C2[[^<A^?8f?ROPFf>RP16ID'LPEC2P316HI=OOB17JFfERJfCREfDRD?5LORQ/06,>@P1C2[\C^<A^?8P0%1N%K<RC%K?R?'ZRR,9N%1HA4NHR';';PEPM13KP/8HPIC2P2A5EOP#119QR%1PA4QPR';';P0A5JMLRQ/9R%1OA4QOR';fGRQPJfFRH/3K/8OPPC2P3A5QEK/9R%1KfHRP?5DE?4KR';P0%1EfIR0?5JD?4ERfKRDP0fJRO/3H/8EPKC2P3%1JfLRE?5PQ?4HRP>1BHPR>PJ%IJRN%=J#1RS1XC?RT194C%1?194R[[RU%1CRVg0119RWAWC?2UW=R?%1R\W^=VRVg00mlRW#VRR%GWRWP81F81RCP2%U8RXCA%T8RY%S8RZ1D8<R<1D89R['E,<Z%n:R:1m84AP8[<R\'E,<ZCN1kZ;R;P3P11j571h31#bdAa842C`R4b6b9b:X08X1817231B21R7#1[^08^18P3PEPOPHO3b5b7b8b;PNPSPTPUP?PVPRPWP8P81F8GP1PXCAP21F86RXCAPYPZ%_9,D8R99?8[RS1D8=R=9?8<'E,<ZP:A?8\9/E=,<ZCNP;P4b6b9b:X08X18X38X>81031R11026'7A476G[^08^18^38^>8P3PD%=0PEPOPJO5b5b7b8b;O4fNRGPEfMR6/30R=,C@/0P/0>,>@PJC2%IH%=H#1PTPUP?PVPRPWP8PCP2PXCAPYP8A?8[<g00mEAP8<99?8SCQ,<ZP;P4b6b9b:X08X18X38103210175@8^08^18^38P3P6PDfR/3G,C@O3b5b7b8b;13GO,C@R6/0Q10601BQ0'05@8P8fOR6/3D,C@RD/0O1BPO'0fQROP61>@3PPC2XR8P210DPRDP3E^fPR1PG1>@DPQC2P3POP6131E/80PPC2eb4b2b4PGPE18=HPJC2RJePJeWDWCP2P3O2n2001000000121000000W2WBP2P3O2n2001000000121000000W2WAP2P3O2n2001000000121000000PKPL16FIRI#e,3M%\I'8PBC2ePKPL1LMIPBC2eW4WHP2P3O2n2001000000121000000b2WFWEWIWGX<AXM8XP8XN8WKWLWOWJW@WQo"). Qed.
End VP7.

(* [comment removed for export] *)
Section VP8. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma kwr_store_ok_lit : forall segs E M kn i kk len (k : Z) (m : nat),
  know_ok segs E M kn -> nth_error kn i = Some (KWr (SA (ELit 0) kk) len) ->
  (kk <= k)%Z -> (k + Z.of_nat m <= kk + len)%Z -> (0 <= k < 2 ^ 64)%Z ->
  store_ok segs M (Z_to_bv 64 k) m = true.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP8"] "h01Hh11Eh22H1h32H2h42HKh52Hkh62Hnh71Mh81ih91kh:2kkh;2knh<3lenh=1mh>4segsh?1zp;1p;4p;3p;2p;>p;6g003Lj1:Tg003lj10Tg004Qj18Tg004oj15Tg005Rj1<Tg0064j4HTg002Pj3DTg01GCj1ATg019kj27Tg01;5j2>Tg007Dj2=Tg007fj39Tg00URj24Tg00CQj1ITg00F@j23Tg00Ebj1;Tg00TNj2GTg00F]j2FTg00A:j2ETg01HLl>CTg01=Mj2BTg01E:j42Tg00O3j26Tg01IXj1@Tg00NWj6?Tg00nXf0R0g00o839p=1g00;h#:g00<gg00=o#0R1#0#0R2#0#0#0R3#8R4#5%82#5#<[g00>TR2#:g00?_R5g00gWR6f8R7f7R8f6R9f5R:CH%<2AD29:g00iZR;#AR<f4R='7f3R>'>,=23914:>%I>,3=139:'414;:%;1%;3'G,F:'Ef=R3f<R1f;R2f:f9P<P7P8P9P:P=P>f2f1M>CP3P217<9,B1P:C2#1P613;8f?P31640P8C2#1X?6P0P8%@8E?f>P11648P9C2#1P0b0b0W5W3W2W6W4X=5X96X<6W:W8W;W7W1W>o"). Qed.
End VP8.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition entry_below_b (spi : nat) (ihi : Z) (e : sentry) : bool :=
  match e with
  | SE (SA (EVar i) k) w _ => Nat.eqb i spi && Z.leb (k + Z.of_nat w) 0 && Z.leb (- 2 ^ 40) k
  | SE (SA (ELit 0) k) w _ => Z.leb 0 k && Z.leb (k + Z.of_nat w) ihi
  | _ => false
  end.

Definition log_below_b (spi : nat) (ihi : Z) (log : list sentry) : bool :=
  forallb (entry_below_b spi ihi) log.

Section VP9. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma entry_below_sound : forall E spi ihi b k w v (x : word),
  entry_below_b spi ihi (SE (SA b k) w v) = true ->
  (2 ^ 40 <= bv_unsigned (ev E spi))%Z ->
  (bv_unsigned (ev E spi) <= bv_unsigned x)%Z -> (ihi <= bv_unsigned x)%Z ->
  (bv_unsigned (adenot E (SA b k)) + Z.of_nat w <= bv_unsigned x)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP9"] "p'0h02Heh11Hh24__x1h34__x2h44__x3h54__x4h63He1h71ni001nh82Hah93He2h:7__arithh;4__ffh<4__p1h=6__sat4h>6__sat5h?6__sat6h@8__varmaphA5__withB2b1hC2b2hD4cstrhE1mhF2opi012ophG1zi021zhH1ii031ihI3He3hJ6__sat3hK6__sat7hL1bi041bhM1pi051phN2sxi062sxhO1EhP2H0hQ2HshR3HsphS3Hx1hT3Hx2hU3HxrhV1ei071ehW3ihihX1ki081khY2k0hZ2loi092loh[3spih\1vh]1wh^1xi0:1ap%0p&0p;1p;2p;3p;4p;6p;7p;8g003lj1:Tg004Qj1pTg004ok105Tg00Ebj1TTg0123j1oTg00TNj2hTg01J9j2ITg00Bgj21Tg00SPj1\Tg00F]j2<Tg00A:R0j2>Tg00CQj12Tg01GCj1HTg01K>j2BTg00F@j23Tg01K[j2JTg01L9j3XTg00URj20Tg01L\k201Tg00G9j1dTg00X[j2eTg00YCj3gTg00ECj1DTg012Xj2[Tg013jj2MTg00G^j1sTg00S0j3LTg003Lj1rTg00H>j2VTg00Ygj1qTg00ZEj4UTg00H\k10ATg00I:k10@Tg00JHj2KTg00Jkk10?Tg00dbj3ZTg00KMk20>Tg00Dik20=Tg00Kok20<Tg00L[k30;Tg00M:k40:Tg00Iej2kTg00fOk609Tg00Zcj3jTg00[Fj2fTg002nj6RTg01IXk107Tg007fj39Tg00NWk604Tg01M<k203Tg01M[k102Tg01N9j1OTg01OBj2?Tg01Obk100Tg01P?j2~Tg01Pbj2{Tg01QEj3bTg01RNj3`Tg01SWj3aTg01T`j3]Tg01Uij4_Tg01W2j4^Tg019kj2cTg01AZj1zTg01Bcj1yTg01=Mj2xTg01X;k306Tg01YFj3wTg01>Vj2iTg00O3j2STg013Aj3vTg00cSj4lTg00d>j7nTg00eEj8YTg00g3j7uTg01ZSj2tTg00nXR1f5R2f4R3f3R4f2R5'cf1R6f0R74063wg00o8R839p=71167,05p=Wg00iZR9/07p=5f7R:f6R;1i34,12/35'S'1/36/07p=8A9178p=41B67=918p=A1S45,13/36/07p=|1356/07p=Fg00gWR</[7p=GAv<67p=;P5g00j_R=g00k>R>P>g00k^R?P<P6g00j8P7Clg00l>R@Fnp=6P;P=P>P>P?P2P3P4P=P>P>P?P5P6P7GYGYp=C1S67,15p=mP<P6g00l^P7Clp=QP6P=P>P>P?P7P@Fnp=PP5P=P>P>P?P6P7Fup=NP4P=P>P>P?P5P6P7GYp>081i45,13/36,S2,1;/37p=@g01[41t67g01[Z39p==1B79p=E1156/37p=}g00<gg00?_R@g01F:RAg00=oRB#:RC#:RD#:#:#:#:RE#pRF$05P;P2P3P4P5P6E7%TCRG%oCRH#:#:#:S00#TRI'hRJf8RK/I:7WFf9RL/IK,1F?WF5AWKF4%\311F3RM#5%TERE,hGRN,<M'>PAf<ROf;RPP7PLPKP:E7PFPFPFf>RQP6f:RR%2L11F:G8]0PLf=RSPO%H7PRPLPKE7P<P<P1P71B9ORT%2P,3OS01/BQRU'Jg01\@RVPVn011020003001010510105#4PFPFPFfARW%H6PS%2ORX11FRS02G8]0P61B9P%2R,3PS03/BS'J#4AXTU7%4T%4U'>P01A9S13SXf?RU'APFPFPFfBRT%H9S04PQ%2SRY11FPRZG8P71A9Uf@R[%2U'3S05/ATP01A671056[R\10671A56R][1045R^\]20167P6n2001000000120000000XE<X7<R]P\^E<^7<R\P7P9PTP5O3%5TP]P\P7fDR_fCR`#2'3RafFRbP4O310abP<fERcPFPFP7%2cRd11F`ReD|XG<P<PcAF7deXG<%d_Re%2_S06#5Rd1eGIRf1<9GRg%5I1<9J[[Rh%5GRig0119RjAgGI6UW8RI%5J\j^8iRk1eGERl%5E1<9N[\gRgAgGE6VjX8iRE%5N\j^8iRig00mlRmg00i;Rn#DRo#DRp#GRq%Go1[<nRn';S07';g015_Ro'M%smRr3LS08%rmRsP<P<1V<3S09P5%q<S0:CUP61V<4CUS0;&0A<Rt&0@<Ru1K<DRD%oB,K<Rv56u&0?>RwPu1K<BRB1K<CRC5Z<Rx=6uDPwA6uxvS0<FC20>u?RyP7P520=1820<75#4dB0;<96H0:Rzb;b@bAX2<X3<X4<X5<AF6531354R{/03[\^^2<^3<^4<^5<P7fMS0=fHR^,1FR|fJR}#2S0>fKR~P_P;O6b:bJb=b>b?bDAmFFcPePdPfPhPIPkPlPgPEPip-0Rd%DpRp#DRe#DS0?#GS0@%GeS0A%Gp1;qn';Rn';';/Mo=LmrPsP<1V<5P6P<Q09P4Q0:CUCUPtPu1k<9Rq=6uCPwPuPuP=P>P>P?P;J09R?1K<HRH1k<GRG=j<FR>'Q,Pu5NuPwPuA6uvHPwPuQ0<PwPuA6uqBRHPw1QB>,Pu9NuHH08FCFCPyPzb;b@bAX2<X3<X4<X5<W<%561<3N,>2S0<1032AF432%53%521<2N'>[[[[[^2<^3<^4<^5<^<dP7%5|P|Q0=Q0>P~P2P`P_P;PKO:b:bJb=b>b?bD,fcER139c&07cERPFPFPFfIRHQ04PcQ0611FTG8eb9b1b6b1W9W6P6P7O2n2001000000121000000b0W0g01\`R=A91V8RpPFPFPFPT%T6#HPQPYF@Re/=ZP1PVP1PdP7g01]ERVPjn0110400020000XV1g0109P8P6J04PV203V7bPRVW110eZeW0WMP7O1PFPFPFPT&026#HPQPYF@Re/=ZPVW110eZeX0pXM=P7O1n011020003011010510105P7O1W0XG<P7O1PSPO%O7R=PRPLPKE71?6QQ03#E'JRp&00JRe/BPRZ;X7%4p%4Z'>P01?5UQ01#E'J#41AeOPFPFPFPW%O4PSPXQ02G8P71?3W13QY#E'J#41AeU1?;`RYQ05#ERX;X6%4Y%4X'>P01?:_#4%2[R_,3W#E#4PFPFPFPb%OKPT%2W11FUG8P71?Lb#4%Ea#4P01?67#4A9@56[R0A9@671?56#4Ra[A9@45\a1~67P6n2001000000120000000XE@X7@P0^E@^7@P7POPHP5O3A9@OHP@P}PFPFPFfLRHP=P^fG#2R=11FcG8XH@P]P\P713^=R=P9P4O310=9P]P\P7PeP}PRO310e}fORRfNR\'IR]#\11F]R]#51<]N'>P<fP/IR=}FHR]%2H11F}5F7XG<%d~R=%2~#5R^PfPhPIPkPlPgPEPiQ08PsQ0;PtPuA6uBDR0PwPuAZ<Cv=6uqRaPwAZ<xv=6uDFCPyPzb;b@bAX2<X3<X4<X5<107410{9AF{32[[^2<^3<^4<^5<P711FRR{fQ#2RbfRRXfVfU'I,1FRYPHPLO6b:b=b>b?bKbDAmFF]P=P^PfPhPIPkPlPgPEPi1MnoQ0?#D#GQ0@Q0AQ07';';';/Mo=Lmr5LmPsQ0;PtPuA6uqvPwPu1QD>,Pu9Nu?PwPuP0PwPuQ00#p9j<GRG=6uBPwPu1{<G=6uCPwPuPaPwA6uqx1Qx>,Pu5NuFCFCFCPyPzb;b@bAX2<X3<X4<X5<X<d%55Q0<105210J410e213;:Re/09%5e1<eN'>[[[[[[^2<^3<^4<^5<^<dP7%5{P{PbPXPYP2P}PHQ0=P:PLO;b:b=b>b?bKbD,f]ERbQPFPFPFPR%O\P~Q0>P|G8ebIb1b9b1PSP7ERb6b1W9W6P6P7O2n2001000000121000000b6WIW6P6P7O2n2001000000121000000b0W0XH@P7O1g01]bR|PWP[Ab567PQPSPOE7PFPFPFP`Ab456PU%2QR~F@R\11FORR'=PVW110\ReW0XCAXBAWFP5P6P7O3PWP[A`567PQPSPOE7PFPFPFP`A`456PUP~F@R\/=RPVW110\ReW0XCAXBAXF|P5P6P7O3g01^NR|PWP[Aa567PQPSPOE7PFPFPFP`Aa456PUP~F@R\/=RPVW110\ReW0XCAXBAWFP5P6P7O3PWP[A]567PQPSPOE7PFPFPFP`A]456PUP~F@R~/=RPVW110~ReW0XCAXBAXF|P5P6P7O3P`PTP4P5P6P7C_P[PUPQE7PFPFPFPcP3P4P5P6C_PWP_F@R|11FQR~'=PVW110|~eW0XLAX7@XZ@XN1P4P5P6P7O4P`PTP4P5P6P7C^P[PUPQE7PFPFPFPcP3P4P5P6C^PWP_F@R_/=~PVW110_~eW0X7@XH<XY@XN1P4P5P6P7O4n01107000811102111003010110:1043010110:1043010110:1043010110:1044010610910010740106108103100P3O1bUPFPFPFPP1cK:RK#z%yK%2;R;PMG8e1xPK,1F?F;MeWTWSWRW0W^X\AX]@XX<WLXW<W[WOo"). Qed.
End VP9.

Section VP10. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma mem_denot_above : forall E M log spi ihi (x : word),
  log_below_b spi ihi log = true ->
  (2 ^ 40 <= bv_unsigned (ev E spi))%Z ->
  (bv_unsigned (ev E spi) <= bv_unsigned x)%Z -> (ihi <= bv_unsigned x)%Z ->
  mem_denot E M log x = M x.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP10"] "p'0h02Hbh12Hah24__x1h34__x2h44__x3h57__arithh64__ffh74__p1h86__sat3h96__sat4h:6__sat5h;6__sat6h<8__varmaph=5__with>4cstrh?1lh@3loghA1nhB1EhC4HbndhD2HehE5HresthF3HsphG3Hx1hH3Hx2hI3HxrhJ2IHhK1MhL1ahM1bhN7e_addr0hO5e_vali005e_valhP7e_widthi017e_widthhQ3ihihR1khS1ohT4resthU3spihV1vhW1whX1xi026a_basei035a_offi046e_addri051sp;1p;2p;3p;<p;4p;6p;7p;8g003lj14Tg004Qj1UTg004oj1PTg005Rj1`Tg003Lj1VTg00Ebj1FTg0123j1RTg00TNj2OTg01J9j2NTg00Bgj20Tg00URj21Tg00G^j1ZTg00Dij2WTg01X;j35Tg019kj23Tg01YFj3Gj2DTg01_:j3CTg01L9j3fTg00A:R0j2JTg01_Vl<bTg01=Mj2>Tg00CQj1?Tg00F@j2;Tg00SPj1aTg00F]j28Tg01`gj4Mj3_Tg007fj3<Tg01>Vj2^Tg01b9j2]Tg01cAj4\Tg00G9j1[Tg00X[j2KTg00YCj3TTg00ECj1YTg012Xj2ITg013Aj3XTg013jj2zTg00S0j3LTg00H>j2STg00Ygj1yTg00ZEj4ATg00H\j1xTg00I:j1sTg00fOj6rTg00JHj2=Tg00Iej2qTg00Zcj3pTg00cSj4QTg00g3j7oTg00Jkj1nTg00dbj3hTg00KMj2gTg00Koj2iTg00L[j3jTg00M:j4kTg01d;j2lTg01d[j2mTg002nj6BTg01ecj2eTg01f=j3dTg01fWj6cTg01gZj6tTg01h<j3uTg00d>j7vTg00eEj8wTg00nXR1f2R2f1R3f0R43ug00o8R53<p=2f5R6f4R7f3R8P2P3CM;<4p=7g01iGR9?L34p=:A<145p=9g00iZR:/14p=6P3g00j_R;g00k>R<P<g00k^R=P4g00l>Fvp=@g00gWR>P3g00j8P4CQp=HP8P;P<P<P=P2P3P4Gwp=Eg00<gg00=oR?#4R@#4RA#4RB#4#4#4RC#URD#PRE%UB#PRB#`RF[%V9RGg00?_RHA2238%F@RI%R@#4#4#4#FRJ'ORKf6RL/N8,0D'1f7RM/N7,0D10D2'110D8,17P9A2ML4PFf;RNf:ROP3PLPOPLO1E7]0X@G%Z992L6f9RPP6O1,WFW0P9f8RQ=2P4PFf=RRf<RSP3PQPSPQO1E7]01:2392OPPFf>RTPR1:82PPPRPPO1E7]0[^?GP4g01jRRUPUg01F:RUf?RV?2T4PFfCRWfBRXP3PTPXPTO1E7]0f@A5782/:372VPFfDRYPWA5678/:2PVPWPVO1E7]0[^?G]O^PHP4fARV=2X4PFfFRZfER[P3PVP[PVO1E7]01367?582/:392WX13L6?5789GYWR\1DYW=C92R];f4%9\%9]'JP013ML?5679G[Y#91D[Y=C98#9PFfIR0fHR]13QM?5L6/:7PYP]PYO1E7P4fGR713PQ?5ML7GZ#91D]7=C9L#9fLRZP0P]PNPOPPPQP7P3P[PYPWM<b13NO,>Z,0D%?P';10D7'1%a]10D]R]#6%FCRC,OIR7,8]'JPFfNR]fMRZPPP0CMP]fJRYO19<F4XSFPQP2O1A_]ZPRQ13RSRS,>]R[1^]OR\,]NR^P0C\P^PQP[P0PHPNfORQ13TR'>,0DRT%?4';RR/17XAH%[NR_%?NR`#6Ra1KIJRb18:IRc%6J18:K[[Rd%6IReg0119RfATIJ3UW1RJ%6K\f^1eRK1KICRg%6C18:7[\cRcATIC3VfX1eRC%67\f^1eRep-0Rfg00mlRhg00i;Ri#YRj#Y,I>1I>j1I>i5X>5X>g015_'z%ZhRi3L%VhRhP>P>1S>8RjP2%y>RkCAP3PkCA%x>Rk%s>RlPlP;P<P<P=PlP;P<P<P=P6ErP>1=>ARAg00l^1q>I=p>DRICQ,@lFo%n<R<Pl1=>?1=>@5h>R@/HA,@lP<1H@I,@lCECE1gl=R=P4P21W151i42#9dAj>:3CkR:b6b<b=X2>X3>X4>W71827,J81;32/18R51;28/17[[^2>^3>^4>^7fP410DQRQ#6PQ%?VRVfT13WX'>,0DRXPLPMO6b5b8b9b:b;b>1lB^R^1mN\R\EBPHPN10DYRY/8T11RY'eXAH10D0RY10D[R['81;[`/1YP_PaPbPdPJPKPgPcPCPePiPhP>1S>2P3PjCAPkPl%R?,=>,H@,@lRlP<PlCEP=P:b6b<b=X2>X3>X4>1;43/12P5[^2>^3>^4>P4PQPVPXPMO4b5b8b9b:b;b>3dP^P\EBEcEBPFP]PZA5SNO/:PP0PZP0O1E7ebIbCWEWDP3P4O2n2001000000121000000b0W0WJXTGXVUXWHXR>XMUP3P4O2n01105000121102103WNP2P3P4O3n01105000131104101100XL9PMP8EtWHWGWFW0XXEXQ>WUW@WKWBo"). Qed.
End VP10.

Section VP11. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma rdn_mem_denot_above : forall segs E M log spi ihi (a : word) n,
  log_below_b spi ihi log = true ->
  (2 ^ 40 <= bv_unsigned (ev E spi))%Z ->
  (bv_unsigned (ev E spi) <= bv_unsigned a)%Z -> (ihi <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  rdn segs (mem_denot E M log) a n = rdn segs M a n.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP11"] "h02Hah14__x1h24__x2h34__x3h43Hj0h57__arithh66__sat3h76__sat4h86__sat5h96__sat6h:4cstrh;5cstr0h<4__ffh=8__varmaph>5__with?4__x4h@1zhA1EhB1HhC2H1hD2H2hE2HbhF2HjhG3HnwhH3HsphI1MhJ1ahK3ihihL1jhM3loghN1nhO4segshP3spip;1p;3p;2p;4p;7p;6p;:p;<p;8g003Lj1FTg003lj13Tg004Qj1ETg004oj1ITg005Rj1kTg01h<j3_Tg007fj3QTg00Ebj1@Tg0123j1NTg00TNj2JTg01J9j2=Tg00Bgj22Tg00URj20Tg00CQR0j18Tg00F@j29Tg01`gj3gTg00BOR1j2STg00SPj1^Tg00F]R2j26Tg00A:j2PTg00O3j2[Tg00Dij2ATg00X4j4YTg00G9j1MTg00X[j2LTg00YCj3KTg00ECj1:Tg012Xj27Tg013Aj3;Tg013jj2?Tg00G^j1XTg00S0j3BTg00H>j2>Tg00ZEj4CTg00H\j1WTg00I:j1VTg00Iej2HTg00JHj2<Tg00Jkj1jTg00dbj3GTg00KMj2iTg00Koj2hTg00L[j3fTg00M:j4eTg00Ygj1bTg00cSj4DTg00Zcj3TTg00g3j7`Tg00[Fj2aTg002nj6RTg01k\l:]Tg014Vj6cTg00WOl<dTg00d>j7UTg00eEj8\Tg00iZR3f0R4'0p=1g00?_R5g00gWR6P1P0P2g00hYf5R2f4R0f3R1f2R7f1R8P4M<dp=ZP7g00j_R9g00k>R:P:g00k^R;P6P8g00j8P4CDg00l>R<FUp=4P1P9P:P:P;P7P8P4G\p=5P8P9P:P:P;P4P<FUp=Og00;h#Fg00<gg00=oR<#3R=#3#3R>#3#3#3R?#ER@#IRA%E>#I#k[g01iG#Fg00nXR>A_170g00o8RB3Q%@=RC%N=RD#3#3#3RE#@RF'JRGf7RH/=0,2@'0f8RI/=2,2@12@1'012@0,0212@2%80'9%@?R?,JCRJ'0f<RKf;RLf:RMf9RN3gPMP2f6RO1S4O%^I12@IRP#116PJ'Pf>RPf=RQPKPLPM12@N%87RN'9RR,[@RSPHPOP6PRf?/=K,2@/04X@61S7I%8IRT,6NRUP7PN1A6NPIPT1A6TEZP8CYRTPU%M1RI%81#1RN%MMRV%8MRM#1RW1LCFRX163CRY%1F163G[[RZ%1CR[g0119R\AKCF8UW0RF%1G\\^0[R]1LC?R^%1?163J[\YRYAKC?8V\X0[R?%1J\\^0[R[g00mlR\g00i;R_#:R`#:Ra,76176`176_R_5;65;6R`g015_Rb'?%X\Rc3B%F\RdP61>67ReP81>61CC%W6Rf%V6Rg1H63Rh%N<,<6Ri54g%j:RjPg1<6<R<1<6=R=54gPjAG6=i94g<C5C51ig;RkP4P71A>B1h47=Q>BdAf638CeR3b<b=b>X16X26X36RB%1710871910,07[[^16^26^36R>P4PMfA,2@RlfFfC'=,2@RmPOPQO5b5b6b7b8b9b;b:b412@SRSPTPUPIPNPVPWPXPZPFP]P^PYP?P[%:aRa#:Rn,76176a=;6_5;6/?b%:n,76=;6`/?b=B\c5B\PdP6PeP8P61>60P1%b6CCCCPfPgA4gh=PjPgP6P=g00l^Rf1<6DRDCD,OgPjPgAG6<D1H6CRC=T6@R@54gPjPgA4gi<PjPg%EE9T6C=4giPjPgP9P:P:P;AG6<=R=94ghP6P=PfP@CD,OgF`C5C5C5C5C5PkP3b<b=b>X16X26X36X?6%1816701972/0J102110GO192OR2#1162J'P[[[[[^16^26^36^?6P4f@#8PmPMPlPOPHPLPQPPO9b5b6b7b8b9b;b:b4,aRRPERP6PR10L4X@6PTPUPIPNPVPWPXPZPFP]P^PYP?P[PBP>P4PMPlfBPOPKO5b5b6b7b8b9b;b:b4PSPPERM:]bBWFXL5EcWGWDWCWHWEXN5XJAXK6XP5WMWIWAWOo"). Qed.
End VP11.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint esub (f t : expr) (e : expr) : expr :=
  if expr_eqb e f then t else
  match e with
  | EAlu op a b => EAlu op (esub f t a) (esub f t b)
  | EAluw op a b => EAluw op (esub f t a) (esub f t b)
  | EMd op a b => EMd op (esub f t a) (esub f t b)
  | EMdw op a b => EMdw op (esub f t a) (esub f t b)
  | EExt sx lo n a => EExt sx lo n (esub f t a)
  | _ => e
  end.

Section VP12. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma esub_sound : forall E f t e,
  edenot E f = edenot E t -> edenot E (esub f t e) = edenot E e.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP12"] "p'0h02Eqh11bi001bh23Hfth34IHe1h44IHe2h52e1h62e2h71fh82oph91eh:1nh;2sxh<1Eh=3IHeh>1ih?1kh@2lohA1thB1zp;1p;2p;3p;6p;4p;:g003lj1ITg004Qj1OTg004oj1STg01GCj1JTg01lkj22Tg00Dij27Tg01>Vj20Tg01n6j3>Tg007fj31Tg00O3j2WTg01N9j1HTg01J9j2VTg01QEj3<Tg01oJj3KTg020Nj3MTg002nj66Tg01RNj3BTg0216j1FTg021^j3LTg022Fj3:Tg01SWj3;Tg0231j4ATg01T`j38Tg01Uij4?Tg023[j4NTg01W2j4ETg024ej2QTg025jj4PTg0275l:TTg028@j4UTf4R0f3R1f2R2'0f1R3f0R4'031p=Gf6R5f5R6AK012'0103431p=5g00nXR71223;14p=31023=114p=4g00o89174p=9g01F:R8?134p=DP8P0P1P2P3P4E6p=CP01012P3P4CUp=@g01\@9174p==10349112p=Rg00<gg00=o#I#I#I#I#IR9#I#OR:#SR;P1P2P1P3DGP;P6P0P1P4P6P4F5X98g00gWR<%J4R=/20P71774R>%J3?364P7%J1R?f7R@;34P;f9RAP7P8P3P@%J0RBn010000002000010ABRCC4]0P3%J2/25RD#9A>?@41D?@f8REP;f:RFP410FERGC4X78RHP6PBP4DC10A@RB91;CP;PF%J6PGP4D@b2b0W0%=D1W:1,7;10E?R?=1;?eW0n0110000020000P4O1b0b1P;P6P0P1P=P6P=F5eWBg00?_R=%H4R?/20P7P>%H3?364P7%H1RD?3@4P;PAP7P8P3P@%H0RCn010000002000010ACRIC4]0P3%H2/25RJ#9A>D@41DD@PEPHP6PCP4DCA1;IBP;PF%H6PGP4D@b2b0W0%=J1VE1,7;10EDRD=1;DeW0n0110000020000P4O1b0b1P;P6P0P1P?P6P?F5eW:g01]bR?P;P5P6P0P4P5P4F5RDP;PEP@P5P4PEP4F5RJA<013RG/2EP7P>A<602?3A4P7A<@50RIf;RB;34P;f=RCP7P8P3PBf<RH?KB@RKAKHB6RL5<En0100000020000A<E@6RM,0CRNC4]0P3A<561/2FRO#9A>IB41DIBPHP;f>RPP410PHRQC4X78RRPAPMP4DC10CBRM91;NP;PPA<AE5PQP4D@b2b0W0%=OP;10H5RO10CLRN9ME410C@RS10C6RT5MERU51;X1;P;10H0RVAMES4=1;UX1;AM@OV,7;AKBF0RU,0HRWP1E6AKBF5RX,0HRYP6E6P;PHA<@XUPHPIDGeW0n0110000020000P4O1b0b1P;PAPEP@PGPAPGF5eW4X68W3X58W8AB013RG/2EP7P>AB602?3A4P7AB@50RI?3B4P;PCP7P8P3PBABEKLn0100000020000ABE@6RZ,0CR[C4]0P3AB561/2FR\#9A>IB41DIBPHPRPAPZP4DCA1;[MP;PPABAE5PQP4D@b2b0W0%=\P;PO%O9R9%F4R\%FNR[5LE7::%FSRZ%FTR]5LE9:9:R^51;X1;P;PVALEZ\9:9:=1;^X1;%FOR^%FVR_5L@9:9:,7;PWP1E6PYP6E6P;PHAB@XUPHPIDGeW0n0110000020001P4O1b0b1P;PAPEP@PGPAPGF5eX4JX68X3DX58X8?g01^NR?A;013RG/2EP7P>A;602?3A4P7A;@50RI?3B4P;PCP7P8P3PBA;EKLn0100000020000A;E@6R`,0CRaC4]0P3A;561/2FRb#9A>IB41DIBPHPRPAP`P4DCA1;aMP;PPA;AE5PQP4D@b2b0W0%=bP;POP:PEP4PNCAP:PEPSPTCARN51;X1;P;PVP:PEPSP4CA=1;NX1;P:P@POPVCA,7;PWP1E6PYP6E6P;PHA;@XUPHPIDGeW0n0110000020001P4O1b0b1P;PAPEP@PGPAPGF5eX4JX68X3DX58W8A8013RG/2EP7P>A8602?3A4P7A8@50RI?3B4P;PCP7P8P3PBA8EKLn0100000020000A8E@6RK,0CRNC4]0P3A8561/2FRS#9A>IB41DIBPHPRPAPKP4DCA1;NMP;PPA8AE5PQP4D@b2b0W0%=SP;POP9PEP\P[CA9:9:P9PEPZP]CA9:9:R]51;X1;P;PVP9PEPZP\CA9:9:=1;]X1;P9P@P^P_CA9:9:,7;PWP1E6PYP6E6P;PHA8@XUPHPIDGeW0n0110000020001P4O1b0b1P;PAPEP@PGPAPGF5eX4JX68X3DX58X8?P0P1P2P3C?R?/2EP7P>P6P0P1P2C??3A4P7P@P5P6P0C?RD?3B4P;PCP7P8P3PBPEP@P5PLC?n0100000020000PEP@P5P6C?RL,0CRGC4]0P3P5P6P0P1C?/2FRI#9A>DB41DDBPHPRPAPLP4DCA1;GMP;PPPAPEP@P5C?PQP4D@b2b0W0%=IP;PVPEP@P5P4CNPEP@P5PTCN51;X1;P@P5P6PVCN,7;PWP1E6P;PHP@P5P6PUC?PHPDDGeW0n0110000020000P4O1b0b1P;PAPEP@P?PAP?F5eX=JX98X:=X@=X;7P1P2P3P4CERJ/2@P7P>P0P1P2P3CE?3E4P7P5P6P0P1CER>?3F4P;PHP7P8P3PFP@P5P6P0CER?n010000002000010H?RDC4]0P3P6P0P1P2CE/2ARA#9A>>F41D>FPBP;PCP4PMC4X78PEP?P4DCP;PDPHPFCRP;PCPEP@P5P6CEPMP4D@b2b0W0%=AP51QB6P0P1CP,7;10B>R>=1;>eW0n0110000020000P4O1b0b1P;PEP@P5PJPEPJF5eX:=X><X?=X;7P3M:TW2X98XA8X78W<o"). Qed.
End VP12.

Definition asub (f t : expr) (a : saddr) : saddr := SA (esub f t (a_base a)) (a_off a).

Section VP13. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma asub_sound : forall E f t a,
  edenot E f = edenot E t -> adenot E (asub f t a) = adenot E a.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP13"] "p'0h01bh11Eh21Hh31ah41fh51kh61ti006a_basei015a_offi021sp;1p;2p;3p;5p;6g003lj11Tg004Qj1>Tg004oj1=Tg01>Vj20Tg007fj32Tg028\j37Tg01=Mj24Tg01?_j23Tg00Dij2<Tg01oJj36Tg029`j5;Tg002nj6:Tg019kj25Tg01AZj19Tg01Bcj18Tg00<gg01F:R0g01jRR1P1g00=o#1#1#1#1#1#1#>#=R1f4R2f3R3'0f2R4,0232f5R5f1R69723'41456521[f0R2g00gWf7R7f6R8'01075521P1f8R5/04R91324f9/03/34521X011396,<1A6784,05P5P7P8P4P2D;E:1546R4#9R99678%84R3'5R:#9,05%8:'31059/33521eA7784,451454521eW2W5X00P6P2O2n01102000120100101W3X60W4W1o"). Qed.
End VP13.

Section VP14. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma asub_estart : forall E f t a,
  edenot E f = edenot E t -> estart E (asub f t a) = estart E a.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP14"] "p'0h01bh11Eh21Hh31ah41fh51kh61ti006a_basei015a_offi021sp;1p;2p;3p;5p;6g003lj11Tg004Qj1?Tg004oj1>Tg01>Vj20Tg007fj32Tg028\j38Tg01Ckj25Tg00Bgj24Tg00F@j23Tg00Dij2=Tg01oJj36Tg029`j5<Tg002nj6;Tg019kj2:Tg01AZj19Tg01Bcj17Tg00<gg01F:R0g01jRR1P1g00=o#1#1#1#1#1#1#?R1#>R2f4R3f3R4'0f2R5,0332g00gWR6f5R7f1R89834'5157832[f0R3f7R9f6R:'01097522P2f8R7/05R;1413/35f9/04,41/35526X02141;/38,=6A69:5,07P7P9P:P5P3D<E;1:58R5#9R;969:%75R2':R4#9,07,41%74'3107;,41/32526eA89:5,571575526eW2X56X00P8P3O2n01102000120100101W3X60W4W1o"). Qed.
End VP14.

Definition ksub (f t : expr) (K : kentry) : kentry :=
  match K with
  | KWord a w v => KWord (asub f t a) w (esub f t v)
  | KZero a n => KZero (asub f t a) (esub f t n)
  | KBlob a n bk => KBlob (asub f t a) (esub f t n) bk
  | KImg lo hi => K
  | KAlign e m => KAlign (esub f t e) m
  | KRange e lo hi => KRange (esub f t e) lo hi
  | KWr a n => KWr (asub f t a) n
  | KDisj a1 n1 a2 n2 => KDisj (asub f t a1) n1 (asub f t a2) n2
  end.

Section VP15. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma flat_asub : forall E f t a n,
  edenot E f = edenot E t -> flat E (asub f t a) n <-> flat E a n.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP15"] "h02H0h12H2h21Eh31Hh42H1h52H3h62H4h71ah81fh91nh:1th;1zp;1p;2p;3p;4p;5p;6g003lj15Tg004Qj1FTg004oj1@Tg01>Vj2;Tg007fj3ETg01Ckj21Tg00Ebj1<Tg00TNj2?Tg00F]j22Tg00A:j24Tg00AUj2>Tg02:jj48Tg02;Ej59Tg028\j3DTg02;bj5CTg002nj6ATg01<@j3=Tg00URj2:Tg00F@j2BTg00iZR0f0R1':p=3f2R2f1R3'B/:1p=01431,42p=71:03/41p=6g00<gg01F:R0g01jRg00gWR4g00=o#5R5#5#5#5#5#5R6#F#@f4R7f3R8';1;723EP4f5R9/12R:%<5%<6'?R6,21%32R5A012637,61f6R;/18R<#3R=12<6A0<26775R5'4R<'>X;412:6%33A0:3637,6:R:P<[R4P4P=P5P<f7R</17R5/26%38A058637f8R5/19R4/26R>A0476,67R?14>?,64f9R4/1;?096,69%3;R?f:/1<R@?0;6R;12@6?7?;,6@f;/15?0<6f</14R4#31246R<%35R@A0456R4'4R5'4P9P<P5P8P@P4P3P1C8C8C8W6X1?P1D9W5X0>P1D9W1X4=P1D9X0:R:P:C8AD782R:,19P9P7P8P2P1DCEAA=9:3A=923'>eW3W9W7X:0W8W2o"). Qed.
End VP15.

Section VP16. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma ksub_sound : forall segs E M f t K,
  edenot E f = edenot E t -> kentry_ok segs E M K -> kentry_ok segs E M (ksub f t K).
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP16"] "p'0h02HKh11ih21bh31zh41ai001ah55lemmah61mi011mh71ni021nh81dh91ei031eh:2hii042hih;2loi052loh<1Ah=1Bh>1Eh?1Hh@1KhA1MhB2a1i062a1hC2a2i072a2hD1fhE1ki081khF2n1i092n1hG2n2i0:2n2hH4segshI1thJ1vi0;1vhK1wi0<1whL1xhM1yp;1p;2p;3p;4p;8p;7p;6p;;p;5p;=g003Lj1\Tg003lj1>Tg004Qj1VTg004oj1QTg005Rj1`Tg01>Vj24Tg007fj32Tg008@j45Tg02<mj3TTg01=Mj2KTg00ECj1;Tg02>8j2aTg028\j37Tg00CQj1DTg01<@j31Tg00D1j4OTg01oJj3=Tg01b9j2LTg007Dj2?Tg00A:R0j20Tg00AUR1j2GTg000Sj4jTg02>Rj4FTg02?9j2iTg02?fR2j2hTg02@Dj4gTg02@fj8UTg02AYj7fl=kTg02BHj3eTg02C>R3j6dTg02D0l;cTg02Dkj6ETg029`j5BTg002nj66Tg02F4j5bTg02G>j2NTg00Bgj2<Tg00URj2:Tg00F]j2ATg01Ckj23Tg00O3j2_Tg02;bj5JTg02HIj2ITg02IWj3]Tg024ej2HTg01d;j2[Tg02Jbj1oTg02KBj4RTg016Kj2ZTg02K^j2PTg00]`j2nTg02Lij3YTg01;5j2STg00F@j2@Tg01E:j4XTg02N4j4WTg01ecj2^Tg02O?j3mTg02PCj4lTf5R4f4R5f3R6f2R7f1R8f0R93mC5p=8p-0R:P1P8P9Clp=C1@89,_7p=9P9P8P0P3P7g00l>R;P6P5P4f6R<f7R=f8R>f9R?M=kp=Mg00;h#\g00<gg00=o#>#>#>R@#>#>#>#VRA#QRB%V@R@#QRC#`RD[g01F:REg00>TRF1457145852BP<P4P5P8C5PFP>P=P<P9C5P?P>P=P<P4P8E8]0P7g01jRRFg00?_RGf=RHf<RIf;RJAT789C5PB1KH6g00i;#;#;#;#;#;#;#;#;,a6RKf>RLA7IJ5RM%D6RN31RO%\CRP#`RQf?RRPHP9P6COA=IJ7,4L,L6,?P32'0'0X2BPB14H8PRPH1KL5P6CORS1L69,?P52Q,0O,0KX2Bf:RT=7J6RU%D7RV51HA1H6V'GP:P:^=:RWP1P:P:P1P:P:P:P2CjR2CFRXP0PW\:P:P:\:P1P:P:P1P1CFRYCFRZP0P3P:PWP1PXCFR3P;P:PWP1P11i:1R;PYPXP:P:P1P1P;P1P2P:P11h98XM:XL:g02Q6CgGUGUR2FfPKg02Ql9e:1R1/CK14L7,L6,?P92QSRS,0OA1L5NRN/0SPOPNP9PSPS1C1SEdM;cW5PHPJPTP6PVP>EEP9O2A=JT8,4HPHPJPTP8P>DBE61KHUPHPJPTP6P>DbE6PLPHPIPJPTAT678E8eW0XJEWKW4P7P8P9O3PJPTP?1N89C5PB14J8RVA7T?6RS1<A9RN51Ig00gWROg00iZRQ/:9RP1<A8,A9'0RKPHA7IJ4,3L=9A8O11_@QR@,?CR;52D[]1'0X2BPO13J7RX14I7,<ARY91ISR014H6R[,<A,A9,0PR\PHA9A78R]O1=2D;[^1O'0X3OA7?>7R^1<AVRV51JA1J7V'GPW^<:R:PZP3P2P0A1I6YP9PH13L4=9A8O1=2D;\\^1OR\P\1C1\M:MW5PJP?P>P7PVP<EEP9O213J^RVPJP?P>P7P<DJR\E6A=?>8RY,4JPJP?P>P8P<DBE61IJY91J^A=T?7,II,A9,0PPIA7JT5,3H=9A8O1=2D;[^1O'0ePIPJPTP?P>1N78E8eW0X7EX4FP8P9O2PHPIPJA]789C5PB14H7R;A1LMN1HL7,[C#DRY=2ONPRf@R0A7LH<'3=9A8O1PC%o8RW1H05P@CR,?CR_52D\K^1O'0'0X2BPO13H614L6,<ARK91LMRMA2OYKRY14R5,<A,A9,0PR`PRP]O1=2D_[^1O'0'0X3O1<A;R;91HUA1H6;'GP:PZP3P2PMA1L5KP9PR130<=9A8O1=2D_\`^1O,0YRYPY1C1YM:MW5PHPJPTP6P;P>EEP9O213HUPHPJPTP6P>DJE6A=JT7R;,4HPHPJPTP7P>DBE61IH;R;91HU1HH8,[C#D=2O;A=IJ6,IL,A9,0PPLA7HI4,3R=9A8O1PCPW1HR6P@CR,?C52D[^1O'0'0ePLPHPIPJPTA]678E8eW0XEGX7EX4FP7P8P9O3PJPTP?1Z89C5P9PIPJPTP?P>1Z78E8eW0X:OX;OP8P9O2PJPTP?1P89C5PB14J71AQ71nN7=2OQ'0X2BP9A=?>7,4JPJP?P>P7P<DBE6PIPJPTP?P>1P78E8eW0X6OX9EP8P9O2PHPIPJAY789C5PBP[1:6N1:N7'0X2BP9A=JT6,4HPHPJPTP6P>DBE6PLPHPIPJPTAY678E8eW0X:OX;OX9EP7P8P9O3PJPTP?1S89C5POPXA1IS7RS1:Q8RQ%D8,@7/:4RXg00nXRBfARNPRA9A56P7CXg00o8R[32[[^6G^8O'0X3OA1J^8A1J78'GP:PZP3P2PSA1I67P9PNPR130==9A6P7CX=2B[\X\Q^6G^8ORGPG1C1GM:MW5PJP?P>P7P8P<EEP9O2PVP\E6PIPJPTP?P>1S78E8eW0X7OX4FP8P9O2PRPLPHP6P7P8P9CWC5PO13R51@95A7LH6,30R>':1@>7/:9'^X3OPO13R71304R4/@5/:91@97/:4'^X3OP9A7HI7,3RPRPHPIP7PTDJE6A7HI5,3RPRPHPIP5PTDJE6P0PRPLPHPIP5P6P7P8CWE8eW0XGOXCFXFOXBFP6P7P8P9O4n0110800083110010<10;2110010231100102108201051042010310130103105104211001024010610910710:P9O1W0W?W@XIEWDWAW>WHo"). Qed.
End VP16.

Section VP17. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma know_ok_ksub : forall segs E M f t kn,
  edenot E f = edenot E t -> know_ok segs E M kn -> know_ok segs E M (map (ksub f t) kn).
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP17"] "h01fh11xh21Ah31Bh41Ph51lh61Eh71Hh82H0h92HKh:1Kh;1Mh<2knh=4segsh>1tp;1p;2p;3p;4p;5p;7p;6g003Lj13Tg003lj10Tg004Qj16Tg004oj14Tg005Rj1@Tg01>Vj28Tg007fj3;Tg0064j45Tg02R\j42Tg009Rj31Tg02S8R0j59Tg02O?j27j3?Tg008@j3:j4>Tg02SWj7=Tg02Taj6<Tg00;h#3g00<gg00=o#0#0#0R1#0#0#0#6#4R2%61#4#@[g01F:R1g00>TR3#3f4R4f2R5'8f1R6,845;2f6R2f5R7P4P6C5P0p4p710R8P0p4p7210R0P6\6R9p-0\6R:f3R;#3R<g00A:P4P;P5f0R=C291;6P;P4P=O1O1X17=176R>[P5P;P=O1O1X14=14=P7P4P;P6C29145[R?P2P7P4P5C2917;\>P4P;P5P6P=D9P=n2001000000120000000W5W4W0W3W2P?^5<^4:^09^30^28P=P3P31774f8R8f7R0;:2R9P;P3P9f9R9P8P0A?27=C>X13P9P8P0P2P7P=P;F=X:3P;P6E<O6b8P0P2P7P3P3174;P5C2C5eW9W7W<X>1W0W;W6W=o"). Qed.
End VP17.

Section VP18. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma regs_ok_esub : forall E f t sr R,
  edenot E f = edenot E t -> regs_ok E sr R -> regs_ok E (map (esub f t) sr) R.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP18"] "p'0h01ih12srh21bi001bh31Eh41Hh52HRh62IHh71Rh82_Hh91eh:1fh;1rh<4resth=1ti011np;1p;2p;3p;5p;4p;6g003Lj1QTg003lj14Tg0123j1JTg004Qj1>Tg004oj1CTg02UAj2NTg01>Vj20Tg02Umj39Tg02W=j2<Tg00Qhj3DTg02XFj3PTg01GCj1OTg02Y3j1BTg00Dij2;Tg01oJj27j3FTg00G^j1MTg00ECj1ITg00S0j38Tg029`j5GTg028@j4HTg01gZj6ETg02Z:j2KTg002nj6LTg007fj3@Tg02R\j4ATg02KBj4=Tf3R0f2R1f1R2'0f0R33@p=2g01F:R4P41712P3CAp=110239@01p=?P4P1P2P3C=p=3P4P4P2P3CAp=6P4P1P2P3C=,00p=5P4g00i;P2P3C=p=:g00<g%Q4R5g00=o#4R6#J#>R7%46#4#4#4#4#>#CR6'NP6f4R8P01081C2f5R9?912%C7P6f7R:1<83'0R;P6P3f8R<f6R==1:9/<2C?X26g00iZR>g01095D79P73g00nXR7P7P6f9R?P7P4P3%O>R>%B1R@?3=>n0100000020000P7P4P3P>A1<:==3@>n0100000020000,0?C2P310<>,;6g00?_R<f:R??93=P4P6f=R@A332>R7P@P3f<RAf;RB'7RC/62P>C5C2^0<X15P<P6P@%M4RD=33>P@P316CDP>C5C2P3A1B?D/:>,0A,;6f>RB%I3RC17@ARA/6DP>C5,;6X0<P3O1n0110100020010101X0<P6PBP7PBP316A2P>C5C2^0<P<P6f@RAA8480R7=33>PAP3f?RD?1B7P>C5C2P3P6AFB@0,0D10D0PDPBP@P0P?DGCHP6PDA8401R?/:>A1B@?/:>,0DC2eP0P3O1P6fAR?A8498RB=3C>P?PCA1ADBP>C5C2eX0<P3O1n0110100020010101X0<W6X<5X94P2P1EEW8X15W0%B2P9P1O3n0110000020001b2P6P;P:A1=98/<3C?e1K03P2P3O1ELW;A1980=9=1eW5W4W7W1X=4X:4W3o"). Qed.
End VP18.

(* [comment removed for export] *)
Section VP19. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma regs_ok_ext : forall E sr sr' R,
  length sr = length sr' ->
  (forall i, (i < length sr)%nat -> edenot E (nth i sr (ELit 0)) = edenot E (nth i sr' (ELit 0))) ->
  regs_ok E sr R -> regs_ok E sr' R.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP19"] "p'0h04__x1h14__x2h24Hge0h35Hlen0h47__arithh54__ffh68__varmaph75__with84__x3h91bi001bh:4cstrh;5cstr0h<5cstr1h=1eh>1Eh?2HRh@3HeqhA3HgehB4HlenhC3HlthD1RhE1ihF1ohG1rhH2srhI3sr'hJ1xhK1yp;1p;2p;3p;4p;<p;5p;6p;7p;8g003Lj1NTg003lj18Tg0123j1HTg004Qj1ETg004oj1PTg02UAj2bTg007fj30j1GTg00BOj2:Tg01GCj1XTg01>Vj21Tg02Umj3MTg02W=j2?Tg00Qhj3jTg02XFj3iTg02Y3j17Tg00Dij26Tg02[3j2^Tg02>8R0j29Tg01ecR1j2[Tg00CQR2j12Tg00URR3j25Tg00X4j4ITg02[[j2ZTg02\>j3YTg00WOl<FTg00G9j1KTg01M[j1WTg02\[j2VTg00ECj1DTg012Xj2ATg02]<j3UTg013Aj3CTg013jj2TTg00G^j1RTg00S0j3STg00H>j2BTg00ZEj4QTg00H\j1lTg00I:j1kTg00JHj2<Tg00cSj4>Tg00Jkj1hTg00KMj2fTg00Koj2aTg00L[j3`Tg00M:j4_Tg00Mlj4LTg02]ej5OTg002nj6=Tg00Ygj1cTg02Z:j2dTg01d;j2eTg02KBj4]Tg00d>j7\Tg00eEj8gTg01F:R4f0R5'ep=3P4f2R6f1R7P5C]p=4g00?_R8g00gWR9P0P2P3g02^Ff5R3f4R0f3R:P6P7P5M<Fp=JP7g00j_R;g00k>R<P<g00k^R=P5g00l>F\p=;P:P;P<P<P=P6P7P5Ggp=@g00<g%N4R;g00=oR>#8R?#H#ER@%8?#8#8#8#8#E#PRA'b%36%37508%30,:5f6RBg00iZRC#XRD9473'1A470D,1B50A[^E8AM306%P@PAf7RE1?B5'1RFf8RG1?B7'190A5X9Ag01099j@C9i@5g00nXR@P@f9RHP@P4P5PD%76RI?4GDn0100000020000'1P@P4P5PDA4IEDn0100000020000,1H50AP511GD,6A%77RJ%3ERK'^1:JK19KJ'[P1%3GR1,:I191If:R1%7:RI?4HD'1A4IGD,1150AP5%3HRK,:IPB%70RJP5O2WCP5O119KIP4PDf<RI/15RL%73?41D,1I50AX=4P4PD11ID=0ALX=4f;RL/1D,6AA4JHDP4PHPJPD19KJ%2KRH%2JRI'5PKPH169HPJPI169IRHEJ%31RK/9JRM%2KRN/5IROPKPN169NRPPJPIPHEJRHP5CIRIPO%3LRL=08K%2LRQ=09NRRP8P9%G8P2%G9%27%25509A08751Z753YXK8XJ8PLPQ169QPKPNPPM<FPGCIRGPR%7BRP#KRN%2P,5CRPf=#3RK#KRQ%2K,5CRKPQPKg00mlRL%W>,V9g00i;R8#DR2#D,A95U91A921A985C95C9g015_'T%RLR83S%NLRLP91B96R2P71B9:CQ%l9RS%k9RTP9%H>,<9RUg00mE1<9>R>C>,;T%h<R<PTP9PUg00j8RU1<9?R?C>,;TP<P9P>PUP?C>,;TR?C@C@1fT=R=P5P6g00o8RU,6@1a56=0@UdA`9C7C_RCb5b6b7X09X19X89A096515:6156:[[^09^19^89P5f@#3#2RU%71#2R@f?#3#2P0P3O5b4b<b;b:b3b2CLDOE=A4J1DP4P1PJPDPMPOPHPIPOPGPRPNPPPQPKPQPKP8PLP9P2P7%c9CQPSPTP?P<P?C@P=PCb5b6b7X09X1915571576[^09^19P5P@PUP3O3b4b<b;b:b3b2CLDOE=WAP5O1n200100000021000011000bFn0110000020001b91?35,1E90AFe1d05P7P5O1E=WGAMB0:eW?W@WBWDXI;WHW>o"). Qed.
End VP19.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section VP20. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma junk_vals_length : forall R, length (junk_vals R) = 32%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP20"] "h01Rh11ih21np;1p;2p;3p;6p;4g003lj11Tg0123j1BTg004Qj14Tg004oj17Tg02UAj2ATg02^hj2;Tg01d;j23Tg007fj35Tg00Dij29Tg02_Dj28Tg002nj66Tg00CQj1:Tg00O3j2@Tg02Z:j2?Tg02R\j4>Tg02_cj4<Tg02`Bj1=Tg00ECj12Tf0R0#2#2#2#2p=0g00=o#1R1#B#4R2%11#1#1#1#1#4#7R1'Ag00?_R3g00i;R4%04#0#0#0#0#0#0#0R5';R6,33R7A5305X23R8P3P5P81935P71854E6P3P1f1%:0,@2'?X13R2P6C>,31P3P1P2P6C<E6%=0,31=535eW0o"). Qed.
End VP20.

Section VP21. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma vals_ev_app_l : forall vals extra n, (n < length vals)%nat ->
  vals_ev (vals ++ extra) n = vals_ev vals n.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP21"] "h01bh15extrah21nh34valsp;1p;2p;4p;3p;6g003lj10Tg004Qj1=Tg004oj15Tg003Lj14Tg01d;j2<Tg00BOj2;Tg00O3j2:Tg02KBj41Tg007fj32Tg00Dij26Tg00@]j37Tg02aJj68Tg002nj69Tg02agj23Tg00=o#0#0#0#0#0#0#=R0#5R1#4R2g00?_f0R3f2R4,<1';P1P1f1R5f3R6g00iZ,:0R0C1R7P1P4f4P0C19213X011617P1P5A7164R7P0C1P1P6P4P0P5P3E8E913751365521eUW2X12W3o"). Qed.
End VP21.

Section VP22. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma vals_ev_app_r : forall vals extra n,
  vals_ev (vals ++ extra) (length vals + n) = vals_ev extra n.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP22"] "h01bh15extrah21nh34valsp;1p;2p;4p;3p;5p;6g003lj10Tg004Qj1=Tg004oj1;Tg003Lj14Tg00O3j2<Tg02KBj41Tg007fj32Tg00Dij2:Tg01d;j25Tg02bkj26Tg00@]j37Tg02cBj58Tg002nj69Tg02agj23Tg00=o#0#0#0#0#0#0#=R0#;R1#4R2g00?_P1P1f0R3f1R4g00iZ,<0R0C1R5P1P4f2R6P0C19213X011:15P11516/63R5A7164R7P0C1P1P6P4P0P3D8E913751343521eW2X12W3o"). Qed.
End VP22.

(* [comment removed for export] *)
Section VP23. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma env_app_know : forall segs vals extra ebs M kn,
  kn_vars_lt (length vals) kn = true ->
  know_ok segs (Env (vals_ev vals) ebs) M kn -> know_ok segs (Env (vals_ev (vals ++ extra)) ebs) M kn.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP23"] "h01Mh13ebsh25extrah32knh44segsh54valsp;1p;2p;3p;4p;9g003Lj11Tg003lj10Tg004Qj14Tg004oj15Tg005Rj1=Tg01d;j26Tg02cdj2;Tg007fj38Tg02agj12Tg02dkj23Tg0064j47Tg00@]j39Tg02f3j3:Tg02g>l9<Tg00;h#1g00=o#0#0#0R0#0#0#0#4#5R1#1R2g00?_%40#5R0#1[%=0\1g00>T#1g00nXf4R0,61f0R3';g00o838f6R4f5R5#2f3R6'3f2R7f1R8C7f71614%24/30A9145#2/30P6P7A:450P8P3M9<UUW3W0W1X22W5W4o"). Qed.
End VP23.

Section VP24. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma env_app_regs : forall vals extra ebs sr R,
  sr_vars_lt (length vals) sr = true ->
  regs_ok (Env (vals_ev vals) ebs) sr R -> regs_ok (Env (vals_ev (vals ++ extra)) ebs) sr R.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP24"] "h01Rh13ebsh25extrah32srh44valsp;1p;2p;3p;8g003lj10Tg004Qj14Tg004oj15Tg003Lj12Tg0123j1>Tg02UAj2;Tg01d;j26Tg02hHj29Tg007fj38Tg02agj13Tg02dkj21Tg02Umj37Tg00@]j3:Tg02f3j3=Tg02iOj8<Tg00=o#0R0#0#0R1#0#0#0#4#5R2#2R3g00?_%41#5#2[g01F:#2%>0#4/;2g00nXf4R0,62f1R1'9g00o838f5R4#3f3R5'1f2R6;71f6R7,62%37/10A:274#3/10P5P6A=740P1f0G<UUW0W3W1X23W4o"). Qed.
End VP24.

Section VP25. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma env_app_edenot : forall vals extra ebs e,
  expr_vars_lt (length vals) e = true ->
  edenot (Env (vals_ev (vals ++ extra)) ebs) e = edenot (Env (vals_ev vals) ebs) e.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP25"] "h01eh13ebsh25extrah34valsp;1p;2p;3p;6p;4g003lj10Tg004Qj17Tg004oj12Tg003Lj16Tg01d;j23Tg02jYj2<Tg007fj3;Tg02agj14Tg02dkj25Tg01>Vj21Tg00@]j38Tg02f3j39Tg02kbj6:Tg028@j4=Tg00=o#0#0#0R0#0#0#0#7#2R1#6R2g00?_%70#2#6[g01F:g00nXf3R0,31f0R3'<g00o83;P1f4R4#4f2R5'5R6f1R7'1A8140#4/55R8/171314P6P8P7A9405P3E:C=UW0W1X22W3o"). Qed.
End VP25.

(* [comment removed for export] *)
Section VP26. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma regs_after_keeps : forall vals ebs sr R R' (kept : list reg),
  sr_vars_lt (length vals) sr = true ->
  regs_ok (Env (vals_ev vals) ebs) sr R ->
  (forall r : reg, In r kept -> getr R' r = getr R r) ->
  ~ In 0%bv kept ->
  regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs)
          (sr_after_call_j sr (map ridx kept) (length vals)) R'.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP26"] "p'0h01xi001xh11Hh21rh31Ah41Bh52Hih63Hinh72Hrh81bh91fh:1ih;1lh<1yh=2H0h>2HRh?2Hkh@3HlthA3Hr0hB1RhC2R'hD3ebshE4kepthF1nhG2srhH4valsp;1p;2p;3p;4p;5p;6p;:g003lj16Tg004Qj1ATg004oj1?Tg003Lj19Tg0123j1TTg02UAj2RTg01d;j2QTg02hHj2MTg007fj31Tg02agj1JTg02dkj2HTg02Umj3FTg00:3j30Tg02Z:j22Tg02lkj2STg00Qhj3ETg02mNj1CTg02R\j4=Tg00A:R0j23Tg02mgR1j28Tg02nAj5PTg02Y3R2j15Tg00BOj2:Tg00CQj1<Tg00O3j2;Tg02n`j1LTg0303j1ITg002nj6BTg02:jj4KTg00NWj6DTg00Dij2GTg031Jj3NTg032[l:OTg00ECj1>Tg00?_R3f1R4f0R531p=7%>5#>#>#>p=4g00i;R69135p=@g00=o#6R7#6#6R8#6#6#6#A#?R9#9%A8#?#9\3g01F:#9%T7#AR7/R9R8%?7R:#9g00nXf5R;,Q9f3R<'Mg00o831f6R=#J/H;f4R>;F<A0:5<12;412=4519[^2:g00iZR?g0109R@1S7?d5E7=0:<#Cf9RAf8RBf7RCP=P;P:P3P2P>C=RDP<f2REP:P3P2P;C=9035g033iRFp4p710RGPFp4p7210RFP4\4RH%9ERIP0P>P<PEP4C=90<5P>P5O1=1;EA0=5<'3X0;,8;[RJP<P5O1=1>4A0;5E'3X0>,8>P;P>P<PEC=90>4RK[P;P5O1=1=<A0C5>'3X0=,8=\KP>P<PEP4P5DPP4n2001000000120000000X<EW;W9W4W3RKPJ^<E^;I^9H^4F^3GRGP5P:P3P2PCPEP4O6%55RE/7<A0:5BRF'3X0:,8:P1P:17E>A0:5A'3X0:%46#4#4#4#4#4#4#4RH,:>f:RI%<>,;7RJ'2f;RL/2J519'3P517E=A0:5L'3P0%54RJ/7Cf<90:41:BHf>RM%<B,;7RB'2f?RN/2B519'3P5%5<R</7AP3%5>f@90:;1:4HfBRA%<4,;7RB'2fCRO/2B519'3[X:3A0:>N%5;RN/:HfARH%<N,;7RB'212AB519%L;P:P;12A512O5519X8:f=P;P5O2PB%I;EBCKW7PIP5EDW1P4P5O2n2001000000121000000W1X2:P4P5O2n2001000000121100000b5b1W5X:3A036DRDPKPGP5P:P3P2P=P6P4O6%@EREA0:5C'3X0:,8:P1P:13EFX0:g01]ERFP5A0:5I,3EP0%@JA0:4LPFP5%@<A0:>MPLAE7?@R@P3P6%5@R6,75XF31G36PNP4EB5N;A1:;@P:P=A0:5HX8:P4P@P5EDb1O1W7WAP4P5O2n2001000000120000000W1X2:P4P5O2n2001000000120100000b6b1W6%CDeM:OW=W?W>W@WEXC8WBWGWDWHo"). Qed.
End VP26.

(* [comment removed for export] *)
Section VP27. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma know_after_store : forall segs E M kn sa w v bs kn' scs hs,
  carry [SE sa w v] kn [] = (kn', scs, hs) -> scs = [] ->
  know_ok segs E M kn -> (w <= 8)%nat -> flat E sa (Z.of_nat w) ->
  bs = word_to_le_bytes w (edenot E v) ->
  know_ok segs E (wbytes M (adenot E sa) bs) kn'.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP27"] "h02Hch11Hh22bsh33scsh41Eh52HKh63Hflh72Hwh81Mh92hsh:2knh;3kn'h<2sah=4segsh>1vh?1wp;1p;2p;3p;4p;=p;6p;7g003Lj14Tg003lj13Tg004Qj1>Tg004oj1=Tg005Rj1LTg034Fj2CTg01X;j36Tg00G^j18Tg00S0j37Tg034fj39Tg035nj42Tg007fj31Tg0064j45Tg00ECj10Tg02>8j2<Tg00CQj1;Tg01<@j3:Tg01>Vj2BTg01b9j2ATg01=Mj2KTg01cAj3@Tg00A:j2JTg02:jj4?Tg036Nj2GTg037_j3FTg0390j2ETg039Ql=HTg002nj6Ij7DTg00;h#4g00<gg00=o#3#3#3R0#3#3#3#>#=%>0#=R0#L[g00>T#4R1g01jRg00?_g01F:%40R0g03:YR2#4R3g00nXR4#4R51C13R6/C5R7g01iGR8f6R9f5R:f4R;36%88R<37f7R=%84R439P6P5P1P3f2R>f1R?C2f0R@C231%82RA913>P3PAf9RBf8RC;6==78<f:RD;94P6P5P1P3P:P@C2f3R:C2517f>REf=RFf<RGf;RHC5g00i;#0#0#0#0#0#0#0#0RI,<Df?RJ%;H7:Gf@RK/BH,AGRL910DfBRMfARN1KNERO=@KHPDC5[[[[]0X33A6C=9=78<?9B4P6P5P1P3P;PAC2P>C2517PFPGPHPDC51<BI%;D9:EH1BJD,AH910BP0PLPMPNA@KO@PDC5X20PNPKPJA6FGH=78<R<PEP4PBPAP=P;1<GI%;G9:KFRFg0119RG'JP>PFPGP?g0109C?C?1GK<eP:AFNJK,E2M=HPDP@EIW1W6W7W5W0P:P@P?FDW1W0W9W3X;1W2W>W?W<W:W8W4W=o"). Qed.
End VP27.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section VP28. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma Z_to_bv_lit : forall z (w : word), bv_unsigned w = z -> Z_to_bv 64 z = w.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP28"] "h01zh11Hh21wp;1p;2p;3p;6g003lj10Tg004Qj17Tg004oj13Tg00Bgj21Tg007fj32Tg00O3j26Tg00P:j25Tg00NWj64Tg00gWR0g00=o#0#0#0#0#0#0#7R1#3R2f0R3,11f1R4520P011141613f2R5522X001514P5P3E4W1W2W0o"). Qed.
End VP28.

(* [comment removed for export] *)
Section VP29. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma flat_intro : forall E b k n,
  (0 <= bv_unsigned (edenot E b) + k)%Z -> (0 <= n)%Z ->
  (bv_unsigned (edenot E b) + k < 2 ^ 64)%Z ->
  (bv_unsigned (edenot E b) + k + n <= 2 ^ 64)%Z ->
  flat E (SA b k) n.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP29"] "h02Hah14__x1h24__x2h34__x3h41Eh57__arithh64__ffh76__sat3h86__sat4h98__varmaph:5__with;1bh<1kh=1np;1p;2p;3p;4p;7p;8g003lj14Tg004Qj1ZTg01>Vj25Tg00Bgj27Tg00F@j20Tg00Ebj1=Tg00TNj2ITg00F]j23Tg00URj26Tg00X[j2ETg00YCj3CTg00G^j1BTg003Lj1YTg00H>j2ATg00ZEj4UTg00H\j1PTg00I:j1OTg00JHj2;Tg00dbj3@Tg0123j1JTg00Iej2>Tg00Zcj3HTg00Jkj1GTg00cSj4?Tg00KMj2FTg00Dij2KTg00Koj2DTg007fj3LTg00L[j3MTg00M:j4NTg00A:j22Tg019kj2QTg01AZj1RTg01Bcj1STg01<@j3TTg00d>j7XTg00g3j7WTg00eEj8VTg00iZR0f0R1'6p=1g00gWR2f1R3g00j8P1C?p=:P3g00j_R4g00k>R5P5g00k^R6P1g00l>FXp=9f2R7P4P5P5P6P3P1FWp=<f3R8P4P5P5P6P7P3P1GVp=8g00<gg01F:g00=oR4#4R9#4#4#4#4#4R:#ZR;1587'7/03#1%13f5R<f4R='5,7;/08%=9R>%=:R:'IR?'3f6R@/5<,7;/0=/08/6?1E>:130>%1:130?[[%1>RAg0119RBAC>:3UW0%1?\B^0Ag00mlRA#B%YAP21A27P31A28CU%P2%O2RA1;241;295@2R9%J4,;2R45@21>2>=H2;R>':,9ARB%G5R5PAP2P9g00l^P>C?,9AR>P5PA1>20R:/:4,9AR4P5PA1::9,9AR:P5A<A4B9<A>9<A:C8C8C8C81FA6P1P7g00nXRAg00o8R6'K1D17=LA6dAM203CNb6b9b:X12X22X321013/07/6?1037/3?%1=R7108=#110=<R3#1133?%1@103@/6?'2'2'2[[[[^12^22^32P1f7R1f8f:f9'5,7;P8P=P<P@O7b5b7b81Q@<R@#R,51,7;%S@'0R;#113;?10;=/6?,27'2'2eAT1@=eUUUUX=2X<2W;W4o"). Qed.
End VP29.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ECALLW : bv 32 := Z_to_bv 32 0x73.
Section VP30. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma is_ecall_ECALLW : is_ecall ECALLW = true.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP30"] "p;2g00Dij20Tg00nXg00o8'0o"). Qed.
End VP30.

(* [comment removed for export] *)
Section VP31. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma adenot_lit0 : forall E a, adenot E (SA (ELit 0) a) = Z_to_bv 64 a.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP31"] "h01Eh11ah21zp;1p;2p;3p;6g003lj10Tg004Qj1?Tg004oj18Tg00O3j21Tg007fj32Tg00Dij2;Tg00F@j23Tg01IXj17Tg002nj65Tg01GCj16Tg019kj24Tg01AZj19Tg01>Vj2:Tg00Bgj2>Tg01Bcj1=Tg01=Mj2<Tg00<gg00gWR0P0f0R1g00=o#0#0#0#0#0#0#?R2#8R31121R4f1R5,1232X201;34g00iZR0/31%71E5%60/41R1#9,:5,>2%=1'3,12=234e1<51=234eW1W0o"). Qed.
End VP31.

Section VP32. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma edenot_add_lit : forall E b k, edenot E (EAlu ALU_ADD b (ELit k)) = adenot E (SA b k).
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP32"] "h01zh11bh22b1h32b2h41nh51Eh61Hh71kp;1p;2p;3p;6g003lj19Tg004Qj1KTg004oj17Tg01>Vj2:Tg00O3j25Tg03;fj2ITg019kj2=Tg01=Mj2?Tg007fj33Tg00Bgj20Tg00\Vj3ATg00F@j21Tg00]:j24Tg00Ebj1@Tg00TNj2JTg00]`j28Tg03<`j3HTg00^@j1;Tg00_Bj2<Tg01AZj1FTg01Bcj1DTg020Nj3CTg03=Gj2ETg002nj6>Tg01GCj1BTg01QEj3GTg00gWR0f1R1f0R233p=2P0f4R3f3R4f2R5P1P2E>p=6g00<gg01F:g00=o#9R6#9#9#9#9#9R7#KR8#7R91:51R:1582R;'IR<1=51,?49392X19g011UR=%72R>%71R?g00A:%75?31210451041'2R@[10511052'2%74?351[RA%73?345\@AA512P2n2001000000120000000W3W2W4PA^3?^2>^4=P2P81:45,08R=1581,08R>'1R?,58RA11=1R@,58RB148?1:34,08R4/15R3,58,08RC,22X001481RD1142RE,48/2CX00148@RC1485,14,48/22X0011=DRF%@6%@7'JR7'81483R3,22X00181718E7/23X0018@71857,14/87/22X00AH1=7PC%;@D6PD%;1D6148F%;FD6108B1<8@D6P>1<81D6108A1<8?D6O4b6108:108;'1,581=12R?#F,:5,08%D?'1,58539e1?5?R?939<eg03>CR<?C:;1E:;E>%B29G<1,:5=39?eX70W1W5o"). Qed.
End VP32.

(* [comment removed for export] *)
Ltac split_foralls :=
  repeat lazymatch goal with
  | |- scs_denot _ _ _ [] => constructor
  | |- scs_denot _ _ _ (_ :: _) => constructor; [| ]
  | |- Forall _ [] => constructor
  | |- Forall _ (_ :: _) => constructor; [| ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac p6_body t :=
  first [ let b := eval cbv delta [t] in t in b | t ].

(* [comment removed for export] *)
Ltac p6_run HR HK fuel stops scr NX keep segs E sr R M kn pc rom model T ssn scs scr' knn scs2 hs2 :=
  eapply (rz_run segs fuel stops scr pc sr kn NX ssn scs scr' knn scs2 hs2 E M rom R model T);
  [ vm_cast_no_check (@eq_refl _ (ssn, scs, scr'))
  | vm_cast_no_check (@eq_refl _ (knn, scs2, hs2))
  | exact HR | exact HK
  | split_foralls
  | split_foralls
  | try reflexivity; try assumption
  | try reflexivity; try assumption
  | clear HR HK;
    let R' := fresh "R" in let M' := fresh "M" in let EQM := fresh "EQM" in
    intros R' M' HR HK EQM; cbn [s_pc s_regs s_log] in HR, EQM |- *;
    lazymatch keep with
    | true => idtac
    | false => clear EQM; try clear R; try clear M;
               try rename R' into R; try rename M' into M
    end;
    tryif is_var kn then try clear kn else idtac;
    tryif is_var sr then try clear sr else idtac ].

Ltac run_block_with HR HK fuel stops scr NX keep :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- realizes _ (mkCfg (mkst R (Z_to_bv 64 ?pc) M ?rom) ?model) ?T =>
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn NX) []) in
        lazymatch r with
        | (SS ?pc' ?sr' ?log' ?kn0 ?nx', ?scs, ?scr') =>
          let c := eval vm_compute in (carry log' kn []) in
          lazymatch c with
          | (?kn', ?scs2, ?hs2) =>
            let SRn := fresh "P6_SR" in
            pose (SRn := sr');
            let ssn := constr:(SS pc' SRn log' kn nx') in
            let knb := p6_body kn in
            tryif constr_eq knb kn'
            then p6_run HR HK fuel stops scr NX keep segs E sr R M kn pc rom model T ssn scs scr' kn scs2 hs2
            else (let KNn := fresh "P6_KN" in
                  pose (KNn := kn');
                  p6_run HR HK fuel stops scr NX keep segs E sr R M kn pc rom model T ssn scs scr' KNn scs2 hs2)
          end
        end
      end
    end
  end.

Tactic Notation "run_block_gen" constr(fuel) constr(stops) constr(scr) constr(NX) constr(keep) :=
  match goal with
  | HR : regs_ok _ _ _, HK : know_ok _ _ _ _ |- _ => run_block_with HR HK fuel stops scr NX keep
  end.

(* [comment removed for export] *)
Ltac regv HR r :=
  lazymatch type of HR with regs_ok ?E ?sr ?R =>
    let e := eval vm_compute in (sr_get sr r) in
    rewrite (reg_val E sr R r HR); change (sr_get sr r) with e;
    lazymatch e with ELit _ => cbn [edenot] | _ => idtac end
  end.

(* [comment removed for export] *)
Ltac krd HK a n H :=
  lazymatch type of HK with
  | know_ok ?segs ?E ?M ?kn =>
    let r := eval vm_compute in (kread segs kn (ELit 0) a n) in
    lazymatch r with
    | Some ?v =>
        pose proof (kread_rdn segs E M kn (ELit 0) a n v HK
                      ltac:(vm_cast_no_check (@eq_refl _ (Some v))) ltac:(lia) ltac:(lia)
                      ltac:(unfold flat, estart; cbn [a_base a_off edenot];
                            change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia)) as H;
        rewrite adenot_lit0 in H; cbn [edenot] in H
    | None => fail "krd: knowledge does not determine this read"
    end
  end.

(* [comment removed for export] *)
Ltac krdv HK i k n H :=
  lazymatch type of HK with
  | know_ok ?segs ?E ?M ?kn =>
    let r := eval vm_compute in (kread segs kn (EVar i) k n) in
    lazymatch r with
    | Some ?v =>
        let Hf := fresh "Hflat" in
        assert (Hf : flat E (SA (EVar i) k) (Z.of_nat n));
        [ | pose proof (kread_rdn segs E M kn (EVar i) k n v HK
                          ltac:(vm_cast_no_check (@eq_refl _ (Some v))) ltac:(lia) ltac:(lia) Hf) as H;
            clear Hf; cbn [edenot] in H ]
    | None => fail "krdv: knowledge does not determine this read"
    end
  end.

(* [comment removed for export] *)
Ltac kidx kn p :=
  let r := eval vm_compute in (kindex p kn 0) in
  lazymatch r with Some ?i => i | None => fail "kidx: no such entry" end.

(* [comment removed for export] *)
Ltac krd_solve HK :=
  lazymatch goal with
  | |- rdn _ _ (Z_to_bv 64 ?a) ?n = Some _ =>
      let H := fresh "Hrd" in
      krd HK a n H; rewrite H; clear H;
      first [ reflexivity | rewrite ?Z_to_bv_bv_unsigned; reflexivity | idtac ]
  end.

Section VP33. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma callee_kept_no0 : ~ In (0%bv : reg) callee_kept.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP33"] "p'0h03Hinh11Hh21ei001zp;1p;3p;2p;6g003lj18Tg0123j19Tg004Qj1>Tg004oj1=Tg00Qhj3:Tg00G^j1?Tg00S0j34Tg00:3j30Tg007fj31Tg00Bgj1<j22Tg01M<j2DTg02mNj1;Tg02lkj2CTg00Ebj1BTg03>oj6@Tg00NWj6ATf1R0f0R1#Bg0109R23:p=6f4g00gWR3f3R4f2R5P0P1E@p=7A1301p=5P3P4P5P2P0P1EAp=3g00=oR0#8R5#9R4#>R6#=R7g00iZR8=:62R91660R:1665R;%90R0,66R<%85R5,66R=%85,66R>%95R5,66R?%84R@,66RA%85,66RB%95,66R5%8@,66RC%9@,66R@%94R4#8,66RD%94,66R4%80R0#8RE#8,66RF%9E,66RE%90R0#8,66RG%90,66R0%?7RH547RI547RJ547RK547RL547RM547RN547RO547RP547RQ547RR547RS547RT547RU547RV547RW547RX54730RYg01ecRZA17:9R[A079XRXg01]ER\P1P7%<6R]P:P9P1D7126:R:1269R^'5P:P3p-0P1P\g0119P\n011000003001000010000X23R3P^P1C3P\1D\1R:b1b0X0[P1O1PZA17;9R[A079WRWP\P1P7P]P;P9P1D7126;R;/5^P;P3P^P1C3P\P:b1b0X0[P1O1PZA17<9R[A079VRVP\P1P7P]P<P9P1D7126<R</5^P<P3P^P1C3P\P:b1b0X0[P1O1PZA17=9R[A079URUP\P1P7P]P=P9P1D7126=R=/5^P=P3P^P1C3P\P:b1b0X0[P1O1PZA17>9R[A079TRTP\P1P7P]P>P9P1D7126>R>/5^P>P3P^P1C3P\P:b1b0X0[P1O1PZA17?9R[A079SRSP\P1P7P]P?P9P1D7126?R?/5^P?P3P^P1C3P\P:b1b0X0[P1O1PZA17A9R[A079RRRP\P1P7P]PAP9P1D7126ARA/5^PAP3P^P1C3P\P:b1b0X0[P1O1PZA17B9R[A079QRQP\P1P7P]PBP9P1D7126BRB/5^PBP3P^P1C3P\P:b1b0X0[P1O1PZA1759R[A079PRPP\P1P7P]P5P9P1D71265R5/5^P5P3P^P1C3P\P:b1b0X0[P1O1PZA17C9R[A079OROP\P1P7P]PCP9P1D7126CRC/5^PCP3P^P1C3P\P:b1b0X0[P1O1PZA17@9R[A079NRNP\P1P7P]P@P9P1D7126@R@/5^P@P3P^P1C3P\P:b1b0X0[P1O1PZA17D9R[A079MRMP\P1P7P]PDP9P1D7126DRD/5^PDP3P^P1C3P\P:b1b0X0[P1O1PZA1749R[A079LRLP\P1P7P]P4P9P1D71264R4/5^P4P3P^P1C3P\P:b1b0X0[P1O1PZA17F9R[A079KRKP\P1P7P]PFP9P1D7126FRF/5^PFP3P^P1C3P\P:b1b0X0[P1O1PZA17E9R[A079JRJP\P1P7P]PEP9P1D7126ERE/5^PEP3P^P1C3P\P:b1b0X0[P1O1PZA17G9R[A079IRIP\P1P7P]PGP9P1D7126GRG/5^PGP3P^P1C3P\P:b1b0X0[P1O1PZA1709RZA079HRHP\P1P7P]P0P9P1D71260R0/5^P0P3P^P1C3P\P:b1b0X0ZP1O1P1X0HP1O1n200100000021000010000X0IP1O1n200100000021000011000X0JP1O1n200100000021000011000X0KP1O1n200100000021000011000X0LP1O1n200100000021000011000X0MP1O1n200100000021000011000X0NP1O1n200100000021000011000X0OP1O1n200100000021000011000X0PP1O1n200100000021000011000X0QP1O1n201100000021000011000X0RP1O1n201100000021000011000X0SP1O1n201100000021000011000X0TP1O1n201100000021000011000X0UP1O1n201100000021000011000X0VP1O1n201100000021000011000X0WP1O1n201100000021000011000X0XP1O1n201100000021000011000W0%;YeP21C68d9:68P7eg03?L507#;eo"). Qed.
End VP33.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kentry_apart_b (allkn : list kentry) (ub : expr) (uk un : Z) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => ranges_apart allkn ub uk un b k (Z.of_nat w)
  | KZero (SA b k) (ELit l) => Z.leb 0 l && Z.ltb l (2 ^ 64) && ranges_apart allkn ub uk un b k l
  | KBlob (SA b k) (ELit l) _ => Z.leb 0 l && Z.ltb l (2 ^ 64) && ranges_apart allkn ub uk un b k l
  | KImg _ _ => true
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b k) n => ranges_apart allkn ub uk un b k n
  | _ => false
  end.

Definition kn_unfill (kn : list kentry) (ub : expr) (uk un : Z) : list kentry :=
  List.filter (kentry_apart_b kn ub uk un) kn.

Section VP34. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma unfill_outside : forall (a n : word) M (x : word),
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
  unfill a n M x = M x.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP34"] "p'0h01Hh11bi001bh21Mh31ah41nh51xp;1p;2p;3p;4p;6g003lj11Tg004Qj1=Tg004oj1<Tg005Rj1@Tg00Bgj20Tg00F]j23Tg00F@j25Tg00URj24Tg01ecR0j2ATg01K>j29Tg03@Pj28Tg01K[j26Tg00Jkj1?Tg007fj32Tg00Dij2>Tg03@mj2DTg03AMj4:Tg002nj6;Tg03Ahj2CTg03BHj4BTg00nXR1f0R2g01\@R332p=7g00=o#1#1#1R4#1#1#1#=R5#<R6%=4#<R4#@R7\61052R8f3R9,05R:'3f2R;,05R<,5:/48'AP0f1R0,05R8f4R=,05R>'315>:/48P1P7f5R8,05R?/9<15?>R@,8<'6%?4R4P9P;O1RAn0100000020000=27AP213<?P1P3P1P7f7,05RAf6RB,05RC'5RD,8>RE,62P4P8P=O1RFn0100000020000=27FX11P=P9O1,>719C:RG%7G13>A[13:C19A>#7[1DC:P2C:E;W0P2O114@<PGP1P1P1P7f8,05/5ARA,8?R5,62P4PBP8O1R8n0100000020000=278P2P1P3P1P7g00o8/62P4P8n0100000020000=278X111>7FRFPE%7E14A?[14D>%75[1C>DP0C:E;PFn0110000020100b1W0P2O1n200100000021100011000P=P9P;P0CBP;P0O1527eW0X56W2X46W3o"). Qed.
End VP34.

Section VP35. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma unfill_none : forall (a n : word) M (x : word), M x = None -> unfill a n M x = None.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP35"] "p'0h01xh11Hh21Mh31ah41bi001bh51nh61op;1p;3p;2p;6p;4g003lj10Tg004Qj18Tg004oj14Tg005Rj1;Tg00Jkj1=Tg007fj32Tg00Bgj21Tg01K>j25Tg00F@j26Tg03@Pj27Tg01K[j23Tg00Dij2:Tg002nj69Tg03BHj4<Tg00=o#0#0#0R0#0#0#0#8R1#4R2%80#4R0#;R3^02f1R4f0R5O1%=0R0523P3P0g00nXR6P3f5,11R7f2R8,11R9'5f4R:,11R;,67,79'3P0P5n0100000020000=230X631114R9,5;f3R7,11,6;,79'3P6P6P6P3P5P0P0n0100000020000=230P51:30R6P6n0110000020000b4P8P4O1P5E9P:P7P8P4C<=230eW1X02W2X52W3o"). Qed.
End VP35.

Section VP36. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma wview_ext : forall segs M M' (x : word), M' x = M x -> wview segs M' x = wview segs M x.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP36"] "p'0h01xi001xh11Hh21Mh32M'h41oh54segsi011bi023segp;1p;3p;2p;6g003Lj1DTg003lj10Tg004Qj14Tg004oj13Tg005RR0j1CTg007fj31Tg007Dj2>Tg00Bgj22Tg00Ebj1=Tg03CBj36Tg03DFj1<Tg03EHj1;Tg03FGj1:Tg03GEj1BTg01@Zj29Tg03Gcj15Tg03HAj27Tg00Jkj1ATg00Dij2@Tg002nj6?Tg03IHj38Tg00;hR1#Dg00=oR2#0#0#0R3#0#0#0#4R4#3R5%43#3R3#CR6]0R7f1R8f0R9O1f2R:P9O1516P6f3R;P8O1R<P0P3P6P91>39R=P0P1P6f5124:R>%=2R236g00nXR?P6%<9R@%;9RA124;%:9#BRB'9#5'7%A3RCn0100000020000PCn10110000021010200RDn10110000021010100P0P3P6f4REP:O1P=PDn10110000021010100516X46P0P3P6P<P=P0P1P61248=6E2P?P6P@19>B#5,7APCn0100000020000PCn10110000021010200n10110000021010100,@6P:P8O1P9E?A8E:8A8E;8516eW1X05X37W2W5o"). Qed.
End VP36.

Section VP37. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma store_ok_agree : forall segs M M' (a : word) n,
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  (forall x : word, (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n)%Z -> M' x = M x) ->
  store_ok segs M a n = true -> store_ok segs M' a n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP37"] "h01xh13Hagh23Hnwh32Hsh42Hxh51Mh62M'h71ah81nh91oh:4segsp;1p;2p;3p;4p;8p;5p;6g003Lj1ETg003lj10Tg004Qj17Tg004oj16Tg005Rj1DTg00Bgj21Tg00CQj13Tg00F@j22Tg00Ebj18Tg00TNj2<Tg00URj24Tg00F]j29Tg00A:j2:Tg007fj35Tg01E:j4CTg03IHj3;Tg00Jkj1@Tg02mNj1?Tg03JEj8>Tg03KEj5=Tg002nj6ATg03LNj6BTg00;h#Eg00=o#0R0#0#0R1#0#0#0R2#7R3#6R4%71#6R1#DR5]0R6g00?_f1R7,13f0R8#3'2%80%82'<'4f3R2,13R01138R9'4f2R:#3,20,99':f5R0P7O1f6R;P7O1555[^04g00nXP;P0P2P:CCg00o835f7R<P2P0f4R=P:1130R3/49%3=,23,99':P5f9R9f8R3;;7%@19558#?X95P9P3P0P;P=P:P7P8G>A;9<7P9P3P<P7P2P7P8O2D=EAW4X04EBW3W1W2W8X74X66W5W:o"). Qed.
End VP37.

Section VP38. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma know_ok_unfill : forall segs E M kn ub uk un,
  know_ok segs E M kn -> flat E (SA ub uk) un -> (un < 2 ^ 64)%Z ->
  know_ok segs E (unfill (adenot E (SA ub uk)) (Z_to_bv 64 un) M) (kn_unfill kn ub uk un).
Proof.
ltac2:(KReplay.run1 (kr_t_SymDriveX ()) ["VP38"] "p'0h01ii001ih11Hh22Hbh33HKKh43Hinh54__x1h64__x2h74__x3h84__x4h97__arithh:6__sat5h;6__sat6h<1ni011nh=1mi021mh>1xh?1zi031zh@4__ffhA4__p1hB8__varmaphC5__withD4cstrhE4__p2hF4__x5hG1dhH4len1hI4len2hJ2opi042ophK1ki051khL1ohM2HfhN1bi061bhO1li071lhP3Hm0hQ1AhR2G1hS2G2hT2G3hU2G4hV3Hl0hW3Hl1hX2HmhY2HzhZ2a0i082a0h[3lenh\2loi092loh]2sxi0:2sxh^2Hih_3Hj0h`3Hw0ha2Hxhb3Hx0hc1ei0;1ehd2Elhe2Hahf3Haphg4HinFhh4Hlenhi1Phj4__x6hk1fhl2hii0<2hihm2k0i0=2k0hn1vi0>1vho1wi0?1whp1yhq5APARThr1Ehs2F1ht2F2hu2F3hv2F4hw2H0hx2H1hy2HKhz2Hdh{3Hflh|2Hjh}2Hnh~5Hnonei0@2Hri0A3Hsti0B2Hui0C3Hubi0D3Huni0E2Hwi0F1Ki0G1Mi0H3OUTi0I1ai0J2a1i0K2a2i0L2bki0M1ji0N2kni0O2n1i0P2n2i0Q2nwi0R4segsi0S2ubi0T2uki0U2uni0V6a_basei0W5a_offi0X2b0i0Y2k1i0Z2n0i0[1sp%0p%1p%2p&0p&1p;1p;4p;2p;3p;5p;6p;7p;<p;8p;Bg003Lk106Tg003lj1yTg004Qk10nTg004ok10iTg005Rk10wTg0064k40<Tg019kj25Tg01<@j3<Tg00Ebk10MTg00TNk210Tg00F]R0j27Tg03MQk40hTg01Ckj21Tg00F@R1j20Tg01=Mj2TTg00O3j2NTg03BHj3Ck40[Tg03N`k40NTg00X[k213Tg00YCk312Tg00G^k111Tg00H\k10~Tg00I:k10{Tg00JHk20jTg00Iek20^Tg00Zck30yTg00Jkk10gTg00KMk21NTg00Dik20vTg00Kok21KTg00L[k31JTg00M:k41ITg00A:R2j2:Tg00[Fj2rTg00Bgj2HTg03Oik51GTg009Rk30?Tg00:3j3^Tg00:Jk30sTg008@k30bj4;Tg03Q7k40ck51<Tg03REk30OTg03R`k419Tg00;Mk615Tg03S>j7VTg03TMm<14Tg02<mj3tTg00ECR3j1KTg02>8R4k201Tg00CQR5j13Tg01>Vj2fTg01b9k200Tg007Dj2]Tg00D1k40oTg00BOR6k20_Tg00URR7j22Tg00X4j4eTg00G9j1oTg012Xk203Tg01M[k10}Tg02\[k20|Tg02]<k30kTg00Ygk10zTg0123k10KTg00cSk40JTg014Vk60xTg00NWk60]Tg02:jj4lTg02G>j2|Tg03@Pj2aTg01K[j2cTg02HIj28Tg007fj3=Tg01GCj1ETg01L9k30\Tg01K>k20fTg01L\k21MTg03Uhk21LTg002nk60eTg01N9k10FTg01QEk30DTg01RNk30CTg01SWk30BTg01T`k30ETg01Uik40;Tg01W2k40ATg02IWj3~Tg024ej2DTg02Jbk10tTg02KBk407Tg01d;k20@Tg016Kk20WTg03VHk51FTg02K^k20VTg02Lik30LTg01;5j2nTg00VNk10UTg00Vlk41ATg00Mlk41@Tg03WSk60qTg01ecS00k20dTg03X<k81?Tg02N4k40QTg00H>k21>Tg00d>k70aTg00g3k71=Tg00eEk80RTg00WOm<0TTg013Ak31;Tg013jk21:Tg00S0k31BTg00ZEk41CTg00dbk31DTg00fOk61ETg03YJk718Tg01M<k217Tg01E:k41HTg00bnm<0uTg00eimB16Tf2R8f1R9f0R:'T'Hp=hg00gWR;?=9:p=Zg00iZR</2:p=6129:,:8p=i1789/::p=_1189/0:p>0`1089/2:p=421>;:p>04P;P9g00l^P:H0Jp=}P9g00j_R=g00k>R>P>g00k^R?P:g00l>R@K0ap=kP8P=P>P>P?P;P9g00j8RAP:H0JP@K0ap=QP8P=P>P>P?P9P:K1=p={f6RBP=P>P>P?f5RCf4RDf3REP=P>P>P?P8P9P:L0RL0Rp=jg00nXRFg00o8S017=:p=>178900d:p=SP;PDPEP8P9P:J0ep=uPDPEP8P9H0[==C:p=Rg00>TRG?^9:p=MPDPEP8P9P:I1<Q015=Fp=I129:-0d8p>02PDPEP8P9H0o==C:p=sA<E89/::p>0>1:9:,:8p>0p12<E1089/2:':p=W109:,N8p=L159:,18p=A20v;:p=@g00?_RHP;P6P5P0g00hYPCPDPEP8P9P:N<0Tp>0mPHP;P4P5P7g02^FPCPDPEP8P9P:N<0Tp>0lB1;;9:p=Jg00mlR4g015_-1:9<1B:p=bP;P8P9P:H1Cp=B20j;:p=mB1D;9:p=FP9P=P>P>P?P:J1Ep>0IP8P=P>P>P?P9P:K18p>0HPEP=P>P>P?P8P9P:L0Rp=wPCP=P>P>P?PDP=P>P>P?P;PEPAP8H0JP@K0aP9P:L0Rp=d12<9/::p>0G1|89=^G:p=X20f<:p=q179:,:8p=?18899<DE/::p=[189:,78,:Ep=9f7R@PBPCPD1089,NEH0[;=:p=G189:9<E8p=v1189/0:,NEp=zP;PDPEP8P9P:J0]p>081:89017:p=OA~E89=^G:p=Y20@9:#3p=\PDPE1D89P:H07p>0Z1]9:9=E8p=pA<CDEA=;89/::':p=PPEP8P9P:H07,]Dp=UA=;89/::p=g1D9:-0@8p>0Y%39==;:p>0X12E8179:':p=`1289/::p>0:PCPD1089,NEP:H1HQ015=Fp=xPHPHP;P;P3P5P5PEg00h5P8P9P:N<0up>0=PHP;P;P;P5P5PCPDPEP8P9P:N<0up>05P;P;P;P;P;P;P1P:P9P8P1PEPDPCPBP@f8R1f9R5NB16p>09P;P;P7P@P7PBPCPDPEP8P9P:N<0Tp>0S109:,08p>0PP;P;P0P@P0PBPCPDPEP8P9P:N<0Tp>0rg00;h$06g00<gg00=oS02#yS03#yS04#yS05#y#y#yR0$0nR7$0iS06Q05$0nS07$0iR3$0wRA[&06Gg01F:R=PBPCPDPEH0<15E8S08=<B9Q03$0MR6&0M0R0+10RI,78RJP115CDS09PEP9H0hQ099h71Q09,11'ZP215BCS0:,15RK#6%6DS0;10KD;iI9_KIf;RKf:RL15@BS0<,TL1N7C;C5P1P@PBPCH0NH0<P8151@S0=,1K#6f<RM1551S0>'1RN%6@S0?10N@;iI7_IP2f=RN15L5S0@'1RO/7I%61S0A10O1;iIf?ROf>RP15KLS0B,TP1N75;CNPMPKPLP5H0NH0<P:15MKS0C,1O/7I%6KS0Df@S0E15NMS0F<0`K;iIP2%6MS0GfARQ15PNS0H'1?4MIfCS0IfBRR15OPS0J,TR1N7N;CQQ0EPOPPPNH0NH0<P:%6PS0KfDS0LQ0E,5QS0M'1?4OIfERS15RQS0N'TQ061N7QQ0621360S0O17<6%6017<I[[S0P%66RTg0119S0QB12609UWeS0RQ0Q%6I[^eTS0S&114S0T&064S0U&049&0~;S0V&0{;R4Q02-0j;S0W20^;6>0y;7S0X'},k4R6&0g>R>P420^;<S0YQ0W5Q4S0ZP>Q0Z={46Fj21N4?S0[P:P8Q01-0vFS0\21K:8#>dB1J;<9H1IS0]b@bBbCX5;S0^17:I%69R?%68S0_/:J[[^5;S0`P:PSPRPBO3b9b:b;,rR1H7:S0a/ZRQ06Q0afIRJfFS0b/5SS0c'1R6Q0LQ0a5463SR6PDPEPJP9fJRTfGR0Q0b'5RU'11H78S0d1H7DS0eQ0d54:7S:X?;PSQ0dfKRVfHRW/50S0f'1RXQ0d94X:3SX?;P:1H7EP8DuQ0ePQDuI1GWaW>Q06PAPDPEPJP9PJP9O1ER\6]>g03Ynp4p710R6p-0RX\:RY&069RZP2B0?89:A^D:8PDP9O1[^>ER[[A^E:9PEP9O1[^>8B0?E89[R\B0?DE8\[B0s89:P:n2001000000120000000WOWiWQP\^OZ^iY^Q6P:PGACDEJ:0bVTPWP0Q0bPSH0c>0OGWPJPWP0Q0bH0c>0OGJ,M:g03ZKp4p710R6PF\:RY&068RZP2B0OE8:9^E9A^D89PEP8O1#>':[R\A^E9:P8P9O1#>':B0ODE99^D8R[[A^CE8PDPEO1#>':\[PEP8P9P:H19P9n2001000000120000000WOX>9WkWQP\^OZ^>9^kY^Q6P:PGPVPTPJPWH0cP8PVP9O51M8VPVPTPJPWP8DI':P2fLR6,MEP6PVPTPJPEDIfPRYfORZfNR\9C51PDC;P:1MC\PZP\fMR[P6PBDIfSR]fRR^fQR_40bR`>0?GY1M:^fVRafURbfTRcP9C;[^>G[1M:_PbPcP]P9C;[^>GB0bc]^>0?G_[B0sG`YP6P@P9J15P]P^P_P@C;PcP]P^P_P8P9P:FV#>R`fXRdfWRePaPbPcP]P^PEP8P9P_P:N<14W1X<;XK;XN=15c]S0g,1eRfQ08,1eRg74^10g9<02f\`^<;^K;^N=PG1M:]PcP]P^P_P9DIPdPePaP8C;fYR`PdACRQePEC;]3]2]4P5g01jRS0hQ0hAt89:/M`fZRfP`PdPeAtE89DIf^Rgf]Rhf\RiAtDE8C;f_RjPgACW0hS0iAtCDEC;]3]2]4^n=^oHP:Q08?t9:/MiPhPif[RkPf15DES0j?t89DIfaRlf`RmPjQ09?tE8C;P2g00i;S0k#KS0l#KS0m#KS0n#KS0o#KS0p#K#K#KRn-01DPlQ0:%3DS0q&063Ro$0wRpfbRqPmQ0:,TlPD1flE-00D,]oEsH0>201CnQ0<%3CS0r5<qPpfcRrAC6VlQ0<,TqPC1fqD-00C,]oEs40pP:201BnfdRsQ0>%3@S0sPpfeRtPrQ0>,TsP@1fsB-00@,]oEsH0>P2Q0@%31S0t5<tPpffRuPsQ0@,TtP11ft@-001,]oEs2015nQ0B%35S0u5<uPpfgRvACYZtQ0B,TuP51fu1-005,]oEs40pP:Q0C%3L5<vPpfiRwPvfhRxQ0F'TPK1fxL-00K,]oEs201MnQ0H%3M5<wRyPpfjRzAC]^xR{Q0H,TwR|PM1fwK-00M,]oS0vEsRo':PCPyPoP9PpPzPxP|PMH0oPpfkRoACc]wQ0J,TzPNP:EsXLpPzP{PxPMP|20_:NPoQ0E/5OS0w%3PR|PEH0hQ0w9h7oQ0w,1oS0x'ZP2flS0yQ0M'1R{#6%3ORpP{PpPICW9_{IPAPePaQ0yfmR{Q0N5h7%3ES0z5L7RpQ0yPpO1ERPDfnS0{Q0I/5RS0|'1#6foS0}Q0LQ0I'5S0~'1S10%3RRpQ10PpPICW7_IP2fpS11Q0L7ASRp/7IQ0I#3Ry#6S1210py;iIPAPkPfQ11fqS13Q0c5h7Q0s5L7RyQ11PyO1ERP:frS14/1U/7IQ0b#3RUfsS15Q0f'1PUPICWP2%30S16#6ftRU15JWS17'1Q16;4IPAPjPgPUfuRy15TJS185h7%3K5L7RpPUPpO1ERP:%3J#6fwS19156VS1:'1S1;%3T;4IPjfxS1<15[6S1=5h7/0|S1>,N7S1?Q1>fyS1@fvRp;AyS1AQ1A/0US1B/2:5S:X?;PcP[P6%3VR}PWO4Q1<?AyUS1CQ15Q1<Q1='1R~3410~}Q1C402Q00Q1BQ1@15\[S1C'1S1D'2Q1D%36S1EQ1A34fzS1F15Z\S1G5h7Q0E#3S1H'0R~Q1FQ19;ApS1IQ1I/0yS1J/2~3SP:Q1JQ1FQ1G'1S1K'220_Q\%3QR~%3\S1L'7S1MPQP~%@~P\Q1LQ1L#@J0mQ0ECeS1LQ1M201Zn%3ZR~Q05$0MS1N'2S1OPZP~%@~PnQ1NQ1N#@S1PJ0lPWCeS1QQ1OQ0I#oS1RQ12Q0OQ0PQ0RQ0SQ0n-03;S0nQ0m-03;S0mQ02$0}-0|;S1SQ0l-03;S0l60k;Q0k-03;S1T'J'J'JQ0T'bQ0U&04DS1U&0z;R~7B8S1V&04CS1W9B~E7B9Q0VP4Q0YQ03#mS1X5Q4S1YP>P4Q02$0KS1Z#mS1[Q04#m'FS1\Q1Z$0K#mS1]5Q4P>P4P;Q0Wg00mEQ1]H0J,k4S1^P>20I4@S1_Q1\Q0WQ1X'FS1`5Q460H4S1aCwFjQ0[Q0]b@bBbCX5;X6;X7;X8;XF;XAX10EDS1b/2C1Z8B10CBS1cQ1b6021[[\?^5;^6;^7;^8;^F;^AXP:p+01BS1d15abS1e5h7S1fQ16'0S1gQ1df~S1hf}S1i3AS1j'7Q1dQ1e'1S1kf|S1lQ1jQ16Q1fPEPBPSO9b9b:b;bDb`b_W1P:O1Q1K%3[Q1I34Q1LQ1MQ1QQ1OQ1RQ12Q0OQ0PQ0RQ0SQ0nQ0mQ0lQ1T'JS0l'JS12'JQ0T'bS1RQ0UQ1W?BC~S1O?B8~Q1U9B~ES1Q7B9Q0VP4Q1XQ05#mS05'},k4S1MP>P4Q1]Q05'FS1LQ1[5Q4P>P4Q1^P>Q1`Q1['},k4Q1_60H4S1mCwFjQ0[Q0]b@bBbCX5;X6;X7;X8;XF;XAX179D10DCS1n/2ES1o1Z8CQ1b?SC1[[[^5;^6;^7;^8;^F;^AXP:Q1jQ1lQ1g34%3cQ1kQ1jQ16Q1fPCPBPSO9b9b:b;bDb`b_W1P:O1n200100000021100011000bLQ1?,H7Q1>20_PV17|}S1?PPP|%@|PVP}%@}J0mPNCeQ1?2016nQ1EQ1N'2R}P6Q1EQ1E#@PnQ1NQ1PJ0lPSCeP}Q0E#oQ1H#6Q0OQ0PQ0RQ0SQ0o-03;S0oQ0nQ0mQ1T'JS1T'JS0m'JQ0p-03;S0pQ1SQ0n60k;Q0l'J'JQ0T'b'bQ0UQ1U?BD~S1S?B8~S1H&04ES1P9B~DS1N7B9S1EQ0VP4Q1YP>P4Q1MP>P4Q1^P>P4Q1LQ0X5Q4P>P4P4Q0YQ1]P>Q0YQ1`5Q4Q1`Q0X'},k45{4S1LEdFjFjQ0[Q0]b@bBbCX5;X6;X7;X8;178DS1^1Z8DQ1c/2I%6BS1MQ1cQ1c/7I+0GS1c[[[[\?^5;^6;^7;^8;P:%3_Q1h15]^S1?'1S1fQ0L#3Q1hQ1?5h7PEPCPRPBPOO9b9b:b;bDb`b_'rDuO2WUWTP9P:O2n2001000000121000000W1WSP9P:O2n2001000000121000000W1WRP9P:O2n2001000000121000000c0CW|Z0MHJ0xQ0vP:J0]ClClY0@WMP9P:O2n2001000000121000000W1Y0EP9P:O2n2001000000121000000PqPlACVTmS0vQ0:?tDEC;eW3W2W4Xn=XoHXK;XN=P9P:O2n0110[00012110V10WWZP8P9P:O3Q0hQ0hAX9:ePdPePaPb1|89DIPiPkPf1|E8C;PhPiQ0b?CSkS1>1|DEC;]3]2]4^<=P:1589S16?X:fPkPfP`PdQ08/|9DIPjPgPhQ0j/|8C;P=Q0:?X:gP=PFP9%q:1a:I'cS1jPmPjPgPhP1P@P:FV'cg01\@S1kQ1kQ1kQ1kQ1kQ1kQ1kn011010008101071010Z3010410810X3010410810X3010410810X3010410810X4010:10910Z10;4010:10=10010Z#>PqQ0=PqP8%6:R}18rES1g7?:PrQ0@,1sS1p=L79O1Q07/N<Rn,]3R|5=A[^0;D[PrQ0>Q1gP}P:PsPDC9PAPZP\PsQ0B,1tS1g=L79S07P|ER[^0;H0>]3]2]4PEQ0<%E:S1q;Xj%q91a9I'cS1rPmPjPgPhP1P@P9FV'c#>PrQ0>Pr%E8S1sP}P:Ps%EES1tC9PsQ07O1==A|S07[^0;D[%qE1aEI'cS1uPqPlPmPjPLP5PEFVS1v<0\9Q1u#>S1wQ1v#>':P2%qD1aDI'c#>S1vPrPqPlPmPKPLPDFV#>PuQ0CPu%ECS1xP}P:Pv%EBS1yC9PAP^P_PvP7Q0H,1xS1zP9P|GG[^0;D[P:%qB1aBI'c#>S1{PuPtPsPrPPPNP@FV#>%q1S1|1a1IS1}<0\9S1~Q1|#>Q1}#>':S1}P2%q5#>S1|1a5I#>S20PoQ0MPo%ELS21P}P:Q0y%EKS22C9PAPePaQ0yP7Q0|,1{P9P|GGS0|[^0;D[P:%qK#>S231aMI#>S24P220f9:#>1289[S25129:S2620f89#>S27[Q2712E8[21M9:P9n2001000000120000000X=;X<;S27Q25^=;^<;S25P:P<PPP8O3S28Q0KP21a9:#>1789[S29179:S2:1a89#>R<[17E8\<21L9:P9n2001000000120000000X=;X<;S2;Q29^=;^<;S29P:Q0EPIPEO3S2<Q0E/7IS2=P2Q14Q0fQ14%EQS14CvQ15%ERS0f'8R<9?}:Q15P7PUQ18P9CzO1==A|[^0;Q15Q17P<Q0I#ES15,8UR<9?}:PAPjPgPUP715VTS2>,1yS2?P9P|GG[^0;H0>PPQ18=<U<%ESS2@,8pR<9?}:PpQ19Q1='1S1==L79O1==A|[^0;Q1:=<p<Q19Q0b#ES2A'8S2B9?}:PAPqPlQ19P7Q1<Q1C'1S2CP9P|GG[^0;P9Q0OQ0PQ0RQ0SQ0^Q0`P:PWP@P5O3b9b:b;,rSQ2@,fp,H7/ZSe1Z<SR<eP<Q0bA?}:9S2DPAPsPrQ1@Q1F15YZS2E'1S2F=L79R<P|ER[^0;X?;Q2BQ2DQ1@P<O1==A|[^0;X?;P9Q0bP:I08A?}:0Q1<Q1@Q1G'1S2G=L79O1==A|[^0;Q1<%E0S2H'8Q1@Q1G;<:X?;PEP0P9I08Q1<Q1C;<0P2Q2G#6Q2GPWQ2GPWPICW7_IA?}:TPAPuPtf{S1GP7Q1l15^_S2I'1S2JP9P|GG[^0;P:Q1G15_YS2K'1S2L#6Q2JPVQ2JPVPICW7_IP2Q1iQ1?'1R</7IP6P<P6PICWA?}:\PAPzPwp+01@S1?P7p+01AS2MQ1e'1R<P9P|GG[^0;P:Q1?15bcS1e'1/7IPZP<PZPICWP2%6YS2NQ1d15eaS2O'1?4YIA?}:^PAQ0{P{p+01DS1dP7p+01ES2P?Af`R<P9P|GG[^0;P:%6^A4<]IA?}:bPAp+01GS2Qp+01HS2R15hiS2S'1S2T/09S2U,N7S2VO1A=A:|XLAPOP9P:O2Q13Q11Q2QQ2VH0[Q0{Q2VQ2Up+01IS2Wp+01FS2XQ2P3AR<Q1d,0<S2Y/2:5S:X?;PrPhPiPaP\O4Q2RQ2PQ1d3AS2Zp+01CS2[Q2T34Q2T/0aQ2Z402Q00Q2YQ2W?AghS2Z'2Q2Z?4e<p+01JS2Z?AjgS2Y/0ES2TQ2ZQ2QQ2X3AS2XQ2XQ2P'0R<Q2T'23SP:Q2Y,2<Q0OQ0PQ0RQ0SQ12Q0T'bS12Q0UQ1VQ1P7B9Q0VP4P4Q1\Q0WP>P4Q1Y20I4BS1\5{4P>Q1aCwEdQ0[Q0]b@bBbCX5;X6;X7;X8;XAXXEXS1a108ES1V/2:Q0_/:CQ1nQ1V602@[[^5;^6;^7;^8;^AX^EXS1nP:p+01NS2T15rqS2\'1S2]/0@S2^Q2Tp+01KS2_Q2Z3AR<'717@iQ2WP<P@Q2]PEPBO8b9b:b;W1P:O1Q2YQ2X74dQ0OQ0PQ0RQ0SQ12Q0U&048S2XQ1Q7B9Q0VP4P4Q0WQ1]'FS1QQ1[P>P4Q1\Q1XQ1]'},k4S2Y5{4P>Q1mCwEdQ0[Q0]b@bBbCX5;X6;X7;X8;XAXXEXS1mA4:E8Q1^,:CQ1V?SD@[[^5;^6;^7;^8;^AX^EXS1^P:Q2WQ2^54<Q0?PiP<P@Q2]PEPBO8b9b:b;W1P:O1n200100000021100011000bLQ2V,H7Q2UQ0OQ0PQ0RQ0SQ0mQ0oQ0l'JQ0T'b'bQ0UQ2XQ1P9B~E7B9Q0VP4Q1YQ2Y5{4P>P4P4Q1QQ0XP>P4Q0ZP>Q1LCwEdS1LCwQ0[Q0]b@bBbCX5;X6;X7;S0ZA??98A49EIQ0_Q1bQ1b/7I+0G[[[^5;^6;^7;S0_P:P`PDQ2_15mjS1Q'1PEPCPPO6b9b:b;'rDuO2J0eW^X0;WUWTP9P:O2n2001000000121000000W1WSP9P:O2n2001000000121000000W1WRP9P:O2n2001000000121000000bMbYQ2BP:DubdClWYWMP9P:O2n2001000000121000000bWb1bVb1WWWVP9P:O2n2001000000121000000b2WfW2P9P:O2n2001000000121000000b2W3W2W4XO;P:O1Q0<&0F:S2B;XjQ1kQ015=FR<PrQ0>Pr&0F8S2UP}P:Ps&0FES2YC9Q07[^0;D[PFQ1kPFPXP:g01]ES07Q0Qn0110600020000XcFg0109Q01P9J0]S01Q07PtQ0BPt&0FDS0QCvP}P:Pu&0FCS2XC9PAP_PYPuP7Q0F,1vS0mP9P|GG[^0;;O:b1W3W2W4X<HP:O1g01]bS2VQ0BB0D89:S2];XrPvQ0FPvB0DDE8S2^P}P:PxB0DCDES1\C9PxQ0J,1wS2`=L79O1==A|S2a[^0;D[Q01Q07PwQ0JPwB0DBCDS2bCvP}P:PzB0D@BCS2cC9PAPbPcPzQ0M,1oS2d=L79S2eP|ERS2f[^0;;O:b1W3X2<W4XI=XH=WJP8P9P:O3Q2VQ0BB0C89:S2g;XrPvQ0FPvB0CDE8S2hP}P:PxB0CCDES2iC9Q2a[^0;D[Q01Q07PwQ0JPwB0CBCDS2jCvP}P:PzB0C@BCS2kC9Q2f[^0;;O:b1W3X2<W4XI=XH=WJP8P9P:O3g01^NS2lQ0BB0B89:S2m;XrPvQ0FPvB0BDE8S2nP}P:PxB0BCDES2oC9Q2a[^0;D[Q01Q07PwQ0JPwB0BBCDS2pCvP}P:PzB0B@BCS2qC9Q2f[^0;;O:b1W3X2<W4XI=XH=WJP8P9P:O3Q2lQ0BB0E89:S2r;XrPvQ0FPvB0EDE8S2sP}P:PxB0ECDES2tC9Q2a[^0;D[Q01Q07PwQ0JPwB0EBCDS2aCvP}P:PzB0E@BCS2uC9Q2f[^0;;O:b1W3X2<W4XI=XH=WJP8P9P:O3Q0FPEP8P9P:H0;S2f;XtPwQ0JPwPCPDPEP8H0;S2vP}P:PzPBPCPDPEH0;S2wC9PzQ2eO1==A|R|[^0;D[Q01Q07PoQ0MPoP@PBPCPDH0;S2eCvP}P:Q0yP1P@PBPCH0;S2xC9Q0|[^0;;O:b1W3X2<W4X[=X<HX\HX]FPEP8P9P:O4Q0FPEP8P9P:H0AS2y;XtPwQ0JPwPCPDPEP8H0AS2zP}P:PzPBPCPDPEH0AS2{C9P|[^0;D[Q01Q07PoQ0MPoP@PBPCPDH0AS0MCvP}P:Q0yP1P@PBPCH0AS2|C9Q0|[^0;;O:b1W3X2<W4X<HX0;XmHX]FPEP8P9P:O4n0110;000811103101013010410I1063010410I1063010410I1063010410I1064010:10910110;4010:105100101P8P9P:O3PmPjACJWgS0|Q09/|EC;eW3W2W4X[=XK;XN=P9P:O2n0110[00012110V10WWZP9P:O2Q0hQ0hP8P9P:P`CYPfP`PdPeA~E89DIPgPhPiA~DE8C;PjPgQ0iA~CDEC;]3]2]4^KH^<=P:Q08P9P:PiCYPhPiPkPfQ0j?~89DIPlPmPjQ09?~E8C;P=Q0<P:PDPmCYP=PFP9Q1jPqPlPmPjP5P1P:FV'cQ1kQ1kQ1kQ1kQ1kQ1kQ1kn011010008101071010Z3010410810X3010410810X3010410810X3010410810X4010:10910Z10;4010:10Y10010Z#>PsQ0>18s8R|1DsB,\3P|18tES1k9?}:PAPtP7PuQ0BP9CzO1P3P3&0t9R|PuP1PnI0ZCp[^0;EPPtQ0@Q1k1Dt@,\3S0BQ1kP}P:PuPDC9PAP_PYPuP7PvQ0CP9CzS1kP3P3P|1Dv5S1jPnDUS0iER[^0;EP]3]2]4PDQ0=Q1qPCPlCYQ1rPqPlPmPjP5P1P9FV'c#>PtQ0@Q1s,8tS1sQ0BQ1sP}P:PuQ1tC9PuQ1kO1Q0i5=AS0i[^0;EPQ1uPsPrPqPlPKPLPEFVS1k<0\9Q1wQ1k#>':P2Q1vPtPsPrPqPMPKPDFV#>PxQ0FQ1x,8xS1x1DxL,\3Q1xP}P:PwQ1yC9PAPcP]PwP7Q0J,1zP9P3P3P|1DzMPnDUGG[^0;EPP:Q1{PxPvPuPtPOPPP@FV#>Q1~Q1}P2Q1|Q20P{Q0NQ21,8{S211D{OS20,\3S1|Q21P}P:Q0{Q22C9PAP`PdQ0{P7Q10P9P3P3P|Q0}/DQPnDUGGS10[^0;EPP:Q23Q24Q27Q25Q28Q0KQ2;Q29Q2<Q2=P2Q17Q14,8US145<UQ0b,DU,\3Q14Q0f,8yS0f9?}:PAPyP7PpQ2>P9CzO1P3P3P|PpPWPnI0ZCp[^0;3gPyQ18Q0f1Dy0,\3Q0fQ15,8pS159?}:PAPlPmPpP7Q1;P9P3P3P|Q19/DJS1;PnDUGG[^0;EPPPQ2>Q155<pQ1;,\3Q19Q0L#E'8Q1<Q2@'8S2@9?}:PAQ1<Q1D=L79O1P3P3P|Q1@/DVS1DPnH07Cp[^0;3gP2Q1<>0Y3TQ2@+0XQ1@Q2A'8S2A9?}:PAQ1@Q1K=L79O1P3P3P|Q1F/D6S1KPnH07Cp[^0;Q1@Q1CQ2AQ1D,\3Q2AQ1FQ2H'8S2H9?}:PAPtPsQ1FP7Q1GQ2E'1P9P3P3P|Q1G/D[PnDUGG[^0;EPP:Q1K-0@3Q2H+0XQ1l%EJS2H'8S1K9?}:PAQ1lP7Q1iQ2IP9CzO1P3P3P|Q1iPZPnI0ZCp[^0;Q1lQ2KQ1K3<Q1l>0Y3\S2K#3S2IQ1K'ZS2EQ1i%ET'8S1F9?}:PAPxPvQ1iP7Q1fP9P3P3P|Q1h/DYS1fPnDUGG[^0;S2A':PCQ2EQ2AP9Q2K#oQ2I#6Q0OQ0PQ0RQ0SQ0^Q0`P:P[PMPPO3b9b:b;bD,rJQ1lQ2H'f,H7/ZJeQ1K/ZJS1KeQ1KPTQ2DPAPzPwQ1?Q2MQ1e'1S1K=L79S2HP3P3P|Q2M/D^PnDUS1lER[^0;X?;Q1FQ2DQ1?Q2HO1Q1l5=A[^0;X?;P9PTP:I08A?}:VPAQ1hP7Q1?Q0gP9CzO1P3P3P|Q1?/D_S2DPnH07Cp[^0;Q1h%EV'8Q2D-0@300X:X?;PEPVP9I08Q1f-0@300XVQ1?%E6'8Q2MQ1e;<:X?;P1P6P8I08Q1?Q0g;<6P2Q1K#6Q1KP[Q1KP[PICW7_IA?}:ZPAP{Q0yQ2[P7Q1d15deS1K'1S1eP9P3P3P|Q1d/DbPnDUGG[^0;P:Q2[Q2O'1#6Q1eQ2NQ1e/0Y;iI7_IP2Q2P?A`dS2P/7IP_Q2PP_PICWA?}:]PAQ13Q11Q2QP7Q2R?AikS2PP9P3P3P|Q2R/D`PnDUGG[^0;P:Q2Q?Akf/7IPcQ2PPcPICWP2%6bQ2WQ2S'1?4bIA?}:ePAPyPUQ2_P7p+01LS2WQ1Q'1S1QP9P3P3P|Q2W/DhPnDUGG[^0;P:%6eQ1Q?4dIA?}:fPAQ2Tp+01OS1QQ2\'1S2\/09S2S,N7S2PO1PAP:P3P3&0t8p+01PS2QPlPnI0ZCpXLAQ0EP9P:O2Q1<Q19Q2TQ2PH0[PyQ2PQ2SQ2Qp+01MS2RQ2W3AS1eQ1eQ2_'0S2N/2:5S:X?;PzPrPqPkP]O4Q1QQ2WQ2_3AS2_Q2ZQ2\34Q2\/0kQ2_402Q00Q2NQ2Q?AsrS2Q'2Q2QQ1e74ip+01QS2Q?AtsS1e/0ES2NQ2QQ2TQ2R3AS2RQ2RQ2W'0S2WQ2N'23SP:Q2WQ1e'2p+01RS2W>0Y3rS2N#oS2TQ2N#3#6S2NQ0OQ0PQ0RQ0SQ1aQ1nP:p+01VS1n?AzwS1a/01S2_Q1np+01SS2\Q2W3AS1n'7171qQ2QQ1nP1Q1aPDP@O8b9b:b;bDW1P:O1Q1eQ2R74hQ2TQ2NQ0OQ0PQ0RQ0SQ1mQ1^P:Q1nQ2QQ2_34Q0APqQ1nP1Q1aPDP@O8b9b:b;bDW1P:O1n200100000021100011000bLQ2P,H7Q2SQ1Q>0Y3mS1Q#oQ1Q#3#6Q0OQ0PQ0RQ0SQ0ZQ0_P:PjPCQ2\?AvuPDPBPOO6b9b:b;bD'rDuO2J0eW^X0;WUWTP9P:O2n2001000000121000000W1WSP9P:O2n2001000000121000000W1WRP9P:O2n2001000000121000000bMbhbYQ1FP:DubdClClWYWhP9P:O2n2001000000121000000W1WMP9P:O2n2001000000121000000bWb1bVb1WWWVP9P:O2n2001000000121000000b2WfW2P9P:O2n2001000000121000000b2W3W2W4XO;P:O1Q0=Q2BPCPlCYPtQ0@Q2U,8tS2UQ0BQ2UP}P:PuQ2YC9Q0i[^0;EPQ01Q07Q0CQ0Q,8vS0Q5<vQ1j,\3Q0QP}P:PxQ2XC9PAP]P^PxP7Q0H,1wP9P3P3P|1DwKR]PnDUGG[^0;3g;O:b1W3X2<W4X<HP:O1Q2VQ0CQ2]P5PtCYPwQ0HQ2^,8wS2^1\3]S2]Q2^P}P:PzQ1\C9PAPzQ0x=L79O1P3P3P|1DoNR]PnH07CpS0x[^0;EPQ01Q07Q0wQ2b,8oS2b5<o1\3]R]Q2bP}P:Q0yQ2cC9PAPePaQ0yP7P{Q0NP9CzS2cP3P3P|Q20PnDUS20ERRn[^0;3g;O:b1W3X2<W4XI=XH=WJP8P9P:O3Q2VQ0CQ2gP5PtCYPwQ0HQ2h,8wR|Q2]P|P}P:PzQ2iC9Q0x[^0;EPQ01Q07Q0wQ2j,8oR|5<oP}P:Q0yQ2kC9Pn[^0;9g]|;O:b1W3X2<W4XI=XH=WJP8P9P:O3Q2lQ0CQ2mP5PtCYPwQ0HQ2n,8wR|Q2]P|P}P:PzQ2oC9Q0x[^0;EPQ01Q07Q0wQ2p,8oR|5<oP}P:Q0yQ2qC9Pn[^0;9g]|;O:b1W3X2<W4XI=XH=WJP8P9P:O3Q2lQ0CQ2rP5PtCYPwQ0HQ2s,8wR|Q2]P|P}P:PzQ2tC9Q0x[^0;EPQ01Q07Q0wQ2a,8oR|5<oP}P:Q0yQ2uC9Pn[^0;9g]|;O:b1W3X2<W4XI=XH=WJP8P9P:O3Q0HQ2fPKPvCYPoQ0wQ2v,8oR|P]P|P}P:Q0yQ2wC9Q0yQ2cO1Q205=AR|[^0;EPQ01Q07Q0NQ2e,8{Rn5<{Q1|P}P:Q0{Q2xC9Q10[^0;7gn;O:b1W3X2<W4X[=X<HX\HX]FPEP8P9P:O4Q0HQ2yPKPvCYPoQ0wQ2z,8oRnP]PnP}P:Q0yQ2{C9P|[^0;EPQ01Q07Q0NQ0M,8{R|5<{Q1|P}P:Q0{Q2|C9Q10[^0;7g|;O:b1W3X2<W4X<HX0;XmHX]FPEP8P9P:O4n0110;010811103111013110410I1063110410I1063110410I1063110410I1064110:10910110;4110:105100101P8P9P:O3PqPlQ0vQ0:?~DEC;eW3W2W4Z0LHX[=XK;XN=P9P:O2n0110[00012110V10WWZP8P9P:O320W9:/MaPePaPbPc20W89DIPkPfP`20WE8C;P2Q0;PCP:P:PDC`Pi1N79RFO1&0g3R35=A[^0;:0:EIPBP:P:PCC`PAPWP0PhPFP3ER[^0;:0:DI-0GCP:Q1MP1P:P:P@C`PjPFO1==A3[^0;:0:BIP212@IP5P:P:P1C`PmPFO1==A3[^0;PLP:P:P5C`PAP6PVPlPFP3ER[^0;:0:1I-0G5P:125IPMP:P:PKC`PrPFO1==A3[^0;Q0G12KIR6PNP:P:PMC`R<PAPZP\PsPFP3ER[^0;R3':PCP6P3P9PZP\PsPFP8P9P:O2I1FX^<X0;ClClW~WxP9P:O2n2001000000121000000W1WwP9P:O2n2001000000121000000PiPkQ0L=CSfR<20WDEC;eW3W2W4Xl;X\;P9P:O220V9:/MaPePaPbPc20V89DIPkPfP`20VE8C;P:PiPkP<20VDEC;eW3W2W4X=;Xc=P9P:O2B0L89:/MdP`PdPePaB0LE89DIPhPiPkB0LDE8C;P:PgPhQ0b=C0iB0LCDEC;eW3W2W4Xl;X\;Xc=P8P9P:O3Q0hQ0h1n9:/MePdPePaPb1n89DIPiPkPf1nE8C;PhPiQ1>1nDEC;]3]2]4^<;P:Q16/n:/MfPkPfP`PdQ08/n9DIPjPgPhQ0j/n8C;P2Q09=<jE%39Ri,08Re/2BPsPqP7Q0>,1rRqPEP8Ex[\?^=H^G;PmQ0:PD12e@PtAC\[rP7Q1pPEP8Ex[\?^=H^G;H0>P:Q0<=<lC12e5PvPtP7Q0C,1uRtPEP8Ex[\?^=H^G;Q0>=<r@12eLPxAC_YuP7Q0mPEP8Ex[\?^=H^G;P9P2%6qQ0?10q@;iI9_qI12eKPwAC^_vP7Q1zPEP8Ex[\?^=H^G;P9Q1g#6PLPtPLPICW9_tIP2Q0m/7IQ0DQ0m/0K;iI12eOP{ACaboP7Q0yQ0N'1PEP8Ex[\?^=H^G;P:Q2`/7IQ0KQ0w>0`zP;iIP2%6OQ2d?4OIQ0I,2eQ13Q0}9Cf`P7Q11Q0c'1PEP8Ex[\?^=H^G;P:%6QQ0{Q0~'1?4RIQ0b,2ePH%3:Re=4DWPpACjgUP7Q2?PCP9Ex]XP8Q0k#3=4E0Q0\WX%K:#3=4CJQ19PyACmjyQ1:>0`pBRy,N7RU%K9RQPy%K8#3R2=4:IX?;%3QRz,0yRo/2IQ02$0MR{,0iRt,0yRv/2IP:X>;RwQ26$0UXp;X>;RqPoPvPwPwPwP;P;g010U109:H1A#@X=;X<;RvPyPy%@yPzPtPwPw%@eX>HRePQPt10:{X>;RoP9Pi%@iH0=RuJ05N:09PIPI%@IL0S10BzRY/2TA4BtTRtPwPqPYPwPoPiO1RiO1RY,0BPwPwPwPvPBPB%@BPzPYPwPwPePQPiPuJ05N:09PTPT%@TL0SP:CeRuPt%o8Ri%38#6RYQ0OQ0PQ0RQ0SQ12Q0UQ1HQ1P7B9Q0VP4P4Q1XQ1[20^;{Rz'FRx'FQ05P>P4P4Q0WQ05'FQ0XP>Q1`/FxQ0X5Q4EdEdQ0[Q0]b@bBbCX5;X6;X7;X8;108{=49EA49DIQ1V10D{Rx;4I[[^5;^6;^7;^8;P:PZ%3BRrPKQ2LPDPMO6b9b:b;bDbPH1@1H7UPuPtPiPYQ0OQ0PQ0RQ0SQ0pQ0oQ1T'J'JQ0nQ0l'JQ0T'b'bRYQ0UQ1EQ0VP4Q0YQ055Q4RiP>P4Q1XQ05/Fz'FQ1]5Q4P>P4Q1YP>Q1LCwRtFjQ0[Q0]b@bBbCX5;X6;X7;X8;%6ERuA48xE10ECRx/2IQ0;Q1c[[\u[[^5;^6;^7;^8;RuP:PrPZPKQ2LPEPDP5PMPSO9b9b:b;bDbP,ryDuQ06Q1==L7@,H7RyQ0aQ0a10y2C`Q2C/01Ry,N7,H7R2P:Q0dQ0d%KDRr#3RI,0:C`X?;P:Py1H79RU,22Rl%KERs#3R<,02Rc,7URF':Q0z>0P2{9?lUR3PlPFPlPwPoQ0zO1RFO1R6,02RA,7U&0UlPwQ2:$0UXp;X>;RlPUPU%@UPcPAPwPwPwPvP2P2%@2P<P6PwPwPePsPFPoPEQ0zQ0z#@H0=J05N:09L0rJ0qP:CeP3105IR3/2[Q0q/0{=45[RFPwPqP3PwPoQ0qO1R3O1Rs,05PwPwPwPvP5P5%@5PIPsPwPwPePrP3PoPDQ0qQ0q#@H0=J05N:09P[P[%@[L0SPECePF%oCQ0r#6Q0OQ0PQ0RQ0SPYQ0UQ1S9B~8Q1N7B9Q0VP4P4Q0YQ03$0K#y#mRYP>P4P4Q1X1FYz'FQ1]P>PtEdEdQ0[Q0]b@bBbCX5;X6;X7;X8;PuP:Q0uP^PPQ1hQ0g'1PEPDPMPOPWO9b9b:b;bDbPbb,ryI08PyPUPU10y<C`PmP8PbPZP\P[PVO4Q1BQ2G'2Q2G/0[Q1A402Q00Q1JQ2F'2Q2FQ1I74\Q0eQ1GQ1<Q193AR\10\pRpQ0e'23SP:Q2L,2pQ2J/0MRM1H7CRp'2R[%K@RV#3Rb,0MR<,7pRy':Q0s>0PM{9?[pRUP[PyP[PwPoQ0sO1RyO1RO,0MRP,7p&0U[PwPlPpPp%@pP<PPPwPwPwPvPMPM%@MPbPOPwPwPePVPyPoP@Q0sQ0s#@H0=J05N:09L0rJ0qPECeRyPU%K1RV#3RO,0NRb/2_Q0t/0{=4N_RMPwPqPbPwPoQ0tO1RbO1Rq,0NPwPwPwPvPNPN%@NPOPqPwPwPePVPbPoP1Q0tQ0t#@H0=J05N:09P_P_%@_L0SP@CeR_PM%o5RoQ0u#6RbQ0OQ0PQ0RQ0SQ1RQ0UQ1OQ1U7B8Q1P7B9Q0VP4Q1Z#y#mRVQ05'FReQ0W5Q4Q1_5{4P>P4Q1XQ1['FRw=Q4VP>P4PiP>20I41R1Q0W9Q4w60H4CwFjQ0[Q0]b@bBbCX5;X6;X7;X8;XF;XAXXEXQ1b@0::CQ1V/2DQ1MQ1o-0d5[[[^5;^6;^7;^8;^F;^AX^EXP:1H7KRKQ2[Q1?Q1h3AR7'7Q2[Q1K'1Rw/0RRi%3NRN<0P{,7KPRPwQ1iP7PKPCPBQ0EO:b9b:b;bDbPbbW1P:O1Q2L?4Z\PyPUP_PMPoPbQ0OQ0PQ0RQ0SQ1RQ0UQ1W?BB~Q1P7B8&04B?BB~Q1U7BB7B9Q0VP4P4Q05Q04$0K#m/FzRz'FQ1]P>P4Q0W1Fez'},k49{41P>P4Q1],FVQ1X5Q4P>Q0WQ1X'},k420I4560H4FjEdQ0[Q0]b@bBbCX5;X6;X7;X8;XF;Xj;XAXXEX10C{=4DEB0PxB{9?@9Q1oASEDL[[[^5;^6;^7;^8;^F;^j;^AX^EXP:Q1i=47K12iKPNPRPaPwP7PKPDPCPBO;b9b:b;bDbPbbW1P:O1n200100000021100011000bLO2baWaW>Q0IPBPQPDP:O4L1?WXX=HP:O1n0110100020011101P:O1WXXz?X=HXG;WUWTP9P:O2n2001000000121000000W1WSP9P:O2n2001000000121000000W1WRP9P:O2n2001000000121000000ClY0AWMP9P:O2n2001000000121000000PmPjQ0|Q09/nEC;eW3W2W4X<;XK;XN=P9P:O2n0110[00012110V10WWZP9P:O2Q0hQ0hPEP8P9P:H0Q/MfPkPfP`PdPDPEP8P9H0QDIPjPgPhPCPDPEP8H0QC;P:PmPjQ0|PBPCPDPEH0QC;eW3W2W4Z0P;Y0KZ0O;Y0JPEP8P9P:O4n0110500083110I10?10>2110I1013110I1011052110910<2010;1023010;10910<2110I1014010J10O10K10PPEP8P9O3bqb3W2W4P9P:O2n2001000000121000000bgb1WgZ0FGO4b1PTPJACE8WP0Q0bPSQ0LH0NH0<ec0Hb}c0Qc0IWvWuP9P:O2n2001000000121000000W1WtP9P:O2n2001000000121000000W1WsP9P:O2n2001000000121000000c0BY0DW{WyZ0U;Z0T;Y0SY0NY0GWrY0Ro"). Qed.
End VP38.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Ltac p6_sr_body sr k := tryif is_var sr then (let b := eval cbv delta [sr] in sr in k b) else k sr.
