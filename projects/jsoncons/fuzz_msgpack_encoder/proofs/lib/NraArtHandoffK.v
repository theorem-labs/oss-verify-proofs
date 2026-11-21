(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: changed AH, RESV0, SINV and 42 more; added abrt, apc, execfn and 10 more; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/As0ArtHandoffK.v, 261 lines within its lines 168-1192. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BackingAlgebra. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3SoundK AxSymRun3K AsanPlanSoundK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BackingAlgebra OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.AsanPlacement OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023.AsanCeil OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AxSymExec3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3SoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymRun3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanCoreK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanInitK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0DefsK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0PlanImagesK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffBridgeK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffLedgerK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffBInvK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffCellsK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffRolesK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0HandoffK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0ArtCellsK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0BssZeroK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.AsanNodesLibEK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.AsanNodesMmLibK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffLazyK.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0086. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0085. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0078. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require NatInitCache. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003.As0Tables OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtRunsMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0086.NatLeaf OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0086.NatPoison OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0085.NatRzLog OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0085.NatAllocA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0085.NatCls OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0078.NatDepotA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0078.NatDepot OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtRuns OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.ArtBridge OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.NatInitCache OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.NarInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.NarFsInv. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). Local Ltac lia := L5FastLiaT.plia2.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0251. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0251.NarCreditT.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_tL_NraArtHandoffK () := "C46Stdlib5Lists4List2InC47Corelib4Init9Datatypes3fstC35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C46Stdlib5Lists4List7forallbK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes3nat02C47Corelib4Init5Peano2ltI46Stdlib9micromega7EnvRing5PExpr00c49OSSVerify5KrLib>NraArtHandoffK<art_sym_listC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthK47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib7Mh_0132=HandoffRolesK5rbaseC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK4botEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK2uEC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02I46Stdlib9micromega=RingMicromega5Psatz00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02I46Stdlib9micromega5Tauto8GFormula00I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC47Corelib4Init5Logic3iffc49OSSVerify5KrLib>NraArtHandoffK6as0_rnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv5rn_tpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv7rn_loffC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib7Mh_01456NarInv5rn_arC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5ar_fsC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK2bKC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltI47Corelib5Lists7ListDef6Forall00C47Corelib5Lists7ListDef3nthC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3divc49OSSVerify5KrLib>NraArtHandoffK4topEC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib7Mh_00356ArtMem5apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv7rn_dtlsC1?~~~~~~~~~~~~~~~I46Stdlib9micromega6VarMap1t00C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega:ZMicromega=Zeval_formulaK47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv5rn_qsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv4rn_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv6rn_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv7rn_parrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:Forall_nthC46Stdlib5Lists4List=Forall_forallC46Stdlib5Lists4List>forallb_forallC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2I47Corelib4Init5Logic3and00C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr05I47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegI47Corelib4Init5Logic2or00C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega6VarMap1t01C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init5Logic3notI47Corelib4Init5Logic2eq00C59OSSVerify5KrLib7Mh_01456NarInv:art_run_okC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK3rglC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK2bTC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK4xposC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK2bCC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK2bFC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modK47Corelib4Init5Logic2ex01C46Stdlib9micromega;ZifyClasses9and_morphc49OSSVerify5KrLib>NraArtHandoffK7rg_holeC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK6rg_imgC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK6ra_subC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02c49OSSVerify5KrLib>NraArtHandoffK2bDC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_01456NarInv6rn_tsdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv8rn_kbaseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv6rn_keyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv5rn_l2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv6rn_blkC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3ltbK46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02C46Stdlib9micromega6VarMap4findC46Stdlib9micromega5Tauto7eval_bfK46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib5Arith8PeanoNat3Nat6ltb_ltK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega6VarMap1t03C46Stdlib9micromega;ZifyClasses9not_morphK47Corelib4Init5Logic3and01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes3nat00K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums8positive00K47Corelib4Init9Datatypes3nat01c49OSSVerify5KrLib>NraArtHandoffK8I_KSPACEC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK6I_PARRC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK8I_THREADC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK5I_CTXC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK4I_L2C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK5I_BLKC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK6I_FAKEC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK6I_DTLSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5e_sp0C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00c49OSSVerify5KrLib>NraArtHandoffK7sp0_winC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK6spb_qsC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK2TPC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK3TSDC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK4LOFFC1?~~~~~~~~~~~~~~~". Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac2 kr_t_NraArtHandoffK () := "C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List7forallbI47Corelib4Init9Datatypes4list00c49OSSVerify5KrLib>NraArtHandoffK8all_trueC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes8list_indI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init5Logic4True01C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3hop02C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK6hsplitC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indK47Corelib4Init9Datatypes6option02C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K8expr_eqbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbK47Corelib4Init5Logic2eq01K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3hop01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C47Corelib4Init5Logic7f_equalC35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK;expr_eqb_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rK47Corelib4Init9Datatypes4prod01K47Corelib7Numbers7BinNums8positive02C47Corelib4Init9Datatypes3appI69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3hop00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib7Mh_00438AgentLib7u64_litC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6edenotC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib>AsanPlanSoundK4APSK2uEC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K3env00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_00039As0Tables7AsanTab:class_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC69OSSVerify5KrLib7Mh_00039As0Tables7AsanTab6zrangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_ltC46Stdlib5Lists4List2InC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00039As0Tables7AsanTab8in_ziotaC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib7Mh_0117;Na0HandoffK7as0_chkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6a_mapsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6no_fogC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_hnaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132>HandoffLedgerK<hops_in_mapsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_hlzC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK2knC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132>HandoffLedgerK9vis_sh_wrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_visC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132>HandoffLedgerK<vis_off_bandC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7a_ghostC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8amap_eqbC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7am_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K3xloC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01178Na0DefsK5ASAN0C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4amap00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132<HandoffBInvK5M_LOWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132<HandoffBInvK5M_GAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132<HandoffBInvK6M_HIGHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117;Na0HandoffK5RESm0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132=HandoffCellsK8chk_wordC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K5saddr01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK4flatC1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC59OSSVerify5KrLib7Mh_01329AsanInitK5SINV0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01329AsanInitK5argH0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132=HandoffCellsK7hc_wordC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib7Mh_00356ArtMem4cellC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib7Mh_01178Na0DefsK6ASEGS0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01329AsanInitK5LIMITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01178Na0DefsK4APH0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117>Na0PlanImagesK=asan0_in_hullC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117>Na0PlanImagesK=asan0_hull_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117<Na0ArtCellsK7art_litC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib5Arith8PeanoNat3Nat3eqbC47Corelib4Init9Datatypes3sndI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib5Arith8PeanoNat3Nat6eqb_eqc49OSSVerify5KrLib>NraArtHandoffK5cellLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117<Na0ArtCellsK8ART_LITWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132=HandoffCellsK8chk_zeroC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02I47Corelib4Init5Peano2le00C59OSSVerify5KrLib7Mh_0132=HandoffCellsK<hc_zero_cellC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib7Mh_0132=HandoffCellsK6chk_wrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132=HandoffCellsK5hc_wrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00356ArtMem2wrC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK<art_sym_listC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK;all_true_ofC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthc49OSSVerify5KrLib>NraArtHandoffK4spbEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K9split_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5eaddzC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK2bPC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK2bCC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK2bTC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK4topEC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK4botEC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK2bKC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK2bFC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subc49OSSVerify5KrLib>NraArtHandoffK3bL2C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK4bBLKC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK3tfEC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK9is_var_inC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK3stEC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK4e_atC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK9img_coverC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132=HandoffRolesK4roleC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK7xlo_posC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK2bDC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK6vis_inC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK8glob_chkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02C46Stdlib9micromega;ZifyClasses;rew_iff_revc49OSSVerify5KrLib>NraArtHandoffK7lit_lenC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK3TSDC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK2TPC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK2B1C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK2B2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117;Na0BssZeroK6DEP_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117;Na0BssZeroK6DEP_HIC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK8I_KSPACEC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK6I_PARRC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK8I_THREADC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK5I_CTXC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK6I_FAKEC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK4I_L2C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK5I_BLKC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK6I_DTLSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5e_topC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK9e_stk_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01458NarFsInv;ART_GLOBALSC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib>AsanPlanSoundK4APSK6co_ispC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spC59OSSVerify5KrLib>AsanPlanSoundK4APSK8pagedownC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr07C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5e_sp0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6e_sppgC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C47Corelib4Init5Peano2ltC47Corelib5Lists7ListDef3nthC46Stdlib5Lists4List:Forall_nthC46Stdlib5Lists4List=Forall_forallC56Stdlib5Arith8PeanoNat3Nat3ltbC56Stdlib5Arith8PeanoNat3Nat6ltb_ltC59OSSVerify5KrLib>AsanPlanSoundK4APSK;amap_eqb_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6am_lenC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01c49OSSVerify5KrLib>NraArtHandoffK6uE_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132=HandoffRolesK5rbaseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132=HandoffRolesK4rlenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132=HandoffRolesK8role_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132=HandoffRolesK8role_geoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6img_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6img_hiC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC47Corelib4Init5Logic3notC46Stdlib9micromega;ZifyClasses9not_morphC59OSSVerify5KrLib7Mh_0132=HandoffRolesK:role_apartC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04I47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula06c49OSSVerify5KrLib>NraArtHandoffK5len17C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z6inj_lec49OSSVerify5KrLib>NraArtHandoffK5nofogC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK;role_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK2MrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7co_knowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK9xlo_soundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z7div_modC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr05c49OSSVerify5KrLib>NraArtHandoffK2rgC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphc49OSSVerify5KrLib>NraArtHandoffK2raC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C59OSSVerify5KrLib7Mh_00356ArtMem5apartC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK6as0_rnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv:art_run_okC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK3rglC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK4xposC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K46Stdlib9micromega:ZMicromega;ZArithProof03c49OSSVerify5KrLib>NraArtHandoffK7rg_holeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv7rn_dtlsC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK6rg_imgC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK6ra_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv5rn_arC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv5rn_qsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv4rn_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv6rn_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv5rn_tpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv6rn_tsdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv8rn_kbaseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv7rn_parrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv6rn_keyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv7rn_loffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv5rn_l2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv6rn_blkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5ar_fsC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK7sp0_winC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK6spb_qsC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK4LOFFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK?split_lit_denotC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses:impl_morphC4ELinuxProcessSemantics5Riscv3Sem5alu64C56Stdlib6ZArith6BinInt1Z9mod_smallC59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7u_add64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K5mkAluC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK;mkAlu_denotC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01c49OSSVerify5KrLib>NraArtHandoffK7spb_valC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebK69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry04C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init9Datatypes?andb_true_introC59OSSVerify5KrLib>AsanPlanSoundK4APSK7in_hullC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132>HandoffBridgeK6hb_imgC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry09C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry0:C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K5saddr00C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK5cellWC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK6cellLbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv>art_rt_staticsC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK3uE0C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK7ris_valC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK8got_noneC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK3wrKC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_stack_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA?ar_stack_bottomC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv=art_rt_threadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117;Na0HandoffK=as0_chk_partsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7am_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0035:ArtRunsMemAart_wr_of_definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132>HandoffLedgerKAhl_shadow_definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117>Na0PlanImagesK?asan0_shadow_okC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5mkind00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132>HandoffLedgerK6SHB_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132>HandoffLedgerK7SHB_LENC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okc49OSSVerify5KrLib>NraArtHandoffKBas0_art_rt_primaryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv5g_clsC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK>class_size_posC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv6rn_spbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00856NatCls;art_cptr_okC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00856NatCls7art_cls01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00856NatCls5cl_auC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00856NatCls5cl_muC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00856NatCls8cl_cacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00856NatCls7cl_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv7art_gs0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv4g_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv=art_chunk_hdrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ;shadow_blkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv7art_lchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv4g_qtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv4g_qgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv>art_in_batchesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv7bt_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv=art_rt_chunksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA1SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7byte_atC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_01456NarInv7art_cst00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_01456NarInv7art_cst01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00856NatCls8art_cls0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_01456NarInv9art_batch00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC47Corelib4Init3Nat3addC59OSSVerify5KrLib7Mh_0117<Na0ArtCellsK9cell0_catC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC46Stdlib9micromega8ZifyInst7Inj_Z_Zc49OSSVerify5KrLib>NraArtHandoffK>as0_art_rt_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv>art_batch_listC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C59OSSVerify5KrLib7Mh_01456NarInv8bt_itemsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_01456NarInv7art_cst03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv5g_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv7sc_quarC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv4sc_uC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv4sc_nC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8flat_mapC47Corelib5Lists7ListDef3mapc49OSSVerify5KrLib>NraArtHandoffK5cellZC1?~~~~~~~~~~~~~~~K35stdpp4base5NoDup01C59OSSVerify5KrLib7Mh_01456NarInvAart_batches_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv;art_rt_quarC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_01456NarInv7art_cst04C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_01456NarInv7art_sec00C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK9lock_quarC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv4g_iaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv9art_rt_iaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:kentry_eqbC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK=kentry_eqb_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132>HandoffBridgeK5hb_knC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK9kentry_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr08C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv5Instr5aluop00I4ELinuxProcessSemantics5Riscv5Instr5mulop00C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC59OSSVerify5KrLib7Mh_0117;Na0BssZeroK@as0_dep_rdn_zeroC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatC59OSSVerify5KrLib7Mh_0132=HandoffCellsK9wleb_zeroC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK@as0_art_rt_depotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00856NatCls6cl_mfaC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib<NatInitCache9art_ic_mcC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib<NatInitCache?art_ic_mc_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv<art_rt_ghostC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffKAas0_art_alloc_repC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_01456NarInv6art_gs00C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffKAas0_art_rt_chunksC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK?as0_art_rt_quarC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK=as0_art_rt_iaC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK@as0_art_rt_ghostC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132=HandoffCellsK7hc_zeroC1?~~~~~~~~~~~~~~~I46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr05K46Stdlib;setoid_ring<Ring_polynom5PExpr06I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterI46Stdlib;setoid_ring<Ring_polynom3Mon00K46Stdlib;setoid_ring<Ring_polynom5PExpr07C56Stdlib6ZArith6BinInt1Z4to_NK46Stdlib;setoid_ring<Ring_polynom5PExpr09C56Stdlib6ZArith6BinInt1Z7mod_mulK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib7Mh_00368AsanAcct4A_wfC1?~~~~~~~~~~~~~~~K46Stdlib;setoid_ring<Ring_polynom5PExpr03c49OSSVerify5KrLib>NraArtHandoffK9as0_EXTRAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<in_shadow_ofC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9page_baseC59OSSVerify5KrLib>AsanPlanSoundK4APSK<page_base_leC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1Z;div_le_monoC59OSSVerify5KrLib>AsanPlanSoundK4APSK6allowAC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbC46Stdlib4Bool4Bool<orb_true_iffC59OSSVerify5KrLib>AsanPlanSoundK4APSK5sh_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK5sh_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK6pageupC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List;in_flat_mapC59OSSVerify5KrLib>AsanPlanSoundK4APSK6allow1C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_or_appC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:shadow_offC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List;existsb_appC59OSSVerify5KrLib7Mh_0089:HeapIfaceA>shadow_allowedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct=page_allowedbC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK7as0_A0xC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3acs00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6spiece00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC59OSSVerify5KrLib7Mh_01456NarInv5rn_HIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7a_totszC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8a_abytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7a_eagerC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct7A_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117;Na0HandoffK=as0_binv_mainC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01099ArtBridge:BINV_introC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_01099ArtBridge4BInv00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv4KMAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00238AsanCeil=alloc_ceilingC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK9as0_BASExC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00357ArtRuns3aev00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00238AsanCeil>bottomup_floorC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK3KSHC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK<as0_EXTRA_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117;Na0HandoffK8as0_BASEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117;Na0HandoffK6as0_A0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01099ArtBridge<in_shadow_rwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01099ArtBridge8bi_shdefC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_lC59OSSVerify5KrLib7Mh_00356ArtMem:art_bytes1C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK9as0_shdefC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA:shadow_blkC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool8orb_propc49OSSVerify5KrLib>NraArtHandoffK5byteZC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00c49OSSVerify5KrLib>NraArtHandoffK5byte1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01099ArtBridge6HSH_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01099ArtBridge6HSH_HIC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK7glob_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01458NarFsInv=art_c_staticsC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00C59OSSVerify5KrLib7Mh_01458NarFsInv:art_fs_geoC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec8Z_lt_decI47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib7Mh_01458NarFsInvAart_fsinv_handoffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8FS_BYTESC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffKAas0_art_c_staticsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0251:NarCreditT>art_credit_gs0C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK3K0DC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv7PRIMCAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv4KCNTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7app_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<blocks_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA=fframes_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK<isp_facts_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK9isp_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK7u_e_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK4utopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0109?AsanNodesMmLibK;u_e_stk_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK;utop_boundsC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffKBvis_shadow_allowedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv=art_client_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117>Na0PlanImagesK=asan0_res_lenC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK<art_lazy_chkC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK6E_RISXC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK7hop_preC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK8hop_zoneC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK6vis_hiC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK6own_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6ealignC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK9hsplit_eqC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK6is_rngC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC59OSSVerify5KrLib>AsanPlanSoundK4APSK7hreplayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132>HandoffBridgeK7hb_lazyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132>HandoffLedgerK:hl_hops_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132>HandoffLedgerK9hl_replayC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK3bKSC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK<is_rng_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132<HandoffLazyK=hl_replay_subC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK:lazy_partsC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK6hlz_okC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK8ris_val2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv=art_lazy_zoneC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesC59OSSVerify5KrLib7Mh_0132<HandoffLazyK=hl_page_pieceC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK8pb_factsC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK:lazy_pieceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv?g_sec_committedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv=art_committedC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK3apxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6flat_xC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K>ranges_apart_xC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK<flat_x_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6a_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K5a_offC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK6estartC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SKDranges_apart_x_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK5elenZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K3xhiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK9xhi_soundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7compareI47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison03c49OSSVerify5KrLib>NraArtHandoffK8round_idC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_modc49OSSVerify5KrLib>NraArtHandoffK:win_nolazyC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK9apx_soundC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK8round_alC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132>HandoffLedgerK;hl_off_bandC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib>AsanPlanSoundK4APSK5cs_ok00C1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decC59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK<ealign_soundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6divideC56Stdlib6ZArith6BinInt1Z:mod_divideC56Stdlib6ZArith6BinInt1Z9pow_add_rC56Stdlib6ZArith6BinInt1Z<divide_transc49OSSVerify5KrLib>NraArtHandoffK;round_apartC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK;as0_lazy_c1C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_app_orc49OSSVerify5KrLib>NraArtHandoffK:own_windowC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK<vis_hi_soundC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK;win_allowedC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK9vis_in_InC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv;art_lazy_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01099ArtBridge3KN0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK8amap_denC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01099ArtBridge3ivZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132=HandoffRolesK7role_inC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6in_mapC59OSSVerify5KrLib7Mh_0132>HandoffBridgeK7hb_mapsC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK7role_knC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunCsegment_reservationc49OSSVerify5KrLib>NraArtHandoffK6seg_knC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv9art_kn_okC1?~~~~~~~~~~~~~~~C49OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asanYTgt_fuzz_msgpack_encoder_asan_segment_000C1@~~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C49OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asanYTgt_fuzz_msgpack_encoder_asan_segment_001C1@~~~~~~~~~~~~~~~~C49OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asanYTgt_fuzz_msgpack_encoder_asan_segment_002C1@~~~~~~~~~~~~~~~~C49OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asanYTgt_fuzz_msgpack_encoder_asan_segment_003C1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117>Na0PlanImagesK<asan0_res_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01099ArtBridge8BINV_awfC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK<as0_art_binvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv=art_alloc_repC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01458NarFsInv9art_fsinvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv=art_credit_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv<art_eager_okC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK=as0_art_fsinvC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK>as0_art_creditC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK?as0_art_lazy_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01099ArtBridge4BINVC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInvBart_handoff_targetC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_01458NarFsInv7art_fsg00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01458NarFsInv8art_fsg0C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK>as0_art_clientC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK=as0_art_kn_okC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib>NraArtHandoffK=as0_art_eagerC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00".   (* [comment removed for export] *)
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition I_KSPACE : nat := 5.   Definition I_PARR : nat := 6.   Definition I_THREAD : nat := 7.   Definition I_CTX : nat := 8.
Definition I_FAKE : nat := 11.    Definition I_L2 : nat := 14.    Definition I_BLK : nat := 15.   Definition I_DTLS : nat := 10.   (* [comment removed for export] *)

Definition e_at (k : list kentry) (b : expr) (off : Z) (w : nat) : expr :=
  match kfind_word k b off w with Some e => e | None => ELit 0 end.
Definition bT (cs : acs) : expr := am_base (role cs I_THREAD).
Definition bC (cs : acs) : expr := am_base (role cs I_CTX).
Definition bF (cs : acs) : expr := am_base (role cs I_FAKE).
Definition bP (cs : acs) : expr := am_base (role cs I_PARR).
Definition bL2 (cs : acs) : expr := am_base (role cs I_L2).
Definition bBLK (cs : acs) : expr := am_base (role cs I_BLK).
Definition bD (cs : acs) : expr := am_base (role cs I_DTLS).
(* [comment removed for export] *)
Definition spbE (cs : acs) : expr := e_at (kn cs) (ELit 0) (1426456 + 32) 8.
Definition bK (cs : acs) : expr := fst (split_lit (spbE cs)).
(* [comment removed for export] *)
Definition topE (cs : acs) : expr := e_at (kn cs) (bT cs) 8 8.
Definition botE (cs : acs) : expr := e_at (kn cs) (bT cs) 16 8.
(* [comment removed for export] *)
Definition tfE (cs : acs) : expr := e_at (kn cs) (ELit 0) 0x231948 8.
Definition stE (cs : acs) : expr := e_at (kn cs) (ELit 0) (0x231948 + 24) 4.

Definition TP : Z := 0x693b00.
Definition TSD : Z := 0x6b4fb8.
Definition LOFF : Z := 0x10.

Definition as0_ar (E : env) (cs : acs) : asan_run :=
  AR (uE E e_sp0) (uE E (topE cs)) (uE E (botE cs)) (rbase E cs I_FAKE) (uE E (bK cs) + 0x10000).
Definition as0_rn (E : env) (cs : acs) : art_run :=
  ARN (as0_ar E cs) (rbase E cs I_THREAD) (rbase E cs I_CTX) TP 0 TSD LOFF ((uE E (bK cs) + 0x10000) / 65536)
      (rbase E cs I_KSPACE) (rbase E cs I_PARR) (rbase E cs I_L2) (rbase E cs I_BLK) (rbase E cs I_DTLS) [].   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition is_var_in (k : list kentry) (e : expr) (lo hi : Z) : bool :=
  match e with EVar _ => existsb (kentry_eqb (KRange e lo hi)) k | _ => false end.

(* [comment removed for export] *)
Definition B1 : Z := 4434396.
Definition B2 : Z := 2452888.
Definition img_cover (k : list kentry) (lo hi : Z) : bool :=
  existsb (fun K => match K with KImg l h => (Z.leb l lo && Z.leb hi h)%bool | _ => false end) k.
Definition xlo_pos (k : list kentry) (e : expr) : bool := match xlo k e with Some lo => Z.ltb 0 lo | None => false end.
Definition lit_len (cs : acs) (i : nat) (L : Z) : bool := expr_eqb (am_len (role cs i)) (ELit L).
Definition vis_in (cs : acs) (b n : expr) : bool := existsb (fun p => (expr_eqb (fst p) b && expr_eqb (snd p) n)%bool) (a_vis cs).

(* [comment removed for export] *)
Definition glob_chk (k : list kentry) (g : Z * Z) : bool :=
  ((Z.eqb (snd g / 8) 0 || chk_zero k (ELit 0) (fst g / 8 + 0x7fff8000) (snd g / 8)) && (if Z.eqb (snd g mod 8) 0 then true else chk_word k (ELit 0) (fst g / 8 + 0x7fff8000 + snd g / 8) 1 (ELit (snd g mod 8)))
   && (0x10000 <=? fst g) && (fst g <? 0x6b6000) && (0 <=? snd g) && (snd g <? 8192))%bool.

Definition art_sym_list (cs : acs) : list bool :=
  let k := kn cs in
  [ ((17 =? Z.of_nat (length (a_maps cs))));
    (chk_word k (ELit 0) (1426456 + 32) 8 (spbE cs));
    (Z.eqb (snd (split_lit (spbE cs))) 0x10000);
    (chk_word k (ELit 0) (1426456 + 48) 8 (eaddz (spbE cs) (2 ^ 37)));
    (chk_word k (ELit 0) (1426456 + 64 + 8) 8 (bP cs));
    (chk_word k (ELit 0) TSD 8 (bC cs));
    (chk_word k (bC cs) 152 8 (bT cs));
    (chk_word k (bT cs) 0 8 (bC cs));
    (chk_word k (bC cs) 8 4 (ELit 0));
    (chk_word k (bT cs) 8 8 (topE cs));
    (chk_word k (bT cs) 16 8 (botE cs));
    (chk_word k (bT cs) 40 1 (ELit 0));
    (chk_word k (bT cs) 3168 1 (ELit 0));
    (chk_wr k (bT cs) 0 4096);
    (chk_zero k (bT cs) 80 3088);
    (chk_zero k (bK cs) 0x2000010000 4096);
    (chk_wr k (bK cs) 0x2000010000 4096);
    (chk_wr k (bF cs) 0 0xb09000);
    (chk_word k (ELit 0) TP 8 (bF cs));
    (chk_word k (bT cs) 72 8 (bF cs));
    (chk_word k (bF cs) 88 8 (ELit 20));
    (chk_zero k (bF cs) 0 88);
    (chk_zero k (bF cs) 96 (4096 + 32768 - 96));
    (chk_word k (ELit 0) 0x641968 8 (bL2 cs));
    (chk_word k (ELit 0) (0x231948 + 16) 8 (bBLK cs));
    (chk_word k (ELit 0) 0x231948 8 (tfE cs));
    (is_var_in k (tfE cs) 2 3);
    (chk_word k (ELit 0) (0x231948 + 24) 4 (stE cs));
    (is_var_in k (stE cs) 2 3);
    (chk_wr k (ELit 0) 0x241958 4194308);
    (chk_wr k (ELit 0) 0x231948 32);
    (chk_wr k (bL2 cs) 0 (2 ^ 20));
    (chk_wr k (bBLK cs) 0 (2 ^ 23));
    (chk_word k (bL2 cs) 24 4 (ELit 0));
    (chk_word k (bL2 cs) 16 8 (e_at k (bL2 cs) 16 8));
    (chk_word k (ELit 0) B1 4 (e_at k (ELit 0) B1 4));
    (is_var_in k (e_at k (ELit 0) B1 4) 0 1);
    (chk_word k (ELit 0) B2 4 (e_at k (ELit 0) B2 4));
    (is_var_in k (e_at k (ELit 0) B2 4) 0 1);
    (img_cover k DEP_LO B2);
    (img_cover k (B2 + 4) B1);
    (img_cover k (B1 + 4) DEP_HI);
    (amap_eqb (role cs 0) M_LOW);
    (amap_eqb (role cs 1) M_GAP);
    (amap_eqb (role cs 2) M_HIGH);
    (xlo_pos k (bT cs));
    (xlo_pos k (bC cs));
    (xlo_pos k (bF cs));
    (lit_len cs I_KSPACE 0x2000011000);
    (lit_len cs I_PARR 0x800000);
    (lit_len cs I_THREAD 4096);
    (lit_len cs I_CTX 0x10000);
    (lit_len cs I_FAKE 0xb09000);
    (lit_len cs I_L2 0x100000);
    (lit_len cs I_BLK 0x800000);
    (* [comment removed for export] *)
    (lit_len cs I_DTLS 4096); (xlo_pos k (bD cs)); (chk_word k (ELit 0) (1426456 + 64 + 16) 8 (bP cs)); (vis_in cs (ELit 0x10000) (ELit 0x6a6000));
    (vis_in cs (bF cs) (ELit 0xb09000));
    (vis_in cs e_top e_stk_len);
    (* [comment removed for export] *)
    (img_cover k 0x150000 0x158000);
    (* [comment removed for export] *)
    (chk_word k (ELit 0) (TP + 8) 8 (bD cs)); (chk_word k (bD cs) 24 8 (ELit TP));
    (chk_zero k (ELit 0) 2147459072 10056); (chk_zero k (ELit 0) 2147469144 4); (chk_zero k (ELit 0) 2147469176 12); (chk_zero k (ELit 0) 2147470520 20); (chk_zero k (ELit 0) 2147470544 44); (chk_zero k (ELit 0) 2147470788 36); (chk_zero k (ELit 0) 2147470840 12); (chk_zero k (ELit 0) 2147470932 152656); (chk_zero k (ELit 0) 2147623604 5216); (chk_zero k (ELit 0) 2147629172 701324);
    (forallb (glob_chk k) ART_GLOBALS) ]%bool.
Definition art_sym_chk (cs : acs) : bool := forallb (fun b => b) (art_sym_list cs).

Fixpoint all_true (l : list bool) : Prop := match l with [] => True | b :: r => b = true /\ all_true r end.
Lemma all_true_of : forall l, forallb (fun b => b) l = true -> all_true l.
Proof.
ltac2:(KReplay.run1 (kr_t_NraArtHandoffK ()) [] "h01Hh11lh21bh32H1h42H2h52IHp;1p;3p;2p;4p;5p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0g000dR0p4p710p8g001@j1;Tg001`j12Tg002\j1:Tg003<j33Tg003\j39Tg004?R1j25Tg004Zj46Tg0055j57TP0j34Tg005Wj38Tg0061R0f1R2f0R334p=1g006Q9803p=0%;0R4P0P3X20R5/13#0%22[R6X14%:0,15#0g0071W0f2R7=302,15#0f3R81157R7;93%08%07'5P1f4R1#01158#0f5=301#2P3f6R1#01151#0f8#0f7#2P2P1P3O1C6W4W3P2P3O2n2001000000120000000b0W0X56X14X20P3D7W1o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bKS (cs : acs) : expr := am_base (role cs I_KSPACE).
(* [comment removed for export] *)
Definition E_RISX (cs : acs) : expr := EAlu Instr.ALU_ADD (bK cs) (ELit 0x2000010000).

Fixpoint hsplit (r : expr) (h : list hop) : option (list hop * list hop) :=
  match h with
  | [] => None
  | HSub b n :: t =>
      if (expr_eqb b r && expr_eqb n (ELit 4096))%bool then Some ([], t)
      else match hsplit r t with Some (h1, h2) => Some (HSub b n :: h1, h2) | None => None end
  | x :: t => match hsplit r t with Some (h1, h2) => Some (x :: h1, h2) | None => None end
  end.
Lemma hsplit_eq : forall r h h1 h2, hsplit r h = Some (h1, h2) -> h = h1 ++ HSub r (ELit 4096) :: h2.
Proof.
  intros r h. induction h as [|x t IH]; intros h1 h2 H; [discriminate|]. cbn [hsplit] in H.
  destruct x as [b n|b n].
  - destruct (hsplit r t) as [[a1 a2]|] eqn:Hs; [|discriminate]. injection H as <- <-. cbn [app]. f_equal. apply IH. reflexivity.
  - destruct (expr_eqb b r && expr_eqb n (ELit 4096))%bool eqn:Hb.
    + injection H as <- <-. apply andb_prop in Hb as [B1 B2]. apply expr_eqb_eq in B1. apply expr_eqb_eq in B2. subst. reflexivity.
    + destruct (hsplit r t) as [[a1 a2]|] eqn:Hs; [|discriminate]. injection H as <- <-. cbn [app]. f_equal. apply IH. reflexivity.
Qed.

Definition is_rng (b n : expr) (b0 : expr) (L : Z) : bool := (expr_eqb b b0 && expr_eqb n (ELit L))%bool.
(* [comment removed for export] *)
Definition hop_pre (cs : acs) (x : hop) : bool :=
  match x with HSub _ _ => true | HCons b n => (is_rng b n (bBLK cs) 0x800000 || is_rng b n (bP cs) 0x800000)%bool end.
(* [comment removed for export] *)
Definition hop_zone (cs : acs) (x : hop) : bool :=
  match x with
  | HSub _ _ => true
  | HCons b n => (is_rng b n (bBLK cs) 0x800000 || is_rng b n (bP cs) 0x800000 || is_rng b n (bKS cs) 0x2000011000
                  || is_rng b n (ELit 0x7fff7000) 0x10000000 || is_rng b n (ELit 0x8fff7000) 0x20000000000 || is_rng b n (ELit 0x2008fff7000) 0xdfff0001000)%bool
  end.
(* [comment removed for export] *)
Definition vis_hi (k : list kentry) (p : expr * expr) : bool :=
  ((expr_eqb (fst p) e_top && expr_eqb (snd p) e_stk_len)
   || match xhi k (fst p), snd p with Some hi, ELit n => (0 <=? n) && (n <? 2 ^ 64) && (hi + n <=? 2 ^ 47) | _, _ => false end)%bool.
(* [comment removed for export] *)
Definition apx (k : list kentry) (zb : expr) (zn : Z) (p : expr * expr) : bool :=
  let '(zb', zk) := split_lit zb in let '(pb, pk) := split_lit (fst p) in
  (flat_x k zb' zk (ELit zn) && flat_x k pb pk (snd p) && ranges_apart_x k zb' zk (ELit zn) pb pk (snd p))%bool.
(* [comment removed for export] *)
Definition own_ok (cs : acs) (p : expr * expr) : bool :=
  let k := kn cs in
  (is_rng (fst p) (snd p) (bBLK cs) 0x800000
   || is_rng (fst p) (snd p) (E_RISX cs) 4096
   || (apx k (bKS cs) 0x2000011000 p && apx k (bP cs) 0x800000 p
       && (apx k (bBLK cs) 0x800000 p || (expr_eqb (snd p) (ELit 4096) && (12 <=? ealign k (fst p))))))%bool.
Definition art_lazy_chk (cs : acs) : bool :=
  (match hsplit (E_RISX cs) (a_hlz cs) with Some (h1, _) => forallb (hop_pre cs) h1 | None => false end
   && forallb (hop_zone cs) (a_hlz cs)
   && forallb (fun p => vis_hi (kn cs) p && own_ok cs p) (a_vis cs ++ a_ghost cs)
   && (12 <=? ealign (kn cs) (bBLK cs)) && vis_in cs (bBLK cs) (ELit 0x800000))%bool.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma uE_lit : forall E z, 0 <= z < 2 ^ 64 -> uE E (ELit z) = z.
Proof.
ltac2:(KReplay.run1 (kr_t_NraArtHandoffK ()) [] "h01Eh12Hzh21zp;2p;1p;3g00I[j2<Tg00DWj10Tg009?j11Tg00J7j23Tg00JTj2;Tg004?j2:Tg00K0j28Tg00Kmj14Tg009]j15Tg00LKj26Tg00MOj27Tg005Wj32Tg00N9j29Tg00O4g00P7R0g00PUf0R1'<g00G]#0R2#1%02#0#0#0#0R2#1'3,;1':f1R3/81%42f2R2%53R1'6'7=203e1921=203eW1W2W0o"). Qed.

Lemma class_size_pos : forall c, 1 <= c <= 30 -> 0 < AsanTab.class_size c.
Proof.
  intros c Hc. assert (H : forallb (fun c => 0 <? AsanTab.class_size c) (AsanTab.zrange 1 30) = true) by (vm_compute; reflexivity).
  apply Z.ltb_lt. apply (proj1 (forallb_forall _ _) H). unfold AsanTab.zrange. apply AsanTab.in_ziota. change (Z.of_nat (Z.to_nat 30)) with 30. lia.
Qed.

Section Derive.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  (* [comment removed for export] *)
  Variable mbase : word.
  Variable stdin : InputStream.
  Variable gid : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.
  Variable abrt : bool.
  Variable ur : InputStream.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variable sdf : bool.   (* the SIGPIPE disposition at exec, free at LPS 727298f3 *)
  Variable apc : N.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc).
  #[local] Notation argH := (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
  #[local] Notation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
  Let AH := argH0_high sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva.

  Variable cs : acs.
  Hypothesis CHK0 : as0_chk cs = true.
  Hypothesis CHKL : art_lits_chk cs = true.
  Hypothesis CHKS : art_sym_chk cs = true.

  Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis HC : CSOK E cs R FULL model.

  #[local] Notation rn := (as0_rn E cs).
  #[local] Notation T := (rbase E cs I_THREAD).
  #[local] Notation CTX := (rbase E cs I_CTX).
  #[local] Notation KB := (rbase E cs I_KSPACE).
  #[local] Notation SPB := (uE E (bK cs) + 0x10000).
  #[local] Notation SP0 := (uE E e_sp0).

  (* [comment removed for export] *)
  Hypothesis HGEO_SPB : KB < SPB <= KB + 65536 /\ SPB mod 65536 = 0.
  Hypothesis HGEO_STK : uE E (topE cs) = uE E (botE cs) + 8388608 /\ uE E (botE cs) mod 4096 = 0
                        /\ SP0 - 8388608 <= uE E (botE cs) + 4096 /\ uE E (botE cs) <= SP0 - 8388608 + 4096 /\ uE E (topE cs) <= 2 ^ 47.

  (* [comment removed for export] *)
  Hypothesis HSP16 : SP0 + 16 <= 2 ^ 47.
  Hypothesis HSPA : SP0 mod 16 = 0.                                    (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac chk_split H := repeat (let X := fresh "C" in apply andb_prop in H as [H X]).

  #[using="CHK0"] Lemma nofog : no_fog (a_maps cs) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_NraArtHandoffK ()) ["Derive"] "p'0h01Hh11mh21Ch32C0h42C1h52C2h62C3h72C4h82C5h92C6h:2C7i002loi011xp;1p;2p;3g00d;j1GTg00e;j1>Tg00f<j1:Tg00g=j1FTg00h=j27Tg00?>j23Tg00iEj1=Tg008=j2<Tg00jEj1;Tg00kBj29Tg00lGj18Tg000dj34Tg00mGj1ETg00nOj1DTg00E<j3BTg00oQj16Tg010Tj35Tg0110j1@Tg0122j2?Tg00Raj2ATg003\j32Tg004?R0j21Tg005Wj3CTg0061R1f0R2g006Q3Cp=0p,4CHK0p,2csR3#G#0%>3R4#:R5%F3,74R6'3R7%=3,74R8'3R9g00FYR:/<:R:g0133%;3R;'9%83R<34R='3R>%E;%D39B:<54:R:'3R<g013nR3g014o#6;54R?'3R@g015n#6=534RA'3RBg016m#6=534RC'3RD%62=534X13g017mR4543RE'3RFg008]g00P7P1%@2,?;g00PU/A2g00I;n10110100021010000X13=434R4;22%0FRF%04R4'1P0PFP4%05R3P2f1R;92DE%0DRD%0ERE'1P0PDPEP3P2A2BC;%0BRB%0CRC'1P0PBPCP3P2A2@A;%0@R@%0ARA'1P0P@PAP3P2A2<?;%0<R<%0?R?'1P0P<P?P3P2A2>:;%0>R>%0:R:'1P0P>P:P3P2A29=;%09R9%0=R='1P0P9P=P3P2A278;%07R7%08R8'1P0P7P8P3P2A256;%06R6,13P0P3P6P3P2P;X:6X03P;P2O2n2001000000120000000b0X98X07P;P2O2n2001000000120000000b0X8=X09P;P2O2n2001000000120000000b0X7:X0>P;P2O2n2001000000121000000b0X6?X0<P;P2O2n2001000000121000000b0X5AX0@P;P2O2n2001000000121000000b0X4CX0BP;P2O2n2001000000121000000b0X3EX0DP;P2O2n2001000000121000000b0X24X0FP;P2O2n2001000000121000000b0b0o"). Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH R model HC"] Lemma cellW : forall b off w v, chk_word (kn cs) b off w v = true -> cellA FULL (uE E b + off) w (uE E v).
  Proof.
    intros b off w v H. unfold cell.
    exact (proj2 (hc_word ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model b off w v HC H)).
  Qed.
  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva cs CHKL E R model HC"] Lemma cellL : forall a w v, In (a, w, v) ART_LITW -> cellA FULL a w v.
  Proof. exact (art_lit sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva E cs R FULL model HC CHKL). Qed.
  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva cs CHKL E R model HC"] Lemma cellLb : forall a w v,
    existsb (fun c => (Z.eqb (fst (fst c)) a && Nat.eqb (snd (fst c)) w && Z.eqb (snd c) v)%bool) ART_LITW = true -> cellA FULL a w v.
  Proof.
    intros a w v H. apply existsb_exists in H as ([[a' w'] v'] & Hin & Hb). cbn [fst snd] in Hb.
    apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2]. apply Z.eqb_eq in H1. apply Nat.eqb_eq in H2. apply Z.eqb_eq in H3. subst.
    exact (cellL _ _ _ Hin).
  Qed.
  #[using="sp brk0 rdraw argv envp uid hw fs R model HC"] Lemma cellZ : forall b off n a (w : nat), chk_zero (kn cs) b off n = true -> (w <= 8)%nat ->
    uE E b + off <= a -> a + Z.of_nat w <= uE E b + off + n -> cellA FULL a w 0.
  Proof.
    intros b off n a w H Hw H1 H2. unfold cell.
    exact (hc_zero_cell ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model b off n HC H a w Hw H1 H2).
  Qed.
  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH R model HC"] Lemma wrK : forall b off n, chk_wr (kn cs) b off n = true -> wrA FULL (uE E b + off) n.
  Proof.
    intros b off n H d k Hd Hk.
    exact (hc_wr ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model b off n HC H d k Hd Hk).
  Qed.

  #[using="CHKS E"] Lemma len17 : length (a_maps cs) = 17%nat.
Proof. pose proof (all_true_of _ CHKS) as H. cbn [all_true art_sym_list] in H. destruct H as [H _]. apply Z.eqb_eq in H. lia. Qed.

  #[using="CHKS"] Lemma sym_all : all_true (art_sym_list cs).
Proof.
ltac2:(KReplay.run1 (kr_t_NraArtHandoffK ()) ["Derive"] "p;1p;2g01WIj11Tg01XIj20Tp,2cs#1p,4CHKS'0o"). Qed.
  Ltac chk_old := let H := fresh in pose proof sym_all as H; cbn [all_true art_sym_list] in H; decompose [and] H; assumption.
  (* [comment removed for export] *)
  Ltac chk_find eqt g l i :=
    lazymatch l with
    | cons ?hd ?tl =>
        first [ (eqt hd g;
                 exact (proj1 (List.Forall_nth (fun xb : bool => (fun yb : bool => yb) xb = true) (art_sym_list cs))
                          (proj2 (List.Forall_forall (fun xb : bool => (fun yb : bool => yb) xb = true) (art_sym_list cs))
                             (proj1 (List.forallb_forall (fun yb : bool => yb) (art_sym_list cs)) CHKS))
                          i true (proj1 (Nat.ltb_lt i (length (art_sym_list cs))) (@eq_refl bool true))))
              | chk_find eqt g tl constr:(Datatypes.S i) ]
    end.
  Ltac chk :=
    first [ lazymatch goal with
            | |- ?g = true =>
                let l := eval cbv beta zeta delta [art_sym_list] in (art_sym_list cs) in
                first [ chk_find ltac:(fun u v => constr_eq u v) g l constr:(Datatypes.O) | chk_find ltac:(fun u v => unify u v) g l constr:(Datatypes.O) ]
            end
          | chk_old ].

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs cs R FULL model HC HSP16"] Lemma sp0_win : 0x7fff80000000 <= SP0 <= 2 ^ 47.
  Proof.
    destruct (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as (_ & ISP & _). unfold sp_window_lo, sp_window_hi in ISP. lia.
  Qed.

  #[using="CHKS"] Lemma role_shadow : rbase E cs 0 = 0x7fff7000 /\ rlen E cs 0 = 0x10000000 /\ rbase E cs 1 = 0x8fff7000 /\ rlen E cs 1 = 0x20000000000
                      /\ rbase E cs 2 = 0x2008fff7000 /\ rlen E cs 2 = 0xdfff0001000.
  Proof.
    assert (H0 : amap_eqb (role cs 0) M_LOW = true) by chk. assert (H1 : amap_eqb (role cs 1) M_GAP = true) by chk.
    assert (H2 : amap_eqb (role cs 2) M_HIGH = true) by chk.
    apply amap_eqb_eq in H0. apply amap_eqb_eq in H1. apply amap_eqb_eq in H2. unfold rbase, rlen. rewrite H0, H1, H2.
    cbn [M_LOW M_GAP M_HIGH am_base am_len]. rewrite !uE_lit by lia. repeat split; reflexivity.
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL model HC HGEO_STK"] Lemma rg : forall i L, (i < 17)%nat -> lit_len cs i L = true -> 0 <= L < 2 ^ 64 ->
    rbase E cs i mod 4096 = 0 /\ 0 <= rbase E cs i /\ 0 < L /\ rbase E cs i + L <= SP0 - 8388608
    /\ (rbase E cs i + L <= 0x10000 \/ 0x6b6000 <= rbase E cs i)
    /\ ((3 <= i)%nat -> rbase E cs i + L <= 0x7fff7000 \/ 0x10007fff8000 <= rbase E cs i).
Proof. intros i L.
intros Hi HL HLr.
unfold lit_len in HL. apply expr_eqb_eq in HL.
pose proof (role_lit E cs i L HL HLr) as El.
destruct (role_geo ASEGS0 ASAN0 Mh_0132.AsanInitK.LIMIT SINV argH fs E cs R FULL model i HC nofog ltac:(rewrite len17; exact Hi)) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
rewrite El in *. cbn [img_lo img_hi ASAN0] in G4.
repeat split; try assumption. intros H3.
destruct role_shadow as (S0 & L0 & S1 & L1 & S2 & L2).
pose proof (role_apart ASEGS0 ASAN0 Mh_0132.AsanInitK.LIMIT SINV argH fs E cs R FULL model i 0 HC nofog ltac:(rewrite len17; exact Hi) ltac:(rewrite len17; lia) ltac:(lia)) as A0.
pose proof (role_apart ASEGS0 ASAN0 Mh_0132.AsanInitK.LIMIT SINV argH fs E cs R FULL model i 1 HC nofog ltac:(rewrite len17; exact Hi) ltac:(rewrite len17; lia) ltac:(lia)) as A1.
pose proof (role_apart ASEGS0 ASAN0 Mh_0132.AsanInitK.LIMIT SINV argH fs E cs R FULL model i 2 HC nofog ltac:(rewrite len17; exact Hi) ltac:(rewrite len17; lia) ltac:(lia)) as A2.
rewrite El, ?S0, ?L0, ?S1, ?L1, ?S2, ?L2 in *. lia.
Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL model HC"] Lemma ra : forall i j Li Lj, (i < 17)%nat -> (j < 17)%nat -> i <> j -> lit_len cs i Li = true -> lit_len cs j Lj = true ->
    0 <= Li < 2 ^ 64 -> 0 <= Lj < 2 ^ 64 ->
    rbase E cs i + Li <= rbase E cs j \/ rbase E cs j + Lj <= rbase E cs i.
  Proof.
    intros i j Li Lj Hi Hj Hne HLi HLj Ri Rj. unfold lit_len in *. apply expr_eqb_eq in HLi. apply expr_eqb_eq in HLj.
    pose proof (role_apart ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model i j HC nofog ltac:(rewrite len17; exact Hi) ltac:(rewrite len17; exact Hj) Hne) as D.
    rewrite (role_lit E cs i Li HLi Ri), (role_lit E cs j Lj HLj Rj) in D. exact D.
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs R FULL model HC"] Lemma xpos : forall e, xlo_pos (kn cs) e = true -> 0 < uE E e.
  Proof.
    intros e H. unfold xlo_pos in H. destruct (xlo (kn cs) e) as [lo|] eqn:Hx; [|discriminate]. apply Z.ltb_lt in H.
    pose proof (xlo_sound ASEGS0 E _ (kn cs) e lo (co_know _ _ _ _ _ _ _ _ _ _ _ HC) Hx). unfold uE. lia.
  Qed.

  Ltac lenok := first [assert_succeeds (idtac); (chk)].
  Ltac RG i L := let X := fresh "G" in pose proof (rg i L ltac:(unfold I_KSPACE, I_PARR, I_THREAD, I_CTX, I_FAKE, I_L2, I_BLK; lia) ltac:(chk) ltac:(lia)) as X.
  Ltac RA i j Li Lj := let X := fresh "D" in
    pose proof (ra i j Li Lj ltac:(unfold I_KSPACE, I_PARR, I_THREAD, I_CTX, I_FAKE, I_L2, I_BLK; lia) ltac:(unfold I_KSPACE, I_PARR, I_THREAD, I_CTX, I_FAKE, I_L2, I_BLK; lia)
                  ltac:(unfold I_KSPACE, I_PARR, I_THREAD, I_CTX, I_FAKE, I_L2, I_BLK; lia) ltac:(chk) ltac:(chk) ltac:(lia) ltac:(lia)) as X.

  #[using="HGEO_SPB"] Lemma spb_qs : 65536 * (SPB / 65536) = SPB.
Proof.
ltac2:(KReplay.run1 (kr_t_NraArtHandoffK ()) ["Derive"] "h02Hah17__arithh24__ffh37__sat17h47__sat18h58__varmaph65__with74__x1h84__x2h94__x3h:1Hh;2Hmh<2_Hh=7__sat19h>7__sat20h?7__sat21h@7__sat22hA1ap;3p;1p;2p;6p;4p;7p;8g02W<j3gTg01a9j1fTg00N9j2?Tg00DWj15Tg009?j14Tg00];j22Tg00JTj2<Tg00I[j2ETg004?R0j2CTg02`bj2;Tg02jZj2LTg02k7j2ATg005Wj33Tg00Q3j18Tg020Aj2_Tg00J7j2\Tg020ij3[Tg002\j1ZTg001@j1YTg02Udj1XTg00V[j1WTg00W9j1VTg00Wdj2DTg02b]j6UTg00Z\j2TTg00?\j2STg00[>j2PTg00[jj3OTg00\Ij4NTg02kTj3MTg01`Aj1QTg02`1j2@Tg02l5j2RTg01R3j1BTg022Lj2:Tg023^j36Tg024Gj2KTg021Mj1eTg021kj2dTg0235j3JTg003<j3FTg00V=j2aTg02aBj4ITg00XGj2=Tg00YUj3HTg02lfj3^Tg00=Vj1`Tg00Xjj4]Tg00_:j7bTg00Z8j8cTf0R1#5#5p=1g00P7R2g00PUR3731p=>1E31p=0P2f1R4g02G1P1C]p=7P4g00`BR5g00`aR6P6g00aAR7P1g00aaFbp=9f3R8P5P6P6P7f2R9P4P1Gcp=Gp,8HGEO_SPBp,1ER:p,2csR;g02<03gR<%f;,?:R=g00G]R>#5R?#5R@#1RA#1#1#1#1RB#1#1#4RC'2RD'<12<C,ED'CR<1;DCRE#>RF'CP0P<PF1LDCR0,ACRG=32DP1%4?RH%8?#8#8#8#4RI'_RJ1<3H%0I1\HIRK,<3[[RL%0HRMg00H_RNA[HI4UW0RI%0K\N^0MRMg00bARN#ZRK%YNRH%X2RO%W2RP%V2RQP5P6P6P71D2CR51D23RR'7,9QEU1TQ7R7P1P9g0061RSg006QRT'S1P19=3STdAO234CNR3b2b5b6%>Cg00HB[P1b1b3b49MDC12GE932DPJPLPIPM%Q;,?:R;%4BRB'@%0;%0B1;;B#0[[g02LO,?:R:%4ARA'@%0:%0A1;:A#0[[1@DC%0DRA%0CR:%0E[[1RDC%00\:\Ag01T3RA#BR:#B,:2RD1:2:R:1:2ARA562562g02FERB'K%e>,d2R;=J2DAJ2;:=62A562/KB=FNK5FNPHP2P21a28P9POCIP4POCIPPPQ1=2?=H25R?1=2>9^25R51=2@R@5H2'7,9Q%`6R6PQ17@R,9QP6175?,9QCGCGP7P3b2b5b6X72X82X92124C1AC1/29532%>81AC9128C532[[^72^82^92P1PEP=P0f7f8O5b1b3b4b=b>b?b@b:X;FX<<P4P1O2n2001000000121000000bAo"). Qed.

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL model HC HGEO_STK"] Lemma rgl : forall i L, (i < 17)%nat -> lit_len cs i L = true -> 0 <= L < 2 ^ 64 ->
    rbase E cs i mod 4096 = 0 /\ 0 <= rbase E cs i /\ 0 < L /\ rbase E cs i + L <= SP0 - 8388608.
Proof. intros i L Hi HL HLr. destruct (rg i L Hi HL HLr) as (G1 & G2 & G3 & G4 & _). auto. Qed.
  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL model HC HGEO_STK"] Lemma rg_img : forall i L, (i < 17)%nat -> lit_len cs i L = true -> 0 <= L < 2 ^ 64 ->
    rbase E cs i + L <= 0x10000 \/ 0x6b6000 <= rbase E cs i.
Proof. intros i L Hi HL HLr. destruct (rg i L Hi HL HLr) as (_ & _ & _ & _ & G5 & _). exact G5. Qed.
  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL model HC HGEO_STK"] Lemma rg_hole : forall i L, (3 <= i < 17)%nat -> lit_len cs i L = true -> 0 <= L < 2 ^ 64 ->
    rbase E cs i + L <= 0x7fff7000 \/ 0x10007fff8000 <= rbase E cs i.
Proof. intros i L Hi HL HLr. destruct (rg i L ltac:(lia) HL HLr) as (_ & _ & _ & _ & _ & G6). apply G6. lia. Qed.
  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL model HC"] Lemma ra_sub : forall i j Li Lj a n b m, (i < 17)%nat -> (j < 17)%nat -> i <> j -> lit_len cs i Li = true -> lit_len cs j Lj = true ->
    0 <= Li < 2 ^ 64 -> 0 <= Lj < 2 ^ 64 -> rbase E cs i <= a -> a + n <= rbase E cs i + Li -> rbase E cs j <= b -> b + m <= rbase E cs j + Lj ->
    apart a n b m.
  Proof.
    intros i j Li Lj a n b m Hi Hj Hne HLi HLj Ri Rj Ha Hn Hb Hm. unfold apart.
    destruct (ra i j Li Lj Hi Hj Hne HLi HLj Ri Rj) as [X|X]; [left | right]; lia.
  Qed.
  Ltac IDX := unfold I_KSPACE, I_PARR, I_THREAD, I_CTX, I_FAKE, I_L2, I_BLK, I_DTLS; lia.
  Ltac RASUB i j Li Lj := apply (ra_sub i j Li Lj); [IDX | IDX | IDX | chk | chk | lia | lia | lia | lia | lia | lia].

  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL model HC HGEO_SPB HGEO_STK HSP16"] Theorem as0_art_run_ok : art_run_ok rn.
Proof.
pose proof sp0_win as W. pose proof spb_qs as Q. destruct HGEO_SPB as ((K1 & K2) & K3).
pose proof (rgl I_KSPACE 0x2000011000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (g1 & g2 & g3 & g4).
pose proof (rgl I_PARR 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (p1 & p2 & p3 & p4).
pose proof (rgl I_THREAD 4096 ltac:(IDX) ltac:(chk) ltac:(lia)) as (t1 & t2 & t3 & t4).
pose proof (rgl I_CTX 0x10000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (c1 & c2 & c3 & c4).
pose proof (rgl I_L2 0x100000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (l1 & l2 & l3 & l4).
pose proof (rgl I_BLK 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (b1 & b2 & b3 & b4).
pose proof (rgl I_FAKE 0xb09000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (f1 & f2 & f3 & f4).
pose proof (xpos (bT cs) ltac:(chk)) as PT. pose proof (xpos (bC cs) ltac:(chk)) as PC. pose proof (xpos (bF cs) ltac:(chk)) as PF.
change (uE E (bT cs)) with T in PT. change (uE E (bC cs)) with CTX in PC. change (uE E (bF cs)) with (rbase E cs I_FAKE) in PF.
assert (QT : exists qt, T = 4096 * qt) by (exists (T / 4096); pose proof (Z.div_mod T 4096 ltac:(lia)); lia).
assert (T4 : 4096 <= T) by (destruct QT as [qt Eq]; lia).
assert (C4 : 4096 <= CTX) by (pose proof (Z.div_mod CTX 4096 ltac:(lia)); lia).
assert (F4 : 4096 <= rbase E cs I_FAKE) by (pose proof (Z.div_mod (rbase E cs I_FAKE) 4096 ltac:(lia)); lia).
assert (KHOLE : 0x10007fff8000 <= KB).
{ destruct (rg_hole I_KSPACE 0x2000011000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; lia. }
unfold art_run_ok, art_geo, rn_HI, rn_spb, rn_ris, rn_spb, app_mem, BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES.
cbn [as0_rn as0_ar rn_ar rn_t rn_ctx rn_tp rn_key rn_tsd rn_loff rn_qs rn_kbase rn_parr rn_l2 rn_blk ar_sptop ar_space_beg ar_fs]. unfold TP, TSD, LOFF.
rewrite Q. change (2 ^ 20) with 0x100000. change (2 ^ 23) with 0x800000.
split.
{ split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [exact T4|]. split; [lia|]. split; [exact (rg_img I_THREAD 4096 ltac:(IDX) ltac:(chk) ltac:(lia))|].
split; [exact (rg_hole I_THREAD 4096 ltac:(IDX) ltac:(chk) ltac:(lia))|].
split; [RASUB I_THREAD I_KSPACE 4096 0x2000011000|]. split; [exact QT|].
split; [exact C4|]. split; [lia|].
split; [destruct (rg_img I_CTX 0x10000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; [left | right]; lia|].
split; [destruct (rg_hole I_CTX 0x10000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; [left | right]; lia|].
split; [RASUB I_CTX I_KSPACE 0x10000 0x2000011000|].
split; [RASUB I_THREAD I_CTX 4096 0x10000|]. lia. }
split; [reflexivity|]. split; [exact g1|]. split; [lia|]. split; [lia|].
split; [exact p1|].
split; [destruct (rg_img I_PARR 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; lia|]. split; [lia|].
split; [split; [lia|]; split; [|lia]; exact (rg_hole I_PARR 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia))|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [RASUB I_L2 I_THREAD 0x100000 4096|]. split; [RASUB I_L2 I_CTX 0x100000 0x10000|]. split; [RASUB I_L2 I_KSPACE 0x100000 0x2000011000|].
split; [unfold apart; destruct (rg_hole I_L2 0x100000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; [left | right]; lia|].
split; [RASUB I_BLK I_THREAD 0x800000 4096|]. split; [RASUB I_BLK I_CTX 0x800000 0x10000|]. split; [RASUB I_BLK I_KSPACE 0x800000 0x2000011000|].
split; [unfold apart; destruct (rg_hole I_BLK 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; [left | right]; lia|].
split; [RASUB I_PARR I_THREAD 0x800000 4096|]. split; [RASUB I_PARR I_CTX 0x800000 0x10000|]. split; [RASUB I_PARR I_KSPACE 0x800000 0x2000011000|].
split; [RASUB I_PARR I_L2 0x800000 0x100000|]. split; [RASUB I_PARR I_BLK 0x800000 0x800000|].
split; [RASUB I_FAKE I_THREAD 0xb09000 4096|]. split; [RASUB I_FAKE I_CTX 0xb09000 0x10000|]. split; [RASUB I_FAKE I_KSPACE 0xb09000 0x2000011000|].
split; [RASUB I_FAKE I_L2 0xb09000 0x100000|]. split; [RASUB I_FAKE I_BLK 0xb09000 0x800000|]. split; [RASUB I_FAKE I_PARR 0xb09000 0x800000|].
split; [lia|].
split; [split; [lia|]; split; [|lia]; exact (rg_hole I_FAKE 0xb09000 ltac:(IDX) ltac:(chk) ltac:(lia))|].
split; [exact (rg_img I_FAKE 0xb09000 ltac:(IDX) ltac:(chk) ltac:(lia))|]. split; [exact F4|].
pose proof (rgl I_DTLS 4096 ltac:(IDX) ltac:(chk) ltac:(lia)) as (d1 & d2 & d3 & d4).
pose proof (xpos (bD cs) ltac:(chk)) as PD. change (uE E (bD cs)) with (rbase E cs I_DTLS) in PD.
assert (D4 : 4096 <= rbase E cs I_DTLS) by (pose proof (Z.div_mod (rbase E cs I_DTLS) 4096 ltac:(lia)); lia).
cbn [as0_rn rn_dtls].
split; [destruct (rg_img I_L2 0x100000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; lia|].
split; [destruct (rg_img I_BLK 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; lia|].
split; [RASUB I_FAKE I_KSPACE 0xb09000 0x2000011000|].
split; [exact D4|]. split; [lia|].
split; [exact (rg_img I_DTLS 4096 ltac:(IDX) ltac:(chk) ltac:(lia))|].
split; [split; [lia|]; split; [|lia]; exact (rg_hole I_DTLS 4096 ltac:(IDX) ltac:(chk) ltac:(lia))|].
split; [RASUB I_DTLS I_THREAD 4096 4096|]. split; [RASUB I_DTLS I_CTX 4096 0x10000|]. split; [RASUB I_DTLS I_KSPACE 4096 0x2000011000|].
split; [RASUB I_DTLS I_PARR 4096 0x800000|]. split; [RASUB I_DTLS I_L2 4096 0x100000|]. split; [RASUB I_DTLS I_BLK 4096 0x800000|].
split; [RASUB I_DTLS I_FAKE 4096 0xb09000|].
split; [RASUB I_THREAD I_KSPACE 4096 0x2000011000|]. split; [RASUB I_CTX I_KSPACE 0x10000 0x2000011000|].
split; [RASUB I_L2 I_KSPACE 0x100000 0x2000011000|]. split; [RASUB I_PARR I_KSPACE 0x800000 0x2000011000|].
exact KHOLE.
Qed.

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL model HC HGEO_SPB HGEO_STK HSP16"] Lemma spb_val : uE E (spbE cs) = SPB.
  Proof.
    assert (Hs : Z.eqb (snd (split_lit (spbE cs))) 0x10000 = true) by chk. apply Z.eqb_eq in Hs.
    pose proof (split_lit_denot E (spbE cs) (bK cs) 0x10000) as Hd. unfold bK in Hd |- *.
    pose proof sp0_win as W. destruct HGEO_SPB as ((K1 & K2) & _). RG I_KSPACE 0x2000011000. unfold bK in K1, K2.
    destruct (split_lit (spbE cs)) as [b k] eqn:Hspl. cbn [fst snd] in *. subst k. specialize (Hd eq_refl).
    unfold uE in *. rewrite Hd. apply u64_lit. lia.
  Qed.
  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL model HC HGEO_SPB HGEO_STK HSP16"] Lemma ris_val : uE E (eaddz (spbE cs) (2 ^ 37)) = SPB + 2 ^ 37.
  Proof.
    unfold eaddz, uE. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite u64_lit by lia. fold (uE E (spbE cs)). rewrite spb_val.
    apply Z.mod_small. pose proof sp0_win. destruct HGEO_SPB as ((K1 & K2) & _). RG I_KSPACE 0x2000011000. unfold uE in *. lia.
  Qed.
  #[using="cs"] Lemma uE0 : uE E (ELit 0) = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_NraArtHandoffK ()) ["Derive"] "h02Hah17__arithh24__ffh37__sat17h47__sat18h57__sat19h67__sat20h78__varmaph85__witp;1p;2p;3p;4p;7g00DWj10Tg009?j13Tg00Q3j12Tg020Aj25Tg00JTj24Tg00I[j21Tg00J7j27Tg020ij38Tg002\j1?Tg001@j1>Tg02Udj1=Tg00V[j1<Tg00W9j1;Tg00Wdj2:Tg00Xjj49Tg00Kmj1KTg02Klj3JTg00_^j7ITg00Z\j2DTg00?\j2CTg00[>j2BTg005Wj3ATg00[jj3@Tg00\Ij4ETg004?j2FTg02VBj3GTg00_:j7HTf1R0g00`BR1g00`aR2P2g00aAR3f0R4g00aaFHp=6p,1Eg00PUR5g00G]#0R6#3R7%26#2#2#2#3R8'51457R911581778R:,45[[1157R;g00H_R<A8780UW0115:\<^0;%06#0#0#0#0R6#3R:,57115:177:R8,45R=[\9A87:0V<X0;1158\<^0;g00bAR;#?%>;g00P7R;#=%<;%;;R<P1P2P2P3P;1:;5R2g00bmP2C9,6<P;P2g00cT1:;7%K65J;C9,6<FI1D<3P4f2R<g0061R3g006QR6'C1B4<=A36dA@;50CEb2b7b81155/F=P4b1b3b4b5b63Go"). Qed.

  Ltac CL := apply cellLb; vm_compute; reflexivity.
  Ltac CW a w v := let X := fresh in pose proof (cellW (ELit 0) a w v ltac:(chk)) as X; rewrite uE0 in X; rewrite ?Z.add_0_l in X.

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH cs CHKS E R model HC"] Lemma got_none : forall a, 0x150000 <= a < 0x158000 -> FULL (Z_to_bv 64 a) = None.
Proof.
intros a Ha. assert (H : img_cover (kn cs) 0x150000 0x158000 = true) by chk.
unfold img_cover in H. apply existsb_exists in H as (K & Hin & Hc).
destruct K as [| | | l h | | | | | |]; try discriminate. apply andb_prop in Hc as [L1 L2]. apply Z.leb_le in L1. apply Z.leb_le in L2.
apply (hb_img ASEGS0 ASAN0 Mh_0132.AsanInitK.LIMIT SINV argH fs asan0_hull_ok AH E cs R FULL model l h HC Hin); [lia|].
unfold in_hull. cbn [img_lo img_hi ASAN0]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHK0 CHKL CHKS R model HC HGEO_SPB HGEO_STK HSP16"] Theorem as0_art_rt_statics : art_rt_statics rn FULL.
  Proof.
    unfold art_rt_statics, art_rt_tlsgot, art_prim_consts, art_layout, art_tsd, art_alloc_rodata, art_rz_rodata, DRoD, rn_spb, rn_ris, rn_spb, SB, kHighMemEnd.
    cbn [as0_rn rn_qs rn_tp rn_key rn_tsd rn_ctx rn_t rn_loff]. unfold TP, TSD, LOFF. rewrite spb_qs.
    pose proof (cellW (ELit 0) (1426456 + 32) 8 (spbE cs) ltac:(chk)) as X1. rewrite uE0, spb_val in X1.
    pose proof (cellW (ELit 0) (1426456 + 48) 8 (eaddz (spbE cs) (2 ^ 37)) ltac:(chk)) as X2. rewrite uE0, ris_val in X2.
    pose proof (cellW (ELit 0) TSD 8 (bC cs) ltac:(chk)) as X3. rewrite uE0 in X3. unfold TSD in X3.
    pose proof (cellW (bC cs) 152 8 (bT cs) ltac:(chk)) as X4.
    change (uE E (bC cs)) with CTX in *. change (uE E (bT cs)) with T in *.
    RG I_THREAD 4096. RG I_CTX 0x10000. pose proof sp0_win.
    pose proof (xpos (bC cs) ltac:(chk)) as PC. change (uE E (bC cs)) with CTX in PC.
    assert (C4 : 4096 <= CTX) by (pose proof (Z.div_mod CTX 4096 ltac:(lia)); lia).
    repeat match goal with |- _ /\ _ => split end; try exact X1; try exact X2; try exact X3; try exact X4; try exact got_none; try CL; lia.
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHKL CHKS R model HC"] Theorem as0_art_rt_thread : art_rt_thread rn FULL.
  Proof.
    unfold art_rt_thread. cbn [as0_rn as0_ar rn_t rn_ctx rn_tp rn_loff rn_ar ar_stack_top ar_stack_bottom]. unfold TP, LOFF.
    pose proof (wrK (bT cs) 0 4096 ltac:(chk)) as W. rewrite Z.add_0_r in W.
    pose proof (cellW (bT cs) 0 8 (bC cs) ltac:(chk)) as X1. rewrite Z.add_0_r in X1.
    pose proof (cellW (bC cs) 8 4 (ELit 0) ltac:(chk)) as X2. rewrite uE0 in X2.
    pose proof (cellW (bT cs) 8 8 (topE cs) ltac:(chk)) as X3. pose proof (cellW (bT cs) 16 8 (botE cs) ltac:(chk)) as X4.
    pose proof (cellW (bT cs) 40 1 (ELit 0) ltac:(chk)) as X5. rewrite uE0 in X5.
    pose proof (cellW (bT cs) 3168 1 (ELit 0) ltac:(chk)) as X6. rewrite uE0 in X6.
    repeat match goal with |- _ /\ _ => split end; try assumption. CL.
  Qed.

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHK0 CHKS R model HC HGEO_SPB HGEO_STK HSP16"] Lemma kshadow_wr : wrA FULL (0x7fff8000 + 8192 * (SPB / 65536)) (2 ^ 34).
  Proof.
    destruct (as0_chk_parts cs CHK0) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
    pose proof sp0_win as W. destruct HGEO_SPB as ((K1 & K2) & K3). RG I_KSPACE 0x2000011000.
    destruct G as (g1 & g2 & g3 & g4 & g5 & g6). specialize (g6 ltac:(unfold I_KSPACE; lia)).
    pose proof (Z.div_mod SPB 65536 ltac:(lia)) as DM. rewrite K3 in DM.
    set (q := SPB / 65536) in *.
    apply art_wr_of_defined; [lia | lia |].
    intros x Hx.
    apply (hl_shadow_defined ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH asan0_shadow_ok ltac:(cbn; unfold SHB_LO; lia)
             E cs R FULL model HC C1 C4 C5 M_HIGH 0x2008fff7000 0xdfff0001000 C8 eq_refl eq_refl eq_refl); unfold SHB_LO, SHB_LEN; lia.
  Qed.

  #[using="cs E"] Lemma wr0 : forall a, wrA FULL a 0.
Proof.
ltac2:(KReplay.run1 (kr_t_NraArtHandoffK ()) ["Derive"] "h02Hkh12Hah24__x1h34__x2h41kh51Hh62Hdh77__arithh84__ffh97__sat17h:7__sat18h;8__varmaph<5__with=1ah>4cstrh?1dh@1xhA1yp;1p;2p;3p;<p;4p;7p;8g01;3R0j14Tg00];j25Tg00I[j23Tg005Wj30j1BTg01n7j2STg01nZj3PTg00?\j29Tg01o7l<FTg01o\j1ETg00DWj12Tg009?j1?Tg00Q3j16Tg020Aj2^Tg00JTj2ATg00J7j2WTg020ij3UTg01R3j1@Tg022Lj2;Tg023^j3>Tg024Gj2RTg002\j1OTg003<j3NTg001@j1MTg02Udj1LTg00V=j2KTg02aBj4GTg00V[j1HTg00W9j1ITg00Wdj2JTg00XGj2=Tg00=Vj1DTg00YUj3QTg00Xjj4<Tg00Z\j2CTg00[>j2TTg00[jj3aTg00\Ij4`Tg0253j4_Tg00Kmj1]Tg01=6j2\Tg0483j4YTg00CYj7XTg01VSj4ZTg00_:j7[Tg00Z8j8VTg00PUR1f0R2'3p=1g00P7R3f1R4g00bmP2C<p=:P4g00`BR5g00`aR6P6g00aAR7P2g00aaF[p=7f3R8P5P6P6P7f2R5P4P2GVp=8g01CbR9%14%44R:,55/31g01T3R;9095R<%45R==031P9P3%B9P0%B3%42R0903:A09421S423PXA9X@9P5P=193=P;P11931M<F%E5%1=g00G]R=#2R:#?R>%6:#6#6#6#?R?'^1A1>%1?1W>?R@,A1[[%1>RAg00H_RBAU>?4UW1%1@\B^1Ag00bARA%@;RB#@,;31;3B1;3;5>35>3g02FE'R%OA3N%MAP3%L3P41K35CG%H3%I3RA1J31RB1=3=R@':,7A%D6R6PA%6=,=3R==Q3@/:B,7AP6PA1:B=,7AP6P3P@g02G1PBC<,7AC8C8C81CA7P2P5g0061RAg006QR7'9RB1T25=0A7dAa314C`b8b;b<X23X33%121554/31%18A0381[[[^23^33P2f7R5f6R@#4P8f4R6f5R=O5b7b9b:b>C_P<P9P;15=0/31g01IER=p,4FULLR0%2:#2#2#2#2#]155@'\P4CY=0A7]0X49%4;,56/31PBW0P8P2P4FXb5W0W6W4X?3P=P0P2P1CZeX=3o"). Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHK0 CHKS R model HC HGEO_SPB HGEO_STK HSP16"] Theorem as0_art_rt_primary : forall (FSG : Type) (gfs0 : FSG) (k0 : nat), art_rt_primary FSG rn (art_gs0 FSG gfs0 k0) FULL.
  Proof.
    intros FSG gfs0 k0. unfold art_rt_primary. cbn [art_gs0 g_inited g_cls as0_rn rn_t rn_qs]. unfold rn_spb, rn_ris, rn_spb. cbn [as0_rn rn_qs]. rewrite spb_qs.
    assert (ZT : chk_zero (kn cs) (bT cs) 80 3088 = true) by chk.
    assert (ZR : chk_zero (kn cs) (bK cs) 0x2000010000 4096 = true) by chk.
    assert (WR : chk_wr (kn cs) (bK cs) 0x2000010000 4096 = true) by chk.
    split; [|split; [|exact kshadow_wr]].
    - intros c Hc. split; apply (cellZ (bT cs) 80 3088 _ _ ZT); change (uE E (bT cs)) with T; lia.
    - intros c Hc. split; [|split; [|split; [|split]]].
      + unfold art_cls_rep, art_cache_rep, art_region_rep, art_cls0. cbn [cl_cache cl_free cl_mfa cl_au cl_mu cl_na cl_nfr length]. change (Z.of_nat 0) with 0.
        pose proof (wrK (bK cs) 0x2000010000 4096 WR) as W.
        repeat match goal with |- _ /\ _ => split end;
          try (apply (cellZ (bT cs) 80 3088 _ _ ZT); change (uE E (bT cs)) with T; lia);
          try (apply (cellZ (bK cs) 0x2000010000 4096 _ _ ZR); lia);
          try (intros j Hj; cbn in Hj; lia); try apply wr0.
        apply (wr_sub _ _ _ _ _ _ W); lia.
      + unfold art_cls_ok, art_cls0. cbn [cl_cache cl_free cl_mfa cl_au cl_mu cl_na cl_nfr length app]. pose proof (class_size_pos c Hc).
        repeat match goal with |- _ /\ _ => split end; try lia; try (exists 0; lia); try constructor.
      + unfold art_cls0. cbn [cl_cache]. intros H. congruence.
      + exists 0. reflexivity.
      + unfold art_cls0. cbn [cl_au]. intros H. lia.          (* [comment removed for export] *)
  Qed.

  #[using="Type"] Theorem as0_art_rt_chunks : forall (FSG : Type) (gfs0 : FSG) (k0 : nat), art_rt_chunks FSG rn (art_gs0 FSG gfs0 k0) [] FULL.
  Proof.
    intros FSG gfs0 k0. unfold art_rt_chunks. cbn [art_gs0 g_cls g_st]. unfold art_cls0. cbn [cl_cache cl_free cl_au cl_mu app].
    intros c Hc. pose proof (class_size_pos c Hc) as Hs. split; [|split; [|split]].
    - intros x Hx. lia.
    - intros w [].
    - intros w _. reflexivity.                       (* [comment removed for export] *)
    - intros w (W1 & W2 & _). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva cs CHKL E R model HC"] Lemma lock_sec : cellA FULL (1426456 + 64 + 616) 4 0.
Proof.
apply (cell0_cat FULL (1426456 + 64 + 616) 1 3); [lia | lia | lia | CL | CL].
Qed.
  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva cs CHKL E R model HC"] Lemma lock_quar : cellA FULL (0x15c6f0 + 152) 4 0.
Proof.
apply (cell0_cat FULL (0x15c6f0 + 152) 1 3); [lia | lia | lia | CL |].
apply (cell0_cat FULL (0x15c6f0 + 152 + 1) 1 2); [lia | lia | lia | CL | CL].
Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHKL CHKS R model HC"] Theorem as0_art_rt_sec : forall (FSG : Type) (gfs0 : FSG) (k0 : nat), art_rt_sec FSG rn (art_gs0 FSG gfs0 k0) [] FULL.
  Proof.
    intros FSG gfs0 k0. unfold art_rt_sec. cbn [art_gs0 g_sec g_sec_committed g_log as0_rn rn_parr length]. change (Z.of_nat 0) with 0.
    pose proof (cellW (ELit 0) (1426456 + 64 + 8) 8 (bP cs) ltac:(chk)) as X. rewrite uE0 in X.
    pose proof (cellW (ELit 0) (1426456 + 64 + 16) 8 (bP cs) ltac:(chk)) as X2. rewrite uE0 in X2.     (* [comment removed for export] *)
    repeat match goal with |- _ /\ _ => split end; try exact lock_sec; try CL; try exact X; try exact X2.
    - intros H. congruence.
    - intros H. discriminate H.
    - intros i s H. destruct i; discriminate H.
    - intros p [].
    - lia.                                           (* [comment removed for export] *)
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva CHKL CHKS R model HC"] Theorem as0_art_rt_quar : forall (FSG : Type) (gfs0 : FSG) (k0 : nat), art_rt_quar FSG rn (art_gs0 FSG gfs0 k0) FULL.
Proof.
intros FSG gfs0 k0. unfold art_rt_quar. cbn [art_gs0 g_qt g_qg as0_rn rn_t length app map art_batches_bytes fold_right]. change (Z.of_nat 0) with 0.
assert (ZT : chk_zero (kn cs) (bT cs) 80 3088 = true) by chk.
repeat match goal with |- _ /\ _ => split end; try lia; try exact lock_quar; try CL.
- exists 0, 0. repeat split; try reflexivity; apply (cellZ (bT cs) 80 3088 _ _ ZT); change (uE E (bT cs)) with T; lia.
- exists 0, 0. repeat split; try reflexivity; CL.
- constructor.
- intros b [].
- intros b it [].
- cbn. constructor.
- intros b [].
Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva cs CHKL E R model HC"] Theorem as0_art_rt_ia : forall (FSG : Type) (gfs0 : FSG) (k0 : nat), art_rt_ia FSG (art_gs0 FSG gfs0 k0) FULL.
Proof.
intros FSG gfs0 k0. unfold art_rt_ia. cbn [art_gs0 g_ia g_qt g_qg].
repeat match goal with |- _ /\ _ => split end; try CL.
- intros H. discriminate H.
- intros _. split; reflexivity.
Qed.

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs R FULL model HC"] Lemma var_in : forall e lo hi, is_var_in (kn cs) e lo hi = true -> lo <= uE E e <= hi.
  Proof.
    intros e lo hi H. unfold is_var_in in H. destruct e; try discriminate.
    apply existsb_exists in H as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
    pose proof (hb_kn ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ HC Hin) as HK. cbn [kentry_ok] in HK. unfold uE. lia.
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH E R model HC"] Lemma img_zero4 : forall lo hi a, img_cover (kn cs) lo hi = true -> lo <= a -> a + 4 <= hi -> DEP_LO <= a -> a + 4 <= DEP_HI -> cellA FULL a 4 0.
Proof.
intros lo hi a H H1 H2 H3 H4. unfold img_cover in H. apply existsb_exists in H as (K & Hin & Hc).
destruct K as [| | | l h | | | | | |]; try discriminate. apply andb_prop in Hc as [L1 L2]. apply Z.leb_le in L1. apply Z.leb_le in L2.
unfold cell.
assert (HN : forall x : word, a <= bv_unsigned x < a + Z.of_nat 4 -> FULL x = None).
{ intros x Hx. cbn in Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x).
apply (hb_img ASEGS0 ASAN0 Mh_0132.AsanInitK.LIMIT SINV argH fs asan0_hull_ok AH E cs R FULL model l h HC Hin); [lia|].
unfold in_hull, DEP_LO, DEP_HI in *. cbn [img_lo img_hi ASAN0]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
pose proof (as0_dep_rdn_zero FULL 4%nat a H3 ltac:(cbn; lia) HN) as Hz. unfold ASEGS0 in Hz. rewrite Hz.
rewrite (wleb_zero 4 ltac:(lia)). reflexivity.
Qed.

  Definition K0D : nat := 16384%nat.

  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHK0 CHKL CHKS R model HC HGEO_STK HSP16"] Theorem as0_art_rt_depot : forall (FSG : Type) (gfs0 : FSG), art_rt_depot FSG rn (art_gs0 FSG gfs0 K0D) FULL.
  Proof.
    intros FSG gfs0. unfold art_rt_depot. cbn [art_gs0 g_depot as0_rn rn_l2 rn_blk rn_keys]. apply DInvK_nil. unfold DInvD. unfold NID, STO, MAP1, DEP, apart.
    exists 1, (uE E (tfE cs)), (uE E (stE cs)).
    pose proof sp0_win as W. RG I_L2 0x100000. RG I_BLK 0x800000. RA I_L2 I_BLK 0x100000 0x800000.
    destruct G as (l1 & l2 & l3 & l4 & l5 & l6). destruct G0 as (b1 & b2 & b3 & b4 & b5 & b6).
    pose proof (var_in (tfE cs) 2 3 ltac:(chk)) as VT. pose proof (var_in (stE cs) 2 3 ltac:(chk)) as VS.
    pose proof (cellW (ELit 0) 0x231948 8 (tfE cs) ltac:(chk)) as X1. rewrite uE0 in X1.
    pose proof (cellW (ELit 0) (0x231948 + 24) 4 (stE cs) ltac:(chk)) as X2. rewrite uE0 in X2.
    pose proof (cellW (ELit 0) 0x641968 8 (bL2 cs) ltac:(chk)) as X3. rewrite uE0 in X3.
    pose proof (cellW (ELit 0) (0x231948 + 16) 8 (bBLK cs) ltac:(chk)) as X4. rewrite uE0 in X4.
    pose proof (wrK (ELit 0) 0x241958 4194308 ltac:(chk)) as W1. rewrite uE0 in W1.
    pose proof (wrK (ELit 0) 0x231948 32 ltac:(chk)) as W2. rewrite uE0 in W2.
    pose proof (wrK (bL2 cs) 0 (2 ^ 20) ltac:(chk)) as W3. rewrite Z.add_0_r in W3.
    pose proof (wrK (bBLK cs) 0 (2 ^ 23) ltac:(chk)) as W4. rewrite Z.add_0_r in W4.
    change (uE E (bL2 cs)) with (rbase E cs I_L2) in *. change (uE E (bBLK cs)) with (rbase E cs I_BLK) in *.
    unfold K0D. change (Z.of_nat 16384) with 16384.
    repeat match goal with |- _ /\ _ => split end; try assumption; try lia; try CL.
    - (* [comment removed for export] *)
      intros b Hb.
      pose proof (cellW (ELit 0) B1 4 (e_at (kn cs) (ELit 0) B1 4) ltac:(chk)) as Y1. rewrite uE0 in Y1. pose proof (var_in (e_at (kn cs) (ELit 0) B1 4) 0 1 ltac:(chk)) as V1.
      pose proof (cellW (ELit 0) B2 4 (e_at (kn cs) (ELit 0) B2 4) ltac:(chk)) as Y2. rewrite uE0 in Y2. pose proof (var_in (e_at (kn cs) (ELit 0) B2 4) 0 1 ltac:(chk)) as V2.
      unfold B1, B2 in *.
      destruct (Z.eq_dec b 517153) as [->|N1]; [eexists; split; [exact Y1 | lia]|].
      destruct (Z.eq_dec b 21776) as [->|N2]; [eexists; split; [exact Y2 | lia]|].
      exists 0. split; [|lia].
      destruct (Z_lt_dec b 21776); [|destruct (Z_lt_dec b 517153)].
      + apply (img_zero4 DEP_LO 2452888); [chk | unfold DEP_LO; lia | lia | unfold DEP_LO; lia | unfold DEP_HI; lia].
      + apply (img_zero4 (2452888 + 4) 4434396); [chk | lia | lia | unfold DEP_LO; lia | unfold DEP_HI; lia].
      + apply (img_zero4 (4434396 + 4) DEP_HI); [chk | lia | unfold DEP_HI; lia | unfold DEP_LO; lia | unfold DEP_HI; lia].
    - (* [comment removed for export] *)
      intros id Hid. assert (id = 1) by lia. subst id.
      pose proof (cellW (bL2 cs) 16 8 (e_at (kn cs) (bL2 cs) 16 8) ltac:(chk)) as N1. pose proof (cellW (bL2 cs) 24 4 (ELit 0) ltac:(chk)) as N2. rewrite uE0 in N2.
      change (uE E (bL2 cs)) with (rbase E cs I_L2) in *.
      exists (uE E (e_at (kn cs) (bL2 cs) 16 8)), 0. pose proof (u64_range (edenot E (e_at (kn cs) (bL2 cs) 16 8))). unfold uE in *.
      repeat split; try lia; [exact N1 | replace (rbase E cs I_L2 + 16 * 1 + 8) with (rbase E cs I_L2 + 24) by ring; exact N2].
  Qed.

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva CHKL R model HC"] Theorem as0_art_rt_ghost : forall (FSG : Type) (gfs0 : FSG) (k0 : nat), art_rt_ghost FSG rn (art_gs0 FSG gfs0 k0) FULL.
Proof.
intros FSG gfs0 k0. assert (C : cellA FULL (0x15c6f0 + 72) 8 0xe666661) by CL.
unfold art_rt_ghost. cbn [art_gs0 g_qt g_qg g_cls app]. split; [intros b it []|]. split; [|split; [intros b []|exact C]].
intros c Hc. cbn [art_cls0 cl_au cl_mfa cl_cache length]. split; [intros X; exfalso; lia|]. pose proof (art_ic_mc_range c ltac:(lia)). cbn. lia.
Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHK0 CHKL CHKS R model HC HGEO_SPB HGEO_STK HSP16"] Theorem as0_art_alloc_rep : forall (FSG : Type) (gfs0 : FSG), art_alloc_rep FSG rn (art_gs0 FSG gfs0 K0D) [] FULL.
  Proof.
    intros FSG gfs0. unfold art_alloc_rep.
    exact (conj as0_art_run_ok (conj as0_art_rt_statics (conj as0_art_rt_thread (conj (as0_art_rt_primary FSG gfs0 K0D)
             (conj (as0_art_rt_chunks FSG gfs0 K0D) (conj (as0_art_rt_sec FSG gfs0 K0D) (conj (as0_art_rt_quar FSG gfs0 K0D)
             (conj (as0_art_rt_depot FSG gfs0) (conj (as0_art_rt_ia FSG gfs0 K0D) (conj (fun b (Hb : In b []) => match Hb with end) (as0_art_rt_ghost FSG gfs0 K0D))))))))))).
  Qed.

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs R model HC"] Lemma byteZ : forall b off n a, chk_zero (kn cs) b off n = true -> uE E b + off <= a < uE E b + off + n -> byte_at FULL a 0.
  Proof.
    intros b off n a H Ha. unfold byte_at.
    destruct (hc_zero ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model b off n HC H) as (_ & _ & Hz).
    replace a with (uE E b + off + (a - (uE E b + off))) by ring. apply Hz. lia.
  Qed.

  (* [comment removed for export] *)
  Definition KSH : Z := 0x7fff8000 + 8192 * (SPB / 65536).
  Definition as0_EXTRA : list (Z * Z) := [(KSH, KSH + 2 ^ 34)].
  Definition as0_A0x : list (Z * Z) := as0_A0 as0_EXTRA cs E.

  #[using="Type"] Lemma as0_EXTRA_wf : A_wf as0_EXTRA.
  Proof.
    unfold A_wf, as0_EXTRA, KSH, page_size. constructor; [|constructor]. cbn [fst snd].
    set (q := SPB / 65536).
    replace (2147450880 + 8192 * q) with ((524280 + 2 * q) * 4096) by ring.
    replace ((524280 + 2 * q) * 4096 + 2 ^ 34) with ((524280 + 2 * q + 4194304) * 4096) by ring.
    rewrite !Z.mod_mul by lia. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma vis_shadow_allowed : forall b n a m, vis_in cs b n = true ->
    uE E b <= a -> a + m <= uE E b + uE E n -> (uE E b + uE E n) mod 8 = 0 -> 0 < m -> 0 <= a -> a + m <= 2 ^ 47 ->
    shadow_allowed as0_A0x a m.
  Proof.
    intros b n a m Hv H1 H2 H8 Hm Ha Hhi x [X1 X2]. unfold OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA.S, OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA.SB in X1, X2.
    unfold vis_in in Hv. apply existsb_exists in Hv as (p & Hp & Hb). apply andb_prop in Hb as [Eb En].
    apply expr_eqb_eq in Eb. apply expr_eqb_eq in En. destruct p as [pb pn]. cbn [fst snd] in Eb, En. subst pb pn.
    pose proof (page_base_le (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) 0%nat (Z_to_bv 64 x)) as (P1 & P2 & P3).
    assert (Hx : 0 <= x < 2 ^ 64).
    { pose proof (Z.div_pos a 8 Ha ltac:(lia)). assert ((a + m - 1) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8) with (2 ^ 44) in *. lia. }
    rewrite u64_lit in P1, P2 by exact Hx.
    unfold as0_A0x, as0_A0, A0_of, page_allowedb. rewrite existsb_app. apply orb_true_iff. left.
    apply existsb_exists. exists (pagedown (sh_lo ASAN0 E (b, n)), pageup (sh_hi ASAN0 E (b, n))). split.
    - unfold allowA. apply in_flat_map. exists (b, n). split; [apply in_or_app; left; exact Hp|]. right. left. reflexivity.
    - cbn [fst snd]. unfold sh_lo, sh_hi, page_size. cbn [fst snd shadow_off ASAN0].
      assert (L1 : uE E b / 8 <= a / 8) by (apply Z.div_le_mono; lia).
      assert (L2 : (a + m - 1) / 8 < (uE E b + uE E n) / 8).
      { pose proof (Z.div_mod (uE E b + uE E n) 8 ltac:(lia)) as D. rewrite H8 in D.
        assert ((a + m - 1) / 8 <= (uE E b + uE E n - 1) / 8) by (apply Z.div_le_mono; lia).
        assert ((uE E b + uE E n - 1) / 8 < (uE E b + uE E n) / 8); [|lia].
        apply Z.div_lt_upper_bound; [lia|]. lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      apply andb_true_intro. split; apply Z.leb_le; unfold pagedown, pageup; lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  (* [comment removed for export] *)
  Variables BUDGET LENMAX : Z.
  Hypothesis BUD : 0 <= BUDGET /\ 0 <= NarInv.KMAX /\ 0 <= LENMAX < 2 ^ 62.
  Hypothesis BUD_le : a_eager cs + a_abytes cs + 2 ^ 34 + BUDGET <= AsanInitK.LIMIT.
  Hypothesis BUD_ge : 2 ^ 36 + 2 ^ 20 + PRIMCAP <= BUDGET.      (* [comment removed for export] *)
  Hypothesis GAP : AsanCeil.bottomup_floor + LENMAX + (a_totsz cs + BUDGET)
                   + (Z.of_nat (length (segments_reserved ASEGS0) + n_resx ASAN0 + length (a_maps cs)) + NarInv.KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.

  #[local] Notation MAPS0 := (vm_maps (m_vmmaps model)).
  (* [comment removed for export] *)
  #[local] Notation RESV0 := (vm_reserved (m_vmmaps model)).
  #[local] Notation NOACC0 := (vm_noaccess (m_vmmaps model)).
  Definition as0_BASEx : Z := as0_BASE as0_EXTRA cs.

  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva CHK0 R HC LENMAX BUD BUD_le GAP"] Theorem as0_art_binv :
    BINV Asan.M.loaded_segments MAPS0 RESV0 NOACC0 (rn_HI rn) as0_BASEx BUDGET [] as0_A0x FULL (m_vmmaps model) (m_vm_lazy model).
  Proof.
    apply BINV_intro. unfold rn_HI. cbn [as0_rn as0_ar rn_ar ar_sptop].
    assert (Hb : a_eager cs + a_abytes cs + A_bytes as0_EXTRA + BUDGET <= AsanInitK.LIMIT).
    { unfold as0_EXTRA. cbn [A_bytes fst snd]. lia. }
    exact (as0_binv_main sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva BUDGET LENMAX NarInv.KMAX BUD as0_EXTRA as0_EXTRA_wf cs CHK0 Hb GAP E R FULL model HC).
  Qed.

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva cs CHK0 E R model HC BUDGET LENMAX BUD BUD_le GAP"] Lemma as0_shdef : forall a : word, in_shadow_rw (bv_unsigned a) -> FULL a <> None.
  Proof.
    assert (Hb : a_eager cs + a_abytes cs + A_bytes as0_EXTRA + BUDGET <= AsanInitK.LIMIT).
    { unfold as0_EXTRA. cbn [A_bytes fst snd]. lia. }
    pose proof (as0_binv_main sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva BUDGET LENMAX NarInv.KMAX BUD as0_EXTRA as0_EXTRA_wf cs CHK0 Hb GAP E R FULL model HC) as B.
    intros a Ha. eapply bi_shdef; [exact B | exact Ha].
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHK0 E R model HC BUDGET LENMAX BUD BUD_le GAP"] Lemma byte1 : forall a v, chk_word (kn cs) (ELit 0) a 1 (ELit v) = true -> 0 <= a < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> in_shadow_rw a -> byte_at FULL a v.
  Proof.
    intros a v H Ha Hv Hs. pose proof (cellW (ELit 0) a 1 (ELit v) H) as X. rewrite uE0, (uE_lit E v Hv), Z.add_0_l in X.
    unfold cell in X. rewrite (art_bytes1 v Hv) in X. cbn [rdn] in X. unfold byte_at.
    pose proof (as0_shdef (Z_to_bv 64 a) ltac:(rewrite u64_lit by lia; exact Hs)) as D.
    destruct (FULL (Z_to_bv 64 a)) as [b|]; [|contradiction]. injection X as ->. reflexivity.
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHK0 E R model HC BUDGET LENMAX BUD BUD_le GAP"] Lemma glob_ok : forall g, glob_chk (kn cs) g = true -> shadow_blk FULL (fst g) (snd g).
Proof.
intros [beg size] H. cbn [fst snd]. unfold glob_chk in H. cbn [fst snd] in H. chk_split H.
repeat match goal with X : Z.leb _ _ = true |- _ => apply Z.leb_le in X | X : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in X end.
assert (Q1 : 0x10000 / 8 <= beg / 8) by (apply Z.div_le_mono; lia). assert (Q2 : beg / 8 <= 0x6b6000 / 8) by (apply Z.div_le_mono; lia).
change (0x10000 / 8) with 8192 in Q1. change (0x6b6000 / 8) with 879616 in Q2.
assert (Q3 : 0 <= size / 8) by (apply Z.div_pos; lia). assert (Q4 : size / 8 <= 8192 / 8) by (apply Z.div_le_mono; lia). change (8192 / 8) with 1024 in Q4.
pose proof (Z.mod_pos_bound size 8 ltac:(lia)) as Q5.
unfold shadow_blk, shadow_zero, Mh_0089.HeapIfaceA.S, Mh_0089.HeapIfaceA.SB. split.
- intros j Hj. apply orb_prop in H as [H|H]; [apply Z.eqb_eq in H; lia|].
  apply (byteZ (ELit 0) (beg / 8 + 0x7fff8000) (size / 8)); [assumption | rewrite uE0; lia].
- intros NZ. apply byte1; [match goal with X : (if Z.eqb (size mod 8) 0 then true else ?c) = true |- ?c = true => destruct (Z.eqb_spec (size mod 8) 0) as [E0|_]; [exfalso; exact (NZ E0) | exact X] end
| lia | lia | unfold in_shadow_rw, LSH_LO, LSH_HI; left; lia].
Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHK0 CHKL CHKS R model HC HGEO_STK HSP16 BUDGET LENMAX BUD BUD_le GAP"] Theorem as0_art_c_statics : art_c_statics rn FULL.
Proof.
unfold art_c_statics. cbn [as0_rn as0_ar rn_tp rn_dtls]. unfold TP.
pose proof sp0_win as W.
pose proof (rgl I_DTLS 4096 ltac:(IDX) ltac:(chk) ltac:(lia)) as (d1 & d2 & d3 & d4).
pose proof (xpos (bD cs) ltac:(chk)) as PD. change (uE E (bD cs)) with (rbase E cs I_DTLS) in PD.
assert (D4 : 4096 <= rbase E cs I_DTLS) by (pose proof (Z.div_mod (rbase E cs I_DTLS) 4096 ltac:(lia)); lia).
split; [repeat split; lia|].
split; [CL|]. split; [CL|]. split; [CL|].
split. { pose proof (cellW (ELit 0) (TP + 8) 8 (bD cs) ltac:(chk)) as X. rewrite uE0 in X. exact X. }
split. { pose proof (cellW (bD cs) 24 8 (ELit TP) ltac:(chk)) as X. rewrite (uE_lit E TP) in X by (unfold TP; lia). exact X. }
split.
{ intros x Hx. change (Mh_0089.HeapIfaceA.S 0x10000) with 2147459072 in Hx. change (Mh_0089.HeapIfaceA.S 0x23a40) with 2147469128 in Hx. change (Mh_0089.HeapIfaceA.S 0x23ac0) with 2147469144 in Hx. change (Mh_0089.HeapIfaceA.S 0x23ae0) with 2147469148 in Hx. change (Mh_0089.HeapIfaceA.S 0x23bc0) with 2147469176 in Hx. change (Mh_0089.HeapIfaceA.S 0x23c20) with 2147469188 in Hx. change (Mh_0089.HeapIfaceA.S 0x265c0) with 2147470520 in Hx. change (Mh_0089.HeapIfaceA.S 0x26660) with 2147470540 in Hx. change (Mh_0089.HeapIfaceA.S 0x26680) with 2147470544 in Hx. change (Mh_0089.HeapIfaceA.S 0x267e0) with 2147470588 in Hx. change (Mh_0089.HeapIfaceA.S 0x26e20) with 2147470788 in Hx. change (Mh_0089.HeapIfaceA.S 0x26f40) with 2147470824 in Hx. change (Mh_0089.HeapIfaceA.S 0x26fc0) with 2147470840 in Hx. change (Mh_0089.HeapIfaceA.S 0x27020) with 2147470852 in Hx. change (Mh_0089.HeapIfaceA.S 0x272a0) with 2147470932 in Hx. change (Mh_0089.HeapIfaceA.S 0x151520) with 2147623588 in Hx. change (Mh_0089.HeapIfaceA.S 0x1515a0) with 2147623604 in Hx. change (Mh_0089.HeapIfaceA.S 0x15b8a0) with 2147628820 in Hx. change (Mh_0089.HeapIfaceA.S 0x15c3a0) with 2147629172 in Hx. change (Mh_0089.HeapIfaceA.S 0x6b6000) with 2148330496 in Hx.
destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[Hx|Hx]]]]]]]]].
- apply (byteZ (ELit 0) 2147459072 10056); [chk | rewrite uE0; lia].
- apply (byteZ (ELit 0) 2147469144 4); [chk | rewrite uE0; lia].
- apply (byteZ (ELit 0) 2147469176 12); [chk | rewrite uE0; lia].
- apply (byteZ (ELit 0) 2147470520 20); [chk | rewrite uE0; lia].
- apply (byteZ (ELit 0) 2147470544 44); [chk | rewrite uE0; lia].
- apply (byteZ (ELit 0) 2147470788 36); [chk | rewrite uE0; lia].
- apply (byteZ (ELit 0) 2147470840 12); [chk | rewrite uE0; lia].
- apply (byteZ (ELit 0) 2147470932 152656); [chk | rewrite uE0; lia].
- apply (byteZ (ELit 0) 2147623604 5216); [chk | rewrite uE0; lia].
- apply (byteZ (ELit 0) 2147629172 701324); [chk | rewrite uE0; lia]. }
split; [|exact as0_shdef].
assert (HG : forallb (glob_chk (kn cs)) ART_GLOBALS = true) by chk.
apply Forall_forall. intros g Hg. exact (glob_ok g (proj1 (forallb_forall _ _) HG g Hg)).
Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHK0 CHKL CHKS R model HC HGEO_STK HSP16 BUDGET LENMAX BUD BUD_le GAP"] Theorem as0_art_fsinv : art_fsinv_handoff -> art_fsinv rn art_fsg0 [] [] FULL.
  Proof.
    intros FSH. apply FSH; cbn [as0_rn as0_ar rn_ar rn_t rn_tp ar_fs]; unfold TP.
    - (* [comment removed for export] *)
      unfold art_fs_geo, rn_HI, app_mem, BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES. cbn [as0_rn as0_ar rn_ar rn_t rn_tp ar_fs ar_sptop]. unfold TP.
      pose proof sp0_win as W. RG I_FAKE 0xb09000. RA I_FAKE I_THREAD 0xb09000 4096. RG I_THREAD 4096.   (* [comment removed for export] *)
      destruct G as (f1 & f2 & f3 & f4 & f5 & f6). specialize (f6 ltac:(unfold I_FAKE; lia)).
      pose proof (xpos (bF cs) ltac:(chk)) as PF. change (uE E (bF cs)) with (rbase E cs I_FAKE) in PF.
      assert (F4 : 4096 <= rbase E cs I_FAKE) by (pose proof (Z.div_mod (rbase E cs I_FAKE) 4096 ltac:(lia)); lia).
      repeat split; lia.
    - pose proof (wrK (bF cs) 0 0xb09000 ltac:(chk)) as W. rewrite Z.add_0_r in W. exact W.
    - pose proof (cellW (ELit 0) TP 8 (bF cs) ltac:(chk)) as X. rewrite uE0 in X. exact X.
    - exact (cellW (bT cs) 72 8 (bF cs) ltac:(chk)).
    - pose proof (cellW (bF cs) 88 8 (ELit 20) ltac:(chk)) as X. rewrite (uE_lit E 20) in X by lia. exact X.
    - intros a Ha Hn. change (rbase E cs I_FAKE) with (uE E (bF cs)) in *.
      destruct (Z_lt_dec a (uE E (bF cs) + 88)).
      + apply (byteZ (bF cs) 0 88); [chk | lia].
      + apply (byteZ (bF cs) 96 (4096 + 32768 - 96)); [chk | lia].
    - exact as0_art_c_statics.                                                   (* [comment removed for export] *)
  Qed.

  #[using="LENMAX BUD_ge GAP"] Theorem as0_art_credit : forall (FSG : Type) (gfs0 : FSG), art_credit_ok FSG BUDGET rn (art_gs0 FSG gfs0 K0D) [] (KCNT, 2 ^ 36).
Proof.
ltac2:(KReplay.run1 (kr_t_NraArtHandoffK ()) ["Derive"] "h02Hah17__arithh24__ffh38__varmaph45__with56__sat0h66__sat1h74__x1h83FSGh96__sat2h:6__sat3h;6__sat4h<6__sat5h=4gfs0p;2p;1p;3p;4p;8p;9p;7p200R0p105=dp4p710p8P0g06NKR1p4p710p8g031Kj2WTg00DWj12Tg009?j10Tg00Q3j15Tg00J7j2>Tg020Aj2<Tg00JTj27Tg020ij3;Tg002\j1GTg001@j1ETg02Udj1DTg00V[j1VTg00W9j1UTg00Wdj26Tg00Kmj1=Tg02Klj3:Tg00Z\j2QTg00?\j2PTg00[>j2OTg005Wj3NTg00[jj3MTg00\Ij4JTg00V=j2ITg00YUj3@Tg02lfj3ATg00XGj2HTg00=Vj1KTg02a`j3FTg00Z8j8LTg00];j2BTg02k7j2?Tg00I[j24Tg01bej2CTP1l9RTg00Xjj4STg00_:j7TTf0R1#2#2p=3g00PUR2/41p=1g00P7R3f1R4g00bmP1CSp=8P4g00`BR5g00`aR6P6g00aAR7P1g00aaFTp=9P4p,6BUDGETR8p,1Ep,2cs'WP1g06OQg00G]R9#2R:#0R;%2:R<#5#3R=#0R>'>R?1<;>R@172;RA%1>172?[[RB%1;RCg00H_RDA;;>4UW0R>%1?RE\D^0CRFg00bARG#GRH%EGRG%D3RI%V3RJ%U3RK1632163;RL%==5:3R='8'91QK7RMP1f2RNg0061ROg006QRP'P1O1N=NOPdAM324CJRPb2b3b4PEP1b1b5b6P@PBP>PF%2<#3R<#0RF,<;%1F1>;FR>,72[\AA;;F4VDX0C%1>\D^0C%5:#3R:#0RF,<;%1F1>;FRB,72[\AA;;F4VDX0C%1B\D^0CPHPG1I34PJPKP5P6P6P7%=:9:3L9@3=R=%59#5#5#2#0R:,63%=<9:3L5A3R75@31H39R9'8,9K%K6AF397,8=,9KGLPMPPb2b3b4X731B?BRB1?:>R:'B/411C4:,4B[^73P1P8p,6BUD_geO2b1b5b6b9b:b;b<g06PH,C8,4BePHPGPIPJ%3<#3#3#3R<#0RJ,639A3L%2<#0R<,63'8,9KPMPPb2b3b41?;J/4<P1b1g06QC,?;/4<eM9RX=1X80o"). Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R model HC HGEO_STK HSP16 HSPA BUDGET LENMAX GAP"] Theorem as0_art_client : art_client_ok rn [] [] [] as0_A0x FULL.
  Proof.
    unfold art_client_ok. cbn [as0_rn as0_ar rn_ar ar_sptop ar_fs ar_stack_top ar_stack_bottom map].
    pose proof sp0_win as W. destruct HGEO_STK as (S1 & S2 & S3 & S4 & S5).
    pose proof (isp_facts_of ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model HC) as ISP.
    pose proof (u_e_top ASEGS0 ASAN0 asan0_res_len asan0_hull_ok E ISP) as UT. pose proof (u_e_stk_len ASEGS0 ASAN0 asan0_res_len asan0_hull_ok E ISP) as UL.
    pose proof (utop_bounds E) as UB.
    repeat match goal with |- _ /\ _ => split end; try lia.
    - intros b [].
    - constructor.
    - (* [comment removed for export] *)
      apply (vis_shadow_allowed e_top e_stk_len); [chk | lia | lia | rewrite UT, UL; replace (utop E + (2 ^ 47 - utop E)) with (2 ^ 47) by ring; reflexivity | lia | lia | lia].
    - (* [comment removed for export] *)
      RG I_FAKE 0xb09000. destruct G as (f1 & f2 & f3 & f4 & f5 & f6).
      apply (vis_shadow_allowed (bF cs) (ELit 0xb09000)); change (uE E (bF cs)) with (rbase E cs I_FAKE); rewrite ?(uE_lit E 0xb09000) by lia; unfold FS_BYTES; try lia; [chk|].
      pose proof (Z.div_mod (rbase E cs I_FAKE) 4096 ltac:(lia)) as D. rewrite f1 in D.
      replace (rbase E cs I_FAKE + 11571200) with ((512 * (rbase E cs I_FAKE / 4096) + 1446400) * 8) by lia. apply Z.mod_mul. lia.
    - (* [comment removed for export] *)
      apply (vis_shadow_allowed (ELit 0x10000) (ELit 0x6a6000)); rewrite ?(uE_lit E 0x10000), ?(uE_lit E 0x6a6000) by lia; try lia; [chk | reflexivity].
    (* [comment removed for export] *)
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis CHKZ : art_lazy_chk cs = true.
  #[local] Notation PARR := (rbase E cs I_PARR).
  #[local] Notation BLKB := (rbase E cs I_BLK).
  #[local] Notation RIS := (SPB + 2 ^ 37).

  #[using="CHKZ"] Lemma lazy_parts : exists h1 h2, a_hlz cs = h1 ++ HSub (E_RISX cs) (ELit 4096) :: h2 /\ forallb (hop_pre cs) h1 = true
    /\ forallb (hop_zone cs) (a_hlz cs) = true
    /\ forallb (fun p => vis_hi (kn cs) p && own_ok cs p)%bool (a_vis cs ++ a_ghost cs) = true
    /\ 12 <= ealign (kn cs) (bBLK cs) /\ vis_in cs (bBLK cs) (ELit 0x800000) = true.
  Proof.
    pose proof CHKZ as H. unfold art_lazy_chk in H.
    apply andb_prop in H as [H C5]. apply andb_prop in H as [H C4]. apply andb_prop in H as [H C3]. apply andb_prop in H as [C1 C2].
    destruct (hsplit (E_RISX cs) (a_hlz cs)) as [[h1 h2]|] eqn:Hs; [|discriminate].
    exists h1, h2. split; [exact (hsplit_eq _ _ _ _ Hs)|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
    split; [apply Z.leb_le; exact C4 | exact C5].
  Qed.

  #[using="Type"] Lemma is_rng_sound : forall b n b0 L, is_rng b n b0 L = true -> 0 <= L < 2 ^ 64 -> uE E b = uE E b0 /\ uE E n = L.
  Proof.
    intros b n b0 L H HL. unfold is_rng in H. apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1. apply expr_eqb_eq in H2. subst.
    split; [reflexivity | apply uE_lit; exact HL].
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL model HC HGEO_SPB HGEO_STK HSP16 BUDGET LENMAX GAP"] Lemma ris_val2 : uE E (E_RISX cs) = RIS.
  Proof.
    unfold E_RISX, uE. cbn [edenot]. rewrite u_add64. cbn [edenot]. rewrite (u64_lit 0x2000010000) by lia.
    pose proof sp0_win. destruct HGEO_SPB as ((K1 & K2) & _).
    pose proof (rgl I_KSPACE 0x2000011000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (g1 & g2 & g3 & g4).
    unfold uE in *. rewrite Z.mod_small by lia. lia.
  Qed.

  #[using="CHK0"] Lemma hlz_ok : hops_in_maps (a_maps cs) (a_hlz cs) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_NraArtHandoffK ()) ["Derive"] "p'0h01Hh11mh22H0h32H1h42H2h52H3h62H4h72H5h82H6h92H7h:2H8i002loi011xp;1p;2p;3g00d;j1GTg00e;j1>Tg00f<j1:Tg00g=j1FTg00h=j27Tg00?>j23Tg00iEj1=Tg008=j2<Tg00jEj1;Tg00kBj29Tg00lGj18Tg000dj34Tg00mGj1ETg00nOj1DTg00E<j3BTg00oQj16Tg010Tj35Tg0110j1@Tg0122j2?Tg00Raj2ATg003\j32Tg004?R0j21Tg005Wj3CTg0061R1f0R2g006Q3Cp=0p,4CHK0p,2csR3#G#0%>3R4#:R5%F3,74R6'3R7%=3,74R8'3R9g00FYR:/<:R:g0133%;3R;'9%83R<34R='3R>%E;%D39B:<54:R:'3R<g013nR3g014o#6;54R?'3R@g015n#6=534RA'3RBg016m#6=534RC'3RD%62=534X13g017mR4543RE'3RFg008]g00P7P1%@2,?;g00PU/A2g00I;n10110100021010000X13=434R4;22%0FRF%04R4'1P0PFP4%08R3P2f1R;92DE%0DRD%0ERE'1P0PDPEP3P2A2BC;%0BRB%0CRC'1P0PBPCP3P2A2@A;%0@R@%0ARA'1P0P@PAP3P2A2<?;%0<R<%0?R?'1P0P<P?P3P2A2>:;%0>R>%0:R:'1P0P>P:P3P2A29=;%09R9%0=R='1P0P9P=P3P2A278;%07R7/13P0P7P3P3P2A256;%05R5%06R6'1P0P5P6P3P2f5X:6X05P;P2O2n2001000000120000000b0X93X07P;P2O2n2001000000120000000b0X8=X09P;P2O2n2001000000120000000b0X7:X0>P;P2O2n2001000000121000000b0X6?X0<P;P2O2n2001000000121000000b0X5AX0@P;P2O2n2001000000121000000b0X4CX0BP;P2O2n2001000000121000000b0X3EX0DP;P2O2n2001000000121000000b0X24X0FP;P2O2n2001000000121000000b0b0o"). Qed.

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL HC HGEO_SPB HGEO_STK HSP16 BUDGET LENMAX GAP CHKZ"] Lemma lazy_piece : forall q, In q (m_vm_lazy model) ->
    let b := bv_unsigned (fst q) in let e := bv_unsigned (fst q) + bv_unsigned (snd q) in
    ((BLKB <= b /\ e <= BLKB + 0x800000) \/ (PARR <= b /\ e <= PARR + 0x800000) \/ (KB <= b /\ e <= KB + 0x2000011000)
     \/ (0x7fff7000 <= b /\ e <= 0x10007fff8000))
    /\ (e <= RIS \/ RIS + 4096 <= b) /\ b < e.
  Proof.
    intros q Hq. cbv zeta. rewrite (hb_lazy ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model HC) in Hq.
    destruct lazy_parts as (h1 & h2 & Hsplit & Hpre & Hzone & _).
    pose proof (hl_hops_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model (a_hlz cs) HC nofog hlz_ok) as WF.
    destruct (hl_replay E (a_hlz cs) WF q Hq) as (P1 & P2 & b & n & Hb & P3 & P4).
    split; [|split; [|lia]].
    - pose proof (proj1 (forallb_forall _ _) Hzone (HCons b n) Hb) as Hz. cbn [hop_zone] in Hz.
      repeat (apply orb_prop in Hz as [Hz|Hz]).
      + destruct (is_rng_sound _ _ _ _ Hz ltac:(lia)) as [E1 E2]. left. change (uE E (bBLK cs)) with BLKB in E1. lia.
      + destruct (is_rng_sound _ _ _ _ Hz ltac:(lia)) as [E1 E2]. right. left. change (uE E (bP cs)) with PARR in E1. lia.
      + destruct (is_rng_sound _ _ _ _ Hz ltac:(lia)) as [E1 E2]. right. right. left. change (uE E (bKS cs)) with KB in E1. lia.
      + destruct (is_rng_sound _ _ _ _ Hz ltac:(lia)) as [E1 E2]. rewrite (uE_lit E 0x7fff7000) in E1 by lia. right. right. right. lia.
      + destruct (is_rng_sound _ _ _ _ Hz ltac:(lia)) as [E1 E2]. rewrite (uE_lit E 0x8fff7000) in E1 by lia. right. right. right. lia.
      + destruct (is_rng_sound _ _ _ _ Hz ltac:(lia)) as [E1 E2]. rewrite (uE_lit E 0x2008fff7000) in E1 by lia. right. right. right. lia.
    - rewrite Hsplit in Hq, WF.
      pose proof (hl_replay_sub E h1 (E_RISX cs) (ELit 4096) h2 WF) as SUB. rewrite ris_val2, (uE_lit E 4096) in SUB by lia.
      apply SUB; [|exact Hq]. intros b' n' Hin.
      pose proof (proj1 (forallb_forall _ _) Hpre (HCons b' n') Hin) as Hp. cbn [hop_pre] in Hp.
      destruct HGEO_SPB as ((K1 & K2) & _).
      apply orb_prop in Hp as [Hp|Hp]; destruct (is_rng_sound _ _ _ _ Hp ltac:(lia)) as [E1 E2]; rewrite E1, E2.
      + change (uE E (bBLK cs)) with BLKB.
        destruct (ra I_BLK I_KSPACE 0x800000 0x2000011000 ltac:(IDX) ltac:(IDX) ltac:(IDX) ltac:(chk) ltac:(chk) ltac:(lia) ltac:(lia)) as [X|X]; [left | right]; lia.
      + change (uE E (bP cs)) with PARR.
        destruct (ra I_PARR I_KSPACE 0x800000 0x2000011000 ltac:(IDX) ltac:(IDX) ltac:(IDX) ltac:(chk) ltac:(chk) ltac:(lia) ltac:(lia)) as [X|X]; [left | right]; lia.
  Qed.

  #[using="Type"] Lemma pb_facts : forall x : word, bv_unsigned (page_base x) <= bv_unsigned x < bv_unsigned (page_base x) + 4096 /\ bv_unsigned (page_base x) mod 4096 = 0.
  Proof.
    intros x. pose proof (page_base_le (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) 0%nat x) as (P1 & P2 & P3). auto.
  Qed.

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL HC HGEO_SPB HGEO_STK HSP16 BUDGET LENMAX GAP CHKZ"] Lemma as0_lazy_c1 : forall (FSG : Type) (gfs0 : FSG) (k0 : nat) (w : word),
    page_in_ranges (page_base w) (m_vm_lazy model) = true -> art_lazy_zone FSG rn (art_gs0 FSG gfs0 k0) (bv_unsigned w).
  Proof.
    intros FSG gfs0 k0 w Hl. destruct (hl_page_piece w _ Hl) as (q & Hq & Q1 & Q2).
    destruct (pb_facts w) as ((P1 & P2) & _). destruct (lazy_piece q Hq) as (Hz & Hr & _). cbv zeta in Hz, Hr.
    destruct HGEO_SPB as ((K1 & K2) & _).
    assert (NC : ~ (RIS <= bv_unsigned w < RIS + 4096)) by lia.
    assert (NCOM : ~ art_committed FSG rn (art_gs0 FSG gfs0 k0) (bv_unsigned w)).
    { unfold art_committed, rn_ris, rn_spb. cbn [as0_rn as0_ar rn_ar rn_qs ar_space_beg art_gs0 g_cls g_sec_committed]. unfold art_cls0. cbn [cl_mu cl_mfa].
      rewrite spb_qs. intros [X|[(c & _ & [X|X])|(X & _)]]; [exact (NC X) | lia | lia | discriminate X]. }
    unfold art_lazy_zone. cbn [as0_rn as0_ar rn_ar rn_blk rn_kbase rn_parr]. change (2 ^ 23) with 0x800000.
    destruct Hz as [Z|[Z|[Z|Z]]].
    - right. left. lia.
    - right. right. split; [right; lia | exact NCOM].
    - right. right. split; [left; lia | exact NCOM].
    - left. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="cs E BUDGET LENMAX GAP"] Lemma win_nolazy : forall lo hi, lo mod 4096 = 0 -> hi mod 4096 = 0 ->
    (forall q, In q (m_vm_lazy model) -> bv_unsigned (fst q) + bv_unsigned (snd q) <= lo \/ hi <= bv_unsigned (fst q)) ->
    forall x : word, lo <= bv_unsigned x < hi -> page_in_ranges (page_base x) (m_vm_lazy model) = false.
  Proof.
    intros lo hi Hlo Hhi Hap x Hx. destruct (page_in_ranges (page_base x) (m_vm_lazy model)) eqn:Hl; [exfalso | reflexivity].
    destruct (hl_page_piece x _ Hl) as (q & Hq & Q1 & Q2). destruct (pb_facts x) as ((P1 & P2) & P3).
    pose proof (Z.div_mod lo 4096 ltac:(lia)) as D1. pose proof (Z.div_mod hi 4096 ltac:(lia)) as D2.
    pose proof (Z.div_mod (bv_unsigned (page_base x)) 4096 ltac:(lia)) as D3. rewrite Hlo in D1. rewrite Hhi in D2. rewrite P3 in D3.
    destruct (Hap q Hq) as [X|X]; lia.
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs R FULL model HC BUDGET LENMAX GAP"] Lemma apx_sound : forall zb zn p, apx (kn cs) zb zn p = true -> 0 <= zn < 2 ^ 64 ->
    (uE E zb + zn <= uE E (fst p) \/ uE E (fst p) + uE E (snd p) <= uE E zb) /\ 0 < uE E (snd p) /\ uE E (fst p) + uE E (snd p) <= 2 ^ 64.
  Proof.
    intros zb zn p H Hzn. unfold apx in H. destruct (split_lit zb) as [zb' zk] eqn:Hz. destruct (split_lit (fst p)) as [pb pk] eqn:Hp.
    apply andb_prop in H as [H Hap]. apply andb_prop in H as [Fz Fp].
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    pose proof (flat_x_sound ASEGS0 E _ (kn cs) zb' zk (ELit zn) HK Fz) as (A1 & A2 & A3).
    pose proof (flat_x_sound ASEGS0 E _ (kn cs) pb pk (snd p) HK Fp) as (B1 & B2 & B3).
    pose proof (split_lit_denot E _ zb' zk Hz) as Dz. pose proof (split_lit_denot E _ pb pk Hp) as Dp.
    cbn [edenot] in A2, A3. rewrite (u64_lit zn) in A2, A3 by lia.
    assert (Ez : uE E zb = estart E (SA zb' zk)).
    { unfold uE. rewrite Dz. unfold estart in *; cbn [a_base a_off] in *. rewrite u64_lit by lia. reflexivity. }
    assert (Ep : uE E (fst p) = estart E (SA pb pk)).
    { unfold uE. rewrite Dp. unfold estart in *; cbn [a_base a_off] in *. pose proof (u64_range (edenot E (snd p))). rewrite u64_lit by lia. reflexivity. }
    pose proof (ranges_apart_x_sound ASEGS0 E _ (kn cs) _ _ _ _ _ _ HK Hap) as D.
    unfold elenZ in D. cbn [edenot] in D. rewrite (u64_lit zn) in D by lia. rewrite <- Ez, <- Ep in D.
    split; [exact D|]. split; [exact B3|]. rewrite Ep. unfold uE. lia.
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs R FULL model HC BUDGET LENMAX GAP"] Lemma vis_hi_sound : forall p, vis_hi (kn cs) p = true -> uE E (fst p) + uE E (snd p) <= 2 ^ 47.
  Proof.
    intros p H. unfold vis_hi in H. apply orb_prop in H as [H|H].
    - apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1. apply expr_eqb_eq in H2. rewrite H1, H2.
      pose proof (isp_facts_of ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model HC) as ISP.
      rewrite (u_e_top ASEGS0 ASAN0 asan0_res_len asan0_hull_ok E ISP), (u_e_stk_len ASEGS0 ASAN0 asan0_res_len asan0_hull_ok E ISP). lia.
    - destruct (xhi (kn cs) (fst p)) as [hi|] eqn:Hx; [|discriminate]. destruct (snd p) as [n| | | | | | |] eqn:Hn; try discriminate.
      apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
      pose proof (xhi_sound ASEGS0 E _ (kn cs) (fst p) hi (co_know _ _ _ _ _ _ _ _ _ _ _ HC) Hx) as X.
      unfold uE. cbn [edenot]. rewrite (u64_lit n) by lia. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="cs E BUDGET LENMAX GAP"] Lemma round_apart : forall b n zl zh, zl mod 4096 = 0 -> zh mod 4096 = 0 -> (zh <= b \/ b + n <= zl) ->
    zh <= pagedown b \/ pageup (b + n) <= zl.
  Proof.
    intros b n zl zh Hl Hh Hap. unfold pagedown, pageup.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    destruct Hap as [X|X]; [left | right]; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.
  #[using="cs E BUDGET LENMAX GAP"] Lemma round_al : forall z, pagedown z mod 4096 = 0 /\ pageup z mod 4096 = 0 /\ pagedown z <= z <= pageup z.
  Proof.
    intros z. unfold pagedown, pageup. rewrite !Z.mod_mul by lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    repeat split; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.
  #[using="cs E BUDGET LENMAX GAP"] Lemma round_id : forall z, z mod 4096 = 0 -> pagedown z = z /\ pageup z = z.
  Proof.
    intros z Hz. unfold pagedown, pageup.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    split; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL HC HGEO_SPB HGEO_STK HSP16 BUDGET LENMAX GAP CHKZ"] Lemma own_window : forall p, In p (a_vis cs ++ a_ghost cs) ->
    let lo := pagedown (uE E (fst p)) in let hi := pageup (uE E (fst p) + uE E (snd p)) in
    (BLKB <= lo /\ hi <= BLKB + 0x800000)
    \/ (forall x : word, lo <= bv_unsigned x < hi -> page_in_ranges (page_base x) (m_vm_lazy model) = false).
  Proof.
    intros p Hp. cbv zeta. destruct lazy_parts as (_ & _ & _ & _ & _ & Hvis & HalB & _).
    pose proof (proj1 (forallb_forall _ _) Hvis p Hp) as Hb. apply andb_prop in Hb as [_ Hown].
    pose proof (rgl I_BLK 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (b1 & b2 & b3 & b4).
    pose proof (rgl I_PARR 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (p1 & p2 & p3 & p4).
    pose proof (rgl I_KSPACE 0x2000011000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (g1 & g2 & g3 & g4).
    destruct HGEO_SPB as ((K1 & K2) & K3).
    unfold own_ok in Hown. apply orb_prop in Hown as [Hown|Hown]; [apply orb_prop in Hown as [Hown|Hown]|].
    - (* [comment removed for export] *)
      destruct (is_rng_sound _ _ _ _ Hown ltac:(lia)) as [E1 E2]. rewrite E1, E2. change (uE E (bBLK cs)) with BLKB.
      destruct (round_id BLKB b1) as [R1 _]. destruct (round_id (BLKB + 0x800000) ltac:(rewrite Z.add_mod, b1 by lia; reflexivity)) as [_ R2].
      left. rewrite R1, R2. lia.
    - (* [comment removed for export] *)
      destruct (is_rng_sound _ _ _ _ Hown ltac:(lia)) as [E1 E2]. rewrite E1, E2, ris_val2.
      assert (RA4 : RIS mod 4096 = 0).
      { pose proof (Z.div_mod SPB 65536 ltac:(lia)) as D. rewrite K3 in D. replace RIS with ((16 * (SPB / 65536) + 33554432) * 4096) by lia. apply Z.mod_mul. lia. }
      destruct (round_id RIS RA4) as [R1 _]. destruct (round_id (RIS + 4096) ltac:(rewrite Z.add_mod, RA4 by lia; reflexivity)) as [_ R2].
      right. rewrite R1, R2. apply win_nolazy; [exact RA4 | rewrite Z.add_mod, RA4 by lia; reflexivity |].
      intros q Hq. destruct (lazy_piece q Hq) as (_ & Hr & _). exact Hr.
    - (* [comment removed for export] *)
      apply andb_prop in Hown as [Hown HB]. apply andb_prop in Hown as [HK HP].
      destruct (apx_sound _ _ _ HK ltac:(lia)) as (AK & NPOS & NW). destruct (apx_sound _ _ _ HP ltac:(lia)) as (AP & _ & _).
      change (uE E (bKS cs)) with KB in AK. change (uE E (bP cs)) with PARR in AP.
      set (b := uE E (fst p)) in *. set (n := uE E (snd p)) in *.
      destruct (round_al b) as (L1 & _ & L3). destruct (round_al (b + n)) as (_ & H2 & H3).
      (* [comment removed for export] *)
      pose proof CHK0 as C0. unfold as0_chk in C0. repeat (apply andb_prop in C0 as [C0 ?]).
      match goal with Hf : forallb (vis_off_band (kn cs)) (a_vis cs ++ a_ghost cs) = true |- _ =>
        pose proof (proj1 (forallb_forall _ _) Hf p Hp) as Hband end.
      assert (ABAND : b + n <= 0x7fff7000 \/ 0x10007fff8000 <= b).
      { pose proof (hl_off_band ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model p) as OB.
        destruct (Z_lt_le_dec b 0x7fff7000) as [Hlt|Hge].
        - left. destruct (Z_lt_le_dec 0x7fff7000 (b + n)) as [Hin|]; [exfalso | lia].
          apply (OB 0x7fff7000 HC Hband); [fold b n; lia | unfold SHB_LO, SHB_LEN; lia].
        - right. destruct (Z_lt_le_dec b 0x10007fff8000) as [Hin|]; [exfalso | lia].
          apply (OB b HC Hband); [fold b n; lia | unfold SHB_LO, SHB_LEN; lia]. }
      (* [comment removed for export] *)
      assert (ABLK : (b + n <= BLKB \/ BLKB + 0x800000 <= b) \/ (BLKB <= b /\ b + n <= BLKB + 0x800000 /\ b mod 4096 = 0 /\ n = 4096)).
      { apply orb_prop in HB as [HB|HB].
        - destruct (apx_sound _ _ _ HB ltac:(lia)) as (AB & _ & _). change (uE E (bBLK cs)) with BLKB in AB. left. fold b n in AB. lia.
        - apply andb_prop in HB as [HB1 HB2]. apply expr_eqb_eq in HB1. apply Z.leb_le in HB2.
          assert (N4 : n = 4096) by (unfold n; rewrite HB1; apply uE_lit; lia).
          destruct (ealign_sound ASEGS0 E _ (kn cs) (fst p) (co_know _ _ _ _ _ _ _ _ _ _ _ HC)) as ((EA1 & EA2) & EA3).
          assert (B4 : b mod 4096 = 0).
          { unfold b, uE. apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (2 ^ ealign (kn cs) (fst p))); [|exact EA3].
            exists (2 ^ (ealign (kn cs) (fst p) - 12)). change 4096 with (2 ^ 12). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
          pose proof (Z.div_mod b 4096 ltac:(lia)) as D1. pose proof (Z.div_mod BLKB 4096 ltac:(lia)) as D2. rewrite B4 in D1. rewrite b1 in D2.
          destruct (Z_lt_le_dec b BLKB); [left; left; lia|]. destruct (Z_lt_le_dec b (BLKB + 0x800000)); [right; lia | left; right; lia]. }
      destruct ABLK as [ABLK|(I1 & I2 & I3 & I4)].
      + right. apply win_nolazy; [exact L1 | exact H2 |].
        intros q Hq. destruct (lazy_piece q Hq) as (Hz & _ & Hne). cbv zeta in Hz, Hne.
        destruct Hz as [Z|[Z|[Z|Z]]].
        * destruct (round_apart b n BLKB (BLKB + 0x800000) b1 ltac:(rewrite Z.add_mod, b1 by lia; reflexivity) ltac:(lia)) as [X|X]; [left | right]; lia.
        * destruct (round_apart b n PARR (PARR + 0x800000) p1 ltac:(rewrite Z.add_mod, p1 by lia; reflexivity) ltac:(lia)) as [X|X]; [left | right]; lia.
        * destruct (round_apart b n KB (KB + 0x2000011000) g1 ltac:(rewrite Z.add_mod, g1 by lia; reflexivity) ltac:(lia)) as [X|X]; [left | right]; lia.
        * destruct (round_apart b n 0x7fff7000 0x10007fff8000 ltac:(reflexivity) ltac:(reflexivity) ltac:(lia)) as [X|X]; [left | right]; lia.
      + left. destruct (round_id b I3) as [R1 _]. destruct (round_id (b + n) ltac:(rewrite I4, Z.add_mod, I3 by lia; reflexivity)) as [_ R2].
        rewrite R1, R2. lia.
  Qed.

  #[using="Type"] Lemma vis_in_In : forall b n, vis_in cs b n = true -> In (b, n) (a_vis cs ++ a_ghost cs).
  Proof.
    intros b n Hv. unfold vis_in in Hv. apply existsb_exists in Hv as (p & Hp & Hb). apply andb_prop in Hb as [Eb En].
    apply expr_eqb_eq in Eb. apply expr_eqb_eq in En. destruct p as [pb pn]. cbn [fst snd] in Eb, En. subst pb pn. apply in_or_app. left. exact Hp.
  Qed.

  (* [comment removed for export] *)
  #[using="cs E BUDGET LENMAX GAP"] Lemma win_allowed : forall (A : list (Z * Z)) lo hi (x : word), In (lo, hi) A -> lo mod 4096 = 0 -> hi mod 4096 = 0 ->
    lo <= bv_unsigned x < hi -> page_allowedb A (page_base x) = true.
  Proof.
    intros A lo hi x Hin Hlo Hhi Hx. unfold page_allowedb. apply existsb_exists. exists (lo, hi). split; [exact Hin|]. cbn [fst snd]. unfold page_size.
    destruct (pb_facts x) as ((P1 & P2) & P3).
    pose proof (Z.div_mod lo 4096 ltac:(lia)) as D1. pose proof (Z.div_mod hi 4096 ltac:(lia)) as D2.
    pose proof (Z.div_mod (bv_unsigned (page_base x)) 4096 ltac:(lia)) as D3. rewrite Hlo in D1. rewrite Hhi in D2. rewrite P3 in D3.
    apply andb_true_intro. split; apply Z.leb_le; lia.
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL HC HGEO_SPB HGEO_STK HSP16 BUDGET LENMAX GAP CHKZ"] Theorem as0_art_lazy_ok : forall (FSG : Type) (gfs0 : FSG), art_lazy_ok FSG rn (art_gs0 FSG gfs0 K0D) as0_A0x (m_vm_lazy model).
  Proof.
    intros FSG gfs0. unfold art_lazy_ok. cbn [as0_rn as0_ar rn_ar rn_blk rn_qs]. change (2 ^ 23) with 0x800000.
    pose proof sp0_win as W. destruct HGEO_SPB as ((K1 & K2) & K3).
    pose proof (rgl I_KSPACE 0x2000011000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (g1 & g2 & g3 & g4).
    pose proof (rgl I_BLK 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (b1 & b2 & b3 & b4).
    split; [exact (as0_lazy_c1 FSG gfs0 K0D)|]. split; [|split].
    - (* [comment removed for export] *)
      intros w Hw. unfold as0_A0x, as0_A0, A0_of in Hw. apply in_app_or in Hw as [Hw|Hw].
      + unfold allowA in Hw. apply in_flat_map in Hw as (p & Hp & Hwp). unfold allow1 in Hwp. destruct Hwp as [<-|[<-|[]]]; cbn [fst snd].
        * destruct (own_window p Hp) as [X|X]; [right; left; exact X | right; right; exact X].
        * left. destruct lazy_parts as (_ & _ & _ & _ & _ & Hvis & _).
          pose proof (proj1 (forallb_forall _ _) Hvis p Hp) as Hb. apply andb_prop in Hb as [Hhi _]. apply vis_hi_sound in Hhi.
          unfold sh_lo, sh_hi. cbn [shadow_off ASAN0]. pose proof (u64_range (edenot E (fst p))) as U1. pose proof (u64_range (edenot E (snd p))) as U2. unfold uE in *.
          unfold pagedown, pageup.
          Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
          split; lia.
          Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      + unfold as0_EXTRA in Hw. destruct Hw as [<-|[]]. cbn [fst snd]. left. unfold KSH.
        pose proof (Z.div_mod SPB 65536 ltac:(lia)) as D. rewrite K3 in D. lia.
    - (* [comment removed for export] *)
      intros x Hx. apply (win_allowed as0_A0x KSH (KSH + 2 ^ 34)).
      + unfold as0_A0x, as0_A0, A0_of. apply in_or_app. right. left. reflexivity.
      + unfold KSH. replace (2147450880 + 8192 * (SPB / 65536)) with ((524280 + 2 * (SPB / 65536)) * 4096) by ring. apply Z.mod_mul. lia.
      + unfold KSH. replace (2147450880 + 8192 * (SPB / 65536) + 2 ^ 34) with ((524280 + 2 * (SPB / 65536) + 4194304) * 4096) by ring. apply Z.mod_mul. lia.
      + unfold KSH. lia.
    - (* [comment removed for export] *)
      intros x Hx. destruct lazy_parts as (_ & _ & _ & _ & _ & _ & _ & Hvin).
      apply (win_allowed as0_A0x BLKB (BLKB + 0x800000)); [| exact b1 | rewrite Z.add_mod, b1 by lia; reflexivity | lia].
      unfold as0_A0x, as0_A0, A0_of. apply in_or_app. left. unfold allowA. apply in_flat_map. exists (bBLK cs, ELit 0x800000).
      split; [exact (vis_in_In _ _ Hvin)|]. unfold allow1. cbn [fst snd]. left.
      rewrite (uE_lit E 0x800000) by lia. change (uE E (bBLK cs)) with BLKB.
      destruct (round_id BLKB b1) as [R1 _]. destruct (round_id (BLKB + 0x800000) ltac:(rewrite Z.add_mod, b1 by lia; reflexivity)) as [_ R2].
      rewrite R1, R2. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL HC BUDGET LENMAX GAP"] Lemma role_kn : forall i L a n, (i < 17)%nat -> lit_len cs i L = true -> 0 <= L < 2 ^ 64 ->
    rbase E cs i <= a -> a + n <= rbase E cs i + L ->
    exists q, In q (KN0 MAPS0 RESV0) /\ fst q <= a /\ a + n <= snd q.
  Proof.
    intros i L a n Hi HL HLr Ha Hn. exists (ivZ (amap_den E (role cs i))). split.
    - unfold KN0. apply in_map. apply in_or_app. right.
      rewrite (hb_maps ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model HC nofog). apply in_map. apply role_in. rewrite len17. exact Hi.
    - unfold lit_len in HL. apply expr_eqb_eq in HL. pose proof (role_lit E cs i L HL HLr) as El.
      unfold ivZ, amap_den. cbn [fst snd]. unfold rbase, rlen, uE in *. lia.
  Qed.
  Lemma seg_kn : forall b sz, In (Z_to_bv 64 b, Z_to_bv 64 sz) (segments_reserved ASEGS0) -> 0 <= b < 2 ^ 64 -> 0 <= sz < 2 ^ 64 ->
    exists q, In q (KN0 MAPS0 RESV0) /\ fst q <= b /\ b + sz <= snd q.
  Proof.
    intros b sz Hin Hb Hs. exists (ivZ (Z_to_bv 64 b, Z_to_bv 64 sz)). split.
    - unfold KN0. apply in_map. apply in_or_app. left.
      destruct (co_res _ _ _ _ _ _ _ _ _ _ _ HC) as (rx & Hres & _). rewrite Hres. apply in_or_app. left. exact Hin.
    - unfold ivZ. cbn [fst snd]. rewrite !u64_lit by lia. lia.
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL HC BUDGET LENMAX GAP"] Theorem as0_art_kn_ok : art_kn_ok MAPS0 RESV0 rn.
  Proof.
    unfold art_kn_ok, art_objs. cbn [as0_rn as0_ar rn_ar rn_t rn_ctx rn_kbase rn_parr rn_l2 rn_blk rn_dtls ar_fs]. unfold FS_BYTES.
    change (2 ^ 23) with 0x800000. change (2 ^ 20) with 0x100000.
    intros o Ho.
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply (role_kn I_THREAD 4096); [IDX | chk | lia | lia | lia]|].
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply (role_kn I_CTX 0x10000); [IDX | chk | lia | lia | lia]|].
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply (role_kn I_KSPACE 0x2000011000); [IDX | chk | lia | lia | lia]|].
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply (role_kn I_PARR 0x800000); [IDX | chk | lia | lia | lia]|].
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply (role_kn I_L2 0x100000); [IDX | chk | lia | lia | lia]|].
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply (role_kn I_BLK 0x800000); [IDX | chk | lia | lia | lia]|].
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply (role_kn I_FAKE 0xb09000); [IDX | chk | lia | lia | lia]|].
    pose proof seg_kn as SK. rewrite asan0_res_eq in SK.
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply SK; [cbn [In]; repeat (first [left; reflexivity | right]) | lia | lia]|].
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply SK; [cbn [In]; repeat (first [left; reflexivity | right]) | lia | lia]|].
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply SK; [cbn [In]; repeat (first [left; reflexivity | right]) | lia | lia]|].
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply SK; [cbn [In]; repeat (first [left; reflexivity | right]) | lia | lia]|].
    destruct Ho as [<-|[]]. cbn [fst snd]. apply (role_kn I_DTLS 4096); [IDX | chk | lia | lia | lia].      (* [comment removed for export] *)
  Qed.

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva CHK0 R FULL HC BUDGET LENMAX BUD BUD_le GAP"] Lemma as0_art_eager : art_eager_ok [] as0_A0x (m_vm_lazy model).
Proof.
  split; [eapply BINV_awf; exact as0_art_binv | intros b x []]. Qed.

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHK0 CHKL CHKS R HC HGEO_SPB HGEO_STK HSP16 HSPA LENMAX BUD BUD_le BUD_ge GAP CHKZ"] Theorem as0_art_handoff : art_fsinv_handoff ->
    art_handoff_target art_fsg MAPS0 RESV0 NOACC0 as0_BASEx BUDGET art_fsinv rn art_fsg0 K0D KCNT (2 ^ 36) as0_A0x FULL (vml_of model).
  Proof.
    intros FSH. unfold art_handoff_target, vml_of. cbn [fst snd].
    exact (conj (as0_art_alloc_rep art_fsg art_fsg0) (conj (as0_art_fsinv FSH) (conj as0_art_binv (conj (as0_art_credit art_fsg art_fsg0) (conj as0_art_client (conj as0_art_kn_ok (conj (as0_art_lazy_ok art_fsg art_fsg0) as0_art_eager))))))).
  Qed.
End Derive.
