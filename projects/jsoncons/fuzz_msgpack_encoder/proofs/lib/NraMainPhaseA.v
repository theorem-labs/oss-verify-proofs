(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: changed HSA_pc, Hsp, SINV and 11 more; added HRZ, Hlau, Hvl and 7 more; removed role_ks_0, role_ks_1; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/As0MainPhaseA.v, 46 lines within its lines 25-287. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Na0HandoffInstK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3SoundK AsanPlanSoundK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0077. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0107. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AxSymExec3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3SoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanCoreK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanInitK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0DefsK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0PlanImagesK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0077.Na0StartupK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffBridgeK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffBInvK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffRolesK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0HandoffK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0107.Na0HSK_0 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0107.Na0HSK_1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0107.Na0MainTableK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Na0HandoffInstK.Na0HandoffInstK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0DrvEntryK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0077.Na0StartupFinalK.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require NraArtHandoffK NraArtHandoffInstK NraStkShK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0077. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceANull OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.LibIfaceAB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtRuns OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.ArtBridge OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.NarInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.NarFsInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.NraArtHandoffK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.NraArtHandoffInstK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.NraStkShK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.As0DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0077.Na0DrvEntryInst OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0Drv_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvRead OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvStdio OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057.Na0ExitCells.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.ShapeLaws OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.Spec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.BigintSpec.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080.HeapIfaceAMxI OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080.StrictOfB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080.StrictOfBI.      (* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.PnAImgGap.      (* [comment removed for export] *)
Require Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Na0CertK_202.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023.
Ltac2 kr_t_NraMainPhaseA () := "C47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib7Mh_00634Spec1WC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00634Spec9exit_codeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg>t_emit_has_nilC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib7Mh_00634Spec5t_dieC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib5Arith8PeanoNat3Nat3lebC59OSSVerify5KrLib7Mh_00634Spec?msg_cannot_openC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00634Spec=list_byte_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00634Spec>msg_read_errorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg6t_alt2C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupC59OSSVerify5KrLib7Mh_0063:BigintSpec6t_bodyC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib7Mh_00639ShapeLaws@t_alt2_has_nil_lC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib7Mh_0063:BigintSpec4specC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_00634Spec9msg_usageC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib7Mh_00634Spec8dot_pathC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr05C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4amap01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C59OSSVerify5KrLib7Mh_0132=HandoffRolesK4roleC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4amap00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5mkind01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5mkind04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01078Na0HSK_04HS_0C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>NraArtHandoffK8I_KSPACEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117;Na0HandoffK8M_KSPACEC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>NraArtHandoffK6I_PARRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117;Na0HandoffK8M_PTRARRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01078Na0HSK_14HS_1C1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC59OSSVerify5KrLib?Na0HandoffInstK?Na0HandoffInstK3HSAC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7am_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6am_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK2uEC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr07C49OSSVerify5KrLib>NraArtHandoffK6uE_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132<HandoffBInvK4resZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132=HandoffRolesK5rbaseC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC49OSSVerify5KrLib>NraArtHandoffK6as0_rnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv8rn_kbaseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv7rn_parrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117;Na0HandoffK7as0_RESC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv7art_RESC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib4Init9Datatypes4prod01K46Stdlib9micromega5Tauto8GFormula05I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K3env00C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA9role_ks_0C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA9role_ks_1C1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic4True00K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib7Mh_01456NarInv4KMAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv6LENMAXC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib7Mh_00238AsanCeil>bottomup_floorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00238AsanCeil=alloc_ceilingC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?Na0HandoffInstK?Na0HandoffInstK;HSA_numbersC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7a_totszC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7a_eagerC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8a_abytesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC47Corelib4Init3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6a_mapsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib7Mh_01178Na0DefsK6ASEGS0C1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib7Mh_0117>Na0PlanImagesK<asan0_res_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK2pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0107=Na0MainTableK6HS_as0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init5Logic9False_indC59OSSVerify5KrLib?Na0HandoffInstK?Na0HandoffInstK8HSA_someC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib7Mh_0077;Na0StartupK5HOLESC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0077?Na0DrvEntryInst;drv_chk_HSAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117<Na0DrvEntryK9ent_modelC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C56Stdlib5Arith8PeanoNat3Nat6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvC4ELinuxProcessSemantics?LinuxProcessSem3Run@entry_stack_fitsC49OSSVerify5KrLib>NraArtHandoffK6as0_arC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC49OSSVerify5KrLibBNraArtHandoffInstKAas0_art_handoff_hC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC49OSSVerify5KrLib>NraArtHandoffK9as0_BASExC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>NraArtHandoffK7as0_A0xC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?Na0HandoffInstK?Na0HandoffInstKBas0_handoff_staticC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA;as0_RES_artC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA8mp_gap_hC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117<Na0DrvEntryK7sp0_valC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib7Mh_01456NarInv7art_gs0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv=art_alloc_repC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv5rn_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv<art_eager_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv=art_client_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv:art_run_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv>art_rt_staticsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv=art_rt_threadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv>art_rt_primaryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv=art_rt_chunksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv:art_rt_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv;art_rt_quarC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv<art_rt_depotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv9art_rt_iaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv=art_rt_blocksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv<art_rt_ghostC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA3HIRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_hiC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ>asan_iface_okR00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00809StrictOfB=rt_flag_in_fsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00809StrictOfB9strict_okC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA3HIAC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0089<HeapIfaceAMx>asan_iface_okB00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00809StrictOfBCstrict_free_null_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089>HeapIfaceANull?afree_null_specC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0089:IcptIfaceA8aicpt_ok00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ;asan_ext_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00809StrictOfB=strict_of_nilC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ9strict_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0080:StrictOfBI;strict_icptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01799PnAImgGap6PMAGAP:rt_img_gapC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01c49OSSVerify5KrLib=NraMainPhaseA;lib_ext_okGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv5rn_arC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv8art_rn_kC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0092:LibIfaceAB5lla_LC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0092:LibIfaceAB=lib_iface_okA00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_01199Na0DrvLib;drv_layoutA00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>NraArtHandoffK<as0_EXTRA_wfC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>NraArtHandoffK9as0_EXTRAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct4A_wfC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>NraArtHandoffK3KSHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct7A_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0077?Na0DrvEntryInst>as0_main_entryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec<cat_argv_ptrC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthI47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7Mh_0077?Na0DrvEntryInst=as0_main_auxvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117<Na0DrvEntryK9auxv_listC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct>H_off_segmentsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC59OSSVerify5KrLib7Mh_00368AsanAcct:lazy_coverC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00368AsanAcct4MInv00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI47Corelib4Init5Logic2or00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7app_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ;shadow_blkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<blocks_apartC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib7Mh_0089:HeapIfaceA=fframes_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5ar_fsC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA?ar_stack_bottomC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_stack_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA>shadow_allowedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC49OSSVerify5KrLib>NraArtHandoffK4topEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0077?Na0DrvEntryInstFas0_main_stack_definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib6STKTOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<in_shadow_ofC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC49OSSVerify5KrLib9NraStkShK>as0_stksh_mainC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppC49OSSVerify5KrLib9NraStkShKAas0_stksh_main_hiC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_01199Na0DrvLib4dinv01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_01199Na0DrvLib4dinv00C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_envpC4ELinuxProcessSemantics?LinuxProcessSem3Run?total_arg_bytesI47Corelib5Lists7ListDef6Forall00C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei>path_has_slashC4ELinuxProcessSemantics?LinuxProcessSem2Fs8path_eqbC46Stdlib5Lists4List2tlC4ELinuxProcessSemantics?LinuxProcessSem2Fs8valid_fsc49OSSVerify5KrLib=NraMainPhaseA<inst_ok_stmtC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA>free_null_stmtC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA<icpt_ok_stmtC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA;ext_ok_stmtC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA;dla_ok_stmtC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA?drv_consts_stmtC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA=drv_main_stmtC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C59OSSVerify5KrLib7Mh_0119;Na0DrvEntry:auxv_listAC1?~~~~~~~~~~~~~~~I46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr07K46Stdlib;setoid_ring<Ring_polynom5PExpr05K46Stdlib;setoid_ring<Ring_polynom5PExpr06I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7mod_mulC46Stdlib9micromega;ZifyClasses9and_morphC59OSSVerify5KrLib7Mh_0077?Na0DrvEntryInstDas0_main_str_definedC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA6HSA_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK:holes_stmtC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib7Mh_01329AsanInitK5SINV0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01329AsanInitK5argH0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib>AsanPlanSoundK4APSK5cs_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK6cfg_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC59OSSVerify5KrLib7Mh_01456NarInvBart_handoff_targetC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_01099ArtBridge=bridge_static00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01458NarFsInv9art_fsinvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01099ArtBridge4BINVC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv9art_kn_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv;art_lazy_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv=art_credit_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv9art_ifaceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0DrvEntry9env_mainAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117;Na0HandoffK6as0_A0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecCtotal_arg_bytes_natC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0116:As0DrvKitA5lzinvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC49OSSVerify5KrLib>NraArtHandoffK4botEC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substI69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3acs00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01178Na0DefsK4APH0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01178Na0DefsK5ASAN0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01329AsanInitK5LIMITC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7fds_stdC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I59OSSVerify5KrLib7Mh_01458NarFsInv7art_fsg00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01458NarFsInv8art_fsg0C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>NraArtHandoffK3K0DC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv4KCNTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5e_sp0C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0DrvEntry8sr_mainAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0DrvEntry8kn_mainAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8FS_BYTESC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I47Corelib4Init5Logic5False00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00I59OSSVerify5KrLib7Mh_01456NarInv7art_run00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0089:HeapIfaceA8asan_run00C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA6mp_budC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA6mp_gapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00357ArtRuns3aev00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0089:HeapIfaceA:asan_iface00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_LOC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0089:HeapIfaceA;asan_layout00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX23env00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei;dotdot_pathC46Stdlib9micromega8ZifyInst7Inj_Z_ZC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiI47Corelib7Numbers7BinNums1N00C49OSSVerify5KrLib>AsanPlanSoundK>asanreflect_fxC1?~~~~~~~~~~~~~~~I46Stdlib;setoid_ring<Ring_polynom3Mon00C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA<spec_has_nilC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0077@Na0StartupFinalKBas0_startup_closedC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA>as0_main_phaseC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLiaT.plia1.
Import ListNotations.
Open Scope Z_scope.

#[local] Existing Instance PropExec.fx0.

(* [comment removed for export] *)
Lemma spec_has_nil : forall argv fs, spec argv fs [].
Proof.
  intros argv fs. unfold spec.
  assert (D : forall m f, t_die m f []) by (intros; unfold t_die; apply OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg.t_emit_has_nil).
  destruct argv as [|a0 [|p [|x l]]]; try apply D.
  destruct (4096 <=? length p)%nat; [apply D|]. destruct (list_byte_eqb p []); [apply D|].
  destruct (list_byte_eqb p dot_path); [apply OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.ShapeLaws.t_alt2_has_nil_l; apply D|].
  destruct (fs_lookup fs p); [apply OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.ShapeLaws.t_alt2_has_nil_l; apply D | apply D].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition HIR (BUDGET : Z) (MAPS0 RESV0 NOACC0 : list (word * word)) (BASE : Z) (rn : art_run) : asan_iface :=
  art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn.
Definition HIA (BUDGET : Z) (MAPS0 RESV0 NOACC0 : list (word * word)) (BASE : Z) (rn : art_run) : asan_iface :=
  HAJ.strict_of (HIR BUDGET MAPS0 RESV0 NOACC0 BASE rn).

(* [comment removed for export] *)
Definition inst_ok_stmt (scfg : SpuriousCfg) (L : asan_layout) (C : asan_statics_cells) (BUDGET : Z) : Prop :=
  forall MAPS0 RESV0 NOACC0 BASE rn,
    bridge_static ASEGS0 MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET NarInv.LENMAX NarInv.KMAX ->        (* [comment removed for export] *)
    art_run_ok rn -> rn_tp rn = 0x693b00 -> rn_key rn = 0 -> rn_tsd rn = 0x6b4fb8 -> rn_loff rn = 0x10 ->
    hl_img_hi L <= BIGSHADOW_LO /\ HAJ.asan_iface_okR L (rn_ar rn) C scfg (HIR BUDGET MAPS0 RESV0 NOACC0 BASE rn)
    /\ rt_flag_in_fs L (rn_ar rn) (HIR BUDGET MAPS0 RESV0 NOACC0 BASE rn).      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition free_null_stmt (scfg : SpuriousCfg) (L : asan_layout) (BUDGET : Z) : Prop :=
  forall MAPS0 RESV0 NOACC0 BASE rn,
    bridge_static ASEGS0 MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET NarInv.LENMAX NarInv.KMAX ->
    art_run_ok rn -> rn_tp rn = 0x693b00 -> rn_key rn = 0 -> rn_tsd rn = 0x6b4fb8 -> rn_loff rn = 0x10 ->
    afree_null_spec L (rn_ar rn) scfg (HIR BUDGET MAPS0 RESV0 NOACC0 BASE rn).
(* [comment removed for export] *)
Definition h4e_stmt (BUDGET : Z) : Prop :=
  forall MAPS0 RESV0 NOACC0 BASE rn gfs0 k0 K0 B0 A0 M V,
    art_handoff_target art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn gfs0 k0 K0 B0 A0 M V ->
    ri_inv (HIR BUDGET MAPS0 RESV0 NOACC0 BASE rn) [] [] [] (K0, B0) A0 M V.
(* [comment removed for export] *)
Definition icpt_ok_stmt (scfg : SpuriousCfg) (L : asan_layout) (IL : icpt_layout) (BUDGET : Z) : Prop :=
  forall MAPS0 RESV0 NOACC0 BASE rn,
    bridge_static ASEGS0 MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET NarInv.LENMAX NarInv.KMAX ->
    art_run_ok rn -> rn_tp rn = 0x693b00 -> rn_key rn = 0 -> rn_tsd rn = 0x6b4fb8 -> rn_loff rn = 0x10 ->
    aicpt_ok L (rn_ar rn) IL scfg (HIR BUDGET MAPS0 RESV0 NOACC0 BASE rn).
(* [comment removed for export] *)
Definition ext_ok_stmt (scfg : SpuriousCfg) (L : asan_layout) (EX : HAJ.ext_consts) (BUDGET : Z) : Prop :=
  forall MAPS0 RESV0 NOACC0 BASE rn,
    bridge_static ASEGS0 MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET NarInv.LENMAX NarInv.KMAX ->
    art_run_ok rn -> rn_tp rn = 0x693b00 -> rn_key rn = 0 -> rn_tsd rn = 0x6b4fb8 -> rn_loff rn = 0x10 ->
    HAJ.asan_ext_ok L (rn_ar rn) scfg (HIR BUDGET MAPS0 RESV0 NOACC0 BASE rn) EX.
(* [comment removed for export] *)
Definition gap_ok_stmt (BUDGET : Z) : Prop :=
  forall MAPS0 RESV0 NOACC0 BASE rn,
    bridge_static ASEGS0 MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET NarInv.LENMAX NarInv.KMAX ->
    art_run_ok rn -> rn_tp rn = 0x693b00 -> rn_key rn = 0 -> rn_tsd rn = 0x6b4fb8 -> rn_loff rn = 0x10 ->
    PMAGAP.rt_img_gap (HIR BUDGET MAPS0 RESV0 NOACC0 BASE rn).
(* [comment removed for export] *)
Definition lib_ext_okG (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (scfg : SpuriousCfg) (HI : asan_iface) (EX : HAJ.ext_consts) : Prop :=
  exists HIR, HI = HAJ.strict_of HIR /\ HAJ.asan_iface_okR L ar C scfg HIR /\ aicpt_ok L ar IL scfg HIR /\ HAJ.asan_ext_ok L ar scfg HIR EX /\ PMAGAP.rt_img_gap HIR.
(* [comment removed for export] *)
Definition lib_ok_stmt (scfg : SpuriousCfg) (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (EX : HAJ.ext_consts) (Lay : lib_layoutA) (LSt : asan_run -> lib_statics) : Prop :=
  forall ar HI, asan_iface_okB L ar C scfg HI -> aicpt_ok L ar IL scfg HI ->
    lib_ext_okG L ar C IL scfg HI EX ->      (* [comment removed for export] *)
    lla_L Lay = L /\ lib_iface_okA Lay ar scfg HI (LSt ar).
(* [comment removed for export] *)
Definition dla_ok_stmt (scfg : SpuriousCfg) (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) : Prop :=
  forall ar HI (sp0 : word), asan_iface_okB L ar C scfg HI -> ar_sptop ar = bv_unsigned sp0 -> drv_layoutA L ar IL sp0.
(* [comment removed for export] *)
Definition drv_consts_stmt (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) : Prop :=
  as0_icpt_layout IL /\ incl RD_CELLS (asc_cells C) /\ 0 <= hl_k_per_malloc L /\ 0 <= hl_b_lin L /\ 0 <= hl_b_overhead L
  /\ incl PR_CELLS (asc_cells C)       (* [comment removed for export] *)
  /\ incl EX_CELLS (asc_cells C)       (* [comment removed for export] *)
  /\ incl DG_CELLS (asc_cells C) /\ incl DGS_CELLS (asc_cells C)       (* [comment removed for export] *)
  /\ incl [(1443672, 1, 1); (1412088, 8, 1311060); (1440376, 8, 2147450880)] (asc_cells C).      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition drv_main_stmt (scfg : SpuriousCfg) (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (Lay : lib_layoutA) (LSt : asan_run -> lib_statics) : Prop :=
  sc_alloc scfg = false -> sc_fs scfg = true -> drv_consts_stmt L C IL ->
  forall (sp : word) (a0s path : list byte) (envp : list (list byte)) (fs : Fs.Fs),
    valid_sp sp -> valid_argv [a0s; path] -> valid_envp envp -> valid_fs fs ->
  forall (ar : asan_run) (HI : asan_iface) (p0 p1 can tid auxvp : word) (A0 : list (Z * Z)) (cr0 : credit)
         (R : bvmap 5 word) (M0 : word -> option byte) (model : Model),
    asan_iface_okB L ar C scfg HI -> afree_null_spec L ar scfg HI -> aicpt_ok L ar IL scfg HI -> lib_iface_okA Lay ar scfg HI (LSt ar) ->
    (forall g M, ls_ok (LSt ar) g M -> exists ax : axv, atexit_cellsA M ax) ->      (* [comment removed for export] *)
    drv_layoutA L ar IL sp ->
    SX2S.regs_ok (env_mainA sp p0 p1 can tid auxvp R) sr_mainA R ->
    SX2S.know_ok ASEGS (env_mainA sp p0 p1 can tid auxvp R) (mrestrict (ahid A0 model) M0) kn_mainA ->
    auxv_atA sp auxvp M0 ->                                                     (* [comment removed for export] *)
    dinv ar HI sp M0 [] [] cr0 A0 M0 model ->
    defined M0 (bv_unsigned sp) (ar_stack_top ar - bv_unsigned sp) ->
    m_fds model = APSK.fds_std -> m_fs model = fs ->
    rdn ASEGS (mrestrict (ahid A0 model) M0) p1 (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    bv_unsigned sp <= bv_unsigned p1 /\ bv_unsigned p1 + Z.of_nat (length path) + 1 + 9 <= 2 ^ 47 ->
    cr0 = (8192, 2 ^ 36) ->
    (* [comment removed for export] *)
    defined M0 (bv_unsigned p1) (Z.of_nat (length path) + 1 + 8) ->
    shadow_allowed A0 (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xaea2c) M0 (seg_rom ASEGS)) model) (spec [a0s; path] fs).
(* [comment removed for export] *)
Definition usage_stmt (scfg : SpuriousCfg) : Prop :=
  forall sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc (r : Z),
  valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp -> valid_fs fs ->
  (* [comment removed for export] *)
  entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw)
    (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf) ->
  valid_launch (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf) ->
  r = APK.rseq_z (kb_rseq (in_kernel (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf))) ->
  forall h, (h < 2)%nat -> forall E R FULL model,
    APSK.cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT (SINV0 APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc) (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf) fs E (HSA r h) R FULL model ->
    length argv <> 2%nat ->
    srealizes ASEGS0 scfg (APSK.cfg_of ASEGS0 R (APCK.pc (HSA r h)) FULL model) (spec argv fs).

(* [comment removed for export] *)
Lemma role_ks_HSA : forall r h, (h < 2)%nat -> role (HSA r h) I_KSPACE = M_KSPACE /\ role (HSA r h) I_PARR = M_PTRARR.
Proof. intros r [|[|h]] H; [| |lia]; unfold HSA; destruct (Z.eqb r 1); vm_compute; split; reflexivity. Qed.
Lemma as0_RES_art : forall r h, (h < 2)%nat -> forall E, as0_RES E = art_RES (as0_rn E (HSA r h)).
Proof.
  intros r h Hh E. unfold as0_RES, HandoffBInvK.RES_of, RESm0, art_RES. cbn [map as0_rn rn_kbase rn_parr]. unfold HandoffBInvK.resZ, rbase.
  assert (R : role (HSA r h) I_KSPACE = M_KSPACE /\ role (HSA r h) I_PARR = M_PTRARR) by exact (role_ks_HSA r h Hh).
  destruct R as (-> & ->). cbn [APK.am_base APK.am_len M_KSPACE M_PTRARR]. rewrite !NraArtHandoffK.uE_lit by lia. reflexivity.
Qed.

Section MainPhase.
  Variable scfg : SpuriousCfg.
  Hypothesis Halloc : sc_alloc scfg = false.
  Hypothesis Hfs : sc_fs scfg = true.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable L : asan_layout.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable Lay : lib_layoutA.
  Variable LSt : asan_run -> lib_statics.
  Variable EXc : HAJ.ext_consts.      (* [comment removed for export] *)
  Variable BUDGET : Z.
  Hypothesis BUD_ge : 2 ^ 36 + 2 ^ 20 + NarInv.PRIMCAP <= BUDGET.      (* [comment removed for export] *)
  Hypothesis BUD_hi : BUDGET <= 2 ^ 39 - 2 ^ 35.

  Hypothesis INST_OK : inst_ok_stmt scfg L C BUDGET.
  Hypothesis FREE_NULL : free_null_stmt scfg L BUDGET.
  Hypothesis H4E : h4e_stmt BUDGET.
  Hypothesis ICPT_OK : icpt_ok_stmt scfg L IL BUDGET.
  Hypothesis EXT_OK : ext_ok_stmt scfg L EXc BUDGET.
  Hypothesis GAP_OK : gap_ok_stmt BUDGET.
  (* [comment removed for export] *)
  Variable FAMP : asan_run -> (list (list Z) -> asan_iface) -> Prop.
  Hypothesis LIB_OKF : forall ar HIk, FAMP ar HIk -> lla_L Lay = L /\ lib_iface_okA Lay ar scfg (HAJ.strict_of (HIk [])) (LSt ar).
  Hypothesis FAM_OK : forall MAPS0 RESV0 NOACC0 BASE rn,
    bridge_static ASEGS0 MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET NarInv.LENMAX NarInv.KMAX ->
    art_run_ok rn -> rn_tp rn = 0x693b00 -> rn_key rn = 0 -> rn_tsd rn = 0x6b4fb8 -> rn_loff rn = 0x10 ->
    FAMP (rn_ar rn) (fun D => art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv (art_rn_k rn D)).
  Hypothesis DLA_OK : dla_ok_stmt scfg L C IL.
  Hypothesis DRV_CONSTS : drv_consts_stmt L C IL.
  Hypothesis DRV_MAIN : drv_main_stmt scfg L C IL Lay LSt.
  Hypothesis USAGE : usage_stmt scfg.
  (* [comment removed for export] *)
  Hypothesis LSXFA : forall ar g M, ls_ok (LSt ar) g M -> exists ax : axv, atexit_cellsA M ax.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable sp brk0 mbase : word. Variable rdraw : EntryDraw. Variables argv envp : list (list byte). Variable fs : Fs.Fs.
  Variable stdin : InputStream. Variables uid gid hw : word. Variable groups : list word. Variable net : NetQueue.
  Variables nofile sigmask : word. Variable abrt : bool. Variable ur : InputStream.
  (* [comment removed for export] *)
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variable sdf : bool.   (* the SIGPIPE disposition at exec, free at LPS 727298f3 *)
  (* [comment removed for export] *)
  #[local] Notation apc := Asan.M.init_pc.
  (* [comment removed for export] *)
  Variable r : Z.
  Hypothesis Hsp : valid_sp sp. Hypothesis Hbrk : valid_brk ASEGS0 brk0. Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv. Hypothesis Hve : valid_envp envp. Hypothesis Hfit : entry_stack_fits sp argv envp.
  (* [comment removed for export] *)
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw)
    (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
  Hypothesis Hvl : valid_launch (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
  Hypothesis HRZ : r = APK.rseq_z (kb_rseq (in_kernel (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf))).
  Remark r01 : 0 <= r <= 1.
  Proof. rewrite HRZ. apply APK.rseq_z_range. Qed.
  Hypothesis Huid : valid_id uid. Hypothesis Hhw : valid_hwcap hw. Hypothesis Hvfs : valid_fs fs.
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc).
  #[local] Notation argH := (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
  #[local] Notation CSOK := (APSK.cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
  #[local] Notation usp := (bv_unsigned sp).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
#[using="BUD_ge"] Lemma mp_bud : 0 <= BUDGET /\ 0 <= NarInv.KMAX /\ 0 <= NarInv.LENMAX < 2 ^ 62.
Proof. pose proof BUD_ge as B. unfold Mh_0145.NarInv.PRIMCAP in B. unfold Mh_0145.NarInv.KMAX, Mh_0145.NarInv.LENMAX. lia. Qed.
#[using="BUD_hi"] Lemma mp_gap : AsanCeil.bottomup_floor + NarInv.LENMAX + (17729665413120 + BUDGET) + (23 + NarInv.KMAX) * (NarInv.LENMAX + 4095) <= AsanCeil.alloc_ceiling.
Proof. unfold Mh_0145.NarInv.KMAX, Mh_0145.NarInv.LENMAX, Mh_0023.AsanCeil.bottomup_floor, Mh_0023.AsanCeil.alloc_ceiling. lia. Qed.
#[using="BUD_hi"] Lemma mp_gap_h : forall h, (h < 2)%nat ->
AsanCeil.bottomup_floor + NarInv.LENMAX + (APK.a_totsz (HSA r h) + BUDGET)
+ (Z.of_nat (length (segments_reserved ASEGS0) + APK.n_resx ASAN0 + length (APK.a_maps (HSA r h))) + NarInv.KMAX) * (NarInv.LENMAX + 4095) <= AsanCeil.alloc_ceiling.
Proof.
intros h Hh. destruct (HSA_numbers r h Hh) as (N1 & N2 & N3 & N4). rewrite N4, asan0_res_eq. change (APK.n_resx ASAN0) with 2%nat. cbn [length Nat.add]. change (Z.of_nat 23) with 23.
unfold Mh_0145.NarInv.KMAX, Mh_0145.NarInv.LENMAX, Mh_0023.AsanCeil.bottomup_floor, Mh_0023.AsanCeil.alloc_ceiling. lia.
Qed.

  #[using="Type"] Lemma HSA_pc : forall h, (h < 2)%nat -> APK.pc (HSA r h) = 0xaea2c.
  Proof. intros [|[|h]] H; [| |lia]; unfold HSA; destruct (Z.eqb r 1); vm_compute; reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Halloc Hfs L C IL Lay LSt BUDGET BUD_ge BUD_hi INST_OK FREE_NULL H4E ICPT_OK EXc EXT_OK GAP_OK FAMP LIB_OKF FAM_OK DLA_OK DRV_CONSTS DRV_MAIN USAGE LSXFA Hsp Hva Hve Hfit Hvfs Hlau Hvl HRZ"] Theorem as0_main_phase : APSK.holes_stmt ASEGS0 scfg ASAN0 AsanInitK.LIMIT (HS_as0 r) SINV argH (HOLES (fun fs' => spec argv fs')) fs.
  Proof.
  intros h ch Hh E R FULL model HC.
  assert (Hh2 : (h < 2)%nat).
  { destruct (Nat.lt_ge_cases h 2) as [Hlt|Hge]; [exact Hlt|]. rewrite (HSA_none r h Hge) in Hh. discriminate Hh. }
  rewrite (HSA_some r h Hh2) in Hh. injection Hh as <-.
  assert (EFS : m_fs model = fs).
  (* [DrvEntryK]'s [drv_chk_parts] proves its [OE] with a bare [subst], which
  rewrites with that Section's [HRZ]; so [ent_model] and [sp0_val], which use
  [drv_chk_parts], take [HRZ] (after [r], resp. after [Hlau]). *)
  { exact (proj2 (ent_model sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc r HRZ (HSA r h) (drv_chk_HSA r h r01 Hh2) E R FULL model HC)). }
  unfold HOLES. rewrite EFS.
  destruct (Nat.eq_dec (length argv) 2) as [Hargc|Hargc]; [|exact (USAGE sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc r Hsp Hva Hve Hfit Hvfs Hlau Hvl HRZ h Hh2 E R FULL model HC Hargc)].
  destruct argv as [|a0s [|path [|x l]]] eqn:Hargv; try discriminate Hargc. clear Hargc.
  set (cs := HSA r h). set (rn := as0_rn E cs). set (ar := as0_ar E cs).
  set (MAPS0 := vm_maps (m_vmmaps model)). set (RESV0 := vm_reserved (m_vmmaps model)). set (NOACC0 := vm_noaccess (m_vmmaps model)).
  pose proof (as0_art_handoff_h sp brk0 rdraw [a0s; path] envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva Hve Hfit Hlau BUDGET BUD_ge BUD_hi r h Hh2 E R FULL model HC) as HT.
  pose proof (as0_handoff_static sp brk0 rdraw [a0s; path] envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc BUDGET Mh_0145.NarInv.LENMAX Mh_0145.NarInv.KMAX mp_bud mp_gap r h Hh2 E R FULL model HC) as BS.
  rewrite (as0_RES_art r h Hh2 E) in BS. fold cs rn in BS.
  (* [comment removed for export] *)
  pose proof (sp0_val sp brk0 rdraw [a0s; path] envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc r Hsp Hva Hve Hfit Hlau HRZ BUDGET Mh_0145.NarInv.LENMAX Mh_0145.NarInv.KMAX (HSA r h) (drv_chk_HSA r h r01 Hh2) (mp_gap_h h Hh2)
  E R FULL model HC) as SPV.
  pose proof HT as (REP & _ & _ & _ & CLI & _). destruct REP as (ROK & _).
  set (HR0 := HIR BUDGET MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn).
  assert (INSTR : hl_img_hi L <= BIGSHADOW_LO /\ HAJ.asan_iface_okR L ar C scfg HR0 /\ rt_flag_in_fs L ar HR0).
  { apply (INST_OK MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn); [exact BS | exact ROK | reflexivity | reflexivity | reflexivity | reflexivity]. }
  destruct INSTR as (IMGL & HIRok & FLG).
  assert (HIok : asan_iface_okB L ar C scfg (HIA BUDGET MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn)) by exact (strict_ok L ar C scfg HR0 IMGL FLG HIRok).
  assert (FNok : afree_null_spec L ar scfg (HIA BUDGET MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn)).
  { apply (strict_free_null_of L ar C scfg HR0 HIRok). apply (FREE_NULL MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn); [exact BS | exact ROK | reflexivity | reflexivity | reflexivity | reflexivity]. }
  assert (ICR : aicpt_ok L ar IL scfg HR0).
  { apply (ICPT_OK MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn); [exact BS | exact ROK | reflexivity | reflexivity | reflexivity | reflexivity]. }
  assert (EXR : HAJ.asan_ext_ok L ar scfg HR0 EXc).
  { apply (EXT_OK MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn); [exact BS | exact ROK | reflexivity | reflexivity | reflexivity | reflexivity]. }
  pose proof (strict_of_nil HR0 _ _ _ _ (H4E _ _ _ _ _ _ _ _ _ _ _ _ HT)) as RI.
  set (HI := HIA BUDGET MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn) in *.
  change (HAJ.strict_of HR0) with HI in RI.
  assert (SPT : ar_sptop ar = usp) by exact SPV.
  assert (ICok : aicpt_ok L ar IL scfg HI) by exact (strict_icpt L ar C IL scfg HR0 IMGL HIRok ICR).
  assert (GAPR : PMAGAP.rt_img_gap HR0).
  { apply (GAP_OK MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn); [exact BS | exact ROK | reflexivity | reflexivity | reflexivity | reflexivity]. }
  assert (LXok : lib_ext_okG L ar C IL scfg HI EXc).
  { exists HR0. split; [reflexivity|]. split; [exact HIRok|]. split; [exact ICR|]. split; [exact EXR| exact GAPR]. }
  assert (FAMok : FAMP ar (fun D => art_iface art_fsg MAPS0 RESV0 NOACC0 (as0_BASEx cs E) BUDGET art_fsinv (art_rn_k rn D))).
  { apply (FAM_OK MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn); [exact BS | exact ROK | reflexivity | reflexivity | reflexivity | reflexivity]. }
  destruct (LIB_OKF ar _ FAMok) as (LayL & LIok). change (lib_iface_okA Lay ar scfg HI (LSt ar)) in LIok. pose proof (DLA_OK ar HI sp HIok SPT) as DL.
  pose proof (as0_EXTRA_wf cs E) as XWF.
  assert (XBL : 16515072 + 2461477888 + A_bytes (as0_EXTRA cs E) + BUDGET <= Mh_0132.AsanInitK.LIMIT).
  { unfold as0_EXTRA. cbn [A_bytes fst snd]. unfold Mh_0132.AsanInitK.LIMIT, target_alloc_limit. lia. }
  (* [comment removed for export] *)
  destruct (as0_main_entry sp brk0 rdraw a0s path envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc r Hsp Hva Hve Hfit Hlau Hvl HRZ BUDGET Mh_0145.NarInv.LENMAX Mh_0145.NarInv.KMAX mp_bud (as0_EXTRA cs E) XWF XBL mp_gap
  h Hh2 E R FULL model HC) as (can & tid & HR & HK & LZ & FDS & _ & STR).
  pose proof (as0_main_auxv sp brk0 rdraw a0s path envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc r Hsp Hva Hve Hfit Hlau Hvl HRZ BUDGET Mh_0145.NarInv.LENMAX Mh_0145.NarInv.KMAX mp_bud (as0_EXTRA cs E) XWF XBL mp_gap
  h Hh2 E R FULL model HC) as AUXA.
  destruct LZ as (_ & _ & _ & MI & HALT).
  destruct CLI as (_ & _ & _ & _ & S1 & S2 & S3 & S4 & S5 & _).
  cbn [as0_rn rn_ar as0_ar ar_stack_top ar_stack_bottom ar_sptop] in S1, S2, S3, S4, S5.
  assert (SDEF : defined FULL usp (ar_stack_top ar - usp)).
  { apply (as0_main_stack_defined sp brk0 rdraw a0s path envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc r Hsp Hva Hve Hfit Hlau Hvl HRZ BUDGET Mh_0145.NarInv.LENMAX Mh_0145.NarInv.KMAX mp_bud (as0_EXTRA cs E) XWF XBL mp_gap
  h Hh2 E R FULL model HC); unfold ar, cs; cbn [as0_ar ar_stack_top]; rewrite SPV in *.
  - rewrite S5. rewrite <- Z.add_mod_idemp_l by lia. rewrite S3. reflexivity.
  - lia. }
  assert (DI : dinv ar HI sp FULL [] [] (Mh_0145.NarInv.KCNT, 2 ^ 36) (as0_A0x cs E) FULL model).
  { apply DINV; [exact RI | exact MI | exact HALT | reflexivity | | | exact (APSK.co_rdr _ _ _ _ _ _ _ _ _ _ _ HC)].
  intros x Hx. apply (as0_stksh_main sp brk0 rdraw [a0s; path] envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva Hve Hfit Hlau r h Hh2 E R FULL model HC).   (* [comment removed for export] *) unfold STKTOP, ar, cs in Hx. cbn [as0_ar ar_sptop ar_stack_top] in Hx. rewrite SPV in Hx. exact Hx.
  intros x Hx. apply (as0_stksh_main_hi sp brk0 rdraw [a0s; path] envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva Hve Hfit Hlau r h Hh2 E R FULL model HC). unfold ahl_ceil, ar, cs in Hx. cbn [as0_ar ar_sptop] in Hx. rewrite SPV in Hx. exact Hx. }
  destruct (STR 1%nat ltac:(lia)) as (STR1 & PV1 & PH1). cbn [nth] in STR1, PH1.
  (* [comment removed for export] *)
  assert (T1 : Z.of_nat (total_arg_bytes_nat (firstn 1 [a0s; path])) = Z.of_nat (length a0s) + 1)
  by (unfold total_arg_bytes_nat; cbn [firstn fold_right]; lia).
  assert (CP1 : cat_argv_ptr (ed_top rdraw) [a0s; path] envp execfn 1 = Z_to_bv 64 (bv_unsigned (cat_argv_ptr (ed_top rdraw) [a0s; path] envp execfn 1)))
  by (symmetry; apply Z_to_bv_bv_unsigned).
  rewrite PV1, T1, Z.add_assoc in CP1. rewrite PV1, T1 in PH1.
  unfold APSK.cfg_of, cs. rewrite (HSA_pc h Hh2). fold cs.
  refine (DRV_MAIN Halloc Hfs DRV_CONSTS sp a0s path envp fs Hsp Hva Hve Hvfs ar HI _ _ can tid _ (as0_A0x cs E) (Mh_0145.NarInv.KCNT, 2 ^ 36) R FULL model HIok FNok ICok LIok (LSXFA ar) DL HR HK _ DI SDEF FDS EFS _ _ eq_refl _ _).
  - (* [comment removed for export] *)
  exact AUXA.
  - rewrite <- CP1. exact STR1.
  - rewrite <- CP1, PV1, T1. lia.
  - rewrite <- CP1. intros i Hi.
  exact (as0_main_str_defined sp brk0 rdraw a0s path envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc r Hsp Hva Hve Hfit Hlau Hvl HRZ BUDGET Mh_0145.NarInv.LENMAX Mh_0145.NarInv.KMAX mp_bud (as0_EXTRA cs E) XWF XBL mp_gap
  h Hh2 E R FULL model HC 1%nat ltac:(lia) i Hi).
  - pose proof HT as (_ & _ & _ & _ & CLI' & _). destruct CLI' as (_ & _ & SAH & _). exact SAH.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Halloc Hfs L C IL Lay LSt BUDGET BUD_ge BUD_hi INST_OK FREE_NULL H4E ICPT_OK EXc EXT_OK GAP_OK FAMP LIB_OKF FAM_OK DLA_OK DRV_CONSTS DRV_MAIN USAGE LSXFA Hsp Hbrk Hva Hve Hfit Huid Hhw Hvfs Hmb Hlau Hvl HRZ"] Theorem as0_realizes_spec_run :
    srealizes ASEGS0 scfg (init_config ASEGS0 Asan.M.init_pc APH0 sp brk0 mbase rdraw AsanInitK.LIMIT
                                 (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf))
              (spec argv fs).
  Proof.
    (* [comment removed for export] *)
    pose proof as0_main_phase as HM. rewrite HRZ in HM.
    exact (as0_startup_closed scfg Halloc sp brk0 mbase rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf
             Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hvl Hlau (fun fs' => spec argv fs') (fun fs' => spec_has_nil argv fs') HM).
  Qed.
End MainPhase.
