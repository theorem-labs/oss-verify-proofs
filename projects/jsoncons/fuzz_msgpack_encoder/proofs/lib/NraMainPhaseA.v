(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3SoundK AsanPlanSoundK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0077. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0107. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AxSymExec3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3SoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanCoreK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanInitK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0DefsK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0PlanImagesK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0077.Na0StartupK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffBridgeK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffBInvK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffRolesK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0HandoffK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0107.Na0HSK_0 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0107.Na0HSK_1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0107.Na0MainTableK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0HandoffInstK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0DrvEntryK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0077.Na0StartupFinalK.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require NraArtHandoffK NraArtHandoffInstK NraStkShK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0077. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceANull OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.LibIfaceAB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtRuns OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.ArtBridge OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.NarInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.NarFsInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.NraArtHandoffK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.NraArtHandoffInstK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.NraStkShK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.As0DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0077.Na0DrvEntryInst OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0Drv_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvRead OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvStdio OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057.Na0ExitCells.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.ShapeLaws OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.Spec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.BigintSpec.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080.HeapIfaceAMxI OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080.StrictOfB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080.StrictOfBI.      (* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.PnAImgGap.      (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023.
Ltac2 kr_t_NraMainPhaseA () := "C47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib7Mh_00634Spec1WC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00634Spec9exit_codeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg>t_emit_has_nilC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib7Mh_00634Spec5t_dieC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib5Arith8PeanoNat3Nat3lebC59OSSVerify5KrLib7Mh_00634Spec?msg_cannot_openC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00634Spec=list_byte_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00634Spec>msg_read_errorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg6t_alt2C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupC59OSSVerify5KrLib7Mh_0063:BigintSpec6t_bodyC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib7Mh_00639ShapeLaws@t_alt2_has_nil_lC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib7Mh_0063:BigintSpec4specC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_00634Spec9msg_usageC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib7Mh_00634Spec8dot_pathC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr05C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4amap01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C59OSSVerify5KrLib7Mh_0132=HandoffRolesK4roleC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4amap00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5mkind01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5mkind04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01078Na0HSK_04HS_0C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>NraArtHandoffK8I_KSPACEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117;Na0HandoffK8M_KSPACEC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>NraArtHandoffK6I_PARRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117;Na0HandoffK8M_PTRARRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01078Na0HSK_14HS_1C1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC59OSSVerify5KrLib7Mh_0117?Na0HandoffInstK3HSAC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7am_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6am_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK2uEC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr07C49OSSVerify5KrLib>NraArtHandoffK6uE_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132<HandoffBInvK4resZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0132=HandoffRolesK5rbaseC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC49OSSVerify5KrLib>NraArtHandoffK6as0_rnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv8rn_kbaseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv7rn_parrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117;Na0HandoffK7as0_RESC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv7art_RESC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib4Init9Datatypes4prod01K46Stdlib9micromega5Tauto8GFormula05I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K3env00C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA9role_ks_0C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA9role_ks_1C1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic4True00K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib7Mh_01456NarInv4KMAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv6LENMAXC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib7Mh_00238AsanCeil>bottomup_floorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00238AsanCeil=alloc_ceilingC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117?Na0HandoffInstK;HSA_numbersC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7a_totszC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7a_eagerC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8a_abytesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC47Corelib4Init3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6a_mapsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib7Mh_01178Na0DefsK6ASEGS0C1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib7Mh_0117>Na0PlanImagesK<asan0_res_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK2pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0107=Na0MainTableK6HS_as0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init5Logic9False_indC59OSSVerify5KrLib7Mh_0117?Na0HandoffInstK8HSA_someC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib7Mh_0077;Na0StartupK5HOLESC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0077?Na0DrvEntryInst;drv_chk_HSAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117<Na0DrvEntryK9ent_modelC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C56Stdlib5Arith8PeanoNat3Nat6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvC4ELinuxProcessSemantics?LinuxProcessSem3Run@entry_stack_fitsC49OSSVerify5KrLib>NraArtHandoffK6as0_arC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC49OSSVerify5KrLibBNraArtHandoffInstKAas0_art_handoff_hC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC49OSSVerify5KrLib>NraArtHandoffK9as0_BASExC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>NraArtHandoffK7as0_A0xC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117?Na0HandoffInstKBas0_handoff_staticC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA;as0_RES_artC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA8mp_gap_hC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117<Na0DrvEntryK7sp0_valC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib7Mh_01456NarInv7art_gs0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv=art_alloc_repC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv5rn_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv<art_eager_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv=art_client_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv:art_run_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv>art_rt_staticsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv=art_rt_threadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv>art_rt_primaryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv=art_rt_chunksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv:art_rt_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv;art_rt_quarC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv<art_rt_depotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv9art_rt_iaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv=art_rt_blocksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv<art_rt_ghostC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA3HIRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_hiC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ>asan_iface_okR00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00809StrictOfB=rt_flag_in_fsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00809StrictOfB9strict_okC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA3HIAC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0089<HeapIfaceAMx>asan_iface_okB00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00809StrictOfBCstrict_free_null_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089>HeapIfaceANull?afree_null_specC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0089:IcptIfaceA8aicpt_ok00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ;asan_ext_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00809StrictOfB=strict_of_nilC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ9strict_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0080:StrictOfBI;strict_icptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01799PnAImgGap6PMAGAP:rt_img_gapC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01c49OSSVerify5KrLib=NraMainPhaseA;lib_ext_okGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv5rn_arC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv8art_rn_kC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0092:LibIfaceAB5lla_LC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0092:LibIfaceAB=lib_iface_okA00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_01199Na0DrvLib;drv_layoutA00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>NraArtHandoffK<as0_EXTRA_wfC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>NraArtHandoffK9as0_EXTRAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct4A_wfC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>NraArtHandoffK3KSHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct7A_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0077?Na0DrvEntryInst>as0_main_entryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec<cat_argv_ptrC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthI47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7Mh_0077?Na0DrvEntryInst=as0_main_auxvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117<Na0DrvEntryK9auxv_listC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct>H_off_segmentsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC59OSSVerify5KrLib7Mh_00368AsanAcct:lazy_coverC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00368AsanAcct4MInv00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI47Corelib4Init5Logic2or00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7app_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ;shadow_blkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<blocks_apartC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib7Mh_0089:HeapIfaceA=fframes_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5ar_fsC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA?ar_stack_bottomC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_stack_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA>shadow_allowedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC49OSSVerify5KrLib>NraArtHandoffK4topEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0077?Na0DrvEntryInstFas0_main_stack_definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib6STKTOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<in_shadow_ofC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC49OSSVerify5KrLib9NraStkShK>as0_stksh_mainC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppC49OSSVerify5KrLib9NraStkShKAas0_stksh_main_hiC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_01199Na0DrvLib4dinv01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_01199Na0DrvLib4dinv00C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_envpC4ELinuxProcessSemantics?LinuxProcessSem3Run?total_arg_bytesI47Corelib5Lists7ListDef6Forall00C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei>path_has_slashC4ELinuxProcessSemantics?LinuxProcessSem2Fs8path_eqbC46Stdlib5Lists4List2tlC4ELinuxProcessSemantics?LinuxProcessSem2Fs8valid_fsc49OSSVerify5KrLib=NraMainPhaseA<inst_ok_stmtC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA>free_null_stmtC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA<icpt_ok_stmtC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA;ext_ok_stmtC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA;dla_ok_stmtC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA?drv_consts_stmtC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA=drv_main_stmtC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C59OSSVerify5KrLib7Mh_0119;Na0DrvEntry:auxv_listAC1?~~~~~~~~~~~~~~~I46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr07K46Stdlib;setoid_ring<Ring_polynom5PExpr05K46Stdlib;setoid_ring<Ring_polynom5PExpr06I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7mod_mulC46Stdlib9micromega;ZifyClasses9and_morphC59OSSVerify5KrLib7Mh_0077?Na0DrvEntryInstDas0_main_str_definedC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA6HSA_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK:holes_stmtC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib7Mh_01329AsanInitK5SINV0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01329AsanInitK5argH0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib>AsanPlanSoundK4APSK5cs_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK6cfg_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC59OSSVerify5KrLib7Mh_01456NarInvBart_handoff_targetC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_01099ArtBridge=bridge_static00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01458NarFsInv9art_fsinvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01099ArtBridge4BINVC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv9art_kn_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv;art_lazy_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv=art_credit_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv9art_ifaceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0DrvEntry9env_mainAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117;Na0HandoffK6as0_A0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecCtotal_arg_bytes_natC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0116:As0DrvKitA5lzinvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC49OSSVerify5KrLib>NraArtHandoffK4botEC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substI69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3acs00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01178Na0DefsK4APH0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01178Na0DefsK5ASAN0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01329AsanInitK5LIMITC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7fds_stdC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I59OSSVerify5KrLib7Mh_01458NarFsInv7art_fsg00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01458NarFsInv8art_fsg0C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>NraArtHandoffK3K0DC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv4KCNTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5e_sp0C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0DrvEntry8sr_mainAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0DrvEntry8kn_mainAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8FS_BYTESC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I47Corelib4Init5Logic5False00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00I59OSSVerify5KrLib7Mh_01456NarInv7art_run00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0089:HeapIfaceA8asan_run00C1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA6mp_budC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA6mp_gapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00357ArtRuns3aev00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0089:HeapIfaceA:asan_iface00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_LOC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0089:HeapIfaceA;asan_layout00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX23env00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei;dotdot_pathC46Stdlib9micromega8ZifyInst7Inj_Z_ZC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiI47Corelib7Numbers7BinNums1N00C49OSSVerify5KrLib>AsanPlanSoundK>asanreflect_fxC1?~~~~~~~~~~~~~~~I46Stdlib;setoid_ring<Ring_polynom3Mon00C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA<spec_has_nilC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0077@Na0StartupFinalKBas0_startup_closedC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib=NraMainPhaseA>as0_main_phaseC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLiaT.plia1.
Import ListNotations.
Open Scope Z_scope.

#[local] Existing Instance PropExec.fx0.

(* [comment removed for export] *)
Lemma spec_has_nil : forall argv fs, spec argv fs [].
Proof.
ltac2:(KReplay.run1 (kr_t_NraMainPhaseA ()) [] "p'0h01bi001bh11fh21li011lh32l0i022l0h41mh51Dh62a0h74argvi034argvh82fsh91oi041oh:1ph;1xi051xi064datai072l1i082l2i092l3i0:4pathp;1p;2p;3p-1p10000p4p710R0p9g000LR1p4p70R2P0p8P2p1001:p4p710p8g001Xj1<Tg002=j1LTg002[j1DTg003>R2j1=Tg003^j1KTg004<j2JTg004oj1ITg005jj2CTg006fj2BTg007jj1;Tg008Jj3Aj22Tg009Aj2@Tg009aj2?Tg00:Aj17Tg00;Bj28Tg00<Aj1:Tg00=Aj23Tg00>=j29Tg00?2j26Tg00@0j35Tg00@Pj3>Tg00AWR0j1ETg00B9j3FTg00C5j3GTg00CLj1HTg00DGj11Tf2R3f1R4f0R53G#Hp=4%15#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g00Df#<R6#<#<#L#DR7#=R8#=R9%K6R6/J4%I6/C5'Bg00EK#;R69A45R:eX11X48P:^11^48P2P8P2P8g00FAR:P5%;7R;=485/23P2P8P:P5A48;3f4R<'2P2P8P:P5g00G;R=P:g00G[#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0R>1@74'?R?%74R@f6RA'2RBP=P:184;RCPBP=P:g00H:RD,84RE%:4RF/2A,3BP0P8P:19A4%73RGf7RH'2165H'3PBn10110500021010600n0100000020000n0100000020000n0100000020000A48;Af8RB'2n10110700020120108109n1011020002002110:107n10110300020021101102P6O1P3P5%;8RI948;P4O2P2P8P2P8P:P5A5835948;/2AP2P8P:P5P=P:P?12@BR@P=P:PCP@P=P:PE12FB,3@P0P8P:19B4f9RF,2G165F'3P@n10110500021010600n0100000020000n0100000020000n0100000020000A58A<948;f:R@'2n10110700020120108109n1011020002002110:107P6O1P5P<A584I948;f5RIO2P2P8P2P8P:P5P=P:1@73,?>12G@R>P=P:183;R7P>P=P:183D%:3/2@,3>P0P8P:19@3f3R2#7REf;RC'2RJ165C'3P>n10110500021010600n0100000020000n0100000020000n0100000020000A58<3958B948;f<RB'2n10110700020120108109P6O1P5P?P=P=P=P:P5PJP=P:182;PJP=P:182DR?%:2/2C,3JP0P8P:19C2%7<R2/2BR3165B'3PJn10110500021010600n0100000020000n0100000020000n0100000020000P6O1P5PFPGP@O2P7P=P=P=P:P5P3P=P:18<D%:</2BRD,33P0P8P:19B<R<%7IR7f=RG'2RJ165G'3P3n10110500021010600n0100000020000n0100000020000P6O1P5P@PEPCO2P?P=P=P=P:P5%:I/2G,3JP0P8P:19GI%7Af>RA'2R=165A'3PJn10110500021010600n0100000020000P6O1P5PCP2PBO29>3DP<%E8P0P8P0P8P:P5%7HRHf?R:'2R0165:R<'3P=n10110500021010600P6O1P5PAPHP:O29>0<X28P5O1PBP7PGO2n10110400021010100b9n0110000020000b0n0110000020000b0n0110000020000b0PBA5845958I958F948;PGO2X29X;8P4P5O2n10110101020120101101X39X:8P4P5O2n10110101020021101101X39X68P4P5O2n10110101020021101101b5AF456eX81W7o"). Qed.

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
  forall (ar : asan_run) (HI : asan_iface) (p0 p1 can tid : word) (A0 : list (Z * Z)) (cr0 : credit)
         (R : bvmap 5 word) (M0 : word -> option byte) (model : Model),
    asan_iface_okB L ar C scfg HI -> afree_null_spec L ar scfg HI -> aicpt_ok L ar IL scfg HI -> lib_iface_okA Lay ar scfg HI (LSt ar) ->
    (forall g M, ls_ok (LSt ar) g M -> exists ax : axv, atexit_cellsA M ax) ->      (* [comment removed for export] *)
    drv_layoutA L ar IL sp ->
    SX2S.regs_ok (env_mainA sp p0 p1 can tid R) sr_mainA R ->
    SX2S.know_ok ASEGS (env_mainA sp p0 p1 can tid R) (mrestrict (ahid A0 model) M0) kn_mainA ->
    auxv_atA sp p0 M0 ->                                                     (* [comment removed for export] *)
    dinv ar HI sp M0 [] [] cr0 A0 M0 model ->
    defined M0 (bv_unsigned sp) (ar_stack_top ar - bv_unsigned sp) ->
    m_fds model = APSK.fds_std -> m_fs model = fs ->
    rdn ASEGS (mrestrict (ahid A0 model) M0) p1 (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    bv_unsigned sp <= bv_unsigned p1 /\ bv_unsigned p1 + Z.of_nat (length path) + 1 + 16 <= 2 ^ 47 ->
    cr0 = (8192, 2 ^ 36) ->
    (* [comment removed for export] *)
    defined M0 (bv_unsigned p1) (Z.of_nat (length path) + 1 + 16) ->
    shadow_allowed A0 (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xaea2c) M0 (seg_rom ASEGS)) model) (spec [a0s; path] fs).
(* [comment removed for export] *)
Definition usage_stmt (scfg : SpuriousCfg) : Prop :=
  forall sp brk0 rdraw argv envp uid hw fs, valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp -> valid_fs fs ->
  forall h, (h < 2)%nat -> forall E R FULL model,
    APSK.cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT (SINV0 APH0 sp rdraw brk0 argv envp uid hw) (argH0 APH0 sp rdraw argv envp uid hw) fs E (HSA h) R FULL model ->
    length argv <> 2%nat ->
    srealizes ASEGS0 scfg (APSK.cfg_of ASEGS0 R (APCK.pc (HSA h)) FULL model) (spec argv fs).

(* [comment removed for export] *)
Lemma role_ks_0 : role HS_0 I_KSPACE = M_KSPACE /\ role HS_0 I_PARR = M_PTRARR.
Proof.
ltac2:(KReplay.run1 (kr_t_NraMainPhaseA ()) [] "p;1p;3p;2p;4g003^j15Tg00I4j16Tg00J8j1=Tg00K<j3;Tg00L@j19Tg001Xj11Tg00Lej37Tg00Mfj34Tg00N@j2<Tg00NZj4ATg00O5j2:Tg00P4j2@Tg00DGj10Tf0R0#1#1#1#1p=2%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=3%10#1p=8%00#0p=?%00#0#0#0#0#0#0#0p=>%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=Bg00POR0g00QPR1g00Df#2#2#2R2#5#6R3g00G[#3#3#3#3#3#3#3R4#=3;%22#2R2#9#1#8#9#2#2#2#5#6g00R<37R5;45%?4#>#B#=9;13%12#8#5#6g00S>37R2=4021<051<02CAg00T@R2g00U:':g00V6540g00W7,:2g00X1540'@do"). Qed.
Lemma role_ks_1 : role HS_1 I_KSPACE = M_KSPACE /\ role HS_1 I_PARR = M_PTRARR.
Proof.
ltac2:(KReplay.run1 (kr_t_NraMainPhaseA ()) [] "p;1p;3p;2p;4g003^j15Tg00I4j16Tg00J8j1=Tg00K<j3;Tg00L@j19Tg001Xj11Tg00Lej37Tg00Mfj34Tg00N@j2<Tg00NZj4ATg00O5j2:Tg00P4j2@Tg00DGj10Tf0R0#1#1#1#1p=2%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=3%10#1p=8%00#0p=?%00#0#0#0#0#0#0#0p=>%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=Bg00POR0g00QPR1g00Df#2#2#2R2#5#6R3g00G[#3#3#3#3#3#3#3R4#=3;%22#2R2#9#1#8#9#2#2#2#5#6g00R<37R5;45%?4#>#B#=9;13%12#8#5#6g00S>37R2=4021<051<02CAg00Y2R2g00U:':g00V6540g00W7,:2g00X1540'@do"). Qed.
Lemma as0_RES_art : forall h, (h < 2)%nat -> forall E, as0_RES E = art_RES (as0_rn E (HSA h)).
Proof.
ltac2:(KReplay.run1 (kr_t_NraMainPhaseA ()) [] "p'0h02Hhh13Hh0h27__arithh34__ffh48__varmaph55__with64cstrh71Hh82Hah94__p1h:6__sat0h;6__sat1h<4__x1h=1ah>1hh?1zh@1EhA1RhB1ni001nhC1xp&0p;1p;2p;4p;3p;6p;<p;7p;8g00DGR0j10Tg00YlR1j2:Tg00ZDj14Tg00P4R2j2ATg00[DR3j1HTg003^j1<Tg00[dj2DTg001Xj13Tg00\AR4j29Tg00N@j2ITg00\]j4`Tg00]Dj1^Tg007jj1QTg003>j1\Tg00]ij2~Tg00^Gj1zTg00^ej1wTg00_Pj2ETg00`3j2qTg00`Vj1mTg00a8j3VTg00a[j6lTg00b?j2kTg00baj2jTg00Mfj32Tg00cMj3iTg00clj4hTg00d^j2gTg00e>j1?Tg00f@j1fTg00gAj21Tg00L@j1GTg00h<j2cTg00I4j1RTg00J8j1bTg00K<j3]Tg00hYk204Tg00iAk303Tg00iek102Tg002=k101Tg00jCk300Tg00jfj3ZTg001:j6LTg00k`j2Wj1yTg00l^j3YTg00m^j4xTg00n:j2vTg00o4j1tTg0100j1sTg010kj1rTg011kj1uTg00O5j2XTg012fl<pTg013Kl<{Tg0140j2|Tg014Lj4UTg0157j7oTg015[j8}Tg016?j4JTg00@0j3FTg016_j7nTf0R5g00U:R6'Xp=6g00POR7g00V6R8725p=Cg00W7R9,X5p=5g00X1R:9275p=;g017CR;P;g017bR<P<P0P3P3f3R0g018@f2R=f1R>P5M<pp=eP;P<P1P3P4g018df5R4f4R3P0P=P>P5M<{p=dg019FR1/|5p=7P<P>g019dP5CUp=PP>g01:KR?g01:jR@P@g01;JRAP5g01;jFop=@P<P>g01<JP5CUp=OP0P?P@P@PAP=P>P5G}p=T%05#0p=MP<P<110=P>CJ=F35p=8%35#3#3#3p==%35#3p=Sf6RBP<P<P4P3CJP<P<P=P>CJ=F053Fp=>%05#0#0#0p>05%05#0#0#0#0#0#0#0p=_%05#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=a%05#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=BP<P<P>P5CJp=NAF=>59F30p=KP=P?P@P@PAP>P5Fnp=[g00G[RC#0RD#0RE,:5RFg01=1P;%4>RG#6#C%5G#;'A^0FP=1:CEg01>4W0P;%05RC/:E%0>RF#4RG#6#C%5G#;'A]0P51:DEg01?0W0%0C/:E%0FRC/:E%H>RDg00DfRG#<RH'D/DH%3GRI#<RJ'9RKPC1D5HXC<RCPCPDO1RLO1PCPFPLPCP>PD1I<DCeCePEPJ1I<JRDEdP5C`PK%^=%H=#7p-0RKg01?lRC#QRL%\CRC1~<>%z<RF%w<RM1E<1RN1q<GRG'P,@M%m@ROPM1E<HRP9V<G=V<P1E<JRP'O,@MPOPMP?P@P@PAP0ElCTCT1kMARAP5P=g00G;R@g01@XR?'I1j5==2@?dAi<1>ChR?b3b4b5X<<W9%751D>H/DH/9JP0[[^<<^9KP5%M3#4RK#6#C%5K#;'A%H3P>P=O4b2b6b1W0X>;P5O1n0110000020011100XB;P5O1n0110000020011100P>O1%4=RK#6#C%5K#;'AP2%40R0#6#C%50#;1g<<R0#\R2P0P=%?8RH%f8R@,1=P0P=%?:RO%f:RG,1=%Q0RQD8D8P0P=%43R3#6#?%3I#=RR#S#=RS#=#=RT#G#3#S#G#=#=#=#<RUP0P=%53#?%GI#G#G#<,cJRIPQD8D832P5%44#6#CP7P8f7R3#4#5R=#;P011BHRV11B@P011BO11BGPQF>RWP0PB%?>PUP0PBf8RX#4#5#?PIPQD8D8522[X=7%4BRY#5#;P7P:P0PVPUP0%?5,1BPIPQF>922WX=7P<PUP0g00QPRW%<S#RRS%ME$05#_#a#B#B#B#B#B#BRV#b3]RZ,1BR[P5P0%MV#_#a#b9]WSRS,1BRW%3T#S#<RT#RRV,1BPQF>P01N[UR[P01NWIPQDKR\522X?<P<PTP0P[P01NW5PQDK=22\X?<P0P4PZPUP0P4PSPIPQD8D8,I2114V1:3E%H3RV/9JRSP3PV1I<VPEPJPDEdPBC`RBPS%^XRD%HX#7RX%<RRE-04JRV191J%7E1cJER3,91[[R1%7JRZg01A8R\B03JE>UW8RE%73\\^8ZRZPLPC&02<R\PF1E<TRJ,PN,@M&01R:00<PRP,OJ,@M5[MPAP?b3b4b5%7T19T3'AP5b2b:b;b6b19Z4TEL%RU,14PBPSPDPXPVP1PEPZPLPCP\PF1E<UR<,PN,@M1O<P,@M5[MPAP?b3b4b5%7U19U3'AP5b2b:b;b6b19Z4UELP0114HRH114@P0114ORO114GPQF>P0PHPUP0POPIPQF>522eP=P5ELW7%6YP5ELW7P>P5O2n2001000000121000000bAP01W58P01W5:PQDKP0AY5K6PUP0AY5K9PIPQF>522eP7P0%y5P7P8P7P:%Q7DKCxP01v5KRK#tPUP0%sKPIPQF>522e%r5%uK522eW@W0X>;o"). Qed.

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
  Variables nofile sigmask : word. Variable abrt : bool. Variable ur : InputStream.  (* [comment removed for export] *)
  Hypothesis Hsp : valid_sp sp. Hypothesis Hbrk : valid_brk ASEGS0 brk0.
  Hypothesis Hva : valid_argv argv. Hypothesis Hve : valid_envp envp. Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid. Hypothesis Hhw : valid_hwcap hw. Hypothesis Hvfs : valid_fs fs.
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
  #[local] Notation CSOK := (APSK.cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
  #[local] Notation usp := (bv_unsigned sp).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="BUD_ge"] Lemma mp_bud : 0 <= BUDGET /\ 0 <= NarInv.KMAX /\ 0 <= NarInv.LENMAX < 2 ^ 62.
Proof.
ltac2:(KReplay.run1 (kr_t_NraMainPhaseA ()) ["MainPhase"] "h02Hah14__x1h27__arithh34__ffh46__sat0h56__sat1h67__sat10h77__sat11h87__sat12h97__sat13h:7__sat14h;7__sat15h<6__sat2h=6__sat3h>6__sat4h?6__sat5h@6__sat6hA6__sat7hB6__sat8hC6__sat9hD8__varmaphE5__witp;1p;2p;3p;4p;8p;7g001Xj14Tg003^j12Tg00L@j11Tg00hYj25Tg00h<j27Tg00iAj36Tg007jj1LTg003>j1HTg00]ij2FTg00^Gj1ETg00^ej1WTg00_Pj2?Tg002=j1;Tg00a8j3CTg01ATj3VTg00`3j2UTg00`Vj1QTg014Lj4DTg015[j8PTg00b?j2OTg00N@j2NTg00baj2KTg00Mfj3ITg00cMj3JTg00clj4GTg00[dj2@Tg01B7j2MTg0140j2=Tg00\Aj2BTg00P4j29Tg00jCj3RTg0157j7STg016_j7TTg019FR0f0R1'Bp=31=01p=0%41#4p=8g017bR2f1R3;R1p=:P2P3g019dP1CDp=>P3g01:KR4g01:jR5P5g01;JR6P1g01;jFSp=<f2R7P4P5P5P6P3P1FTp=Ag00DfR8#4R9#2R:%49R;#1R<#1#1#2R='5%3:R>%0=17:=R?#3[[%0:R@g01A8RAA6:=3UW0%0?\A^0@%8<R<#2R?,5:%0?17:?R=#3[\>A6:?3VAX0@%0=\A^0@%18#1#1R?#1#4RB#2RC,5:%0C17:CRD#3[\>A6:C3VAX0@%0D\A^0@%4;R;#1#1#2RC,5:%0C17:CRE#3[\>A6:C3VAX0@%0E\A^0@%4;R;#4RE#2RC,5:%0C17:CRF#3[\>A6:C3VAX0@%0F\A^0@%19#8R9#2RC,5:%0C17:CRG#3[\>A6:C3VAX0@%0G\A^0@%2;RC,5:%0C17:CRH#3[\>A6:C3VAX0@%0H\A^0@%4?R?#2RC,5:%0C17:CRI#3[\>A6:C3VAX0@%0I\A^0@g01?lR@#L%H@1F23%E2%W2R@P4P5P5P61?2:R:%;<':%;9,::5C21?2C%;E,::5V25C21U28R8'>,<@%Q51?20R5/>8,<@%8E#8#8#8#2RE,?2,>5,<@%;?,::%;;,::5C2R;,>5,<@P2P;g01<J%;B,::CD,<@5A@5A@5A@GP1O@6P1P7g00G;R@g01@XR6'N1K17=I@6dAJ203CGb3bDbEX121@=G1MCF'@/=1%03%0E1@IHRI#01BID'9'9'9[^12P1p,6BUDGETR1p,6BUD_geO2b2b4b5b<b=b>b?b@bAbBbCb6b7b8b9b:b;%01g01BT,=0g01CLR1,=01B1D'9'9'9eo"). Qed.
  #[using="BUD_hi"] Lemma mp_gap : AsanCeil.bottomup_floor + NarInv.LENMAX + (17729665331200 + BUDGET) + (21 + NarInv.KMAX) * (NarInv.LENMAX + 4095) <= AsanCeil.alloc_ceiling.
Proof. unfold Mh_0145.NarInv.KMAX, Mh_0145.NarInv.LENMAX, Mh_0023.AsanCeil.bottomup_floor, Mh_0023.AsanCeil.alloc_ceiling. lia. Qed.
  #[using="BUD_hi"] Lemma mp_gap_h : forall h, (h < 2)%nat ->
    AsanCeil.bottomup_floor + NarInv.LENMAX + (APK.a_totsz (HSA h) + BUDGET)
    + (Z.of_nat (length (segments_reserved ASEGS0) + length (APK.a_maps (HSA h))) + NarInv.KMAX) * (NarInv.LENMAX + 4095) <= AsanCeil.alloc_ceiling.
Proof.
intros h Hh. destruct (HSA_numbers h Hh) as (N1 & N2 & N3 & N4). rewrite N4, asan0_res_eq. cbn [length Nat.add]. change (Z.of_nat 21) with 21.
unfold Mh_0145.NarInv.KMAX, Mh_0145.NarInv.LENMAX, Mh_0023.AsanCeil.bottomup_floor, Mh_0023.AsanCeil.alloc_ceiling. lia.
Qed.

  #[using="Type"] Lemma HSA_pc : forall h, (h < 2)%nat -> APK.pc (HSA h) = 0xaea2c.
Proof. intros [|[|h]] H; [reflexivity | reflexivity | lia]. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Halloc Hfs L C IL Lay LSt BUDGET BUD_ge BUD_hi INST_OK FREE_NULL H4E ICPT_OK EXc EXT_OK GAP_OK FAMP LIB_OKF FAM_OK DLA_OK DRV_CONSTS DRV_MAIN USAGE LSXFA Hsp Hva Hve Hfit Hvfs"] Theorem as0_main_phase : APSK.holes_stmt ASEGS0 scfg ASAN0 AsanInitK.LIMIT HS_as0 SINV argH (HOLES (fun fs' => spec argv fs')) fs.
Proof.
intros h ch Hh E R FULL model HC.
assert (Hh2 : (h < 2)%nat) by (destruct h as [|[|h]]; [lia | lia | discriminate Hh]).
rewrite (HSA_some h Hh2) in Hh. injection Hh as <-.
assert (EFS : m_fs model = fs).
{ exact (proj2 (ent_model sp brk0 rdraw argv envp uid hw fs (HSA h) (drv_chk_HSA h Hh2) E R FULL model HC)). }
unfold HOLES. rewrite EFS.
destruct (Nat.eq_dec (length argv) 2) as [Hargc|Hargc]; [|exact (USAGE sp brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit Hvfs h Hh2 E R FULL model HC Hargc)].
destruct argv as [|a0s [|path [|x l]]] eqn:Hargv; try discriminate Hargc. clear Hargc.
set (cs := HSA h). set (rn := as0_rn E cs). set (ar := as0_ar E cs).
set (MAPS0 := vm_maps (m_vmmaps model)). set (RESV0 := segments_reserved ASEGS0). set (NOACC0 := vm_noaccess (m_vmmaps model)).
pose proof (as0_art_handoff_h sp brk0 rdraw [a0s; path] envp uid hw fs Hsp Hva Hve Hfit BUDGET BUD_ge BUD_hi h Hh2 E R FULL model HC) as HT.
pose proof (as0_handoff_static sp brk0 rdraw [a0s; path] envp uid hw fs BUDGET Mh_0145.NarInv.LENMAX Mh_0145.NarInv.KMAX mp_bud mp_gap h Hh2 E R FULL model HC) as BS.
rewrite (as0_RES_art h Hh2 E) in BS. fold cs rn in BS.
pose proof (sp0_val sp brk0 rdraw [a0s; path] envp uid hw fs Hsp Hva Hve Hfit BUDGET Mh_0145.NarInv.LENMAX Mh_0145.NarInv.KMAX (HSA h) (drv_chk_HSA h Hh2) (mp_gap_h h Hh2)
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
destruct (as0_main_entry sp brk0 rdraw a0s path envp uid hw fs Hsp Hva Hve Hfit BUDGET Mh_0145.NarInv.LENMAX Mh_0145.NarInv.KMAX mp_bud (as0_EXTRA cs E) XWF XBL mp_gap
h Hh2 E R FULL model HC) as (can & tid & HR & HK & LZ & FDS & _ & STR).
destruct (as0_main_auxv sp brk0 rdraw a0s path envp uid hw fs Hsp Hva Hve Hfit BUDGET Mh_0145.NarInv.LENMAX Mh_0145.NarInv.KMAX mp_bud (as0_EXTRA cs E) XBL mp_gap
h Hh2 E R FULL model HC) as (uidz & rnd & hwz & AUXW & AUXU & AUXH & AUXR1 & AUXR2).
destruct LZ as (_ & _ & _ & MI & HALT).
destruct CLI as (_ & _ & _ & _ & S1 & S2 & S3 & S4 & S5 & _).
cbn [as0_rn rn_ar as0_ar ar_stack_top ar_stack_bottom ar_sptop] in S1, S2, S3, S4, S5.
assert (SDEF : defined FULL usp (ar_stack_top ar - usp)).
{ apply (as0_main_stack_defined sp brk0 rdraw a0s path envp uid hw fs Hsp Hva Hve Hfit BUDGET Mh_0145.NarInv.LENMAX Mh_0145.NarInv.KMAX mp_bud (as0_EXTRA cs E) XBL mp_gap
h Hh2 E R FULL model HC); unfold ar, cs; cbn [as0_ar ar_stack_top]; rewrite SPV in *.
- rewrite S5. rewrite <- Z.add_mod_idemp_l by lia. rewrite S3. reflexivity.
- lia. }
assert (DI : dinv ar HI sp FULL [] [] (Mh_0145.NarInv.KCNT, 2 ^ 36) (as0_A0x cs E) FULL model).
{ apply DINV; [exact RI | exact MI | exact HALT | reflexivity | |].
intros x Hx. apply (as0_stksh_main sp brk0 rdraw [a0s; path] envp uid hw fs Hsp Hva Hve Hfit h Hh2 E R FULL model HC). unfold STKTOP, ar, cs in Hx. cbn [as0_ar ar_sptop ar_stack_top] in Hx. rewrite SPV in Hx. exact Hx.
intros x Hx. apply (as0_stksh_main_hi sp brk0 rdraw [a0s; path] envp uid hw fs Hsp Hva Hve Hfit h Hh2 E R FULL model HC). unfold ahl_ceil, ar, cs in Hx. cbn [as0_ar ar_sptop] in Hx. rewrite SPV in Hx. exact Hx. }
destruct (STR 1%nat ltac:(lia)) as (STR1 & PV1 & PH1). cbn [nth] in STR1, PH1. unfold total_arg_bytes_nat in PV1. cbn [firstn fold_right] in PV1.
assert (HB : 0 <= Z.of_nat (length envp) <= 256 /\ 0 <= Z.of_nat (length a0s) <= 131071).
{ pose proof Hve as [Hle _]. pose proof Hva as (_ & _ & Hfa & _). inversion Hfa as [|x l Hx _]; subst. lia. }
assert (SR : 0x7fff80000000 <= usp <= 2 ^ 47) by (destruct Hsp as (H1 & H2 & H3); unfold sp_window_lo, sp_window_hi in H1, H2; lia).
assert (PE : Z_to_bv 64 (usp + 8 * Z.of_nat (length envp) + Z.of_nat (length a0s) + 201) = cat_argv_ptr sp [a0s; path] envp 1).
{ apply bv_eq. rewrite PV1, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia. }
unfold APSK.cfg_of, cs. rewrite (HSA_pc h Hh2). fold cs.
destruct (STR 0%nat ltac:(lia)) as (_ & PV0 & PH0). cbn [nth] in PH0. unfold total_arg_bytes_nat in PV0. cbn [firstn fold_right] in PV0.
assert (SA16 : usp mod 16 = 0) by (destruct Hsp as (_ & _ & H3); exact H3).
assert (UP0 : bv_unsigned (Z_to_bv 64 (usp + 8 * Z.of_nat (length envp) + 200)) = usp + 8 * Z.of_nat (length envp) + 200) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); apply Z.mod_small; lia).
refine (DRV_MAIN Halloc Hfs DRV_CONSTS sp a0s path envp fs Hsp Hva Hve Hvfs ar HI _ _ can tid (as0_A0x cs E) (Mh_0145.NarInv.KCNT, 2 ^ 36) R FULL model HIok FNok ICok LIok (LSXFA ar) DL HR HK _ DI SDEF FDS EFS _ _ eq_refl _ _).
- exists uidz, rnd, hwz. rewrite UP0.
split; [intros j Hj; replace (usp + 8 * Z.of_nat (length envp) + 200 - 160 + 8 * Z.of_nat j) with (usp + 8 * Z.of_nat (length envp) + 40 + 8 * Z.of_nat j) by ring; exact (AUXW j Hj)|].
repeat split; try lia.
pose proof (Z.div_mod usp 16 ltac:(lia)) as DM. rewrite SA16 in DM.
replace (usp + 8 * Z.of_nat (length envp) + 200) with ((2 * (usp / 16) + Z.of_nat (length envp) + 25) * 8) by lia. apply Z.mod_mul. lia.
- rewrite PE. exact STR1.
- rewrite PE, PV1. rewrite PV1 in PH1. lia.
- rewrite PE. intros i Hi.
exact (as0_main_str_defined sp brk0 rdraw a0s path envp uid hw fs Hsp Hva Hve Hfit BUDGET Mh_0145.NarInv.LENMAX Mh_0145.NarInv.KMAX mp_bud (as0_EXTRA cs E) XBL mp_gap h Hh2 E R FULL model HC 1%nat ltac:(lia) i Hi).
- pose proof HT as (_ & _ & _ & _ & CLI' & _). destruct CLI' as (_ & _ & SAH & _). exact SAH.
Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Halloc Hfs L C IL Lay LSt BUDGET BUD_ge BUD_hi INST_OK FREE_NULL H4E ICPT_OK EXc EXT_OK GAP_OK FAMP LIB_OKF FAM_OK DLA_OK DRV_CONSTS DRV_MAIN USAGE LSXFA Hsp Hbrk Hva Hve Hfit Huid Hhw Hvfs"] Theorem as0_realizes_spec_run :
    srealizes ASEGS0 scfg (init_config ASEGS0 Asan.M.init_pc APH0 sp brk0 mbase rdraw AsanInitK.LIMIT
                                 (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur))
              (spec argv fs).
Proof.
ltac2:(KReplay.run1 (kr_t_NraMainPhaseA ()) ["MainPhase"] "h03fs'p;2p;Mg00B9j22Tg04bJj21Tg04cIlM0Tp,4scfgp,6Hallocp,2spp,4brk0p,5mbasep,5rdrawp,4argvR0p,4envpp,2fsp,5stdinp,3uidp,3gidp,2hwp,6groupsp,3netp,6nofilep,7sigmaskp,4abrtp,2urp,3Hspp,4Hbrkp,3Hvap,3Hvep,4Hfitp,4Huidp,3Hhwg000LR1f0R2,20W01102X01g04dYMM0o"). Qed.
End MainPhase.
