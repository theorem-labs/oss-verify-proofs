(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AgentNodes Nodes AllocSim
  AsanAcct AsanAcctShape AsanPlacement BackingAlgebra MmapSim RefNodes Gap04.  (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanNodesIface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import AsanNodesLibE.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import AsanNodesMmLib.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import AsanCeil.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AsanNodesMmA () := "C47Corelib4Init9Datatypes3fstC47Corelib4Init5Logic7f_equalI47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00I47Corelib5Lists7ListDef6Forall00C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI69OSSVerify5KrLib2AS=AsanPlanSound3APS5cs_ok00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP;is_ecall_atC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib2AS>AsanNodesMmLib9kind_noneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLib9kind_lazyC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC47Corelib4Init9Datatypes3orbC47Corelib4Init9Datatypes4negbC69OSSVerify5KrLib2AS8AsanPlan2AP;is_tok_kindC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP9mmap_nullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP3nxtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC69OSSVerify5KrLib2AS8AsanPlan2AP2pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLibAis_ecall_at_soundC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic2ex00C69OSSVerify5KrLib2AS8AsanPlan2AP8mmap_lenC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init5Logic2eq01C69OSSVerify5KrLib2AS8AsanPlan2AP<expr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP6a_mapsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP2knC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP8lowboundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP;grant_factsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS8AsanPlan2AP4amap01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes6option02K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib2AS8AsanPlan2AP6gap_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP8no_holesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propC69OSSVerify5KrLib2AS8AsanPlan2AP8fresh_okC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses9and_morphC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC47Corelib4Init9Datatypes6lengthC69OSSVerify5KrLib2AS8AsanPlan2AP5n_resC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC69OSSVerify5KrLib2AS8AsanPlan2AP6img_hiC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib2AS8AsanPlan2AP6img_loC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib2AS8PropExec4getrC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C59OSSVerify5KrLib2AS>AsanNodesMmLib<Z_to_bv64_m1C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC69OSSVerify5KrLib2AS8AsanPlan2AP3regC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02C69OSSVerify5KrLib2AS=AsanPlanSound3APS7co_haltC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC59OSSVerify5KrLib2AS>BackingAlgebra6ivs_wfC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC59OSSVerify5KrLib2AS8AsanCeil:init_sp_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC69OSSVerify5KrLib2AS=AsanPlanSound3APS5co_wfC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2I59OSSVerify5KrLib2AS>AsanNodesMmLib:grant_post00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLib9grant_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP7a_eagerC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP8a_abytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib2AS>AsanNodesMmLib8null_cs1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6regupdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS7in_hullC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS6in_ivsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX23xhiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP7a_totszC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP5a_yloC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP7a_ghostC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP8vis_costC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP5a_brkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP4a_fdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP8a_tidsetC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS8AsanPlan2AP3acs01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP9add_entryC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<AsanNodesMmA:some_inj12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS4ext1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLib<ext1_agree''C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib2AS8PropExec4mkstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP7vis_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP7reg_litC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib2AS8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8RefNodesBgrant_ok_na_unpackC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC59OSSVerify5KrLib2AS5Gap04Aalloc_top_lt_2_64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP9kdisj_newC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP?kn_grant_filterC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:Forall_appC59OSSVerify5KrLib2AS>AsanNodesMmLib@grant_facts_pureC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLib>kdisj_new_pureC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP<grant_keep_bC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6filterC69OSSVerify5KrLib2AS=AsanPlanSound3APS@kimg_in_hull_appC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS<kimg_in_hullC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr03C69OSSVerify5KrLib2AS=AsanPlanSound3APS4atopC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib2AS>AsanNodesMmLib8gp_noaccC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib2AS>AsanNodesMmLib9v_addi_pcC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib2AS8AsanPlan2AP9budget_okC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backing_usedC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC56Stdlib6ZArith6BinInt1Z8le_transC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap@mmap_noreserve_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapHmmap_noreserve_backed_okC59OSSVerify5KrLib2AS7MmapSim:mmap_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSim5zfillC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State5m_tidC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spK59OSSVerify5KrLib2AS>AsanNodesMmLib:grant_post01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSim9zfill_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLib8zfill_inC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapAwith_mmap_backingC59OSSVerify5KrLib2AS>AsanNodesMmLibGwith_mmap_backing_plainC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLib<srz_mmap_rw1C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_add_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State=lazy_interiorC47Corelib4Init9Datatypes3appK46Stdlib9micromega=RingMicromega7Formula01C59OSSVerify5KrLib2AS8AgentLib7u64_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLibClazy_interior_freshC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?with_vm_backingC59OSSVerify5KrLib2AS>BackingAlgebraIm_vm_lazy_with_vm_backingC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLibFwith_mmap_backing_lazyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8RefNodes>noaccess_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSim6unfillC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSim:unfill_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLib9unfill_inC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLib>srz_mmap_none1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS6cfg_ofC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS7SpinAlg9srealizes00C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbK69OSSVerify5KrLib2AS:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP6escaleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP4a_ssC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX26s_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX26sr_updC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula08C59OSSVerify5KrLib2AS8RefNodes;grant_ok_naC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_addiC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C69OSSVerify5KrLib2AS8AsanPlan2AP<shadow_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP5mk_ssC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP5a_visC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes4bool02I69OSSVerify5KrLib2AS8AsanPlan2AP3acs00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I69OSSVerify5KrLib2AS:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C69OSSVerify5KrLib2AS:AxSymExec33AX25two64C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203c59OSSVerify5KrLib2AS<AsanNodesMmA>asanreflect_fxC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2AS:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeI47Corelib4Init5Logic4True00I69OSSVerify5KrLib2AS8AsanPlan2AP5mkind00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2AS:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib2AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLib6bv5_17C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLib6bv5_10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLib6bv5_12C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLib6bv5_13C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLib6bv5_14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLib6bv5_15C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLib6bv5_11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP3KHIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS=AsanPlanSound>asanreflect_fxC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS8AsanPlan2AP5mkind01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS8AsanPlan2AP5mkind02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS8AsanPlan2AP5mkind03C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00K69OSSVerify5KrLib2AS8AsanPlan2AP5mkind04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS8AsanPlan2AP5mkind05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS8AsanPlan2AP5mkind06C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLibBmmap_flags_core_22C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLibCmmap_noreserve_b_22C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLib>asanreflect_fxC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C59OSSVerify5KrLib2AS>AsanNodesMmLibDmmap_flags_core_4022C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLibEmmap_noreserve_b_4022C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201C69OSSVerify5KrLib2AS8AsanPlan2AP:fixed_argsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP:with_maps0C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC69OSSVerify5KrLib2AS8AsanPlan2AP7is_holeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP7am_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS2uEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP6am_lenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP@mmap_fixed_grantC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX29split_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP6flat_xC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS?AxSymExec3Sound4AX2S6estartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLib9fixed_cs1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLib?env_agree_refl'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP9mkind_eqbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS<AsanPlanCore3APC;is_tok_kindC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS2MrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS?AxSymExec3Sound4AX2S5elenZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS3visC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9page_baseC4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesC69OSSVerify5KrLib2AS=AsanPlanSound3APS8in_allowC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbC69OSSVerify5KrLib2AS=AsanPlanSound3APS5in_shC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC46Stdlib4Bool4Bool:orb_true_rC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atC47Corelib4Init5Logic3notC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC59OSSVerify5KrLib2AS7StoreOk?store_ok_of_allC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C69OSSVerify5KrLib2AS=AsanPlanSound3APS7co_knowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS3hidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List?Forall_flat_mapC46Stdlib5Lists4List=Forall_forallC69OSSVerify5KrLib2AS8AsanPlan2AP9shadow_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP?find_containingC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP>shadow_band_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS<hid_cons_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLibGsrz_mmap_fixed_rw_free1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLib?fixed_free_coreC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLibIsrz_mmap_fixed_none_free1C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2I69OSSVerify5KrLib2AS8AsanPlan2AP4amap00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succC69OSSVerify5KrLib2AS8AsanPlan2AP4CEILC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP6TOPMAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8AsanCeil=alloc_ceilingC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLib7CEIL_eqC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS<AsanPlanCore3APC5mkind02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS<AsanPlanCore3APC5mkind03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS<AsanPlanCore3APC5mkind04C1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00C46Stdlib9micromega8ZifyInst7Inj_Z_ZI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib2AS>AsanNodesMmLibBfixed_free_core_32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLibCmmap_noreserve_b_32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLibDfixed_free_core_4032C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLibEmmap_noreserve_b_4032C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLibFfixed_free_core_104022C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLibGmmap_noreserve_b_104022C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP?mmap_fixed_freeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP9find_holeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP6unholeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP6no_fogC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<AsanNodesMmAGmmap_fixed_grant_sound1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX2>ranges_apart_xC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC69OSSVerify5KrLib2AS8AsanPlan2AP=node_mprotectC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2APAnode_mprotect_refC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP@node_mprotect_eqC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP6rekindC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP9kn_unfillC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX26s_nextC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP7am_kindC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP6is_fogC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra<model_ivs_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS6co_sp0C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C69OSSVerify5KrLib2AS=AsanPlanSound3APS8amap_denC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS7co_noneC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib2AS>AsanNodesMmLibBmap_contains_introC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib2AS>BackingAlgebraLmprotect_budget_ok_intro_genC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8RefNodes>mprotect_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLib5sl_nnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State=maps_subtractK59OSSVerify5KrLib2AS>AsanNodesMmLib:slice_post01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS>AsanNodesMmLib:slice_post00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLib9slice_memC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS>AsanNodesMmLib:slice_hyps01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS7co_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLib9sl_chargeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP9kimg_clipC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS7co_sinvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLib7sp_mapsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLib=srz_mprotect1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra;overlap_sumC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<map_containsC69OSSVerify5KrLib2AS8AsanPlan2AP5e_sp0C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums8positive00C4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64K59OSSVerify5KrLib2AS>AsanNodesMmLib5slarm04C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS>AsanNodesMmLib5slarm00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS>AsanNodesMmLib5slarm02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP9mmap_gateC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqI69OSSVerify5KrLib2AS:AxSymExec33AX29sym_state00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP:node_mmap2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP6refuseC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<AsanNodesMmA?mmap_gate_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP7set_regC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX26s_knowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP:shadow_offC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<AsanNodesMmA@mmap_null_sound1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<AsanNodesMmAFmmap_fixed_free_sound1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS8mm2_stmtC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indC69OSSVerify5KrLib2AS8AsanPlan2AP:ENOMEM_RETC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP>node_mprotect2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<AsanNodesMmADnode_mprotect_sound1C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C56Stdlib6ZArith6BinInt1Z9mod_smallC69OSSVerify5KrLib2AS?AxSymExec3Sound4AX2S7u_sub64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX25mkAluC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS?AxSymExec3Sound4AX2S;mkAlu_denotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP4esubC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02C69OSSVerify5KrLib2AS?AxSymExec3Sound4AX2S7u_add64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP4eaddC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01C46Stdlib5Lists4List;in_flat_mapC69OSSVerify5KrLib2AS:AxSymExec33AX27lin_ge0C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib2AS:AxSymExec33AX28expr_eqbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS?AxSymExec3Sound4AX2S=lin_ge0_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS?AxSymExec3Sound4AX2S6xt_denC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_geC46Stdlib4Bool4Bool8orb_propC69OSSVerify5KrLib2AS?AxSymExec3Sound4AX2S;expr_eqb_eqC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:in_map_iffC69OSSVerify5KrLib2AS8AsanPlan2AP:dest_casesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consC69OSSVerify5KrLib2AS8AsanPlan2AP=fixed_in_argsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP=mmap_fixed_inC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2APAfixed_in_args_refC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP@fixed_in_args_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2APAmmap_fixed_in_refC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP@mmap_fixed_in_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib2AS=AsanPlanSound3APS6co_topC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<AsanNodesMmA8slarm_ofC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_flags_coreC69OSSVerify5KrLib2AS8AsanPlan2AP9kn_cutoutC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS>know_ok_cutoutC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS>know_ok_filterC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_budget_okC59OSSVerify5KrLib2AS>BackingAlgebraTmmap_fixed_rw_budget_ok_commit_introC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS6allowAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS7co_minvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLibEvm_backing_used_limitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebraVmmap_fixed_rw_budget_ok_recommit_introC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS=AsanNodesLibE@fixedin_ok_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS=AsanNodesLibEAfixedin_ok_vmmapsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_forget_rangeC4ELinuxProcessSemantics?LinuxProcessSem5StateBpage_outside_rangeC59OSSVerify5KrLib2AS>BackingAlgebraIm_vm_lazy_vm_forget_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS=AsanNodesLibEEsrz_mmap_fixedin_lazyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP9kn_rezeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS=AsanNodesLibE>asanreflect_fxC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2AS8AsanPlan2AP<fixed_in_arm00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS8AsanPlan2AP<fixed_in_arm01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS8AsanPlan2AP<fixed_in_arm02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS8AsanPlan2AP<fixed_in_arm03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLibBmmap_flags_core_32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLibDmmap_flags_core_4032C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS>AsanNodesMmLib5slarm01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS>AsanNodesMmLib5slarm03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP;node_mmapinC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP>mmap_destroyedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2APCmmap_destroyed_withC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX26lins_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX2:lin_nowrapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX26lin_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX26ealignC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:fold_rightC56Stdlib6ZArith6BinInt1Z3oppC69OSSVerify5KrLib2AS:AxSymExec33AX27srl_remC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX2:highmask_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX25snormC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX24laddC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX26lscaleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX28lin_testC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX2:lin_srangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX2;lin_nowrapRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX29xt_nowrapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX28xt_constC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX26xt_linC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX26lsub_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX2:srl_expandC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX27has_srlC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX2>lin_ge0_scaledC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<AsanNodesMmADmmap_fixed_in_sound1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS8mm3_stmtC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv5Instr5aluop00C69OSSVerify5KrLib2AS:AxSymExec33AX23linC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv5Instr5mulop00C69OSSVerify5KrLib2AS:AxSymExec33AX26xtermsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS:res_len_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS7hull_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS=AsanPlanSound3APS9shadow_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesMmLib8hull_covC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<AsanNodesMmA@node_mmap2_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesIface9OBL_mmap2C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2AS8AsanPlan2AP6atable00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<AsanNodesMmADnode_mprotect2_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesIface=OBL_mprotect2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<AsanNodesMmAAnode_mmapin_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanNodesIface:OBL_mmapinC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope Z_scope.

Import AX2. Import AX2S. Import AP. Import APS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma some_inj12 : forall {T : Type} (a b : T), Some a = Some b -> a = b.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmA ()) [] "p'0h02H0h11Hh21Th31ah41bh51ei001oi011tp;1p;2p;3p;6p-1R0p10000R1p4p710p8P0P1p4p7210p8p200R1g000MR0p4p710p8P1P0p4p7210p8g000jR2j12Tg001Lj20Tg001nj31TP0j63Tf0R0f1R3f2R4#21043104031f3R5#2R6P5P2f4R2f5P0P0P5n10110000021010100X5610541053P0E3A1543A1254P0W0P0O1b0W1W4W3X21o"). Qed.

Section Nodes.
Variable SEGS : list Segment.            Variable A : atable.
Variable nx0 : nat.                      Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.     Variable FS0 : Fs.Fs.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis RES_len : res_len_ok SEGS A.
Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
                             (segments_reserved SEGS).
Hypothesis HULL_ok : hull_ok A.                  Hypothesis SHADOW_ok : shadow_ok A.
Hypothesis HULL_cov : AsanNodesMmLib.hull_cov SEGS A.   (* [comment removed for export] *)
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_high2 : forall E M (a : word), SINV E M -> argH E a = true -> APS.uE E e_sp0 <= bv_unsigned a.   (* [comment removed for export] *)
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

#[local] Notation CSOK := (APS.cs_ok SEGS A LIMIT SINV argH FS0).
#[local] Notation HID := (APS.hid A argH).
#[local] Notation VIS := (APS.vis A).
#[local] Notation MR := (APS.Mr A argH).
#[local] Notation ALLOW := (APS.allowA A).
#[local] Notation cfg := (cfg_of SEGS).

(* [comment removed for export] *)
Let HS : nat -> option acs := fun _ => None.
Let XN : nat -> list expr -> acs -> option acs := fun _ _ _ => None.
Let XE : nat -> list expr -> acs -> option (Z * list spiece * acs) := fun _ _ _ => None.
Let XB : nat -> list expr -> acs -> option (acs * acs) := fun _ _ _ => None.
Let RES_len' : length (segments_reserved SEGS) = n_res A := RES_len.
Let HULL_ok' : 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0 /\ img_hi A <= KHI := HULL_ok.
Let SHADOW_ok' : 0 <= shadow_off A <= 2 ^ 47 := SHADOW_ok.
Let RES_hullH : RES_hull_def SEGS A := RES_hull.

(* [comment removed for export] *)
Let reg_sound' := APS.reg_sound SEGS A LIMIT SINV argH FS0.
Let reg_lit_sound' := APS.reg_lit_sound SEGS A LIMIT SINV argH FS0.
Let kentry_keep_sem' := APS.kentry_keep_sem SEGS.
Let kentry_apart_b_sem' := APS.kentry_apart_b_sem SEGS.
Let regs_ok_set_n' := APS.regs_ok_set_n.
Let in_ivs_map_den' := APS.in_ivs_map_den.
Let kimg_clip_in_hull' := APS.kimg_clip_in_hull A.
Let cs_ok_agree' := APS.cs_ok_agree SEGS A nx0 LIMIT SINV argH argH_agree SINV_agree FS0.
Let cs_ok_frame' := APS.cs_ok_frame SEGS A LIMIT SINV argH SINV_frame FS0.
Let hid_agree' := APS.hid_agree A nx0 argH argH_agree.
Let vis_add_sound' := APS.vis_add_sound SEGS A LIMIT HS XN XE XB SHADOW_ok SINV argH argH_high2 FS0 0%nat.
Let A_wf_allowA' := APS.A_wf_allowA A HS XN XE XB 0%nat.
Let know_ok_unhide' := APS.know_ok_unhide SEGS A.
Let hid_hull' := APS.hid_hull A HULL_ok argH argH_high.
Let H_off_segments_cs' := APS.H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high.
Let maps_match_exact' := APS.maps_match_exact nx0 HS XN XE XB.

(* [comment removed for export] *)
Let budget_slack := AsanNodesMmLib.budget_slack SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let escale_4096_denot := AsanNodesMmLib.escale_4096_denot SEGS A RES_len HULL_ok.
Let find_containing_sound := AsanNodesMmLib.find_containing_sound SEGS A RES_len.
Let fixed_args_sound := AsanNodesMmLib.fixed_args_sound SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let fixed_cs1 := AsanNodesMmLib.fixed_cs1 A.
Let gap_ok_sound := AsanNodesMmLib.gap_ok_sound SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let gap_weight_eq := AsanNodesMmLib.gap_weight_eq SEGS A RES_len.
Let grant_cs1_ok := AsanNodesMmLib.grant_cs1_ok SEGS A LIMIT SINV argH FS0 RES_len HULL_ok argH_high2 SINV_frame.
Let grant_eager_le := AsanNodesMmLib.grant_eager_le SEGS A RES_len HULL_ok.
Let grant_keep_apart := AsanNodesMmLib.grant_keep_apart SEGS A RES_len HULL_ok.
Let grant_new_facts := AsanNodesMmLib.grant_new_facts SEGS A LIMIT SINV argH FS0 RES_len HULL_ok argH_high2.
Let grant_vis_add := AsanNodesMmLib.grant_vis_add SEGS A LIMIT SINV argH FS0 SEGS_in_hull RES_len HULL_ok SHADOW_ok argH_high argH_high2.
Let grant_wf := AsanNodesMmLib.grant_wf SEGS A RES_len.
Let in_allow_ext := AsanNodesMmLib.in_allow_ext A.
Let inside_maps_apart := AsanNodesMmLib.inside_maps_apart SEGS A RES_len HULL_ok.
Let kimg_in_hull_cons2 := AsanNodesMmLib.kimg_in_hull_cons2 A HULL_ok SHADOW_ok.
Let kimg_in_hull_pure := AsanNodesMmLib.kimg_in_hull_pure A.
Let kmem_ok := AsanNodesMmLib.kmem_ok SEGS A RES_len HULL_ok.
Let kn_grant_filter_ok := AsanNodesMmLib.kn_grant_filter_ok SEGS A RES_len HULL_ok.
Let kn_rezero_clip_ok := AsanNodesMmLib.kn_rezero_clip_ok SEGS A RES_len HULL_ok.
Let kn_rezero_hull_ok := AsanNodesMmLib.kn_rezero_hull_ok SEGS A RES_len HULL_ok.
Let kn_rezero_ok_gen := AsanNodesMmLib.kn_rezero_ok_gen SEGS A RES_len HULL_ok.
Let kn_unfill_clip_ok := AsanNodesMmLib.kn_unfill_clip_ok SEGS A RES_len HULL_ok.
Let maps_match_disjoint := AsanNodesMmLib.maps_match_disjoint SEGS A RES_len.
Let mmap_fixed_grant_cs1 := AsanNodesMmLib.mmap_fixed_grant_cs1 SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SHADOW_ok argH_high2 SINV_frame.   (* [comment removed for export] *)
Let mmap_fixed_old_facts := AsanNodesMmLib.mmap_fixed_old_facts SEGS A nx0 LIMIT SINV argH FS0 RES_len RES_hull HULL_ok.
Let mmap_fixed_hole_facts := AsanNodesMmLib.mmap_fixed_hole_facts SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SHADOW_ok.
Let fixed_pre := AsanNodesMmLib.fixed_pre SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let mmap_len_sound := AsanNodesMmLib.mmap_len_sound SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let mmap_null_cs1 := AsanNodesMmLib.mmap_null_cs1 SEGS A nx0 LIMIT SINV argH FS0 RES_len HULL_ok HULL_cov argH_high2 argH_agree SINV_frame SINV_agree.
Let null_cs1 := AsanNodesMmLib.null_cs1 A.
Let overlap_sum_contained := AsanNodesMmLib.overlap_sum_contained SEGS A RES_len HULL_ok.
Let page_aligned_sound := AsanNodesMmLib.page_aligned_sound SEGS A RES_len.
Let refuse_cont := AsanNodesMmLib.refuse_cont SEGS A nx0 LIMIT SINV argH FS0 RES_len SINV_frame.
Let refuse_ok := AsanNodesMmLib.refuse_ok SEGS A LIMIT SINV argH FS0 RES_len SINV_frame.
Let region_free_of_apart := AsanNodesMmLib.region_free_of_apart SEGS A nx0 LIMIT SINV argH FS0 RES_len RES_hull HULL_ok.
Let regs_ok_regupd_same := AsanNodesMmLib.regs_ok_regupd_same SEGS A RES_len.
Let reserved_free_above := AsanNodesMmLib.reserved_free_above SEGS A RES_len RES_hull HULL_ok.
Let safe_range_apart := AsanNodesMmLib.safe_range_apart SEGS A RES_len HULL_ok.
Let seps_map_disjoint := AsanNodesMmLib.seps_map_disjoint SEGS A RES_len.
Let shadow_facts_new_ok := AsanNodesMmLib.shadow_facts_new_ok SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SHADOW_ok.
Let slice_args := AsanNodesMmLib.slice_args SEGS A LIMIT SINV argH FS0 RES_len RES_hull HULL_ok.
Let slice_hyps := AsanNodesMmLib.slice_hyps SEGS A LIMIT SINV argH FS0.
Let split_flat_estart := AsanNodesMmLib.split_flat_estart SEGS A RES_len HULL_ok.
Let vis_add_inv := AsanNodesMmLib.vis_add_inv A LIMIT.
Let vis_add_slice_ok := AsanNodesMmLib.vis_add_slice_ok SEGS A LIMIT SINV argH FS0 SEGS_in_hull RES_len HULL_ok SHADOW_ok argH_high argH_high2.
Let vis_grant_out := AsanNodesMmLib.vis_grant_out SEGS A RES_len.
Let page_base_aligned := AsanNodesMmLib.page_base_aligned SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_MR_out := AsanNodesMmLib.sl_MR_out SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_bounds := AsanNodesMmLib.sl_bounds SEGS A LIMIT SINV argH FS0.
Let sl_eager := AsanNodesMmLib.sl_eager SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_in_maps := AsanNodesMmLib.sl_in_maps SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_lazy_in := AsanNodesMmLib.sl_lazy_in SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_lazy_out := AsanNodesMmLib.sl_lazy_out SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_lohi := AsanNodesMmLib.sl_lohi SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_noacc_in := AsanNodesMmLib.sl_noacc_in SEGS A LIMIT SINV argH FS0 RES_len.
Let sl_noacc_out := AsanNodesMmLib.sl_noacc_out SEGS A LIMIT SINV argH FS0 RES_len.
Let sl_vis_in_E := AsanNodesMmLib.sl_vis_in_E SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_vis_in_F := AsanNodesMmLib.sl_vis_in_F SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_vis_in_G := AsanNodesMmLib.sl_vis_in_G SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_vis_out := AsanNodesMmLib.sl_vis_out SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_wf' := AsanNodesMmLib.sl_wf' SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let slice_cs1_ok := AsanNodesMmLib.slice_cs1_ok SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SHADOW_ok argH_high2 SINV_frame.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mmap_null_sound1 : forall cs kd (eager visible : bool) cs' E R FULL model TB,
  CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
  reg_lit cs 17 = Some 222 -> reg_lit cs 10 = Some 0 ->
  reg_lit cs 12 = Some (if kind_none kd then 0 else 3) ->
  reg_lit cs 13 = Some (if kind_lazy kd then 16418 else 34) ->
  reg_lit cs 14 = Some (two64 - 1) -> reg_lit cs 15 = Some 0 ->
  (kind_none kd || kind_lazy kd = negb eager)%bool -> is_tok_kind kd = false ->
  visible = negb (kind_none kd) ->
  mmap_null A nx0 LIMIT cs kd eager visible = Some cs' ->
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg R' (pc cs') FULL' model') TB) ->
  srealizes SEGS (cfg R (pc cs) FULL model) TB.
Proof.
  intros cs kd eager visible cs' E R FULL model TB HC Hec H17 H10 H12 H13 H14 H15 Hkind Hkfog Hvisible Hn HK.
  destruct (is_ecall_at_sound SEGS cs Hec) as (w & Hf & He & Hp0 & Hp4).
  pose proof Hn as Hn0.
  unfold mmap_null in Hn.
  destruct (mmap_len cs) as [[[ne nlo] nhi]|] eqn:HML; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hnoh].
  apply andb_prop in Hcond as [Hcond Hbud]. apply andb_prop in Hcond as [Hcond Hgap].
  apply andb_prop in Hcond as [Hfresh Hnev].
  destruct (reg_lit_sound' E cs R FULL model 17 222 HC ltac:(lia) H17) as [R17 _].
  destruct (reg_lit_sound' E cs R FULL model 10 0 HC ltac:(lia) H10) as [R10 _].
  destruct (reg_lit_sound' E cs R FULL model 12 _ HC ltac:(lia) H12) as [R12 _].
  destruct (reg_lit_sound' E cs R FULL model 13 _ HC ltac:(lia) H13) as [R13 _].
  destruct (reg_lit_sound' E cs R FULL model 14 _ HC ltac:(lia) H14) as [R14 _].
  destruct (reg_lit_sound' E cs R FULL model 15 0 HC ltac:(lia) H15) as [R15 _].
  rewrite <- bv5_17 in R17. rewrite <- bv5_10 in R10. rewrite <- bv5_12 in R12. rewrite <- bv5_13 in R13.
  rewrite <- bv5_14 in R14. rewrite <- bv5_15 in R15. rewrite (Z_to_bv64_m1 _ eq_refl) in R14.
  destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & Hne & Hnlo & HnZ & HnZal & HneE).
  change (Z_to_bv 5 11) with (Z_to_bv 5 (Z.of_nat 11)) in R11. rewrite <- bv5_11 in R11.
  set (len := bv_unsigned (edenot E (reg cs 11))) in *. set (nZ := page_round_up_Z len) in *.
  set (n := Z_to_bv 64 nZ).
  destruct (gap_ok_sound E cs R FULL model nhi nZ HC Hgap ltac:(lia)) as (a0 & Ha0). rewrite <- R10 in Ha0.
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt.
  pose proof (proj2 (proj2 (proj2 (co_wf _ _ _ _ _ _ _ _ _ _ _ HC)))) as Hisp.
  assert (CONT : forall (a : word) model' FULL',
            grant_ok_na (getr R 10) model a nZ = true ->
            grant_post kd a n model model' -> grant_mem kd a n FULL FULL' -> m_fs model' = m_fs model ->
            srealizes SEGS (mkCfg (mkst (regupd R 10 a) (v_addi (Z_to_bv 64 (pc cs)) 4) FULL' (seg_rom SEGS)) model') TB).
  { intros a model' FULL' Hg GPo GM Hfs. rewrite R10 in Hg.
    destruct (mmap_null_cs1 cs kd eager ne nlo nhi E R FULL model a model' FULL' HC HML Hfresh Hnev
                ltac:(intros ->; cbn in Hbud; unfold budget_ok in Hbud; apply Z.leb_le in Hbud; exact Hbud)
                Hkind Hkfog Hnoh Hg GPo GM) as (HC1 & Hbase & HneE' & Un & Hag0 & NEW).
    fold len nZ n in HC1, HneE', Un, NEW.
    rewrite (v_addi_pc (pc cs) Hp0 Hp4). rewrite bv5_10.
    set (E' := ext1 E (nxt cs) (Z_to_bv 64 (bv_unsigned a / 4096))) in *.
    assert (Hpc : pc cs' = pc cs + 4).
    { destruct visible; [|clear - Hn; apply some_inj12 in Hn; subst cs'; reflexivity].
      destruct (vis_add_inv _ _ _ _ _ Hn) as (nhi2 & _ & ->). reflexivity. }
    specialize (HK E' (regupd R (Z_to_bv 5 (Z.of_nat 10)) a) FULL' model' (conj Hag0 (ext1_agree'' E (nxt cs) (Z_to_bv 64 (bv_unsigned a / 4096))))).
    unfold cfg_of in HK. rewrite Hpc in HK. apply HK; [|exact Hfs].
    destruct visible.
    -
      assert (Hrw : kind_none kd = false) by (destruct kd; cbn in Hvisible |- *; congruence).
      pose proof (u64_range a) as Ra.
      destruct (grant_ok_na_unpack _ _ _ _ Hg) as (_ & _ & Hceil & _). pose proof (alloc_top_lt_2_64 (m_vmmaps model)) as ATL.
      eapply (grant_vis_add E' (null_cs1 cs kd eager ne nlo nhi) cs' _ ne _ FULL' model' a n nZ HC1 Hn).
      + unfold null_cs1, add_entry. cbn [kn a_ss mk_ss s_know]. apply kimg_in_hull_app; [|apply kimg_clip_in_hull'].
        apply kimg_in_hull_pure. apply (proj2 (Forall_app _ _ _)); split; [apply grant_facts_pure | apply kdisj_new_pure].
      + exact Hbase.
      + exact HneE'.
      + exact Un.
      + lia.
      + lia.
      + intros x Hx. destruct (NEW x Hx) as (N1 & N2 & N3 & _). rewrite (gp_noacc _ _ _ _ _ GPo), Hrw. auto.
      + intros x Hx. rewrite (proj2 GM x) by (rewrite Un; exact Hx). rewrite Hrw. reflexivity.
    - clear - Hn HC1. apply some_inj12 in Hn. subst cs'. exact HC1. }
  unfold cfg_of.
  destruct kd; cbn [kind_none kind_lazy negb orb] in *; [| | | | discriminate Hkfog | discriminate Hkfog].
  -
    destruct eager; [|discriminate].
    eapply (srz_mmap_rw1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w len (Z_to_bv 64 34) TB Hf He Hhalt Hisp R17 R11 Hlen R12 R13 mmap_flags_core_22 R14 R15).
    + exists a0. exact Ha0.
    + unfold mmap_noreserve_backed_ok. rewrite mmap_noreserve_b_22.
      apply Z.leb_le. cbn in Hbud. eapply Z.le_trans; [|eapply (budget_slack E cs R FULL model nhi HC Hbud)]. fold nZ. lia.
    + intros a Hg _. rewrite (with_mmap_backing_plain _ _ _ _ mmap_noreserve_b_22). apply (CONT a); [exact Hg | | | reflexivity].
      * constructor; reflexivity.
      * split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
  -
    destruct eager; [discriminate|].
    eapply (srz_mmap_rw1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w len (Z_to_bv 64 16418) TB Hf He Hhalt Hisp R17 R11 Hlen R12 R13 mmap_flags_core_4022 R14 R15).
    + exists a0. exact Ha0.
    + unfold mmap_noreserve_backed_ok. rewrite mmap_noreserve_b_4022. reflexivity.
    + intros a Hg _. rewrite (with_mmap_backing_lazy _ _ _ _ mmap_noreserve_b_4022). apply (CONT a); [exact Hg | | | reflexivity].
      * destruct (grant_ok_na_unpack _ _ _ _ Hg) as (Hal & Hpos & Hceil & _). pose proof (alloc_top_lt_2_64 (m_vmmaps model)) as ATL.
        unfold page_size in Hal.
        constructor; try reflexivity.
        unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing. rewrite lazy_interior_fresh; [reflexivity | exact Hal | | |]; subst n; rewrite u64_lit by lia; [exact HnZal | lia | lia].
      * split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
  -
    destruct eager; [discriminate|].
    eapply (srz_mmap_none1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w len (Z_to_bv 64 34) TB Hf He Hhalt Hisp R17 R11 Hlen R12 R13 mmap_flags_core_22 R14 R15).
    + exists a0. exact Ha0.
    + intros a Hg. rewrite (with_mmap_backing_plain _ _ _ _ mmap_noreserve_b_22). apply (CONT a); [exact Hg | | | reflexivity].
      * constructor; reflexivity.
      * split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
  -
    destruct eager; [discriminate|].
    eapply (srz_mmap_none1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w len (Z_to_bv 64 16418) TB Hf He Hhalt Hisp R17 R11 Hlen R12 R13 mmap_flags_core_4022 R14 R15).
    + exists a0. exact Ha0.
    + intros a Hg. rewrite (with_mmap_backing_lazy _ _ _ _ mmap_noreserve_b_4022). apply (CONT a); [exact Hg | | | reflexivity].
      * destruct (grant_ok_na_unpack _ _ _ _ Hg) as (Hal & Hpos & Hceil & _). pose proof (alloc_top_lt_2_64 (m_vmmaps model)) as ATL.
        unfold page_size in Hal.
        constructor; try reflexivity.
        unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing. rewrite lazy_interior_fresh; [reflexivity | exact Hal | | |]; subst n; rewrite u64_lit by lia; [exact HnZal | lia | lia].
      * split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mmap_fixed_grant_sound1 : forall cs ms0 top b off ne nlo nhi kd (fl : Z) (eager visible : bool) cs' E R FULL model TB,
  CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
  reg_lit cs 17 = Some 222 ->
  reg_lit cs 12 = Some (if kind_none kd then 0 else 3) ->
  reg_lit cs 13 = Some fl ->
  (fl = (if kind_lazy kd then 16434 else 50) \/ (kind_lazy kd = true /\ fl = 0x104022)) ->   (* [comment removed for export] *)
  reg_lit cs 14 = Some (two64 - 1) -> reg_lit cs 15 = Some 0 ->
  (kind_none kd || kind_lazy kd = negb eager)%bool -> is_tok_kind kd = false ->
  visible = eager ->
  fixed_args A cs top = Some (b, off, ne, nlo, nhi) -> top <= CEIL ->
  (negb eager || budget_ok LIMIT cs nhi)%bool = true ->
  CSOK E (with_maps0 cs ms0) R FULL model ->
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) (edenot E (reg cs 10))
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) = true ->
  (forall m, In m ms0 -> is_hole m = true ->
     bv_unsigned (edenot E (reg cs 10)) + page_round_up_Z (bv_unsigned (edenot E (reg cs 11))) <= uE E (am_base m)
     \/ uE E (am_base m) + uE E (am_len m) <= bv_unsigned (edenot E (reg cs 10))) ->
  mmap_fixed_grant A LIMIT cs ms0 b off ne nhi kd eager visible = Some cs' ->
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg R' (pc cs') FULL' model') TB) ->
  srealizes SEGS (cfg R (pc cs) FULL model) TB.
Proof.
  intros cs ms0 top b off ne nlo nhi kd fl eager visible cs' E R FULL model TB HC Hec H17 H12 H13 HFL H14 H15 Hkind Hkfog Hvisible HFA Htop Hbud HC0 Hrf Hholes Hn HK.
  destruct (is_ecall_at_sound SEGS cs Hec) as (w & Hf & He & Hp0 & Hp4).
  assert (Hbudget : eager = true -> a_eager cs + a_abytes cs + nhi <= LIMIT).
  { intros ->. cbn in Hbud. unfold budget_ok in Hbud. apply Z.leb_le in Hbud. exact Hbud. }
  unfold mmap_fixed_grant in Hn.
  destruct (reg_lit_sound' E cs R FULL model 17 222 HC ltac:(lia) H17) as [R17 _].
  destruct (reg_lit_sound' E cs R FULL model 12 _ HC ltac:(lia) H12) as [R12 _].
  destruct (reg_lit_sound' E cs R FULL model 13 _ HC ltac:(lia) H13) as [R13 _].
  destruct (reg_lit_sound' E cs R FULL model 14 _ HC ltac:(lia) H14) as [R14 _].
  destruct (reg_lit_sound' E cs R FULL model 15 0 HC ltac:(lia) H15) as [R15 _].
  rewrite <- bv5_17 in R17. rewrite <- bv5_12 in R12. rewrite <- bv5_13 in R13.
  rewrite <- bv5_14 in R14. rewrite <- bv5_15 in R15. rewrite (Z_to_bv64_m1 _ eq_refl) in R14.
  destruct (fixed_args_sound E cs R FULL model top b off ne nlo nhi HC HFA) as (Hsp & HML & _).
  destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & _).
  change (Z_to_bv 5 11) with (Z_to_bv 5 (Z.of_nat 11)) in R11. rewrite <- bv5_11 in R11.
  set (len := bv_unsigned (edenot E (reg cs 11))) in *. set (nZ := page_round_up_Z len) in *.
  set (n := Z_to_bv 64 nZ) in *. set (addr := edenot E (reg cs 10)) in *.
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt.
  pose proof (proj2 (proj2 (proj2 (co_wf _ _ _ _ _ _ _ _ _ _ _ HC)))) as Hisp.
  destruct (fixed_pre cs top b off ne nlo nhi E R FULL model HC HFA Htop)
    as (HneE & Un & Hest & Hal & Hpos & Himg & HtopA & R10 & HnZal & HnZ).
  fold len nZ n addr in HneE, Un, Hest, Hal, Hpos, Himg, HtopA, R10, HnZal, HnZ.
  assert (HaK : bv_unsigned addr + nZ <= CEIL) by lia.
  rewrite <- bv5_10 in R10.
  assert (Hce : bv_unsigned addr + page_round_up_Z len <= alloc_ceiling) by (rewrite CEIL_eq; fold nZ; lia).
  assert (CONT : forall model' FULL',
            grant_post kd addr n model model' -> grant_mem kd addr n FULL FULL' -> m_fs model' = m_fs model ->
            srealizes SEGS (mkCfg (mkst (regupd R 10 addr) (v_addi (Z_to_bv 64 (pc cs)) 4) FULL' (seg_rom SEGS)) model') TB).
  { intros model' FULL' GPo GM Hfs.
    destruct (mmap_fixed_grant_cs1 cs ms0 kd eager top b off ne nlo nhi E R FULL model model' FULL' HC HFA Htop HC0 Hrf Hholes Hbudget Hkind Hkfog GPo GM) as (HC1 & NEW).
    fold len nZ n addr in HC1, NEW.
    rewrite (v_addi_pc (pc cs) Hp0 Hp4). rewrite bv5_10.
    assert (Hpc : pc cs' = pc cs + 4).
    { destruct visible; [|clear - Hn; apply some_inj12 in Hn; subst cs'; reflexivity].
      destruct (vis_add_inv _ _ _ _ _ Hn) as (nhi2 & _ & ->). reflexivity. }
    specialize (HK E (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr) FULL' model' (conj (env_agree_refl' _ _) (env_agree_refl' _ _))).
    unfold cfg_of in HK. rewrite Hpc in HK. apply HK; [|exact Hfs].
    destruct visible.
    -
      subst eager. assert (Hrw : kind_none kd = false) by (destruct kd; cbn in Hkind |- *; congruence).
      pose proof (u64_range addr) as Ra.
      eapply (vis_add_sound'); [exact Hn | exact HC1 |].
      destruct (vis_add_inv _ _ _ _ _ Hn) as (nhi2 & _ & Ecs2).
      apply Forall_app. split.
      +
        assert (Hfl : flat E (SA b off) (elenZ E ne)) by (unfold flat, elenZ; rewrite Hest, HneE, Un; unfold CEIL in HaK; lia).
        assert (BYTE : forall x : word, bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + nZ ->
                  MR E cs' model' FULL' x = Some (Z_to_bv 8 0)).
        { intros x Hx. destruct (NEW x Hx) as (N1 & N2 & N3).
          unfold Mr, mrestrict, hid. rewrite N3. cbn [orb]. unfold vis. rewrite N1. rewrite (gp_noacc _ _ _ _ _ GPo), Hrw, N2. cbn [negb andb].
          assert (Hallow : in_allow A E cs' (bv_unsigned x) = true).
          { unfold in_allow, in_vis. rewrite Ecs2. cbn [a_vis existsb fst snd with_maps0]. unfold uE. fold addr. rewrite HneE, Un.
            rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
          rewrite Hallow, !orb_true_r. cbn [negb]. rewrite (proj2 GM x) by (rewrite Un; exact Hx). rewrite Hrw. reflexivity. }
        constructor; [|constructor; [|constructor]]; cbn [kentry_ok]; split; try exact Hfl; unfold elenZ; rewrite Hest, HneE, Un.
        * intros d w' Hd Hdw. destruct w' as [|w'']; [reflexivity|].
          apply store_ok_of_all; [rewrite u64_lit by (unfold CEIL in HaK; lia); unfold CEIL in HaK; lia|].
          intros x Hx. rewrite u64_lit in Hx by (unfold CEIL in HaK; lia). unfold wview. rewrite (BYTE x) by lia. discriminate.
        * intros i Hi. apply BYTE. rewrite u64_lit by (unfold CEIL in HaK; lia). lia.
      +
        pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC1) as HK1. unfold Mr in HK1 |- *.
        eapply know_ok_unhide'; [apply H_off_segments_cs' | | | | exact HK1].
        * unfold fixed_cs1, add_entry. cbn [kn a_ss mk_ss s_know with_maps0]. apply kimg_in_hull_app; [|apply kimg_clip_in_hull'].
          destruct kd; cbn [mkind_eqb]; try (apply kimg_in_hull_pure; apply Forall_nil).
          apply kimg_in_hull_pure. apply Forall_flat_map. apply Forall_forall. intros p _. unfold shadow_facts.
          destruct (shadow_of A (kn cs) (fst p) (snd p)) as [[sb sk] sn].
          match goal with |- Forall _ (if ?c then _ else _) => destruct c; [|apply Forall_nil] end.
          apply Forall_cons; [exact I|]. apply Forall_cons; [exact I|]. apply Forall_nil.
        * intros y Hy. rewrite Ecs2 in Hy. eapply hid_cons_sub. exact Hy.
        * intros y Hy. apply hid_hull'. exact Hy.
    - clear - Hn HC1. apply some_inj12 in Hn. subst cs'. exact HC1. }
  unfold cfg_of.
  destruct kd; cbn [kind_none kind_lazy negb orb] in *; [| | | | discriminate Hkfog | discriminate Hkfog].
  -
    destruct eager; [|discriminate]. destruct HFL as [-> | [X _]]; [|discriminate X].
    eapply (srz_mmap_fixed_rw_free1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len (Z_to_bv 64 50) TB
              Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce Hisp R12 R13 fixed_free_core_32 R14 R15 Hrf).
    + unfold mmap_noreserve_backed_ok. rewrite mmap_noreserve_b_32. apply Z.leb_le. cbn in Hbud.
      eapply Z.le_trans; [|eapply (budget_slack E cs R FULL model nhi HC Hbud)]. fold nZ. lia.
    + rewrite with_mmap_backing_plain by apply mmap_noreserve_b_32.
      apply CONT; [constructor; reflexivity | | reflexivity].
      split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
  -
    destruct eager; [discriminate|].
    assert (LAZY : forall flw : word, getr R 13 = flw -> fixed_free_core flw -> mmap_noreserve_b flw = true ->
                     srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)) model) TB).
    { intros flw R13w Hcw Hnrw.
      eapply (srz_mmap_fixed_rw_free1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len flw TB
                Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce Hisp R12 R13w Hcw R14 R15 Hrf).
      + unfold mmap_noreserve_backed_ok. rewrite Hnrw. reflexivity.
      + rewrite with_mmap_backing_lazy by exact Hnrw.
        fold nZ. fold n. apply CONT; [| | reflexivity].
        * constructor; try reflexivity.
          unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing.
          rewrite lazy_interior_fresh; [reflexivity | exact Hal | rewrite Un; exact HnZal | rewrite Un; lia | rewrite Un; unfold CEIL in HaK; lia].
        * split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx]. }
    destruct HFL as [-> | [_ ->]].
    + exact (LAZY _ R13 fixed_free_core_4032 mmap_noreserve_b_4032).
    + exact (LAZY _ R13 fixed_free_core_104022 mmap_noreserve_b_104022).
  -
    destruct eager; [discriminate|]. destruct HFL as [-> | [X _]]; [|discriminate X].
    eapply (srz_mmap_fixed_none_free1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len (Z_to_bv 64 50) TB
              Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce Hisp R12 R13 fixed_free_core_32 R14 R15 Hrf).
    rewrite with_mmap_backing_plain by apply mmap_noreserve_b_32.
      apply CONT; [constructor; reflexivity | | reflexivity].
      split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
  -
    destruct eager; [discriminate|].
    assert (LAZY : forall flw : word, getr R 13 = flw -> fixed_free_core flw -> mmap_noreserve_b flw = true ->
                     srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)) model) TB).
    { intros flw R13w Hcw Hnrw.
      eapply (srz_mmap_fixed_none_free1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len flw TB
                Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce Hisp R12 R13w Hcw R14 R15 Hrf).
      rewrite with_mmap_backing_lazy by exact Hnrw.
      fold nZ. fold n. apply CONT; [| | reflexivity].
      * constructor; try reflexivity.
        unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing.
        rewrite lazy_interior_fresh; [reflexivity | exact Hal | rewrite Un; exact HnZal | rewrite Un; lia | rewrite Un; unfold CEIL in HaK; lia].
      * split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx]. }
    destruct HFL as [-> | [_ ->]].
    + exact (LAZY _ R13 fixed_free_core_4032 mmap_noreserve_b_4032).
    + exact (LAZY _ R13 fixed_free_core_104022 mmap_noreserve_b_104022).
Qed.

Lemma mmap_fixed_free_sound1 : forall cs kd (fl : Z) (eager visible : bool) cs' E R FULL model TB,
  CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
  reg_lit cs 17 = Some 222 ->
  reg_lit cs 12 = Some (if kind_none kd then 0 else 3) ->
  reg_lit cs 13 = Some fl ->
  (fl = (if kind_lazy kd then 16434 else 50) \/ (kind_lazy kd = true /\ fl = 0x104022)) ->   (* [comment removed for export] *)
  reg_lit cs 14 = Some (two64 - 1) -> reg_lit cs 15 = Some 0 ->
  (kind_none kd || kind_lazy kd = negb eager)%bool -> is_tok_kind kd = false ->
  visible = eager ->
  mmap_fixed_free A LIMIT cs kd eager visible = Some cs' ->
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg R' (pc cs') FULL' model') TB) ->
  srealizes SEGS (cfg R (pc cs) FULL model) TB.
Proof.
  intros cs kd fl eager visible cs' E R FULL model TB HC Hec H17 H12 H13 Hfl H14 H15 Hkind Hkfog Hvisible Hn HK.
  unfold mmap_fixed_free in Hn.
  destruct (fixed_args A cs CEIL) as [[[[[b off] ne] nlo] nhi]|] eqn:HFA.
  -
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
    apply andb_prop in Hcond as [Hcond Hav]. apply andb_prop in Hcond as [Hcond Hnev].
    apply andb_prop in Hcond as [Hcond Hbud]. apply andb_prop in Hcond as [Hnf Hall].
    destruct (mmap_fixed_old_facts cs b off ne nlo nhi E R FULL model HC HFA Hnf Hall) as (HC0 & Hrf & Hholes).
    eapply (mmap_fixed_grant_sound1 cs (a_maps cs) CEIL b off ne nlo nhi kd fl eager visible cs' E R FULL model TB
              HC Hec H17 H12 H13 Hfl H14 H15 Hkind Hkfog Hvisible HFA ltac:(lia) Hbud
              HC0 Hrf Hholes Hn HK).
  -
    discriminate.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma node_mprotect_sound1 : forall cs cs' E R FULL model TB,
  CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
  node_mprotect A LIMIT cs = Some cs' ->
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg R' (pc cs') FULL' model') TB) ->
  srealizes SEGS (cfg R (pc cs) FULL model) TB.
Proof.
  intros cs cs' E R FULL model TB HC Hec Hn HK.
  destruct (is_ecall_at_sound SEGS cs Hec) as (w & Hf & He & Hp0 & Hp4).
  rewrite node_mprotect_eq in Hn. unfold node_mprotect_ref in Hn.
  destruct (reg_lit cs 17) as [z17|] eqn:H17; [|discriminate].
  destruct (reg_lit cs 12) as [z12|] eqn:H12.
  2: { repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  destruct (fixed_args A cs TOPMAX) as [[[[[b off] ne] nlo] nhi]|] eqn:HFA.
  2: { repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  assert (Hz : z17 = 226 /\ z12 = 3).
  { repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end; auto. }
  destruct Hz as [-> ->].
  destruct (find_containing (kn cs) (a_maps cs) [KNONE; KNONELAZY] b off ne) as [m|] eqn:Hfind; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond _]. apply andb_prop in Hcond as [Hbud _].
  unfold budget_ok in Hbud. apply Z.leb_le in Hbud.
  destruct (reg_lit_sound' E cs R FULL model 17 226 HC ltac:(lia) H17) as [R17 _].
  destruct (reg_lit_sound' E cs R FULL model 12 3 HC ltac:(lia) H12) as [R12 _].
  rewrite <- bv5_17 in R17. rewrite <- bv5_12 in R12.
  destruct (slice_args E cs R FULL model b off ne nlo nhi _ m HC HFA Hfind)
    as (Hm & [Hkind Hnf] & R10 & R11 & Hlen & Hne & Un & HnZpos & HnZ & HnZal & Hal & Hpos & Himg & Hest & Hin1 & Hin2 & HmC & Hmc & Hrfres & Hov).
  rewrite <- bv5_10 in R10. rewrite <- bv5_11 in R11.
  set (len := bv_unsigned (edenot E (reg cs 11))) in *. set (nZ := page_round_up_Z len) in *.
  set (n := Z_to_bv 64 nZ) in *. set (addr := edenot E (reg cs 10)) in *.
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf.
  pose proof (proj2 (proj2 (proj2 Hwf))) as Hisp.
  pose proof (u64_range addr) as Ra.
  pose proof (co_sp0 _ _ _ _ _ _ _ _ _ _ _ HC) as SP0. unfold CEIL, TOPMAX in SP0.
  assert (Hkind' : am_kind m = KNONE \/ am_kind m = KNONELAZY) by (cbn in Hkind; destruct Hkind as [<-|[<-|[]]]; auto).
  assert (Hna : map_contains (vm_noaccess (m_vmmaps model)) addr n = true).
  { pose proof (proj1 (Forall_forall _ _) (co_none _ _ _ _ _ _ _ _ _ _ _ HC) m Hm Hkind') as X.
    eapply map_contains_intro; [exact X | exact Hin1 | rewrite Un; exact Hin2]. }
  unfold cfg_of.
  eapply (srz_mprotect1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len TB Hf He Hhalt R17 R10 Hal R11 ltac:(lia)).
  - unfold two_pow_64. fold nZ. lia.
  - exact R12.
  - exact Hna.
  - exact Hmc.
  - apply mprotect_budget_ok_intro_gen; [exact Hwf|]. pose proof (budget_slack E cs R FULL model nhi HC ltac:(unfold budget_ok; apply Z.leb_le; exact Hbud)). fold nZ n. lia.
  - fold nZ. fold n.
    set (model' := mprotect_model addr n model). set (FULL' := zfill addr n FULL).
    assert (SPo : slice_post SlM addr n model model') by (constructor; reflexivity).
    assert (SM : slice_mem SlM addr n FULL FULL').
    { split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx]. }
    assert (SH : slice_hyps E cs R FULL model SlM m addr n nZ model' FULL').
    { constructor; try assumption; intros HH; [discriminate HH|]. intros Hk. rewrite Hk in Hkind'. destruct Hkind'; discriminate. }
    rewrite (v_addi_pc (pc cs) Hp0 Hp4).
    destruct (vis_add_inv _ _ _ _ _ Hn) as (nhi2 & _ & Ecs').
    assert (Hpc : pc cs' = pc cs + 4) by (rewrite Ecs'; reflexivity).
    specialize (HK E (regupd R (Z_to_bv 5 (Z.of_nat 10)) (Z_to_bv 64 0)) FULL' model' (conj (env_agree_refl' _ _) (env_agree_refl' _ _))).
    unfold cfg_of in HK. rewrite Hpc, <- bv5_10 in HK. apply HK; [|reflexivity]. clear HK.
    assert (Hregs' : regs_ok E (sr_upd (s_regs (a_ss cs)) 10 (ELit 0)) (regupd R (Z_to_bv 5 (Z.of_nat 10)) (Z_to_bv 64 0))).
    { apply regs_ok_set_n'; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) | lia | reflexivity]. }
    assert (MROUT := fun x => sl_MR_out E cs R FULL model SlM m addr n nZ model' FULL' SH cs x eq_refl).
    assert (MROUT' : forall x : word, bv_unsigned x < estart E (SA b off) \/ estart E (SA b off) + elenZ E ne <= bv_unsigned x ->
                      MR E cs model' FULL' x = MR E cs model FULL x).
    { intros x Hx. apply MROUT. rewrite Hest in Hx. unfold elenZ in Hx. rewrite Hne, Un in Hx. exact Hx. }
    assert (Hk' : know_ok SEGS E (MR E cs model' FULL') (kimg_clip A (kn_unfill (kn cs) b off ne))).
    { eapply kn_unfill_clip_ok; [exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | rewrite Hest; unfold elenZ; rewrite Hne, Un; exact Himg | exact MROUT']. }
    pose proof (slice_cs1_ok E cs R FULL model SlM m addr n nZ model' FULL' SH _ _ _ (pc cs + 4) (s_next (a_ss cs)) nhi Hregs' Hk' HnZ ltac:(intros _; exact Hbud)) as HC1.
    cbn [sl_charge] in HC1.
    eapply (vis_add_slice_ok E _ cs' (reg cs 10) b off ne _ FULL' model' (bv_unsigned addr) nZ HC1).
    + exact Hn.
    + cbn [kn a_ss s_know mk_ss]. apply kimg_clip_in_hull'.
    + reflexivity.
    + exact Hest.
    + unfold elenZ. rewrite Hne. exact Un.
    + lia.
    + lia.
    + unfold TOPMAX; lia.
    + intros x Hx. rewrite (sp_maps _ _ _ _ _ SPo).
      split; [exact (sl_in_maps E cs R FULL model SlM m addr n nZ model' FULL' SH x Hx) |].
      split; [exact (sl_noacc_in E cs R FULL model SlM m addr n nZ model' FULL' SH x Hx) |].
      split; [destruct (argH E x) eqn:Ea; [pose proof (argH_high2 _ _ _ (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) Ea); lia | reflexivity]|].
      rewrite (proj2 SM x) by (rewrite Un; exact Hx). reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mmap_gate_sound : forall cs prot flags isnull,
  mmap_gate cs = Some (prot, flags, isnull) ->
  reg_lit cs 17 = Some 222 /\ reg_lit cs 12 = Some prot /\ reg_lit cs 13 = Some flags
  /\ reg_lit cs 14 = Some (two64 - 1) /\ reg_lit cs 15 = Some 0
  /\ (isnull = true -> reg_lit cs 10 = Some 0).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmA ()) ["Nodes"] "p'0h02Hgh13H17h21Hh32p0i002p0h41pi011ph53H15h61oi021oh73H14h83Hm1h91ei031eh:3H12h;3H13h<1ni041nh=2H0h>1bi051bh?7defaulth@5flagsi065flagshA6isnullhB1li071lhC1mi081mhD2m1i092m1hE3p10hF4proti0:4prothG1zi0;1zhH3z15hI3z17hJ2HzhK2cshL1fi0<1ai0=8a_abytesi0>5a_brki0?7a_eageri0@4a_fdi0A7a_ghosti0B6a_mapsi0C4a_ssi0D8a_tidseti0E7a_totszi0F5a_visi0G5a_yloi0H2e0i0I1ii0J1ki0K2l'i0L2loi0M3nthi0N2opi0O2p1i0P2p2i0Q2p3i0R2p4i0S2p5i0T2p6i0U2p7i0V1si0W6s_knowi0X5s_logi0Y6s_nexti0Z4s_pci0[6s_regsi0\6s_resvi0]2sxi0^1xi0_2z0p%0p%1p%2p%3p;2p;1p;3p;4p;6p;7p;8g00IaS00j2gTg000jR0j1jTg055gj1lTg00:Rj1`Tg01PLj21Tg00JAj2NTg00P`j1eTg00;1j1CTg00=Oj2kTg001nj30Tg006@j1:Tg005[j1;Tg001Lj2ETg056dj2XTg00>Ij1\Tg00UOS01j22Tg01QGj2FTg00QBj4QTg01NAj4]Tg00gQj1dTg057Aj2qTg00`hS02j1pTg04RZj1oTg00_Nj2nTg000Mj6cTg00i2j6_Tg003Yj7mj8fTf6R1f5R2f4R3f3R4g02Z^R5g02[^R6P6f2R7f1R8CQf0R9CQ'E30p=H%`9#`p=Z1178=049p=51X89#\p=>P6P6P8P9CQp=aP7P5P8P9CQ,E4p=iP4P5P6P6P7P8CQP9CQ,E3p=3%:9#:p=I%:9#:#;#Cp=T1E69p=4g02[>R:9059p=81147=038/29p=7A0478/29p=@A0123A0478/29'2p=DA0478/29,23p=?A0478/29,23,22p=bg02]UR;9069p=BA0678/29p=JP3P4P7g02d4S03P8P9E_p=91278/F9p=6%C9,E6p==A0647A068;'2/F9p=S%;9#Cp=R%:9#;p=[A0647/28/F9p=OA0689p=GA068;,27/F9p=h1289,27p=V1E68=079p=<A03471289'2,22,21p=WA03471289'2p=L1278,24,23/F9p=A1E699078p=P1E689047/29p=^A0347/28,22/F9p=M1289,27,24p=YA0347/28,22,21/F9p=Uf7R<?0121147=038/29'2p=Kg02\\S041g66R=/g5R>#jR?%l4P>P=P7P8P9FHg02_2#Z#Z#Z#Z#ZR@#ZS05#`RA#`RB#`RC#ZRD,13%j6RE1NE9RFPEP2PDP9C5P0P6PEP<PDP9C5P0P6P?P8P6P?P9%e>RGg051ORHP?P9PGPHP?P9PHP?P9PHP?P9PHP?P9PHP?P9PGPHP?P9PHP?P9PGPGP0P6P?fARIQ05'1P0P6P?fBRJ/1AS06P0P6P?fCRK/1BS07P0P6P?fDRL/1CP6P?P9P5P?g02c8S08g02kZS09#CS0:'kRM,>8RNPGP>P=1a47ROP0P6P5fERP/1@P6P5P9P:g02\<RQPQn0110;0003001010110101RRPQn10110^00021010;00Cin0100000020000PGPGn0110_0003001010U1010UPGn10110^00021010_00PGn10110^00021010900PGn10110^00021010600PGn10110^00021010:00n0110T00031010U1010U01PGPGn0110S00031110T1010T00PGn0110R00031010S1110S00PGPGn0110Q00031110R1010R00PGPGn0110P00031110Q1010Q00PGPGn0110O00031110P1010P00PGPGn0110000031110O1010O00PGn011010003101001110000RSPGn0110;0003001110110101PGn10110^00021110;00P>P=P<P1P2D3S0;50?PEP7Q09#:S0<#;S0=#I#TRT#4RUPEf9RVQ05f8S0>#4PEPVPA%4<RWPEPVPB%4MRXPEPVPC1E6;RY%81PEf:S0?P@PYC5[D7D7D7D7S0@C@]0]1P8PEQ0>PD%49RZC5P?P6P?P8PGPSPGn0110;0003001110110101P>P=Q0>P<P1FHQ0?Q05'1PEPFPEf;S0AQ05P9C5P0P6PEf=S0BQ05P9C5P?P6P?P1PGPHP?P9PGPHP?P9PHP?P9PHP?P9PHP?P9PHP?P9PGPHP?P9PHP?P9PGPGP0P6P?PVP0P6P?fGRS/1AS0CP0P6P?fHR[/1BS0DP0P6P?fIR\/1CS0EP6P?P9P5P?PNPGP>P=POP0P6P5fJRO/1@S0FPRPQn10110^00021010;00R]Cin0100000020000PGPGn0110_0003001010U1010UPGn10110^00021010_00PGn10110^00021010900PGn10110^00021010600PGn10110^00021010:00n0110T00031010U1010U00PGPGn0110S00031110T1010T00PGn0110R00031010S1110S00PGPGn0110Q00031110R1010R00PGPGn0110P00031110Q1010Q00PGPGn0110O00031110P1010P00PGPGn0110000031110O1010O00PGn011010003101001110000PGn0110;0003001110110101P>P=Q0Bf<S0GQ0AFHPEPWPUPEP7f>S0H#4PEf?S0IPAQ0B#4S0JPEQ0IPBPXPEQ0IPCPYQ0G#8PEf@R^P@PYC5[D7D7D7FD]0]:P8PEQ0HQ05PZC5P6P?P<PGPHP?P9PGPHP?P9PHP?P9PHP?P9PHP?P9PHP?P9PGPHP?P9PHP?P9PGPGP0P6P?Q0CP0P6P?Q0DP0P6P?Q0EP6P?P9P5P?PNPGP>P=Q0GP7P]D3n0100000020000PGPGn0110_0003001010U1010UPGn10110^00021010_00PGn10110^00021010900PGn10110^00021010600n0110T00031010U1010U00PGPGn0110S00031010T1010T00PGn0110R00031010S1110S00PGPGn0110Q00031110R1010R00PGPGn0110P00031110Q1010Q00PGPGn0110O00031110P1010P00PGPGn0110000031110O1010O00PGn011010003101001110000PGn0110;0003001110110101P>P=Q0HQ0BQ0GD3S0K50?11^APEPF11IAS0L=0E9P0P611KAS0M=0E9P6P?Q0GPGPHP?P9PGPHP?P9PHP?P9PHP?P9PHP?P9PHP?P9PGPHP?P9PHP?P9PGPGP0P6P?PVP0P6P?fMR]/1BS0NP0P6P?fNR_/1CS0OP6P?P9P5P?PNPGP>P=PIP7P0P6P5fOR`/1@PRPQn10110^00021010;00RaD3n0100000020000PGPGn0110_0003001010U1010UPGn10110^00021010_00PGn10110^00021010900PGn10110^00021010600n0110T00031010U1010U00PGPGn0110S00031010T1010T00PGn0110R00031010S1010S00PGPGn0110Q00031110R1010R00PGPGn0110P00031110Q1010Q00PGPGn0110O00031110P1010P00PGPGn0110000031110O1010O00PGn011010003101001110000PGn0110;0003001110110101P>P=PKPJPID3S0P50?PEQ0JPUPEPW%4LS0QPEP7%4KS0RPEPPPBPXPEPPPCPY%8JPEfFRbP@PYC5[D7D7S0SC@FD]0];P8PEPLPAPZC5P6P?Q0BPGPHP?P9PGPHP?P9PHP?P9PHP?P9PHP?P9PHP?P9PGPHP?P9PHP?P9PGPGP0P6P?Q0NP0P6P?Q0OP6P?P9P5P?PNPGP>P=PIQ0APaD3n0100000020000PGPGn0110_0003001010U1010UPGn10110^00021010_00PGn10110^00021010900n0110T00031010U1010U00PGPGn0110S00031010T1010T00PGn0110R00031010S1010S00PGPGn0110Q00031110R1010R00PGPGn0110P00031110Q1010Q00PGPGn0110O00031110P1010P00PGPGn0110000031110O1010O00PGn011010003101001110000PGn0110;0003001110110101P>P=PLPKPJD3S0T50?11bBPEPF11SBS0U=0E9P0P611\BS0V=0E9P6P?PJPGPHP?P9PGPHP?P9PHP?P9PHP?P9PHP?P9PHP?P9PGPHP?P9PHP?P9PGPGP0P6P?PVP0P6P?fSRa/1CS0WP6P?P9P5P?PNPGP>P=PbP^P0P6P5fTRN/1@S0XPRPQn10110^00021010;00D3Rcn0100000020000PGPGn0110_0003001010U1010UPGn10110^00021010_00PGn10110^00021010900n0110T00031010U1010U00PGPGn0110S00031010T1010T00PGn0110R00031010S1010S00PGPGn0110Q00031010R1010R00PGPGn0110P00031110Q1010Q00PGPGn0110O00031110P1010P00PGPGn0110000031110O1010O00PGn011010003101001110000PGn0110;0003001110110101P>P=P\P[PSD3S0Y50?PEQ0RPUQ0J%4OS0Z50ES0[PEPW%4\S0\PEP7PXPEfKRdPCPY%8[PEfLReP@PYC5[D7S0]C@D?C@]0]7P8PEPOPBPZC5P6P?PKPGPHP?P9PGPHP?P9PHP?P9PHP?P9PHP?P9PHP?P9PGPHP?P9PHP?P9PGPGP0P6P?Q0WP6P?P9P5P?Q0?/>MPGPcn0100000020000PGPGn0110_0003001010U1010UPGn10110^00021010_00n0110T00031010U1010U00PGPGn0110S00031010T1010T00PGn0110R00031010S1010S00PGPGn0110Q00031010R1010R00PGPGn0110P00031010Q1010Q00PGPGn0110O00031110P1010P00PGPGn0110000031110O1010O00PGn011010003101001110000PGn0110;0003001110110101P>P=POP\P[D3S0^50?11eCPEPF11]CS0_=0E9P0P611`CS0`=0E9P6P?P[PGPHP?P9PGPHP?P9PHP?P9PHP?P9PHP?P9PHP?P9PGPHP?P9PHP?P9PGPGP0P6P?PVP6P?P9P5P?Q0I/>MPGP>P=PdPPP0P6P5fYRF/1@PRPQn10110^00021010;00D3n0100000020000RcPGPGn0110_0003001010U1010UPGn10110^00021010_00n0110T00031010U1010U00PGPGn0110S00031010T1010T00PGn0110R00031010S1010S00PGPGn0110Q00031010R1010R00PGPGn0110P00031010Q1010Q00PGPGn0110O00031010P1010P00PGPGn0110000031110O1010O00PGn011010003101001110000PGn0110;0003001110110101P>P=P`P_P]D3S0a50?PEQ0\PUQ0RfPS0b#4S0c50ES0dQ0J%4`S0e50ES0fPEPWPXPEP7PY%8_PEfRS0gP@PYC5[S0hC@EbC@]0]5P8PEQ0bPCPZC5P6P?P\PGPHP?P9PGPHP?P9PHP?P9PHP?P9PHP?P9PHP?P9PGPHP?P9PHP?P9PGPGP6P?PVPcPGPGn0110_0003001010U1010Un0110T00031010U1010U00PGPGn0110S00031010T1010T00PGn0110R00031010S1010S00PGPGn0110Q00031010R1010R00PGPGn0110P00031010Q1010Q00PGPGn0110O00031010P1010P00PGPGn0110000031010O1010O00PGn011010003101001110000PGn0110;0003001110110101P>P=Q0bP`P_D3S0i50?P611aDS0j=0EZP6P?P8PGPHP?P9PGPHP?P9PHP?P9PHP?P9PHP?P9PHP?P9PGPHP?P9PHP?P9PGPGP6P?Q0GP5P?1XJMS0k#\PGP>P=P_P[P0P6P5f\S0l/1@S0mPRPQn10110^00021010;00D3n0100000020000PGPGn0110_0003001010U1010Un0110T00031010U1010U00PGPGn0110S00031010T1010T00PGn0110R00031010S1010S00PGPGn0110Q00031010R1010R00PGPGn0110P00031010Q1010Q00PGPGn0110O00031010P1010P00PGPGn0110000031010O1010O00RcPGn011010003101001110000PGn0110;0003001110110101P>P=PaQ0gfQRWD3S0n50?%B2Rf9J7T]0]1POQ0g/1DS0o=0EYP>P=Q0gPWQ0bD3S0p90?GS0qP?PGP0P>p-0S0rP9g039ARgg02iGS0sn10110200021000000X9?RhQ0nP9D9S0tPgA06;T?6f9b2W0W111NDRf%=9Ri50EPHP?P8PGPcPGn011010003101001110000P>P=PNPaQ0gD3S0u50?PHfWRc/1DS0v=0EiPHP?P8PGPHP?P9PHP?P9PHP?P9PHP?P9PHP?P9PGPHP?P9PHP?P9PGPGP6P?Q0IP5P?1>PMPGP>P=PWPdP0P6P5f_Rj/1@PRPQn10110^00021010;00D3S0wn0100000020000PGPGn0110_0003001010U1010Un0110T00031010U1010U00PGPGn0110S00031010T1010T00PGn0110R00031010S1010S00PGPGn0110Q00031010R1010R00PGPGn0110P00031010Q1010Q00PGPGn0110O00031010P1010P00RkPGPGn0110000031010O1010O00PGn011010003101001110000P>P=PcfVS0xfURlD3S0y50?%C7S0z%BVS0{7JT]0]1P7fXS0|/1DRm%:9Rn#=S0}50EP>P=Q0|PcQ0xD3S0~90?GS10P?PGPhP>P=PFQ0|PcD3S11P9D9S12Pg%:4S13#CS14PTQ0AP9CSb2W0W1X3HP9O1%;9S15#=Ro90EmPHP?P8PkPGPGn0110000031010O1010O00Q0~50?PHf[S16/1DS17=0EoPHP?P8PHP?P9PHP?P9PHP?P9PHP?P9PGPHP?P9PHP?P9PGPGP6P?PJP5P?1>[MPGP>P=PNP_P0P6P5fbS18/1@S19PRPQn10110^00021010;00S1:D3S1;n0100000020000PGPGn0110_0003001010U1010Un0110T00031010U1010U00PGPGn0110S00031010T1010T00PGn0110R00031010S1010S00PGPGn0110Q00031010R1010R00PGPGn0110P00031010Q1010Q00RkPGPGn0110O00031010P1010P00PGPGn0110000031010O1010O00P>P=Q16fZRpPFD3S1<50?%;7S1=#CS1>Q0B#BS1?7JT]0]1P7Q0l/1DRq%;nS1@#=Rr50EPHP?P8PkPGPGn0110O00031010P1010P00P>P=Q0lQ16PpD3S1A50?PH11jDS1B=0ErPHP?P8PHP?P9PHP?P9PHP?P9PGPHP?P9PHP?P9PGPGP6P?PPP5P?1>dMPGP>P=PcPWP0P6P5feRk/1@PRPQn10110^00021010;00D3n0100000020000PGPGn0110_0003001010U1010Un0110T00031010U1010U00PGPGn0110S00031010T1010T00PGn0110R00031010S1010S00PGPGn0110Q00031010R1010R00RsPGPGn0110P00031010Q1010Q00PGPGn0110O00031010P1010P00P>P=Pjf^S1Cf]RtD3S1D50?%:7Ru#;Rv#CS1E%BIS1F7JT]0]1P7f`S1G/1DRw%:nRn#;S1H#=Rx50EPHP?P8PsPGPGn0110P00031010Q1010Q00P>P=Q1GPjQ1CD3S1I50?PHfcRs/1DS1J=0ExPHP?P8PHP?P9PHP?P9PGPHP?P9PHP?P9PGPGP6P?P[P5P?1>_MPGP>P=PpPNP0P6P5fhRy/1@S1KPRPQn10110^00021010;00S1LD3n0100000020000PGPGn0110_0003001010U1010Un0110T00031010U1010U00PGPGn0110S00031010T1010T00PGn0110R00031010S1010S00RzPGPGn0110Q00031010R1010R00PGPGn0110P00031010Q1010Q00P>P=PsQ18faR{D3S1M50?%:uRu#RS1N%BPS1O7JT]0]1P7fdR|/1DS1P%:nRn#;#=R}50EPHP?P8PzPGPGn0110Q00031010R1010R00P>P=P|PsQ18D3S1Q50?PHfgS1R/1DS1S=0E}PHP?P8PHP?P9PGPHP?P9PHP?P9PGPGP6P?PdP5P?1>WMPGP>P=PtPcP0P6P5fkS1T/1@PRPQn10110^00021010;00D3n0100000020000PGPGn0110_0003001010U1010Un0110T00031010U1010U00PGPGn0110S00031010T1010T00RzPGn0110R00031010S1010S00PGPGn0110Q00031010R1010R00P>P=Q1RffS1UPkD3S1V50?%:uRu#RS1W%B\S1X7JT]0]1P711yDS1Y%:nRn#;#=R~50EPHP?P8PGPzPGn0110R00031010S1010S00P>P=PyQ1RQ1UD3S1Z50?PHQ1T/1DS1[=0E~PHP?P8PGPHP?P9PHP?P9PGPGP6P?P_P5P?1>NMPGP>P=Q1GPpP0P6P5fnS1\/1@S1]PRPQn10110^00021010;00D3n0100000020000PGPGn0110_0003001010U1010Un0110T00031010U1010U00S1^PGPGn0110S00031010T1010T00PGn0110R00031010S1010S00P>P=Q1TfjRzfiS1_D3S1`50?%:u#RS1a%B]S1b7JT]0]1P7flS1c/1DS1d%[n#=S1e50EP>P=Q1cQ1TPzD3Rn90?GS1fP?PGPhP>P=fmS1gQ1cQ1TD3S1hP9D9S1iPgQ13#:S13#:#TS1jPTP`P9CSb2W0W1X3HP9O1Q1dQ15#:S1k#:S1l#:S1m#[#=Ru50EPHP?P8Q1^PGPGn0110S00031010T1010T00=0?nPHPEfoS1^PDPuC5PHP?P8PHP?P9PGPGP6P?PWP5P?1>cMPGP>P=PsPtP0P6P5fqS1n/1@PRPQn10110^00021010;00D3n0100000020000PGPGn0110_0003001010U1010US1on0110T00031010U1010U00PGPGn0110S00031010T1010T00P>P=Q1^Q1\Q1gD3S1p50?Q1=#I#TS1=%BWS1q7JT]0]1P7fpS1r/1DS1sQ1@#:#I#[#=Rn50EPHP?P8PGPGQ1on0110T00031010U1010U00P>P=Q1rQ1^Q1\D3S1o50?PHPEfsS1@PDPnC5PHP?P8PGPGP6P?PNP5P?1>pMPGP>P=Q1UQ1GP0P6P5ftS1t/1@S1uPRPQn10110^00021010;00D3n0100000020000PGPGn0110_0003001010U1010Un0110T00031010U1010U00P>P=Q1@frS1vQ1nD3S1w50?%Iv#TS1x%Bl7JT]0]1P7Q1t/1DRvQ1H#:#I#[#=S1H50EP>P=Q1tQ1@Q1vD3S1y90?GS1zP?PGPhP>P=fuS1{Q1tQ1@D3S1|P9D9S1}PgQ13#;#I#TS13PT%BcS1~P9COb2W0W1X3HP9O1Q1k#;S1k#:#I#[#=S2090EvQ1zQ1}Pg%;4S1}#:S21#;S22#I#TS23PTQ1~P9COb2W0W1X3HP9O1Q1v/1DS1z=0EUP6P?PaP5P?1>FMPGP>P=PkPjP0P6P5Q1@/1@PRPQn10110^00021010;00D3n0100000020000PGPGn0110_0003001010U1010UP>P=Q1vQ1nQ1rD3S1~50?P6PEQ1{PCPZC5P6P?P8P5P?Q0l/>MS24PGP>P=PyQ18P0P6P5fvS25/1@S26PRPQn10110^00021010;00D3n0100000020000PGPGn0110_0003001010U1010UQ1|50?1GTTRv%B7S1|'2]0]5PNPEQ1tPCPYC5P5P?Q16/>MPGP>P=Q1RP{P0P6P5Q1{/1@PRPQn10110^00021010;00D3n0100000020000Q1y50?Q24P5P5P5P?P9PGP>P=PzP|P0P6P5fxS24/1@S1yPRPQn10110^00021010;00D3n0100000020000P>P=fwS27Q25Q1{D3S2850?A06;;S29,2vS2:]0P9P>P=Q25Q1{Q1tD3S1{90?GS2;P?PGPhQ28P9D9S28PgQ2:/F9b2W0P>P=Q1_PsP0P6P5Q27/1@PRPQn10110^00021010;00D3Q1{50?Q1yPEP0P6P?P>P=Q1cQ1UP0P6P5P9PRPQn10110^00021010;00S1yD3P>P=fyS1{Q24Q27FHQ2:]0P9P?P>P=Q1gQ1RPRD3P>P=fzS2<Q1{Q24FHP6P?P>P=Q1^Q1_PRD3P>P=f|S2=f{S2>Q2<FHQ2:]0P8P?P=P5Q1\/ayP:CQ,E>P>P=Q2>Q2<Q1{FHPvQ291N6T1N6;C]S29W0P?P=P5Q1r/azPQCQ,E>P>P=f}Q2=Q2>FHQ29W0X3HP9O1S2>Q2>n0110;0003001010110101P9O1W0XG6P9O1P?P=P5Q1T/akPQCQ,E>P>P=Q24Q27Q25FHQ29W0n10110200021110;00P8O1b6W0n0110500020001P8O1b>W0W5Q25/1CS25=0EiQ2;Q28Pg%C4=hv9b2W0W5X3HP9O1Q25%d9#4S2950EQ2;Q28Pg%d4S28=hv9b2W0W5X3HP9O1n0110;0003011010110101PaP9O2W0W1n011010003101011010101P8P9O2W0W1X3HP9O1Q1sQ15#;S15#:#I#[#=S2;50EQ1o90?GS1oP?PGPhP>P=Q1nQ1rQ1^D3S25P9D9S27PgQ1}#;S1}#I#TS24PTPaP9CSb2W0W1X3HP9O1Q1\/1DS2>Q09#;S09#I#TRv#4S2=50EP>P=Q1\Q1gQ1cD3S1{90?GS2<P?PGPhQ1pP9D9S1pPgPvPTQ1qP9COb2W0W1n011010103111011010100P8P9O2W0W1X3HP9O111zDS1qQ0<#:S0<#:S2:#:#RRv#4S2?50EP>P=PzQ1_PyD3S2@90?GS2AP?PGPhQ1`P9D9S2BPgPvPTQ1bP9COb2W0W1n011010103101011110100P8P9O2W0W1X3HP9O1Q1YQ1m#;#=S1m50EQ1Z90?GS1bP?PGPhP>P=Q1_PyQ1RD3S2CP9D9S2DPgQ21#:Rv#:#RS21PTPdP9CSb2W0W1X3HP9O1Q1U/1DS2EQ2:#RS2:#4S2F50EP>P=Q1UPkP|D3S2G90?GS2HP?PGPhQ1VP9D9S2IPgQ2:PTQ1XP9COb2W0W1n011010103111011010100P8P9O2W0W1X3HP9O1Q1PQ1l#;#=S1l50EQ1Q90?GS1XP?PGPhP>P=PkP|PsD3S2:P9D9S2JPg%RvS2KPTPSP9CSb2W0W1X3HP9O1Q18/1DS2LQ0<#RRv#4S0<50EP>P=Q18P{Q1GD3S2M90?GS2NP?PGPhQ1MP9D9S2OPgPvPTQ1OP9COb2W0W1n011010103111011010100P8P9O2W0W1X3HP9O1Q1k#=S1k90EwQ1I90?GS1OP?PGPhP>P=P{Q1GPjD3S2PP9D9S2QPgQ22#CS22PTPKP9CSb2W0W1X3HP9O1Q1C/1DS2RQ0=#CRv#4S0=50EP>P=Q1CPtQ0lD3S2S90?GS2TP?PGPhQ1DP9D9S2UPgPvPTQ1FP9COb2W0W1n011010103111011010100P8P9O2W0W1X3HP9O1Q15#=S1590EqQ1A90?GS1FP?PGPhP>P=PtQ0lQ16D3S2VP9D9S2WPgQ1}#CS1}PTQ0IP9CSb2W0W1X3HP9O111pDS2XQ09#CRv#4S0950EP>P=PpPFQ0|D3S2Y90?GS2ZP?PGPhQ1<P9D9S2[PgPvPTQ1?P9COb2W0W1n011010103111011010100P8P9O2W0W1X3HP9O1Q0x/1DRvQ0:#4S1?50EP>P=Q0xPlPND3S2\90?GS2]P?PGPhQ0yP9D9S2^PgQ0:PTQ0{P9COb2W0W1n011010103101011110100P8P9O2W0W1X3HP9O1Q2990EfQ0u90?GS0:P?PGPhP>P=PlPNPaD3S2_P9D9S2`PgQ28PTP<P9CSb2W0W1X3HP9O1n0110;0103001110110101P\P9O2Q1|9JOTQ011GdT%B4PE%4eS1|PUPE%4bS2a%4aS2bPE%4^S2cQ0g#4S2dPEQ0?#4S2ePXPE%43PY%8WPEPlP@PYC5[C@FDFDP91G]TP6PTQ0v=0EZP6P?P8PGPHP?P9PGPHP?P9PHP?P9PHP?P9PHP?P9PHP?P9PGPHP?P9PHP?P9PGPGP6P?P^P5P?1>bMPGP>P=Q0gPeP0P6P5Q1G/1@S2fPRPQn10110^00021010;00D3n0100000020000PGPGn0110_0003001010U1010Un0110T00031010U1010U00PGPGn0110S00031010T1010T00PGn0110R00031010S1010S00PGPGn0110Q00031010R1010R00PGPGn0110P00031010Q1010Q00PGPGn0110O00031010P1010P00PGPGn0110000031010O1010O00PGn011010003101001110000PGn0110;0003001110110101Q0y50?Q0{PE%44PUPEQ1|%4FS2gPEQ2aQ0|#4S2hPEQ2cPXPEQ2ePY%8cQ16/1@RT=0EY[C@FDFD[]0]1XI6A0EvUP6P?P<P5P?Q0B/>MPGP>P=P\PKP0P6P511c@PRPQn10110^00021010;00D3n0100000020000PGPGn0110_0003001010U1010UQ2\50?Q0>#BP6P;PEPpPCPZC5P6P?P8P5P?1XIMS0{#\PGP>P=P]PSP0P6P5PTPRPQn10110^00021010;00D3n0100000020000PGPGn0110_0003001010U1010UQ2Y50?A0EUURTPE%4_S2eQ16#4R<PE%4[S2i%4pS2jPE%4JS2kPXPE%47S2lPY%8FPEPtP@PYC5[C@FDD?]0]5XH6PEPFPCPYC5S2mP5P?1>^MPGP>P=PePbP0P6P511p@S2nPRPQn10110^00021010;00D3n0100000020000Q1150?Q0{P51N59Q0k=059P51XLM=059P5P?%\8PGQ0wn0100000020000Q2S50?PTPEQ2d%4jS0kPEQ1|Q1C#4S0{PEQ2aPXA0EYYS2o%8tPEP{P@PYC5['2FDD?S2p]0]8P81XKMS2q#8P5P?%\:PGP>P=Q0bPOP0P6P5Q1C/1@S2rPRPQn10110^00021010;00D3S2sn0100000020000Q2V50?Q011X89#81G78[S011G891X78#8S2t[Q2t1G47[1q89P8n2001000000120000000XC6X<6Q01^C6^<6P9PbPMP7O31GbMP6PMPEQ18PBPZC5%4lS01Q18#4S2t50ES2uQ0e%4{S2v50ES2wPE%48S2xPXQ2oQ1G#811|@S2y=0EY[S2z'2D?5VT]7XD6PEP{PBPXC5S2{P?P5P0P>P5P9Q00P=P5P5P9P9n2001101000120101105P0P6P5g02gRRMPEg02_QS2|%pMS2}PM^?M]B]<Q2|Q2}Q2|PMP7Q02PMPMP8P9P8n1011070002002010^10KQ02PMPMP7P8P1P7P9P4O3n1011070002002010^10Kn0110400020010108X?MWBW<p?100110MP@g057aRMQ2}Q04PMPsQ0?n0110<0001;010C10B10E10G10?10F10A10=10>10@10DP3n0110V00016010Z10[10X10W10Y10\%o;O3Q08,n9#4%e6R;P;P;P;P;P;P;n0110300081010;101043010N10<1053010N10<1053010N10<1053010N10<1054010]10L10410H4010]10J10I104PRPQn10110^00021010;00n10110200021010100X9?Q1;Q2PP4EcQ1:=05jP?P6P0P>P6P9Q00P=P5P6P9Q00P6P6P6P8P9n200110100012010;10;n2001101000120101105Q0bn10110200021010100X9?P>P=PlP`P0P6P511s@PRPQn10110^00021010;00D3Q2MP3Ec1G`{P?P6P0P>P6P9Q00P=P5P6P9Q00P6P6P6P8P8n200110100012010;10;n2001101000120101105Pcn10110200021010100X9?P>P=Q0xQ0bP0P6P5Q2yPRPQn10110^00021010;00D3Q1MP2EcQ0x/Gs1Gc|P6Q0|1GakQ1L=05kR4PTPEP<Q2lQ01Q1R#4S2y50ES00A0EXXRMQ2oQ1U#8PEPzP@PYC5S1:[S1;3VS08'2D?[[XF6Q0g/G|P6PaPTA0E<<S04PEQ01Q2xQ08Eb\4X@6P0P6P5Q1R/1@PRPQn10110^00021010;00=05|P5Q1LPTQ04PEQ01Q01Q2o%89Q1:[5VMEbXA5PTQ2jQ2j50ES1:%4NS04Q0450ES08Q2oQ1L#8PEQ1_P@PYC5[S1L'2S2},2MS2|'2R4'21NEUQ1:P4Q2j,NEQ08Q2|Q04,NEPMQ2}1NEXQ2oQ1L1NEYRMQ1KPEP0P6Q1y#8A0E8Y[P9P6%8RQ2x=0EY[P9A05::PMW2A05Q:RMP5PQP5Q0rP9PgQ0sn0110500020000X95Q03P:P9E_R:PgQ0z#4RR=0EY/F9b=W2XEHP9O1P:Pg%d7=<EY/F9b=X2MXEHP9O1n0110;0003001010110101XG6P9O1P:PgA0E;YR:/F9b=X2Mn10110200021010;00b6C]C]C]C]C]PkP9E_W2PkP9E_W2PkP9E_W2P9O1b2P9O1b2P9O1b2W7PSP9PbFmb8b2W0W8Q2q=05QP5P?%\QRQPGQ2sn0100000020000Q2V50?P?P5P?PQPGQ0wn0100000020000PhQ2SP9D9PgQ2p/F9b2W0W8n0110500020101P9P7O2b8b>W0W5PVP9Q0>P8GfW2W0W1P_P9P]P3GfW2P8P9O2n2001000000121000000bJW0W5XH6P9O1Q0O=0E;P6P?PSPGPHP?P9PGPHP?P9PHP?P9PHP?P9PHP?P9PHP?P9PGPHP?P9PHP?P9PGPGPGn0110T00031010U1010U00S0OPGPGn0110S00031010T1010T00S0>PGn0110R00031010S1010S00S2pPGPGn0110Q00031010R1010R00RQPGPGn0110P00031010Q1010Q00RMPGPGn0110O00031010P1010P00R0PGPGn0110000031010O1010O00R4PGn011010003101001010000S0wPGn0110;0003001010110101P>P=P_P]PeD3S2s50?P611WDS2q=0EZP6P?P8PGQ0wPGn0110;0003001010110101S0zP>P=PWQ0bP`D3S0350?Q2l=0EUS2l%4PS0sQ2d50ES0rQ0I#4S2x%4WS1y50ES1LPE%4VS2oPXP:Q0b#8Q0X=0EY[S0XFWRV'2]0]1P[Q0b/1DS2}=0EYQ0i90?GS2|P?PGPhQ03P9D9S08PgA0EYUS1:?6V9b2W0W1Q0o=0EiPHP?P8PGP4PGn011010003101001010000R4Q0p50?PH11lDS02=0EiQ2_90?4A0ERUS2~Q0\Q0x#4S3050ES31Q0RQ0150ES32PEQ0JPXP:%8NPEQ0|P@PYC5[S0JFWS33'2]0]1P7Q0}90EvQ2]Q2^PgQ14=<EUS14%4dS34Q2h50ES35Q0s%4cS3650ES37PEQ2xPXP:Q0x#8Q2n=0EY[S2nDLP9DAb2W0W1X3HP9O1A0EvoPHP?P8P0PGPGn0110000031010O1010O00R0Q2\50?PH11FDS38=0EoQ1190?0Q1>=<EUS1>%4]S39Q2j50ES3:%4SS3;Q2g50ES3<PE%4IS3=PXP:Q0|#8Q0m=0EY[S0mFWS0|'2]0]1P7Q2X=0ErPHP?P8PMPGPGn0110O00031010P1010P00RMQ2Y50?PH11tDS3>=0ErQ2V90?MQ1E=<EUS1EQ1yQ0{50ES3?Q34%4tS3@50ES3APEQ0sPXP:Q0l#8Q2f=0EY[S2fFWS3B'2]0]1P7Q2R=0ExPHP?P8PQPGPGn0110P00031010Q1010Q00RQQ2S50?PH11{DS3C=0ExQ2P90?QQ1N=<EUS1NQ2uQ2wPEQ0\PXP:Q2zFWS3D'2]0]1P7Q2L=0E}PHP?P8Q2pPGPGn0110Q00031010R1010R00RNQ2M50?PH11kDS2p=0E}Q2:90?NQ1W=<EUS1WQ2gQ1U5PES3EQ2b%4kS3F50ES3GPEQ39PXP:%8|Q1K=0EY[S1KFWS3H'2]0]1P7Q2E=0E~PHP?P8PGQ0>PGn0110R00031010S1010S00RRQ2G50?PHPEQ1_PDP~C5Q2C90?RQ1a=<EUS1aQ3@=PEzS2CQ36Q1_5PES2GPEQ1yPXP:%8yPEQ1cP@PYC5[S0>FWS3I'2]0]1P7Q1qQ1e50EQ2AQ2BPgQ1j=<EUS1jQ0kQ1c5PES3JQ2gQ1T5PES3KPEQ2bPXP:%8zQ1]=0EY[S1]DLP9DAb2W0W1X3HP9O1Q1q=0EuPHP?P8Q0OPGPGn0110S00031010T1010T00RzQ2@50?PHPEQ1gPDPuC5Q1h90?zQ1==<EUS1=Q2vQ1\5PES1hQ1g9PE<S2@PEQ01PXP:Q1c#8PEQ1rP@PYC5[S1cFWS0O'2]0]1P7Q2>=0EnPHP?P8PGPGPGn0110T00031010U1010U00RVQ1{50?PHPEQ1nPDPnC5Q2590?VQ1x=<EUS1xPEQ3FQ1vPEQ0kQ1nPEQ2gPXP:Q1r#8Q1u=0EY[DLC^C^S1u'2]0]1P7Q1zQ1H50EQ1~90?GS1~P?PGPhQ1wP9D9S1wPgQ13=<EUS13PEQ2yQ1tPEQ2vQ1@PEP<PXP:Q1v#8Q26=0EY[DLC^C^S26;69b2W0W1X3HP9O1Q1zQ2050EQ1~Q1wPgQ23=<EUS23Q26;69b2W0W1X3HP9O1Q1s=0EUQ1oQ27PgQ1u=6T9b2W0W1n011010003111011110101P8P9O2W0W1X3HP9O1Q2>Q2;50EQ2<Q1pPgQ24=<EUS24PE%4sS1pQ1r#4PEQ3@Q1^PEQ36PXP:Q1\#8PEQ1vP@PYC5[DLC^P9EMb2W0W1X3HP9O1Q1dQ2=50EQ1fQ1iPgQ2==0EUS2<Q0O;69b2W0W1n011010103111011110101P8P9O2W0W1X3HP9O1Q1YQ2?50EQ1bQ2DPgQ2?=0EUS0OQ3I;69b2W0W1n011010103111011110101P8P9O2W0W1X3HP9O1Q2EQ1m50EQ2HQ2IPgQ21=<EUS21APE<yS3IQ00PEQ0ePXP:Q1;DLP9DAb2W0W1X3HP9O1Q1PQ2F50EQ1XQ2JPgQ2F=0EUS1vQ3H;69b2W0W1n011010103111011110101P8P9O2W0W1X3HP9O1Q2LQ1l50EQ2NQ2OPgQ2K=<EUS2KQ36=PE|S3HQ1yQ1p50ES1\PEQ34PXP:Q18#8PEQ1UP@PYC5[S1UDLP9DAb2W0W1X3HP9O1Q0<90EwQ1OQ2QPgQ0<=0EUS18Q3D;69b2W0W1n011010103111011110101P8P9O2W0W1X3HP9O1Q2RQ1k50EQ2TQ2UPgQ22=<EUS22Q2bQ1G#4S1G50ES3DQ39Q0k50ES1rPEQ3;PXP:Q1C#8Q19=0EY[S19DLP9DAb2W0W1X3HP9O1Q0=90EqQ1FQ2WPgQ0==0EUS1CQ3B;69b2W0W1n011010103111011110101P8P9O2W0W1X3HP9O1Q2XQ1550EQ2ZQ2[PgQ1}=<EUS1}Q0eQ0l#4S0l50ES3BQ0\=0E<S2>PEQ0RPXP:%8pQ2r=0EY[S2rDLP9DAb2W0W1X3HP9O1Q0990EmQ10Q12PgQ09=0EURpQ0|;69b2W0W1n011010103111011110101P8P9O2W0W1X3HP9O1Q1?90EfQ0:Q2`PgQ1?=0EUS0|Q33;69b2W0W1n011010103111011110101P8P9O2W0W1X3HP9O1Q0oQ2950EQ0qQ0tPgQ28=<EUS28Q3;Q0450ES33Q3=Q2b50ES1oPEQ0A#4S1uPXP:Q0g#8PEQ0xP@PYC5[S0xDLP9DAb2W0W1X3HP9O1n0110;0103001110111101PSP9O2W0W5n10110201021110;01P9P7O2b5b6W0W7XD6P9O1Q0D=0E;P6P?PIPGQ0wPGn0110;0003001010110101P>P=P[PSPbD3S0D50?P611dDS0g=0EZQ0zP>P=PdPOP\D3S2750?Q2lQ2xQ1|50ES1sPEQ2oQ34A0E;XR:PEQ0_PY%8OPEP_P@PYC5[C@S0_'2D?R|'2]0]1PJ11ODRy=0EYQ0^90?GS1~P?PGPhQ27P9D9S26PgQ1:?6|9b2W0W111eDR|=0EiP>P=PePdPOD3S1w90?4PH11`DS1z=0EiQ0a90?4Q2~Q0dQ0fP:PEPWPCPYQ0hD7S0hCYS0f'2]0]1P7Q2}Q0}50EQ2|Q08PgQ14Q0rQ1LPEQ0WPYQ0XC@S0X,2:P9DAb2W0W1X3HP9O1Q2}=0EoQ0i90?0PHQ0j=0EoQ0n90?0Q1>Q33Q1oP:PEPlPCPYQ0xD7S0xCYS1o'2]0]1P7A0EfrQ0u90?MPHQ0v=0ErQ0y90?MQ1EQ35Q37P:Q2mQ2n'2S2nCYS2m'2]0]1P7A0EmxQ0~90?QPHQ17=0ExQ1<90?QQ1NQ3BQ2>P:PEPtPCPYQ2rD7S2rCYS2>'2]0]1P7A0Eq}Q1A90?NPHQ1B=0E}Q1D90?NQ1WQ3DQ1rP:PEP{PCPYQ19D7S19CYS1r'2]0]1P7A0Ew~Q1I90?RPHQ1J=0E~Q1M90?RQ1aQ3HQ1\P:PEPkPCPYQ1UD7S1UCYS1\'2]0]1P7Q1PQ1e50EQ1XQ2JPgQ1jQ3EQ3GPEQ1RPCPYQ1KD7S1K,2:P9DAb2W0W1X3HP9O1Q1P=0EuQ1Q90?zPHQ1S=0EuQ1V90?zQ1=Q3IQ00P:PEQ1_PCPYQ1;D7S1;CYS00'2]0]1P7Q1Y=0EnQ1Z90?VPHQ1[=0EnQ1`90?VQ1xQ3JQ3KPEQ1gPCPYC5Q1]5V:3VS3K'2]0]1P7Q1dQ1H50EQ1fQ1iPgQ13Q1hQ2@PEQ1^PCPYC5Q1c5V:3VRO;69b2W0W1X3HP9O1Q1dQ2050EQ1fQ1iPgQ23?6O9b2W0W1X3HP9O1Q1q=0EUQ2AQ2BPgQ3K=6T9b2W0W1n011010103111011110101P8P9O2W0W1X3HP9O1Q1YQ2;50EQ1bQ2DPgQ24Q2CQ2GPEQ1TPCPYC5Q0>5V:P9DAb2W0W1X3HP9O1Q2EQ2=50EQ2HQ2IPgQ2<Q00;69b2W0W1n011010103111011110101P8P9O2W0W1X3HP9O1Q2LQ2?50EQ2NQ2OPgQ0OQ1\;69b2W0W1n011010103111011110101P8P9O2W0W1X3HP9O1Q1m90EwQ1OQ2QPgQ21Q2uQ2wPEPsPCPYQ2zD7S2z,2:P9DAb2W0W1X3HP9O1Q2RQ2F50EQ2TQ2UPgQ1vQ1r;69b2W0W1n011010103111011110101P8P9O2W0W1X3HP9O1Q1l90EqQ1FQ2WPgQ2KQ3?Q3APEPjPCPYQ2fD7S2f,2:P9DAb2W0W1X3HP9O1Q2XQ0<50EQ2ZQ2[PgQ18Q2>;69b2W0W1n011010103111011110101P8P9O2W0W1X3HP9O1Q1k90EmQ10Q12PgQ22Q3:Q3<PEQ16PCPYQ0mD7S0m,2:P9DAb2W0W1X3HP9O1Q0=90EvQ2]Q2^PgQ1CQ2m;69b2W0W1n011010103111011110101P8P9O2W0W1X3HP9O1Q1590EfQ0:Q2`PgQ1}Q31Q32PEPcPCPYQ0JD7S0J,2:P9DAb2W0W1X3HP9O1Q0oQ0950EQ0qQ0tPgQ1o=6p9b2W0W1n011010103111011110101P8P9O2W0W1X3HP9O111_DR_Q1?50EQ2s90?GS1oP?PGPhQ0aP9D9S32PgQ0|Q0f;69b2W0W1n011010103111011110101P8P9O2W0W1X3HP9O1Q2990E|Q1w90?GROP?PGPhP>P=P]PePdD3S0fP9D9S2mPgQ28Q3=Q2e50ES3<PEQ1uQ39PEQ0`PY%8ePEQ0bP@PYC5[C@S0b,2:P9FUb2W0W1X3HP9O1n0110;0103011110111101PIP9O2W0W7n10110201021110;01P9P7O2b7b6W0W;XL6P9O1Q06=0E;P6P?Q0APGQ0wPGn0110;0003001010110101P>P=PJPIP^D3S0650?P6PEPPPDPZC5Q0zP>P=PPPLPKD3S0`50?Q2lPEQ2oQ2aPEP;Q0sPEQ0UPXPEPSPCPY%8LPEP[P@PYC5[GKS0UFDR:'2]0]1Q0G11LDRe=0EYQ0T90?GS2oP?PGPhQ0`P9D9S0`PgQ1:?6:9b2W0W111bDR:=0EiP>P=PbPPPLD3S2>90?4PHPEP\PDPiC5Q0Y90?4Q2~Q0[PEP;Q0\PEPdPBPXQ0]D7S0]D?S0['2]0]1P7Q0}90EyQ1~Q26PgQ14Q1sPEP;Q34PEQ0NPXQ0_C@S0_P9FUb2W0W1X3HP9O1A0EyoQ0^90?0PHPEP]PDPoC5Q0f90?0Q1>Q3<PEP;Q39PEP`PBPXQ0bD7S0bD?S3<'2]0]1P7A0E_rQ2s90?MPHQ2q=0ErQ0390?MQ1EQ0rPEP;Q1yPEPaPBPXQ0XD7S0XD?S0r'2]0]1P7Q0o=0ExQ0p90?QPHQ02=0ExQ2_90?QQ1NQ31PEP;Q01PEPcPBPXQ0JD7S0JD?S31'2]0]1P7A0Ev}Q2\90?NPHQ38=0E}Q1190?NQ1WQ3:PEP;Q2gPEQ16PBPXQ0mD7S0mD?S3:'2]0]1P7Q2X=0E~Q2Y90?RPHQ3>=0E~Q2V90?RQ1aQ3?PEP;Q3@PEPjPBPXQ2fD7S2fD?S3?'2]0]1P7Q2RQ1e50EQ2TQ2UPgQ1jQ3DPEP;Q0kQ2{Q19'2S19P9FUb2W0W1X3HP9O1Q2R=0EuQ2S90?zPHQ3C=0EuQ2P90?zQ1=Q2uPEP;Q2vPEPsPBPXQ2zD7S2zD?S2u'2]0]1P7Q2L=0EnQ2M90?VPHQ2p=0EnQ2:90?VQ1xQ3EPEP;Q3FPEQ1RPBPXQ1KD7D?S1K'2]0]1P7Q2EQ1H50EQ2HQ2IPgQ13Q3IPEP;Q2yPEQ1_PBPXQ1;D7D?S1;;69b2W0W1X3HP9O1Q2EQ2050EQ2HQ2IPgQ23Q1;;69b2W0W1X3HP9O1Q1P=0EUQ1XQ2JPgQ1K=6T9b2W0W1n011010103111011110101P8P9O2W0W1X3HP9O1Q2LQ2;50EQ2NQ2OPgQ24Q3HPEP;Q1pPEPkPBPXQ1UD7P9FUb2W0W1X3HP9O1Q2=90EwQ1OQ2QPgQ2<Q2u;69b2W0W1n011010103111011110101P8P9O2W0W1X3HP9O1Q2?90EqQ1FQ2WPgQ0OQ3?;69b2W0W1n011010103111011110101P8P9O2W0W1X3HP9O1Q2XQ1m50EQ2ZQ2[PgQ21Q3BPEP;P<PEPtPBPXQ2rD7S2rP9FUb2W0W1X3HP9O1Q2F90EmQ10Q12PgQ1vQ3:;69b2W0W1n011010103111011110101P8P9O2W0W1X3HP9O1Q1l90EvQ2]Q2^PgQ2KQ35PEP;Q36PEPFPBPXQ2nD7S2nP9FUb2W0W1X3HP9O1Q0<90EfQ0:Q2`PgQ18Q31;69b2W0W1n011010103111011110101P8P9O2W0W1X3HP9O1Q0oQ1k50EQ0qQ0tPgQ22Q33PEP;Q2bPEPlPBPXQ0xD7S0xP9FUb2W0W1X3HP9O1Q2}Q0=50EQ2|Q08PgQ1CQ0r;69b2W0W1n011010103111011110101P8P9O2W0W1X3HP9O1Q1590E_Q1oQ32PgQ1}Q0dPEP;Q0ePEPWPBPXQ0hD7S0hP9FUb2W0W1X3HP9O1Q0990E|Q2mPgQ3<=6p9b2X0OW1n011010103111011110101P8P9O2W0W1X3HP9O111[DR[Q1?50EQ0D90?GS3<P?PGPhQ0YP9D9S0YPgQ0|Q0[;69b2W0W1n011010103111011110101P8P9O2W0W1X3HP9O1Q2990E:Q2>90?GS2>P?PGPhP>P=PSPbPPD3RkP9D9S0[PgQ28PEQ1uQ2iPEP;Q3;PEQ0VPXPEQ0EPY%8bQ0F=0EY[FDRbC@P9EMb2W0W1X3HP9O1n0110;0103011110111101Q0AP9O2W0W;n10110201021110;01P9P7O2b;b6W0W:X46P9O1PEQ0GQ05P;C5P?P6P?P2PGQ0wPGn0110;0003001010110101P>P=Q0GQ0AQ0?FHP6PEQ0IPDPZC5Q0zP>P=Q0IQ0HQ0BD3RZ50?Q2lPEP;Q2cPEQ0LQ2xPEPIPBPXPEPIPCPYQ0H#8PEPJP@PYC5[D7D7FDRB'2]0]1P1PEQ0HPDPYC5Q0K90?GP?PGPhPZP9D9PgQ1:?6B9b2W0W111^DRB=0EiP>P=P^Q0IQ0HD3RZ90?4PHPEPKPDPiC5Q0P90?4Q2~PEP;Q0QPEPPPAQ0RQ0SGKRP'2]0]1P7Q0}90EeQ2oQ0`PgQ14PEP;Q2aPEQ0CQ0sQ0UC@P9EMb2W0W1X4HP9O1A0EeoQ0T90?0PHPEPSPDPoC5A0?0kQ1>PEP;Q2iPEP\PAQ3;PbGKRb'2]0]1P7A0E[rQ0D90?MPHQ0g=0ErQ2790?MQ1EPEP;Q1|PEP]PAQ34Q0_GKR]'2]0]1P7A0E|xQ1w90?QPHQ1z=0ExQ0a90?QQ1NPEP;Q0cPEPWPAQ0eQ0hGKRW'2]0]1P7Q2}=0E}Q0i90?NPHQ0j=0E}Q0n90?NQ1WPEP;Q04PEPlPAQ2bQ0xGKRl'2]0]1P7A0Ef~Q0u90?RPHQ0v=0E~Q0y90?RQ1aPEP;Q2hPEPFPAQ36Q2nGKRF'2]0]1P7Q1e90EmQ10Q12PgQ1jPEP;Q2jPEQ16PAQ2gQ0mD7P9EMb2W0W1X4HP9O1A0EmuQ0~90?zPHQ17=0EuQ1<90?zQ1=PEP;Q0lPEPtPAP<Q2rGKR<'2]0]1P7A0EqnQ1A90?VPHQ1B=0EnQ1D90?VQ1xPEP;Q1GPEP{PAQ0kQ19GKR{'2]0]1P7Q1H90EwQ1OQ2QPgQ13PEP;Q2tPEPsPAQ2vQ2zGKRs;69b2W0W1X4HP9O1Q2090EwQ1OQ2QPgQ23?6s9b2W0W1X4HP9O1Q2R=0EUQ2TQ2UPgA6T{9b2W0W1n011010103111011110101P8P9O2W0W1X4HP9O1Q2;90EqQ1FQ2WPgQ24PEP;Q0{PEPjPAQ3@Q2fD7P9EMb2W0W1X4HP9O1Q2XQ2=50EQ2ZQ2[PgQ2<?6<9b2W0W1n011010103111011110101P8P9O2W0W1X4HP9O1Q2?90EvQ2]Q2^PgQ0O?6F9b2W0W1n011010103111011110101P8P9O2W0W1X4HP9O1Q1m90EfQ0:Q2`PgQ21PEP;Q30PEPcPAQ01Q0JD7P9EMb2W0W1X4HP9O1Q0oQ2F50EQ0qQ0tPgQ1v?6l9b2W0W1n011010103111011110101P8P9O2W0W1X4HP9O1Q2}Q1l50EQ2|Q08PgQ2KPEP;Q2dPEPaPAQ1yQ0XD7P9EMb2W0W1X4HP9O1Q0<90E_Q1oQ32PgQ18?6W9b2W0W1n011010103111011110101P8P9O2W0W1X4HP9O1Q1k90E|Q2mPgQ22PEP;Q2ePEP`PAQ39Q0bD7P9EMb2X0OW1X4HP9O1Q0=90EyQ1~Q26PgQ1C?6]9b2W0W1n011010103111011110101P8P9O2W0W1X4HP9O1Q1590E[Q3<Q0YPgQ1}PEP;Q0ZPEPdPAQ0\Q0]D7P9EMb2W0W1X4HP9O1Q0990E:Q2>Q0[PgA6pb9b2W0W1n011010103111011110101P8P9O2W0W1X4HP9O1PEPJPDQ1?C5Q0690?GP?PGPhQ0PP9D9PgQ0|?6P9b2W0W1n011010103111011110101P8P9O2W0W1X4HP9O1Q2990EBA0?GZP?PGPhP>P=PIP^Q0ID3P9D9PgQ28PEP;Q2kPEQ0MQ3=PEQ07PXPEPKPCPY%8^PEPLP@PYC5[D7FDP9EMb2W0W1X4HP9O1n0110;0103011110111101P2P9O2W0W:n10110201021110;01P9P7O2b:b6W0W1XI6P9O1PEP1PDP;C5P?PGP>P=P1P2P3FHP?PGPhQ0;P9D9PgA0E;UQ0@;69b2W0W1n10110201021110;01P9P7O2b1b6W0XA5X@6XF6WKo"). Qed.

Theorem node_mmap2_sound : mm2_stmt SEGS A nx0 LIMIT SINV argH FS0 (node_mmap2 A nx0 LIMIT).
Proof.
  intros cs csa csb E R FULL model TB HC Hec Hn HKB.
  unfold node_mmap2 in Hn.
  destruct (mmap_gate cs) as [[[prot flags] isnull]|] eqn:Hg; [|discriminate].
  destruct (mmap_gate_sound cs prot flags isnull Hg) as (H17 & H12 & H13 & H14 & H15 & H10).
  match type of Hn with (match ?g with Some csG => _ | None => None end) = _ => destruct g as [csG|] eqn:HG; [|discriminate] end.
  injection Hn as <- <-.
  destruct isnull.
  - specialize (H10 eq_refl).
    assert (ARMS : (prot = 3 /\ flags = 34 /\ mmap_null A nx0 LIMIT cs KRW true true = Some csG)
                   \/ (prot = 3 /\ flags = 16418 /\ mmap_null A nx0 LIMIT cs KRWLAZY false true = Some csG)
                   \/ (prot = 0 /\ flags = 34 /\ mmap_null A nx0 LIMIT cs KNONE false false = Some csG)
                   \/ (prot = 0 /\ flags = 16418 /\ mmap_null A nx0 LIMIT cs KNONELAZY false false = Some csG)).
    { repeat match type of HG with context [match ?x with _ => _ end] => destruct x; try discriminate end; tauto. }
    destruct ARMS as [(-> & -> & Hm)|[(-> & -> & Hm)|[(-> & -> & Hm)|(-> & -> & Hm)]]].
    + eapply (mmap_null_sound1 cs KRW true true); eauto; reflexivity.
    + eapply (mmap_null_sound1 cs KRWLAZY false true); eauto; reflexivity.
    + eapply (mmap_null_sound1 cs KNONE false false); eauto; reflexivity.
    + eapply (mmap_null_sound1 cs KNONELAZY false false); eauto; reflexivity.
  - assert (ARMS : (prot = 3 /\ flags = 16434 /\ mmap_fixed_free A LIMIT cs KRWLAZY false false = Some csG)
                   \/ (prot = 3 /\ flags = 50 /\ mmap_fixed_free A LIMIT cs KRW true true = Some csG)
                   \/ (prot = 0 /\ flags = 16434 /\ mmap_fixed_free A LIMIT cs KNONELAZY false false = Some csG)
                   \/ (prot = 0 /\ flags = 50 /\ mmap_fixed_free A LIMIT cs KNONE false false = Some csG)
                   \/ (prot = 3 /\ flags = 0x104022 /\ mmap_fixed_free A LIMIT cs KRWLAZY false false = Some csG)
                   \/ (prot = 0 /\ flags = 0x104022 /\ mmap_fixed_free A LIMIT cs KNONELAZY false false = Some csG)).
    { repeat match type of HG with context [match ?x with _ => _ end] => destruct x; try discriminate end; tauto. }
    destruct ARMS as [(-> & -> & Hm)|[(-> & -> & Hm)|[(-> & -> & Hm)|[(-> & -> & Hm)|[(-> & -> & Hm)|(-> & -> & Hm)]]]]].
    + eapply (mmap_fixed_free_sound1 cs KRWLAZY 16434 false false); eauto; first [reflexivity | left; reflexivity].
    + eapply (mmap_fixed_free_sound1 cs KRW 50 true true); eauto; first [reflexivity | left; reflexivity].
    + eapply (mmap_fixed_free_sound1 cs KNONELAZY 16434 false false); eauto; first [reflexivity | left; reflexivity].
    + eapply (mmap_fixed_free_sound1 cs KNONE 50 false false); eauto; first [reflexivity | left; reflexivity].
    + eapply (mmap_fixed_free_sound1 cs KRWLAZY 0x104022 false false); eauto; first [reflexivity | right; split; reflexivity].
    + eapply (mmap_fixed_free_sound1 cs KNONELAZY 0x104022 false false); eauto; first [reflexivity | right; split; reflexivity].
Qed.

Theorem node_mprotect2_sound : mm2_stmt SEGS A nx0 LIMIT SINV argH FS0 (node_mprotect2 A LIMIT).
Proof.
  intros cs csa csb E R FULL model TB HC Hec Hn HKB.
  unfold node_mprotect2 in Hn.
  destruct (node_mprotect A LIMIT cs) as [csG|] eqn:HG; [|discriminate]. injection Hn as <- <-.
  eapply node_mprotect_sound1; eauto.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition slarm_of (arm : fixed_in_arm) : slarm := match arm with ArmE => SlE | ArmF => SlF | ArmG => SlG end.

(* [comment removed for export] *)
Lemma eu_sub : forall E a b, bv_unsigned (edenot E b) <= bv_unsigned (edenot E a) ->
  bv_unsigned (edenot E (esub a b)) = bv_unsigned (edenot E a) - bv_unsigned (edenot E b).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmA ()) ["Nodes"] "h02Hah14__p1h24__p2h34__p3h44__x1h54__x2h64__x3h71bh81Eh91Hh:2H0h;2H1h<9RES_len'0h=7__arithh>4__ffh?6__sat3h@6__sat4hA6__sat5hB6__sat6hC6__sat7hD6__sat8hE8__varmaphF5__withG1ahH4cstrhI5cstr0hJ1xhK1yhL1zp;1p;2p;3p;<p;4p;6p;7p;8g005[j1=Tg006ej1^Tg00ljj2;Tg007Cj1gTg00kCj29Tg05EMj3]Tg00l@j26Tg00=Oj2<Tg001nj31j1QTg00;1j1ATg00Gnj2OTg00_Nj2HTg01Qfj1RTg00Ujj23Tg00UOj24Tg00Iaj2cTg00Voj1bTg00Wmj2`Tg00XMj1_Tg00YFR0j1:Tg00Yfj2ZTg00ZIj3YTg00JAj2CTg00Zfl<XTg00[Kj4WTg00\2j1MTg006@j18Tg00\Wj2LTg00]?j3KTg00]cj1VTg00^]j2JTg00_nj1UTg00:Rj1BTg00mFj2GTg02QOj3ITg02R8j2TTg00P@j1wTg01`nj3vTg00`hj1uTg00moj2STg02Rdj4tTg00afj1sTg00bDj1oTg00boj2PTg00nMj2DTg00P`j1fTg01^jj3eTg02;Mj4ETg04^^j3dTg00cRj2aTg00d4j2hTg00d`j3iTg00e?j4jTg05F5j3kTg05FXj2lTg003Yj6NTg05G\j3mTg05HXj4nTg05I`j2\Tg02PGj7pTg02SBj6qTg02Pkj7[Tg02Sfj8rTf0R1#=#=p=7f2R2f1R3/91'6p=2g02]UR4/;1p=0g02[^R5P3g02ehP1CEp=@P3g02a9R6g02aXR7P7g02b8R8P1g02bXFpp=5P3P6P7P7P8P1Eqp=FP2P6P7P7P8P3P1F[p=>f3R9P6P7P7P8P2P3P1Grp=?g02j^g02gRR6g02kZR:#=R;#=#7#7R<#^R=?221A2=23';%g=R>g05JXR?1992R@1993RA3]RB16=1f4RC=2=919C2RD,6=RE'<RF515X7>P516=@RG16=A'<RH%A;RI%A<RJ'ORK'HA151FXL5%R@%0G13GK'4%RD%0E13EK'4f5RE=2=CA2=E9'<g02_QRD1c>>p,4SEGS#b'`R>p,1ARG#_RF31%:>RL%:FRM515RNPDP5%QDP0%Q5%:3%:1515A1D311Z313YXKDXJDP>PL1C5LPFPM1C5MM<Xp,8RES_len'CWPN%MF%0M%M>%0L%8;#8#8#8#ARL,LI134IR>%0L1OILRM,34[[%0IRFg02iGRNAKIL3UW0%0M\N^0F%VGRM%7<#7#7#AR<'J%0M%0<RL1HM<RD#0[[1LIJ%0J134K[\>AKIJ3VNX0F%0K\N^0F%UGRG/J<%0G1HG<R<#0\L[p-0RLg02e<RFg02_2RN#B#B#BRJ#B,G51G5J1G5N5I55I5g02dP'T%wF3v%uFP51S52P31S59Ct%s5%o5RF1P54RN1D5;R;'@,5F1FFE5>F%f7R7PFf6,FFP51D5:RJg02`RR>1P5I=e5=RICE,5F5>FP7PF1@;J,5FP7PF%8:,D5,@N,5Ff7,FF5>FP7Ad5J;RJ,@N,5FP5PJP>PICE,5F5>FC?C?C?C?1aF8P1P2g02Z^RFg02[>R8'C1h12=1F8dAi543Cjb>bEbFX45X55X65X1LX2LW3%03/49133K,4E1;92%0Ef8'41<CERE#013EK'4[[[[^45^55^65^1L^2L^3LP1A15<4A15D4g034U,;M'4'4f?RMf>52=RD#0f=92=MRM/3KPGPMPDf:f;f<p,8HULL_ok'O:b=b?b@bAbBbCbDbIbHb<7kKb;b:16=B1l@AENAm?23,99P9P?P2P3CnEN1\2392=9=15HeW9X76WGW8o"). Qed.

Lemma eu_add : forall E a b, bv_unsigned (edenot E a) + bv_unsigned (edenot E b) < 2 ^ 64 ->
  bv_unsigned (edenot E (eadd a b)) = bv_unsigned (edenot E a) + bv_unsigned (edenot E b).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmA ()) ["Nodes"] "h02Hah14__p1h24__p2h34__p3h44__x1h54__x2h64__x3h71bh81Eh91Hh:2H0h;2H1h<9RES_len'0h=7__arithh>4__ffh?6__sat3h@6__sat4hA6__sat5hB6__sat6hC6__sat7hD6__sat8hE8__varmaphF5__withG1ahH4cstrhI5cstr0hJ1xhK1yhL1zp;1p;2p;3p;<p;4p;6p;7p;8g005[j1?Tg006ej1`Tg01;Sj26Tg00;1j1;Tg00Gnj2NTg00Ujj22Tg007Cj1[Tg00kCj28Tg05EMj3XTg00l@j25Tg001nj31j1QTg00_Nj2FTg01Qfj1RTg00UOj23Tg00Iaj2nTg00Voj1fTg00Wmj2dTg00XMj1bTg00YFR0j1ATg00Yfj2]Tg00ZIj3\Tg00JAj2CTg00Zfl<ZTg00[Kj4YTg00\2j1KTg006@j1:Tg00\Wj2JTg00]?j3ITg00]cj1WTg00^]j2HTg00_nj1VTg00:Rj1@Tg00mFj2BTg02QOj3GTg02R8j2UTg00P@j1TTg01`nj3wTg00`hj1vTg00moj2STg02Rdj4uTg00afj1tTg00bDj1sTg00boj2PTg00nMj2DTg00P`j1mTg01_Mj3lTg01^jj3kTg02;Mj4MTg00cRj2eTg00d4j2cTg00d`j3gTg00e?j4hTg00ljj2LTg05F5j3iTg05KDj2jTg003Yj6OTg05G\j3aTg05HXj4oTg05LHj2_Tg02PGj7^Tg02SBj6pTg02Pkj7qTg02Sfj8rTf0R1#?#?p=7f2R2f1R3/81'5p=4g02]UR4/L1p=0g02[^R5P3g02ehP1CMp==P3g02a9R6g02aXR7P7g02b8R8P1g02bXF^p=9P3P6P7P7P8P1Epp=EP2P6P7P7P8P3P1Fqp=>f3R9P6P7P7P8P2P3P1Grp=<g02j^g02gRR6g02kZR:#?R;#?#7#7R<#`R=?423A4=21'6%;;R>%;<R?'NR@'2%[=RAg05M@RB1892RC1893RD3XRE15=1f4RF=4=918F2RG,5=RH'6RI515X7AP515=CRJ15=D'6RK/F@A151IXL5%RC%0J12J@'3%RG%0H12H@'3f5RH=4=FA4=H9'6g02_QRG1nAAp,4SEGS#f'dRAp,1ARJ#bRI31%AARL%AIRM515RNPGP5%QGP0%Q5%A3%A1515A1G311]313\XKGXJGPAPL1C5LPIPM1C5MM<Zp,8RES_len'CYPN%KI%0M%KA%0L%:;#:#:#:#;RL,J>124>RA%0L1N>LRM,24[[%0>RIg02iGRNAI>L3UW0%0M\N^0I%WJRM%7<#7#7#;R<'H%0M%0<RL1FM<RG#0[[1J>?%0?124@[\AAI>?3VNX0I%0@\N^0I%VJRJ/H<%0J1FJ<R<#0\L[p-0RLg02e<RIg02_2RN#@#@#@R?#@,B51B5?1B5N5G55G5g02dP'U%TI3w%vIP51S52P31S59Cu%t5%s5RI1P54RN1D5;R;'=,9I1EIH5>I%m7R7PI1D5:R?,=N,9If6,EI5>IP7PIP5Al5?;R?g02`R1P5>=k5=CM,9IR>P7PI%::,D5,=N,9If7,EI5>IP71=N?,9I=>I>C<C<C<C<1eI8P1P2g02Z^RIg02[>R8'C1c12=1I8dAg543Chb>bEbFX45X55X65X1LX2LW3%03R8/39138H1629/2@%0Hf8'316FHRH#012H@'3[[[[^45^55^65^1L^2L^3LP1A15<4A15G4g034U,LM'3'3f?RMf>54=RG/2@f=94=MRM/2@PJPMPGf:f;f<p,8HULL_ok'O:b=b?b@bAbBbCbDbIbHb<7i@b;b:15=E1jCDEOAaB23,89P9PBP2P3CoEO1_2394=9=15KeW9X76WGW8o"). Qed.

(* [comment removed for export] *)
Lemma dest_cases_complete : forall E M cs ne m (lne rne : bool),
  know_ok SEGS E M (kn cs) ->
  bv_unsigned (edenot E (am_base m)) <= bv_unsigned (edenot E (reg cs 10)) ->
  bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) <= bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) ->
  lne = (bv_unsigned (edenot E (am_base m)) <? bv_unsigned (edenot E (reg cs 10))) ->
  rne = (bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) <? bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m))) ->
  In (lne, rne) (dest_cases cs ne m).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesMmA ()) ["Nodes"] "p'0h02H2h14__x1h21xh32H1h44__x2h51yh61Hh79RES_len'0h87__arithh94__ffh:6__sat3h;6__sat4h<6__sat5h=6__sat6h>8__varmaph?5__with@4cstrhA5cstr0hB1lhC1AhD1BhE2HlhF2HrhG1XhH4__x3hI4__x4hJ1bi001bhK1fhL3lnehM1mhN1rhO3rnehP2HahQ1ahR1nhS1EhT2HKhU4Hin1hV4Hin2hW1MhX2cshY2mbhZ2mlh[2nep%0p&0p;1p;4p;2p;3p;5p;8p;<p;6p;7g005[j1:Tg006ej1sTg007Cj1jTg000jj1vTg00LUj1;Tg03R`k40@Tg03Fkj1STg00jLj2QTg00ljj23Tg03Hbj1aTg03\<j2=Tg00`hj1^Tg03kmR0j4gTg03EYj35Tg00UOS00j2KTg00HKj2]Tg05Mlk505Tg00Iaj2dTg00gQk100Tg00P@j1bTg01`nj31Tg05NLj34Tg05OJj4VTg05Ofj2DTg00=lj2MTg00JAj2JTg05Pej8XTg05Qoj2ETg00Ujj2NTg03\Yk20GTg00Vok10FTg00Wmk20ETg00XMk10DTg001nj32j1qTg00YFR1j1`Tg00Yfk20ATg00ZIk30?Tg00Zfm<0>Tg00[Kk40=Tg00\2j1oTg00;1j1fTg006@j1TTg00\Wk20<Tg00Gnk20;Tg00]?k309Tg00]ck108Tg00^]j2mTg00_Nj2lTg00_nk104Tg00moj2\Tg00aHk103Tg02Rdj4eTg00afk102Tg00bDk101Tg00nMj2[Tg00boj2kTg00P`j1~Tg02;Mj4cTg00cRj2}Tg00d4j2|Tg00d`j3{Tg00e?j4zTg01;Sj2ATg045Yj4ZTg003Yj6OTg04ZCj3LTg05S2j2yTg05SRj3xTg01bMS01k206Tg05Snk307Tg04Z]j3wTg05U6k50:Tg01NAj4nTg01ejj4iTg05UUj3uTg00kCj2pTg00l@j2hTg00:Rj1rTg00QBj4_Tg01_Mj3tTg02PGk70BTg02Sfk80CTf2R2f1R3f0R4'p'hp=0%r4#rp=Rf3R51p34,h2'Ap=8g02Z^R6?234p=9P6P6P3P4C_p=Ig02gRR7g02[^R8P3P4C_p=PP7P8P4g02]UR9C_p=BP7P8P3P9C_=124p=>f4R:A1523;44p=CA5634p=<g02[>R;9264p=7A26;4p=W1394p=?At834p=6P8P3g02ehP4Ccp=GP3g02a9R<g02aXR=P=g02b8R>P4g02bXK0Bp=@P5P<P=P=P>P2P3P4L0Cp=Y1A49p=Fg02\<R<9264p=HA26<4p=Ug02j^g02kZR?#:R@#:S02#:RA#:#:#:RB#sRC#jRD%sA#j#v[g02\\g047^p,4SEGSRAf6REf5RF%;:H0@f7RG%S550Cg02_2#R#R#R#R#RRH,QF90CG'3f8RI1QEH50CPCPIPFC8%S:90CIPCPI%a:C8'3f9RJ%SF50C1QGH90CJ'=,9:f:RK1QIH50CPCPKPGC8%SE90CKPCPK%aEC8'=,9:1QJHP7%SIP7%aJP7P0p4p710RHP0p4p7210R0%^3\3RL%^2RMQ00P:P5P2P3Cg9554A5E45S03P:P4O1S0495F2'KX2F,]FRN[A5F42S05P5P4O1S0695:3'KX2:,]:PFP:P5P2Cg95:3[ROPEPFP:P5Cg95F2\NP:P5P2P3P4I05P4n2001000000120000000X52WBWKWDWCPO^52^BM^KL^D0^CHP4P61d66RHP6PH1I34XN6P6%^6R0f>RL#;RO1d78RN&00?RP,P5RQ%B2RR%bNRS51NRT%B:RUf=RV=>NSS0751NRWDCS08%b6RX916;RYP6P0%B5RZ=1NT94OWA16<XRWA16;WR[n0100000020000n0100000020000S09CVR\XB6P6P0%;VR]PNPQPSPTDCRQPYP6P01D52A1NZSR^94]T'MPWP[n0100000020000n0100000020000RT1IKJR_P6P6P0POPN1P:PS0:PSP^DCR`PYP6P01D:5A1NUSS0;94O^'MPWP[n0100000020000n0100000020000,<4f;RO/IKRa=5H\'KX26PK1<KTP6PH1IO4XN6P6P0P]PN1P2PA>N3SRTf<R\=>NSRb91NZRZDCPYP6P0A1NRT94]ZPWP[n0100000020000n0100000020000CV95H_PQP61J64S0<19`4P6f@R`#;RQ1PEPS0==1NSR_%BFS0>=1NSRZ34/94P6P0P3PYP6P01DGEfAR]#;RT%BERR=1NSRc%BGRd=1NSRe34'MRfPWP[n0100000020000n0100000020000,<L]3P3f?Rg#;S0?PN1PFPS0@PSQ0;DCRh#7PAfBRiP]PQP_PZPOP4GX1EiZ1Ei_'3%WLS0A1<LXS0BP6fCR_=0CEA0C_G'=Rj%W4S0CXL6P6PjP;Q001=34S0D#71N23Rj[1N341=23Rk#7[Rl1=52Rm#7\j20G34P4n2001000000120000000XM8XR8S0EPl^M8^R8S0FP4fDRl=0CGS0GA0ClIS0Hg02_QRj1dDD&0FA+0ERDp,1ARn$0DRo32%`DRp%`oRq528RrPjP8%qjP1%q8%`3%`4528A2j3420A3440?X5jX2jPDPp1J8pPoPq1J8qN<0>p,8RES_len'H0=RjPr%ooRo%?qRq%oDRD%?pRp%f@R1%T@#T#T#T#fRs+0<Rt1N91%?s20;1sRu,N9[[Rv%?1Rwg02iGRxB091s3UWPRs%?u\x^PwRw&08nRx%:B#:#:#:#:#:#fRB'mRu%?x%?BR11lxB#?[[Rx&04nRn/mBRy%?n1lnB#?\1[R1g02e<Rn#bRB%^nRnP81\82P3&038S0ICeS0J&028Rz&018R{1[8?R|1k89R}'6S0K/6}S0L1[8@R@1k8PS0M'6/6}'G,@{%~=S0NP8P|g02`RS0OP@Cc,@{CY1}{>R>P4P21J6;S0P1|42#7dA{893CzR9b9b>b?X18X48%F4S0Q#FS0R1A3P#F'31N32[^18^48P4fLR==0C`A0C=gPJO3b8b:b;b<b=bAb@b7O3b6CZPLPJEO3LbGW3%Hh1DEFA4QZc'MP6Q0<19f4P61DJI%;_S0S%BIS0T=1NSRf%BJS0U=1NSRh34'M/94P6P0P3PWP[n0100000020000,<]S0V]0P31DIG%;iS0W?4ef'MS0X#7%U`1<`XP6fER==0CIS0YA0C=JS0Z'=R~%U4S0[XL6P6P~P<Q00Q0D#H1332S0D[1343%Hk[RkQ0D%Hm[1y34P4n2001000000120000000X58X28S0\Pk^58^28S0]P4fFRk=0CJS0^A0CkKS0_1DKJRm%;lS0`%BKS0a=1NSS0b74hRh;x3%7m%7h+06Q011DOK#7%;=Q0bA>NOSRh34#7fHRm=0C\S0bA0CmOS01'3P41D\O#7B07V\4A27V\P7PVfKRV=0C4A0CVL'3XQ7PjPrPoPqPDPpPtPvPsPwPuPxPyP1PBPn1\83Pz1G||,@{P>P9b9b>b?X181344^18P4fRS0c=0C=S0dO1b8b:b;b<b=bAb@b7PLP4EOb0W0P4O1%;k?4hb#7PAfIRhPmfGRV#;PbQ07PiP4GXQ07,Eh1Ehb'3PjPrPoPqPDPpPtPvPsPwPuPxPyP1PBPnQ0JPzP{Q0L16@}/6}S0J'G,@{Q0N1G|@,@{CYP>P9b9b>b?X18X48Q0R%F3#FS0L'3Q0D[^18^48P4Q0dQ0c=0CkPIO3b8b:b;b<b=bAb@b7bGW0P4O1n200100000021100011000b0O3b6CZP`POEO3LW0Q0X#HP6Q0^Q0_'=,941<3[S0X]EP`%W~A26;;A56;WQ0P3LS0PWE%U~A26;<A56<WA26<<A56<X1J6<3L3wS0cWEn0110000020000POO1W0n0110000020100P4O1b0bJW3n0110000020101P4O1b3bJg05VSR~p4p710S0dP~p4p7210R~P3\3RhQ00P:P5P2P3CV9554Q04=2F2Q03'KX2F,]FRb[Q06=2:3Q05'KX2:,]:PFP:P5P2CV95:3[S05PEPFP:P5CV95F2\bP:P5P2P3P4I0:P4n2001000000120000000X52XBMWKWDWCQ0dQ05^52^BM^Kh^D~]CP4P6PH1I\4R~XN6Q09PaP61I\O92H~P6P0Q0?PNQ0:P^Q0>A>NLS51NR~DCRhPYP6P0Q0?A1NU^74~PWP[n0100000020000n0100000020000,<4'KX26PKA2HaaQ09,<K1JHaQ08P6Q0<19h4P6Q0==1NZRhA>N`S91NdRa54T/94P6P0P3PYP6P0Q0WPNQ0TA>N]SA1NdcDCRdPWP[n0100000020000n0100000020000,<L]3P3PQPNQ0@Q0;A>NgS91NRDCRQ#7PAP_PiPTPhPaP\P4GX1E_a1E_h'3Q0AQ0BP6Q0HPCPlP]C8Q0GPCPlPEC8'=RhQ0CXO6P6PhP;Q0EQ0FP4Q0ZPCP=PiC8Q0YPCP=PGC8PjPrPoPqPDPpPtPvPsPwPuPxPyP1PBPnP8P81\8:P2Q0ICeP31\85CeR;PzP{Q0KQ0J'6Rh%T?,[8R?Q0M'6Q02,[8R[/6}/6}RW'6'G,@{Q0NP816|@R@Q0O16?[R[Cc,@{CYP>P9b9b>b?X18X48XH8XI8Q0QQ0L'AR|1A2P%F5#FRP'A'31A32Rc1A5:R:'N[^18^48^H8^I8P4fMR5=0CgA0C5`fJ90C5A0C5]PJO5b8b:b;b<b=bAb@b7O3b6CZPLPJEO3LbGW3%HQA1NRZ94TaP6Q0<19d4P6Q0`Q0aA>N_S51NRdQ0U=1NfRf34/94Q0V]0P3Q0SPNQ0UA>NiSQ0T=1NeDCRe#7PAPkP=Q0`PdPfPgP4GX1Ekf1Ekd'3%U]1<]XP6A0CVOPCPVPlC8A0CVKPCPVPJC8'=RVQ0[XO6P6PVP<Q0\Q0]P4Q0bPCPmP=C8Q01PCPmPKC8PjPrPoPqPDPpPtPvPsPwPuPxPyP1PBPnP;PzP{16?}/6W,Gh,@{Q0N1G@[,@{CYP>P9b9b>b?X18X48XH8XI8%F2/AP,3|13c:[^18^48^H8^I8P4fPR8=0C5A0C8lA0C8iA0C8_PJO5b8b:b;b<b=bAb@b7O3b6CZP]P\EO3LbGW0%HeP6194VQ0X]FP`Q0_PCPkP_C8Q0^PCPkPIC8'=Rk#WQ0PWF%UkQ0cWFn0110000020000POO1W0n0110000020101P4O1b0bJW3n0110000020101P4O1b3bJCnCiO6b6CnCiO6b6bZbYbQ1IEFAuJIG55HeWFWEWVWUWTXO6XL6WMX[7WXWWWSo"). Qed.

(* [comment removed for export] *)
Lemma mmap_fixed_in_sound1 : forall (hole : bool) cs arm b off ne nlo nhi m csO E R FULL model TB,
  CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
  reg_lit cs 17 = Some 222 ->
  reg_lit cs 12 = Some (match arm with ArmG => 0 | _ => 3 end) ->
  reg_lit cs 13 = Some (match arm with ArmF => 16434 | _ => 50 end) ->
  reg_lit cs 14 = Some (two64 - 1) -> reg_lit cs 15 = Some 0 ->
  fixed_in_args A cs arm = Some (b, off, ne, nlo, nhi, m) ->
  mmap_fixed_in A LIMIT cs arm = Some csO ->
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' csO R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg R' (pc csO) FULL' model') TB) ->
  srealizes SEGS (cfg R (pc cs) FULL model) TB.
Proof.
  intros hole cs arm b off ne nlo nhi m csO E R FULL model TB HC Hec H17 H12 H13 H14 H15 HFI Hn HKB.
  destruct (is_ecall_at_sound SEGS cs Hec) as (w & Hf & He & Hp0 & Hp4).
  rewrite fixed_in_args_eq in HFI. unfold fixed_in_args_ref in HFI.
  destruct (fixed_args A cs TOPMAX) as [[[[[b0 off0] ne0] nlo0] nhi0]|] eqn:HFA; [|discriminate].
  destruct (find_containing (kn cs) (a_maps cs) _ b0 off0 ne0) as [m0|] eqn:Hfind; [|discriminate].
  match type of HFI with (if ?c then _ else _) = _ => destruct c eqn:Hvars; [|discriminate] end.
  injection HFI as -> -> -> -> -> ->.
  rewrite mmap_fixed_in_eq in Hn. unfold mmap_fixed_in_ref in Hn. rewrite fixed_in_args_eq in Hn. unfold fixed_in_args_ref in Hn. rewrite HFA, Hfind, Hvars in Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hbud; [|discriminate] end.
  destruct (reg_lit_sound' E cs R FULL model 17 222 HC ltac:(lia) H17) as [R17 _].
  destruct (reg_lit_sound' E cs R FULL model 12 _ HC ltac:(lia) H12) as [R12 _].
  destruct (reg_lit_sound' E cs R FULL model 13 _ HC ltac:(lia) H13) as [R13 _].
  destruct (reg_lit_sound' E cs R FULL model 14 _ HC ltac:(lia) H14) as [R14 _].
  destruct (reg_lit_sound' E cs R FULL model 15 0 HC ltac:(lia) H15) as [R15 _].
  rewrite <- bv5_17 in R17. rewrite <- bv5_12 in R12. rewrite <- bv5_13 in R13.
  rewrite <- bv5_14 in R14. rewrite <- bv5_15 in R15. rewrite (Z_to_bv64_m1 _ eq_refl) in R14.
  destruct (slice_args E cs R FULL model b off ne nlo nhi _ m HC HFA Hfind)
    as (Hm & [Hkind Hnf] & R10 & R11 & Hlen & Hne & Un & HnZpos & HnZ & HnZal & Hal & Hpos & Himg & Hest & Hin1 & Hin2 & HmC & Hmc & Hrfres & Hov).
  rewrite <- bv5_10 in R10. rewrite <- bv5_11 in R11.
  set (len := bv_unsigned (edenot E (reg cs 11))) in *. set (nZ := page_round_up_Z len) in *.
  set (n := Z_to_bv 64 nZ) in *. set (addr := edenot E (reg cs 10)) in *.
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf.
  pose proof (proj2 (proj2 (proj2 Hwf))) as Hisp.
  pose proof (u64_range addr) as Ra.
  pose proof (co_sp0 _ _ _ _ _ _ _ _ _ _ _ HC) as SP0. unfold CEIL, TOPMAX in SP0.
  assert (Htop : bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model)).
  { fold nZ. unfold alloc_top, stack_max_size. rewrite (co_top _ _ _ _ _ _ _ _ _ _ _ HC). lia. }
  assert (HF : slarm_of arm = SlF -> am_kind m = KRWLAZY).
  { intros Hs. destruct arm; try discriminate. cbn in Hkind. destruct Hkind as [<-|[]]. reflexivity. }
  assert (HnF : slarm_of arm <> SlF -> am_kind m <> KRWLAZY).
  { intros Hs Hk. destruct arm; [|exact (Hs eq_refl)|]; cbn in Hkind; rewrite Hk in Hkind; destruct Hkind as [|[|[|[]]]]; discriminate. }
  set (prot := match arm with ArmG => 0 | _ => 3 end) in *.
  set (flg := match arm with ArmF => 16434 | _ => 50 end) in *.
  assert (Hprot : prot = 0 \/ prot = 3) by (destruct arm; cbn; lia).
  assert (Hcore : mmap_flags_core (Z_to_bv 64 flg) = 50) by (destruct arm; [apply mmap_flags_core_32 | apply mmap_flags_core_4032 | apply mmap_flags_core_32]).
  assert (CONTB : forall model' FULL',
            slice_post (slarm_of arm) addr n model model' -> slice_mem (slarm_of arm) addr n FULL FULL' -> m_fs model' = m_fs model ->
            srealizes SEGS (mkCfg (mkst (regupd R 10 addr) (v_addi (Z_to_bv 64 (pc cs)) 4) FULL' (seg_rom SEGS)) model') TB).
  { intros model' FULL' SPo SM Hfs.
    assert (SH : slice_hyps E cs R FULL model (slarm_of arm) m addr n nZ model' FULL') by (constructor; assumption).
    rewrite (v_addi_pc (pc cs) Hp0 Hp4). rewrite bv5_10.
    assert (Hpc : pc csO = pc cs + 4).
    { destruct arm; try (injection Hn as <-; reflexivity). destruct (vis_add_inv _ _ _ _ _ Hn) as (nhi2 & _ & ->). reflexivity. }
    specialize (HKB E (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr) FULL' model' (conj (env_agree_refl' _ _) (env_agree_refl' _ _))).
    unfold cfg_of in HKB. rewrite Hpc in HKB. apply HKB; [|exact Hfs]. clear HKB.
    assert (Hregs' : regs_ok E (s_regs (a_ss cs)) (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr)).
    { apply regs_ok_regupd_same; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) | lia | rewrite <- bv5_10; exact R10]. }
    assert (MROUT := fun x => sl_MR_out E cs R FULL model (slarm_of arm) m addr n nZ model' FULL' SH cs x eq_refl).
    assert (MROUT' : forall x : word, bv_unsigned x < estart E (SA b off) \/ estart E (SA b off) + elenZ E ne <= bv_unsigned x ->
                      MR E cs model' FULL' x = MR E cs model FULL x).
    { intros x Hx. apply MROUT. rewrite Hest in Hx. unfold elenZ in Hx. rewrite Hne, Un in Hx. exact Hx. }
    pose proof (slice_cs1_ok E cs R FULL model (slarm_of arm) m addr n nZ model' FULL' SH (s_regs (a_ss cs)) (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr)) as CS1.
    destruct arm; cbn [slarm_of sl_charge] in *.
    -
      assert (Hk' : know_ok SEGS E (MR E cs model' FULL') (kimg_clip A (kn_unfill (kn cs) b off ne))).
      { eapply kn_unfill_clip_ok; [exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | rewrite Hest; unfold elenZ; rewrite Hne, Un; exact Himg | exact MROUT']. }
      unfold budget_ok in Hbud. apply Z.leb_le in Hbud.
      pose proof (CS1 _ (pc cs + 4) (s_next (a_ss cs)) nhi Hregs' Hk' HnZ ltac:(intros _; exact Hbud)) as HC1.
      eapply (vis_add_slice_ok E _ csO (reg cs 10) b off ne _ FULL' model' (bv_unsigned addr) nZ HC1).
      + exact Hn.
      + cbn [kn a_ss s_know mk_ss]. apply kimg_clip_in_hull'.
      + reflexivity.
      + exact Hest.
      + unfold elenZ. rewrite Hne. exact Un.
      + lia.
      + lia.
      + unfold TOPMAX; lia.
      + intros x Hx. rewrite (sp_maps _ _ _ _ _ SPo).
        split; [exact (sl_in_maps E cs R FULL model SlE m addr n nZ model' FULL' SH x Hx) |].
        split; [exact (sl_noacc_in E cs R FULL model SlE m addr n nZ model' FULL' SH x Hx) |].
        split; [destruct (argH E x) eqn:Ea; [pose proof (argH_high2 _ _ _ (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) Ea); lia | reflexivity]|].
        rewrite (proj2 SM x) by (rewrite Un; exact Hx). reflexivity.
    -
      assert (Hk' : know_ok SEGS E (MR E cs model' FULL') (kimg_clip A (kn_rezero (kn cs) b off ne))).
      { eapply kn_rezero_clip_ok; [exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | rewrite Hest; unfold elenZ; rewrite Hne, Un; exact Himg | exact MROUT' |].
        intros x Hx Hdef. rewrite Hest in Hx. unfold elenZ in Hx. rewrite Hne, Un in Hx.
        unfold Mr, mrestrict, hid in Hdef |- *.
        rewrite (sl_vis_in_F E cs R FULL model SlF m addr n nZ model' FULL' SH eq_refl cs x eq_refl Hx).
        destruct (argH E x); [exfalso; apply Hdef; reflexivity|]. cbn [orb] in *.
        destruct (VIS E cs model x); [|exfalso; apply Hdef; reflexivity]. cbn [negb].
        rewrite (proj2 SM x) by (rewrite Un; exact Hx). reflexivity. }
      injection Hn as <-. exact (CS1 _ (pc cs + 4) (s_next (a_ss cs)) nhi Hregs' Hk' HnZ ltac:(intros HH; discriminate HH)).
    -
      assert (Hk' : know_ok SEGS E (MR E cs model' FULL') (kimg_clip A (kn_cutout (kn cs) b off ne))).
      { apply know_ok_filter. eapply (APS.know_ok_cutout SEGS); [exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | exact MROUT']. }
      injection Hn as <-. exact (CS1 _ (pc cs + 4) (s_next (a_ss cs)) nhi Hregs' Hk' HnZ ltac:(intros HH; discriminate HH)). }
  unfold cfg_of.
  assert (R12' : getr R 12 = Z_to_bv 64 prot) by (destruct arm; exact R12).
  assert (R13' : getr R 13 = Z_to_bv 64 flg) by (destruct arm; exact R13).
  eapply (srz_mmap_fixedin_lazy SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w prot (Z_to_bv 64 flg) addr len TB
            Hf He Hhalt R17 Hprot Hcore R10 Hal Hpos R11 ltac:(lia) Htop R12' R13' R14 R15 Hrfres Hmc).
  - intros Hp3. fold nZ n. destruct arm; cbn in Hp3; try discriminate Hp3; subst flg.
    + apply mmap_fixed_rw_budget_ok_commit_intro; [apply mmap_noreserve_b_32 | exact Hwf |].
      unfold budget_ok in Hbud. pose proof (budget_slack E cs R FULL model nhi HC Hbud). lia.
    + apply mmap_fixed_rw_budget_ok_recommit_intro; [apply mmap_noreserve_b_4032 | exact Hwf | exact Hal | unfold page_size; rewrite Un; exact HnZal | rewrite Un; lia | rewrite Un; unfold CEIL, TOPMAX in *; lia |].
      eapply vm_backing_used_limit; [exact (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) | apply A_wf_allowA'].
  - fold nZ. fold n. destruct arm; subst prot flg; cbn [Z.eqb slarm_of] in CONTB |- *.
    + unfold fixedin_ok_model, with_mmap_replacement. rewrite with_mmap_backing_plain by apply mmap_noreserve_b_32.
      apply CONTB; [| | reflexivity].
      * constructor; reflexivity.
      * split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
    + unfold fixedin_ok_model, with_mmap_replacement. rewrite with_mmap_backing_lazy by apply mmap_noreserve_b_4032.
      apply CONTB; [| | reflexivity].
      * constructor; try reflexivity.
        unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing, m_vm_lazy_vm_forget_range.
        rewrite lazy_interior_fresh; [reflexivity | exact Hal | rewrite Un; exact HnZal | rewrite Un; lia | rewrite Un; unfold CEIL, TOPMAX in *; lia].
      * split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
    + unfold fixedin_ok_model, with_mmap_replacement. rewrite with_mmap_backing_plain by apply mmap_noreserve_b_32.
      apply CONTB; [| | reflexivity].
      * constructor; reflexivity.
      * split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
Qed.

Theorem node_mmapin_sound : forall hole : bool, mm3_stmt SEGS A nx0 LIMIT SINV argH FS0 (node_mmapin A LIMIT hole).
Proof.
  intros hole cs csa csb cscs E R FULL model TB HC Hec Hn HKB.
  unfold node_mmapin in Hn.
  destruct (mmap_gate cs) as [[[prot flags] isnull]|] eqn:Hg; [|discriminate].
  destruct (mmap_gate_sound cs prot flags isnull Hg) as (H17 & H12 & H13 & H14 & H15 & _).
  destruct isnull; [discriminate|]. cbv zeta in Hn.
  assert (CASES : forall arm,
     reg_lit cs 12 = Some (match arm with ArmG => 0 | _ => 3 end) ->
     reg_lit cs 13 = Some (match arm with ArmF => 16434 | _ => 50 end) ->
     match fixed_in_args A cs arm, mmap_fixed_in A LIMIT cs arm with
     | Some (b, off, ne, nlo, nhi, m), Some csO => Some (refuse cs, csO, mmap_destroyed A hole cs b off ne m)
     | _, _ => None
     end = Some (csa, csb, cscs) ->
     srealizes SEGS (cfg R (pc cs) FULL model) TB).
  { intros arm H12' H13' Hn'.
    destruct (fixed_in_args A cs arm) as [[[[[[b off] ne] nlo] nhi] m]|] eqn:HFI; [|discriminate].
    destruct (mmap_fixed_in A LIMIT cs arm) as [csO|] eqn:HO; [|discriminate]. injection Hn' as <- <- <-.
    eapply (mmap_fixed_in_sound1 hole cs arm b off ne nlo nhi m csO); eauto. }
  destruct prot as [|p|p]; try discriminate Hn; try (repeat (destruct p as [p|p|]; try discriminate Hn));
  destruct flags as [|q|q]; try discriminate Hn; try (repeat (destruct q as [q|q|]; try discriminate Hn));
  refine (CASES _ _ _ Hn); first [exact H12 | exact H13].
Qed.

End Nodes.

(* [comment removed for export] *)
Theorem node_mmap2_sound_OBL : forall SEGS A nx0 LIMIT SINV argH FS0,
  (forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None) ->
  res_len_ok SEGS A ->
  Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A) (segments_reserved SEGS) ->
  hull_ok A -> shadow_ok A -> AsanNodesMmLib.hull_cov SEGS A ->   (* [comment removed for export] *)
  (forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a) ->
  (forall E M (a : word), SINV E M -> argH E a = true -> APS.uE E e_sp0 <= bv_unsigned a) ->   (* [comment removed for export] *)
  (forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a) ->
  (forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M') ->
  (forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M) ->
  OBL_mmap2 SEGS A nx0 LIMIT SINV argH FS0.
Proof. intros. unfold OBL_mmap2. eapply node_mmap2_sound; eauto. Qed.

Theorem node_mprotect2_sound_OBL : forall SEGS A nx0 LIMIT SINV argH FS0,
  (forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None) ->
  res_len_ok SEGS A ->
  Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A) (segments_reserved SEGS) ->
  hull_ok A -> shadow_ok A -> AsanNodesMmLib.hull_cov SEGS A ->   (* [comment removed for export] *)
  (forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a) ->
  (forall E M (a : word), SINV E M -> argH E a = true -> APS.uE E e_sp0 <= bv_unsigned a) ->   (* [comment removed for export] *)
  (forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a) ->
  (forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M') ->
  (forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M) ->
  OBL_mprotect2 SEGS A nx0 LIMIT SINV argH FS0.
Proof. intros. unfold OBL_mprotect2. eapply node_mprotect2_sound; eauto. Qed.

Theorem node_mmapin_sound_OBL : forall SEGS A nx0 LIMIT SINV argH FS0,
  (forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None) ->
  res_len_ok SEGS A ->
  Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A) (segments_reserved SEGS) ->
  hull_ok A -> shadow_ok A -> AsanNodesMmLib.hull_cov SEGS A ->   (* [comment removed for export] *)
  (forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a) ->
  (forall E M (a : word), SINV E M -> argH E a = true -> APS.uE E e_sp0 <= bv_unsigned a) ->   (* [comment removed for export] *)
  (forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a) ->
  (forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M') ->
  (forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M) ->
  OBL_mmapin SEGS A nx0 LIMIT SINV argH FS0.
Proof. intros. unfold OBL_mmapin. eapply node_mmapin_sound; eauto. Qed.
