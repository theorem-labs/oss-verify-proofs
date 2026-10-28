(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_PmXv LbB_PmVec LbB_PmVup LbB_PmGlue LbB_PmVops LbB_PmDS LbB_PmWKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_PmWP1 () := "C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes9Morphisms5flip2C46Stdlib5Lists4List:in_app_iffC47Corelib4Init5Logic6eq_indC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface4bptrC46Stdlib5Lists4List2InC4ELinuxProcessSemantics5Riscv7Prelude5bvmapI6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase4pmwA00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_StI47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmOwn7pmw_okA00I6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5PMXAT00K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_AKRELC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option02C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec7seg_romC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState2MSC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge5rfullC47Corelib4Init9Datatypes3fstC47Corelib5Lists7ListDef3mapC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmCall;keys_nonnegC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut8fkeys_okK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase4c_v1C56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums1Z02C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmCall9obj_sh_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_ffC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells:cells_sizeK47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyI47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z3addC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmVup7set_v1AC4ARocqVerifyHarness?AgentSubmission8PropExec4getrK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr02K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmVops6ffkeepC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_SRC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut7pm_geomC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_s1C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow5aceilC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow2shC56Stdlib6ZArith6BinInt1Z2leC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_loC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase6wa_sp0C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;aceil_factsI47Corelib4Init5Logic3and00C6ARocqVerifyHarness?AgentSubmission3bpB2HF8BeapCeil5hceilC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac:pmw_boundsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase4wa_pC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7wa_consC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase8wa_wordsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase4wa_nC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmOwn7wk_pappC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow4aappC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmOwn7p_rangeC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmXp7xp_geomC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_FSBC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface7ff_addrC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8ff_classC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmOwn?pmw_frame_factsC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3fszC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5wa_fpC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5xa_v1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB3lblK47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C5ARocqVerifyHarness?AgentSubmission7LibCont4CRep4mdefC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega6VarMap1t01C47Corelib4Init5Logic3notC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z3mulC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase4c_m1C5ARocqVerifyHarness?AgentSubmission7LibHash4HRep;umap_blocksC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase4c_m2C5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase4c_m3C5ARocqVerifyHarness?AgentSubmission7LibCont4CRep?vec_opnd_blocksC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase4c_v2C5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase4c_v3C5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase4c_trC47Corelib4Init9Datatypes3appI47Corelib4Init5Logic2or00C47Corelib4Init5Logic3iffC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00K47Corelib4Init9Datatypes4list02K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase8c_blocksC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmVops:cblk_factsI47Corelib4Init5Logic2ex00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<ablock_rangeC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;aapp_boundsC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow@aapp_disjoint_shK46Stdlib9micromega7EnvRing5PExpr07C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow3nshC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase8xa_rheapC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmVup;blk_apart_pC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmXp<blk_apart_ffC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8blk_addrC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8blk_sizeC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmOwn7p_frameC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmXp<lf0_apart_ffC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmWKit>blksh_apart_ffC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase6xa_stkC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame9stk_splitC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_RHEAPC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase6pmc_shC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;addressableC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5xa_shC47Corelib4Init5Logic5proj1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PrsStmt7umap_shC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase8vsh_opndK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C35stdpp7tactics<f_equal_helpC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmVops:mod16_mod8C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase9xa_meminvC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase9xa_aconstC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8as_MPRESC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst6ACONSTC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut>env_world_seedC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut9env_worldC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut4ev_pC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut5ev_ffC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut5ev_s1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac<ev_world_allC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase9wenv_valsC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5EseedC56Stdlib6NArith6BinNat1N6of_natC56Stdlib6NArith6BinNat1N3addC56Stdlib6NArith6BinNat1N2leC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init9Datatypes6lengthC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut@wenv_vals_lengthC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut<edenot_app_xC47Corelib4Init5Logic6eq_symC47Corelib4Init9Datatypes3sndC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26edenotK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmTac6ev_addK47Corelib5Lists7ListDef6Forall02C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut9regs_tblXC56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init5Logic3and01C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame=disjoint_fromC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase8xa_slotsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase8slots_okI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List=Forall_forallC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmVops;sh_aceil_leC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmVops9sh_end_leC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses8or_morphC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase6pm_fshC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase6xa_fshC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit7fsh_patC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut:pm_fsh_lenC46Stdlib5Lists4List:length_mapC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow>SHAD_transportC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow4SHADC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface@aclient_write_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface=aimg_client_wK47Corelib4Init5Logic2ex01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap>ah_RHEAP_frameC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase8xa_lbownC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Own9lb_own_InC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Own;wr_at_wmonoC6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PrsStmt6cc_genC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface6cc_genC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9RtB_Iface=cc_gen_lengthC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7xa_pdefC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmVops8annot_dmC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9kentry_okK5ARocqVerifyHarness?AgentSubmission8SymExec33SX25saddr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmVops>kslot_of_cellsC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7know_okK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr03K5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond02C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut6xboundC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut7tbl_okXC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib3srsC5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sym_execC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8sc_denotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmVops:estart_varC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut6elit_uC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmVops;sc_flat_litC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26s_regsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut=sr_tbl_checkXC5ARocqVerifyHarness?AgentSubmission8SymExec33SX24s_pcC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25s_logC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S7regs_okC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8log_flatC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmGlue6rt_getC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sr_getC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut>regs_ok_of_tblC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Call6inb_InC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmCall>ff_addressableC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadowFaddressable_accessibleC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow:accessibleC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmCall8ff_shvisC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow5shvisC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow8SHAD_appC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow9shadow_ofC56Stdlib6ZArith6BinInt1Z6to_natC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow<poison_bytesC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap<ah_blk_shvisC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow9shvis_subC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmCall9wr_at_subC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_OwnArw_cells_of_wr_hiC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells8cells_atC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells8cells_wfC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells;cells_bytesC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3mkRC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge8rfull_eqC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<amemcpy_postC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib8u64_of_ZC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCellsBcells_bytes_lengthK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell05C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow:in_app_memC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow?aapp_in_app_memC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst9aconst_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib6LbB_SR=aconst_ok_appC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap9ah_memcpyC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_VISC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState6ret_pcC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState;ret_pc_evenC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge9rfull_mkRC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmCall;outside_decC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame7outsideC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC47Corelib4Init5Logic7f_equalC47Corelib4Init5Peano2ltC46Stdlib5Lists4List9nth_errorC46Stdlib5Lists4List9app_nil_rC56Stdlib6ZArith6BinInt1Z8max_specC47Corelib5Lists7ListDef3nthK47Corelib4Init9Datatypes6option01C46Stdlib5Lists4List>nth_error_nth'C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Z2Nat2idC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem2waC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmCall=def_of_mrd_hiC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMStateCZ_to_bv_bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atC47Corelib4Init5Logic5proj2C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmXv8sh_apartC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadowEaddressable_transportK46Stdlib9micromega:ZMicromega;ZArithProof03K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry07C56Stdlib6ZArith6BinInt1Z3divC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_ConvBsh0_of_addressableC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit8kshadow0C5ARocqVerifyHarness?AgentSubmission8SymExec33SX26a_baseC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25a_offC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S6estartC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S5elenZC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv<kwr_of_wr_atK5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit:sym_insideC46Stdlib5Lists4List7forallbC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S9mem_denotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit9munch_symC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit8num_winsC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5munchK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell01C5ARocqVerifyHarness?AgentSubmission8SymExec33SX26e_addrC5ARocqVerifyHarness?AgentSubmission8SymExec33SX27e_widthK47Corelib5Lists7ListDef6Forall01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv@rw_cells_log_nthC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmVops<fld_of_cell8C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame6sub_fpC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv9munch_appC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame<munch_weakenC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame;wmono_transC6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap>ah_mpres_transC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmVup5blkV1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmVup4vwinC56Stdlib6ZArith6BinInt1Z7div_posC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmVup4swinC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmCall9fld_munchC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmVup:pmxa_vupd1C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmVops<ffkeep_munchC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmVops<ffkeep_transC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmVops=shaddr_boundsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit9estart_shC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv?wmono_mem_denotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_FSlotsAmem_denot_definedC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_Conv=stk_mem_denotC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmGlue9rt_lookupC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmVops;pm_run_raw0C6ARocqVerifyHarness?AgentSubmission3bpB2Rt9BsCXXHeap<ahh_evt_thenC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmVops8pm_annotC5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts3t3bC5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts3t3cC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BStep8rw_cellsK45stdpp9bitvector;definitions2bv01C5ARocqVerifyHarness?AgentSubmission7LibHash6HStmts3t3aC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase6wa_LF0C5ARocqVerifyHarness?AgentSubmission7LibCont4CRep8vec_opndC4ARocqVerifyHarness?AgentSubmission8LibIface4liveC5ARocqVerifyHarness?AgentSubmission7LibCont4CRep3fldC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula06C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3stkC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5vsh32C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5wmonoC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem7mem_invC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7wa_diagC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7wa_userC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega7EnvRing5PExpr04C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrameBrw_cells_transportC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem5wr_atC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem8bytes_atC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem3mrdC56Stdlib6ZArith6BinInt1Z3maxC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC47Corelib5Lists7ListDef6firstnC46Stdlib5Lists4List7existsbI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsI47Corelib4Init9Datatypes3nat00K47Corelib4Init5Logic4True01C5ARocqVerifyHarness?AgentSubmission7LibCont4CRep7OPND_SZc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWP16ESH224K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib7Numbers7BinNums1Z01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6SHBASEC5ARocqVerifyHarness?AgentSubmission6LibPrs6PrsInv;PARSER_SIZEC6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs8AIMG_TOPC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6fframeC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase4O_V1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4AC_AC5ARocqVerifyHarness@ProcessOversightVTgt_spvtools_binary_parser_fuzzer_both1M?loaded_segmentsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4LY_AC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_MILB4MI_AC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205C47Corelib7Classes>Morphisms_Prop?or_iff_morphismC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow7AAPP_HIC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface=AINTRIN_STACKC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmCall9KEPT_REGSI47Corelib7Numbers7BinNums1N00C46Stdlib6ZArith4Znat7nat_N_ZC56Stdlib6ZArith4Znat3N2Z7inj_addC56Stdlib6ZArith4Znat3N2Z6inj_leI47Corelib4Init5Logic4True00I7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWP16RT_P1MC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltI5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry00K47Corelib4Init9Datatypes3nat01C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3ivlC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5blockC4ARocqVerifyHarness?AgentSubmission8LibIface3memI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase3pmc00K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<AANNOTATE_CCc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWP14E912c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWP14E944c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWP14E896c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWP18VP1_KEPTC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase4WV_PC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface7AFS_HDRC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface8AFS_SIZEC6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PrsStmt9PM_FCLASSC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface9AFS_FLAGSI47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic5False00C47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC47Corelib7Classes?RelationClasses=iff_ReflexiveC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase6PM_NSHC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5WV_FFC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase5WV_S1c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWP16RT_P1AC46Stdlib9micromega8ZifyInst7Inj_Z_ZC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7PM_OBJSC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow6AHI_LOc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWP16KN_P1AK47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop07I5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<AASAN_MEMCPYI5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts00C5ARocqVerifyHarness?AgentSubmission8SymExec33SX25sr_idC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow3memc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWP16RT_P1BI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWP16KN_P1Bc6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmWP16RT_P1E".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition E912 : expr := EAlu ALU_ADD (EVar 33) (ELit 112).

Definition E896 : expr := EAlu ALU_ADD (EVar 32) (ELit 224).
Definition ESH224 : expr := EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 224)) (ELit 3)) (ELit 2147450880).

Definition RT_P1A : list (reg * expr) :=
  [(1%bv, ELit 0xf1940); (2%bv, EVar WV_S1); (9%bv, EVar WV_S1); (10%bv, EVar 41); (11%bv, E912); (12%bv, ELit 20);
   (23%bv, EAlu ALU_ADD (EVar 41) (ELit 20))].
Definition RT_P1M : list (reg * expr) :=
  [(2%bv, EVar WV_S1); (9%bv, EVar WV_S1); (21%bv, EVar 41); (23%bv, EAlu ALU_ADD (EVar 41) (ELit 20)); (26%bv, E912)].
Definition RT_P1B : list (reg * expr) :=
  [(2%bv, EVar WV_S1); (9%bv, EVar WV_S1); (23%bv, EAlu ALU_ADD (EVar 41) (ELit 20))].
Definition RT_P1E : list (reg * expr) :=
  [(2%bv, EVar WV_S1); (9%bv, EVar WV_S1); (10%bv, E896); (11%bv, ELit 20); (23%bv, EAlu ALU_ADD (EVar 41) (ELit 20))].

Definition KN_P1B : list kentry :=
  [KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 224)) (ELit 3)) SHBASE) 1 (ELit 0);
   KWord (SA (EVar WV_S1) 464) 8 ESH224; KWord (SA (EVar WV_S1) 448) 8 E896;
   KWr (SA (EVar WV_P) 0) (ELit 288)].

Definition VP1_KEPT : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.



Section VP1.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.

  Let HHp : asan_rt_hyps H := rt_bp_base H HHbp.

  Lemma pm_vpush1 : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (cs : list cell) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 AANNOTATE_CC) fc None m (seg_rom asegs) -> rfull R ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    In (448, E896) tbl -> In (464, ESH224) tbl ->
    t3b (c_v1 c) < t3c (c_v1 c) ->
    obj_sh_ok ins 112 20 = true -> rw_cells asegs m (wa_ff w + 112) cs -> cells_size cs = 20%nat ->
    PropExec.getr R 1%bv = Z_to_bv 64 0xf1928 ->
    PropExec.getr R 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R 9%bv = Z_to_bv 64 (wa_s1 w) ->
    PropExec.getr R 10%bv = Z_to_bv 64 (t3a (c_v1 c)) ->
    PropExec.getr R 11%bv = Z_to_bv 64 (t3a (c_v1 c) + OPND_SZ * t3c (c_v1 c)) ->
    PropExec.getr R 12%bv = Z_to_bv 64 (t3a (c_v1 c) + OPND_SZ * t3b (c_v1 c)) ->
    PropExec.getr R 13%bv = Z_to_bv 64 (t3a (c_v1 c) + OPND_SZ * t3b (c_v1 c) + 20) ->
    PropExec.getr R 21%bv = Z_to_bv 64 (t3a (c_v1 c) + OPND_SZ * t3b (c_v1 c)) ->
    PropExec.getr R 23%bv = Z_to_bv 64 (t3a (c_v1 c) + OPND_SZ * t3b (c_v1 c) + 20) ->
    PropExec.getr R 26%bv = Z_to_bv 64 (wa_ff w + 112) ->
    (forall msF3 mo3 m3 R3, as_AKREL H s (mkCfg msF3 mo3) ->
       as_VIS H s msF3 = MS R3 F (Z_to_bv 64 0xf1970) fc None m3 (seg_rom asegs) -> rfull R3 ->
       PMXAT H LINV w s LB LBs m3 mo3 (set_v1A c (t3a (c_v1 c), t3b (c_v1 c) + 1, t3c (c_v1 c))) ins tbl ftbl TB spal ->
       (forall r, In r VP1_KEPT -> PropExec.getr R3 r = PropExec.getr R r) ->
       PropExec.getr R3 10%bv = Z_to_bv 64 (wa_p w + 224) -> PropExec.getr R3 11%bv = Z_to_bv 64 20 ->
       ffkeep w m m3 ->
       as_SR H Q (mkCfg msF3 mo3)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc cs Q OK X KR VIS RF Hknn Hfk H448 H464 HLT Hobj Ccs Hcs
           G1 G2 G9 G10 G11 G12 G13 G21 G23 G26 K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (p_range H w OK) as [PR1 PR2].
    pose proof (wk_papp H w OK) as (PA & PA0 & PA16).
    pose proof (xp_geom H HHp w OK) as (XG1 & XG2 & XG3 & XG4 & XG5 & XG6 & _).
    pose proof (p_apart_ff H w OK) as PAF.
    pose proof (xa_v1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as V1.
    pose proof (xa_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as ((_ & _ & _ & SHV1 & _) & ADP & _).
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    pose proof (xa_lbown _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as OWN.
    pose proof (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as STK.
    pose proof (xa_slots _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as SLOTS.
    pose proof (xa_fsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as FSH.
    pose proof (xa_pdef _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as PDEF.
    destruct (stk_split asegs m (wa_lo w) (wa_s1 w) (wa_sp0 w) STK ltac:(lia)) as [STK1 _].
    destruct (c_v1 c) as [[b n] cap] eqn:EV1. cbn [t3a t3b t3c fst snd] in *.
    destruct V1 as (Hv & Hv' & HD & Hlen & Hb & F0 & F1 & F2).
    unfold OPND_SZ, PARSER_SIZE, O_V1 in *.
    destruct Hb as [[B0 C0] | (Bpos & B16 & Cpos & Bhi & Hlive & Bapart)]; [exfalso; lia |].
    set (e := b + 20 * n) in *.
    assert (Ee : e = b + 20 * n) by reflexivity.
    assert (BLK : exists pid, In (pid, b, 20 * cap) LBs /\ In (pid, b, 20 * cap) LB /\ In (b, 20 * cap) (lbl LB)
                              /\ ablock_range H b (20 * cap) /\ 20 * cap <= 2 ^ 31).
    { apply (cblk_facts H HHp LINV w s LB LBs m mo c ins tbl ftbl TB spal b (20 * cap) OK X).
      unfold c_blocks. rewrite EV1. cbn [t3a t3c fst snd]. rewrite !in_app_iff. right; right; right; left.
      unfold vec_opnd_blocks, OPND_SZ. destruct (Z.eqb_spec b 0); [lia | left; reflexivity]. }
    destruct BLK as (pid & INs & INL & INl & (R0 & R16 & Rn & RI & RC & RF' & RAPP) & SZ).
    pose proof (aapp_bounds _ _ RAPP ltac:(lia)) as (AB1 & AB2 & AB3 & AB4 & AB5).
    pose proof (aapp_bounds _ _ XG6 ltac:(lia)) as (FB1 & FB2 & FB3 & FB4 & FB5).
    pose proof (aapp_bounds _ _ PA ltac:(lia)) as (PB1 & PB2 & PB3 & PB4 & PB5).
    pose proof (blk_apart_ff H HHp w s LB m (pid, b, 20 * cap) OK RH INL) as BAF. cbn [blk_addr blk_size fst snd] in BAF.
    pose proof (blksh_apart_ff H HHp w s LB m pid b (20 * cap) OK RH INL) as (BF1 & BF2).
    pose proof (blk_apart_p H HHp w s LB m b (20 * cap) OK RH INl) as BAP. unfold PARSER_SIZE, O_WIDX in BAP, PAF.
    pose proof (aapp_disjoint_sh b (20 * cap) b (20 * cap) RAPP ltac:(lia) ltac:(lia) ltac:(lia)) as DSHB.
    pose proof (aapp_disjoint_sh b (20 * cap) (wa_p w) 288 RAPP ltac:(lia) ltac:(lia) ltac:(lia)) as DSHP.
    pose proof (aapp_disjoint_sh (wa_p w) 288 b (20 * cap) PA ltac:(lia) ltac:(lia) ltac:(lia)) as DPSH.
    pose proof (sh_apart b (20 * cap) (wa_p w) 288 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) ltac:(lia)) as SHBP.
    assert (SHE : sh b + nsh (20 * cap) <= sh aceil) by (apply sh_end_le; lia).
    assert (SHEP : sh (wa_p w) + nsh 288 <= sh aceil) by (apply sh_end_le; lia).
    assert (SHA : sh aceil <= aceil) by apply sh_aceil_le.
    assert (FSHL : Z.of_nat (length (pm_fsh ins)) = 1448) by (unfold pm_fsh; rewrite length_map, pm_fsh_len; reflexivity).
    assert (B8 : b mod 8 = 0) by (Z.div_mod_to_equations; lia).
    assert (E4 : e mod 4 = 0) by (rewrite Ee; Z.div_mod_to_equations; lia).
    assert (NSHC : 0 <= nsh (20 * cap)) by (unfold nsh; apply Z.div_pos; lia).

    eapply (pm_annot H HHbp w s msF mo R F fc m b (20 * cap) (20 * n) (20 * n + 20) _ Q OK KR VIS RF);
      [ exact G10 | exact G11 | exact G12 | rewrite G13; f_equal; lia | exact G2 | exact G1 | reflexivity | lia
      | exact B8 | lia | lia | lia | exact RAPP | exact (SHV1 ltac:(cbn; lia)) | exact STK1
      | exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | exact (xa_aconst _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | ].
    intros msF2 mo2 m2 R2 KR2 MP2 VIS2 RF2 MU2 WM2 MI2 STK2 SH2 ACm2 KEEP2.
    unfold AINTRIN_STACK in MU2.

    assert (RH2 : as_RHEAP H s LB m2).
    { eapply (ah_RHEAP_frame H HHp); [exact RH | exact MU2 | exact WM2 |].
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
      - right; right; right; left. exists (pid, b, 20 * cap). cbn [fst snd blk_addr blk_size]. split; [exact INL |].
        lia.
      - left. cbn [fst]. lia. }
    assert (FSH2 : SHAD m2 (wa_ff w) (pm_fsh ins)).
    { eapply SHAD_transport; [exact FSH | exact MU2 | exact WM2 |]. rewrite FSHL. cbn [disjoint_from]. unfold PM_NSH in BF2.
      split; [lia | split; [lia | exact I]]. }
    assert (Ccs2 : rw_cells asegs m2 (wa_ff w + 112) cs).
    { eapply rw_cells_transport; [exact Ccs | exact MU2 | exact WM2 |]. rewrite Hcs. cbn [disjoint_from].
      split; [lia | split; [lia | exact I]]. }
    assert (WRB : wr_at asegs m b (20 * cap)) by exact (lb_own_In LBs m (pid, b, 20 * cap) OWN INs).
    assert (WRE2 : wr_at asegs m2 e 20).
    { apply (wr_at_sub asegs m2 b (20 * cap) e 20); [exact (wr_at_wmono m m2 b (20 * cap) WRB WM2) | lia | lia | lia]. }
    destruct (rw_cells_of_wr_hi m2 e 20 WRE2 ltac:(lia) ltac:(lia)) as (jA & CBA).
    assert (ADB : addressable m2 b (20 * n + 20)).
    { split; [lia|]. pose proof SH2 as S'. unfold cc_gen in S'. apply SHAD_app in S'. exact (proj1 S'). }

    set (Xs := [Z_to_bv 64 e]).
    assert (HT2 : regs_tblX w Xs R2 RT_P1M).
    { unfold regs_tblX, RT_P1M. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - rewrite (KEEP2 2%bv ltac:(inb)), G2. reflexivity.
      - rewrite (KEEP2 9%bv ltac:(inb)), G9. reflexivity.
      - rewrite (KEEP2 21%bv ltac:(inb)), G21. ev_xs. reflexivity.
      - rewrite (KEEP2 23%bv ltac:(inb)), G23. symmetry. apply ev_add; [ev_xs; reflexivity | lia | lia].
      - rewrite (KEEP2 26%bv ltac:(inb)), G26. unfold E912. symmetry. apply ev_add; [reflexivity | lia | lia]. }
    assert (HK2 : know_ok asegs (Eseed R2 (wenv_vals w ++ Xs)) m2 []) by apply Forall_nil.
    pm_goR0 HHp MI2 KR2 VIS2 RF2 HT2 Xs (@nil kentry) HK2 40%nat [AASAN_MEMCPY] [false] 42%N RT_P1A.
    { split_scs. cbn [sc_denot].
      assert (YA : edenot (Eseed R2 (wenv_vals w ++ Xs)) (EAlu ALU_AND (EVar 41) (ELit 3)) = Z_to_bv 64 0).
      { change (edenot (Eseed R2 (wenv_vals w ++ Xs)) (EAlu ALU_AND (EVar 41) (ELit 3)))
          with (alu64 ALU_AND (edenot (Eseed R2 (wenv_vals w ++ Xs)) (EVar 41)) (edenot (Eseed R2 (wenv_vals w ++ Xs)) (ELit 3))).
        ev_xs. change (edenot (Eseed R2 (wenv_vals w ++ Xs)) (ELit 3)) with (Z_to_bv 64 3).
        rewrite w_and by lia. f_equal. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. exact E4. }
      rewrite YA. change (edenot (Eseed R2 (wenv_vals w ++ Xs)) (ELit 0)) with (Z_to_bv 64 0).
      rewrite br_ne by lia. reflexivity. }
    intros msF3 mo3 R3 KR3 MP3 VIS3 RF3 MI3 HT3 HR3 Hlf3.
    subst SSr. cbn [s_pc s_log] in VIS3, MI3. change (mem_denot _ m2 []) with m2 in VIS3, MI3.
    assert (G1_3 : PropExec.getr R3 1%bv = Z_to_bv 64 0xf1940) by rtf HT3.
    assert (G2_3 : PropExec.getr R3 2%bv = Z_to_bv 64 (wa_s1 w)) by rtf HT3.
    assert (G10_3 : PropExec.getr R3 10%bv = Z_to_bv 64 e) by rtf HT3.
    assert (G11_3 : PropExec.getr R3 11%bv = Z_to_bv 64 (wa_ff w + 112)).
    { rewrite (rt_get w Xs R3 RT_P1A 11%bv E912 HT3 eq_refl). unfold E912. apply ev_add; [reflexivity | lia | lia]. }
    assert (G12_3 : PropExec.getr R3 12%bv = Z_to_bv 64 20) by rtf HT3.
    destruct Ccs2 as ((CW & CBS) & _).
    rewrite (rfull_eq R3 RF3) in VIS3.
    eapply (ahh_evt_then H HHp); [exact KR3 | exact VIS3 | |].
    { eapply (ah_memcpy H HHp) with (src := cells_bytes cs) (junk := jA) (lo := wa_lo w);
        rewrite ?G10_3, ?G11_3, ?G12_3, ?G2_3; rewrite ?u64_of_Z by lia.
      - exact CBS.
      - rewrite (cells_bytes_length cs CW), Hcs. reflexivity.
      - exact CBA.
      - lia.
      - eapply addressable_accessible; [exact (ff_addressable m2 (wa_ff w) ins 112 20 FSH2 Hobj) | lia | lia | lia].
      - eapply addressable_accessible; [exact ADB | lia | lia | lia].
      - apply (ff_shvis m2 (wa_ff w) ins 112 20 FSH2); lia.
      - eapply shvis_sub; [exact (ah_blk_shvis H HHp _ _ _ _ _ _ RH2 INL) | lia | lia | lia | lia | lia].
      - exact STK2.
      - lia.
      - unfold AINTRIN_STACK. lia.
      - exact MI2.
      - exact ACm2.
      - lia.
      - eapply aapp_in_app_mem; [exact XG6 | lia | lia].
      - eapply aapp_in_app_mem; [exact RAPP | lia | lia].
      - eapply aconst_ok_app; [exact RAPP | lia | lia].
      - left; lia.
      - left; lia. }
    intros msF4 mo4 KR4 MP4 POST.
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m4
                      & VIS4 & MU4 & WM4 & MI4 & ST4 & CB4 & SB4 & ACm4).
    rewrite G10_3, G12_3, G2_3, ?u64_of_Z in MU4 by lia. rewrite G10_3, G12_3, ?u64_of_Z in CB4 by lia.
    rewrite G2_3, u64_of_Z in ST4 by lia. unfold AINTRIN_STACK in MU4.
    rewrite G1_3, (ret_pc_even 0xf1940 ltac:(lia) ltac:(reflexivity)) in VIS4.
    match goal with H0 : as_VIS H s msF4 = MS ?RR _ _ _ _ _ _ |- _ => set (R4 := RR) in VIS4 end.
    assert (RF4 : rfull R4) by apply rfull_mkR.
    assert (KP3 : forall r, In r VP1_KEPT -> PropExec.getr R3 r = PropExec.getr R r).
    { intros r Hr. rewrite (HR3 r). unfold VP1_KEPT in Hr.
      repeat (destruct Hr as [<-|Hr]; [first [ rewrite G2; reflexivity | rewrite G9; reflexivity
                                              | rewrite G21; ev_xs; reflexivity
                                              | rewrite G23; apply ev_add; [ev_xs; reflexivity | lia | lia]
                                              | rewrite G26; unfold E912; apply ev_add; [reflexivity | lia | lia]
                                              | exact (KEEP2 _ ltac:(inb)) ] |]); destruct Hr. }

    assert (DM2 : forall x, m x <> None -> m2 x <> None).
    { apply (annot_dm m m2 b (20 * cap) (cc_gen (20 * cap) (20 * n + 20)) (wa_lo w) (wa_s1 w - 4096) (wa_s1 w) MU2 SH2);
        [rewrite cc_gen_length by lia; reflexivity | exact STK2 | lia | lia | lia | lia]. }
    assert (DM4 : forall x, m2 x <> None -> m4 x <> None).
    { intros x Hx. destruct (outside_dec [(e, e + 20); (wa_s1 w - 4096, wa_s1 w)] (bv_unsigned x)) as [Ho|(a0 & b0 & Hin & Hr)].
      - rewrite (MU4 x Ho). exact Hx.
      - rewrite <- (Z_to_bv_bv_unsigned x). destruct Hin as [Hin|[Hin|[]]]; injection Hin as <- <-.
        + destruct CB4 as ((_ & (_ & _ & BA)) & _).
          assert (Li : (Z.to_nat (bv_unsigned x - e) < length (cells_bytes [CB (Z.to_nat 20) (cells_bytes cs)]))%nat).
          { cbn [cells_bytes cbytes]. rewrite app_nil_r, (cells_bytes_length cs CW), Hcs. lia. }
          pose proof (BA _ Li) as BAi. rewrite Z2Nat.id in BAi by lia. replace (e + (bv_unsigned x - e)) with (bv_unsigned x) in BAi by lia.
          destruct (nth_error (cells_bytes [CB (Z.to_nat 20) (cells_bytes cs)]) (Z.to_nat (bv_unsigned x - e))) as [bb|] eqn:En.
          * unfold wa in BAi. apply (def_of_mrd_hi m4 (bv_unsigned x) bb); [lia | exact BAi].
          * apply nth_error_None in En. lia.
        + apply (stk_defined m4 (wa_lo w) (wa_s1 w)); [exact ST4 | unfold AIMG_TOP in *; lia | lia | lia]. }

    assert (SLOT : forall k ex, In (k, ex) tbl -> 0 <= k -> k + 8 <= 832 ->
                     rw_cells asegs m4 (wa_s1 w + k) [C8 (edenot (Eseed bvmap_empty (wenv_vals w)) ex)]).
    { intros k ex Hin Hk0 Hk8. unfold slots_ok in SLOTS. rewrite Forall_forall in SLOTS.
      pose proof (SLOTS (k, ex) Hin) as S0. cbn [fst snd] in S0.
      eapply rw_cells_transport; [| exact MU4 | exact WM4 |].
      - eapply rw_cells_transport; [exact S0 | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize Z.of_nat].
        split; [lia | split; [lia | exact I]].
      - cbn [disjoint_from cells_size csize]. split; [lia | split; [lia | exact I]]. }
    assert (ADP4 : addressable m4 (wa_p w) 288).
    { eapply addressable_transport; [| exact MU4 | exact WM4 |].
      - eapply addressable_transport; [exact ADP | exact MU2 | exact WM2 |]. cbn [disjoint_from].
        split; [lia | split; [lia | exact I]].
      - cbn [disjoint_from]. split; [lia | split; [lia | exact I]]. }
    assert (WRP4 : wr_at asegs m4 (wa_p w) 288).
    { pose proof (wr_at_of_mdef m (wa_p w) 288 0 288 PDEF ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as W0.
      rewrite Z.add_0_r in W0. exact (wr_at_wmono _ _ _ _ (wr_at_wmono _ _ _ _ W0 WM2) WM4). }
    set (E4x := Eseed R4 (wenv_vals w ++ Xs)).
    pose proof (env_world_seed H w R4 Xs) as HE4. fold E4x in HE4.
    pose proof (ev_world_all H w _ HE4) as (EV32 & EV33 & _ & EV35 & _).
    assert (HT4 : regs_tblX w Xs R4 RT_P1B).
    { unfold regs_tblX, RT_P1B. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - transitivity (PropExec.getr R3 2%bv); [reflexivity | rtf HT3].
      - transitivity (PropExec.getr R3 9%bv); [reflexivity | rtf HT3].
      - transitivity (PropExec.getr R3 23%bv); [reflexivity | rtf HT3]. }
    assert (HK4 : know_ok asegs E4x m4 KN_P1B).
    { unfold know_ok, KN_P1B. apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]].
      - apply (kshadow0 E4x m4 (EAlu ALU_ADD (EVar 32) (ELit 224)) (wa_p w + 224)); [apply ev_add; [exact EV32 | lia | lia] | lia |].
        apply (sh0_of_addressable m4 (wa_p w) 288); [exact ADP4 | change (8 * (288 / 8)) with 288; lia].
      - apply (kslot_of_cells H w E4x m4 464 ESH224 OK HE4 eq_refl); [apply SLOT; [exact H464 | lia | lia] | lia | lia].
      - apply (kslot_of_cells H w E4x m4 448 E896 OK HE4 eq_refl); [apply SLOT; [exact H448 | lia | lia] | lia | lia].
      - assert (EZ : elenZ E4x (ELit 288) = 288) by (apply elit_u; lia).
        apply (kwr_of_wr_at asegs E4x m4 (wa_p w) 288); [exact WRP4 | | | ];
          rewrite ?(estart_p H w E4x 0 OK HE4), ?EZ; lia. }
    pm_goR0 HHp MI4 KR4 VIS4 RF4 HT4 Xs KN_P1B HK4 40%nat [0xf1970] (@nil bool) 42%N RT_P1E.
    { pose proof (shaddr_bounds (wa_p w + 224) ltac:(lia)) as SB224.
      split_scs. all: first
        [ eapply (sc_flat_lit asegs _ _ _ _ (wa_p w + 224) 8); [apply (estart_var _ 32 224 (wa_p w) EV32); lia | apply elit_u; lia | lia | lia | lia]
        | eapply (sc_flat_lit asegs _ _ _ _ (wa_s1 w + 448) 8); [apply (estart_var _ 35 448 (wa_s1 w) EV35); lia | apply elit_u; lia | lia | lia | lia]
        | eapply (sc_flat_lit asegs _ _ _ _ (wa_s1 w + 464) 8); [apply (estart_var _ 35 464 (wa_s1 w) EV35); lia | apply elit_u; lia | lia | lia | lia]
        | eapply (sc_flat_lit asegs _ _ _ _ ((wa_p w + 224) / 8 + SHBASE) 1);
            [apply (estart_sh _ _ (wa_p w + 224)); [apply ev_add; [exact EV32 | lia | lia] | lia] | apply elit_u; lia | lia | lia | lia] ]. }
    intros msF5 mo5 R5 KR5 MP5 VIS5 RF5 MI5 HT5 HR5 Hlf5.
    lazymatch type of VIS5 with _ = MS _ _ _ _ _ ?mm _ => set (m5 := mm) in * end.
    pose proof (munch_sym E4x m4 _ [(EVar WV_P, 224, 232)] Hlf5 ltac:(vm_compute; reflexivity)) as MU5.
    cbn [num_wins map] in MU5. rewrite (ev_p H w E4x OK HE4) in MU5. fold m5 in MU5.
    subst SSr. cbn [s_pc] in VIS5.
    assert (Y41 : edenot E4x (EAlu ALU_ADD (EVar 41) (ELit 20)) = Z_to_bv 64 (e + 20)).
    { apply ev_add; [subst E4x; ev_xs; reflexivity | lia | lia]. }
    assert (RW5 : rw_cells asegs m5 (wa_p w + 224) [C8 (Z_to_bv 64 (e + 20))]).
    { subst m5. cbn [s_log].
      apply (rw_cells_mem_denot_w E4x m4 [] (SA (EVar 32) 224) 8 (EAlu ALU_ADD (EVar 41) (ELit 20)) [] (wa_p w + 224) (C8 (Z_to_bv 64 (e + 20))));
        [exact Hlf5 | apply Forall_nil | rewrite (estart_var _ 32 224 _ EV32); lia
        | apply (wr_at_sub asegs m4 (wa_p w) 288); [exact WRP4 | lia | lia | lia] | reflexivity | exact I | rewrite Y41; reflexivity]. }
    assert (MUA : munch ([(sh b, sh b + nsh (20 * cap)); (e, e + 20); (wa_p w + 224, wa_p w + 232)] ++ [(wa_s1 w - 4096, wa_s1 w)]) m m5).
    { eapply munch_weaken; [| exact (munch_app _ _ _ _ _ MU2 (munch_app _ _ _ _ _ MU4 MU5))].
      intros x Hx. cbn [outside app] in Hx |- *. destruct Hx as (N1 & N2 & N3 & N4 & _).
      repeat split; first [exact N1 | exact N2 | exact N3 | exact N4]. }
    assert (WMA : wmono asegs m m5) by exact (wmono_trans _ _ _ _ WM2 (wmono_trans _ _ _ _ WM4 (wmono_mem_denot _ _ _))).
    assert (X5 : PMXAT H LINV w s LB LBs m5 mo5 (set_v1A c (b, n + 1, cap)) ins tbl ftbl TB spal).
    { replace (b, n + 1, cap) with (t3a (c_v1 c), n + 1, t3c (c_v1 c)) by (rewrite EV1; reflexivity).
      eapply (pmxa_vupd1 H HHp LINV LINV_frame w s LB LBs m mo c ins tbl ftbl TB spal m5 mo5);
        [exact OK | exact X | exact Hknn | exact Hfk | exact MUA | exact WMA
        | intros x Hx; apply mem_denot_defined; apply DM4; apply DM2; exact Hx
        | exact (ah_mpres_trans H HHp _ _ _ MP2 (ah_mpres_trans H HHp _ _ _ MP3 (ah_mpres_trans H HHp _ _ _ MP4 MP5)))
        | exact MI5 | apply stk_mem_denot; exact ST4 | | | |].
      - unfold vwin, blkV1. rewrite EV1. cbn [t3a t3c fst snd]. unfold OPND_SZ, O_V1.
        apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]; cbn [fst snd].
        + split; [lia|]. right; right. split; [lia | lia].
        + split; [lia|]. right; left. split; [lia | lia].
        + split; [lia|]. left. lia.
      - apply Forall_cons; [| apply Forall_nil]. unfold swin. cbn [fst snd]. lia.
      - rewrite EV1. cbn [t3a t3c fst snd]. unfold vec_opnd, OPND_SZ, O_V1.
        split; [exact Hv|]. split; [exact Hv'|].
        split; [intros i Hi; apply mem_denot_defined; apply DM4; apply DM2; apply HD; lia|].
        split; [lia|]. split; [right; repeat split; assumption|].
        split; [| split].
        + eapply (fld_munch _ m m5); [exact F0 | exact MUA | cbn [disjoint_from app]; repeat split; lia | lia | lia].
        + replace (wa_p w + 216 + 8) with (wa_p w + 224) by lia. replace (b + 20 * (n + 1)) with (bv_unsigned (Z_to_bv 64 (e + 20))) by (rewrite u64_of_Z; lia).
          apply fld_of_cell8; [exact RW5 | lia].
        + eapply (fld_munch _ m m5); [exact F2 | exact MUA | cbn [disjoint_from app]; repeat split; lia | lia | lia].
      - rewrite EV1. unfold vsh_opnd. cbn [t3a t3b t3c fst snd]. intros _. unfold OPND_SZ.
        replace (20 * (n + 1)) with (20 * n + 20) by lia.
        eapply SHAD_transport; [| exact MU5 | apply wmono_mem_denot |].
        + eapply SHAD_transport; [exact SH2 | exact MU4 | exact WM4 |]. rewrite cc_gen_length by lia. cbn [disjoint_from].
          split; [lia | split; [lia | exact I]].
        + rewrite cc_gen_length by lia. cbn [disjoint_from]. split; [lia | exact I]. }
    eapply (K msF5 mo5 m5 R5 KR5 VIS5 RF5 X5).
    - intros r Hr. rewrite (HR5 r). pose proof (KP3 r Hr) as K3. unfold VP1_KEPT in Hr.
      repeat (destruct Hr as [<-|Hr]; [first [ rewrite G2; reflexivity | rewrite G9; reflexivity
                                              | rewrite G23; exact Y41
                                              | exact K3 ] |]); destruct Hr.
    - rtf HT5.
    - rtf HT5.
    - apply (ffkeep_munch w _ m m5 MUA WMA). cbn [app].
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]]; cbn [fst snd]; lia.
  Qed.
End VP1.
