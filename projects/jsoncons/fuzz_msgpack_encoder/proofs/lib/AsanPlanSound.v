(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: changed A_bytes_app, A_bytes_fm_here, A_bytes_fm_split and 247 more; added rz; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/AsanPlanSound.v, 2145 lines within its lines 47-4431. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BackingAlgebra. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.DivergeSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.AsanPlacement OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BackingAlgebra.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AsanPlan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_AsanPlanSound () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9Morphisms:forall_defC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List7existsbC46Stdlib5Lists4List8nil_consC46Stdlib5Lists4List8map_consC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List7map_mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_modI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundc59OSSVerify5KrLib=AsanPlanSound3APS8pagedownC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00c59OSSVerify5KrLib=AsanPlanSound3APS6pageupC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z7mod_mulK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subC46Stdlib5Lists4List2InC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23linC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX2;pt_get_leafC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00c59OSSVerify5KrLib=AsanPlanSound3APS7hole_okC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=Forall_forallC69OSSVerify5KrLib7Mh_01128AsanPlan2AP7is_holeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C45stdpp9bitvector;definitions;bv_unsignedC47Corelib4Init9Datatypes3sndK47Corelib4Init5Logic3and01C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7am_baseC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS2uEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP6am_lenC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula06I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01128AsanPlan2AP4amap00C1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00C69OSSVerify5KrLib7Mh_01128AsanPlan2AP3KHIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC7is_holeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic9False_indK47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01c59OSSVerify5KrLib=AsanPlanSound3APS6allow1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List;in_flat_mapC49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powc59OSSVerify5KrLib=AsanPlanSound3APS5sh_loC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS5sh_hiC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS;pagedown_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS9pageup_geC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegc59OSSVerify5KrLib=AsanPlanSound3APS<pagedown_modC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS:pageup_modC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP:shadow_offC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05c59OSSVerify5KrLib=AsanPlanSound3APS6allowAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct4A_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP5a_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7a_ghostC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appK47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeI69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01128AsanPlan2AP3acs00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03C45stdpp9bitvector;definitions7Z_to_bvK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib7Mh_00438AgentLib7u64_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9page_baseC4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesC46Stdlib5Lists4List>existsb_existsC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6leb_lec59OSSVerify5KrLib=AsanPlanSound3APS<page_base_leC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_or_appI47Corelib4Init9Datatypes6option00i59OSSVerify5KrLib=AsanPlanSound3APS5cs_ok00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS3hidC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbC46Stdlib4Bool4Bool=orb_false_iffc59OSSVerify5KrLib=AsanPlanSound3APS3visC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool>negb_false_iffC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC69OSSVerify5KrLib7Mh_01128AsanPlan2AP6img_hiC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS8co_lazybC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APSEpage_in_ranges_boundsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP6img_loC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS7in_hullC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsc59OSSVerify5KrLib=AsanPlanSound3APS6in_ivsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC46Stdlib4Bool4Bool8orb_propC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltc59OSSVerify5KrLib=AsanPlanSound3APS6in_visC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS5in_shC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2ex01C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC47Corelib4Init9Datatypes?andb_true_introK47Corelib4Init5Logic2or02C59OSSVerify5KrLib7Mh_00368AsanAcct:lazy_coverC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct=page_allowedbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS8in_allowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP4CEILC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00c59OSSVerify5KrLib=AsanPlanSound3APS7hull_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC46Stdlib4Bool4Bool>andb_false_iffC56Stdlib6ZArith6BinInt1Z6ltb_geC46Stdlib4Bool4Bool=negb_true_iffC59OSSVerify5KrLib7Mh_00368AsanAcct>H_off_segmentsC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib7Mh_00368AsanAcct;munrestrictC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityI4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00C59OSSVerify5KrLib7Mh_00368AsanAcctEsame_but_materializedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcctKsame_but_materialized_frameC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdC4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State6m_timeC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State7m_pipesC4ELinuxProcessSemantics?LinuxProcessSem5State7m_stdinC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State5m_tidC4ELinuxProcessSemantics?LinuxProcessSem5State=m_rlimit_coreC4ELinuxProcessSemantics?LinuxProcessSem5State7m_clockC59OSSVerify5KrLib7Mh_00368AsanAcct:eager_usedC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00I4ELinuxProcessSemantics?LinuxProcessSem5State;InputStream00c59OSSVerify5KrLib=AsanPlanSound3APS8vis_sameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS7vis_extC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00368AsanAcct4MInv00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26s_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25s_logC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS2MrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26s_knowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7with_ssC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP4a_ssC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP2knC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP4a_fdC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS6fds_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP8a_tidsetC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC69OSSVerify5KrLib7Mh_01128AsanPlan2AP6a_mapsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS:maps_matchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP5a_yloC1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib=AsanPlanSound3APS4seps00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebra<model_ivs_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7am_kindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS8amap_denC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS9sum_sizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7a_totszC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseC59OSSVerify5KrLib7Mh_0037=AsanPlacement<ledger_splitC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC69OSSVerify5KrLib7Mh_01128AsanPlan2AP5a_brkC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC69OSSVerify5KrLib7Mh_01128AsanPlan2AP7a_eagerC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct7A_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP8a_abytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS8in_ghostC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01c59OSSVerify5KrLib=AsanPlanSound3APS8hid_sameC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry02c59OSSVerify5KrLib=AsanPlanSound3APS4fds3C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupc59OSSVerify5KrLib=AsanPlanSound3APS4flenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init3Nat3addC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22ebC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS5chunkC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebra6ivs_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00238AsanCeil:init_sp_okC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib=AsanPlanSound3APS5cs_ok01C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX29sym_state00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26sentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01128AsanPlan2AP5mkind00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP5mkind03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP5mkind04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP5mkind02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0037=AsanPlacement;kHighMemBegC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01128AsanPlan2AP3afd00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS7fds_stdC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry06C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6filterC46Stdlib5Lists4List9filter_InI69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP6set_knC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP3regC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX29split_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP;live_vars_tC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP=kn_gc_entry_tC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS7co_knowC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS>know_ok_filterC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS<cs_ok_set_knC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP5cs_gcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX2:itab_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2APBmk_itab_ranges_accC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX2<mk_itab_fuelC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX2Bmk_itab_fuel_soundC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24itabC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25ptree01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26pt_getC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX2:itab_entryC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX2;itab_lookupC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APSHmk_itab_ranges_acc_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP>mk_itab_rangesC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib7Numbers7BinNums8positive00C69OSSVerify5KrLib7Mh_01128AsanPlan2AP2pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP8drop_ixsC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbc59OSSVerify5KrLib=AsanPlanSound3APS=drop_ixs_inclC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS;kfoot_apartC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC49OSSVerify5KrLib8PropExec7rdn_extC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S6estartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S5elenZC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC59OSSVerify5KrLib?AxSymExec3Sound4AX2S6flat_uC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry03C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3nthK69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses9and_morphC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atC59OSSVerify5KrLib7Mh_00387StoreOk<store_ok_allC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC59OSSVerify5KrLib7Mh_00387StoreOk?store_ok_of_allC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry09C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC46Stdlib9micromega;ZifyClasses5mkrelC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z8inj_succI69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZK69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3lebC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX2>ranges_apart_xC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat6leb_leC59OSSVerify5KrLib?AxSymExec3Sound4AX2SDranges_apart_x_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS9elenZ_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP>kentry_apart_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25two64C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APSBkentry_apart_b_semC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS?kentry_keep_semC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APSAkentry_apart_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28mk_sprepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX2>ranges_apart_pC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2SAranges_apart_p_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP?kentry_apart_bpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP5kwr_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX29kzero_cutC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX29kfill_cutC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28kunk_cutC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APSBkentry_apart_bp_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7havoc1pC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP6havoc1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List?Forall_flat_mapC59OSSVerify5KrLib7Mh_00387StoreOk=store_ok_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S:Forall_oneC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S?kzero_cut_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S?kfill_cut_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S>kunk_cut_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS:havoc1p_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP8kn_havocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7zf_kindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS7pw_kindC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC59OSSVerify5KrLib?AxSymExec3Sound4AX2S7u_smallC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC47Corelib4Init5Logic3iffI47Corelib7Numbers7BinNums1N00C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24kcutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S3eqmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9u_add_eqmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S8eqm_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9eqm_u_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7eqm_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9eqm_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S;mkAlu_denotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX27lin_ge0C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:Forall_appC59OSSVerify5KrLib?AxSymExec3Sound4AX2S=lin_ge0_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S6xt_denC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9u_sub_eqmC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega7EnvRing5PExpr06C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26a_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25a_offC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2K47Corelib5Lists7ListDef6Forall02C56Stdlib6ZArith6BinInt1Z7add_0_rC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25mkAluC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop02C59OSSVerify5KrLib?AxSymExec3Sound4AX2S6u_lit0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS=kcut_pw_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS:pw_kind_wrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7kwr_cutC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP8cutout1pC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7cutout1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS=kwr_cut_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS;cutout1p_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP9kn_cutoutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk>mem_grows_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS=know_ok_havocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP>node_droprangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP9node_bumpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP3nxtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP4bumpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24s_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26s_nextC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP5mk_ssC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP3acs01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC47Corelib4Init3Nat3subC69OSSVerify5KrLib7Mh_01128AsanPlan2AP9mkind_eqbC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP5mkind01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP5mkind05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP5mkind06C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX29saddr_eqbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28expr_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S<saddr_eqb_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S;expr_eqb_eqC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat6eqb_eqC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC69OSSVerify5KrLib7Mh_01128AsanPlan2AP:kentry_eqbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP8amap_eqbC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4amap01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS<mkind_eqb_eqC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC4amap01C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC4amap00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC5mkind00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP8pair_eqbC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP3afd02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC3afd02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7afd_eqbC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP3afd01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP3afd03C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC3afd00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP8list_eqbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS;list_eqb_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC8list_eqbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP9kimg_clipC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS<kimg_in_hullC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics;memory_readC59OSSVerify5KrLib7Mh_00368AsanAcctCmemory_read1_hiddenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C49OSSVerify5KrLib8PropExec6u_add1C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC47Corelib4Init9Datatypes7nat_indc59OSSVerify5KrLib=AsanPlanSound3APS;rdn_visibleC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool<orb_true_iffC46Stdlib4Bool4Bool=andb_true_iffc59OSSVerify5KrLib=AsanPlanSound3APS=in_allow_consC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS8vis_monoC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool:orb_true_rC46Stdlib5Lists4List;existsb_appC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedI46Stdlib5Lists4List5NoDup00c59OSSVerify5KrLib=AsanPlanSound3APSCpage_allowedb_app_rC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00368AsanAcct4MInv01C1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib7Classes?RelationClasses>iff_TransitiveC45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC56Stdlib6ZArith6BinInt1Z7add_0_lK69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_rC49OSSVerify5KrLib8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedC49OSSVerify5KrLib8PropExec7alu_addC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr08C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop04K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop08K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I4ELinuxProcessSemantics5Riscv5Instr5aluop00I4ELinuxProcessSemantics5Riscv5Instr5mulop00C69OSSVerify5KrLib7Mh_01128AsanPlan2AP6flat_xC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX2:base_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23xloC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23xhiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S@base_range_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9xlo_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9xhi_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS?split_lit_denotC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC69OSSVerify5KrLib7Mh_01128AsanPlan2AP6no_fogC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP6is_fogC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpI69OSSVerify5KrLib7Mh_01128AsanPlan2AP6spiece00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS;in_ivs_trueC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS=maps_match_InC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP;is_tok_kindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS?filter_all_trueC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX29aluop_eqbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX29mulop_eqbC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_reflC56Stdlib5Arith8PeanoNat3Nat8eqb_reflc59OSSVerify5KrLib=AsanPlanSound3APS?aluop_eqb_refl'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS?mulop_eqb_refl'C1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool3eqbC46Stdlib4Bool4Bool9eqb_reflxC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28expr_indC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS>expr_eqb_refl'C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:map_removeC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC49OSSVerify5KrLib8PropExec:bv_eqb_neqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS;amap_eqb_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APSAmap_remove_notin'C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS>amap_eqb_refl'C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6in_mapc59OSSVerify5KrLib=AsanPlanSound3APSDexistsb_false_forallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7vis_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP;vis_add_refC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP:vis_add_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP9shadow_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP<expr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP8vis_costC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS<flat_x_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS:u_of_splitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS<hid_cons_subC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APSCpageup_pagedown_gapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP?find_containingC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9find_someC46Stdlib4Bool4Bool;orb_false_rC59OSSVerify5KrLib?AxSymExec3Sound4AX2S=xinside_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS7co_mapsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS9co_boundsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25mkSrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7u_srl64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S;mkSrl_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7u_add64C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9mod_smallc59OSSVerify5KrLib=AsanPlanSound3APSAin_ivs_maps_matchC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS8co_kindsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_gtC46Stdlib5Lists4List>forallb_forallc59OSSVerify5KrLib=AsanPlanSound3APS7co_zeroC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP<shadow_factsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS;A_bytes_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS8MInv_appC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26ealignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX27xinsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP4eaddC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS9shadow_okC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS4ext1C1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS?expr_vars_lt_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP=saddr_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3=saddr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP>kentry_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3>kentry_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP:kn_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3:kn_vars_ltC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APSAkentry_vars_lt_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP:sr_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3:sr_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<edenot_agreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS=kn_vars_lt_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3=know_ok_agreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS=sr_vars_lt_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3=regs_ok_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP5shape02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP=shape_vars_ltC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS2sdC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS2WpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS9piece_denC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP6spiece01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP6spiece02C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<flat_map_extK4ELinuxProcessSemantics?LinuxProcessSem5State5event02K69OSSVerify5KrLib7Mh_01128AsanPlan2AP5shape03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg6t_alt2C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP5shape04C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS=edenot_agree'C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP5shape05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP5shape06C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP9shape_indC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01128AsanPlan2AP5shape00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg5t_nilC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP5shape01C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00K69OSSVerify5KrLib7Mh_01128AsanPlan2AP5shape07C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5event03C59OSSVerify5KrLib7Mh_00368ShapeAlg>t_emit_has_nilC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS>t_exit_has_nilC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4t_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS:sd_has_nilC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS<t_alt2_nil_lC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS<t_alt2_nil_rC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP5salt2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS:t_eq_refl'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26erangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S<erange_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP9kn_contraC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26lin_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX29lin_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S?lin_range_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S4tdenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S<lin_of_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S4ldenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S2uEC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega5Tauto8GFormula0:K46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_01128AsanPlan2AP4xlo1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26zlit64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX2:lin_brangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX2:lin_srangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7u_lit64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9zlit64_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S@lin_brange_soundC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6PosDef3Pos7compareC47Corelib4Init9Datatypes7CompOppC56Stdlib6ZArith6BinInt1Z8max_specC59OSSVerify5KrLib?AxSymExec3Sound4AX2S@lin_srange_soundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7compareI47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison03K47Corelib4Init9Datatypes:comparison01K47Corelib4Init9Datatypes:comparison02C69OSSVerify5KrLib7Mh_01128AsanPlan2AP4xhi1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specC69OSSVerify5KrLib7Mh_01128AsanPlan2AP5deandC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z;log2_nonnegC56Stdlib6ZArith6BinInt1Z6mod_leC56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega=RingMicromega5Psatz03C59OSSVerify5KrLib?AxSymExec3Sound4AX2S=land_highmaskC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7u_and64C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7sub_0_rC69OSSVerify5KrLib7Mh_01128AsanPlan2AP3xb2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS:xlo1_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS:xhi1_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS;deand_soundC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC69OSSVerify5KrLib7Mh_01128AsanPlan2AP4xlo2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS9xb2_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP4xhi2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP4esubC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7u_sub64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP<residue_factC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7fact_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S<ealign_soundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6divideC56Stdlib6ZArith6BinInt1Z:mod_divideC59OSSVerify5KrLib?AxSymExec3Sound4AX2S>pow2_divide_leC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z<divide_transc59OSSVerify5KrLib=AsanPlanSound3APS:xlo2_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS:xhi2_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS=fact_ok_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP6add_knC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7entailsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS:afd_eqb_eqC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool8eqb_propc59OSSVerify5KrLib=AsanPlanSound3APS7hid_extC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS=kentry_eqb_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS:holes_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS;pair_eqb_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24ridxC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC47Corelib7Classes?RelationClasses=eq_TransitiveC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26sr_getC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS7co_regsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqc59OSSVerify5KrLib=AsanPlanSound3APS8ridx_litC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z<pos_div_euclC56Stdlib6ZArith6BinInt1Z7mod_modC69OSSVerify5KrLib7Mh_01128AsanPlan2AP6lit_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7reg_litC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS<lit_of_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS9reg_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26sr_updC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S;regs_ok_pinC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3;regs_ok_setC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP8fresh_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP=pairs_vars_ltC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List;forallb_appC69OSSVerify5KrLib7Mh_01128AsanPlan2AP<maps_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP:fd_vars_ltC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6concatC46Stdlib5Lists4List:map_ext_inC46Stdlib5Lists4ListCflat_map_concat_mapC46Stdlib4Bool4Bool8negb_orbC46Stdlib4Bool4Bool9negb_andbC46Stdlib4Bool4Bool?negb_involutivec59OSSVerify5KrLib=AsanPlanSound3APS<env_agree_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS>in_allow_agreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS>fresh_ok_partsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS9hid_agreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS<allowA_agreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS>regs_ok_agree'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS>know_ok_agree'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS<fds_ok_agreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS@maps_match_agreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS;holes_agreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS>in_ghost_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP9run_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP=run_block_refC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP<run_block_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS=fresh_ok_monoC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX29sym_state01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3;runTX_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S5st_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9mem_denotC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S8log_flatC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS;cs_ok_agreeC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01c59OSSVerify5KrLib=AsanPlanSound3APSAH_off_segments_csC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS=lazy_cover_csC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS;A_wf_allowAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS7co_minvC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS7co_haltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct6hcleanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S8sc_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S;carry_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APSKmrestrict_munrestrict_cleanC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC59OSSVerify5KrLib7Mh_00368AsanAcct:unrestrictC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS;cs_ok_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0036=AsanAcctShapeGsrz_msteps_restricted_TC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS6cfg_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX2:sym_execTXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25carryC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28sidecond00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C69OSSVerify5KrLib7Mh_01128AsanPlan2AP<run_block_gcC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25ptree00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS8cs_gc_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS8pc_cs_gcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS?run_block_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS6alwaysC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP:node_freshC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3ltbC69OSSVerify5KrLib7Mh_01128AsanPlan2AP6escaleC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat6ltb_ltC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rc59OSSVerify5KrLib=AsanPlanSound3APS:ext1_agreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS>nth_sr_vars_ltC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7mul_divK46Stdlib9micromega7EnvRing3Pol02c59OSSVerify5KrLib=AsanPlanSound3APS7u_smallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7u_mul64C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS7ext1_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24mkMdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S:mkMd_denotC1?~~~~~~~~~~~~~~~C56Stdlib5omega8PreOmega1Z:divide_altC56Stdlib6ZArith6BinInt1Z7mod_0_lC56Stdlib6ZArith6BinInt1Z8sub_diagc59OSSVerify5KrLib=AsanPlanSound3APS:deand_varsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APSBresidue_fact_soundC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4ZdivAZplus_mod_idemp_rc59OSSVerify5KrLib=AsanPlanSound3APS?regs_ok_respellC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS:node1_stmtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7set_regC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01c59OSSVerify5KrLib=AsanPlanSound3APS:fresh_stmtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP9listZ_eqbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP:spiece_eqbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP;spieces_eqbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS<listZ_eqb_eqC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC6spiece01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC6spiece02C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC6spiece00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC5shape02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP9shape_eqbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS>spieces_eqb_eqC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC5shape03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC5shape05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC5shape06C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC5shape00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP9find_disjC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP>disj_side_factC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP5eaddzC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP=node_casedisjC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS?find_disj_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APSDdisj_side_fact_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP;node_shdisjC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP?node_shdisj_refC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP>node_shdisj_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS=shadow_of_valC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_mulc59OSSVerify5KrLib=AsanPlanSound3APSAexpr_vars_lt_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS8ext_listC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS>env_agree_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS?env_agree_transC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS>ext_list_agreeC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rC56Stdlib6ZArith4Znat5Nat2Z7inj_addC69OSSVerify5KrLib7Mh_01128AsanPlan2AP8sr_freshC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List?Forall_cons_iffc59OSSVerify5KrLib=AsanPlanSound3APS?sr_vars_lt_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS>sr_vars_lt_updC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP:node_havocC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS@regs_ok_sr_freshC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APSCkentry_vars_lt_monoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP;kn_bigsubstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP4bigbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS;kn_bigexprsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS@kn_vars_lt_mono'C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7map_nthC69OSSVerify5KrLib7Mh_01128AsanPlan2AP=node_havocbigC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3seqc59OSSVerify5KrLib=AsanPlanSound3APS;havoc_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS>node_havoc_nxtC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_mapc59OSSVerify5KrLib=AsanPlanSound3APS;ext_list_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APSAkn_bigsubst_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS3updC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP6esubstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C4ELinuxProcessSemantics5Riscv7Prelude4sextC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26mkAluwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S<mkAluw_denotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25mkMdwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S;mkMdw_denotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX27ext_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28blob_valC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP6asubstC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS<esubst_denotC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indc59OSSVerify5KrLib=AsanPlanSound3APS=adenot_asubstC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS=estart_asubstC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6or_indC69OSSVerify5KrLib7Mh_01128AsanPlan2AP6ksubstC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS@kentry_ok_ksubstC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7map_appC69OSSVerify5KrLib7Mh_01128AsanPlan2AP6psubstC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7map_extC69OSSVerify5KrLib7Mh_01128AsanPlan2AP6msubstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP6fsubstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP4instC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS<existsb_map'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS9upd_agreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS=inst_in_allowC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC47Corelib7Classes?RelationClasses?iff_equivalenceC47Corelib7Classes?RelationClasses=iff_Reflexivec59OSSVerify5KrLib=AsanPlanSound3APSAmaps_match_msubstC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryc59OSSVerify5KrLib=AsanPlanSound3APS8inst_hidC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS;inst_allowAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS9inst_mapsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS=inst_in_ghostC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS<regs_ok_instC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS>know_ok_ksubstC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS;fds_ok_instC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS<holes_msubstC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:in_map_iffC69OSSVerify5KrLib7Mh_01128AsanPlan2AP<kentry_eqb_hC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP;saddr_eqb_hC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7kflat_hC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS@seg_rom_off_hullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP6cover1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS>rdn_bytes_someC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7cover_xC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8leb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z8ltb_specc59OSSVerify5KrLib=AsanPlanSound3APS<cover1_soundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;lt_ge_casesC69OSSVerify5KrLib7Mh_01128AsanPlan2AP<kunk_coveredC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP;off_image_xC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS=cover_x_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP9kn_incl_hC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP:kn_incl1_hC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP@kimg_sub_coveredC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APSBkentry_eqb_h_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APSBkunk_covered_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS8is_havocC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS4henvC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS>is_havoc_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP<regs_match_hC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3eqbC69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC<regs_match_hC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS6upd_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APSAregs_match_h_charC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S:ridx_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS:henv_havocC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS:henv_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP8set_regsC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses>flip_ReflexiveC69OSSVerify5KrLib7Mh_01128AsanPlan2AP9entails_hC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26s_resvC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS9henv_highC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS?kn_incl_h_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APSBregs_match_h_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS;cs_ok_reenvC1?~~~~~~~~~~~~~~~C47Corelib7Program6Basics4implC47Corelib7Classes?RelationClasses>impl_ReflexiveC69OSSVerify5KrLib7Mh_01128AsanPlan2APAnode_diamond_joinC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS?entails_h_soundC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3maxC69OSSVerify5KrLib7Mh_01128AsanPlan2AP9diff_regsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List5nodupC56Stdlib5Arith8PeanoNat3Nat6eq_decC56Stdlib6ZArith4Znat5Nat2Z7inj_maxC69OSSVerify5KrLib7Mh_01128AsanPlan2AP7loop_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP9check_allC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4cres01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP;init_acs_ofC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4cres02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS<shape_eqb_eqC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9fold_leftI69OSSVerify5KrLib7Mh_01128AsanPlan2AP4cres00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP5checkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP6lc_bndC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP5STOPSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP9node_joinC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7kn_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP;is_ecall_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP8node_sysC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP:node_mmap2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP>node_mprotect2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP9node_brk2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP6node_xC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP7loopctx01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP?loop_body_stateC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP9node_exitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP8node_fogC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP;node_fognewC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP:node_ghostC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP:node_unvisC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP=node_havocbrkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP:node_introC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP<branch_probeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP;node_renameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP<node_compactC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP6via_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2APAnode_abstractcellC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP?node_havocwordsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP<node_respellC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0<C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0=C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0>C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0?C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0@C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0AC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS:salt2_varsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0BC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS<check_all_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0CC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0DC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0EC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0FC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0GC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0HC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0IC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0KC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0NC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0OC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0PC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0QC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0RC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0SC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0TC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0UC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0VC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0WC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0XC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0YC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0ZC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0[C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0\C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP;node_mmapinC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP7loopctx02C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01128AsanPlan2AP7loopctx00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0JC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0LC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan06C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01128AsanPlan2AP5snode00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01128AsanPlan2AP5xnode00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP4plan0MC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP9fog_tokenC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01128AsanPlan2AP<list_set_nthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP?list_insert_nthC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS?In_list_set_nthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC<list_set_nthC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APSBIn_list_insert_nthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC?list_insert_nthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP9with_mapsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APSGlist_set_nth_maps_matchC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS?cs_ok_with_mapsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APSJlist_insert_nth_maps_matchC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APSCpage_allowedb_app_lC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC46Stdlib5Lists4List<flat_map_appC46Stdlib5Lists4List9app_assocc59OSSVerify5KrLib=AsanPlanSound3APS;allow1_costC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS8co_limitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS8co_eagerC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS9co_abytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS:MInv_app_rC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7kzero_xC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP8vis_hereC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes9Morphisms5flip2C69OSSVerify5KrLib7Mh_01128AsanPlan2AP>node_unvis_refC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP=node_unvis_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC4a_ssC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC2knC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC9kn_unfillC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC5mk_ssC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC6a_mapsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC7a_totszC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC5a_yloC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC7a_eagerC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC5a_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC7a_ghostC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC8a_abytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC5a_brkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC4a_fdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC8a_tidsetC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC3acs01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9pow_add_rC56Stdlib6ZArith6BinInt1Z?mul_add_distr_rc59OSSVerify5KrLib=AsanPlanSound3APS>kzero_x_sound0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS;vis_here_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP9kn_unfillC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP6kimg_bC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:filter_extc59OSSVerify5KrLib=AsanPlanSound3APSEA_bytes_allow1_nonnegC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS?A_bytes_fm_hereC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS@A_bytes_fm_splitC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:in_app_iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Classes9MorphismsFsubrelation_respectfulC46Stdlib6ZArith:ZArith_dec8Z_le_decC46Stdlib6ZArith:ZArith_dec8Z_lt_decI69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC3acs00C1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC47Corelib7Classes>Morphisms_Prop?or_iff_morphismc59OSSVerify5KrLib=AsanPlanSound3APS6co_brkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP6nt_getC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP6mk_fwdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP6nt_setC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC6nt_getC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP:nt_get_setC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP6mk_bwdC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS?mk_fwd_spec_genC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS?mk_bwd_spec_genC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS7ren_envC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7erenameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS6ren_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS5bw_inC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS5fw_inC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP9evars_allC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS6eb_renC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP9kvars_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7krenameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS@kentry_ok_renameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS9pvars_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7prenameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS9uE_renameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP9rename_csC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS;existsb_mapC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS>existsb_ext_inC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS9ren_agreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS?in_allow_renameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7mrenameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7frenameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP:csvars_allC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS:hid_renameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS=allowA_renameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS>regs_ok_renameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS>know_ok_renameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS=fds_ok_renameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APSAmaps_match_renameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS<holes_renameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS?in_ghost_renameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS6co_logC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS<cs_ok_renameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP6csmaxvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP;compact_mapC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS<rename_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS>know_ok_cutoutC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS9pc_set_knC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP8hw_applyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP6hw_valC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:Forall_invc59OSSVerify5KrLib=AsanPlanSound3APSBhw_apply_true_varsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APSBhw_apply_true_inclC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP5hw_goC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP5sa_ofC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS;hw_apply_okC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat=add_succ_commc59OSSVerify5KrLib=AsanPlanSound3APS8hw_go_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP:respell_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2SCdecide_branch_soundC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem<branch_takenC4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqC45stdpp9bitvector;definitions6bv_subC45stdpp9bitvector;definitions?bv_sub_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX2=decide_branchC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01c59OSSVerify5KrLib=AsanPlanSound3APS@respell_ok_soundC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5ms_pcC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC4ELinuxProcessSemantics5Riscv3Sem5is_x0C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib7Mh_0037:DivergeSim<is_self_jumpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP9SPIN_WORDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS4LCOKC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS8lc_guardC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS:LCOK_agreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS:check_varsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS8sd_agreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS:cont_agreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS8LCOK_bndC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APSBrun_block_gc_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS;split_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS?kn_contra_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS>casedisj_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS<shdisj_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS:fact_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS<forget_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS?droprange_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS:bump_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS>havocbig_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APSCnode_fresh_sound_pfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS8sd_salt2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg:srz_conseqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS9t_eq_alt2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg:t_eq_transC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS=loop_ok_factsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS:cs_ok_instC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS7pc_instC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS7upd_updC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS=entails_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS9fog_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS<fognew_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS;ghost_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS;unvis_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS>havocbrk_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS;intro_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APSBdiamond_join_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS=LCOK_agree_gbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS=compact_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APSBabstractcell_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS@havocwords_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib=AsanPlanSound3APS=respell_soundC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Module APS.
Import AX2. Import AX2S. Import AP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Local Ltac lia := L5FastLia.plia.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition uE (E : env) (e : expr) : Z := bv_unsigned (edenot E e).

Definition pagedown (z : Z) : Z := z / 4096 * 4096.
Definition pageup (z : Z) : Z := (z + 4095) / 4096 * 4096.

#[using="Type"] Lemma pagedown_le : forall z, pagedown z <= z.
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
ltac2:(KReplay.run1 (kr_t_AsanPlanSound ()) ["FPX_1"] "h04__p1h14__x1h24__x2h34__x3h41Hh52H0h62H1h72H2h82H3h97__arithh:4__ffh;6__sat0h<8__varmaph=5__with>1qh?1rh@1zp;1p;2p;3p;4p;6p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p7210p9P0p1002Qp4p710p9P0p10038p4p710R1p9P0p1003Vp4p710p9P0p1004Np4p710p8P0p1004ep4p710p8P0p1005FR2p4p710p8P0P2p4p7210p8P0p1005cp4p710p8p1006?p4p710P1p8p1006\p4p7210R0p10079p4p710p8P0P1p8p1007Up4p7210P1p8p10082p4p73110P1p8g008Nj17Tg0093j1PTg009Qj2GTg00:Bj20Tg00:^j2<Tg00;;j2VTg00;\j31Tg00<6j1MTg00<Oj2:Tg00<lj25Tg00=Lj2ATg00=ij2DTg00>Pj24Tg00>lj2=Tg00?Gj2]Tg00?nj2YTg00@Tj2WTg00A:j1BTg00AYj2;Tg00BBj1UTg00B`j2TTg00CAj3OTg00Cjj3@Tg00DSj2NTg00E?j1LTg00E_j3KTg00F?j1ITg00F_j2>Tg00G=j4HTg00G[j1JTg00H9j1FTg00Hdj2?Tg00IGj42Tg00J2j1ETg00JTj1QTg00K9j29Tg00K\j6RTg00L@j7STg00Ldj6cTg00MHj3CTg00Mkj3bTg00NNj2aTg00O0j2`Tg00OJj2\Tg00P6j3ZTg00PUj4[Tg00QGj1XTg00RFj7^Tg00Rjj8_Tf0R1#7#7p=3f1R0g00SNR2g00SmR3P3g00TMR4P1g00TmF^p=6f3R5P2P3P3P4f2R6P0P1G_p=8g00UMR7g00UkR8#7R9#7#3#3#3#3#3#PR:,G1g00VPR;/0110;:1<6:R<,0;[[1V0:A17:;R=#M1::<156:'A9176[1D6:14;:R<155:R>,0;14>:'=[1]5:14:;f4R>/5:R?,4:10?;'=[1Y>:f5R?/<:=17;\=1W?:f6R@/5:=17@\=1<@:P7f7RA/5:P7p-0RBg00VnRCg00WZRD#BRE#B,;7%U8,T71;7E5O71;7D5@75@7g00X9'N%LC3K%ICP71>76P01>75CH%J7%F7RCPCP71?7;RDg00Xe1?7:REC2,6C%E3RFPCP2P3P3P4P7PDg00YLRG%Q8,97RHC2,6CPCP2P3P3P4P?ERFSC8PFPCPCPCP2P3P3P4P7PEg00Z3R3PDC2,6CEcPFP71979R9P31978R89C7E=b7HC2,6CC8PFP7AC78EPGP9C2,6CC8C81aC4P1P6g00ZZRCg00[:R4'`1\16=1C4dAZ7;0C[b:b<b=X17X27X37W010;5/=>\<g00[Z\=1::6/A>9175[1:6:/05[[^17^27^37^0BP1140:P0f9P6P@PAO6b9b?b>b8b7b6b5b4b;%X1/01eW@o"). Qed.
End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section FPX_2. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

#[using="Type"] Lemma pageup_ge : forall z, z <= pageup z.
Proof. intros z. unfold pageup. lia. Qed.
#[using="Type"] Lemma pagedown_mod : forall z, pagedown z mod 4096 = 0.
Proof. intros z. unfold pagedown. rewrite Z.mod_mul. reflexivity. lia. Qed.
#[using="Type"] Lemma pageup_mod : forall z, pageup z mod 4096 = 0.
Proof. intros z. unfold pageup. apply Z.mod_mul. lia. Qed.
#[using="Type"] Lemma pageup_minus_pagedown : forall a b, a <= b -> pageup b - pagedown a <= b - a + 8192.
Proof. intros a b H. unfold pageup, pagedown. lia. Qed.
End FPX_2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_3. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
Definition in_ivs (z : Z) (l : list (word * word)) : bool :=
  existsb (fun iv => (bv_unsigned (fst iv) <=? z) && (z <? bv_unsigned (fst iv) + bv_unsigned (snd iv)))%bool l.

Definition in_hull (A : atable) (z : Z) : bool := ((img_lo A <=? z) && (z <? img_hi A))%bool.

(* [comment removed for export] *)
Definition iv_disjoint (p q : word * word) : Prop :=
  bv_unsigned (fst p) + bv_unsigned (snd p) <= bv_unsigned (fst q)
  \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst p).
Inductive seps : list (word * word) -> Prop :=
| seps_nil : seps []
| seps_cons : forall p l, Forall (iv_disjoint p) l -> seps l -> seps (p :: l).

Fixpoint sum_sizes (l : list (word * word)) : Z :=
  match l with [] => 0 | iv :: r => bv_unsigned (snd iv) + sum_sizes r end.

Definition cfg_of (SEGS : list Segment) (R : bvmap 5 word) (p : Z) (M : word -> option byte) (model : Model) : config :=
  mkCfg (mkst R (Z_to_bv 64 p) M (seg_rom SEGS)) model.

Section Sound.
Context {boffK : BmOff bmK}.   (* [comment removed for export] *)
Variable SEGS : list Segment.
Variable scfg : SpuriousCfg.
Variable IT : itab.
Hypothesis IT_ok : itab_sound SEGS IT.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
(* [comment removed for export] *)
Variable rz : Z.
Variable HS : nat -> option acs.
(* [comment removed for export] *)
Variable XN : nat -> list expr -> acs -> option acs.
Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Variable XON : xnode -> bool.

(* [comment removed for export] *)
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
(* [comment removed for export] *)
Definition res_len_ok : Prop := length (segments_reserved SEGS) = n_res A.
Definition hull_ok : Prop := 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0 /\ img_hi A <= KHI.
Definition shadow_ok : Prop := 0 <= shadow_off A <= 2 ^ 47.
Hypothesis RES_len : res_len_ok.
Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A) (segments_reserved SEGS).
Hypothesis HULL_ok : hull_ok.
Hypothesis SHADOW_ok : shadow_ok.

(* [comment removed for export] *)
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

(* [comment removed for export] *)
Variable HOLES : nat -> env -> Fs.Fs -> TSet.
Hypothesis HOLES_agree : forall h E E' fs, env_agree nx0 E E' -> HOLES h E fs = HOLES h E' fs.
Hypothesis HOLES_nil : forall h E fs, HOLES h E fs [].
(* [comment removed for export] *)
Variable FS0 : Fs.Fs.

(* [comment removed for export] *)
Variable KC : nat.

#[local] Notation CHECK := (AP.check SEGS IT A nx0 LIMIT rz XN XE XB XON HS KC).

#[local] Notation cfg := (cfg_of SEGS).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition Wz (fd : Z) (bs : list Z) : list event := map (fun z => WriteEv (Z_to_bv 64 fd) (Z_to_bv 8 z)) bs.
(* [comment removed for export] *)
Definition piece_den (E : env) (p : spiece) : list byte :=
  match p with SPLit bs => map (Z_to_bv 8) bs | SPBlob k => eb E k end.
Definition Wp (E : env) (fd : Z) (ps : list spiece) : list event :=
  map (WriteEv (Z_to_bv 64 fd)) (flat_map (piece_den E) ps).

(* [comment removed for export] *)
Fixpoint sd (D : TSet) (E : env) (fs : Fs.Fs) (s : shape) : TSet :=
  match s with
  | SNil => t_nil
  | SExit c => t_exit (Z_to_bv 64 c) fs
  | SEmitP fd ps s' => t_emit (Wp E fd ps) (sd D E fs s')
  | SAlt2 a b => t_alt2 (sd D E fs a) (sd D E fs b)
  | SCase e mid s1 s2 => if (bv_unsigned (edenot E e) <=? mid)%Z then sd D E fs s1 else sd D E fs s2
  | SHole h => HOLES h E fs
  | SNext => D
  end.

(* [comment removed for export] *)
Definition sh_lo (E : env) (p : expr * expr) : Z := shadow_off A + uE E (fst p) / 8.
Definition sh_hi (E : env) (p : expr * expr) : Z := shadow_off A + (uE E (fst p) + uE E (snd p)) / 8.

(* [comment removed for export] *)
Definition allow1 (E : env) (p : expr * expr) : list (Z * Z) :=
  [(pagedown (uE E (fst p)), pageup (uE E (fst p) + uE E (snd p))); (pagedown (sh_lo E p), pageup (sh_hi E p))].
Definition allowA (E : env) (cs : acs) : list (Z * Z) := flat_map (allow1 E) (a_vis cs ++ a_ghost cs).

Definition amap_den (E : env) (m : amap) : word * word := (edenot E (am_base m), edenot E (am_len m)).

(* [comment removed for export] *)
Definition in_vis (E : env) (cs : acs) (z : Z) : bool :=
  existsb (fun p => (uE E (fst p) <=? z) && (z <? uE E (fst p) + uE E (snd p)))%bool (a_vis cs).
Definition in_sh (E : env) (cs : acs) (z : Z) : bool :=
  existsb (fun p => (sh_lo E p <=? z) && (z <? sh_hi E p))%bool (a_vis cs).
Definition in_allow (E : env) (cs : acs) (z : Z) : bool := (in_vis E cs z || in_sh E cs z)%bool.

(* [comment removed for export] *)
Definition in_ghost (E : env) (cs : acs) (z : Z) : bool :=
  existsb (fun p => (uE E (fst p) <=? z) && (z <? uE E (fst p) + uE E (snd p)))%bool (a_ghost cs).

(* [comment removed for export] *)
Definition vis (E : env) (cs : acs) (model : Model) (a : word) : bool :=
  let h := m_vmmaps model in
  let z := bv_unsigned a in
  (in_hull A z
   || (CEIL <=? z)
   || (in_ivs z (vm_maps h) && negb (in_ivs z (vm_noaccess h))
       && (negb (page_in_ranges (page_base a) (m_vm_lazy model)) || in_allow E cs z)))%bool.

Definition hid (E : env) (cs : acs) (model : Model) (a : word) : bool :=
  (argH E a || negb (vis E cs model a))%bool.

(* [comment removed for export] *)
Definition Mr (E : env) (cs : acs) (model : Model) (FULL : word -> option byte) : word -> option byte :=
  mrestrict (hid E cs model) FULL.

Definition fds_std : list (word * FdEntry) :=
  [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
   (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].

(* [comment removed for export] *)
Definition CH : nat := Z.to_nat 65536.
Definition chunk (j : nat) (c : list byte) : list byte := firstn CH (skipn (CH * j) c).
Definition flen (c : list byte) : Z := Z.min (Z.of_nat (length c)) (2 ^ 26).
Definition fds3 (e : FdEntry) : list (word * FdEntry) := (Z_to_bv 64 3, e) :: fds_std.
Definition fds_ok (E : env) (f : afd) (model : Model) : Prop :=
  match f with
  | AP.FdStd => m_fds model = fds_std
  | AP.FdDir => m_fds model = fds3 State.FdDir
  | AP.FdFile k len off => exists p c,
        m_fds model = fds3 (State.FdFile p (edenot E off)) /\ fs_lookup (m_fs model) p = Some c
     /\ uE E len = flen c /\ uE E off <= uE E len
     /\ (forall j, (65536 * Z.of_nat j < 2 ^ 26)%Z -> eb E (k + j)%nat = chunk j c)
  end.

(* [comment removed for export] *)
Fixpoint maps_match (E : env) (ms : list amap) (l : list (word * word)) : Prop :=
  match ms with
  | [] => l = []
  | m :: ms' =>
      if is_fog m       (* [comment removed for export] *)
      then maps_match E ms' l
           \/ exists iv l', l = iv :: l' /\ bv_unsigned (snd iv) <= uE E (am_len m) /\ maps_match E ms' l'
      else exists l', l = amap_den E m :: l' /\ maps_match E ms' l'
  end.

(* [comment removed for export] *)
Definition hole_ok (E : env) (ylo : Z) (l : list (word * word)) (m : amap) : Prop :=
  is_hole m = true ->
  (forall iv, In iv l -> bv_unsigned (fst iv) + bv_unsigned (snd iv) <= uE E (am_base m)
                         \/ uE E (am_base m) + uE E (am_len m) <= bv_unsigned (fst iv))
  /\ (uE E (am_base m) + uE E (am_len m) <= KHI \/ ylo <= uE E (am_base m)).
#[using="Type"] Lemma holes_mono : forall E y y' l ms,
  Forall (hole_ok E y l) ms -> y' <= y -> Forall (hole_ok E y' l) ms.
Proof.
  intros E y y' l ms H Hy. apply Forall_forall. intros m Hm Hh.
  destruct (proj1 (Forall_forall _ _) H m Hm Hh) as [H1 H2]. split; [exact H1 | lia].
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma holes_sublist : forall E y l l' ms,
  Forall (hole_ok E y l) ms -> (forall iv, In iv l' -> In iv l) -> Forall (hole_ok E y l') ms.
Proof.
  intros E y l l' ms H Hs. apply Forall_forall. intros m Hm Hh.
  destruct (proj1 (Forall_forall _ _) H m Hm Hh) as [H1 H2]. split; [intros iv Hiv; apply H1; apply Hs; exact Hiv | exact H2].
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma holes_none : forall E y l ms, Forall (fun m => is_hole m = false) ms -> Forall (hole_ok E y l) ms.
Proof. intros E y l ms H. apply Forall_forall. intros m Hm Hh. pose proof (proj1 (Forall_forall _ _) H m Hm) as X. congruence. Qed.

Record cs_ok (E : env) (cs : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model) : Prop := CS_OK {
  (* [comment removed for export] *)
  co_regs  : regs_ok E (s_regs (a_ss cs)) R;
  co_log   : s_log (a_ss cs) = [];
  co_know  : know_ok SEGS E (Mr E cs model FULL) (kn cs);
  (* [comment removed for export] *)
  co_halt  : m_halted model = None;
  co_fds   : fds_ok E (a_fd cs) model;
  co_fs    : m_fs model = FS0;
  co_tid   : a_tidset cs = false -> m_tid model = None;
  co_res   : vm_reserved (m_vmmaps model) = segments_reserved SEGS;
  co_limit : vm_limit (m_vmmaps model) = LIMIT;
  (* [comment removed for export] *)
  co_maps  : maps_match E (a_maps cs) (vm_maps (m_vmmaps model));
  co_holes : Forall (hole_ok E (a_ylo cs) (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) (a_maps cs);   (* [comment removed for export] *)
  co_seps  : seps (vm_maps (m_vmmaps model));
  co_wf    : model_ivs_wf model;
  co_bounds : Forall (fun iv => 0 < bv_unsigned (snd iv)
                                /\ bv_unsigned (fst iv) mod 4096 = 0 /\ bv_unsigned (snd iv) mod 4096 = 0
                                /\ img_hi A <= bv_unsigned (fst iv)
                                /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CEIL) (vm_maps (m_vmmaps model));
  co_lazyb : Forall (fun iv => img_hi A <= bv_unsigned (fst iv)
                               /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CEIL) (m_vm_lazy model);
  co_nasub : forall z, in_ivs z (vm_noaccess (m_vmmaps model)) = true -> in_ivs z (vm_maps (m_vmmaps model)) = true;
  co_none  : Forall (fun m => am_kind m = KNONE \/ am_kind m = KNONELAZY ->
               In (amap_den E m) (vm_noaccess (m_vmmaps model))) (a_maps cs);
  co_kinds : Forall (fun m => am_kind m = KRWLAZY ->
               forall a : word, bv_unsigned (edenot E (am_base m)) <= bv_unsigned a < bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) ->
                 in_ivs (bv_unsigned a) (vm_noaccess (m_vmmaps model)) = false
                 /\ page_in_ranges (page_base a) (m_vm_lazy model) = true) (a_maps cs);
  co_totsz : sum_sizes (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) <= a_totsz cs;
  co_split : exists Y, a_ylo cs <= Y /\ Y mod 4096 = 0 /\ Y <= bv_unsigned (vm_mmap_base (m_vmmaps model))
                       /\ ledger_split (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) kHighMemBeg Y;
  co_brk   : vm_brk (m_vmmaps model) = edenot E (a_brk cs);
  co_sbrk  : bv_unsigned (vm_start_brk (m_vmmaps model)) <= bv_unsigned (vm_brk (m_vmmaps model));
  (* [comment removed for export] *)
  co_eager : eager_used model <= a_eager cs;
  co_abytes : A_bytes (allowA E cs) <= a_abytes cs;
  co_minv  : MInv (allowA E cs) model;
  (* [comment removed for export] *)
  co_zero  : forall a : word, hid E cs model a = true ->
               in_ivs (bv_unsigned a) (vm_maps (m_vmmaps model)) = true ->
               in_ivs (bv_unsigned a) (vm_noaccess (m_vmmaps model)) = false ->
               page_in_ranges (page_base a) (m_vm_lazy model) = true ->
               in_ghost E cs (bv_unsigned a) = false ->
               FULL a = Some (Z_to_bv 8 0);
  co_sinv  : SINV E FULL
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="HS XN XE XB KC"] Lemma A_wf_allowA : forall E cs, A_wf (allowA E cs).
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
ltac2:(KReplay.run1 (kr_t_AsanPlanSound ()) ["FPX_3"; "Sound"] "p'0h01Hh11xi001xh21Ah34__p1h44__x1h54__x2h64__x3h74__x4h81lh93Hinh:1Bh;2H0h<2Hah=1Ph>7__arithh?4__ffh@6__sat1hA6__sat2hB6__sat4hC8__varmaphD5__withE4__x5hF4__x6hG4__x7hH4__x8hI4__x9hJ1fhK2ivhL1yhM1EhN2H1hO3H10hP3H11hQ3H12hR3H13hS3H14hT2H2hU2H3hV2H4hW2H5hX2H6hY2H7hZ2H8h[2H9h\2Hbh]2Hnh^2_Hh_6__sat3h`2csha1phb1qhc2q0hd1rhe2r0p%0p&0p;1p;3p;2p;4p;5p;6p;7p;8p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0p10038p4p710R5p9P0p1003Vp4p710R6p9P0g00_3R7p4p710p8P0g004eR8p4p710p8P0g005FR9p4p710p8P0P9p4p7210p8P0p1005cp4p710p8p100_Jp4p70R0g00;\R:p4p710R;p8P0P1p8P0P2p8P0g0079R<p4p710R=p8P0P4p8P0P3p4p710R3p8P0P6p8p1006?p4p710P5p8p100`:p4p70R0P;p8P0P1p8P0P2p8P0p100`hp4p7210p8P0P=p8P0P4p8P0P3p8P0P5p8P0P6p8p100aDp4p70P=p8p100bCp4p7210R0P1p8P0P2p8P0P=p8P0P4p8P0P3p8P0P6p8p100bop4p70R0P1p8P0P2p8P0P4p8P0P3p8P0P6p8p1006\p4p7210R6P=p8P6P5p8g007UR6p4p7210R=P5p8p10082p4p73110P5p8p100cep4p710P5p8g00F?j1mTP8j3nTP7j30Tg00gKk30CTg00emk205Tg015oj1hj2XTP6j4\Tg00>lR7j21Tg016lR8j2aTg017Fk50XTg017fk104Tg008Nj19Tg00dlk10STg00iHj2FTg0093j1_Tg018]k20LTg00>Pj25Tg00kjj2>Tg00QGj16TP:j3;Tg019:j2OTg01:6j2KTg00\7j1:Tg00E?j1yTg00E_j3cTg01;2j1|Tg00:Bj23Tg00=Lj24Tg01<4k106Tg01=4j2JTg01>6k20VTg01>^k30UTg00A:j1HTg00AYk203Tg00DSk201Tg00]4k10TTg00G[k10RTg00H9k10PTg00JTj1`Tg00Mkj3YTg00J2k10OTg00K9j2}Tg00Hdj2{Tg00NNk20KTg00O0k20JTg00OJk20ITg00P6k30HTg00PUk40FTg01?Bj1wTg01@Ej1vTg00jOj4[Tg00<lj27TP<j6~Tg01AFk10ETg00:^j2=Tg009Qj2tTg00;;j2sTg00<6k10DTg00<Oj2]Tg00=ij2rTg00?Gj2oTg00?nj2pTg00@Tj2qTg00BBk10BTg00B`k20ATg00CAk30@Tg01BIk20?Tg01C2j3eTg00IGj4^Tg00Ldk60>Tg00MHj3xTg01C[k20=Tg01DXk10<TP9j3TTg00j2j3VTg01ERk10;Tg01FPk10MTg01GPk30NTg01Gmk40:Tg00Cjj3iTg00F_k209Tg00G=k408Tg00RFk700Tg00K\k60QTg00L@k707Tg00Rjj8jTg00UMR9f0R<7T9p=EAV99<p=Df3R:f2R5'3f1R0g01HMR3'7g00VPR45;917<3=;94'1'1p=<&0;0&0M<60N5p=Bg01IER3?V3<,J0p=k134<p=2AT33<,J0p>0GAT33<p=QAV33<p=Z140<#:p=AP9P9P0P<H0:p=@1J0<,F5p>0W1F0<,45p=l170<=;94p=N2039<p=IAi90<p>02Ai90<9i95p=b2099<p=PP9P5P0P<H08p=L1}9<p=CP5g00SNR2g00SmR1P1g00TMR;P9P0g00YLP<C^g00TmR>K00p=?P0P2P1P1P;P<J0Qp=zP5P2P1P1P;P0P<K07p=gP:P2P1P1P;P5P0P<Gjp=Wf6R?P2P1P1P;f5R@f4RAP:P2P1P1P;P5P0P<GjGjp=SAV33<,J0,F5p=UAT33<,J0,F5p=813:5A;904/1<'1p=uAT33:,JA,F@AV33<,J0,F5'4p=GA;9<4p=fA;90<p=MP0P2P1P1P;P<P>K00p=RP9P0g00Z3P<C^p=dg00n`g01JGg010`p4p710R>p-0RB\<RC%m0RDP7An50<A0A<5PAP0O1[^1:RE[A0:<0P:P0O1[^15An:50[RFAnA:5\EB0C50<P<n2001000000120000000W8W=W2PF^8D^=C^2>P<20599R>%E<RC%D<RFPCPFC<XK>RF20533R3P>%h5AB300C\P3P>%h:AB355C\90><P6p4p710R6PD\0RD%m5RCP7PAP:P5P0C\90:<A0?<:PAP<O190@5'1X1@,a@[REA0@<5P:P<O190A0'1X1A,aAP@PAP:P5C\90A0RG[f7RH?0<AP@P<O190?:'1X1?,a?\GPAP:P5P0P<I0XP0n2001000000120000000XL5W8WJX:=W2PE^L5^8C^JD^:=^26P<P3P>%h@AB3AAP5P0O6AB3@@903<1X?<90>:'1X13,a3P8P3AB3??903<1XH<90>A'1X13%EAR8%DAR6P8P6C<P<f8R6=B36903<f9R8/X<90>?'1P7AB3889030f:R=/X090>H%E6RD%D6RCPDPCC<P<f;RC=B3C903:f=RD/XA90>=f>RE/k@RG$04g00UkRI#9RJ#9RK#9RL#9#9#9RM$0SRN/FGRG#2%_JRO%_MRP+0LRQ,5G'1f?RG00G?RR$041FNRRR#215RQ'1g00mbRRf@RS%QH'>RT#6%ZH,>S,AT'@=;>D1OSH#61KSH#:'@%y>RT5c>90>D%EERU%DERVPUPVC<P5fARV%Q6'>RU#6%Z6,>V,AU'@=;>EP>fBRU%Q8'>RW#6RX%Z8,>U,AWRY'@RZPF%|W13XWfCRW%Q='>%Z=,>W'4R[$06%:[,3[fDR[%QCR\60WNR]#6R^%ZCR_,J[9l]NR`#:Ra'3%9M#9#9#9#9#9#_RM,N^R^1NaMRa'120VOPRb154O%2P154Q[[Rc%2ORdg0157ReB0UOP0UW<RP%2Q\e^<dRdg00VnReg00WZRO#HRf#HRg#HRh#IRi%Ig%IfRf2039ORO+023bg00X9Rg+01%yeRj3c%meRk%PA&0T9Rl7L5%P:7L0&0R9S00&0P9Rm%CKRn%`IRo#CRp5Y9Rq%CJRr5?m&0O1RsPm1}9IRt=?mnPsPm1{94Ru=?mpS011zm?5gmPsA?mtrS02CWFS20Km;S03P<P5g00ZZRpg00[:Rv+0J20I<5=;pvdB0H940H0FS04b?bCbDX49X59X69X79X3B14:5/30130A%2A/1?13:A[[[^49^59^69^79^3BP<fGRv=UNERp/5QA8NvERwPp1Awp%6wP:PAP6O8b>b@bAP^Pa%w]%v`C[C[1>[\R\#6R`1>[_,A\R\17`M1N\MCueb;b0PXPYPXPYC<e%EZRY%DZRZPYPZC<ePGP<E~W0P<O11OV6#61KV6#:'@=c>T90>EPR1OU8#61KU8#:'@=;>GA0>GT%ESRR%DSREPRPEC<P<1OW=#61KW=#:'@=;>SP>1O[CRE#6RR1K[C#:RZ'@RYPF%|E13REfEREf<RF'KRX$06%:X,3Xp,1A$0ERXfFR\=8NDR`%_LR_'='4R]#6Ra1k\D9l`N/=_,4XR^#:Rw'31NaMRa1NwMRw'11t`_%2`%2_R`fHRp=8NG/=_#2[[PbPcPPPdPNfIRdPSPNPdPSEGRP/t_%2PfKRP=8NURc1kPU7lN/=_#2\`[fJRb=8NV/s_%f_Rx$0DRy1=c_,]_17c_'4,Mc[1rc_154_RcfLRz=8NWRW/7_R{#215{_'1[1oW_15_4RWfMR{=8N[R[/7_R|,5_13|4'1[1p[_fNR[=8NERE/=_#f\x1qE_fORE=8N\R|/7_/M|\x1=|_P9fP=8Nv/7_P9PNfQR|PpPNP|PpEG/s_PNfRR}PdPNP}PdEGR~1=~_,]_17~_'4'M\y1r~_PNfSR~PbPNP~PbEGRb/7_Ry#215y_'1\c1ob_PNfTRbPPPNPbPPEGRP/7_Rb,5_13b4'1\W1pP_PNfURPPzPNPPPzEGRW/=_#f\x1qW_PNfVRWP{PNPWP{EGRb/7_/Mb\x1=b_P9PNfWRbP[PNPbP[EG/7_P9P7fX=8NERE#215EQ14X8#61AX5'3PpfZ=8N|#2f[=8N}/5QP7f\=UN~R~#215~Q14XD#61AX?'3P{f^=UNP#2f_=UNW/5QPdP@O1%2V\`%HhRh#HR`#HRd#HRQ#H#I%IQ%Id&0BI-0A9%I`60@920?9_R`%Ih5e9Ae9`iAe9`O-02f3b3b3b001g=cejPk%P6?LAl%P?7L5%P8?L@l%PH7L:7L0Q00PmPmP9Pug00XeRl1{9_R5C^,RmR?Ps%`K#CRK9?muP9PKPlP5C^,Rm5gmCWPsPmPmPmP2P1P1P;1d5u,RmJ0>R;Ps%`o#CR19x95=Y9K,dq,RmCWPsPmPmP?Ps%CLRL9?mu1zmC5gmCWPsPmPmP;Ps%9o#CRo9x95=Y9L,dn,RmCWPsPm%`J#CRJ=Y91=?mrPsPmAY9Jo9?mtPsPmA?munPsPmQ01PsQ02FSFSFSFSQ03Q04b?bCbDX49X59X69X79XE9XF9XG9XH9XI9X3B%28Rs158_'1\cg00[ZRm\xRx14@A1]_6/4='M[%2=/1F\c1]_8/4C,MH\x146=/3@148=,3@1368\s\s[[[[[[^49^59^69^79^E9^F9^G9^H9^I9^3BP<15V_P=PVPCPUPXfbR=fYR_58NAUN=_1AXC14XU#6PGPSP\PvPzP{PHP:OBb>bBWSWRP0P<O2n2001000000121000000WQWPP0P<O2n2001000000121000000bebcbOb[bZbYbXbdbbbWbVbUbTbNb@bAb_bBPaPw%w]%v^C[C[1O\D#6R^1K\D#:R\17^M1N\MCueb;b0PRPZPRPZC<e%EYRZ%DYRYPZPYC<ePVP<E~W0P<O1A0>STPm%EURm%DURUPmPUC<P<n010000000W0P<O1n200100000021100010000W0P<O1n200100000021100011000b\b]W9W^P0P<O2n2001000000121000000W0Xa3P0P<O2n2001000000121100000b9b0W9XK>O4b020=0<$0<eW`WMo"). Qed.

#[using="HS XN XE XB KC"] Lemma page_base_le : forall a : word, bv_unsigned (page_base a) <= bv_unsigned a
                                       /\ bv_unsigned a < bv_unsigned (page_base a) + 4096
                                       /\ bv_unsigned (page_base a) mod 4096 = 0.
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
ltac2:(KReplay.run1 (kr_t_AsanPlanSound ()) ["FPX_3"; "Sound"] "h04__x1h14__x2h26__sat2h37__arithh44__ffh56__sat0h66__sat1h78__varmaph85__with94__p1h:4__x3h;2Hah<1Hh=2H0h>2H1h?2H2h@2H3hA2H4hB2H5hC1qhD1rhE1zhF2H6hG1ap%0p;1p;2p;3p;4p;6p;7p;8p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0g0038R5p4p710R6p9P0p1003Vp4p710R7p9P0p1004Np4p710p8P0p1004ep4p710p8P0p1005FR8p4p710p8P0P8p4p7210p8P0p1005cp4p710p8p100_Jp4p70R0g00;\R8p4p710R9p8P0P1p8P0P2p8P0p10079p4p710R:p8P0P4p8P0P3p4p710R3p8P0P7p8p1006?p4p710P6p8p100`:p4p70R0P9p8P0P1p8P0P2p8P0p100`hp4p7210p8P0P:p8P0P4p8P0P3p8P0P6p8P0P7p8p100aDp4p70P:p8p100bCp4p7210R0P1p8P0P2p8P0P:p8P0P4p8P0P3p8P0P7p8p100bop4p70R0P1p8P0P2p8P0P4p8P0P3p8P0P7p8p1006\p4p7210R7P:p8P7P6p8p1007Up4p7210P6p8p10082p4p73110P6p8p100cep4p710P6p8g008Nj1GTg00dlj1jTg00eJj1aTg017fj1}Tg00iHj22Tg0093j1NTg018]j2eTg00>Pj21Tg00>lR6j23Tg009Qj2PTg00:^j29Tg01>6j2|Tg01>^j3zTg00;;j2WTg00<6j1rTg00<Oj26Tg00<lj28Tg00=Lj2:Tg00=ij2VTg00?Gj2OTg00:Bj27Tg00?nj2XTg00@Tj2QTg00A:j1FTg00AYj2@Tg00BBj1cTg00B`j2bTg00CAj3`Tg00DSj2DTg01BIj2_Tg01C2j3^Tg01KEj2]Tg00E?j1\Tg00E_j3BTg00F?j1[Tg00F_j2ZTg00G=j4YTg00G[j1{Tg00H9j1yTg00Hdj2ITg00J2j1vTg00JTj1uTg00K9j2MTg00Ldj6qTg00MHj3ETg00Mkj3JTg00NNj2pTg00O0j2STg00OJj2oTP8j3LTg00P6j3nTg00PUj4mTg00]4j1lTg00]Rj3kTP5j6UTg00jOj4TTg01L1j2iTg01LWj3hTg01M:j2gTg01N7j1sTg00Cjj3tTg00IGj4KTg00RFj7fTg00L@j7wTg00Rjj8dTg00K\j6xTf0R5#G#Gp=Ag00VPR8/75p=0g00UMR7?L58p=<f1R:=L75p=>At7:5p=;P7P:g00XeP5CKp=?P:g00SNR0g00SmR3P3g00TMR4P5g00TmFfp=5P7P:g00YLP5CKp=Cf2R2P0P3P3P4P:P5Fwp==f3R1P0P3P3P4P2P:P5Gdp=4P7P:g00Z3P5CKp=HP:P0P3P3P4P5Exp=Rg00UkR9#GR;#G#A#AR<#jR=#a%}512=5R>#0%N;R?%N<R@'eRA,1>'312=:RB%A<#A#A#NR<'P%0B%0<RC12=1RD/9<#0[[1|?@RE118?%0@118A[[RF%0?RGg0157RHAz?@:UW;R@%0A\H^;GRGf4RH,2=RI/W<%<<RJ#rRKf5RL,2=RM19M<,6<18M<':'>[1VM<118<RNf6RO,2=RP/8<RQ#011Q<'3[1OP<11<8RRf7RS,2=RT/8<RU,1<17U8'3[1XT<f8,2=RV/9<#<\J1QV<f9,2=RW/8</>W\J19W<RXP7f:RY,2=RZ/8<R[P7P6f;R\,2=R]#011]A162<R^#0R_f<R`,2=Ra,7^'3PYf=RY,2=Rb#0f>,2=Rc/1APYP:O1S00%0OS01\CS02g00VnRYg00WZRd#FRe#FRf#FRg#F,@7Rh%c9,b71@7fRf5`71@7dRd';';g00X9Ri'D1_7<=^7d1@7gRg/;f,;h';/Di,]d%\YRh5BY3B%[YRjP71Z72RkP:1Z71CYS03%{7Rl%y7RmPm1I78Rn1I7<Ro'?,5mS04%v3Rp%u9,M7Rq,Cn,5m1?qo,5mRr5=mC4PpPmPmPmP0P3P3P41Hon,5mEqR3Pp1M7;R;1M79R99E7o=J7q'H,5mC4PpPm1Cn;,5mR0PpAE79oRs,Cn,5mRn1Cs;,5mRt5=mS05C4C4C41pm4R4P5P2g00ZZRug00[:Rv'S1o52=LuvdAn78:CmRvb4b7b8X07X17X:7%01Ru111<Rw'3\Ng00[Z\JRx16<2/:H,>1[161<Ry#017yH'3\u[[^07^17^:7P5POfA,2=PSP\P`P1O6b3b2WBWAP:P5O2n2001000000121000000bDbCb@b?b>b=b<b5b6b219B</6<Ru#017uB'3P712=2Ru/9<RB/6<Rz175D1:5<,1D185<#<'3'3XE717zu1:z<,1uRD18z<R{#<R|'31Pu<R}%0u19I<#0\C[RCPEPFP@PGp-0RIPhPjP7PkP:%l7RkCYS06PlPm1RmH==mtPpPtC4P4Pvb4b7b8X07X17W9165<Rt/7:Ru,3216:</72[^07^17^9IP519P<R~/6<#0PPP~PHO4b3b5b6b2PDP|P}PCPEPFP@PG1WM<16<~/:Q,>P\K1VP<%0U11U<'3\N1OT<18V<RT,1<17T8'3\R1XV<%<X\J1QW<1>[Z\J19Z<P718]<P7P6%0a11aA1:^<,1bP\%0cf?,2=/1AQ00Q021@7e/;dRd,;f/Di=BYhPjQ03PlPmPmQ04Pp1RmL==mrC4PpPmPmP3PpAE7o;=J7q,H9,5mC4PpAE7;o=J7o,?9,5mC4C4P4Pvb4b7b8X07X17X:7X9I13Hw\N16<1/:H,>2\x1:y<,12[[^07^17^:7^9IP5Q01POPSfB,2=P\P`O6b3b2WFWBP:P5O2n2001000000121000000bDbCbAb@b?b>b=b5b6b2P7P8%<5XE71S78P{PEPFP@PGPhPjPkPlP3P4Pvb4b7b8PxP5b3b5b69kB<EUCTCT1i=z,2=P}PCPEPFP@PG1;gd/Di=BYhPjQ06PlPmQ05PpPm1I7?=h7=R?,?;,5m9=m0Pp1?s?,5m9=mnC4C4P4Pvb4b7b8X07X17%0t/3u%02112A'311^A,3_[[^07^17P5PPP~PHPLO4b3b5b6b2,gzEUb<b;%s5,2=R=/7>1:=<,1>18=<#<'3'3eWGo"). Qed.

(* [comment removed for export] *)
#[using="HS XN XE XB KC"] Lemma page_in_ranges_bounds : forall (a : word) l lo hi,
  Forall (fun iv => lo <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= hi) l ->
  page_in_ranges (page_base a) l = true ->
  lo <= bv_unsigned a /\ bv_unsigned a + 1 <= hi + 4095.
Proof.
  intros a l lo hi Hl Hp. unfold page_in_ranges in Hp. apply existsb_exists in Hp as [iv [Hin Hb]].
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) Hl iv Hin) as [L1 L2].
  pose proof (page_base_le a) as (P1 & P2 & P3). unfold page_size in H2. lia.
Qed.

#[using="HS XN XE XB HULL_ok KC"] Lemma lazy_cover_cs : forall E cs R FULL model,
  cs_ok E cs R FULL model -> lazy_cover (hid E cs model) (m_vm_lazy model) (allowA E cs).
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
ltac2:(KReplay.run1 (kr_t_AsanPlanSound ()) ["FPX_3"; "Sound"] "p'0h01Hh11xi001xh22Hvh34__p1h44__x1h54__x2h64__x3h74__x4h81Ah92Hbh:3Hb1h;3Hb2h<7__arithh=4__x5h>4__x6h?4__x7h@1fhA1lhB1mhC1nhD4__ffhE8__varmaphF5__withG1rhH3H10hI3H11hJ3H12hK3H13hL3H14hM3H15hN3H16hO3H17hP3H18hQ3H19hR3H20hS3H21hT3H22hU2H4hV2H5hW2H6hX2H7hY2H8hZ2H9h[6__sat4h\6__sat5h]6__sat6h^6__sat7h_1ph`1qha2q0hb2q1hc2q2hd2r0he2r1hf2r2hg3Hinhh1bhi2ivhj1Bhk2Hhhl3Hlzhm2P1hn2P2ho2P3hp2_Hhq4__x8hr2b1hs2b2ht1yhu2B1hv2B2hw1Ehx4FULLhy2H0hz2H1h{2H2h|2H3h}2HCh~2HUi012Hai022L1i032L2i041Ri052csi065modeli071wp%0p%1p&0p&1p;1p;2p;5p;4p;6p;3p;7p;8p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0p10038p4p710R5p9P0p1003Vp4p710R6p9P0g00_3R7p4p710p8P0g004eR8p4p710p8P0g005FR9p4p710p8P0P9p4p7210p8P0g005cR0p4p710R:p8p100_Jp4p70R;g00;\R<p4p710R=p8P;P1p8P;P2p8P;g0079R>p4p710R?p8P;P4p8P;P3p4p710R3p8P;P6p8g01SPR;p4p710P5p8p100`:p4p70R@P=p8P@P1p8P@P2p8P@p100`hp4p7210p8P@P?p8P@P4p8P@P3p8P@P5p8P@P6p8p100aDp4p70P?p8g00bCR@p4p7210R=P1p8P=P2p8P=P?p8P=P4p8P=P3p8P=P6p8p100bop4p70R=P1p8P=P2p8P=P4p8P=P3p8P=P6p8p1006\p4p7210R6P?p8P6P5p8g007US00p4p7210S01P5p8p10082p4p73110P5p8p100cep4p710P5p8g008Nj1CTg00JTk105Tg00dlk10YTg00eJk10sTP@k21LTg01Snk11>Tg01TPk514Tg01N7j1?Tg01UNk40xk31?Tg01VHk208Tg00>lR@j2=Tg01Vek21PTg01WFk40ITg01X@j1<Tg01X^k11=Tg01Y@j1LTg01Z8k116Tg01[7k60iTg01\6k612Tg00iHj20Tg00:Bj22Tg0093k10CTg00=Lj23Tg01]Bk10zTg00<lj24Tg01^Aj2zTg01_?j1xTg01`6j1|Tg01`lj2JTg01aik10:Tg01Plj2fTg01bck30dTg00mbS02k20bTg01POj29Tg01c?k20JTg01QJk30>Tg00>Pj2DTg01c\k21FTg00E?k10mTg00F?k10[Tg00]4k11<Tg00G[k11:Tg00H9k119Tg00K9k20pTg00J2k115Tg00NNk213Tg00O0k20XTg00OJk211Tg00P6k310Tg00PUk40~Tg01Qmk20}TP0k30WTg016lS03j2FTg01Olk30|Tg00emk20VTg00j2j3MTP7j36TP8k30hTg00gKk30{Tg00hmk60yTg01RMk10gTg00A:j1jTg00AYk20fTg00DSk20STg00E_k30@Tg00Hdk20?TP>k60wTg015oj1[k20rTg01ERj1ATQ00j4YTg01d<k30OTg01e9k30NTg00kjj2STg01FPk10uTg01GPk30tTg00QGk107Tg00\7k101Tg017Fk51RTg01f5k30cTP;k51QTP<j3>Tg019:j2:Tg01:6j2VTg00jOk403Tg01fOk40LTg01fik20qk30oTg009Qk20KTg00:^j2;Tg00;;j2sTg00<6k11OTg00=ij2wTg00?Gj2iTg00?nj2hTg00@Tj2qTg00BBk11KTg00B`k21JTg00CAk30=Tg01BIk21ITg01C2k31HTg01KEk20nTg00Ldk61GTg00MHk30;Tg00<Ok20<Tg01gZk30kTg01hCk31ATg01C[k20^Tg01h]k31;Tg01Nok21@Tg01i]k20jTg01j`k31BTg00F_k21CTg00G=k40`Tg00IGk40FTg00K\k618Tg00RFk70aTg00Rjk80BTP9k30HTg00Cjk30\Tg00Mkk317Tg01Gmk41MTg00L@k71NTf0R9#C#Cp>0Rf1R<%L9+1@p=]g00ZZR;g00[:R>7>9p=1g014W9>;9p=@f2R800^<%?9+0j=>;>p=R&059$05p=T138</29p=gg00VPR7/29p=7%C9#C#C#Cp={g00UMR0?>97p=Kg01k_R5/99p=yf3R6B1B8<9+08p=d1f<9=>;>p>0420^8<00j9=>;>p=eA>;9>,=<p=O19<9=>;>p=H20J<9=>;>p=`21C09p=tP0P8P<P9H0`p>0G20p09p=uP0P<g00YLR?P9H0Fp>0ZP0P<g00XeP9H0Fp=}P<g00SNR=g00SmR3P3g00TMR4P9J18p>0Ef4R2P=P3P3P4P6P=P3P3P4P8g00TmR1K0aP<P9L0Bp>0DA668</=9p=BB0H8<9,06p=G%?9,0<p=510<9,38p=mg01HMRA,3</99p=l198</f9p=^198</f9=>;>p=E139Ap>0UAM8<9,06p>0T14<9=>07p=P1D8</=9p=I13<9,D8p=k20f09p=pB0\0<9p>0AB0\0<9:0\08p=rP0P0P2P6P8H0`P<P9H0`p=cB170<9p=WP<P=P3P3P4P9P1K0ap=NP8P=P3P3P4P0P<P?P9H0FP1K0ap>02f6R1P=P3P3P4f5R?P2P6P=P3P3P4P8P<P9L0BL0Bp=QB0H009p>0QAM009p>0P&0u9:0t8<p=\g01IERA@0HA9p>0vAMAA9p=n13<9-0J8p>09B0HAA9,S<p=8AMAA9,S<p>0M1S<9,38p=~P0P0P<P9H1Mp>06P6P8P<P9CY96?2p>0e20<8</399>06p=U1D<9,=8p=X1297p=vA>0<9p=ZP0P<g00Z3P9H0Fp=oP6P=P3P3P4P8P<P9L0Bp=aP8P=P3P3P4P<P9K1Np>0_20<8</39p>1EAMAA<,S8,36/39p=b138</39p>1D13<99>08p>0l1V<9-0J8p>001:8</99p>0]1V8</39p=_g00n`g01JGg00UkRB#CRC$05S04$0Y%CCRD#CRE#CS05$0RRF$0YRG$0sRH+1L&0YE$0s$1>\Hg01l\P2P6P8P<P9I14%?9/]8#1f7REP1P6P<H0x#@P@208<9#@%@8RI%@<RJ'=[RK%@9,=J2088<#@RJ[%@6/=I\J21P<9P<n2001000000120000000Xs;Xr;PK^s;^r;P9p,4argHRKf9RJP6O2RIPJf8RLP?P6H0I#<RMP<O3%@I%@M'=P@PKf:RMP2O2#@PMPJP1P2H0I#<#@f;RI?RM?P9PKf<RKP1O2#@f=RNPKPJPEH0I#<#@P@%<9S06#@%1<[RO%19%<<#@RP[%18\P&1=9P<n2001000000120000000Xh;PO^h;P9f?ROf>RPPIPJH0IRQP<O2%1QPM%LKp,1ARQ$16RRP5f@RSPOPPPNPKPIJ0iPJJ1210GMRT,2R&0CBRU&05BS07#T#T#T#T#TRV$0CRW,35RX5gT'=P@10GIRT,2RAgTUXfBRTfAS08;RKP910GN,2R10GP?gUXp,7HULL_okg01mRP@&0zQRX#7S09&0RF#{$0CRF,4XRU#KS0:14RFRK#KS0;g011=,2RS0<'=S0='=S0>fGRYfFRZQ083RP9Q09Q0>P@Q0:Q0=fKS0?fJfES0@3RP9Q0:Q0=P@Q0;Q0<fOR[fNR\fIS0A3RP9Q0;Q0<fLS0B,0GR],zQ%y]+08R^%x\R_#|,J]&0:_,J]#<'fQ0B#?/]\#<fRR_fQR`P]Cd'fR]<0dT%1^%1]+0bQ02fMR],0GR^,zQ%y^+08#1%x[Ra#|,J^&0:a,J^#<'f%?]/][#<fSRaP_P^Cd+04fTR^%?\S0C7eaP910G\R\,zQ%y\+08#110G[S0D,zQRbQ0D#yRc<0d9%1b%1c+0bQ02fPS0E,0GS0F,zQ#1Q0F#y#1fWRcfVS0G;R`S0HP910G`Rb,zQ#110G_S0I,9XRQQ0I00JRRd<0>9%1Q/OdP@10GaS0J,HXQ0J/`RfZS0KfYRd%?^S0L3eS0MP9fURQ,0GS0N,HXQ0G,0GS0O/`RP@1`<91D8<[Re1D<91`8<Rf[1D68\f21F<9P<n2001000000120000000XB0XC0S0PPe^B0^C0S0QP9fXS0R,0GS0SPRP<O3Q0S/DRp-0Reg00VnRf$0mS0T&0[fS0U%t8&1<0Rg80G<&1:0S0V&190RhPh%uCRC20p0BRi+0Z&153RjPhPh1}iCPj20Eh2I0DI0D213h4S0WP9P820X;>21198#1dB1007<H0~S0XbDbEbFX40X50W312<9Rk1D<8P2[[^40^50^3eP9f`Rlf_S0YQ0K#?Rm3ePRQ0K,0GS0ZQ0BP<O5b<b2b0W2WpP<P9O2n2001000000121000000b2W2P9O1%yb#1P@1H<9128<S0[[S0\1H8<Rb\kS0]1268\b20}<9S0^P<n2001000000120000000XB0XC0S0_Q0\^B0^C0S0`P9P5Q0JP<O3Q0J,25P;\9S0a&0[<S0bP@B0W8<9#1P2P9P8P6P9O1S0c#1CBX16,F6S0d[S0eP6P9P<P8P9O1#1CBX18,F8B0W68<#1Rb[S0fP?P9P6P2P9O1S0g#1CBX12,F2\bB0|8<9S0hP<n2001000000120000000WAW@X8:S0iQ0aQ0bQ0e]A]@^8:S0jP920VHHRbPGPHPHP9CGRkQ0G,5GRnAMHH99mkGRo,ln3^RpXGb%LcP^O4PbP9Q0R#L%1pCBX1b,FbQ03PbPbP9%Ld%?cRc,0GRp1lpo5EkCBX1bf]Rpf\S0k;ecS0lP9PbP9f[S0m#L15GdS0nQ0n/lo5EkCBP@Q0k#L96b<PGPHPHP<CGRc10GmS0oQ0oAMHH<9mcG'l3EfaS0pQ0m7RlS0qP9f^Rc#L96b6PGPHPHP2CGRm15GpS0rQ0rAMHH29mmG'l3EPGPHPHP?CGRm%?cS0s,0GRc'9RpAMHH?9mmG,lcRc<0>9%1p/OcP@PGPHPHP1CGRcQ0Y,5GRp'H&0UpAMHH19mcG'HffRcfeRp%?lS0t3eP9PGPHPHPLCGQ0p,5G'Hfb,5GS0u$0UPGPHPHPJCGAMHHJ7mG'HQ0_Q0`P9PGPHPHPICGRmfdRq,5GRrP8O312mrQ0_Q0`P915GcS0v$0URrPGPHPHPNCGAMHHN7mGRmP6O312rm12Rk12o5'=XibRofiRk#LRm60hbfkRr#L96b9PoP<O1Rs[^1b[fjRt#LRu96b9Ps[^1bB0hbou[B0{bomfmRmflRuPrPtPkfhS0wJ0iPPPMJ0yPoPPO1P@PGPHPHPOCGRo,2RPGPHPHPOH0T=go5foRofnRs;RkP9PGPHPHQ08CG,2RPGPHPHPTCGPGPHPHPTH0T;g5&0gu15GuR510GuRv'2135F1P5F5Iv'=P@15GmR510GmRw'2135F1P5F5IwftR5fsRx;RsP915GoS0x10GoS0y'2fpS0z,0GS0{Q0z,5GRy/3F1PyF3IP@fqRy,0G15GyRz;kF1PzFfxS0|fwfrRz3RP910Gx15Gx;kF15G5/PFg00WZR{#jR|#jR}#jS0}#pS0~%p}S10%p|20f0{S11+0A3rg00X9S12+0SQ0T60@fQ0U%t2P8PgP<%t6DcQ0VPh%uDRD20?0FR{,WCR|'},NhS13PjPhQ07#uS14,WiR}&05V#T#C#T#T#T#T#C$0R#{#{#{#{#{$0CRV-0?0R~602hPjPhPh20Z~DPjPhPh20Z|}Pj20Eh1I0DI0DFQQ0WQ0XbDbEbFX40X50X60X70X3eAk6<FAg<6V12V?136?9g2FPL[[[[^40^50^60^70^3eP9f|RVf{R}fvR|#?R~3e10G|PGPHPHP]H0T10G~R~PGPHPHP]CGP8PMP_POO9b<fzR]fuS15#?S165e}eWoWnP<P9O2n2001000000121000000W0WmP<P9O2n2001000000121000000b0Y03Y02P<P9O2n2001000000121000000b0b;b0b:b0W;W:P<P9O2n2001000000121000000b9W9WgP<P9O2n2001000000121000000W0XibP<P9O2n2001000000121100000blb0Q0Meb2b0W2P9O1n200100000021100011000b2W2P9O1Q0E#xRb#|,J\&0:b,J\#<'fQ0CQ0E']#<P^PaP\Cd+04Q0D%x`R\#|'JQ0D&0:\'J#<'fR\%?[/]`#<PQP^Q0DCdR`<0>9%1\/O`P@Q0F%x_R`#|'JQ0F&0:`'J#<+04Q0E#?/]_#<Q0GPQQ0FCd#1Q0HP9Q0I%x^R`#|'JQ0I&0:`'J#<+04%?a/]Q#<PdQ0RQ0JCd#1P;Q0LQ0G']Q06Q0mQ0KQ0NCd#1Xh;P9P>PaJ0w%<>Q0KPd10G^Cd#1&0gQ15GQRQQ0N'2Q0N13QF1PQF3I'=P@Q0O,2nQ0O13nF1PnF3IQ0lP9Q0R,5GQ0S'210GdQ0n/3FQ0n/PF3IP@Q0ZQ0o;kFQ0o/PFQ0qP9Q0k,0GQ0k,5G;kFQ0r/PFQ0aQ0bP@Q0eQ0fQ0dB0W268#1[Q0hP9n2001000000120000000WAW@X8:Q0aQ0bQ0f]A]@^8:P920V00R:&0Q9RdQ0t,0GRn&0P9RQ,ln3^S0tXi:20VAARAP:%[p%Aq=\AqCYQ0Y,0GRn:0OpqR>B0NpqnRn<0dM%1>%1n+0bQ0210GlRn:0Ocp#1B0Ncpn#1P:P9PAP:Q0w#[fgRn#A=\AnCYQ0uQ0u/3F/9Q5EdCBX1:,F:P9Q0p,0GS0p:0Onc#1Q0iQ0jP9PA&0v9R>,StRa10GqS0uQ0u%n9R;,St809a3^RaX_AQ0w#AS02P<O4%Ak96A9S0Y/OaX1A,FAQ03PA%At96A9S0a1Sr>Ra10GpS0fQ0f1Sr;809a3^'OX1AP:P9PAP:%[u%Ar=\ArCYQ0vQ0v/3F/9Q5EdCBX1:,F:S0vP9%Au96A9S0h1Sm>R>10GnS0dQ0d1Sm;809>3^'OP@%Am96A<S0e18s<R>Q0w,0GS0wQ0w20Ms<809>3EP:P9PAP:Q0z#[%AoR>=\AoCY15GtRo13oF/9Q5EdCBX1:,F:S0zP9A6A6>S0r18y2R>10GrS0kQ0k20My2809>3E18z?R>/9vRo20Mz?:09v>R><0>9%1o/O>P@18x1R>/Hw%n19~>x,`wP:P9PAP:Q15#[%A5=\A5CYQ0xQ0x/3F/9Q5EdCBX1:,F:S0xP9Q15/8LQ0y'HQ0{18|J%nJ7~|'`Q0_Q0`P9Q0|/8IR>10GzS0qP8O3Q0q,2>Q0PQ0QP910G5S0o18]N%nN7~]R5P6O3Q0o/D5P:P:P9PAP:%[VS0Z%A}R5&0u}R>60tAS0nCY13~FS0S/9Q9Ed~CBX1:S0R18}PRd$07RQ%nP9~d}$01Rd+06RoPAP:%[}%A]=\A]CYS0l96:o&0QoQ16,0GR;13;FRu&0Po'93ES16Q00p4p710RoQ01Q0b\<Ra&0[8R`P@P6P9P2P6P8P<J0eP1P9P6Q0g96?8CBX1?,F?R\[P?P9P8Q0c962<CBX12,F2P2P<P?P2P6P8J0e[R[P?P8P1P?P2P6J0e\\P2P6P8P<P9I1RP9n2001000000120000000Xt8WAW@WjW8S0cQ01P[^t8^A`^@a]j^8oS01P9PAP:Q0ZQ0n18VORo$07S0g%nO9~oV$01S0b+06RoPA%AV=\AV96A9S00f}Ra/8SR`$07%nS9~`a$01+0620ra9S0O56:'=X1APOQ0n96AOS0N20rVOS0K96:oPAP5P>POA6AO5A6AO><0cII1QS0mA>:oo1:VO$07S061VVO$01S0L+06RV&0m:S0G60@:S0J96:o20X:o40cH03H0LO6b019Q;RQ19udRd%1Q%1dP@Q0\Q0]Q0[1H68[Q0^P9n2001000000120000000XB0XC0S0^Q0]^B0^C0S0]P9Q0gP~20q~FS0[%7~%7FRdQ0|,5G/4F#7[[S0\20K`F%7`p+01@S0I/8T/;F#7\d[B0oXFp%7US0H\dS0F20qRFS0E%7R%7KR`\d[S0Dp+01AS0CfCS0M'8S17/sF%KFRQ$1OR>p+01BS18fDS19'8R5PF1;5F145FCU[1w5F1D7FR[p+01CS1:Q0@'8S1;/4FR\#7?X\F[Q1;/iF1DF7R\p+01DS1</8ZS1=/4FRb%vb5IF[Q1=/hFp+01ES1>/8YS1?/;F#K\QQ1?/qFp+01FS1@fHS1A'8S1B/4FQ1B'Z\QQ1B/;FP0p+01GS1CQ0A'8S1D/4FP01sRFS1EPRPF1;RFRbPKCU\>S1F1wRFS1GAX`KF\[S1H1iRFS1I%vK9IFK\\S1J1hRFS1K%Kb\QS1L1qRFS1M1ZKR\QS1NPbP0PKP01sXFS1OPXPF1;XFRRPUCU\>S1P1wXFS1QQ0H?XUF\[S0H1iXFS1R%vU9IFU\\S1S1hXFS1T%KR\QS1U1qXFS1V1ZUX\QS1WPRP0PUP0p+01P,5G/sFS1Xp+01Q,5GR`PF1;`F14`FCU\>S1Y1w`FS1Zp+01R,5GS1[/4FR`#7?X`F\[S1\Q1[/iFS1[p+01S,5GS1]/4FR`%v`5IF\\S1^Q1]/hFS1]p+01T,5GR`/;F#K\QS1_1q`FS1`p+01U,5GR`/4F/Z`\QS1a1;`FS1bP0p+01V,5G/4FS1cP0&1KB-1J0RBQ0}#jS0}#jS1d#jS1e#pR`60=0Q0~:0=0BQ113r21I0FQ1161H0S1fQ1e#j#pS1eQ1d#pS1d:0=0BQ0}#pS0}Q0~Q10+0AS10+0A5r`3rQ12+0S+0nQ0T60@fQ0U%tES1g@0GEgS1h%t?S1i80G2P8PgP<PgPE%t1S1jP6PgDcDcQ0VPhPhPhP=P3P3P420?07R7,o{,NhJ1GR4PjQ05#u:0;0{Q07#CR3#C#uR='WS07,oC,NhCaPjPhPh1}7{,NhS05Pj&053#uR3:02h720EhJS1k60_hCaPjPhPhP4PjQ14B0;0{i/W3'o,NhCaPjPh1o=7,NhS1lPjPhQ13PjPhQ14>02hDPjB0;0i{>02hCFQFQFQQ0WQ0XbDbEbFX40X50X60X70X=0X>0X?0X3eS13g00[Z\QR=B1EFE?S1m,Z8[%7E/=J\[P?PFP6PLCU\=%KES1nAkE?F12EL20<1F/2E[[[[[[^40^50^60^70^=0^>0^?0^3eS1oP91DZFS1pP8PZP<p+01XS1q,0GS1rp+01^R7/8lS1sQ1q,5GRGPYPEQ0?Q0BPkPtP^O>b<bfbcbTbSbRbQbPbebbbObNbMbLbKbdbabJbIbHbZbYbGb`bXbWbVbUb0b[b\b]b^Q0g/2~eO3b0Q0^Q0]P9Q0SQ0bQ0[Q0\B0oXFqS0gQ0Ff~RXQ08'8PXQ08PWCbRX00KF%7XQ17Q0CQ0MPWCbRX/;F#7\d[Q0EQ0D1sXFP5Q18Q19PWCbR5PF1;5F145FCU\>1w5FQ1;Q1:Q0@PWCbR5/4FRX#7?XXF\[1i5FQ1=Q1<PZPWCbR5/4FRX%vX5IF\\1h5FQ1?Q1>PYPWCbR5/;F#K\Q1q5FQ1BQ1@Q1APWCbR5/4F/Z5\Q1;5FP0Q1DQ1CQ0APWCb/4FP0Q1EQ1FQ1GQ1HQ1IQ1JQ1KQ1LQ1MQ1NPbP0PKP0Q1OQ1PQ1QQ0HQ1RQ1SQ1TQ1UQ1VQ1WPRP0PUP0Q1XQ1YQ1ZQ1\Q1[Q1^Q1]Q1_Q1`Q1aQ1bP0Q1cP0Q0~Q115r`Q1fQ1e:0=0BQ1dQ0}:0=0BQ10+0A5r`3rQ12+0S+0nQ0T60@fS0TQ0U%tLPLPgP2Q1jDcP8PgP<PgP?Q1gP6PgDcDcQ0VPhPhP4PjQ07,oi,NhCaS07PjPhPhQ05Pj20EhM1}3{,NhRf60_hCaPjPhPhP4PjQ14Q04#uR`'WRB20?0WR5'WB0;0{C/W3R3'o,NhCaPjPhQ1lPjPhB02hiDRXPjPh1}DB,NhPj1Wi{B0;0C{602hR{FQFQFQQ0WQ0XbDbEbFX40X50X60X70X=0X>0X?0Xq0X3eP<PFPLP1CU\=AXMLF\[B1D?EW20<F2RM<0lJ\=%KL122EAkLEJ20<EF9g1FRC[[[[[[^40^50^60^70^=0^>0^?0^q0^3eP9%7ZRiP8PZP<20M7lQ1rQ1sPYPGPEQ0?Q0BPkPsP_O?b<bfbcbTbSbRbQbPbebbbObNbMbLbKbdbabJbIbHbZbYbGb`bXbWbVbUb0b[b\b]b^Q0SQ0b'2eO3b0H0340kQ16eH03H0Lb;b0b:b0W;W:P<P9O2n2001000000121000000b9W9WgP<P9O2n2001000000121000000W0X_AP<P9O2n2001000000121100000b2b0W2P9O1Q0p:0Nnc#1Q0iQ0jP9PA1:t9Q0uQ0u@00t93^RnX_AQ02P<O4Q0Y/OnX1A,FAQ03PAQ0a1:r9Q0fQ0f@00r93^'OX1AQ0vP9Q0h1:m9Q0dQ0d@00m93^'OP@Q0eQ0w:0]s<Q0w@00s<+04Q0zP9Q0rQ0k:0]y2Q0k@00y2+04B0]z?vRyB00vz?Rz<0>9%1y/OzP@1:x1/Hw1Vx1,`wQ0xP9Q15/:LQ0y'HQ0{1V|J'`Q0_Q0`P9Q0|/:IRIQ0qP8O3Q0q,2IQ0PQ0QP9Q0o1V]NR]P6O3Q0o/D]P:Q0R1:}P$07R]1V}P$01R}+06RPQ0l96:P&0QP&0PP,9u7E;RPQ0cQ01P9PAP:Q0ZQ0nPVPAQ001:aS$071VaS$01+06Q0O56:'=X1APOQ0NQ0K96:VQ0mA>:oVQ0J96:VA>:VVQ0G96:V20X:V40c41AH03H0LO6b019];R]19u}R}%1]%1}Q0^Q0]P9Q06P~Q0[Q0\Q0gQ0FQ0EQ0DQ0I/:TR}00KF%7}Q18Q19':R}/;FR]#7\d[Q0CQ0M':/sFP}PFP]14}FCU\>1w}FQ1:Q0@':R}/4FR]#7?X]F\[1i}FQ1</:ZR}/4FR]%v]5IF\\1h}FQ1>/:YR}/;F#K\Q1q}FQ1@Q1A':R}/4F/Z}\Q1;}FP0Q1CQ0A':/4FP0Q1EQ1FQ1GQ1HQ1IQ1JQ1KQ1LQ1MQ1NPbP0PKP0Q1OQ1PQ1QQ0HQ1RQ1SQ1TQ1UQ1VQ1WPRP0PUP0Q1XQ1YQ1ZQ1\Q1[Q1^Q1]Q1_Q1`Q1aQ1bP0Q1cP0Q13Q1oP9Q1pP8PZP<Q1r1:7lPGPYPEQ0?Q0BPkPtP^O>b<bfbcbTbSbRbQbPbebbbObNbMbLbKbdbabJbIbHbZbYbGb`bXbWbVbUb0b[b\b]b^Q06/2~eO3b0Q0^Q0]P9Q0SQ0LQ0[Q0\Q0gQ0FQ0EQ0DQ0I?_TWRT00KF%7TQ18Q19;_WRT/;FR~#7\d[Q0CQ0M;_W/sFPTPFP~14TFCU\>1wTFQ1:Q0@;_WRT/4FR>#7?X>F\[1iTFQ1<?_ZWRT/4FR>%v>5IF\\1hTFQ1>?_YWRT/;F#K\Q1qTFQ1@Q1A;_WRT/4F/ZT\Q1;TFP0Q1CQ0A;_W/4FP0Q1EQ1FQ1GQ1HQ1IQ1JQ1KQ1LQ1MQ1NPbP0PKP0Q1OQ1PQ1QQ0HQ1RQ1SQ1TQ1UQ1VQ1WPRP0PUP0Q1XQ1YQ1ZQ1\Q1[Q1^Q1]Q1_Q1`Q1aQ1bP0Q1cP0Q0TQ0UQ1hQ1i80G6P8PgP<PgP2Q1jPEPgDcDcQ0VPhQ07PjPhPhQ05PjQ1k>0_hfCaPjPhPhP4Pj1W`5/o3,NhCaPjPhQ1lPjPhPXPjPh1}D`,NhPjP{FQFQFQQ0WQ0XbDbEbFX40X50X60X70X=0X>0X?0X3eQ1m,Z<\=AXJEF\[131W@0lML\=Q1n12211DELPC[[[[[[^40^50^60^70^=0^>0^?0^3eP9PiP8PZP<1V7lQ1rPYPGPEQ0?Q0BPkPsP_O>b<bfbcbTbSbRbQbPbebbbObNbMbLbKbdbabJbIbHbZbYbGb`bXbWbVbUb0b[b\b]b^Q0SQ0L'2eO3b0H0340kPPeH03H0Lb;b0b:b0W;W:P<P9O2n2001000000121000000b9W9WgP<P9O2n2001000000121000000W0X_AP<P9O2n2001000000121100000b2b0W2P9O1n200100000021100011000b2P:P9PAP:%[c%Ap=\ApCYQ0t#1CBX1:,F:eO4b0fcQ0s5eqeWoWnP<P9O2n2001000000121000000W0WmP<P9O2n2001000000121000000b0b2W2WpP<P9O2n2001000000121000000b2W2P9O1n200100000021100011000b2W|W{P<P9O2n2001000000121000000W0WzP<P9O2n2001000000121000000W0WyP<P9O2n2001000000121000000b~WvWuP<P9O2n2001000000121000000b0b2b0W2Y01P<P9O2n2001000000121000000bkb0WkWlZ07HB1??2<%L<20^?241;eW}Y06WxY04Y05Wwo"). Qed.

#[using="SEGS_in_hull HULL_ok argH_high"] Lemma H_off_segments_cs : forall E cs model, H_off_segments SEGS (hid E cs model).
Proof.
  intros E cs model a Hh. unfold hid in Hh. apply orb_prop in Hh as [Ha|Hv].
  - apply SEGS_in_hull. unfold in_hull. pose proof (argH_high _ _ Ha). pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (?&?&?&?).
    unfold CEIL, KHI in *. apply andb_false_iff. right. apply Z.ltb_ge. lia.
  - apply negb_true_iff in Hv. unfold vis in Hv. apply orb_false_iff in Hv as [Hv _]. apply orb_false_iff in Hv as [Hv _].
    apply SEGS_in_hull. exact Hv.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma mrestrict_munrestrict_clean : forall (H : word -> bool) FULL m',
  (forall a, H a = true -> m' a = None) ->
  mrestrict H (munrestrict H FULL m') = m'.
Proof.
  intros H FULL m' Hc. apply functional_extensionality. intros a.
  unfold mrestrict, munrestrict. destruct (H a) eqn:Ha; [symmetry; apply Hc; exact Ha | reflexivity].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma vis_same : forall E cs model model',
  same_but_materialized model model' -> vis E cs model' = vis E cs model.
Proof.
  intros E cs model model' Hs. pose proof (same_but_materialized_frame _ _ Hs) as Hfr.
  apply functional_extensionality. intros a. unfold vis.
  replace (m_vmmaps model') with (m_vmmaps model) by (symmetry; apply Hfr).
  replace (m_vm_lazy model') with (m_vm_lazy model) by (symmetry; apply Hfr). reflexivity.
Qed.

#[using="Type"] Lemma hid_same : forall E cs model model',
  same_but_materialized model model' -> hid E cs model' = hid E cs model.
Proof. intros. unfold hid. apply functional_extensionality. intros a. rewrite (vis_same _ _ _ _ H). reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma vis_ext : forall E cs cs' model,
  a_vis cs' = a_vis cs -> vis E cs' model = vis E cs model.
Proof. intros E cs cs' model Ha. apply functional_extensionality. intros a. unfold vis, in_allow, in_vis, in_sh. rewrite Ha. reflexivity. Qed.
#[using="Type"] Lemma hid_ext : forall E cs cs' model,
  a_vis cs' = a_vis cs -> hid E cs' model = hid E cs model.
Proof. intros. unfold hid. apply functional_extensionality. intros a. rewrite (vis_ext _ _ _ _ H). reflexivity. Qed.

(* [comment removed for export] *)
#[using="SINV_frame"] Lemma cs_ok_frame : forall E cs R FULL model ss' R' FULL' model',
  cs_ok E cs R FULL model ->
  same_but_materialized model model' ->
  MInv (allowA E cs) model' ->
  regs_ok E (s_regs ss') R' -> s_log ss' = [] ->
  know_ok SEGS E (Mr E cs model FULL') (s_know ss') ->
  (forall a, hid E cs model a = true -> FULL' a = FULL a) ->
  cs_ok E (with_ss cs ss') R' FULL' model'.
Proof.
  intros E cs R FULL model ss' R' FULL' model' HC Hs Hinv HR HL HK Hhid.
  pose proof (same_but_materialized_frame _ _ Hs) as Hfr.
  assert (Evm : m_vmmaps model' = m_vmmaps model) by apply Hfr.
  assert (Elz : m_vm_lazy model' = m_vm_lazy model) by apply Hfr.
  destruct HC. constructor; cbn [with_ss a_ss a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset kn];
    rewrite ?Evm, ?Elz; try assumption.
  - unfold Mr. rewrite (hid_same _ _ _ _ Hs). exact HK.
  - replace (m_halted model') with (m_halted model) by (symmetry; apply Hfr). assumption.
  - unfold fds_ok in *. replace (m_fds model') with (m_fds model) by (symmetry; apply Hfr).
    replace (m_fs model') with (m_fs model) by (symmetry; apply Hfr). assumption.
  - replace (m_fs model') with (m_fs model) by (symmetry; apply Hfr). assumption.
  - intros Ht. replace (m_tid model') with (m_tid model) by (symmetry; apply Hfr). auto.
  - unfold model_ivs_wf in *. rewrite Evm, Elz. assumption.
  - replace (eager_used model') with (eager_used model) by (symmetry; apply Hfr). assumption.
  - intros a Hh. rewrite (hid_same _ _ _ _ Hs) in Hh. rewrite (Hhid a Hh). auto.
  - eapply SINV_frame; [|eassumption]. intros a Ha. apply Hhid. unfold hid. rewrite Ha. reflexivity.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma know_ok_filter : forall E M f k, know_ok SEGS E M k -> know_ok SEGS E M (List.filter f k).
Proof.
  intros E M f k HK. unfold know_ok in *. apply Forall_forall. intros K Hin.
  apply filter_In in Hin as [Hin _]. exact (proj1 (Forall_forall _ _) HK K Hin).
Qed.

#[using="Type"] Lemma cs_ok_set_kn : forall E cs R FULL model k',
  cs_ok E cs R FULL model -> know_ok SEGS E (Mr E cs model FULL) k' ->
  cs_ok E (set_kn cs k') R FULL model.
Proof.
  intros E cs R FULL model k' HC HK.
  destruct HC; constructor; cbn [set_kn with_ss a_ss a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset kn mk_ss s_regs s_log s_know];
    try assumption; reflexivity.
Qed.

#[using="Type"] Lemma cs_gc_ok : forall gb E cs R FULL model, cs_ok E cs R FULL model -> cs_ok E (cs_gc gb cs) R FULL model.
Proof.
  intros gb E cs R FULL model HC. unfold cs_gc. destruct (split_lit (reg cs 2)) as [spb spk].
  apply cs_ok_set_kn; [exact HC|]. apply know_ok_filter. exact (co_know _ _ _ _ _ HC).
Qed.

#[using="Type"] Lemma mk_itab_ranges_acc_sound : forall rs t, itab_sound SEGS t -> itab_sound SEGS (mk_itab_ranges_acc SEGS rs t).
Proof.
  induction rs as [|[lo n] rs IH]; intros t Ht; cbn [mk_itab_ranges_acc]; [exact Ht|].
  apply IH. apply mk_itab_fuel_sound. exact Ht.
Qed.
#[using="Type"] Lemma mk_itab_ranges_sound : forall rs, itab_sound SEGS (mk_itab_ranges SEGS rs).
Proof.
  intros rs. unfold mk_itab_ranges. apply mk_itab_ranges_acc_sound.
  intros pc i. unfold itab_lookup. destruct pc; try discriminate. rewrite pt_get_leaf. discriminate.
Qed.

#[using="Type"] Lemma pc_set_kn : forall cs k, pc (set_kn cs k) = pc cs.
Proof. reflexivity. Qed.
#[using="Type"] Lemma pc_cs_gc : forall gb cs, pc (cs_gc gb cs) = pc cs.
Proof. intros gb cs. unfold cs_gc. destruct (split_lit (reg cs 2)); reflexivity. Qed.

#[using="Type"] Lemma drop_ixs_incl : forall ixs i k K, In K (drop_ixs ixs i k) -> In K k.
Proof.
  intros ixs i k. revert i. induction k as [|K' r IH]; intros i K Hin; cbn [drop_ixs] in Hin.
  - exact Hin.
  - destruct (existsb (Nat.eqb i) ixs).
    + right. eapply IH. exact Hin.
    + destruct Hin as [<-|Hin]; [left; reflexivity | right; eapply IH; exact Hin].
Qed.

#[using="Type"] Lemma forget_sound : forall E cs R FULL model ixs,
  cs_ok E cs R FULL model -> cs_ok E (set_kn cs (drop_ixs ixs 0 (kn cs))) R FULL model.
Proof.
  intros E cs R FULL model ixs HC. apply cs_ok_set_kn; [exact HC|].
  unfold know_ok. apply Forall_forall. intros K Hin. apply drop_ixs_incl in Hin.
  exact (proj1 (Forall_forall _ _) (co_know _ _ _ _ _ HC) K Hin).
Qed.

(* [comment removed for export] *)
Definition kfoot (E : env) (K : kentry) : option (Z * Z) :=
  match K with
  | KWord a w _ => Some (estart E a, Z.of_nat w)
  | KZero a l => Some (estart E a, elenZ E l)
  | KBlob a l _ => Some (estart E a, elenZ E l)
  | KImg lo hi => Some (lo, hi - lo)%Z
  | KWr a n => Some (estart E a, elenZ E n)
  | KFill a l _ => Some (estart E a, elenZ E l)
  | KUnk a l => Some (estart E a, elenZ E l)
  | KAlign _ _ | KRange _ _ _ | KDisj _ _ _ _ => None
  end.

Definition kfoot_apart (E : env) (K : kentry) (lo n : Z) : Prop :=
  match kfoot E K with
  | None => True
  | Some (s, l) => (s + l <= lo \/ lo + n <= s)%Z
  end.

#[using="Type"] Lemma kentry_keep_sem : forall E M M' K lo n,
  kentry_ok SEGS E M K -> kfoot_apart E K lo n ->
  (forall x : word, (bv_unsigned x < lo \/ lo + n <= bv_unsigned x)%Z -> M' x = M x) ->
  kentry_ok SEGS E M' K.
Proof.
  intros E M M' K lo n HK Hap Hout.
  assert (RD : forall (a : word) k, (bv_unsigned a + Z.of_nat k <= 2 ^ 64)%Z ->
     (bv_unsigned a + Z.of_nat k <= lo \/ lo + n <= bv_unsigned a)%Z ->
     rdn SEGS M' a k = rdn SEGS M a k).
  { intros a k Hnw Hd. apply rdn_ext; [exact Hnw|]. intros x Hx. apply Hout. lia. }
  unfold kfoot_apart, kfoot in Hap.
  destruct K as [[b k] w v|[b k] nn|[b k] nn kb|ilo ihi|e m|e rlo rhi|[b k] nn|a1 n1 a2 n2|[b k] nn fc|[b k] nn]; cbn [kentry_ok] in *;
    try exact HK.
  7: { (* [comment removed for export] *) destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
    destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia. }
  6: { (* [comment removed for export] *) destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
    destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia. }
  - (* [comment removed for export] *) destruct HK as (Hw & Hfl & Hrd). split; [exact Hw|]. split; [exact Hfl|].
    rewrite RD; [exact Hrd | rewrite (flat_u E _ _ Hfl); destruct Hfl; lia | rewrite (flat_u E _ _ Hfl); lia].
  - (* [comment removed for export] *) destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
    destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
  - (* [comment removed for export] *) destruct HK as (Hfl & Hlen & Hz). split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi.
    destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
  - (* [comment removed for export] *) destruct HK as (HA & HB & HC). split; [exact HA|]. split; [exact HB|]. intros i Hi.
    rewrite Hout; [apply HC; lia|]. rewrite u64_lit by lia. lia.
  - (* [comment removed for export] *) destruct HK as [Hfl Hs]. split; [exact Hfl|]. intros d m Hd0 Hdm.
    pose proof (Hs d m Hd0 Hdm) as H. destruct Hfl as (F1 & F2 & F3 & F4).
    destruct m as [|m']; [reflexivity|].
    apply store_ok_of_all; [rewrite u64_lit by lia; lia|].
    intros x Hx. rewrite u64_lit in Hx by lia.
    unfold wview. rewrite Hout by lia. fold (wview SEGS M x).
    eapply (store_ok_all SEGS M (Datatypes.S m')); [| exact H |]; rewrite u64_lit by lia; lia.
Qed.

#[using="Type"] Lemma elenZ_lit : forall E z, (0 <= z < 2 ^ 64)%Z -> elenZ E (ELit z) = z.
Proof. intros E z Hz. unfold elenZ. cbn [edenot]. rewrite u64_lit by lia. reflexivity. Qed.

#[using="Type"] Lemma kentry_apart_b_sem : forall E M allkn K ub uk un,
  know_ok SEGS E M allkn -> kentry_apart_b allkn ub uk un K = true ->
  kfoot_apart E K (estart E (SA ub uk)) (elenZ E un).
Proof.
  intros E M allkn K ub uk un Hall Hb. unfold kfoot_apart, kfoot.
  destruct K as [[b k] w v|[b k] nn|[b k] nn kb|ilo ihi|e m|e rlo rhi|[b k] nn|a1 n1 a2 n2|[b k] nn fc|[b k] nn]; cbn [kentry_apart_b] in Hb;
    try exact I; try discriminate.
  7: { pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb). lia. }
  6: { pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb). lia. }
  - apply andb_prop in Hb as [Hw Hb]. apply Nat.leb_le in Hw.
    pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb) as Hd.
    rewrite (elenZ_lit E (Z.of_nat w)) in Hd by lia. lia.
  - pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb). lia.
  - pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb). lia.
  - apply andb_prop in Hb as [Hb Hap]. apply andb_prop in Hb as [Hb Hlt]. apply andb_prop in Hb as [H0 Hl].
    apply Z.leb_le in H0. apply Z.leb_le in Hl. apply Z.ltb_lt in Hlt. unfold two64 in Hlt.
    pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hap) as Hd.
    rewrite (elenZ_lit E (ihi - ilo)) in Hd by lia.
    unfold estart in Hd at 2 3. cbn [a_base a_off edenot] in Hd.
    rewrite !u64_lit in Hd by lia. lia.
  - pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb). lia.
Qed.

#[using="Type"] Lemma kentry_apart_keep : forall E M M' allkn K (ub : expr) uk un,
  know_ok SEGS E M allkn -> kentry_ok SEGS E M K ->
  kentry_apart_b allkn ub uk un K = true ->
  (forall x : word, (bv_unsigned x < estart E (SA ub uk) \/ estart E (SA ub uk) + elenZ E un <= bv_unsigned x)%Z ->
                     M' x = M x) ->
  kentry_ok SEGS E M' K.
Proof.
  intros E M M' allkn K ub uk un Hall HK Hb Hout.
  eapply kentry_keep_sem; [exact HK | eapply kentry_apart_b_sem; [exact Hall | exact Hb] | exact Hout].
Qed.

#[using="Type"] Lemma know_ok_filter_apart : forall E M M' k (f : kentry -> bool) (ub : expr) uk un,
  know_ok SEGS E M k ->
  (forall K, In K k -> f K = true -> kentry_apart_b k ub uk un K = true \/ kentry_ok SEGS E M' K) ->
  (forall x : word, (bv_unsigned x < estart E (SA ub uk) \/ estart E (SA ub uk) + elenZ E un <= bv_unsigned x)%Z ->
                     M' x = M x) ->
  know_ok SEGS E M' (List.filter f k).
Proof.
  intros E M M' k f ub uk un HK Hf Hout. unfold know_ok. apply Forall_forall. intros K Hin.
  apply filter_In in Hin as [Hin Hfk].
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  destruct (Hf K Hin Hfk) as [Hap | Hdone]; [|exact Hdone].
  eapply kentry_apart_keep; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma kentry_apart_bp_eq : forall allkn ub uk un K,
  kentry_apart_bp allkn (mk_sprep allkn ub uk un) ub uk un K = kentry_apart_b allkn ub uk un K.
Proof.
  intros allkn ub uk un K. destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
    cbn [kentry_apart_bp kentry_apart_b]; rewrite ?ranges_apart_p_eq; reflexivity.
Qed.

#[using="Type"] Lemma havoc1p_eq : forall k ub uk un K,
  havoc1p k (mk_sprep k ub uk un) ub uk un K = havoc1 k ub uk un K.
Proof. intros. unfold havoc1p, havoc1. rewrite kentry_apart_bp_eq. reflexivity. Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma know_ok_havoc : forall E M M' k b o n,
  know_ok SEGS E M k ->
  (forall x : word, (bv_unsigned x < estart E (SA b o) \/ estart E (SA b o) + elenZ E n <= bv_unsigned x)%Z -> M' x = M x) ->
  mem_grows M M' ->
  know_ok SEGS E M' (kn_havoc k b o n).
Proof.
  intros E M M' k b o n HK Hout Hg. unfold kn_havoc, know_ok. cbv zeta.
  apply Forall_flat_map. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HKK.
  rewrite havoc1p_eq. unfold havoc1.
  destruct (kwr_b K || kentry_apart_b k b o n K)%bool eqn:Hf.
  - apply Forall_one. apply orb_prop in Hf as [Hw|Ha].
    + destruct K as [| | | | | |[wb wk] wn| | |]; try discriminate.
      destruct HKK as [Hfl Hs]. cbn [kentry_ok]. split; [exact Hfl|].
      intros d m Hd Hdm. eapply store_ok_mono; [exact Hg | apply Hs; assumption].
    + eapply kentry_apart_keep; eassumption.
  - destruct K as [|[kb kk] len| | | | | | |[kb kk] len fc|[kb kk] len]; try constructor.
    + eapply kzero_cut_sound; [exact HK | exact HKK | exact Hout].
    + eapply kfill_cut_sound; [exact HK | exact HKK | exact Hout].
    + eapply kunk_cut_sound; [exact HK | exact HKK | exact Hout].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pw_kind (mk : saddr -> expr -> kentry) (P : (word -> option byte) -> word -> Prop) : Prop :=
  forall E M a n,
    kentry_ok SEGS E M (mk a n)
    <-> (flat E a (elenZ E n) /\ forall i, (0 <= i < elenZ E n)%Z -> P M (Z_to_bv 64 (estart E a + i))).

#[using="Type"] Lemma pw_kind_zf : forall mk byteof, zf_kind SEGS mk byteof -> pw_kind mk (fun M x => byteof (M x)).
Proof. intros mk byteof H E M a n. exact (H E M a n). Qed.

#[using="Type"] Lemma pw_kind_wr : pw_kind KWr (fun M x => wview SEGS M x <> None).
Proof.
  intros E M a n. cbn [kentry_ok]. split; intros [Hfl H]; split; try exact Hfl.
  - intros i Hi. pose proof (H i 1%nat ltac:(lia) ltac:(cbn; lia)) as S1. cbn [store_ok] in S1.
    destruct (wview SEGS M (Z_to_bv 64 (estart E a + i))); [discriminate | discriminate].
  - intros d m Hd Hdm. pose proof Hfl as Hfl0. destruct Hfl as (F1 & F2 & F3 & F4).
    destruct m as [|m']; [reflexivity|]. set (m := Datatypes.S m') in *.
    assert (Hm : 1 <= Z.of_nat m) by (subst m; rewrite Nat2Z.inj_succ; lia).
    assert (Hu : bv_unsigned (Z_to_bv 64 (estart E a + d)) = estart E a + d) by (apply u_small; lia).
    apply store_ok_of_all; rewrite Hu; [lia|].
    intros x Hx. replace x with (Z_to_bv 64 (estart E a + (bv_unsigned x - estart E a))).
    + apply H. lia.
    + apply bv_eq. rewrite u_small; [lia|]. pose proof (u64_range x). lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma kcut_pw_sound : forall mk P E M0 M M' allkn wb wk wn kb kk len,
  pw_kind mk P ->
  know_ok SEGS E M0 allkn ->
  kentry_ok SEGS E M (mk (SA kb kk) len) ->
  (forall x : word,
     (bv_unsigned x < estart E (SA wb wk) \/ estart E (SA wb wk) + elenZ E wn <= bv_unsigned x)%Z ->
     P M x -> P M' x) ->
  Forall (kentry_ok SEGS E M') (kcut mk allkn wb wk wn kb kk len).
Proof.
  intros mk P E M0 M M' allkn wb wk wn kb kk len Hkind Hall HK Hout.
  apply (proj1 (Hkind E M _ _)) in HK. destruct HK as [Hfl Hz].
  unfold kcut.
  set (ws := mkAlu ALU_ADD wb (ELit wk)). set (ks := mkAlu ALU_ADD kb (ELit kk)).
  assert (Uws : eqm (bv_unsigned (edenot E ws)) (estart E (SA wb wk))).
  { subst ws. rewrite mkAlu_denot. unfold estart; cbn [a_base a_off edenot].
    eapply eqm_trans; [apply u_add_eqm|]. apply eqm_add; [apply eqm_refl|apply eqm_u_lit]. }
  assert (Uks : eqm (bv_unsigned (edenot E ks)) (estart E (SA kb kk))).
  { subst ks. rewrite mkAlu_denot. unfold estart; cbn [a_base a_off edenot].
    eapply eqm_trans; [apply u_add_eqm|]. apply eqm_add; [apply eqm_refl|apply eqm_u_lit]. }
  pose proof Hfl as Hfl0. destruct Hfl as (F1 & F2 & F3 & F4).
  apply Forall_app; split.
  - (* [comment removed for export] *)
    destruct (lin_ge0 allkn [(kb, kk)] [(wb, wk)]); [constructor|].
    destruct (lin_ge0 allkn [(wb, wk)] [(kb, kk)]) eqn:H1; [|constructor].
    destruct (lin_ge0 allkn [(kb, kk); (len, 0%Z)] [(wb, wk)]) eqn:H2; [|constructor].
    pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall H1) as A0. cbn [xt_den] in A0.
    pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall H2) as B0. cbn [xt_den] in B0.
    constructor; [|constructor]. apply (proj2 (Hkind E M' _ _)).
    assert (HL : elenZ E (mkAlu ALU_SUB ws ks) = (estart E (SA wb wk) - estart E (SA kb kk))%Z).
    { unfold elenZ. rewrite mkAlu_denot.
      assert (eqm (bv_unsigned (alu64 ALU_SUB (edenot E ws) (edenot E ks))) (estart E (SA wb wk) - estart E (SA kb kk))) as [q Hq].
      { eapply eqm_trans; [apply u_sub_eqm|]. apply eqm_add; [exact Uws|]. destruct Uks as [q Hq]. exists (-q)%Z. lia. }
      pose proof (u64_range (alu64 ALU_SUB (edenot E ws) (edenot E ks))) as R.
      pose proof (u64_range (edenot E len)) as RL.
      unfold flat, estart, elenZ in *; cbn [a_base a_off] in *. lia. }
    rewrite HL. split.
    + unfold flat in *. unfold estart, elenZ in *; cbn [a_base a_off] in *. lia.
    + intros i Hi. apply Hout; [|apply Hz]; unfold estart, elenZ in *; cbn [a_base a_off] in *; [|lia].
      left. rewrite u_small; lia.
  - (* [comment removed for export] *)
    destruct (lin_ge0 allkn [(kb, kk); (len, 0%Z)] [(wb, wk); (wn, 0%Z)]) eqn:H1; [|constructor].
    destruct (lin_ge0 allkn [(wb, wk); (wn, 0%Z)] [(kb, kk)]) eqn:H2; [|constructor].
    destruct (lin_ge0 allkn [(ELit 0, (two64 - 1)%Z)] [(kb, kk); (len, 0%Z)]) eqn:H3; [|constructor].
    pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall H1) as A0. cbn [xt_den] in A0.
    pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall H2) as B0. cbn [xt_den] in B0.
    pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall H3) as C0. cbn [xt_den edenot] in C0.
    rewrite u_lit0 in C0. unfold two64 in C0.
    cbv zeta.
    set (we := mkAlu ALU_ADD ws wn).
    assert (Uwe : eqm (bv_unsigned (edenot E we)) (estart E (SA wb wk) + elenZ E wn)).
    { subst we. rewrite mkAlu_denot. eapply eqm_trans; [apply u_add_eqm|]. apply eqm_add; [exact Uws|apply eqm_refl]. }
    destruct (split_lit we) as [hb ho] eqn:Hsp.
    lazymatch goal with |- Forall _ [mk ?ha0 _] => set (ha := ha0) end.
    assert (Hst : estart E ha = (estart E (SA wb wk) + elenZ E wn)%Z).
    { subst ha.
      destruct (lin_ge0 allkn [(hb, ho)] [(wb, wk); (wn, 0%Z)] && lin_ge0 allkn [(wb, wk); (wn, 0%Z)] [(hb, ho)])%bool eqn:Hh.
      - apply andb_prop in Hh as [Hh1 Hh2].
        pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall Hh1) as C1. cbn [xt_den] in C1.
        pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall Hh2) as C2. cbn [xt_den] in C2.
        unfold estart, elenZ in *; cbn [a_base a_off] in *. lia.
      - unfold estart at 1; cbn [a_base a_off]. rewrite Z.add_0_r.
        destruct Uwe as [q Hq]. pose proof (u64_range (edenot E we)).
        pose proof (u64_range (edenot E len)) as RL.
        unfold flat, estart, elenZ in *; cbn [a_base a_off] in *. lia. }
    assert (HL : elenZ E (mkAlu ALU_SUB (mkAlu ALU_ADD ks len) we)
                 = (estart E (SA kb kk) + elenZ E len - (estart E (SA wb wk) + elenZ E wn))%Z).
    { unfold elenZ at 1. rewrite mkAlu_denot.
      assert (eqm (bv_unsigned (alu64 ALU_SUB (edenot E (mkAlu ALU_ADD ks len)) (edenot E we)))
                  (estart E (SA kb kk) + elenZ E len - (estart E (SA wb wk) + elenZ E wn))) as [q Hq].
      { eapply eqm_trans; [apply u_sub_eqm|]. apply eqm_add.
        - rewrite mkAlu_denot. eapply eqm_trans; [apply u_add_eqm|]. apply eqm_add; [exact Uks|apply eqm_refl].
        - destruct Uwe as [q Hq]. exists (-q)%Z. lia. }
      pose proof (u64_range (alu64 ALU_SUB (edenot E (mkAlu ALU_ADD ks len)) (edenot E we))) as R.
      pose proof (u64_range (edenot E len)) as RL.
      unfold flat, estart, elenZ in *; cbn [a_base a_off] in *. lia. }
    constructor; [|constructor]. apply (proj2 (Hkind E M' _ _)). rewrite HL.
    split.
    + unfold flat. rewrite Hst. pose proof (u64_range (edenot E len)) as RL.
      unfold flat, estart, elenZ in *; cbn [a_base a_off] in *. lia.
    + intros i Hi. rewrite Hst.
      apply Hout.
      * right. pose proof (u64_range (edenot E len)) as RL.
        rewrite u_small; unfold flat, estart, elenZ in *; cbn [a_base a_off] in *; lia.
      * replace (estart E (SA wb wk) + elenZ E wn + i)%Z
          with (estart E (SA kb kk) + (estart E (SA wb wk) + elenZ E wn - estart E (SA kb kk) + i))%Z by lia.
        apply Hz. unfold estart, elenZ in *; cbn [a_base a_off] in *. lia.
Qed.

#[using="Type"] Lemma kwr_cut_sound : forall E M0 M M' allkn wb wk wn kb kk len,
  know_ok SEGS E M0 allkn ->
  kentry_ok SEGS E M (KWr (SA kb kk) len) ->
  (forall x : word,
     (bv_unsigned x < estart E (SA wb wk) \/ estart E (SA wb wk) + elenZ E wn <= bv_unsigned x)%Z ->
     M' x = M x) ->
  Forall (kentry_ok SEGS E M') (kwr_cut allkn wb wk wn kb kk len).
Proof.
  intros. eapply (kcut_pw_sound KWr _ E M0 M M'); [apply pw_kind_wr | eassumption | eassumption |].
  intros x Hx HP. unfold wview in *. rewrite (H1 x Hx). exact HP.
Qed.

#[using="Type"] Lemma cutout1p_eq : forall k ub uk un K,
  cutout1p k (mk_sprep k ub uk un) ub uk un K = cutout1 k ub uk un K.
Proof. intros. unfold cutout1p, cutout1. rewrite kentry_apart_bp_eq. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma know_ok_cutout : forall E M M' k b o n,
  know_ok SEGS E M k ->
  (forall x : word, (bv_unsigned x < estart E (SA b o) \/ estart E (SA b o) + elenZ E n <= bv_unsigned x)%Z -> M' x = M x) ->
  know_ok SEGS E M' (kn_cutout k b o n).
Proof.
  intros E M M' k b o n HK Hout. unfold kn_cutout, know_ok. cbv zeta.
  apply Forall_flat_map. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HKK.
  rewrite cutout1p_eq. unfold cutout1.
  destruct (kentry_apart_b k b o n K) eqn:Hf.
  - apply Forall_one. eapply kentry_apart_keep; eassumption.
  - destruct K as [|[kb kk] len| | | | |[kb kk] len| |[kb kk] len fc|[kb kk] len]; try constructor.
    + eapply kzero_cut_sound; [exact HK | exact HKK | exact Hout].
    + eapply kwr_cut_sound; [exact HK | exact HKK | exact Hout].
    + eapply kfill_cut_sound; [exact HK | exact HKK | exact Hout].
    + eapply kunk_cut_sound; [exact HK | exact HKK | exact Hout].
Qed.

#[using="Type"] Lemma droprange_sound : forall E cs R FULL model b n,
  cs_ok E cs R FULL model -> cs_ok E (node_droprange cs b n) R FULL model.
Proof.
  intros E cs R FULL model b n HC. unfold node_droprange. destruct (split_lit b) as [bb bk].
  apply cs_ok_set_kn; [exact HC|]. eapply know_ok_havoc; [exact (co_know _ _ _ _ _ HC) | intros; reflexivity | apply mem_grows_refl].
Qed.

#[using="Type"] Lemma bump_sound : forall E cs R FULL model m cs',
  cs_ok E cs R FULL model -> node_bump cs m = Some cs' -> cs_ok E cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros E cs R FULL model m cs' HC H. unfold node_bump in H. destruct (Nat.leb (nxt cs) m); [|discriminate]. injection H as <-.
  split; [|reflexivity].
  destruct HC; constructor; cbn [bump with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset];
    try assumption; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mkind_eqb_eq : forall a b, mkind_eqb a b = true -> a = b.
Proof. intros [] []; cbn; intros; first [reflexivity | discriminate]. Qed.
#[using="Type"] Lemma kentry_eqb_eq : forall x y, kentry_eqb x y = true -> x = y.
Proof.
  intros x y H. destruct x, y; cbn [kentry_eqb] in H; try discriminate;
  repeat match goal with
    | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
    end;
  repeat match goal with
    | H : saddr_eqb _ _ = true |- _ => apply saddr_eqb_eq in H
    | H : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in H
    | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
    | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
    end; subst; reflexivity.
Qed.
#[using="Type"] Lemma amap_eqb_eq : forall x y, amap_eqb x y = true -> x = y.
Proof.
  intros [b l k] [b' l' k'] H. unfold amap_eqb in H. cbn [am_base am_len am_kind] in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply expr_eqb_eq in H1. apply expr_eqb_eq in H2. apply mkind_eqb_eq in H3. congruence.
Qed.
#[using="Type"] Lemma pair_eqb_eq : forall x y, pair_eqb x y = true -> x = y.
Proof.
  intros [a b] [a' b'] H. unfold pair_eqb in H. cbn [fst snd] in H. apply andb_prop in H as [H1 H2].
  apply expr_eqb_eq in H1. apply expr_eqb_eq in H2. congruence.
Qed.
#[using="Type"] Lemma afd_eqb_eq : forall x y, afd_eqb x y = true -> x = y.
Proof.
  intros [|k l o|] [|k' l' o'|] H; cbn [afd_eqb] in H; try discriminate; try reflexivity.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Nat.eqb_eq in H1. apply expr_eqb_eq in H2. apply expr_eqb_eq in H3. congruence.
Qed.
#[using="Type"] Lemma list_eqb_eq : forall {T} (eqb : T -> T -> bool), (forall x y, eqb x y = true -> x = y) ->
  forall x y, list_eqb eqb x y = true -> x = y.
Proof.
  intros T eqb Heq x. induction x as [|a x IH]; intros [|b y] H; cbn [list_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. rewrite (Heq _ _ H1), (IH _ H2). reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kimg_in_hull (k : list kentry) : Prop :=
  Forall (fun K => match K with KImg lo hi => img_lo A <= lo /\ hi <= img_hi A | _ => True end) k.

#[using="Type"] Lemma kimg_clip_in_hull : forall k, kimg_in_hull (kimg_clip A k).
Proof.
  intros k. unfold kimg_in_hull, kimg_clip. apply Forall_forall. intros K Hin. apply filter_In in Hin as [_ Hb].
  destruct K; try exact I. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H3. lia.
Qed.

#[using="Type"] Lemma kimg_clip_incl : forall k K, In K (kimg_clip A k) -> In K k.
Proof. intros k K H. unfold kimg_clip in H. apply filter_In in H as [H _]. exact H. Qed.

#[using="Type"] Lemma kimg_in_hull_app : forall k1 k2, kimg_in_hull k1 -> kimg_in_hull k2 -> kimg_in_hull (k1 ++ k2).
Proof. intros. unfold kimg_in_hull in *. apply Forall_app. auto. Qed.

(* [comment removed for export] *)
#[using="HULL_ok argH_high"] Lemma hid_hull : forall E cs model (a : word), in_hull A (bv_unsigned a) = true -> hid E cs model a = false.
Proof.
  intros E cs model a Hh. unfold hid, vis. rewrite Hh. cbn [orb].
  destruct (argH E a) eqn:Ha; [|reflexivity]. exfalso.
  pose proof (argH_high _ _ Ha). unfold in_hull in Hh. apply andb_prop in Hh as [_ Hh]. apply Z.ltb_lt in Hh.
  pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (?&?&?&?). unfold CEIL, KHI in *. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rdn_visible : forall (H : word -> bool) FULL (a : word) w bs,
  H_off_segments SEGS H ->
  rdn SEGS (mrestrict H FULL) a w = Some bs ->
  forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat w -> H x = false.
Proof.
  intros H FULL a w. revert a. induction w as [|w IH]; intros a bs HH Hr x Hx; [lia|].
  cbn [rdn] in Hr. unfold mrestrict in Hr at 1.
  destruct (H a) eqn:Ha.
  - (* [comment removed for export] *)
    assert (Hs : seg_rom SEGS a = None).
    { unfold seg_rom. rewrite (memory_read1_hidden SEGS H HH a Ha). reflexivity. }
    rewrite Hs in Hr. discriminate.
  - destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
    + assert (x = a) by (apply bv_eq; exact Heq). subst x. exact Ha.
    + fold (mrestrict H FULL) in Hr.
      destruct (match FULL a with Some b => Some b | None => seg_rom SEGS a end) as [b|]; [|discriminate].
      destruct (rdn SEGS (mrestrict H FULL) (a + 1)%bv w) as [rest|] eqn:Hr2; [|discriminate].
      pose proof (u64_range x).
      assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
      eapply (IH (a + 1)%bv rest HH Hr2). rewrite Hu1. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma know_ok_unhide : forall E (H1 H2 : word -> bool) FULL k,
  H_off_segments SEGS H1 ->
  kimg_in_hull k ->
  (forall a, H2 a = true -> H1 a = true) ->
  (forall a : word, in_hull A (bv_unsigned a) = true -> H1 a = false) ->
  know_ok SEGS E (mrestrict H1 FULL) k -> know_ok SEGS E (mrestrict H2 FULL) k.
Proof.
  intros E H1 H2 FULL k HH1 Hki Hsub Hhull HK.
  assert (AG : forall a, H1 a = false -> mrestrict H2 FULL a = mrestrict H1 FULL a).
  { intros a Ha. unfold mrestrict. rewrite Ha. destruct (H2 a) eqn:Ha2; [|reflexivity].
    rewrite (Hsub a Ha2) in Ha. discriminate. }
  assert (GR : mem_grows (mrestrict H1 FULL) (mrestrict H2 FULL)).
  { intros x Hx. unfold mrestrict in *. destruct (H1 x) eqn:H1x; [exfalso; apply Hx; reflexivity|].
    destruct (H2 x) eqn:H2x; [rewrite (Hsub x H2x) in H1x; discriminate | exact Hx]. }
  unfold know_ok in *. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  pose proof (proj1 (Forall_forall _ _) Hki K Hin) as HKi.
  destruct K as [a w v|a n|a n kb|lo hi|e m|e lo hi|a n|a1 n1 a2 n2|a n fc|a n]; cbn [kentry_ok] in *; try exact HKK.
  7: { (* [comment removed for export] *) destruct HKK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
    pose proof (Hz i Hi) as Hzi. rewrite AG; [exact Hzi|].
    unfold mrestrict in Hzi |- *. destruct (H1 _); [exfalso; apply Hzi; reflexivity | reflexivity]. }
  - (* [comment removed for export] *) destruct HKK as (Hw & Hfl & Hrd). split; [exact Hw|]. split; [exact Hfl|].
    rewrite <- Hrd. apply rdn_ext.
    + rewrite (flat_u E _ _ Hfl). destruct Hfl as (?&?&?&?). lia.
    + intros x Hx. apply AG. eapply rdn_visible; [exact HH1 | exact Hrd | exact Hx].
  - (* [comment removed for export] *) destruct HKK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
    pose proof (Hz i Hi) as Hzi. rewrite AG; [exact Hzi|].
    unfold mrestrict in Hzi. destruct (H1 _); [discriminate | reflexivity].
  - (* [comment removed for export] *) destruct HKK as (Hfl & Hlen & Hz). split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi.
    pose proof (Hz i Hi) as Hzi. rewrite AG; [exact Hzi|].
    unfold mrestrict in Hzi. destruct (H1 _); [discriminate | reflexivity].
  - (* [comment removed for export] *) destruct HKK as (HA & HB & HC). split; [exact HA|]. split; [exact HB|]. intros i Hi.
    assert (Hh : in_hull A (bv_unsigned (Z_to_bv 64 i)) = true).
    { unfold in_hull. rewrite u64_lit by lia. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    rewrite AG; [apply HC; exact Hi | apply Hhull; exact Hh].
  - (* [comment removed for export] *) destruct HKK as [Hfl Hs]. split; [exact Hfl|]. intros d m Hd Hdm.
    eapply store_ok_mono; [exact GR | apply Hs; assumption].
  - (* [comment removed for export] *) destruct HKK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
    pose proof (Hz i Hi) as Hzi. rewrite AG; [exact Hzi|].
    unfold mrestrict in Hzi. destruct (H1 _); [discriminate | reflexivity].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma vis_mono : forall E cs cs' model a,
  (forall z, in_allow E cs z = true -> in_allow E cs' z = true) ->
  vis E cs model a = true -> vis E cs' model a = true.
Proof.
  intros E cs cs' model a Hm H. unfold vis in *.
  apply orb_true_iff in H. apply orb_true_iff. destruct H as [H|H]; [left; exact H|]. right.
  apply andb_true_iff in H as [H1 H2]. apply andb_true_iff. split; [exact H1|].
  apply orb_true_iff in H2. apply orb_true_iff. destruct H2 as [H2|H2]; [left; exact H2|]. right. apply Hm. exact H2.
Qed.

#[using="Type"] Lemma in_allow_cons : forall E cs p ss tot ylo eg gh ab brk fd tid z,
  in_allow E cs z = true -> in_allow E (ACS ss (a_maps cs) tot ylo eg (p :: a_vis cs) gh ab brk fd tid) z = true.
Proof.
  intros. unfold in_allow, in_vis, in_sh in *. cbn [a_vis existsb].
  apply orb_true_iff in H. apply orb_true_iff.
  destruct H as [H|H]; [left|right]; apply orb_true_iff; right; exact H.
Qed.

#[using="Type"] Lemma hid_cons_sub : forall E cs p model a ss tot ylo eg gh ab brk fd tid,
  hid E (ACS ss (a_maps cs) tot ylo eg (p :: a_vis cs) gh ab brk fd tid) model a = true -> hid E cs model a = true.
Proof.
  intros E cs p model a ss tot ylo eg gh ab brk fd tid H. unfold hid in *.
  apply orb_true_iff in H. apply orb_true_iff. destruct H as [H|H]; [left; exact H|]. right.
  apply negb_true_iff in H. apply negb_true_iff.
  destruct (vis E cs model a) eqn:Hv; [|reflexivity].
  rewrite (vis_mono E cs _ model a (fun z Hz => in_allow_cons E cs p ss tot ylo eg gh ab brk fd tid z Hz) Hv) in H. discriminate.
Qed.

#[using="Type"] Lemma A_bytes_app : forall l1 l2, A_bytes (l1 ++ l2) = A_bytes l1 + A_bytes l2.
Proof. intros l1 l2. induction l1; cbn [A_bytes app]; [lia|]. rewrite IHl1. lia. Qed.

#[using="Type"] Lemma page_allowedb_app_r : forall l1 l2 p, page_allowedb l2 p = true -> page_allowedb (l1 ++ l2) p = true.
Proof. intros. unfold page_allowedb in *. rewrite existsb_app, H. apply orb_true_r. Qed.

#[using="Type"] Lemma MInv_app : forall l1 l2 m, MInv l2 m -> eager_used m + A_bytes (l1 ++ l2) <= vm_limit (m_vmmaps m) -> MInv (l1 ++ l2) m.
Proof.
  intros l1 l2 m [N1 N2 N3 N4 N5] Hb. constructor; try assumption.
  intros p Hp. apply page_allowedb_app_r. apply N3. exact Hp.
Qed.

#[using="Type"] Lemma in_ivs_true : forall z l, in_ivs z l = true <-> exists iv, In iv l /\ bv_unsigned (fst iv) <= z < bv_unsigned (fst iv) + bv_unsigned (snd iv).
Proof.
  intros z l. unfold in_ivs. rewrite existsb_exists. split.
  - intros [iv [Hin Hb]]. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. eauto.
  - intros [iv [Hin Hb]]. exists iv. split; [exact Hin|]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

#[using="Type"] Lemma split_lit_denot : forall E e b k, split_lit e = (b, k) ->
  edenot E e = Z_to_bv 64 (bv_unsigned (edenot E b) + k).
Proof.
  intros E e b k H.
  assert (G : forall e' : expr, edenot E e' = Z_to_bv 64 (bv_unsigned (edenot E e') + 0)).
  { intros e'. rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
  unfold split_lit in H.
  destruct e; try (injection H as <- <-; apply G).
  - injection H as <- <-. cbn [edenot]. rewrite u64_lit by (unfold two64; lia). rewrite Z.add_0_l. reflexivity.
  - lazymatch type of H with (match ?o with _ => _ end = _) => destruct o end; try (injection H as <- <-; apply G).
    lazymatch type of H with (match ?y with _ => _ end = _) => destruct y end; try (injection H as <- <-; apply G).
    injection H as <- <-. cbn [edenot]. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Z.add_mod_idemp_r by lia. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma flat_x_sound : forall E M k b off n,
  know_ok SEGS E M k -> flat_x k b off n = true ->
  0 <= estart E (SA b off) /\ estart E (SA b off) + bv_unsigned (edenot E n) <= 2 ^ 64 /\ 0 < bv_unsigned (edenot E n).
Proof.
  intros E M k b off n HK H. unfold flat_x in H.
  destruct (base_range k b) as [[lo hi]|] eqn:Hb; [|discriminate].
  destruct (xlo k n) as [nl|] eqn:Hnl; [|discriminate]. destruct (xhi k n) as [nh|] eqn:Hnh; [|discriminate].
  apply andb_prop in H as [H Hn]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in Hn. unfold two64 in H2.
  pose proof (base_range_sound SEGS E M k b lo hi HK Hb). pose proof (xlo_sound SEGS E M k n nl HK Hnl). pose proof (xhi_sound SEGS E M k n nh HK Hnh).
  unfold estart. cbn [a_base a_off]. lia.
Qed.

#[using="Type"] Lemma u_of_split : forall E e b k, split_lit e = (b, k) ->
  0 <= estart E (SA b k) < 2 ^ 64 -> bv_unsigned (edenot E e) = estart E (SA b k).
Proof.
  intros E e b k Hs Hr. rewrite (split_lit_denot E e b k Hs). unfold estart in *. cbn [a_base a_off] in *.
  apply u64_lit. lia.
Qed.

#[using="HS XN XE XB KC"] Lemma pageup_pagedown_gap : forall a b, a <= b -> pageup b - pagedown a <= b - a + 8190.
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
ltac2:(KReplay.run1 (kr_t_AsanPlanSound ()) ["FPX_3"; "Sound"] "h04__p1h14__p2h24__x1h34__x2h44__x3h54__x4h64__x5h74__x6h81Hh92H0h:2H1h;2H2h<2H3h=2H4h>2H5h?2H6h@2H7hA2H8hB2H9hC7__arithhD4__ffhE6__sat0hF6__sat1hG8__varmaphH5__withI1ahJ1bhK1qhL2q0hM1rhN2r0p;2p;1p;3p;4p;6p;7p;8p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0p10038p4p710R5p9P0p1003Vp4p710R6p9P0p1004Np4p710p8P0p1004ep4p710p8P0p1005FR7p4p710p8P0P7p4p7210p8P0p1005cp4p710p8p100_Jp4p70R0g00;\R7p4p710R8p8P0P1p8P0P2p8P0p10079p4p710R9p8P0P4p8P0P3p4p710R3p8P0P6p8p1006?p4p710P5p8p100`:p4p70R0P8p8P0P1p8P0P2p8P0p100`hp4p7210p8P0P9p8P0P4p8P0P3p8P0P5p8P0P6p8p100aDp4p70P9p8p100bCp4p7210R0P1p8P0P2p8P0P9p8P0P4p8P0P3p8P0P6p8p1062Tp6051000R0P5p8P0p103VIp4p710p8P0p1063Vp4p710p8p100bop4p70R0P1p8P0P2p8P0P4p8P0P3p8P0P6p8p1006\p4p7210R6P9p8P6P5p8p1007Up4p7210P5p8p10082p4p73110P5p8p100cep4p710P5p8g00:Bj27Tg008Nj1;Tg0093j1JTg009Qj2WTg00:^j26Tg00JTj1ETg00=Lj20Tg00;;j2OTg00<6j1XTg00<Oj2<Tg00<lj21Tg00=ij2STg00>Pj25Tg00>lj29Tg00?Gj2QTg00?nj2RTg00@Tj2PTg00A:j1>Tg00AYj2?Tg00BBj1bTg00B`j2aTg00CAj3`Tg00Cjj3BTg00DSj2_Tg00E?j1^Tg00E_j3]Tg00F?j1\Tg00F_j2ITg00G=j4MTg00]4j1[Tg00G[j1ZTg00H9j1YTg00Hdj2ATg00IGj4FTg00J2j1oTg00K9j2:Tg00Ldj6nTg00MHj3GTg00Mkj3CTg00^3j3TTg00NNj2mTg00O0j2lTg00OJj2kTP7j3LTg00P6j3gTg00PUj4fTg00^Vj2DTg00\7j1eTg00QGj1dTg00RFj7hTg00K\j6cTg00L@j7iTg00Rjj8jTf0R7#;#;p=@g00VPR5/77p=2%E7#Ep==g00UMR6?L75p=Hf1R9=L67p=8P9g00SNR0g00SmR3P3g00TMR4P7g00TmFhp=4P9P0P3P3P4P7Ecp=Vf2R2P0P3P3P4P9P7Fip=Uf3R1P0P3P3P4P2P9P7Gjp=3P6P9g00Z3P7CFp=NP6P9g00YLP7CFp=K1797g00UkR8#;R:#;R;#@#@#@#@#@#JR<,W2%22%2<R=f4R>/6<#2[[%E8R?#=#=#=#=#=R@#JRA,02RB/W<%2B10>ARB/6<RC#2\=[101A/O<%H<R=#XRD1<<C11B<'0,8B[1SB<155<RBf5RC/0ARE/1<RF#215F<'9[1QE<15<5REf6RF/0ARG/1<RH,5<17H5'9[1RG<f7RH/0ARI/6<#H\=1PI<f8RI/0ARJ/1</8J\=16J<P6f9RJ/0A/1<P6f;/O<f<RK16K<,<<11K<'0'8\D1SK<f=RK/1<RD#215D<'9\B1QK<f>RD/1<RL,5<17L5'9\E1RD<f?RE/6<#H\=1PE<f@RE/1</8E\=16E<P6fARE/1<P6p-0RLg00VnRMg00WZRN#>#>RO#>RP#>RQ#>,?61?6Q1?6P%b8,a61?6O5`61?6N5B65B65B65B6g00X9'_%^M3]%\MP6P61I6>P21I6FCMP9P61I6CP1%[6CMCM%Z6%Y6RMPMP61A65RNg00XeRO1A6<RPCF,4MRQ%o3RR1VMIP6%;?,:6RSPOPPCF,4M5UMC3PRPMPMPMP0P3P3P41NPN,4MEnR3PR1:6;R;1:6:R09G6P=C6S'N,4MC3PRPMPMPQPR%E:,:6R:,KN,4M1VMJ5UMC3PRPMPMP3PR1:6?R?1A6A5C61:68R89G6P=C6:'N,4MC3PRPM1K;?,4MPRAG68PAG60P5T6AT6?;%;@#JR@,A65C6'K,4MC3C3C3C3C31mM4P7P2g00ZZRMg00[:R4'l1k72=LM4dAg659CfbDbGbHX26X36X46X56X66X76X0LW115F<,9H\Bg00[Z\=R=1<<1/0H,8C[%2Hf:'9\B1<<>/0I,8G\=17HF1<C<1<F<'D1DHI/0@'7[[[[[^26^36^46^56^66^76^0L^1LP715I<%29P9PIfCfBP2PJPFPHPKPDPEO=bCbNbLbBbAb@b?b>bMbKb=b<b;b:b9bEbF%e9%d2'D1D92/0@'7eW8XJ6XI6o"). Qed.

(* [comment removed for export] *)
#[using="nx0 HS XN XE XB"] Lemma maps_match_exact : forall E ms l,
  no_fog ms = true -> (maps_match E ms l <-> l = map (amap_den E) ms).
Proof.
  intros E ms. induction ms as [|m ms IH]; intros l Hnf; cbn [maps_match map].
  - tauto.
  - cbn [no_fog forallb] in Hnf. apply andb_prop in Hnf as [Hm Hr]. apply negb_true_iff in Hm. rewrite Hm.
    split.
    + intros (l' & -> & Hm'). f_equal. apply (proj1 (IH l' Hr)). exact Hm'.
    + intros ->. exists (map (amap_den E) ms). split; [reflexivity|]. apply (proj2 (IH _ Hr)). reflexivity.
Qed.

#[using="Type"] Lemma maps_match_In : forall E ms l m,
  maps_match E ms l -> In m ms -> is_fog m = false -> In (amap_den E m) l.
Proof.
  intros E ms. induction ms as [|m0 ms IH]; intros l m HM Hin Hf; [destruct Hin|].
  cbn [maps_match] in HM. destruct Hin as [<-|Hin].
  - rewrite Hf in HM. destruct HM as (l' & -> & _). left. reflexivity.
  - destruct (is_fog m0).
    + destruct HM as [HM|(iv & l' & -> & _ & HM)]; [exact (IH _ _ HM Hin Hf) | right; exact (IH _ _ HM Hin Hf)].
    + destruct HM as (l' & -> & HM). right. exact (IH _ _ HM Hin Hf).
Qed.

#[using="Type"] Lemma in_ivs_maps_match : forall E ms l m z,
  maps_match E ms l -> In m ms -> is_fog m = false ->
  bv_unsigned (edenot E (am_base m)) <= z < bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) ->
  in_ivs z l = true.
Proof.
  intros E ms l m z HM Hin Hf Hz. apply (proj2 (in_ivs_true z _)). exists (amap_den E m).
  split; [exact (maps_match_In E ms l m HM Hin Hf) | exact Hz].
Qed.

#[using="Type"] Lemma maps_match_cons : forall E ms l b n k,
  is_tok_kind k = false -> maps_match E ms l ->
  maps_match E (AM b n k :: ms) ((edenot E b, edenot E n) :: l).
Proof.
  intros E ms l b n k Hk HM. cbn [maps_match]. unfold is_fog. cbn [am_kind]. rewrite Hk. exists l. split; [reflexivity | exact HM].
Qed.

#[using="Type"] Lemma maps_match_length : forall E ms l, maps_match E ms l -> (length l <= length ms)%nat.
Proof.
  intros E ms. induction ms as [|m ms IH]; intros l HM; cbn [maps_match] in HM.
  - subst l. cbn. lia.
  - cbn [length]. destruct (is_fog m).
    + destruct HM as [HM|(iv & l' & -> & _ & HM)]; [pose proof (IH _ HM); lia | cbn; pose proof (IH _ HM); lia].
    + destruct HM as (l' & -> & HM). cbn. pose proof (IH _ HM). lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma maps_match_elem : forall E ms l iv,
  maps_match E ms l -> In iv l ->
  exists m, In m ms /\ ((is_fog m = false /\ iv = amap_den E m) \/ (is_fog m = true /\ bv_unsigned (snd iv) <= uE E (am_len m))).
Proof.
  intros E ms. induction ms as [|m ms IH]; intros l iv HM Hin; cbn [maps_match] in HM.
  - subst l. destruct Hin.
  - destruct (is_fog m) eqn:Hf.
    + destruct HM as [HM|(iv0 & l' & -> & Hsz & HM)].
      * destruct (IH _ _ HM Hin) as (m' & Hm' & H'). exists m'. split; [right; exact Hm' | exact H'].
      * destruct Hin as [<-|Hin].
        -- exists m. split; [left; reflexivity|]. right. split; [exact Hf | exact Hsz].
        -- destruct (IH _ _ HM Hin) as (m' & Hm' & H'). exists m'. split; [right; exact Hm' | exact H'].
    + destruct HM as (l' & -> & HM). destruct Hin as [<-|Hin].
      * exists m. split; [left; reflexivity|]. left. split; [exact Hf | reflexivity].
      * destruct (IH _ _ HM Hin) as (m' & Hm' & H'). exists m'. split; [right; exact Hm' | exact H'].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma maps_match_rekind : forall E ms l (f : amap -> amap),
  (forall m, am_base (f m) = am_base m /\ am_len (f m) = am_len m /\ is_fog (f m) = is_fog m) ->
  maps_match E ms l -> maps_match E (map f ms) l.
Proof.
  intros E ms. induction ms as [|m ms IH]; intros l f Hf HM; cbn [maps_match map] in *; [exact HM|].
  destruct (Hf m) as (Hb & Hn & Hk). rewrite Hk. unfold uE, amap_den in *. rewrite Hb, Hn.
  destruct (is_fog m).
  - destruct HM as [HM|(iv & l' & -> & Hsz & HM)]; [left; exact (IH _ f Hf HM) | right].
    exists iv, l'. split; [reflexivity|]. split; [exact Hsz | exact (IH _ f Hf HM)].
  - destruct HM as (l' & -> & HM). exists l'. split; [reflexivity | exact (IH _ f Hf HM)].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma filter_all_true : forall {T} (f : T -> bool) l, (forall x, In x l -> f x = true) -> List.filter f l = l.
Proof.
  intros T f l H. induction l as [|x l IH]; [reflexivity|]. cbn. rewrite (H x (or_introl eq_refl)).
  rewrite IH by (intros y Hy; apply H; right; exact Hy). reflexivity.
Qed.

#[using="Type"] Lemma aluop_eqb_refl' : forall o, aluop_eqb o o = true.
Proof. intros []; reflexivity. Qed.
#[using="Type"] Lemma mulop_eqb_refl' : forall o, mulop_eqb o o = true.
Proof. intros []; reflexivity. Qed.
#[using="Type"] Lemma expr_eqb_refl' : forall e, expr_eqb e e = true.
Proof.
  induction e; cbn; rewrite ?aluop_eqb_refl', ?mulop_eqb_refl', ?IHe1, ?IHe2, ?IHe, ?Z.eqb_refl, ?Nat.eqb_refl, ?Bool.eqb_reflx; reflexivity.
Qed.
#[using="Type"] Lemma amap_eqb_refl' : forall m, amap_eqb m m = true.
Proof. intros [b l k]. unfold amap_eqb. cbn. rewrite !expr_eqb_refl'. destruct k; reflexivity. Qed.

#[using="Type"] Lemma map_remove_notin' : forall l (a : word),
  (forall b sz, In (b, sz) l -> b <> a) -> map_remove l a = l.
Proof.
  induction l as [|[b sz] l IH]; intros a H; [reflexivity|].
  unfold map_remove in *. cbn [List.filter fst]. rewrite (bv_eqb_neq b a) by (apply (H b sz); left; reflexivity). cbn [negb].
  f_equal. apply IH. intros b' s' Hin. apply (H b' s'). right. exact Hin.
Qed.

#[using="Type"] Lemma maps_match_remove : forall E ms l m,
  maps_match E ms l -> In m ms -> is_fog m = false ->
  List.NoDup l ->
  (forall iv, In iv l -> fst iv = edenot E (am_base m) -> iv = amap_den E m) ->
  maps_match E (List.filter (fun m' => negb (amap_eqb m' m)) ms) (map_remove l (edenot E (am_base m))).
Proof.
  intros E ms. induction ms as [|m0 ms IH]; intros l m HM Hin Hf Hnd Huniq; [destruct Hin|].
  cbn [maps_match] in HM. cbn [List.filter].
  destruct (amap_eqb m0 m) eqn:Heq.
  - (* [comment removed for export] *)
    apply amap_eqb_eq in Heq. subst m0.
    rewrite Hf in HM. destruct HM as (l' & -> & HM). cbn [negb].
    unfold map_remove. cbn [List.filter amap_den fst]. rewrite bv_eqb_refl. cbn [negb].
    inversion Hnd as [|x l0 Hnotin Hnd']; subst.
    assert (Hnotin' : ~ In m ms).
    { intros Hm. apply Hnotin. exact (maps_match_In E ms l' m HM Hm Hf). }
    rewrite (filter_all_true (fun m' => negb (amap_eqb m' m)) ms).
    2:{ intros x Hx. destruct (amap_eqb x m) eqn:Ex; [|reflexivity]. apply amap_eqb_eq in Ex. subst x. exfalso. exact (Hnotin' Hx). }
    fold (map_remove l' (edenot E (am_base m))). rewrite map_remove_notin'; [exact HM|].
    intros b sz Hbs Hb. apply Hnotin. rewrite <- (Huniq (b, sz) (or_intror Hbs) Hb). exact Hbs.
  - (* [comment removed for export] *)
    destruct Hin as [->|Hin]; [rewrite amap_eqb_refl' in Heq; discriminate|].
    cbn [negb maps_match].
    destruct (is_fog m0) eqn:Hf0.
    + destruct HM as [HM|(iv & l' & -> & Hsz & HM)].
      * left. exact (IH _ _ HM Hin Hf Hnd Huniq).
      * inversion Hnd as [|x l0 Hnotin Hnd']; subst.
        assert (Hne : bv_eqb (fst iv) (edenot E (am_base m)) = false).
        { apply bv_eqb_neq. intros Hb. apply Hnotin. rewrite (Huniq iv (or_introl eq_refl) Hb).
          exact (maps_match_In E ms l' m HM Hin Hf). }
        unfold map_remove. cbn [List.filter]. rewrite Hne. cbn [negb]. fold (map_remove l' (edenot E (am_base m))).
        right. exists iv, (map_remove l' (edenot E (am_base m))). split; [reflexivity|]. split; [exact Hsz|].
        apply (IH _ _ HM Hin Hf Hnd'). intros x Hx. apply Huniq. right. exact Hx.
    + destruct HM as (l' & -> & HM).
      inversion Hnd as [|x l0 Hnotin Hnd']; subst.
      assert (Hne : bv_eqb (fst (amap_den E m0)) (edenot E (am_base m)) = false).
      { apply bv_eqb_neq. intros Hb. apply Hnotin. rewrite (Huniq _ (or_introl eq_refl) Hb).
        exact (maps_match_In E ms l' m HM Hin Hf). }
      unfold map_remove. cbn [List.filter]. rewrite Hne. cbn [negb]. fold (map_remove l' (edenot E (am_base m))).
      exists (map_remove l' (edenot E (am_base m))). split; [reflexivity|].
      apply (IH _ _ HM Hin Hf Hnd'). intros x Hx. apply Huniq. right. exact Hx.
Qed.

#[using="Type"] Lemma in_ivs_map_den : forall E ms m z,
  In m ms ->
  bv_unsigned (edenot E (am_base m)) <= z < bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) ->
  in_ivs z (map (amap_den E) ms) = true.
Proof.
  intros E ms m z Hin Hz. apply (proj2 (in_ivs_true z _)). exists (amap_den E m). split; [apply in_map; exact Hin | exact Hz].
Qed.

#[using="Type"] Lemma existsb_false_forall : forall {T} (f : T -> bool) l, (forall x, In x l -> f x = false) -> existsb f l = false.
Proof.
  intros T f l H. induction l as [|x l IH]; [reflexivity|]. cbn [existsb].
  rewrite (H x (or_introl eq_refl)). cbn [orb]. apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

(* [comment removed for export] *)
#[using="HS XN XE XB SHADOW_ok argH_high KC"] Lemma vis_add_sound : forall E cs b n k cs2 R FULL model,
  vis_add A LIMIT cs b n k = Some cs2 ->
  cs_ok E cs R FULL model ->
  know_ok SEGS E (Mr E cs2 model FULL) k ->
  cs_ok E cs2 R FULL model.
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
ltac2:(KReplay.run1 (kr_t_AsanPlanSound ()) ["FPX_3"; "Sound"] "p'0p'1p'2h01pi001ph14__x1h21Hh34__x2h44__x3h54__x4h66__sat6h76__sat7h87__arithh94__x5h:1zi011zh;4__ffh<8__varmaph=5__with>4__p1h?4__x6h@4__x7hA6__sat8hB6__sat9hC1bi021bhD4__p2hE4__x8hF6heq_S0hG1xi031xhH2HchI1mhJ4__p3hK4__x9hL2HvhM1ai041ahN5__x10hO5__x11hP7__sat10hQ7__sat11hR7__sat12hS7__sat13hT1DhU3HpphV5__x12hW1ni051nhX2HahY2A2hZ2H0h[6__sat4h\6__sat5h]2b1h^2b2h_2H1h`3H10ha3H11hb3H12hc2H2hd2H3he2H4hf2H5hg2H6hh2H7hi2H8hj2H9hk3Hsshl1ei061ehm1qhn2q0ho1rhp2r0hq3H13hr3H14hs3H15ht3H16hu3H17hv4Hdw0hw3Hpshx3Hshhy4cstrhz2q1h{2r1h|1yh}3H18h~3H19i073H20i083H21i093H22i0:3H23i0;3H24i0<2Hfi0=5Hkindi0>2q2i0?2r2i0@2A1i0A3H25i0B3H26i0C3H27i0D3H28i0E3H29i0F3Hdwi0G4Hnhii0H2Hpi0I3Hx0i0J2I2i0K4__p4i0L7__sat14i0M5__x13i0N1ii0O1oi0P2q3i0Q2r3i0R3H30i0S3H31i0T3H32i0U3H33i0V3HKki0W6Haparti0X4Hapgi0Y2Hii0Z4Hinsi0[6Hspliti0\1Pi0]2S0i0^2a0i0_3cs2i0`1Ai0a3Fp1i0b3Fp2i0c3Fp3i0d4Hap2i0e7Hbudgeti0f3Hmbi0g3Hnfi0h3Hpfi0i2Hxi0j2I1i0k2Rbi0l2U'i0m2U2i0n2Upi0o1Yi0p5__x14i0q2b0i0r1di0s2ivi0t1li0u2l1i0v2l2i0w2p0i0x2pbi0y2pki0z3sb'i0{3sk'i0|2sni0}2B1i0~2B2i102B3i112B4i122B5i134BYTEi141Ei153ES0i163ES1i172F1i182F2i192F3i1:2F4i1;4FULLi1<3Fb1i1=3Fb2i1>3Fb3i1?2G1i1@2G2i1A2G3i1B2HAi1C2HCi1D2HKi1E4HKshi1F3HS0i1G4Halbi1H4Halni1I4Hap1i1J5Harghi1K5Hcosti1L2Hdi1M3Hfli1N5Hflati1O3Hghi1P2Hhi1Q5Hhid1i1R3Hlzi1S3Hm1i1T4Hmini1U3Hmvi1V3Hnai1W5Hnhi'i1X4Holdi1Y4Hsh2i1Z3Hvbi1[5Hvis2i1\3Hvni1]2Hzi1^1Ri1_3Rmbi1`2Rni1a3Rsni1b2SOi1c3SUBi1d2Uai1e2Ubi1f3Usni1g2Z1i1h2Z2i1i2Z3i1j2Z4i1k3Zini1l2bbi1m2bki1n:co_abytes0i1o:co_bounds0i1p7co_brk0i1q9co_eager0i1r7co_fds0i1s6co_fs0i1t8co_halt0i1u9co_holes0i1v9co_kinds0i1w8co_know0i1x9co_lazyb0i1y9co_limit0i1z7co_log0i1{8co_maps0i1|8co_minv0i1}9co_nasub0i1~8co_none0i208co_regs0i217co_res0i228co_sbrk0i238co_seps0i248co_sinv0i259co_split0i267co_tid0i279co_totsz0i286co_wf0i298co_zero0i2:2csi2;1ki2<5modeli2=3nhii2>2sbi2?2ski2@1wi2A2w'i2B9co_abytesi2C9co_boundsi2D6co_brki2E8co_eageri2F6co_fdsi2G5co_fsi2H7co_halti2I8co_holesi2J8co_kindsi2K7co_knowi2L8co_lazybi2M8co_limiti2N6co_logi2O7co_mapsi2P7co_minvi2Q8co_nasubi2R7co_nonei2S7co_regsi2T6co_resi2U7co_sbrki2V7co_sepsi2W7co_sinvi2X8co_spliti2Y6co_tidi2Z8co_totszi2[5co_wfi2\7co_zeroi2]3segp%0p%1p%2p%3p%4p%5p%6p%7p%8p&0p&1p&2p&3p&4p;1p;2p;6p;5p;4p;7p;3p;;p;8p;>p;<p;9p;:p;Pp;Bp-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0g0038R5p4p710R6p9P0p1003Vp4p710R7p9P0g00_3R8p4p710R9p8P0g004eR:p4p710p8P0g005FR;p4p710p8P0P;p4p7210p8P0g06dOR0p4p710R<p8p100_Jp4p70R=g00;\R>p4p710R?p8P=P1p8P=P2p8P=g0079R@p4p710RAp8P=P4p8P=P3p4p710R3p8P=P7p8p1006?p4p710P6p8g00`:S00p4p70R=P?p8P=P1p8P=P2p8P=p100`hp4p7210p8P=PAp8P=P4p8P=P3p8P=P6p8P=P7p8p100aDp4p70PAp8g00bCR=p4p7210R?P1p8P?P2p8P?PAp8P?P4p8P?P3p8P?P7p8p1062Tp6051000R?P6p8P?p103VIp4p710RBp8P?p1063Vp4p710p8p106kQp6051000R?P9p8P?P6p8P?PBp8P?P<p8g07<2R?p6051000RCP9p8PCPBp8PCP<p8p100bop4p70R<P1p8P<P2p8P<P4p8P<P3p8P<P7p8p1006\p4p7210R7PAp8P7P6p8p1007Up4p7210P6p8p10082p4p73110P6p8p100cep4p710P6p8g00F?k11uTg008Nj1KTg00JTj1{Tg00dlk12ZTg00eJk11tTP=k24[Tg01SnS01k12ITg07==k63OTg01TPS02k508Tg07>=k640Tg07?Ak63vTP@k61Hm:4dk74\Tg03JOk12QTg00emR@k22ETg00O0k212Tg02X7j13Tg07@Dk41\Tg06_:k20}Tg0093k10pTg06\6j4>Tg05R^j1UTg07AFj2JTg04L8j7:Tg01ERj1|TP0k309Tg01Plj2=Tg01FPj1QTg02lFj1PTg02nCk102Tg07BKk10JTg02^\j1HTg02fVj1iTg02`\j1ZTg00=LR0j21Tg02jMj1fTg02Y2j1jTg02Zlj1gTg05WWl;yTg00J2k128TP>j35Tg030Ck22:Tg05XUk62GTg01QJk30bTg01POj2STg00:BR>j24Tg01Qmk24JTg03M^k64HTg02S>j4lk51:Tg06bFk84FTg07CLk82oTg018]k22CTg03iTj2MTg01>6k23@Tg01>^k33?Tg00A:R=j1\Tg00AYk23=Tg00E?k12ATg00]4k141Tg00G[k13~Tg00H9k13{Tg00Hdk23;Tg00K9k239Tg01LWk338Tg00NNk23pTg00OJk23oTg00P6k34yTg00PUk44xTg00>PR6j26Tg00>lR7j2CTg07DOk630Tg07EPm>4qTg01UNk41gTg015ok22@Tg01C[k21NTg01GPk30gTg01=4j2ETg017fk11|Tg00iHj2;k14=Tg07FSk33_Tg00\7k10zTg00QGk10|Tg00^Vj2sTg01AFk14`Tg009Qj2Yk34wTg00:^j28Tg00;;k20UTg00<6k11rTg00<Ok20eTg00=ij2_Tg00<lj29Tg00?Gj2aTg00?nj2dTg00@Tj2cTg00BBk13UTg00B`k23TTg01BIk23RTg00kjj2TTg01:6k22uTg019:k22FTg01Gmk41CTg00E_k30DTg02mFk10fTg07G]k625Tg02cWk12_Tg00jjk10CTg00lck106Tg07Hek54RTP8k307Tg01X@k10FTg020Vk14PTg06ejk13KTg05YIk24Ok13VTg01VHj2uTg07ICk14NTg05fBk34MTg07Ibm<4LTg03gQk20NTg07Jik63HTg06iIk74KTg02dWk20;Tg01Z8k14ITP:k30=Tg00gKk33FTg07Kgk64GTg00hmk62pm93|k34uTg05A^k13ETg04JVk14ETg07Lgj3XTg045Hk22nTg01L1k20wTg05C@k321Tg01M:k21DTg07Mhk23BTg07Nim93ATP5k61Vk73eTg06cIk54@Tg05B?k34?Tg057nk44>Tg07Onk24<Tg01fik20ETg01KEk249Tg07Pok347Tg05>_k146Tg05?ak145Tg07QRm942Tg01`lk20hTg01_?j1zTg01N7k11eTg01Y@k10`Tg01aik11{Tg07RZk63}Tg01WFk42XTg01X^k13zTg01^Ak22WTg01j`k31zTg01c?j2eTg005ck31KTg00mbS03k218Tg06>Ak23yTg01c\k23xTg00jOk426Tg01gZk33wTg01f5k32UTg01e9k32TTg01d<k32^Tg06AEk137Tg01Nok22iTg01`6k11@Tg01]Bk13uTg01oTk23tTg0206k23sTg01hCk32STg07SYk23rTg01Vek23qTg07T9k336Tg03fQj2pTg04Mem<2gTP?k432Tg05@bk34tTg02oDk331Tg07T\m<4sTg03k1k32~Tg03ETk32mk43gTg03nXk22tTg035GR?j1tTg04E^k41xTg046Lk12PTg046jk44pTg03m1k41hTg03dFk12fTg047Mk44mTg0488k62|Tg04oJk34lTg01nPk33jTg048ak14kTg049ck14jTg04:bk14hTg04;`k14gTg04<>k13iTg04<\k23hTg0148k22lTg04>dk34fTg04?ak64eTg04dok23CTg05A=k63fTg07UZk52]Tg02Q<k33dTg02W:k12BTg02R=k13cTg02A\k13GTg02Yok33bTg02@ik13aTg02BSk13`Tg02[mk122Tg02\gk14bTg02]ek12rTg02_[k33^Tg00fMk33LTg02aZk13JTg02bWk13]Tg02eVk13\Tg02gVk13ITg02hQk33[Tg016lk23MTg02iXk12{Tg02kKk13ZTg02E9k12aTg02O>k22yTg02P:k12cTg05:6k44aTg02U9k42zTg07V_k24_Tg07Wak54^Tg03:2mP4]Tg07X`k22MTP;k33YTg00j2k32eTg03_dk13XTg05VYk43WTg00Cjk311Tg00DSk22LTg00F_k24ZTg00G=k40tTg00IGk40vTg00RFk70_Tg00L@k71}Tg00Rjk80VTg00Mkk32dTg00CAk34YTg01C2k34XTg00K\k64iTg00Ldk64WTg00MHk34nTg00^3k34oTg07Ybk74VTg07Zek23kTg04F^m<3lTg04GCmB4UTg04E9m<3nTf2R;f1R5g01JGS04f0R:+2:35p>0yf6R8f5RAf4R<f3R3P;P5ClP:H2zp>00&2Q5=5;:p>0Sf7R422M8A'S22M3;,S<'=/=5/=:p>0Zg01IER2@3Y2:p>03B2e22:p=R1=;5/=:p=x113;/15/S:p>0d1J<3,=A/=;/=5/=:p>0ng03GPS05PAP<P3P;P5I2]<0g:p>0i&3X3&2B;$2cP5P:H3Wp>1vP2P2P;P5H1C>0D3:p>1wQ0402::p>0[P2g00UMR1P5P:H1Cp>2<P;P2P5P:H1Cp>2b22M5:,S;p=W22M3;,S</=5/=:p>2J1S5:,=;p>3S%|::09;5p>0~%Q::09;5p>1p&3X3&2B;$2cP5%U:H3Wp>0IP2P2P;P5H1C%|:60D3p>0M&025&0J:'1p>0@g00ZZRCg00[:S0675:p=7Q0695C5Q0695C:'Cp>0a1=3;/=5/=:Q0655Cp>1ZQ05PA%3<P3P;P5I2]<0g:p>1A22M;5,S3/=:p>241=<3/=;/=5/=:p>3NB09;5:Q0655Cp>0]PAP<P3P;C>/=5/=:p>1=P<P3P;P5C>/=:p>1X1=5:Q0655Cp>0k11;5/1:p>2s1E5:,;;p=01M5:,p;p=<14;5g00VPRB/6:'Cp>1E14B5/C:p>1914B:p=21p;5/1:p>2011;5/4:p=?16B:p=]23=1:p>0>B1115:p=qg00VnR9g00X9RD-2L5<0D:p>1P24Z1:p>0HP1P1P<P3P;H0tP5P:H0tp=~2391:p=OP1P5g00XeREP:H0vp>0L23;1:p>1iP;g00SNRFg00SmRGPGg00TMRHP1P5g00YLRIP:H0vg00TmRJK0_p=LP;PFPGPGPHP1P5PEP:H0vPJK0_p=[P;PFPGPGPHP5P:K1}p>1dP3PFPGPGPHP;P5P:L0Vp>2?P8PFPGPGPHPAPFPGPGPHP1B2d1<3PIP;H0vPJK0_P5P:L0Vp>0sP<PFPGPGPHP3PFPGPGPHP;PJK0_P5P:L0Vp>1cA515:p=@P2P2P5P:H1Cp>2=14B;165:'Cp=D1E5:,;;,13p>0?P1P;P5P:H0tp=hB2d15:p=F%{:#{p>1`1s;5/4:p>1^185:,1;p>01185:,4Bp>0XA51:Bp>2N195:,1;9513p>3m16;514:B'Cp=b19;5=51:p=`1E;5,;3/1:p=v18;5-0e3/1:951<p>4T185:=51Bp=n11;5/9:p>2K1E5:,;;,4Bp>1]1;;5/6:p>0GB4Y15:p>10B4X15:p>0qB1115::111;:1113:111<p>1qP1P<P3P1P;P5P:H0tH0tp>0RP1P1P1P8PAP<H0tP3P;H0tP5P:H0tp>04P5PFPGPGPHP:J4ip>0QP3PFPGPGPHP;P5PFPGPGPHP:PJK0_K1}p>1FP;PFPGPGPHP1P5g00Z3REP:H0vPJK0_p>2`P5PFPGPGPHP:J4Wp>3QB4n15:p>1oP3PFPGPGPHP1P;PEB2d15:H0vPJK0_p>0<P8PFPGPGPHPAP<P3PFPGPGPHP;P5P:L0VL0Vp>0:P8PFPGPGPHPAPFPGPGPHP<P3P;L0VP5P:L0Vp=N165:,C;p=r115:951;p=k183;-0e<195:'1951Ap=w1;;5/9:p>0cB111;5:111302LD>0D9:p>0WP<PFPGPGPHP3PFPGPGPHP1P;PIP5H0vPJK0_P:K1}p>0KB4o15:p>29P1P1P8PAP<H0tP3P1P;P5P:H0tH0tp>2H%K:#Kp>2x%K:#K#K#Kp>2wPAPFPGPGPHP<PFPGPGPHP1P3PIP;H0vPJK0_P5P:L0Vp=VPAPFPGPGPHP<PFPGPGPHP3P;K1}P5P:L0Vp=o115:,4;p>3P11:Bp>271T5:,1;p>2vP3P2P2P1P;P5H1CP:H1Cp>1BQ0522n<3Q0522t;5<0D:40Dp>0P&3K:$0Fp>14g03=;S07&3V5<1K:p>4SPAP<P3P;P5PBP:K4Vp>1?Q07&2_5$3V<1K:p>1>Q0695C:,C5p>4Qg014WS0895C:p=B20N5:,1;p>1l20N;5,13/4:p>0{14;5/C:p=}%z:$1@p>1<B2e;5:,;3p>0mB3Y;5:,;3p>0l195:=51Bp>23115:g01k_S09'4p>1;A515B/C:p>1j1C5:,C;p>0x&0C:,E5,;;p=AP1P<P3P;P5P:J1Hp>0^&0C:,E5p>0A%3;?X5:p>0B23k5:$2Qp>4DAX3;503k:p>1WQ0522t;5<0D:p>4CP<P3P;Q05@0D5:H2zp>4B1;;5/1:p>3DP8PAP<P3P;P5P:F:,=4p>4A2121:p=IP1P<P3P;P5P:J1Vp=mAX;5:,E3p>0u115:-0w;p>0\20w5:,;;p>0o113;/95=51:p>161;;5/8:p>4;1E;5,;3/8:p>1U145:,C;p>2\22L;D22L5D>0D9:60D9p>2[%K:#K#K#K#K#K#K#Kp>1T&06:,E5,;;p=G195:,4Bp>0O1;;500U:p>0j&06:,E5p>1S1;5:,4Bp>1~B1115::111;p>1RB1115:02LDp>4:B0D95:p>48P1P5PIP:H0vp>3>PAPFPGPGPHP<PFPGPGPHP1P3PEP;H0vPJK0_P5P:L0Vp>1QAX;5:-0N3p>3<%3;?X5:-0N3p>051E;5,;3/8:,4Bp>1[1;5:,1;p>44Q09,6:p>1f14<3115:,6;'Cp=^P3PFPGPGPHP;PFPGPGPHP5PJK0_P:K1}p>43&1{:-0h5p>1722i5:Q0655Cp>0rQ0895C5/C:p>1Og00oaRI@0=5:p>1a%z:$1{p>2k20h5:Q0855Cp>2Y1u5:Q0855Cp>1b&0`:-2i5p>3:1u5:Q0655Cp>0Y1S;5/=:p>1y115:,6;p>2V11;5/8:p>2j1S<3115:,e;'=p>2D22u5:,e;p>2qQ08/u:p>1kPCQ06P3P;P5P:J1Vp>1mPCQ08P3P;P5P:J1Vp>1Y1S;5/=:Q0855Cp>151=5:Q0855Cp>2h1T5:,1;,e3p>0T22FA</S322u5:,e;'=Q0855Cp>1_1S3;/=5Q0855C/C:p>1LB2e22:,E5,;;p>1314;5018:p>1G11;5/S:p>2>115:,e;,=3Q0855Cp>35B2e22:,E5,;;,13p>1I115:,e;p>2RP1P;PEB2d15:H0vp>34P<PFPGPGPHP3P;P5PFPGPGPHP:PJK0_L0Vp>4vPAPFPGPGPHP<P3P;PFPGPGPHP5P:K1}L0Vp>3314B311;5/4:'Cp>1J16;5/C:p>1sQ05@0D5:p>4rg03D=S0:Q0:P1P1P=P?P?P3g04HKP;P5P:N<3lp>2;Q0:P1P1P1P?P?PAP<P3P;P5P:N<3lp>1nP1P1P1P1P1P1P0P:P5P;P0P3P<PAP8P4f8R0f9R?NB4Up>1MP1P1P>P4P>P8PAP<P3P;P5P:N<3np>2OP1P1P6P4P6P8PAP<P3P;P5P:N<3np>2}&2B:$2cp>4cg00n`Q04Q05$1uS0;Q04g00UkS0<#KR6#{S0=$2Z%K6S0>#KS0?#KS0@#KS0A#KS0B$2ZR>$1tR=+4[Q0?$2ZS0C$1tS0D$2IRF\=g01l\Q04$2IRJp,1AREp,5LIMITS0EP4P8PAP<J3O<0y3P?P0P3P;P5I08p,4SEGSRDf:RKPKPAP;P3P8K00PJPEQ0EPKP?P0P4J3OB0yJ:4Z0OJP;PEQ0EPKP?P0P4J40RLPEQ0EPKP?P0P4J3vJ1HB0yJL8&2QK22E21RL212L:S0Ff;RM>0SL:P@P2P1f=RN>0SL:P@P2P1PJP5P@PLP2PJPEfARO#3f@RPf?RQH1\P@P2P1PJP5Q01P1PJfERR#3fCS0G+0}PCPJQ0<#{S0H$0pRSfFRT#3RUPRPSPUfDRVPUP8PAPVC>%UTRW/JRL0ZPWPV22E22RXP@P2P1PC&03:S0I$2QRYfIS0J#3RZP5P:%R;R[C>R\PZP?P0fGR]P5P:P[F:PZPAP<P8P5P:P[F:RZ3xn200110300012010x10yX0X%|TR^409P@P2P1PCPY1=\Zn200110300012010x10yX0X%QTRZ609X%PTR\&02TR_&0J:R`Q0EH0dJ0nPTPTPEPU%HTRaPRPVQ0GJ0iPWH1vPa%iT%ZTP\PXPRPVP^H1wPZ11_`%fT%jT%gTM;y$0[Q04$28S0Kn0100000020000Q0Kn10110300021012=00n200110000012112>12?n200110300012110010|n200110300012111l11m>0yJMPOf<R_PMPKP?I08]L_0[P522<5:S0L:0SLPP@PLP2PJPEfBS0M#3POPPH1\P@P2P1PJP5Q01P1PJ20}UVPCPJPS%3]RZPTPSPZPRPZP4P8PRC>%U]R^/JTL0ZP^PRP@P2P1PCPYfJR\#3RaP5P:P[C>RWPaPKP?fHRbP5P:P[F:PaPAP<P8P5P:P[F:Rc3xn200110300012010x10yX0X%|]Rd609XP@P2P1PCPY1=Wcn200110300012010x10yX0X%Q]Rc609X%P]RW&02]ReP`Q0EH0dJ0nP]P]PEPZ%H]RZPTPRPVJ0iP^H1vPZ%i]%Z]PWPXPTPRPdH1wPc11e`%f]%j]%g]M;y$0[Q0Kn0100000020000Q0Kn10110300021012=00n200110000012112>12?n200110300012110010|f>Re60yJPEQ0G#3Q0MPOH1\22EL2Rc212c:PE%3VQ0GQ0MH1\=5c:P@PLP2PEPUPRPVH1\=5c:P@PLP2PJP5P@P2P1PJP5Q01P1PJfKRU#3Q0J+0}PCPJPSfLRd#3RWPUPSPWP\PWP_PMP\C>%UdRZ/JUL0ZPZP\P@P2P1PCPYfOR^#3RfP5P:P[C>RgPfPQPefMRhP5P:P[F:PfPAP<P8P5P:P[F:Ri3xn200110300012010x10yX0X%|dRj609XP@P2P1PCPY1=gin200110300012010x10yX0X%QdRi609X%PdRg&02dRkP`Q0EH0dJ0nPdPdPEPW%HdRWPUP\Q0JJ0iPZH1vPW%id%ZdPgPXPUP\PjH1wPi11k`%fd%jd%gdM;y$0[Q0Kn0100000020000Q0Kn10110300021012=00n200110000012112>12?n200110300012110010|Q0G60yJQ0JPVQ0GQ0MPOI08]L]xP5P@P2P1PEPaQ0JPbH1\B2bL5:55cP@P2P1PJP;Q01P1PJ%3hRa00}UPCPJPSfNRk#3RiPhPSPiPdPiPePNPdC>%UkRj/JhL0ZPjPdP@P2P1PCPYfQS0N#3S0OP5P:P[C>RgQ0OPOPPP^P5P:P[F:Q0OPAP<P4P5P:P[F:RW3xn200110300012010x10yX0X%|kRZ609XP@P2P1PCPY1=gWn200110300012010x10yX0X%QkRW609X%PkRg&02kRlP`Q0EH0dJ0nPkPkPEPi%HkRmPhPdPUJ0iPjH1vPm%ik%ZkPgPXPhPdPZH1wPW11l`%fk%jk%gkM;y$0[Q0Kn0100000020000Q0Kn10110300021012=00n200110000012112>12?>0yJ]PhPbP]PTPRI08]L]x^l2P:PEPaPdPUH1\22<;5S0P>2bL:55cQ01P1PJ20}idPCPJPSPfPkPSPfPhPfPQPePhC>%U^Ri/JkL0ZPiPhP@P2P1PCPYfRS0Q#3RaP5P:P[C>RlPaQ0MPOfPS0RP5P:P[F:PaP4P8PAP5P:P[F:RW3xn200110300012010x10yX0X%|^RZ609XP@P2P1PCPY1=lWn200110300012010x10yX0X%Q^RW609X%P^Rl&02^RgP`Q0EH0dJ0nP^P^PEPf%H^RmPkPhPdJ0iPiH1vPm%i^%Z^PlPXPkPhPZH1wPW11g`%f^%j^%g^M;y$0[Q0Kn0100000020000Q0Kn10110300021012=00>0yJ\20}fh&2I1S0SQ0S012:Q0SQ0R#300}k;5:Q01P1Q0SQ0R-0}a;5:Q01P1PJP5PCPJPSfTRa#3RffSS0TQ0Q9WSfPfPVQ0GQ0QC>I2J%UaRgQ0TQ0Q,JgP@P2P1PCPYfWRW#3RZP5P:P[C>RlPZP]PTfUS0UP5P:P[F:PZP_PMPKP5P:P[F:Rm3xn200110300012010x10yX0X%|aRi609XP@P2P1PCPY1=lmn200110300012010x10yX0X%QaRm609XJ0nRl%PaRj&02aRn'1Ro/1`Q0E43SPaPaPEPf%HaRfQ0TQ0QQ0NJ0iPgH1vRgPf%iaRp%ZaRqPjPXQ0TQ0QPiH1wRiPm11n`%faR`%jaRr%gaRsM;y$0[Q0Kn0100000020000Q0Kn10110300021012=00&0[^S0V55JQ0UQ0RP^PkPhI08S0W]L_0GP5Q0SQ0T#3Q0N+0}22:1:35PCPJ&0J5Rt,1oQ0E63SlPgPfPpPqPjPiPm11ntP`PrPsM;y$0[Q0Kn0100000020000Q0R60yJPSQ0U#3RsPaPSPsQ0TPsPRPVQ0TC>Q0U#URs/JaL0ZPsQ0TP@P2P1PCPYfXRs#3RrP5P:P[C>R`PrPbP]fVRtP5P:P[F:PrPNP_PMP5P:P[F:Rn3xn200110300012010x10yX0XQ0U60~XP@P2P1PCPY1=`nn200110300012010x10yX0XQ0U61pXQ0U#PQ0U$02&0J;Q0EH0dJ0nPC212C:S0XPS%3tRnQ0UPSPnPaPnPTPRPaC>%UtRnQ0U'JL0ZPnPaP@P2P1PCPYfYRn#3R`P5P:P[C>RmP`Q0JPbPWP5P:P[F:P`PePNP_P5P:P[F:Ri3xn200110300012010x10yX0X>0~XtP@P2P1PCPY1=min200110300012010x10yX0X>1pXt%Pt&02t&0J3Q0EH0dJ0n=5C:PCPSPrPWPSPrPtPrPbP]PtC>%UsRi/JWL0ZPiPtP@P2P1PCPYf[Rm#3RjP5P:P[C>RqPjPUP\PnP5P:P[F:PjPPPQPeP5P:P[F:Rp3xn200110300012010x10yX0X%|sRf609XP@P2P1PCPY1=qpn200110300012010x10yX0X%QsRp609X%PsRq&02sRg&0JARlQ0EH0dJ0n=5C:PCPJP5PnPnPEP`%HnR`PsPWPtJ0iPnH0IP`%in%Zn%PnPXPsPWPnH0M%Qn20@n8%fn%jn%gnM;yR`$0[RoQ0Kn0100000020000Q0U$0[S0Y55JPmPtQ0UPaQ0TI08S0Z]L]HP5PSPZPtPSPZQ0UPZP]PTQ0UC>%UWRZ/JtL0ZPZQ0UP@P2P1PCPYfZRZ#3RuP5P:P[C>RvPuP\Q0JPsP5P:P[F:PuPQPePNP5P:P[F:Rw3xn200110300012010x10yX0X>0~XWP@P2P1PCPY1=vwn200110300012010x10yX0X>1pXW%PW&02W&0J<Q0EH0dJ0nS0[#7PsPsPEPr%HsRrPWPtQ0UJ0iPiH1vPr%is%ZsPqPXPWPtPfH1wPp11gl%fs%js%gsM;y$0[&0[aS0\55JPJQ04Q01Q04Q04P:P:PZPZPEPu%HZRuPnPsPWJ0iPZH0IPu%iZ%ZZ%PZPXPnPsPZH0M%QZ20@Z4%fZ%jZ%gZM;yRun10110O00021010400XlJPoQ0YP:J2GQ04Q0U75`Q04?5utQ04PmPmPEPj%HmRjPZPnPsJ0iPmH0IPj%im%Zm%PmPXPZPnPmH0M%Qm20@m0%fm%jm%gmM;yRjQ04PDf]RuPuP:Q0UPtPnK00f^S0]P5PsPWPtI08_0VY0_PDf\S0^Q0^PjPaQ0UPsK00PSQ0^#3RjPmAWSjZPjPdPUPZC>I2JQ0^#URjPm1JjZP@P2P1PCPYf_S0_#3RjP5P:P[C>R`PjP^PkPuP5P:P[F:PjPVQ0GQ0MP5P:P[F:Ro3xn200110300012010x10yX0XQ0^60~XP@P2P1PCPY1=`on200110300012010x10yX0XQ0^61pXJ0nRoQ0^#PQ0^$02&0J?Q0EH0dR`<0b<20ao`P7PS%3uR`Q0^PSP`PmP`PhPdPmC>%UuR`Q0^'JL0Z1J`mP@P2P1PCPYf`S0`#3R`P5P:P[C>RoP`Q0RP^Q0]P5P:P[F:P`PRPVQ0GP5P:P[F:R`3xn200110300012010x10yX0X>0~XuP@P2P1PCPY1=o`n200110300012010x10yX0X>1pXuH1Z%Pu&02u&0JKQ0EH0d#7Q0_Q0]Q0]PEQ0]Q0]#HR`PuQ0^PmJ1AQ0]H0IP`Q0]#iQ0]#ZQ0]#PPXPuQ0^Q0]H0MQ0]#QQ0]00@MQ0]#fQ0]#jQ0]#gM;yPnPsPWI08P:PSPjQ0]PSPjPuPjP^PkPuC>Q0_#URjQ0]'JL0Z1JjuP@P2P1PCPYfbS0a#3RjP5P:P[C>R`PjQ0QQ0NQ0`P5P:P[F:PjP]PTPRP5P:P[F:Ro3xn200110300012010x10yX0XQ0_60~XP@P2P1PCPY1=`on200110300012010x10yX0XQ0_61pXH1ZQ0`#PQ0`$02&0JNQ0EH0d#7PSfaS0b#3RoQ0`Q0_9WSoH24PoQ0NQ0RQ0_C>Q0b#URoQ0`'JQ0_,JoP@P2P1PCPYfdS0c#3RoP5P:P[C>R`PoPaQ0TQ0aP5P:P[F:PoQ0JPbP]P5P:P[F:Rl3xn200110300012010x10yX0XQ0b60~XI3NRgP@P2P1PCPY1=`ln200110300012010x10yX0XQ0b61pXRl<0b520aglP7PSPjQ0bQ0`9WSjPjQ0QQ0NQ0`C>I2JQ0a#URjQ0b'JQ0`,JjP@P2P1PCPYfeS0d#3RjP5P:P[C>RlPjQ0UPafcS0eP5P:P[F:PjP\Q0JPbP5P:P[F:Rj3xn200110300012010x10yX0XQ0a60~XH1ZP@P2P1PCPY1=ljn200110300012010x10yX0XQ0a#Q60]XQ0cQ0eQ0ePEQ0eQ0e#HRjQ0aQ0bQ0`J1AQ0eH0IPjQ0e#iQ0e#ZQ0e#PPXQ0aQ0bQ0eH0MQ0e#QQ0e00@PQ0e#fQ0e#jQ0e#gM;yQ0]PuQ0^I08P:PSPoQ0eQ0a9WSoPoPaQ0TQ0aC>I2JQ0c#URoQ0e'JQ0a,JoP@P2P1PCPYfgS0f#3RoP5P:P[PoPWPtQ0dP5P:P[F:PoPdPUP\P5P:P[F:J1=n200110300012010x10yX0XQ0c60~XH1ZP@P2P1PCPYfhRj#3RlP5P:P[PlPhPdPUP5P:P[F:I1Xn200110300012010x10yX0XQ0d#Q60]XffS0g#3RgQ0d5WSQ0c9WSgPgPtQ0UQ0cC>Q0g#URgQ0d'JQ0c,JgI3NRgP@P2P1PCPYfiS0h#3R`P5P:P[P`PnPsQ0fP5P:P[F:P`PkPhPdP5P:P[F:J1=n200110300012010x10yX0XQ0g60~XRp<0b520agpP7PSPoQ0gQ0d9WSoH24PoPWPtQ0dC>Q0f#URoQ0g'JQ0d,JoH1ZP@P2P1PCPYfjS0i#3S0jP5P:P[Q0jPZPnPjP5P:P[F:Q0jP^PkPhP5P:P[F:J1=n200110300012010x10yX0XQ0f#|60]XQ0hPjPjPEPl%HjRlQ0fQ0gQ0dJ0iPjH0IPl%ij%Zj%PjPXQ0fQ0gPjH0M%Qj20@jR%fj%jj%gjM;yQ0eQ0aQ0bI08P:PSP`PjQ0f9WS`H24P`PnPsQ0fC>Q0h#UR`/JjQ0f,J`H1ZP@P2P1PCPYfmR`#3RlP5P:P[PlPuQ0^fkS0kP5P:P[F:PlQ0QQ0NQ0RP5P:P[F:J1=n200110300012010x10yX0XQ0i#|60]XPSQ0k#3RoQ0iPSPoQ0hPoPmPZQ0hC>Q0k#URoQ0i'JL0ZRpQ0h,JoRo<0b520apoP7flS0l#3RoQ0k5WSQ0i9WSoPoQ0^PmQ0iC>Q0l#URoQ0k'JH1ZQ0i,Jo#7fnS0mP`P`PEPl%H`RlQ0lQ0kQ0iJ0iP`H0IPl%i`%Z`%P`PXQ0lQ0kP`H0M%Q`20@`\%f`%j`%g`M;yPjQ0fQ0gI08P:Q0m#3Rl=WS`Q0l9WSlPlQ0]PuQ0lC>Q0m#U/J`H1ZfoS0n#U/J`#7PSfpS0o#3RlQ0nQ0m9WSlPlQ0`Q0_Q0mC>I2JRlQ0o#UQ0n'JRo<0b520aloP7PSfqS0p#3RoQ0oQ0n9WSoH24PoQ0bQ0`Q0nC>+0kQ0p#UQ0o'J#7fsS0qfrRoPoPEPo%HoRlQ0pQ0oQ0nJ1APoH0IPl%io%Zo%PoPXQ0pQ0oPoH0M%Qo20@o^%fo%jo%goM;yP`Q0lQ0kI08P:PSQ0q#3RlPoQ0p9WSlH24PlQ0eQ0aQ0pC>+0kftS0r#UQ0q'J#7PSfuS0s#3RlQ0rQ0q9WSlH24RpPlQ0dQ0cQ0qC>Rl<0b520aplP7fvS0t#3RlQ0s5WSQ0r9WSl+0kPlQ0gQ0dQ0rC>#7fxS0ufwRlPlPEPl%HlRpQ0tQ0sQ0rJ1APlH0IPp%il%Zl%PlPXQ0tQ0sPlH0M%Ql20@la%fl%jl%glM;yPoQ0pQ0oI08P:Q0u#3Rp=WSlQ0t9WSp+0kfyS0v#3Q0hPjPlC>#7fzS0w#3RpQ0v5WSRgQ0u9WSpRp<0b520agpP7f{S0x#3RpQ0w5WS#7Q0v9WSp#7f}S0yf|RpPpPEPp%HpRgQ0xQ0wQ0vJ1APpH0IPg%ip%Zp%PpPXQ0xQ0wPpH0M%Qp20@pn%fp%jp%gpM;yPlQ0tQ0sI08P:Q0y#3=WSp#7f~S0z#3=WSp#7P71S5:S0{#714;5S0|[S0}145:S0~1S;5S10#7Rg[S11143;\g24J5:S12P5n2001000000120000000XI1XW1Q0}^I1^W1P:p+01AS13#PQ13$02&0Ju42sRgQ0EP^O3Q0E,4gp+01CS14p+01BS15PpQ0xQ0wQ0uJ4HPDQ14Q14Q15Q0wQ0xQ15#3K00PDp+01DS16Q16Q14Q0xPpClQ14#3Q13Q0_P:Q0]L4FQ16Q1350>Q0_'4p+01ES17Q17Q16PpQ0yClQ16#3Q0qPoQ15P5P?L2oQ17Q0q;<oRgQ17Q1550>Rf,1g&0p6S18Q0B$0pS19+2CRg<1Ef+19P7p+01FRfQ0rQ0q3<Rq#2Q1490>fRr,1q@1Egrp+01GS1:PfPfPEPf%HfRrQ17Q16Q14J1APfH0IPr%if%Zf%PfPXQ17Q16PfH0M%QfQ0a-0@f%ff%jf%gfM;yQ13p+01@S1;Q0zI08P:p+01HS1<Q0tQ0s3<#2p+01IS1=Q0t,MlQ1==0>fRr420@1EgrP7p+01JS1>Q0u;<lQ1>Q1:50>Rr;?g%]rp+01KS1?Q1>Q1>PEQ1>Q1>#HRrQ1=Q1<Q1:J1AQ1>H0IPrQ1>#iQ1>#ZQ1>#PPXQ1=Q1<Q1>H0MQ1>#QQ1>Q0g+0@Q1>#fQ1>#jQ1>#gM;yQ17Q16Q14I08P:p+01LS1@Q0wQ0v3<Q1@Q1=50>;?gp+01MS1AQ1>50>#]p+01NRrQ1@PpQ0xQ0wQ18Q19+3@S1BQ18#]S1CQ19#2%]gS1D[[S1EQ18#2S1Fg0157S1GQ18Q19<3?5UWXS1HQ1FQ1G%2gS1I[]XS1Jg00WZS1K#\S1L#\Rq#\S1M$0>S1N&0>qS1OQ1K-3=1S1P'qS1Q'qS1R&2A9S1S+1PS1T&1u9S1U&411R9P;&0H;S1VP5P9D~&3~1S1W&3{1RqPq23;1BRiQ0H#KS1X#OS1Y+0L&28GRGPqPqQ0<-391RwQ1YQ18$1iS1Z>381>S1[PGPqALqiwS1\PGQ1\Q1[9[qwS1]61dqS1^H2?S1_K0sI1c23pqHS1`P:P;Q06-12CS1a23o:;#7dB4y1B5H4xS1bb;b<b=X11X31%]5RH115;S1c/4g%2;S1d%23S1e163gS1f'C[[[^11^31S1gP:p+01QS1h=0>rQ1hQ1;Q0z3<P3P<P0O5b8b[b\J30Q1@90>rQ0x9<rp'@PrPrPEPr%HrRvQ1AQ1@Q1?J1APrH0IPv%ir%Zr%PrPXQ1AQ1@PrH0M%QrQ0i-0@r%fr%jr%grM;yQ04Q1hp+01PRvp+01OS1i02=rRxQ1=P:PvPvPEPv%HvQ1iPrQ1AJ1APvH0I%iv%Zv%Pv%QvQ0l-0@v%fv%jv%gvN>4qXM=Q1hP5Q1=P:H1g#7p+01RS1jQ1hQ1>P5H1g#7[^M=22E11S1k$1uS1lQ1kQ1h02@xQ1h01Nv40gRx+12Q1lQ1h01N5;5xQ1j/EvRx$1|1;>xRx?Dxgp+01SS1m/EvRx$1|1;>xRx?Dxgp+01TS1nQ1j50>RxPxP>Q1nQ1hH0?RyQ1BQ1EQ1HQ1JQ1SQ1UQ1V?h59S1oQ1WPqPq%O6S1p-0LiPGQ1p,FwS1q9LqwI1cQ1`Q1bb;b<b=X11X31Q1c,45\H^11^31P:p+01WS1rQ1n50>RHQ1rp+01US1s50>R6P?O3b8b[b\43_&0zy&0|x1syxQ0H#{S1t#{S1u#{S1v#{$1`$1`$1`S1w#K$0pRy'141^&4`ERxQ1sQ1m50>RzQ0?$0pR{401S1xPzP>Q1sQ1jH0?Rz>01x{S1y1Yz{%2z%2{Rz116HS1z00X{[[Q1BQ1EQ1HQ1Jp+01XS1{p+01VS1|50>S1}/Y{Q1}#2p+01ZS1~Q1{50>R6/8{RH#2\z[p+01YS20Q1r50>S2100U{&2N{R|$1rS22P620e{HP6P{H3m[1_6{%]{RHp+01[S23Q2050>S24/9{R}?D}{[Q24/a{16{BS25p+01\S26Q1~50>S27/9{R}=b{}[Q27/d{p+01]S28Q2350>R}/8{S29$2N\|1c}{p+01^S2:Q2650>S2;Q2;7`{\|Q2;/8{P1p+01_S2<Q2850>S2=/9{P1P>p+01`S2>Q2:Q2>Q2850>CvS2?00U{Q22P>p+01aS2@Q2<Q2@Q2:50>CvR~P{P~P{19~{S2AI4T[1_~{p+01bS2BQ2>50>S2CP>Q2BQ2<H0?S2D/9{R~?D~{\HQ2D/a{Q25p+01cS2DQ2@50>S2EP>Q2DQ2>H0?S2F/9{R~=b{~[Q2F/d{p+01dS2FQ2B50>S2GP>Q2FQ2@H0?R~/n{\|1c~{p+01eS2HQ2D50>S2IP>Q2HQ2BH0?R~?`{~\|18~{P1p+01fS2JQ2F50>S2KQ2JQ2D50><2K{P1P7p+01gS2LQ2F50>R~#216~g11x;9?x?Q0Gp+01iS2MQ2J61]>p+01jS2NQ2L'E>0G>gP7p+01kS2OQ2M50>R~#216~g11x89?xNPbp+01mS2PQ2O61]>p+01nS2Qp+01lS2R'E>0G>gPTP5O1%2OS2S\zS2Tp-0R~Q1M#\S1M#\S2U#\S2V$0>S2WQ2U$0>S2UQ1M$0>S1MQ0<$3U-3T1S2XQ1N+10Q1L$0>S1L23R1{S2YQ1P+0qS2Z'qS2[I1qS2\Q1S+1PQ1U&0H<S2]P4P9P;&0H8S2^9h94P5P9P3&0HAS2_P4&0H4S2`I0RK04Q1WPqPq&1i{S2a9[qiS2bPGPq20Qq?S2cPqQ1u#OS2dQ2a+0LH1FPGPqPqQ2a>2`qi-3QqS2ePGPqQ0=#{S2f#OS2gQ0?#OS2h'FS2iQ2aQ0H#OS0H+1oS2jQ2dH0<PGPqPqQ2bPGQ1t#KS2k#OS2l9LqiS2m20QqKS2n61dqPGPqPqQ2ePGPqQ2gQ2aQ1p+1oS2oQ2lH0<PGPqQ2g9LqiS2pPGPqQ2h9[qiS2qPGQ1qQ0H,Fw5LqK0:FNFNFNFNQ1`Q1bb;b<b=X11X31X41X51X91X?1X@1X>~WDAr04{\Hg00[ZS2r\|S2s118A20e{<S2t;k0[%20S2u/CMS2v\HQ2s20e{AS2w=k0?[Q2u%]0S2x1184S2y1180S2z'4[[[[[[^11^31^41^51^91^?1^@1^>~^D~P:16O{%2KS2{PKPOp+021S2|p+01oS2}50>Q2|Q2Q50>PMQ0MPxPQPPPTP]P3Q0TO?b8b[WbWaP5P:O2n2001000000121000000W`WjP5P:O2n2001000000121000000bpbnbibhbgbfbebobmbdbcb_bZb2b[b\b6b743_Q1y$0zQ1x$0|Q1yQ1x's/1y41^Q1|Q1n50>S1yP>Q1|Q1mH0?S1x/Y{Q1x#2Q1}P>Q1{Q1sH0?00X{\z[Q1BQ1EQ1HQ1JQ21/Y{Q21#2Q2400X{\z[Q0s/Y{Q0s#220Xl{\z[Q24P>Q23Q1{H0?00U{Q22Q27P>Q26Q20H0?S24P{Q24P{Q24P{Ew[Q24/_{Q28Q1~50>S24,1}S1}/9{S2~Q2~;D{\HQ1}/a{Q25Q2;P>Q2:Q23H0?S2;/9{S2~Q2~5b{[Q2;/d{Q2=P>Q2<Q26H0?S2=/n{\|Q2=/c{Q2?Q2?7`{\|Q2?/8{P1Q2AP1Q2C00U{Q22Q2EP{Q2EP{Q2EP{Ew[Q2E/_{Q2G/9{S2EQ2E;D{\HQ2G/a{Q25Q2I/9{S2GQ2G5b{[Q2I/d{Q2K/n{\|Q2K/c{Q2LQ2H50>S2KQ2K7`{\|Q2K/8{P1p+01hS2KQ2J'E>0c>{P1Q1700U{Q22PfP{PfP{PfP{Ew[1_f{Q1:/9{S2IQ2I;D{\HQ1:/a{Q25Q1</9{S2IQ2I5b{[Q1</d{Q1=/n{\|Q1=/c{Q1>Q1>7`{\|Q1>/8{P1Q1?/9{P1P7p+020S2IQ2P50>S2G#2Q2G/6gQ0<$0pS0<,1;S2G:1^P?Pdp+022S2EQ2}61]>p+023S2CQ2I'E>0G>gP7p+024S2AQ2E50>S2?#2Q2?/6gQ0<,18:1^VNQ0Np+026S2?Q2A61]>p+027S2=p+025S2;'E>0G>gPkP5O1Q2TQ2V#\S2V#\S2T$0>S2~Q2V$0>S2VQ2\Q1SH0WQ1UQ2]P?P9P;&0H0S2\P?P9P?P9D~P5Q2`PAP9P?P9P3&0H?S30P8P9P?P9D~K04K04Q1WPqPqQ2bPGPq20QqMS31PqQ0>#{S32#{#OS33Q2a+0LH1FPGPqPqQ2ePGPqQ32#OS34Q2jQ33H0<PGPqPqQ2bPGPq20Qq_S35PqQ32#K#OS32Q2a+0LH1FPGPqPqQ2ePGPqQ2gQ2oQ32H0<PGPqPqQ2bPGPqPqPiQ0?#{S36#OS3720QqNS38I0KPGPqPqQ2ePGPqQ2iQ2a01owS39Q37H0<PGPqQ2qPGPqQ2hQ345LqPGQ1p-29wS3:Q0HQ0<$1iS3;'FS3<5LqK0:FNFNFNFNFNFNQ1`Q1bb;b<b=X11X31X41X51X91X?1X@1XE1XK1X>~XD~XJ~ArK?{\HQ2sQ2t=k8K[ArNK{\HQ2sQ2w=k?M[%2MS3=/CP\HQ2s11M?20e{8;k_[%]?S3>14KMQ0<,1K:1^0?[[[[[[[[^11^31^41^51^91^?1^@1^E1^K1^>~^D~^J~P:16b{Q2SQ2{PKPOPbp+02:S3?p+028S3@50>Q1|Q3?Q2=50>PMQ0MQ0JPQPPPTP]PhPkQ0^Q0dODb8b\WuWtP5P:O2n2001000000121000000WsWrP5P:O2n2001000000121000000b{bzbqbbbab`bjbpbnbibhbgbfbebobmbdbcb_bZb2b[b\b6b7bAQ1x/8{Q1y/8{Q0p/8{Q0<'141^Q1z/Y{Q1z#2Q21P>Q20Q1|H0?00X{\z[Q1BQ1EQ1HQ1J1Y6{%26Q2700X{\z[Q0t/Y{Q0t#2Q0u/8{S27#2\z[Q2UQ1MQ1NQ1LQ1P'qS1L'qS21Q1SH0WQ1U&0HMS1zPMP9P<P9D~P;Q309h98P5P9PAQ2\P3Q2`PM&0HKS1yK2HD~Q1WPqPqQ2dQ0@#OS1x+29Q1YQ3;'FPGPqPqQ0HQ0>#OS0>+29S3AQ2lQ2d'FS3BQ2lQ1x'F+29&1iyR6'FPGPqPqQ3:Q1X#{#OS3CQ2g'FQ3C+29/F6PGPqPqQ3C9LqiS3DQ38PGPqPqQ2gQ0=#OS38PGQ3:Q3A/Fi'FQ38Q1Y'FS3AQ0B$2x$2wS0B$2xS3E$0pR6$1i'F5LqEVEoEVEVEVQ1`Q1bb;b<b=X11X31X41X51X91X?1X@1XE1XK1XN1XO1X>~Q0<,1AS3F:1^?K1s3<S3G11?KS3H11?M's<3Py11?0/s?/1y:1^;3Q2{/Ce14K01sA81s40$27Q3H/163?[[[[[^11^31^41^51^91^?1^@1^E1^K1^N1^O1^>~P:16}gQ29Q1}/8{RyPxP}Q24Q27Q0uQ29,1x$0|11xy$0z&0|}Q1}$0zP8P4P0PKPbOAb8b[b\b6b7bAc1Ac1@c1?Q1nQ1j'TR}Q1nQ1h42vRy$0z&0|}'sB01xy{$0zB01x}{$0|'s$27Q0nQ0n/8{<2s63?ec1`c0kQ1j/TvR}Q1jQ1i42v$0z&0|}'sS1}Q1jQ1i-2=vR}$03'TRyQ1j%R}42vS29>01x{$0zB01xy{$0|'s$2718`{>2s`6R63?eQ1}Q1j02u}$0zS27Q1j02F}$0|S24's$27;?6eQ1kP1P1&0|yQ29$0zH1CQ1kP1P1Q24Q27H1CQ1k$2A40D40D$0f/46eQ1j02@}$0f&0J`'4R}eP}PcPLQ0tQ0sQ0rH1BPDQ1nQ1nP<Q1@Q1AP@PLP2Q0;P:P@P2P1Q0;P5Q01PIQ0;Q1r#3R}Q1r#HR6Q07g03@;S27Q07$2A40DS24P5P:P;J251M;5RyP3PyP3Q05$2AS29I0PQ29n10110300021010400n200110000012012>12?n200110300012010010|K00X0cQ1j#3S1}Q1j#HS3IQ24Q0tQ0sQ0rJ25&2IIS3JQ3J012:Q3JQ1m#3Q1m#HQ24PlQ0tQ0sJ25;5:Q01PIQ3JQ1s#3Q1s#HQ24Q0vQ0uPlJ25;5:PDQ1rQ1rP4Q1iPvQ01PIQ0;P5Q0xQ0w'MRyQ0vPyQ0vQ29I0PQ29n10110300021010400K00_0<P5Q3JQ1|#3Q1|#HQ24Q0wQ0vQ0uJ2522:I:35PI&14:&2_:S0;Q24+4SQ1{#3RyPpQ0xQ0w&0C:&06:J1?3xXIIP6P5P:I4RB07I56&145Q24-1>5P}Q0xQ0wQ0v&0C5&065J1?3x+4QP7Q1{#H:07I;&14;Q24-1>;'=PyPpQ0xQ0w&0C;S3K&06;S3LJ1?+0kPDQ1~Q1~PKQ1jQ1mQ0y/MpRyQ0xPyQ0xQ29I0PK00P:Q1~#H:07I<&14AQ24-1>A'=Q23#3Q1;Q0zQ0y&0CA&06AJ1?+0k&148Q24-1>8'=RyQ26#3Q13Q1;Q0z&0C8&068J1?R}<0b:20ay}P7&144Q24-1>4+0kQ28#3Q15Q13Q1;&0C4&064J1?#7PDQ2<Q2<PQQ1rQ1{Q14Q15'MR}Q13P}Q13Q29I0PK00P:&14?Q24-1>?+0kQ2>#3Q17Q16Q14&0CK&06KJ1?#7&14MR}Q24-1>MRy<0b520a}yP7&14_#7Q24-1>_#7PDQ2FQ2FPVQ26Q28Q1<Q1:'MRyPfPyPfQ29I0PK00P:&14e#7Q24-1>Q#7P7&0F:S0y#7%B5S3M[S3N%B:S3O&0F5S3P#7Ry[S3Q%B;S3R\y&4P:S3SP5n2001000000120000000XCCQ3N^CCP:&3KORyP;O2%ByPCQ0M$2_Q27+4ORyQ08'u%7:S3TXCCS3UP;Py&4NyJ1H%7yQ0G$2_RyQ27<4M:Q07Q2775yPDQ2OQ2OQ2NQ2DQ2FClQ2N#3Q1iPrQ1A&0CVRyPB&06VR}PWP?N<4LQ2O?<yBRyQ2OQ1i;<rR6P6Q2OQ1AQ2O>1ly}H0{3}P7Q2R&0CR;<BRyQ2RQ1i7<vR}'4P}Q2RPrQ2R&06R61lyH0{PDQ2PQ2PPhQ2HQ2JQ1h/MvRyQ1iPyQ1iQ29I0PK00P:Q2Q&0C];<BQ2QQ1jQ1h3<'4Q2}Q1mQ1j3<Q2}Q1hQ2}&0Cb/MBQ2}&06b+0N420H0{Q2IQ2}#HQ2K$1<RyQ0JQ2IQ2}Q2NQ2MQ2KQ2JJ3HPVP4K4K22E==R}Q2IQ0J+0;<07yP>P=P=P:H0mS3V#]P>P=P=P:H0lS3WQ0B$0pRy+23Q3V/9y&4IER6Q3WQ3WQ3V+1;3}S3W+1j40xZ0s}S3VQ2M$1<S0B60=}Q2O$1<:07}:Q3VP5O1S3X[^G}[Q2N$1<S3Y:07}:Q3X[^G}Q3VQ3Y60=}[Q3VQ0B63F}Q2|Q2IQ2OQ2NQ2MQ2LJ4GQ2|00;\S0BP:J2pQ3VQ0BO1P7P>P=P=Q2E00;US0BH0mS3Y#]P>P=P=Q0BH0lS0B/9yQ3Y/9yQ0BQ0BQ3Y+1;5}6+1j+1jPDQ2CQ2CQ0TQ2OQ2RQ1rQ1|'MS0BQ1sQ0BQ1sQ29I0PK00P:P>P=P=Q2A00;hH0m#]P>P=P=Q2;00;kS0BH0lS3Y/9yP>P=P=Q0BH0mS0B/9yQ3YQ3YQ0B+1;5}6+1j+1jP7P>P=P=Q2?00;^S3YH0lS0B023yP>P=P=Q3YH0mS3Y/9yQ0BQ0BQ3Y+1;5}6+1jPDQ2=Q2=PWQ2}Q2IQ23Q1~'MS0BQ20Q0BQ20Q29I0PK00P:P>P=P=Q3@Q0N+0;H0l023yP>P=P=p+029S0BQ0Q+0;S3YH0mS3X/9yP>P=P=Q3YH0lS3YQ3YQ3X+1;5}6+1jP7P>P=P=Q3?Q0T+0;S3YH0mS3X023yP>P=P=Q3YH0lS3YQ3YQ3X+1;5}6PDp+02;S3YQ3YPmQ2CQ2AQ2<Q2:'MS3XQ28Q3XQ28Q29I0PK00P:P>P=P=p+02<S3XQ0U+0;H0m023yP>P=P=p+02=S3Z00;tS3[H0lS3\Q3\P>P=P=Q3[H0m+1;5}6P7P>P=P=p+02>S3\00;WS3[H0lS3],46Q3]P>P=P=Q3[H0m+1;PDp+02?S3]Q3]Q0_Q2=Q3@Q2DQ2B'MS3[Q2@Q3[Q2@Q29I0PK00P:P>P=P=p+02@S3[00;nH0l,46P>P=P=p+02AS3^00;ZS3_H0lP>P=P=Q3_H0m+1;p+02BS3_=A>mS3`$27P>p+02CS3aQ2LQ2JCvS3b,4:X:1Q0GQ3`Q3`$3EI0^Q3`Q3_Q2J50>Q2H43PQ3aQ0^5A>S3`$27P>p+02DS3cQ2KQ2LCvQ3cQ2JQ3c&06u61l:H0{X:1Q0GQ3`Q3`$3EI0^Q3bQ3aQ2HQ3`Q3aQ0^$0641lH0{Q3c00AuS3`$1|Q3`,;>S3`Q3`;DgQ3cQ3a<0BS&4ExS3`+4DPLQ0Fp+02ES3b#3Q3cPSQ3`H1W>0SL:P@P2P1p+02GS3d#3p+02FS3ePSQ3`H1W>0SL:P@P2P1PcP5Q0Lp+02JS3f#3S3gp+02HS3h;XS62bLn200110300012012>12?PLQ2PQ2RQ2OH1B55cPDQ3fQ3fQ0iQ3_Q3aClS3iQ2QQ2P'MS2PQ2R+2nQ2PQ2RQ2944CI4B]x]kP5Q3gp+02IS2PPSQ3`H1WQ0L60SLQ0Pp+02KS3jQ2P<0BS62bLPLQ2IQ2}Q2QH1B55cPcP2P@PLP2P2P:P:n2001100000120100106XlcPLP3P;p+02LS0PQ3f<0BSS3kH1BPLQ2|Q2IQ2}H1BP:J2GQ3kQ2}552PcP1P@PLP2P1P:P@P2P1P1P5P:n2001100000120106101n2001100000120100106XlcPLP<P3p+02MS3kQ3j<0BSH1BPLQ2EQ2|Q2IH1BP5J2GQ2|,@3PcP2P@PLP2P2P:P@P2P1P2P5P5n2001100000120106101n2001100000120100106XlcPLPAP<p+02NS3lQ0P<0BSH1BPLQ2CQ2EQ2|H1BP;J2GQ2C952AQ2A9528P2Q2;p+02QS3m#3p+02PS3nPSQ3`H1W22<:460SLQ2?,@0p+02SS3o#3S3pQ3m;XSQ2?552S3qPDp+02US3rQ3rQ0sQ3kQ3lQ0BQ3@'MRcQ2=PcQ2=Q29I0PK00[[]kZ0z2Q3n#3p+02OS3sPSQ3`H1WQ2;02<860SLQ2;,@4P1Q2?Q3pp+02RS3pPSQ3`H1WQ3@02<:60SLp+02TS3tQ3p<0BSS3uQ2=552PDp+02VS3vQ3vQ0tQ3lQ3sQ3?Q0B'MRcQ3@PcQ3@Q29I0PK00[]kZ0{1Q3p#3Q3mPSQ3`H1WQ2=Q2?+2<60SLQ3qP2Q3uP@P2P1PCPYp+02XS3u#3S3wP5P:P[C>S3xQ3wQ3hQ3dQ3vP5P:P[F:Q3wQ3ZQ3XP3P5P:P[F:3xn200110300012010x10yX0XQ3r#|60]XP@P2P1PCPYp+02YRc#3S3yP5P:P[Q3yQ3\Q3ZP<P5P:P[F:I1Xn200110300012010x10yX0XQ3v#Q60]Xp+02WS3z#3S3{Q3XQ3YP;Q0p$0CS3|Q0p$06S3}J1?#7P>PcQ3ZQ3XCvPcP320Aco&06o-0Nc63D>H0{PDp+02ZS3~Q3~Q0wQ3pQ3oQ3\Q3Z'MS40P<Q40P<Q29I0PK00_0J_0Z_0X_0WZ0|2P@P2P1PCPYQ3{P5P:P[Q3{Q3dQ3eQ3rP5P:P[F:Q3{Q3XQ3YQ3{Q3r;XSS3{P5P:P[F:J1=n200110300012010x10yX0XQ3t#|60]XP@P2P1PCPYQ3xQ3wQ3ZQ3XQ3wQ3v;XSS3xP5P:P[L4An200110300012010x10yX0XQ3r#Q60]XQ3v#3S40Q3YQ3?Q40Q3t;XSQ0o$0CQ0o$06J1?#7P>Q3uQ3XQ3YCvQ3uQ3{P>Q3uQ3|Q3uQ3}+0NCvH0{P=g06WnS3}Q3v,EcS3|20w>SS3{421S401;>:S41Q3~Q3z50>S42/8{S43'@XC=Q3|,;>S44Q18Q3{,;>S45Q19'9+2CS46'8Q43,@:X:1PSQ42Q18Q19,9:S47+2CS48'8Q43'@X:1Q44/8{S44#IQ45Q1BQ1EQ1HQ1JQ1SQ1UP9Q1WPqPqPi&1iSS43Q43Q1[5[qI0KQ1`Q1bb;b<b=ADSSgS43P:b8b6b7S42-1DSS49DmQ40,;>Q3|Q3{+3BDmQ3x,EcPDPcPcQ3uQ3mQ3pClQ3wQ3vPSQ3{PfPSQ47/@SX:1S47%ISS3wQ45Q49DmN93AJ1VQ3x-0NcQ44'@RcePcQ3~Q3yQ3zPSH0uRc$1|1;>cRc?Dcgp,9SHADOW_okg07[bp+02\S3yQ3~'ERc$1|1;>cRc?Dcgp+02]S44Q3^Q3[3<P1P>p+02^S3xQ3_Q3^CvRc#I1@:cp+02_S49Q3x#3Q44PSQ3`H1WRcQ3aQ3_PMI4@Q49/EcQ49Q3a50>Q3_60\>55=P=p+02`S3|g05ChRcQ49Q3x<0BSS40Q3`44?'Ep+02aS4:Q3b50>Q3c60\>S4;95=:XC=P:Q3|Q40'EQ3|Q3`'E621cS4<Q3|PcQ40Q3`H4>J1HQ4<Q3|Q3c50>Q3a60\>55=P=P1&4=>Q4:Q3|#3S4<Q49PSH0u20w>xS3`621cS40Q4;P:J2GQ40,;>Q4;,;>'@p+02bS4;Q4:#3S40Q3|PSH0uS4=Q3`621c,;>P>p+02cS4>Q3dQ3eCv:0o>>S4?,@:X:1P:Q4=,;>Q3`,;>Rc<2KgS4@Q4=Q3`+4<I0^Q4@P>Q4;Q3eQ3bCv:0o>>'@P=Q4>Q4;#3S4@Q4:PSH0uQ41PcPgP>p+02dS4=Q3hQ3dCvS3`:0o>>S4AH16XC=P:Q3}Q4>Q4:'EQ3{421S4BPDQ4>Q4>Q4;p+02[S4CQ3yClQ4@Q4:PSQ3{PvPSQ47Q3wQ45Q4>Q3dQ3e3<S3w#IQ3w,@AS3weQ3wQ18Q2f#{S3w#{S47$0pS4D+3@S4EQ1CQ4D#2Q18Q4D+2CS4F#][[S1CQ1FQ1GQ18Q4D<3?5UWXS4DQ1FQ1GQ4F#2[]XS1FQ42bAbBS42bF-1DSDmN93AJ1HQ4B>3D>cQ4?7`gQ3}Q4=Q4;'ES4?Q3{421,;>P:PcPgP>p+02eS3}Q2PQ3hCvS4B:0o>>S4GH16X:1P:Q4?Q4664;>S46Q4?Q3{+3BI0^Q46PcPgQ4AH16Q45p+02fS45Q4=50>S4AQ48'8PcPgP>Q45Q3fQ2PCv:0o>>S48H16X:1P:PSQ42Q43e-1DSI0^Q3}Q4>50>S43Q18Q19,9S+2CS18'8PcPgQ4GH16PcP>p+02gS4GQ3}Q18H1US19P:PgP>Q4GQ3jQ3fCvRc:0o>>S42H16X:1P:PxQ4EQ1CQ4DQ1FQ1BQ1EQ1HQ1JQ1SQ1U&0H5Q1WPqPqQ1\Q1ZQ47$2Z6381S1Z9LqwPGQ1^EoQ1`Q1bb;b<b=X11%2:S1^Q4F82\:%25S47?r5gS46[^11P:PxPQO2b8b6b7bAbBADxxge-1DxI0^Q4AQ18'8PxPgQ48H16Q42p+02hS42Q4550>S48Q18'8PxPgP:H16X:1P:PcQ4EQ1CQ4DQ1FQ1BQ1EQ1HQ1JQ2UQ1R'qS1RQ1MQ1L'qS18Q1S42[Q1UP9P;Q2]9h9AP5P9PA&0H3S4APAP9PAQ2_K2HD~Q1WPqPqQ2m20Qq4S2mPGPqPqQ3D20Qq0PGPqPqQ3CQ2d'FS4?Q1w#{$1`#K$1`$1`$1`$1`#K$2x$2w$1T$1T$0pS1w$1iS3{PGPqPqQ1qQ2lQ4?PGPqPqQ3CQ1qPGPqPqPiQ1qQ1qQ1[5[qI0KS4?EVK0sEVEoEoQ1`Q1bb;b<b=X11X31X41X51X91X>~XD~Q1e/CAQ1e/C4Q1w9?<8113<S4H11A47?811<AS4I,4811A8S4JQ4J;DgS4K[[[[[^11^31^41^51^91^>~^D~P:p+02lS4L=A>fS4M/6gQ4Lp+02kS4Np+02iS4O<0BS50>S4P/6gQ4L=G>fS4QQ4PQ4MQ3sQ4LQ3n50>POPWPZQ0GPnO<b8b6b7bAbBADccge-1DcI0^Q19PxPgPcH16Q48/8{/1xS19/9gQ4OQ3k50>S4MQ0P5k:X:1P:Q19Q19Q4EQ1CQ4DQ1FP>p+02jS4PQ42P{H1US4R/1xRc00Eg%2cQ1IP>Q4LQ4PP{H1U/1x00Og[[Q4NQ4250>S1I/Y{S4SQ1I#2p+02mS4TQ4P50>S4U/8{S4V#2\z[S4WQ4Q00EyS4XQ4Q#2%2yS4Qp+02nS4YQ1<5G>00Oy[[S4ZQ1BQ1EQ1HQ1Jp+02oS4[Q4T50>Rc/Y{S4\%2cp+031S4]Q4[50>S4^00X{\z[S4_p+030S4`Q1>5A>Rc00EyS4a%2cQ4Qp+032S4bQ1@5A>S4c00Oy[[S4dQ4^00U{S4^Q22Q4bQ4`50>S4eQ4e/8{S4f-0e{Q4eP{H3m[S4gQ4e/_{S4hp+033S4iQ4]50>S4j/9{Rc?Dc{\HS4kQ4j/a{S4jQ25p+034S4lQ4b50>S4m/9{Rc=b{c[S4nQ4m/d{S4mp+035S4oQ4i50>Rc/n{\|S4p1cc{S4qp+036S4rQ4l50>Rc?`{c\|S4s18c{S4tP1p+037S4uQ4o'E>0c>{S4vP1p+038S4wQ4o'E>0j>{Q22p+039S4xQ4r50>RcP{PcP{PcP{Ew[1_c{p+03:S4yQ4u50>S4z/9{Rc?Dc{\HQ4z/a{Q25p+03;S4zQ4w50>S4{/9{Rc=b{c[Q4{/d{p+03<RcQ4x50>S4{/n{\|Q4{/c{p+03=S4{Q4y50>S4|Q4|7`{\|Q4|/8{P1p+03>S4}Q4z50>S4~/9{P1p+03?S50Q20+0A>0j>y&2NyS51$1rS52p+03@S53Q1~5A>S54PyQ54PyQ54PyEw[Q54/_y%]yS54p+03AS55Q235A>S56/9yS57Q57;Dy[Q56/ay16yBS56p+03BS57Q265A>S58/9yS59Q595by[Q58/dyQ51p+03CS58Q285A>S59/ny[Q59/cyQ51p+03DS59Q2:5A>S5:Q5:7`y[Q5:/8yP1p+03ES5;Q2<+0A>0c>yP1p+03FS5<Q2>+1S>0j>yQ52p+03GS5=Q2@5G>S5>PyQ5>PyQ5>PyEw[Q5>/_yQ54p+03HS5>Q2B5G>S5?/9yS5@Q5@;Dy[Q5?/ayQ56p+03IS5@Q2D5G>S5A/9yS5BQ5B5by[Q5A/dyQ51p+03JS5AQ2F5G>S5B/ny[Q5B/cyQ51p+03KS5BQ2H5G>S5CQ5C7`y[Q5C/8yP1p+03LS5CQ2J+1S>0c>yP111Tx00Ug&2NgS2J$1r11]xS5DPgQ5DPgQ5DPgEw[Q5D/_gQ1D11bxS5D/9gS5EQ5E;Dg[Q5D/ag16gBQ0J/1xS5D/9gS5EQ5E5bg[Q5D/dgQ2J11\xS5D/ng[Q5D/cgQ2J11UxS5DQ5D7`g[Q5D/8gP1B2KdxgP1P7p+03TS5Dp+03RS5E50>S5F#2Q5F/6g11kxS5GQ5G;DgQ0fp+03VS5GQ5D61]>p+03WS5Hp+03US5I'E>0G>gP7p+03XS5JQ5HQ5I<0BSS5K50>S5L#2Q5L/6gQ0Q/1xS5LQ5L;DgP`p+03ZS5Lp+03YS5M#3Q5HPSH0u-1~>p+03[S5NQ5L#3Q5JPSH0u>0G>gP7p+03\S5OQ2?5A>S2?#2Q2?/6g11txS2?Q2?;DgQ1<p+03^S2?Q3@5A>S5P#2p+03_S5QQ0B5A>S5R/6gQ0`P?O1%2Z\zQ0`P;O1Q4Q%2dS5S[Q2T#\S2T#\S5T#\S5U#\S5V#\S5W$0>S5XQ2XQ5U$0>S5U+10Q2T$0>S2TQ2YQ2W+0qS5YQ2Z41RQ5W#\S5W#\S5Z$0>S5[Q2XQ5W$0>S5W+10Q1P41RQ3E#K$2w$1T$1T$1T$1T$1T$1T$0p-3R1Q1P+0qQ2YQ5[+0qQ5XQ5V$0>Q2YQ5U+0qQ2TQ2YQ2~+0qS5VQ5YQ2YQ2U+0qS3EQ2YQ1N+0qS5\I1qI1q+4:+49Q1S+48H0WQ1UQ2\P_Q1zP_P9P_&0H_S5]K2HP;Q2^9h9_P5Q30P_P9P_Q2_P_Q2]P3Q1yP4P9I0RK04D~Q1WPqPqQ1[9[qiPGPqPqPiQ3w#OS3w20QqeS5^I0KPGPqPqQ1[>2`qi-3QqPGPqQ1qQ1[Q2k#K#OS5_+1oQ3wH0<PGPqPqQ2bPGPqQ1X#KS1X#K#OS5`9LqiS5aPqQ5`Q2a+0LH1FPGPqPqQ2ePGPqQ2gQ39Q5`H0<PGPqPqQ3wQ3BPGPqPqQ2gQ1[+0LPGPqQ2pPGPqPqQ1p9LqiS39PqQ1pQ1Z+3>H1FPGPqPqPiQ1xPGPqPqQ3CQ37'FS1ZQ3{PGPqQ379[qiS37PGPqQ3BQ1x'FQ1Z5LqPGPqQ1t#OS1t9[qiS1ZPGQ4?H2?K0:EVEVK0:I1cJ1QFNFNFNFNQ1`Q1bb;b<b=X11X31X41X51X91X?1X@1XE1XK1XN1XO1XV1X>~Q1DQ2{/CN[Q2JQ2r[11;3S2J20egN;kM[%2NS1D?rN{\HQ2sQ2t=k4e[Q3H,@N160g%2?Q2uQ4F82\0%2QS3HQ1w9?NOQ0M#]11POS2tQ0MQ0G,1QS2{3?%]eS3B11NeS5bQ5b;Dg[[[[[[[[[[[[[^11^31^41^51^91^?1^@1^E1^K1^N1^O1^V1^>~P:16QgPPPmPQp+03cS5bQ3Z5G>Q5bp+03bS5cp+03`S5d<0BS50>S5eQ5<Q5bQ5=50>Q5bQ3Z5A>S5fQ5bp+03aS5g50>Q5bQ5d50>S5hPxQ0^PVPRQ0`Q0bQ0kPMP_PlP0Q1jQ2<Q0wQ3eOJb8b6b7Y0EY0DP5P:O2n2001000000121000000Y0CY0BP5P:O2n2001000000121000000Y0AY0;P5P:O2n2001000000121000000c0Qc0Pc0:c09c08c07b~c0?c0>b}bubtbsbrb{bzbqbbbab`bjbpbnbibhbgbfbebobmbdbcb_bZb2b6b7bAbBbPbQbRbSc0LQ19Q19;Dge847gI0^Q19Q42Q0P50>Q3j3kQ4EQ1CQ4DQ1FQ4SQ4WQ4XQ4ZQ1BQ1EQ1HQ1JQ4\Q4_Q4aQ4dQ2XQ2U+10Q1P'qS4dQ1S+1PQ1UQ2]?h;9S4aP5Q2\PAP9P0Q2^D~P3Q2`9h90I0RQ1WPqPqQ0>Q0H'FQ1qPGPqPqQ3DQ2nPGPqPqQ2d9LqiS4_Q31PGPqQ37PGPqQ349[qiPGQ1qQ0HQ0>'FS4\62`qK0:EoEoJ1QQ1`Q1bb;b<b=X11X31X41X51X91X?1X@1XE1X>~XD~113;11:5S4Z'@%28S4X/C?Q2v%]KS4WQ2xQ4J1140S4S'@[[[[[^11^31^41^51^91^?1^@1^E1^>~^D~P:Q4c/6gQ4e/6gQ4bQ1@5G>Q4cQ4eQ4bQ4[50>Q4fPxQ3rQ4bQ3v50>P?PRPuP`Q1sO?b8b6b7bAbBbPbQbRbSbTbTbTbTP>Q3}Q2PQ3h'MS4f$46Q4f$45CvQ43>01x{S43'@eQ43,@4ebTbTbTbTbTbTP>Q49Q44P{H1U9k5xQ1^Q4:Q4<Q3xPSH3<S4<7r:S43Q4;Q40Q49;XSS40+0NS4fQ1d?r;:X:1P:P>Q4;Q49P{H1US1dP0I0^Q47Q1d7r511A;P1Q3`11:<S3`Q3`;DgZ0]1PKQ4=Q4>Q4:PSH05Q4=Q4:50>S3`/8{'@Q3}Q4;50>S1d/Y{Q1d#2P>Q4GQ4=P{H1[\z[Q1BQ1EQ1HQ1JQ2WQ18'qQ2XQ2V+10S18Q1R'qQ1S42[Q1UQ2`P<P9P;Q2^P5Q2_?h39K04Q1WPqPqQ38Q2hPGPqPqQ0H9LqiQ0HQ2h5[qPGPqPqQ0>9LqiS1RQ2cPGPqPqQ0>Q1Y'FS2cQ3{PGPqPqQ1qQ38Q2cPGPqPqQ0>Q1qPGPqPqPiQ1qQ0H'FS2cQ2cQ1[5[qI0KEVK0sEVEoEoJ1QQ1`Q1bb;b<b=X11X31X41X51X91X?1X@1X>~1@<8Q1e?r34%2AS2c/C?Q2zQ1w'4Q4I114?7?0Q4J,40Q2y/10S2zQ2z;Dg[[[[[[^11^31^41^51^91^?1^@1^>~P:Q4OQ145A>S2z/6gP>Q4OQ45P{H1US4eQ4OQ145G>Q4OQ42Q45<0BS50>Q2zP0Q0PQ4MP<P8PaPWPPPtO>b8b6b7bAc0mP8PADmQ1^?r:gS4MeQ4MQ4BQ45Q1;5A>S4B11:AS4MQ4MQ4BQ45Q1;+1S844>S1;'63}Q4M$1fQ4MP:Q4MQ4MP:Q45Q4>50>S4c/8{S2vD^5}640xZ0]1PMQ3}Q4=Q4;PSH05S4MQ1d/8{S1d'@Q4c/Y{Q4c#2P>Q42Q3}P{H1[\z[Q1BQ1EQ1HQ1JQ18Q2UQ1QQ2WQ1L'qQ18Q2UQ1MQ1Q'qS1Q41RQ2WQ21'qQ1S+1P42[H0WQ1UQ2\P<P9P;Q2^P5Q30PAP9P3Q2`D~K04Q1WPqPqQ34Q2hPGPqPqQ1RQ0>Q2h5[qPGPqPqQ38,FwS1RQ1YPGPqPqQ1tPwPGPqPqQ1pQ0H'FS18Q34Q1RPGPqPqPwQ18PGPqPqPwQ18Q0>'FS4cQ4cQ1R5[qI0KPqPqQ4cQ1Y+0LPqPqQ1tQ4cPqPqQ18Q4cQ4cQ18Q2h'F5[qI0KI0KH4361dqEVK0sEVEVEoJ1QQ1`Q1bb;b<b=X11X31X41X51X91X?1X@1XE1XK11@04%2<S4c?r<0A?;8414?3Q4J11<07?_Q2y,4AP8Q4S/1?S1RQ1RP8PKD^Q1R/6MQ1RQ4SQ1RQ1RQ4SPND^5}_40x[[[[[[^11^31^41^51^91^?1^@1^E1^K1P:Q4PQ4OQ4G<0BSS4S50>Q4PQ4G50>S19/8{S5iP6Q09Q4PQ165G>P?Q3kQ4PQ3l50>Q4PQ165A>P<P4PsPnPOPWO?b8b6b7bAc0mP4P8DmQ3}Q0z5A>S5jP5P5Q5jQ3}Q0z5G>S5jD^&1f5P4P5P5P4Q1dD^9}6540xS1deQ1dP7Q4BQ1;,6;7};&1f;146;P0P;P;P0Q2vD^40xQ4GQ1<Q49Q3|20w>3I1:Q0DQ0C00wB+2:S0C55FP:Q42Q155A>RBP<P<PBQ42Q155G>D^&1fA146APMPAPAPMQ4eD^40xP7&1f8P_P8P8P_Q5iD^9}68Q4NQ1@Q4>Q4=20w>4I1:Q0C55FP:&1f0PQP?P?PQQ4VD^9}6?P7146KPPPKPKPPQ4YQ4N50>S4V/8{S5iD^Q4[PvQ4GQ4220w>MI1:Q0C55FP:146_Q0GPNPNQ0GP>Q4]Q4YP{H1UD^20w>eP=21DQeQ41/@QRBePBQ4lQ4i#HQ4L$1<RBPr1;>5S4eQ4lQ4iQ4YQ4TQ4LQ4PJ3HQ1=Q0xPPQ4oQ1i5A>S1<P:P:Q1<Q4oQ1i5G>D^X:1PMQ4eP:DmN942Q4e00hB#7Q07Q0;Q2735S27Q4wQ3K50>RBQ41Q41PBQ4wQ3L50>D^Q4eQ4]#z+17&1e5S1<Q4]$0`S4B+0r+1O[^M=[XIIS1;Q4l#HS1d+1aQ4r#H:07I:Q27Q4zQ3K50>RBQ41Q41PBQ4zQ3L50>D^Q4eQ4l#zS5k$1{S5l+0hQ1<Q4l$0`S5m+0r+1O[^M=[XIIP5O1[^GI[Q4o#HRB:07I:Q27Q4yQ3K50>S5nQ41Q41Q5nQ4yQ3L50>D^Q4eQ4i#z+17Q1<Q4i$0`+0r+1O[^M=[XIIP5O1[^GIQ27Q4xQ3K50>S5nQ41Q41Q5nQ4xQ3L50>D^Q4eQ4b#z+17Q1<Q4b$0`+0r+1O[^M=[XII01aB[Q1;Q1d63FIQ4oQ4lQ4[Q4YQ4TQ4NJ3}Q1iQ1>Q0wP;POQ4r=A>vRBP:P:PBQ4r=G>vD^X:1P_1;>;S1dP5DmN93|Q1dQ4T#z+17&1e;Q4T$0`+0r+1OP71;>3S1;Q4Y$2k+2Y&1e3S5nQ4Y$0`+0rQ4uQ1{Q4[Q4`P<I1:Q0C55FP:1;>AS5oQ4`$2k+2Y&1e8Q4B+0rp,4argHRBQ4yP4O2S4BPCQ0XPBQ4zP0O2S0X=5C:PCPBQ4{PKO2=5C:Q3M]XP5PBPcP?O2S5p#7p,9argH_highQ4{PKP:O3Q091;>KRB'4Q4}Q4;Q4:3<S5q#IQ0RQ5q'@S5qeS5rQ5qQ4EQ1CQ4DQ1FQ1BQ1EQ1HQ1JQ1NQ1OQ1L'qS1L'qS1OQ1S+1PQ1UP9P<Q4AP5P9P<Q1VD~P<P9P<Q2]?h<9S5sP<P9I0RD~Q1WPqPqQ3{Q33PGPqPqQ33Q32PGPqPq20Qq8Q32Q0=#KS0=#OS33Q2l'FS5t5[qPGPqPqQ5tQ3{PGQ2mEVEoJ1QEVQ1`Q1bb;b<b=X11X31X41X51X>~XD~Q1w/431@<3Q2J9r8<Q4HQ1w'4P?[[[[^11^31^41^51^>~^D~P:Q06Q0855CS4HQ5:Q0R'41;>OQ0RQ59Q2:5G>S2mQ5:P8PPPUPoO:b8b6b7bAbBbFQ4Heb2WXQ5p#BQ08-12CS4HWXn0110200020100P:O1bXc0qQ4B#BPcQ28Q4lP?H2XS4B$0F-1b:XCCP7Q0y#B%75S5:[Q3TQ3P#B[S3PQ5:&0F;S5t#B[&3z:P:n2001000000120000000XCCQ3P^CCP:Q4B22WEBS3PQ09/SB'uS32Q4o#zS5u-17BS5v$0F&1eKQ4o+3:S5w$0FQ4{Q2:<1zBS5x'uS5y5x:+0YXCCQ32Q06Q0y'=S5zQ5y'=+0YXCCQ32Q06Q08$0F'=S5yQ0yQ5x'u'=+0YXCCPbQ4{Q4z50>S5{>01x{S5|Q5{Q4|'1>01x{S5{,e:81y:Q4}Q0I50>S4|>01x{S5}Q4|P>Q4}%R:S4|H0?>01x{S5~,e581y5X0X%|cS6061KX+0YX:1P71u5:S61#7%7;Q5:+18S62[Q5:Q3T+181u;5S5:#7[S3TQ621u3;S63#7[23y5:P:n2001000000120000000X^CX]CQ3T^^C^]CP:Q5|Q0J'SS5|Q0JQ5{'eS5{'=S3TQ5}Q5~,e\81y\X0XQ6061KXS60Q3T#7Q60#7Q5|Q5{Q5|#7Q5{#7P7Q0}Q11Q0|1S3;S0}#7[Q12P:n2001000000120000000XI1XW1Q11^I1^W1P:Q4}=0>cS11>01x{P\Q5rQ5qQ4EQ1CQ4DQ1FQ55Q4}50>S12/Y{Q12#2Q58Q5350>S0|00X{\z[Q57Q265G>S6000EyQ60#2Q4QQ2m/9yS3T#2[[Q1BQ1EQ1HQ1JQ5;Q5850>S5}/Y{Q5}#2P>Q5=Q5;P{H1[\z[Q5<Q2>5A>S2>00EyQ2>#2Q4QQ5>Q2B5A>S2>00Oy[[Q2WQ4d'qQ1S+1PQ1UQ2\9h9<S4dP0P9P;P9P5Q2`?h09S5}P0Q2^P3Q2_?h09S5~D~K04Q1WPqPqQ5`Q0H5LqS62Q2nPGPqPqQ5`Q1qPGPqPqQ2pQ31PGPqPqQ3DQ35PGPqQ37PGPqQ2qPGQ1qQ0H5LqK0:S3DEoEoS64J1QEoQ1`Q1bb;b<b=X11X31X41X51X91X?1X@1XE1X>~XD~XJ~A}4;0Q1c,@0Q4X/CMQ2u/CNQ4WQ2xQ2y/40[[[[S4W[[^11^31^41^51^91^?1^@1^E1^>~^D~^J~P:Q2>/6gQ5>Q5<50>S2x/6gQ5>Q5;50>S2y/8{:2VaZPZQ5?Q2>Q2xQ2yPaQ2x/8{S2>PxPTPsPmQ0qQ16Q2OOAb8b6b7bAbBbPbQbRbSbFO3b2P71e5:S5?#716;5S2u[165:S1c1e;5S65#7[S66Q2u1e3;S67#7[23x5:P:n2001000000120000000XI1XW1Q66^I1^W1P:P\Q11Q4~'1>01x{Q5rQ5qQ4EQ1CQ4DQ1FP>Q55Q50Q12CvS12/Y{Q12#2P>Q58Q55Q0|Cv00X{\z[Q57Q5050>S0|/Y{Q0|#2P>Q59Q55P{H1[\z[Q58Q285G>S0|00EyQ0|#2Q4QQ5;Q2<+1S>0c>yS12#2[[Q1BQ1EQ1HQ1JQ5<Q5950>S5q/Y{Q5q#2S5rQ2>#2\z[Q5=Q2@5A>S2>00EyQ2>#2Q4QQ5@Q2D5A>00Oy[[Q2xQ2y'100U{Q22Q5@Q5=50>S2yP>Q5@Q5<H0?S2>P{Q2>P{Q2>P{Ew[Q2>/_{P>Q5AQ5>Q5AQ5=50>CvS2>/9{S11Q11;D{\HQ2>/a{Q25P>Q5BQ5@Q5BQ5>50>CvS2>/9{S11Q115b{[Q2>/d{P>Q5CQ5AQ5CQ5@50>CvS2>/n{\|Q2>/c{P>p+03MS2>Q5BQ2>Q5A50>CvS11Q117`{\|Q11/8{P1p+03NS11Q5C50>Q11Q5B50><2K{P1p+03OS4~Q2>'E>0j>{Q22p+03PS66Q1150>S2uP{Q2uP{Q2uP{Ew[Q2u/_{p+03QS2uQ4~50>S68/9{S69Q69;D{\HQ68/a{Q25Q5EQ6650>S68/9{S69Q695b{[Q68/d{p+03SS68Q2u50>S69/n{\|Q69/c{Q5FQ5F7`{\|Q5F/8{P1Q5IQ6850>S5F/9{P1Q5GQ68'E>0j>{Q22Q5HQ5D50>S69P{Q69P{Q69P{Ew[Q69/_{Q5JQ5I50>S69/9{S6:Q6:;D{\HQ69/a{Q25Q5MQ5G50>S6:/9{S6;Q6;5b{[Q6:/d{Q5LQ5H50>S6;/n{\|Q6;/c{Q5NQ5J50>S6;Q6;7`{\|Q6;/8{S6;P1Q5OQ5M50>S6</9{P1p+03]S6=Q2=+0A>0j>yQ52Q5PPyQ5PPyQ5PPyEw[Q5P/_yQ54Q5R/9yS5PQ5P;Dy[Q5R/ayQ56Q5dQ3?5A>S5R/9yS5PQ5P5by[Q5R/dyQ51Q5gQ3Y5A>S5R/ny[Q5R/cyQ51Q5cQ3X5A>S5RQ5R7`y[Q5R/8yP1Q5f/9yP1p+03dS5fQ3\5G>S5R00UyQ52p+03eS5PQ3]5G>S6>PyQ6>PyQ6>PyEw[Q6>/_yQ54p+03fS6>Q3[5G>S6?/9yS6@Q6@;Dy[Q6?/ayQ56p+03gS6?Q3^5G>S6@/9yS6AQ6A5by[Q6@/dyQ51p+03hS6@Q3_5G>S6A/ny[Q6A/cyQ51p+03iS6BQ3a5G>S6CQ6C7`y[Q6C/8yP1p+03jS6CQ3c+1S>0c>yP1P7%2l16lgQ0u11xkS6D'6Q0tQ0v#2Q0w/6gP7Q0z#2Q0zQ0G'6Q0Q,1xS6E,6pPpQ13#2Q15/6TP7p+043S15p+041S6F50>Rp#216pgQ1311xtS6G'6Q1:p+045S6HQ1561]>p+046S6Ip+044S6J'E>0G>gP7p+047S6KQ6IQ6J<0BS50>Rp#216pgQ1711xZS6L'6Q1Ap+049S6Mp+048S6N#3Q6IPSH0u-1~>p+04:S6OQ6M#3Q6KPSH0u>0G>gP7p+04;S6PQ3r5A>Rp#216pgQ1=Q0],1xS6Q'6Q2Lp+04=S6RQ3z+0A-1~>p+04>S6SQ3u+0A>0G>gPjP?O1S3u%2m\zS6TPjP;O1S6UQ4Q%2hS6V[S6WQ5UQ2XQ5T$0>S5T+10S6XQ2TQ2XQ2~+10S2~Q2VQ2WQ3EQ2YQ1M+0qS6YQ2Z41RI1qQ1SH0WQ1UQ4dP_P9P;P9P_P9P_Q1zI0RP5Q2^P_Q30P_Q1y9h9_S4dP3Q2_P_Q2`P_Q5]I0RK04K04Q1WPqPqQ2bPGPqPqPiQ1v#ORpQ5^I0KPGPqPqQ2ePGPqQ2hQ2aQ3w+1oS1vPpH0<PGPqPqQ2bPGPqPqPiQ1u#K#ORp20QqQS1uI0KPGPqPqQ2ePGPqQ2gQ2aQ1X#{#OS3E+1oS6ZPpH0<PGPqPqQ2bPGPq20QqPS6[PqQ2k#{#OS2kQ2a+0LH1FPGPqPqQ2ePGPqQ2iQ2jQ2kH0<PGPqPq20QqOS6\Q5`Q3w'F9[qwS6]PGPqPqQ5`Q1pQ3EH0<S6^PGPqQ2pPGPqQ37PGPqQ2qPGQ189[qwK0:S2qK0:EoFNFNFNFNFNFNQ1`Q1bb;b<b=X11X31X41X51X91X?1X@1XE1XK1XN1XO1XV1X>~XD~XJ~Z0K~%2_Rp/CN\HQ2s20e{0S37=kAN[Q1D/CP\HS2pQ2s20e{_S6_=k0e[Q0G16e{S6`'C\HQ2s11K?S6aQ37;kQ[11N_9rR8Ake0QS6bQ3B%]NS6c11_NS6d,6M[[S6e\p[[[[[[[[^11^31^41^51^91^?1^@1^E1^K1^N1^O1^V1^>~^D~^J~`0K~P:Q1sQ1i'4Q0e#2S6fQ0^/6{S6gQ0U/6{S6hQ0UQ0^Q0ePuQ1sPtp+04BS6iQ3y5G>Q6ip+04@S6j50>Q6ip+04?S6k50>S6lQ0cPxQ1iPZPmQ0bQ0aPjQ0hQ13Q1mP_Q3\Q3}OKb8b6b7Y0UY0TP5P:O2n2001000000121000000Y0SY0RP5P:O2n2001000000121000000Y0EY0DP5P:O2n2001000000121000000Y0CY0BP5P:O2n2001000000121000000Y0AY0;P5P:O2n2001000000121000000c0Qc0Pc0:c09c08c07b~c0?c0>b}bubtbsbrb{bzbqbbbab`bjbpbnbibhbgbfbebobmbdbcb_bZb2b6b7bAbBbPbQbRbSc0LbFO3b2H2643w42UO3b21;>?RpP0DmQ4y,TcS5{>01x{PpPpPxQ5{Q4x,Tc<2j{I2DQ4{Q0I'TS5{>01x{PBPBPxQ5{Q4{Q4|'T<2j{I2DX0XQ4z#|S5{61KXS5|+0YeQ4yQ4x+2=S6m$03,TcS6n>01x{PpPpPxQ6nQ6m#R,Tc<2j{I2DQ5|+0YeQ6m-2FcQ6m:2qpc81ypQ4{02F:Q4{>2qB:81yBX0XS6mQ5{61KX+0YeQ6mQ28#|61KX#7eQ28>2Tcp#7S6meQ6m1;>MS6m-2WEQ09Q6m'SS5{'uS5|Q4}Q2<Q6m42^/u:$1k+0YXCCQ5|&1k:S6n+0YXCCQ3UQ1aQ32Q06'uQ32$37H1mQ4{Q2:<2^BS3UQ06'uQ3U$37H1mQ4{Q2:<2TBP:H1mQ32Q5x$1k+0Yec1Y22WEpQ09/Sp'uQ5yQ06$0FS06Q28>1zcp'u'=+0Ye&1e?Q5m+2iP;H1mQ5l-0hpP3H1YQ5k$1@-0hpP4H1mQ4B#7eO2b2Q4zQ26Q4iP0H2X$0F$1k#BeQ0XP:H1YQ4zQ26Q4iP0H1g#BRpePpQ4{PcQ4oPKH2XS0X$0F-0Y:XCCP7Q3NQ3QQ3MQ5t#7[Q3SP:n2001000000120000000XCCQ3Q^CCP:Q0XQ5|Q6mQ4r#z+17$0F&1eMQ4r+3:$0FQ4}Q4{Q6m41zS3Q'uRp5x:+1bXCCQ5|Q5z/=p+1bXCCQ5|Q5yQ0yQ3Q'u'=+1bXCCQ0J&3uES5|1e:6815:X:1P722h5:Q3RQ3M+18Rp[Q3MQ3O+1822h;5[S3Q22h3;\p23t5:P:n2001000000120000000X^CX]CS0yQ3Q^^C^]CS3QP:Q5|/S\S5|1e\6RpQ5|#B%BpP7Q5?#B145;Rp[14:5S5?Q65#B[S65Q67#B\p23s5:P:n2001000000120000000X|1XG1S67Q65^|1^G1S65P:PUP6Q50Q4>Q4;3<S5|#IQ0NQ5|'@S5|eS5zQ5|Q4EQ1CQ4DQ1FQ1BQ1EQ1HQ1JQ1SQ1UQ1oQ1WPqQ1p9LqwS3SPGQ3SH2?Q1`Q1bb;b<b=X11X31Q5?Pp[^11^31P:Q0NP6PVO3b8b6b7bAbBbFO3b242SO3b2PBP?DmQ3P#BR6eP6P7Q0{#B165;R6[16:5RpQ10#B[S10Q0}#B\623r5:P:n2001000000120000000X|1XG1S0}Q10^|1^G1S10P:Q091;>_S0{PU&1f:X:1Q5zQ5|Q4EQ1CQ4DQ1FQ1BQ1EQ1HQ1JQ1SQ1UQ1oQ1WPqQ1p9[qwS5|PGQ5|H2?Q1`Q1bb;b<b=X11X31P6\p^11^31P:Q09Q0NPbO3b8b6b7bAbBbFQ0{PMDmO3b2Q5{#BQ091;>NS5{'S,u:Q53Q50Q5{41zS5z$1kRp+1bXCCQ6n01bpXCCP7Q61#BQ3RQ3M'CRp[Q3MQ3O'CQ5:#B[R6Q63#B\p23q5:P:n2001000000120000000X^CX]CP6^^C^]CP:Q53Q50Q5{42^Q53Q50Q5{42TQ53#|S63:07X:S5:P@P2P1PCPYQ59#3R6P5P:P[C>S3MP6Q4lQ4iQ57P5P:P[F:P6Q4OQ42Q57=X6SP5P:P[F:S3R3xn200110300012010x10yX0XR6Q55#|S6160]XQ58#|:07X:P@P2P1PCPYQ5=#3S6nP5P:P[Q6nQ4uQ4rQ5;P5P:P[F:Q6nQ4LQ4NQ6nQ5;;XSS3PP5P:P[F:J1=n200110300012010x10yX0XP5O1#7[^GX[Q57#|Rp:07X:P@P2P1PCPYQ5<#3S5?P5P:P[Q5?Q4rQ4oQ59P5P:P[F:Q5?Q4NQ4PQ5?Q59;XSS3SP5P:P[F:J1=n200110300012010x10yX0XP5O1#7[^GXP@P2P1PCPYQ5;#3S5tP5P:P[Q5tQ4oQ4lQ58P5P:P[F:Q5tQ4PQ4OQ5tQ58;XSS3NP5P:P[F:J1=n200110300012010x10yX0X>0]Xp[Q61:36X6Q0^P5P:J2pP6P5O1#7&03;$2QS4BPLQ0F&033>0SL:S5kP@P2P1&03A>0SL:S5lP@P2P1PCP5Q5>#3S5mP5P:%R0S5xQ5mQ4wQ4uQ5<P5P:Q5xF:Q5mQ4TQ4LQ5mQ5<;XSS3UP5P:Q5xF:J1=n200110300012010x10y#7Q5>&034S6o'TR61;>RRpPpP6Q5>%R4S6pH0TQ5>P4PpPpQ5>P4J1_H1L]U]wP5&030Q0L60SLS0LQ5@#3RpP;P5%R?S6qPpQ4xQ4wQ5=P;P5Q6qF:I1XPpQ4YQ4TQ5==XpSS5=P;P5Q6qF:+0kQ5A#3S6rP3P;%RKS6sQ6rQ4yQ4xQ5>P3P;Q6sF:I1XRpQ6rQ4[Q4YQ6rQ5>;XSP3P;Q6sF:R6<0b:20ap6P7Q5B#3S5>P<P3%RMS6tC>Q5>Q4zQ4yQ5@P<P3Q6tF:+0kQ5>Q4`Q4[Q5>Q5@;XSS5@P<P3Q6tF:#7Q2>&03_S6u'TR61;>\RpPpP6Q2>%R_S6vH0TQ2>P_PpPpQ2>P_J1_H1LP:Q2>#3RpP8PA%RNS6wC>PpQ4{PcQ5BP8PAQ6wF:+0kQ11#3RpQ4iQ4bQ5C=XpSP4P8%ReS6xF:#7Q4~#3RpP0P4%RQS6yC>R6PpQ50Q4}Q2>P0P4Q6yF:Rp<0b520a6pP7Q66#3RpP?P0%RPS6zC>#7PpQ53Q50Q11P?P0Q6zF:#7Q5E&03OS6{'TRp1;>^R6P6PpQ5E%ROS6|H0TQ5EPOP6P6Q5EPOJ1_H1LP:Q5E#3PMPKQ0M#RC>#7Q68#3Q58Q57Q2uP_PMQ0G#RS6}F:#7Q5IQ5IQ5DQ2>Q11ClQ5D#3S6~PNP_%RVS70Q3_P5L2oQ5I1MN_S71'pR6Q5IQ7050>Rp,16@1Egp+19P7Q5G?<eNRp#2Q5G%RRS7250>R6,1p@1Eg6Q5H&03T'TR61;>aRpPpP6Q5H%RTS73H0TQ5HPTPpPpQ5HPTJ1_H1LP:Q5J?<PQ#2Q5M1MOPS74Q5M>13>bRp420@1EgpP7Q5LQ0M/MOS75'pQ5LQ0J#RS7650>Rp;?g%]pQ5N&03\'TRp1;>sS77Q77PpQ5N%R\H0TQ5NP\Q77Q77Q5NP\J1_H1LP:Q5OQ0G,MVS78'pQ5O%RUS7950>;?gQ6=%RdS7:50>#]Q2?&03hS7;PTPRPVQ2?Q57Q553<Rp#IQ0o/@pS7<eS7=Q7<Q4EQ1CQ4DQ1FQ1BQ1EQ1HQ1JQ1TQ1UP9P;P9P;Q1VP;P9I0RP5P9D~Q1WPqPqQ2f#K#ORp-0LiPGPqPqPwPpQ1[PGQ1_K0sI1cQ1`Q1bb;b<b=X11X31S1_Q1gP:Q5fQ0T613>S2fQ5f?<dUR6P8P4PMO5b8b6b7bAbBbFJ30Q2?Q7;50>Q2?1MTRS7;'p'@PDQ5QQ5QQ2?Q5HQ5JClQ2?#3Q11Q2>Q5OP]PT%RkS1TQ0PPKN<2gQ5QQ11Q2>3<S7>Q5QQ5O41lQ5Q1M]TS7?'pS7@Q7@Q5QQ1TQ7>H0{41GPDQ5dQ5dQ5QQ5JQ5MClQ5Q#3S7>Q59Q58Q7>Q6=;XSS7>PbP]%R^S7@Q3kPPN<2gQ5dQ59Q58'MS7A'pS7BQ5dQ7>41lQ5d1Mb]S7>'pS7CQ7CQ5dQ7@Q7BH0{41GQ5gQ0J/MbS7B'pS5dP:Q0_,;>S7CQ7CQ5cQ0N613>S7D,1:S7E'e18:{Q7C62>xQ7CPxQ7E/8{H35H1LX:1P`Q5cQ0J7<\S7EP:Q7EQ7D'1S7D,e:Q7E/8{>2>x:P:PxQ7D/8{H35H1LX:1Q5gQ66Q4~3<Q5cQ5Q50>S7C,1:Q7EQ7D/4:41GX:1P5Q5gQ5Q50>S7EQ3aDmQ7EQ5gQ2?50>S7D'1Q5dQ5dQ5gQ0R#RS7F50>Q7E3?41GQ0uQ5cQ5gQ5QPSH05Q7C/8{'@Q5eQ0t/1:Q2f,16S2fQ0t'481G6X:1P;Q5h/8{S5hP:I0^Q0sQ5h'1Q5b?<U\S5eQ5eQ5bQ0Q613>Q0s3?41GQ0oQ0oQ2f'e6156186{Q0o62>xQ0oPxQ2f/8{H35Q0yQ3QP:Q5P?<hdS2fQ0p'SQ0pQ2fP>Q5PPaH1IS5e'eQ03Q5PQ5c50>S7C/8{Q2f5?lQ5e/4lQ6>?<khS5Q/So#BQ5QP>Q6>Q0UH1IS5d,eo#B+18P5Q0uQ6>Q5b50>S7E/8{Q5Q3?Q6??<^kS7GQ0q'S#BS7HQ0qQ7GP>Q6?PtH1IS7I'e#BS7JQ0}Q10P:Q6@Q0R;<^S7KQ0rQ6@Q5CQ5B3<R6#IQ0w/@6S5BeS7LQ5BQ4EQ1CQ4DQ1Fp+03kS7MQ6@50>R6/Y{S7N%26P>p+03mS7OQ6CP{H1[\z[S6Cp+03lS7PQ3e5G>R600EyS7Q%26Q4Qp+03nS7RQ3h5G>00Oy[[S7SQ1BQ1EQ1HQ1Jp+03oS7TQ7O50>R6/Y{S7U%26P>Q6FQ7TP{H1[\z[S7Vp+040S7WQ3f5A>R600EyS7X%26Q4Qp+042R6Q0P5A>S7Y00Oy[[S7ZQ2WQ2UQ1PQ1SH0WS7[Q1UQ2^P0Q2\P0Q2_D~P;Q2]Q5}7h0P5P9P0Q4AK2HQ1WPqPqQ5`/FpS5}Q1pPGPqPqQ2nQ5}9[qwPGPqPqQ339LqiS5}Q31PGPqPqQ1X#OS1X9LqiQ35PGPqQ1x9[qiS35PGPqQ1ZPGQ5|K0:EoEoEoEVQ1`Q1bb;b<b=X11X31X41X51X91X?1X@1XE1X>~XD~XJ~S5|A?48511049r?5Q2c/CM%24S31/CNQ3>%]41684[[[[[[^11^31^41^51^91^?1^@1^E1^>~^D~^J~S3>P:Q7Y/6gS7\Q7W90>6S7]/6gS7^Q17Q0z'4Q17Q7T90>6S7_/8{S7`Q0P9G>6S7aQ7YQ7]Q7_A<6ZnS7bQ0zPMQ0oPfQ2:Q2QQ3rOAb8b6b7bAbBbPbQbRbSbFO3b242UWYP:O1Q5dQ0u'4Q7HQ7JQ67Q65P:Q0rQ7KP>Q6@PWH1IS7cQ7LQ5BQ4EQ1CQ4DQ1FQ7NQ6CQ7QQ7SQ1BQ1EQ1HQ1JQ7UQ7VQ7XQ7ZQ7[Q1UQ2]P0P9P;P9P5Q2`P0Q2\P0Q2^P3Q5~K04K04Q1WPqPqQ1qQ3EPGPqPqQ3EQ0H5LqQ2nPGQ64EoEVQ1`Q1bb;b<b=X11X31X41X51X91X?1X@1XE1X>~XD~XJ~S64Q4Z/44A}03?Q4W[[^11^31^41^51^91^?1^@1^E1^>~^D~^J~S4WP:Q7\Q7^Q0zQ17Q7`42VQ17Q7aQ7YQ7]Q7_Q0zQ0b:13>6S7_Q7bPMQ0oPfQ2:Q2QQ3rOAb8b6b7bAbBbPbQbRbSbFO3b242SWYP:O1n200100000021100011000O3b2Q0yQ3QP:Q2f/8{Q0p62>xQ0pQ5e/8{82RxQ03Q5PQ5b50>RfQ7CQ2f3?Q5e/4fQ5Q/8{>2>xo#BQ5d/8{:2Rox#B+18P3Q6>Q5f50>S5fQ7EQ5Q3?Q7G/8{Q0q62>x#BS7GQ0qQ7I/8{82Rx#BS7IQ0}Q10P:Q7K>01x{Q0rQ7LQ5BQ4EQ1CQ4DQ1FQ7NQ6CQ7QQ7SQ1BQ1EQ1HQ1JQ7T?<Wt@4w{TQ7W?<sW00X{\zQ7WQ7R50>Ro/Y{S7W%2oQ7]00X{\z[S7]Q6FQ3j5A>Ro00EyS6F%2oQ4QQ15Q3k5A>00Oy[[S7SQ7b00U{Q22Q15?<mZRoP{PoP{PoP{Ew[1_o{Q6JQ0^;<mS7Q/9{R6?D6{\HQ7Q/a{Q25Q6HQ0^7<uS6C/9{R6=b{6[Q6C/d{Q6IQ0];<uS7N/n{\|Q7N/c{Q6KQ0_Q0]3<S7KQ7K7`{\|Q7K/8{P1Q6NQ0`Q0_3<S7E/9{P1Q6MQ6K'E>0j>{S5QQ22Q6OQ6N50>R6P{P6P{P6P{Ew[S5e1_6{S7CQ6PQ6M50>S6M/9{R6?D6{\HS2fQ6M/a{S6MQ25p+04<S5bQ6O50>S6O/9{R6=b{6[S0pQ6O/d{S6OQ6RQ6P50>R6/n{\|S6P1c6{S7JQ6SQ5b50>R6?`{6\|S5b186{S7HP1Q6kQ6R'E>0c>{S6kP1Q6jQ6R'E>0j>{S6RQ22p+04AS0oQ6S50>R6P{P6P{P6P{Ew[S6S1_6{S7YQ6l/9{R6?D6{\HS7aQ6l/a{S6lQ25p+04CS7`Q6j50>S6j/9{R6=b{6[S7^Q6j/d{S6jp+04DQ0o50>R6/n{\|S0o1c6{S7\p+04EQ6i50>R6?`{6\|S6i186{S4ZP1p+04FQ7`'E>0c>{S7`P1p+04GQ4:+0A>0j>yS2nQ52p+04HQ4;5A>R6PyP6PyP6PyEw[S5~1_6yS7[Q54p+04IQ4>5A>S7Z/9yR6?D6y[S7XQ7Z/ayS7ZQ56p+04JQ4=5A>S7V/9yR6=by6[S7UQ7V/dyS7VQ51p+04KQ3}5A>R6/ny[S7d1c6yS7eQ51p+04LQ455A>R6?`y6[S7f186yS7gP1p+04MQ4G+0A>0c>yS7hP1p+04NQ42+1S>0j>yS7iQ52p+04OQ4O5G>R6PyP6PyP6PyEw[S7j1_6yS7kQ54p+04PQ4P5G>S7l/9yR6?D6y[S7mQ7l/ayS7lQ56p+04QQ4N5G>S7n/9yR6=by6[S7oQ7n/dyS7nQ51p+04RQ4L5G>R6/ny[S7p1c6yS7qQ51p+04SQ4T5G>R6?`y6[S7r186yS7sP1p+04TQ4Y+1S>0c>yS7tP1P7Q2B#2S7uQ2B/6gS2BQ2DQ6D'6Q2@Q2F#2S7vQ2H/6gS2HP7Q2M#2S7wQ2MQ0G'6S7xQ2LQ6E'6Q2LQ2O#2S7yQ2R/6TS7zP7p+04]S7{p+04[50>R6#2S7|166gS7}Q2OQ6G'6Q2|p+04_Q7{61]>S7{p+04`R6p+04^S7~'E>0G>gS80P7p+04aS81Q7~>0B6S50>S7~#2S82Q7~/6gS7~Q2}Q6L'6Q2=p+04cS83p+04b#3P6PSH0u-1~>S84p+04dQ83#3Q81PSH0u>0G>gS81P7p+04eQ505A>R6#2S83166gS85Q2CQ6Q'6Q3mp+04gQ55+0A-1~>S86p+04hQ57+0A>0G>gS87Q3uQ6TQ6UQ6WQ5UQ6XQ2TQ2~Q2VQ2WQ2UQ6YQ5\Q2Z'q41RI1qQ1SH0WQ1UQ1zPNP9P<Q2\PNQ1y9h9NK04P;&0HNS5\PNP9PNP9PNP9K04P5Q5]?h89S6XPNQ30PNP9P3Q2_PNQ2`PNP9I0RK04D~Q1WPqPqQ2bPGPqPqPiQ36#K#OR6Q1uI0KPGPqPqQ2ePGPqQ2hQ1vP6H0<PGPqPqQ2bPGPqPqPiQ0@#{#OS0@Q6[I0KPGPqPqQ2ePGPqQ2gQ6ZQ0@434I4vS6ZPGPqPqQ2bPGPqQ6\Q0A#OS0AQ2a5[qJ33PGPqPqQ2ePGPqQ5_Q2jQ0AH0<PGPqPqQ2iQ5_PGPqPqQ0M-0QqS2iQ6]PGPqQ6^PGQ2qH2?EoEVFNK0:FNFNFNQ1`Q1bb;b<b=X11X31X41X51X91X?1X@1XE1XK1XN1XO1XV1Z0M1X>~XD~XJ~Z0K~Q1D/Ce\HQ2sQ37=kAe[%2eS1D/CO\HQ2sQ6_=k0Q[ArVQ{\HQ2sQ37=kQP[Q6a/4Q11eN9r]4AkQ?PQ6e[[[[[[[[[^11^31^41^51^91^?1^@1^E1^K1^N1^O1^V1`0M1^>~^D~^J~`0K~P:Q3]Q0B'4Q6fQ6gQ6hQ0UQ0^Q0ep+04lR6Q1sQ1n3<S6hPuQ3]PtQ5<9G>6S6gp+04j90>6S6fp+04i90>6S6eQ0cPxQ0BPZPmQ0bQ0aPjQ0hQ0sQ2OQ3ZQ42Q4~OLb8b6b7Y0UY0TP5P:O2n2001000000121000000Y0SY0RP5P:O2n2001000000121000000Y0EY0DP5P:O2n2001000000121000000Y0CY0BP5P:O2n2001000000121000000Y0AY0;P5P:O2n2001000000121000000c0Qc0Pc0:c09c08c07b~c0?c0>b}bubtbsbrb{bzbqbbbab`bjbpbnbibhbgbfbebobmbdbcb_bZb2b6b7bAbBbPbQbRbSc0LbFO3b242UY0@P:O1Q5dQ5f'4Q7GQ7IQ67Q65P:Q0rQ7c>01x{Q7LQ5BQ6BQ0NQ0R'MQ6B>13>s420Rm/Y{%2mQ7MQ0TQ0Q'MS5BQ7M%RZS7L50>42000X{\z[Q4EQ1CQ4DQ1FQ7PQ6B50>Rm/Y{%2mP>Q7RQ7MP{H1[\z[Q7OQ3d5G>Rm00Ey%2mQ4QQ7TQ2P5G>00Oy[[Q1BQ1EQ1HQ1JQ7WQ7]Q6FQ7SQ7bQ7_'100U{Q22PoP>Q15Q0aH1IRoP{PoP{PoP{Ew[1_o{Q7QP>Q6JQ0eH1IRo/9{Rm?Dm{\H1ao{Q25Q6CP>Q6HQ0cH1IRo/9{Rm=b{m[1do{Q7NP>Q6IQ0dH1IRo/n{\|1co{Q7KP>Q6KQ0gH1IRo?`{o\|18o{P1Q7EQ6NQ0f613><2K{P1Q5QQ5eQ7CQ2fQ6MQ0pQ6OQ6PQ7JQ5bQ7HP1Q6kP1Q6RQ6SQ7YQ7aQ6lQ7^Q6jQ0oQ7\Q6iQ4ZP1Q7`P1Q2nQ5~Q7[Q7XQ7ZQ7UQ7VQ7dQ7eQ7fQ7gP1Q7hP1Q7iQ7jQ7kQ7mQ7lQ7oQ7nQ7pQ7qQ7rQ7sP1Q7tP1P7Q7uQ2BQ6DQ2D'4Q2@Q7vQ2HP7Q7wQ7xQ6EQ2L'4Q2LQ7yQ7zP7Q7|Q7}Q6GQ2O'4Q2|Q7{Q80P7Q82Q7~Q6LQ2}'4Q2=Q84Q81P7Q83Q85Q6QQ2C'4Q3mQ86Q87Q3uQ6TQ6UQ6WQ5UQ5TQ2TQ2~Q2VQ6YQ0?$3U-3T1S0?Q1N+10Q2Z'qI1qQ1SH0WQ1UQ1zP_P9P<Q2`P_Q309h9_K04P;P9P5Q6XP_Q2\P_Q4dP3Q2_?h_9K04D~Q1WPqPqQ2bPGPqQ5^PqQ0@Q2a+0LH1FPGPqQ6ZPGPqPqQ2bPGPqQ0A9LqiQ1uJ33PGPqPqQ2ePGPqQ5_Q2k'FRoQ2oQ0AH0<PGPqPqPoQ2gPGPqPqQ2k-0LiPGPqPqPiQ5_PGPqPqQ62Q6[PGPqPqQ5`Q3E834wPGQ3DI1cEoEVI1cEVFNK0:FNQ1`Q1bb;b<b=X11X31X41X51X91X?1X@1XE1XK1XN1XO1XV1X>~XD~XJ~ArN_{\HQ2s20e{?=k8N[Q2pQ2sQ6dQ2w;ke[Q6d/40Q3BQ1DA}N?RQ6bQ3BQ6cA?M_N[[[[[[[[[[[^11^31^41^51^91^?1^@1^E1^K1^N1^O1^V1^>~^D~^J~P:Q0BQ3]<2VtQ0e/6{Q0^#2Q0^Q0eQ26:13>6Q6hPuQ3]Q6gQ6fQ6eQ0BQ0cPxQ0bQ0aPjQ0hQ0sQ0zQ16Q2OQ3ZQ42Q4~OJb8b6b7Y0UY0TP5P:O2n2001000000121000000Y0SY0RP5P:O2n2001000000121000000Y0EY0DP5P:O2n2001000000121000000Y0CY0BP5P:O2n2001000000121000000Y0AY0;P5P:O2n2001000000121000000c0Qc0Pc0:c09c08c07b~c0?c0>b}bubtbsbrb{bzbqbbbab`bjbpbnbibhbgbfbebobmbdbcb_bZb2b6b7bAbBbPbQbRbSc0LbFO3b242SY0@P:O1n200100000021100011000O3b2H26bYc0lc0@Q0],;>R6PuDmQ5gQ0R$03Ro50>P;DmQ5g/ToRoP6P6PoQ5gQ7FH0TQ5gQ0RP6P6Q5gQ0RJ1_H1LebYc0@c0nY0cY0bP5P:O2n2001000000121000000W2Y0aP5P:O2n2001000000121000000c0^Y1IY0hP5P:O2n2001000000121000000bUY0dWUP5P:O2n2001000000121000000bUWUWwZ0y1Z0x2P5P:O2n2001100000121106101P:P;O2bwc0wbUY0HX0XQ5:Q57&035R6'TRo1;>QRmPmPoQ57%R5S5gH0TQ57P5PmPmQ57P5J1_H1L[^0XQ57Q0I'TRoPmPmPoQ57Q4|'TI2DX0XRoQ6361KX#BQ5702F:Q57>2qm:81ymX0XS5:Q6361KX#BPXPoQ63Q61:07X:S61Q58/T6R61;>PRoPoP6Q58Q5gH0T415R6Q58P5PoPoQ58P5J1_RoP;P5P:O2Rm44uY0HX0XH32PXQ5:Q63Q61B4t6omY0HX0XH32H26Q55Q531;>eRm42^Q55Q53<2Tm#B+1Oec0\O3b2Q50Q4}Q0{41zRm#BRoePoQ3OXCCQ4HQ5zP:H1Yc1XQ08Q08'u&1km+1beQ09Q0{'SP:H1YQ0{-2WEP5H1YbHc1PQ32Q5yQ06Q4{@1zcB'u'=+1beQ5wP3H1mQ5vP<H1YQ5u$1@-0hBP0H1mQ0X#BeO2b2PcQ4zQ4lP?H2X$0F$1k#7eQ5pP5H1YPcQ4zQ4lP?H1g#7RmePmPXQ4}Q0I'TRmQ6mQ6mPmQ4}Q4|'TI2DX0X%QcQ4{#Q:07X:P@P2P1PCPYQ55#3RmP5P:P[PmQ45Q3}Q50=XmSS4|P5P:P[F:I1Xn200110300012010x10yX0XRmQ4}#QS6m60]XQ53#Q:07X:P@P2P1PCPYQ3MQ3R'=n200110300012010x10yX0XP5O1#7[^GX[Q50#QRo:07X:P@P2P1PCPYQ58#3R6P5P:P[P6Q42Q4GQ55=X6SS58P5P:P[F:I1Xn200110300012010x10yX0XP5O1#7[^GXP@P2P1PCPYQ57#3RYP5P:P[PYQ4GQ45Q53=XYSP5P:P[F:I1Xn200110300012010x10yX0X>0]Xo[Q6m:36XmPsP5P:J2pPmP5O1#7Q4BPLQ0FQ5kP@P2P1Q5lP@P2P1PCP5Q5tP5P:Q5xQ5tQ4PQ4OQ3NP5P:Q5xF:I1Xn200110300012010x10y#7Q5;Q6o'TR@Q0M,;>RmPmP@Q5;Q6pH0T415]U]wP5Q0LQ5?P;P5Q6qC>Q5?Q4NQ4PQ3SP;P5Q6qF:+0kQ6nP3P;Q6sC>R@Q6nQ4LQ4NQ3PP3P;Q6sF:Rm<0b:20a@mP7Q5mP<P3Q6tC>#7Q5mQ4TQ4LQ3UP<P3Q6tF:#7Q5AQ6u'TRm1;>]R@P@PmQ5AQ6vH0T415P:Q6rP8PAQ6wC>#7Q5>Q4`Q4[Q5@P4P8Q6xF:#7Q2>Q2>Q5CQ5;Q5<ClQ5C#3S5<P0P4Q6yQ3?P5L2oQ2>?<04RmQ2>Q6y50>R@,1m@1Eg@+19P7Q11?<?0R@#2Q11Q6z50>Rm,1@@1EgmQ4~Q6{'TRm1;>dR@P@PmQ4~Q6|H0T415P:Q66?<MK#2Q2u1M_MQ2uQ6}50>Rm420@1EgmP7Q5EQ71'pQ5EQ7050>Rm;?g%]mQ68&03R'TRmQ0R,;>R@P@PmQ68Q72H0T415P:Q5D?<QeQ5DQ7350>;?gQ5I>13>]#]Q5G&03bRmPOPPPQQ5GQ4yQ4x3<R@#I1@j@R@eP@Q4EQ1CQ4DQ1FQ1BQ1EQ1HQ1JQ1_Q1gP:Q5OQ1T50>R@Q5OQ7?'pRsP8P4PMO5b8b6b7bAbBbFJ30Q5G=0>mQ5GQ74'p'@PDQ5HQ5HQ5GQ4~Q66ClQ5G#3RmQ4zQ4yQ5D=XmSRmQ0MPOQ76Q3cPKN<2gQ5HQ4zQ4y3<RoQ5H<1lmQ5HQ75'pRmPmQ5HQ76PoH0{41GQ0mQ5JQ5K+0NQ69/8{'@Q5MQ5JQ5G<0BS50>Q0l/1:Q5L?<RVRoQ5LQ7:50>Q0l5?o41GX:1P5Q6:/8{RmP:I0^Q0k/1mQ5MQ78'pRmQ5MQ7950>Q0k5?m41GPoQ77Q77Q5N>13>hRo82R:615:X:1Q0gQ5NQ7;'pRm11moRo,e:815:X:1Q0yQ3QP:Q0f,SmQ0f/eoQ03Q6;=?`m14o`1Ssj#B11s@R@,ej#B+18P5Q0mQ6</8{;?sQ6=Q7>'pRsQ0h'S#BRoQ0hQ6=Q7@50>82Rs#BRsQ0}Q10P:Q2?Q7B'pS7BQ0iQ7=Q7<Q4EQ1CQ4DQ1FQ7D/Y{S10Q7D#2Q5h#2\z[S5hQ5cQ3X5G>R`00EyS5c%2`Q4QQ5R00Oy[[S5RQ1BQ1EQ1HQ1J1Yf{S7D%2fP>Q6?Q5PP{H1[\z[S6?Q6>Q3[5A>Rf00EyS0}%2fQ4QQ6@Q3_5A>Rf00Oy[[S7@Q5|Q3>P:16fgS3>Q6@Q6>50>R`/6gRmQ0wQ0r'4Q0wQ6@Q5P50>R[/8{RYQ6APfP`P[Q6@Q5B'pR6Q0rPMQ0gQ0xQ1nQ2FQ3jOAb8b6b7bAbBbPbQbRbSbFO3b242UWYP:O1Q0m,4@Q67Q65P:Q0iQ7BP>Q2?Q7FH0?Q7=Q7<Q4EQ1CQ4DQ1FQ10Q5hQ5cQ5RQ1BQ1EQ1HQ1JQ7DQ6?Q0}Q7@Q64Q4WP:Q3>PmQ0rQ0w<2VYQ0wQ6APfP`P[Q0rQ6@Q7L50>P6PMQ0gQ0xQ1nQ2FQ3jOAb8b6b7bAbBbPbQbRbSbFO3b2:2SosWYP:O1n200100000021100011000O3b21;>WRsPtDmQ5L&03dRo50>P3DmQ5L/ToRoPsPoQ5LQ7:H0T815sebYc0lbYc0nY0cY0bP5P:O2n2001000000121000000W2Y0aP5P:O2n2001000000121000000c0^Y0dY0hP5P:O2n2001000000121000000bUWUWwZ0y1Z0x2P5P:O2n2001100000121106101P:P;O2bwc0wbUY0HX0XH32Q4{@31cB#BRBePBPCPFP:Q0D$28RBQ4wP_O1n0100000020000Q0C55FXCCQ4}Q4{Q4wQ4uQ4rQ4lPMP5P?PAP<P:N<4sQ4}Q2<Q4rPMH1gP;H1YQ4}Q2<Q4rQ4uPMI1:Q0C55Fec1Oc1Qc1[c1JY1RY1VP5P:O2n2001000000121000000c0^c1Sc1dbMY1jY1iP5P:O2n2001000000121000000W2Y1hP5P:O2n2001000000121000000W2Y1gP5P:O2n2001000000121000000c1kc1]b:c0YY0YZ0N1Q43Q4;Q14Q3~Q4CB0\><5I1:Q0C55F[`0N1P>Q4:Q3xP{H1URXQ4c16<gQ1^11<:<2\g40xX:1Q4:Q3bQ3c'MRs'pRo#I1@3oR6eP6Q4EQ1CQ4DQ1FQ3`/Y{Q3`#2Q2v#2\z[Q5j00EyQ5j#2Q4QQ4GQ135G>00Oy[[Q1BQ1EQ1HQ1JQ48/Y{Q48#2Q4R#2\z[Q2z00EyQ2z#2Q4QQ4NQ175A>00Oy[[Q1900U{Q22Q1IP{Q1IP{Q1IP{Ew[Q1I/_{Q4LQ4O50>R6/9{R[?D[{\H1a6{Q25Q4U/9{R6=b{6[Q4U/d{Q5i$2N\|Q4V/c{Q4[Q4L50>R6?`{6\|186{P1Q4`Q4T'E>0c>{P1Q4^Q4gQ4hQ4kQ4jQ4nQ4mQ4pQ4qQ4sQ4tP1Q4vP1Q4wQ1j+0A>0j>yQ52Q4xQ1m5A>R6PyP6PyP6PyEw[1_6yQ54Q4yQ1n5A>R6/9yR|?D|y[1a6yQ56Q4zQ1s5A>R6/9yR|=by|[1d6yQ51Q1|9A>cR6/ny[1c6yQ51Q4{Q1r5A>R6?`y6[186yP1Q4}Q1{+0A>0c>yP1Q50Q20+1S>0j>yQ52Q53Q1~5G>R6PyP6PyP6PyEw[1_6yQ54Q55Q235G>R6/9yR|?D|y[1a6yQ56Q60/9yR6=by6[Q60/dyQ51Q0|/ny[Q0|/cyQ51Q3TQ2m'@[Q2m/8yP1Q12P1P7Q5rQ5q/6gP]PnP]PgH1J:1sng-19nPnQ2x#2Q2y/6gP7Q5AQ5=50>R6#2166gPUPuPUPgH1J:1sug-19uQ0_Q5CQ5@61]>Q2>Q5<Q5APSH0u>0G>gP7Q11Q2K5A>Ru#216ugQ0bQ0bP^Q0bP^PgH1J81sg+19Q0vQ66Q2N+0A-1~>Q2uQ2O+0A>0G>gPnP?O1Q5S\zPnP;O1Q4Q%2R[Q5WQ2XQ5X+10Q2YQ5T+0qQ2TQ2YQ2V+0qQ5YQ6YQ1NQ2[41RI1qQ5TQ2VQ2WQ1MQ1P41RQ5Z#\$0>Q5[Q0?Q5U+10Q2TQ5VQ2Z'q41RQ1SH0WH0WH0WQ1UQ1yPeQ5\PeQ2^D~P;Q2_PeQ5]P0P9I0RP5P9P<&0HePeQ1z?h49PeQ309h93K04D~Q1WPqPqQ2bPGPqQ6[PqQ3EQ2a+0LH1FPGPqPqQ2ePGPqQ33Q2a01opQ3EH0<PGPqPqQ2bPGQ5aQ6\61dqPGPqPqQ2ePGPqQ1tQ2oQ5`H0<PGPqPqQ1t9LqiPGPqPqPiQ2aPGQ39EVPGPqPqQ0=#{#ORu>34wpPGPqPqPwQ3CQ2l'FR6PGPqQ5}PGPqALqiuS5}Q2i61dqPGPqQ4_PGPqQ1XQ1x'FR|Q3{5LqPGPqQ35PGPqQ2d,F6=Lq|PGPqPqQ33Q34PGPqQ1ZPGPqQ34Q1t'FQ1[5LqPGQ1\Q1]PqQ39PqQ1qQ1[+3>H1F61dq61dqK0:J1QK0:K0:K0:J1QI1cFNFNFNFNFNQ1`Q1bb;b<b=X11X31X41X51X91X?1X@1XE1XK1XN1XO1XV1Z0M1Z0p1X>~XD~XJ~Q6`,CQ\HQ2s20e{N=k8Q[Q3HQ0M'C\HQ2sQ2w=k8P[Q4XQ31\z[AkAQPQ6d,@8Q3=Q0M019bQ2SQ2{Q1w'4%]VQ0MQ0G'111OR7?V1@OP%]PQ0M??OgQ2SQ2t<2\g:1sPg-19P[[[[[[[[[[[[[[[[^11^31^41^51^91^?1^@1^E1^K1^N1^O1^V1`0M1`0p1^>~^D~^J~P:Q4F,4x16a{Q6VPhPaPkPxQ5IQ2}5G>Q5IQ6~Q5E;XS50>Q4wQ5IQ4x50>Q5IQ2}5A>Q5FQ5IQ7A'pQ5IQ5E50>Q0UQ0fQ0QQ0TPnPZQ0`Q0dQ0gP_Q0hP0Q16Q1hQ0lQ2=Q3@Q0BOQb8b6b7Y0;Y0:P5P:O2n2001000000121000000Y09Y08P5P:O2n2001000000121000000Y07W~P5P:O2n2001000000121000000c0?c0>b}bubtbsbrb{bzbqbbbab`bjbpbnbibhbgbfbebobmbdbcb_bZb2b6b7bAbBbPbQbRbSbFQ1eQ1fPXP3PXPgH1J40xeQ4<P4DmQ4<PoQ4<PgH1J:1sog-19oeQ4:Q4<82~sRsePsQ05Q4;Q4;Q14Q3~Q4CClS1462mDRsQ3eQ3b'MRoQ40+2nS4<Q40-2toS40Q29+4rQ4;Q4f82~oS4fQ0:Q47%t5Q4M5?;S4MPDQ45Q1:Q3xQ49ClQ45Q3fQ2P'MRo'p>0\>3P;H1x#7[[]I`0r1P:Q0:Q47Q4MP<Q45Q45Q3}Q4>PSH0582~oP7Q4GQ3jQ3f3<Ro#2Q4GQ45Q4=PSH05RXPoPXPgH1J:1sogPDQ42Q1=Q3|Q4:ClQ42Q0PQ3j3<>0\>AP<H1x#7P:Q4OQ3kQ0P3<#2Q4PQ3lQ3k3<RoQ4PQ4S+0NRXPoPXPgH1J81sgP7Q4NQ3sQ3l3<RX/6gQ4NQ4PQ42PSH05RoPXPoPgH1JPDQ4LQ1AQ4=Q3}ClQ4LQ3nQ3s3<>0\>?P0H1x#7P:Q4TQ3mQ3n3</6gQ4YQ4TQ4NPSH05RoQ4YQ3pQ3m3<PoPgH1JP7Q4[Q4YQ4LPSH05Ro#2Q4[Q3oQ3p3<??ogPDQ4`Q1hQ42Q4OClQ4`Q3tQ3o3<>0\>NP_H1x#7P:Q4]Q4`Q4YPSH05#2Q4bQ3vQ3r3<Q4bQ4]Q4[PSH05;?gQ4iQ3zQ3v3<Ro#I1@RoQ0:Q0M%t:RXQ4oQ4lQ4bPSH053?PDQ4rQ1rQ4YQ4[ClQ0G:0\>bP5H1x#7_0FPPQ1K#tQ4lQ4iQ4]PSH055?OQ1aY0FQ0:Q0G%\:#tQ4rQ4oQ4iPSH053?PD%\5Q4uQ1{Q4[Q4`ClQ0J/1VRZ-0w>RnPZ%\;Rx#tR{=?:gX:1Q4uQ4CQ3~3<Rz#IQ0J/@zRzeS4CPz11\RRH/1{R|/4g%t;R6Q0<'1R[,1HR`/4gP:XG1RfQ0~$2PX|1XG1RYP|P`PfPfPfP1P1g04J2115:H4p#IXI1XW1R`PHPH%IHP{P[PfPfQ0:%IXWGRXPxP[Q0<,1:XG1R|P;P6%I6H2;S0~J1nN:1MPgPg%IgL2O11R{RmQ4wQ4uQ4oPSH05R@'4A?R[@R[PfPYPmPfP|P6O1R6O1Rm,1RPfPfPfP`PRPR%IRP{PmPfPfPXPxP6Q0~J1nN:1MP@P@%I@L2OP5H1hS0~P[&2f3R@%t3#2R6Q4EQ1CQ4DQ1FQ1BQ1EQ1HQ1JQ1LQ1S+1PS1LQ1UQ1VP5Q5s9h9<S5sP3P9I0RQ1WPqPqQ1pQ3<PuPGPqPqPwPuQ1[PGQ1qQ3<'FQ1[5LqK0sK0sQ1`Q1bb;b<b=X11X31X41X51Q2G=?53A?5<gQ2JQ0<,1<Rx;?g[[^11^31^41^51P:Q50Q4}PcPSH05S50%t?RmPdQ0NP8P_O6b8b6b7bAbBbybvH4mbF1;>nQ4CPzQ0~P[P@P6Q4EQ1CQ4DQ1FQ1BQ1EQ1HQ1JQ2UQ1MQ1NQ1P'qQ1LH0WS1PQ1UP9P<Q4A?h<9S1NP;Q5sP5P9K04Q1WPqPqPiPpPGPqPqQ1pQ3;,FpQ0=#K#ORpPGPqPqPwPpQ1[PGPqQ1\PGPqQ39PGQ4?K0:K0sS4?K0sEVQ1`Q1bb;b<b=X11X31X41X51Q1eA?;x311;<S1\/4gQ1eQ2cQ4K[[[[[^11^31^41^51S1eP:PmQ50PdQ0NPAP8P_PRP\O9b8b6b7bAbBbybvbF-1DZDmB0o>>HRHQ41Q41PHP{D^11UTR{:0o>>P:Q1dQ1dP:%\<S50#tRHD^X:1P:P{Q4xQ44Q3y3<RZ#I1@UZRZePZ11d]:0o>>RZQ1d'4R6Q1d11ZHS4x'6R@'CQ1d%t<R[Q0<'1,1Z5r6S4KP6P@P6Q1dPfP|P[O1R@O1Rz,1ZRn'6&2P6PfQ1c$2PX|1XG1S1cQ1dQ1dQ1d#IQ4xPnPfPfPfP`PZPZ%IZPHPzPfPfPXQ50P@P|P<P[%I[H2;J1nN:1ML2}J2|P5H1hQ4K%\AR[#tR@,1bRzQ4zQ4yQ4wPSH05RH'4%tARZQ0<'1=?bHRnPfPYPzPfP|PZO1RzO1R6,1bPfPfPfP`PbPb%IbP@P6PfPfPXP[PzP|PAPZ%IZH2;J1nN:1MPHPH%IHL2OP<H1hPn&2f8%t8Rn#2Q4EQ1CQ4DQ1FQ1BQ1EQ1HQ1JQ1PQ1UP9P<Q2]P<Q1ND~P;P9P5P9D~Q1WPqQ5aPGPqQ1pQ5`Q3;'F'F=LqpPGQ4?K0:Q1`Q1bb;b<b=X11X31X41X51Q1eP:%t_Q57Q4|+0NP^PaPAP8PQPbPhO9b8b6b7bAbBbybvc0IbF-1D{I0^P{Q4eQ4eP{%\3#tD^g050GR{&1t:Ra&1t5RpP7&1t;?55:1;3;1;35'@RH[1;;51;;:'@&1t3?5;5[RZ&1t<?53;\HB4l;5:P:n2001000000120000000W^W]WWPZ^^p^]a^W{P:P>Q1;/shS4|,1hR{-0w>RaP3P{1;><Rp,@:X:1&1|3S57Q1;Q1;;DgS1;Q3|Q495<cRZ#I1@kZS1eeS4?Q1e11^\RZQ5o'4RHQ5o%\4S5`#tRz,1ZS5a'6R['CQ5o%t4R6Q0<'1S1N,1Z5rHR@PHP[PHQ5oPfP|P6O1S1PO1R[,1ZS4w'6&2PHPfQ1cQ5oQ5oQ5o#IQ5aQ4wPfPfPfP`PZPZ%IZPzP[PfPfPXQ5`Q1PP|P4P6%I6H2;J1nS1PN:1ML2}J2|P3H1hS5`P@%\0S4w#tS5a,1US4KQ4}Q4{Q4zPSH05R6'4%t0RZQ0<'1=?U6RHPfPYQ4KPfP|PZO1S4KO1S4},1UPfPfPfP`PUPU%IUQ5aQ4}PfPfPXQ4wQ4KP|P0PZ%IZH2;J1nN:1MP6P6%I6L2OP4H1hS4KPH&2f?R6%2mRmQ4EQ1CQ4DQ1FQ1BQ1EQ1HQ1JQ1SQ1UQ1oQ1WQ1p029w,FwRUQ1p62`qQ1`Q1bb;b<b=X11X311s5:,1:/@5^11^31P:Q5{PWO2b8b6b7bAbBbybvc0IbFb21;>aQ57Q1;Q4?Q1eQ5`P@Q4KPHP6PmQ4EQ1CQ4DQ1FQ1BQ1EQ1HQ1JQ1SQ1UQ1oQ1WPqPqQ39Q1pQ1[5[qPGPqPqPiPUQ1[9[qUI0KEoQ1`Q1bb;b<b=X11X31Q461s;5,15RU?DUg[^11^31P:Q5{PWP?O3b8b6b7bAbBbybvc0IbFb2-1D{DmO4b2Q1d/sd:0\>d=5=;P=PaQ01Q0DPFPcQ28Q4lQ4oP:I1:Q0D02::RdQ01g022;R{PFQ41Q0<63jDPCPF&4k:RU&4j:RgQ4e&4h:$4gRm's$3i+3hPBn0100000020000PBn10110300021012]00n10110300021010200=5FB$1rXG=PFQ0CQ01Q0DPFP:PdQ01P{PF1spk,1k:0o>>Q0<63jDPCPFPUQ5o/s^,1^:0o>>/sm$3i-3hgPBn0100000020000PBn10110300021012]00n10110300021010200=5FB$1rZ0OFQ0C=5FBRgPFQ0CQ01Q0DP~P:Q1GQ2rn10110O00021000000XlFg015SRmPBP:J1HQ2rQ2r02l:bZW2&1rgeQ4zQ26Q4iQ4lPaI1:P\Q4|Q4zQ49Q3x3<Ra#I1@haRaePaQ0J,1kRa/4pRh%\8Rg#tRU,1aRC,6pR{'CQ0<,1n,1a9rhpRdPhP{PhPfP|PnO1R{O1R6,1aRH,6p&2PhPfQ1cPpPp%IpPCPHPfPfPfP`PaPa%IaPUP6PfPfPXPgP{P|P8Pn%InH2;J1nN:1ML2}J2|P;H1hPd11\zRdQ4{PcQ4yPSH05Rc'4Q1N=?\cRnPfPYPd11\[PfPfPfP`P\P\%I\PzP[Q1PN:1MPcPc%IcL2OP8H1hPn&2f0%2ZQ4EQ1CQ4DQ1FQ1BQ1EQ1HQ1JQ1QQ21Q1S42[Q1UQ1VP5P9PAQ2]PAP9I0RP3P9PAQ2_PAP9I0RI0RQ1WPqPqPuQ3wQ3;'FR9Q0HPGPqPqQ1p/FuRu=Lqw1Fu99[qwPGPqQ5}PGPqQ3:9LqiQ3:Q0H5[qJ33EoK0sQ1`Q1bb;b<b=X11X31X41X51X91A?3x;Q1\P5P5Q1\Q3FD^Q2cQ3GQ3G;DA[[[^11^31^41^51^91P:%teQ0NQ59Q58+0NPtQ0{P8P4P^O8b8b6b7bAbBbybvc0IbFO2J1VP3P:J1Hb2Q4yQ23Q4bQ4iCl>4fD;=5FB$1rec0iY0iXG=J4eY0FY2AP:O1n0110500020011105PeO1c16PDQ4iQ1nQ4NQ4LClB0\>oPPQH1x#7eY1:Y19P5P:O2n2001000000121000000W2Y18P5P:O2n2001000000121000000W2Y17P5P:O2n2001000000121000000b2Y0FY1LY2@Z0r1H26PDQ4;Q14Q4<H3geQ05PsQ40Q29Q4fQ1^Q4>Q4@Q3|PSH3<7r:RSQ4=Q17Q3yQ44Q4=Q3hQ3d3<>0\>5I1:Q0C55FRo[`0N1P:P3P5P:O2PoeZ0YSZ0N1H26PDQ4;Q14Q40H3geQ0503CsJ3fJ3fc1Mc13c1Fc15c0]c0kc1bc1ac1fY0JY0ZY0XY0WQ2=P:Q20Q2:Q0ePON:4dW2WkP0P:P5K3eW2WkP4P:PAK3eW2P:O1b2P:O1b2P:O1b2WxWkZ0{1Z0z2P5P:O2n2001100000121106101P:Q2KO2bkb0c1_c0Jc0jY12Y11P5P:O2n2001000000121000000W2Y10P5P:O2n2001000000121000000W2Y0~P5P:O2n2001000000121000000W2Y0}P5P:O2n2011000000121000000b2c1UY0JY0jP5P:O2n2001000000121000000b2c0=c0=c0gb2Y0=Y0gP5P:O2n2001000000121000000c0=Y0ZY0=P5P:O2n2001000000121000000c0fY0fY1TP5P:O2n2001000000121000000c0<Y0<XIIP:O1Q3JQ1n#3Q1n#HQ24Q0uPlQ0tJ25&28I35Q05Q1|Q1|P8PrQ1iCl62mD+3CY0<n10110O00021110400P:O1c0<c0OPEQ1}Q1hPvH1\Q0qJ1VPDQ1mQ1mP3Q1?Q1@PEQ1}Q3IQ1hPvI2]K00RvePvQ02Q1nQ1mPrQ1AQ1@Q1sPAQ1iPrQ1AI08Q1>Q2}Q2Q$4cQ2M43dg03<7Rr$1uRvQ2}$2B$3c&2ArRr35PDQ2|Q2|Q2IQ2MQ2NQ2I#3K00&2I=RlQ2N$3G&28=Rs35Q2CQ2E#jQ2O43bQ00Q2R$3ap,3FS0RS35Q2A#g#BQ2Q$3`=5ls[&1u}RoQ2Q#z$22&4bDRB35Q2}#z$2rQ0E'@Q3@Q2=#HQ2I$1<43^Q0BQ3@#ZQ2|#zRt$22&1@t60g}43LQ3@#H+1aQ2E$1<$3JQ2C$3]Q3VQ2A$1<60=}Q3WZ0s}RtQ2;$0`60=}Q2=#z-17:#7Q3@$1<-0h5#7[^:1Q07Q0;g03>;35Q07Q0;g03?;35+18RxQ3^00;5Q0B#zRi$1{607}[XIIQ3\#H+1aQ27Q3aQ3K50>RuQ41Q41PuQ3aQ3L50>D^Q4eQ3X#zRu+17Q1<Q3X$0`+0r+1O[^M=[XIIQ3]#H+1a&22i&1@i60g}$3\Q3[#i'4Q3_#Z223:yRyQ3Y#zRi$3I,;>,4:&22i&1@i60g}g03A;R9<3[:40x7}:Z0o1-3M1&2{iQ3aQ3_#f'E55=&3Zu,;>&2{u,;>'4Q3Z$2aQ3c#P'4Q3eQ3b+1N$0fQ3b$02'4Q3dQ3e+1NQ3]+2yQ2PQ3hQ3^P:H1g#7Q4eQ3_#zRu$1@Ri+0h#7Q1dQ3a#zRZ$1{Rn+2YQ5nQ3c$0`+0rQ3kQ0P<31p#BQ3dPAO1Q0C55F[[[[[^M=p,4SINVRcQ2PQ3_O2Q3fQ0iQ3cQ3aQ3_P\Q3fQ0i$2BR[$2cQ3c43de212vr&3c[=5vreg010`p4p710RrP~\:Rv&1u5R[&1u;RzP7B0g35::0=3;B0=<3;B0=<35'CR7[B0=3;5B0=3;:'CB0g<;5:0=<3[R`B0gA3;:0=A<\7P3P;P5P:H4aP:n2001000000120000000Y0vY0uY0\Y0`P``0vz`0u[`0\v`0`rP:Q05Q3jQ3jQ0kQ3aQ3cCl62mDRrPEQ3gQ3f#HQ2PQ3hI2]REQ3dQ05@0=rEQ05Q3d80=rQ0fQ2:H26O5b2PDQ3fQ3iQ0jH2zeP]Q3_$3G=5lsePTQ3fQ0i#jQ3_43bePRQ00Q3_$3a;5SePVQ0i#g#BQ3a$3`=5ls[eQ0G&22uRs=5oBeQ0M&2ruRBQ0E'@ePOQ3fQ0i#HRo<3^iePPQ3fQ0i#ZB0g}siRs43L01aoePQ&3JiePeQ3_$3]ePNQ3V>0=}ieP_Q3_$0`:0=}tePM20h:n#7Q3c#zRn$1@Rt-0h5#7[^:1ePKQ0P00;5&1{n607}\xXII01aoeP?Q27Q3kQ3K50>RxQ41Q41PxQ3kQ3L50>D^Q4eQ3e#z+17Q1<Q3e$0`Rx+0r+1O[^M=[XII01aoeP0&3\sQ0i#i'4eP4Q0k#Z&3IZ,;>,4:&22Z&1@Z60g}@3[9:60xy7}:Z0o1-3M1eP8&2{uRyQ3fQ0i#f'E55=ePA&3Zu,;>1;>y'4eP<Q3_$2aQ0i#P'4eQ1lQ1kQ3fQ3hQ3d+2=+2@RyQ3fQ2P+1NR>40gRuQ1l&0f:Q3fQ2L+0@R9'4Y0t&0fy&0f>'1R}14:9X:1Q1BQ1EQ1HQ1JQ1LQ1UQ4aQ4A7h5Q1WPqPqPwQ0>PGPqPqQ1pQ0HPGQ1qQ4\5LqEVEVQ1`Q1bb;b<b=X11X31X41X5114:314;3Q2JQ4I'4[[^11^31^41^51P:Q2M$0JR9Q0P$02RsQ3kQ0P+1N$0fRoQ3kQ3jQ3f+2=+2@$0fRIQ0iP8O6b8b[b\&0fuRn24_y>RiDmQ3fQ0i+1NRlPjJ1V&0flQ0i$02'4eQ1lPuQ1lQ3a-2y:Y0tPyP>Q3_P;P}Q3a$2aR}&2rZ7?:X:1Q0EQ3jQ2PQ3h+2=+2@$0fQ3jQ3f+1N$0f'1=?}:X:1Q1BQ1EQ1HQ1JQ1MQ1O'qQ1S+1PQ1UQ2]P;Q2^P5Q2_P3Q2`K2HQ1WPqPqQ1pQ1tPGPqPqQ0HQ1YPGPqPqPwQ38PGPqPqQ3AQ1tQ0>PGQ18,FwQ0>5LqK0sEVEVEVQ1`Q1bb;b<b=X11X31X41X51X91X?1X@11458143814;8Q1R/48Q4J=?<4[[[[^11^31^41^51^91^?1^@1P:P9PsQ0P#PQ0EPoPIQ3b$2aQ0iP8P4Q0wO;b8b[b\PBQ0MDmPnPiDmI4^PlPjJ1VQ3_-2yleQ3jQ0kQ3aP:H1g#7RlP3P5Q0kP5P:O2O2WXXM=Q4e00ht#7Q1dQ3b$2k+2YQ5n00rxQ3sQ0n<31p#BQ2PPAO1Q0C55F[[[[\l^M=eP:PcQ3fQ3aO2eNP4]Y24Y29Y1|Y1nY1qY22Y1pY25Y27Y1vY1~Y1}Y1xY1oY28Y23Y1uY1{Y1yY21Y26Y1sY1rY1tY1wY1zY20P\Q0JPbP]PTPRPVQ0GQ0MPOPPPQPePNP_PMPKP?P0P4P8PAP<P3P;P5P:OKn50000010000001K112S12N12K12H12F12G12Y12T12M12O12I12V12[12C12L12Q12R12J12Z12X12D12U12E12B12P12\12Wc1Ec1Kc1Bc1cc0_c1eY1>Y1=P5P:O2n2001000000121000000W2Y1<P5P:O2n2001000000121000000bMc1Wc1Dc0eb2Y1HY1GP5P:O2n2001000000121000000bHY1NWHP5P:O2n2001000000121000000bHY1ZWHP5P:O2n2001000000121000000bHY1\WHP5P:O2n2001000000121000000bHY0WWHP5P:O2n2001000000121000000bHY0XWHP5P:O2n2001000000121000000bHY0eWHP5P:O2n2001000000121000000bHY0VPWP:Q0NK4\W2P:O1b2WLWHQ0[#BQ0KQ0\55JPJQ0KQ01Q04P~P:Q2rQ1Gn10110O00021000000XlJR~PmQ0YP:J1HQ2rQ0Z02l:b2WLWHn0110201020100P:P;O2bHc0qWLY0GZ2=1P:O1Q0SQ0O00}^&28135Q0K>0yJkPJQ0KP~PmQ0VP:J1HQ2rQ0W02l:b2WLY0Gn10110O01021110100P:P;O2c0Gc0OWLWxZ0|2Z2?1Z2>2P5P:O2n2001100010121106101X0LP5P:O2n2001100010121100106P:P;O2bxb0WLY0[Z1m1Z1l2P5P:O2n2001100010121106101P:P;O2c0[b0bLY0VY1CWLY2<Y1;Y1^Y0_Y2;XW2XC2Y2:Y14o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ext1 (E : env) (v : nat) (a : word) : env :=
  Env (fun n => if Nat.eqb n v then a else ev E n) (eb E).

#[using="Type"] Lemma ext1_agree : forall E v a, env_agree v E (ext1 E v a).
Proof.
  intros E v a. split; [|reflexivity]. intros n Hn. cbn [ext1 ev].
  destruct (Nat.eqb_spec n v); [lia | reflexivity].
Qed.
#[using="Type"] Lemma ext1_at : forall E v a, ev (ext1 E v a) v = a.
Proof. intros. cbn [ext1 ev]. rewrite Nat.eqb_refl. reflexivity. Qed.
#[using="Type"] Lemma env_agree_le : forall b b' E E', env_agree b' E E' -> (b <= b')%nat -> env_agree b E E'.
Proof. intros b b' E E' [H1 H2] Hle. split; [|exact H2]. intros n Hn. apply H1. lia. Qed.
#[using="Type"] Lemma env_agree_refl : forall b E, env_agree b E E.
Proof. intros. split; [intros; reflexivity | reflexivity]. Qed.
#[using="Type"] Lemma env_agree_trans : forall b E1 E2 E3, env_agree b E1 E2 -> env_agree b E2 E3 -> env_agree b E1 E3.
Proof. intros b E1 E2 E3 [A1 B1] [A2 B2]. split; [intros n Hn; rewrite A1 by lia; apply A2; lia | congruence]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma expr_vars_lt_eq : forall b e, AP.expr_vars_lt b e = AxSymRun3.expr_vars_lt b e.
Proof. intros b e. induction e; cbn; try rewrite IHe1, IHe2; try rewrite IHe; reflexivity. Qed.
#[using="Type"] Lemma kentry_vars_lt_eq : forall b K, AP.kentry_vars_lt b K = AxSymRun3.kentry_vars_lt b K.
Proof.
  intros b K. destruct K as [[? ?] | [? ?] | [? ?] | | | | [? ?] | [? ?] ? [? ?] ?| [? ?] ? ?| [? ?] ?];
    cbn -[AP.expr_vars_lt AxSymRun3.expr_vars_lt]; unfold AP.saddr_vars_lt, AxSymRun3.saddr_vars_lt; cbn [a_base];
    rewrite ?expr_vars_lt_eq; reflexivity.
Qed.
#[using="Type"] Lemma kn_vars_lt_eq : forall b k, AP.kn_vars_lt b k = AxSymRun3.kn_vars_lt b k.
Proof. intros b k. induction k; cbn [AP.kn_vars_lt AxSymRun3.kn_vars_lt]; [reflexivity|]. rewrite kentry_vars_lt_eq, IHk. reflexivity. Qed.
#[using="Type"] Lemma sr_vars_lt_eq : forall b sr, AP.sr_vars_lt b sr = AxSymRun3.sr_vars_lt b sr.
Proof. intros b sr. induction sr; cbn [AP.sr_vars_lt AxSymRun3.sr_vars_lt]; [reflexivity|]. rewrite expr_vars_lt_eq, IHsr. reflexivity. Qed.

#[using="Type"] Lemma edenot_agree' : forall b E E' e, env_agree b E E' -> AP.expr_vars_lt b e = true -> edenot E e = edenot E' e.
Proof. intros. eapply edenot_agree; [eassumption | rewrite <- expr_vars_lt_eq; assumption]. Qed.
#[using="Type"] Lemma know_ok_agree' : forall b E E' M k, env_agree b E E' -> AP.kn_vars_lt b k = true -> know_ok SEGS E M k -> know_ok SEGS E' M k.
Proof. intros. eapply know_ok_agree; [eassumption | rewrite <- kn_vars_lt_eq; eassumption | assumption]. Qed.
#[using="Type"] Lemma regs_ok_agree' : forall b E E' sr R, env_agree b E E' -> AP.sr_vars_lt b sr = true -> regs_ok E sr R -> regs_ok E' sr R.
Proof. intros. eapply regs_ok_agree; [eassumption | rewrite <- sr_vars_lt_eq; eassumption | assumption]. Qed.

(* [comment removed for export] *)

#[using="HOLES_agree"] Lemma sd_agree : forall D E E' fs s,
  env_agree nx0 E E' -> shape_vars_lt nx0 s = true -> sd D E fs s = sd D E' fs s.
Proof.
  intros D E E' fs s Hag. induction s; cbn [shape_vars_lt sd]; intros H; try reflexivity.
  - rewrite IHs by exact H. unfold Wp. replace (flat_map (piece_den E') ps) with (flat_map (piece_den E) ps); [reflexivity|].
    apply flat_map_ext. intros [bs|k]; cbn [piece_den]; [reflexivity|]. destruct Hag as [_ Heb]. rewrite Heb. reflexivity.
  - apply andb_prop in H as [H1 H2]. rewrite IHs1, IHs2 by assumption. reflexivity.
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    rewrite IHs1, IHs2 by assumption. rewrite (edenot_agree' nx0 E E' e Hag H1). reflexivity.
  - apply HOLES_agree. exact Hag.
Qed.

#[using="Type"] Lemma t_exit_has_nil : forall code fs, t_exit code fs [].
Proof. intros. unfold t_exit. apply t_emit_has_nil. Qed.
#[using="HOLES_nil"] Lemma sd_has_nil : forall D E fs s, D [] -> sd D E fs s [].
Proof.
  intros D E fs s HD. induction s; cbn [sd].
  - reflexivity.
  - apply t_exit_has_nil.
  - apply t_emit_has_nil.
  - left. exact IHs1.
  - destruct (_ <=? _)%Z; assumption.
  - apply HOLES_nil.
  - exact HD.
Qed.
#[using="Type"] Lemma t_alt2_nil_l : forall T : TSet, T [] -> t_eq (t_alt2 t_nil T) T.
Proof. intros T HT tr. unfold t_alt2, t_nil. split; [intros [->|H]; assumption | intros H; right; exact H]. Qed.
#[using="Type"] Lemma t_alt2_nil_r : forall T : TSet, T [] -> t_eq (t_alt2 T t_nil) T.
Proof. intros T HT tr. unfold t_alt2, t_nil. split; [intros [H| ->]; assumption | intros H; left; exact H]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma t_eq_alt2 : forall TA TA' TB TB' : TSet, t_eq TA TA' -> t_eq TB TB' -> t_eq (t_alt2 TA TB) (t_alt2 TA' TB').
Proof. intros TA TA' TB TB' HA HB tr. unfold t_alt2. split; (intros [H|H]; [left; apply HA | right; apply HB]; exact H). Qed.
#[using="nx0 HS XN XE XB"] Lemma t_eq_refl' : forall T : TSet, t_eq T T.
Proof. intros T tr. tauto. Qed.
#[using="nx0 HS XN XE XB HOLES_nil"] Lemma sd_salt2 : forall D E fs a b, D [] ->
  t_eq (t_alt2 (sd D E fs a) (sd D E fs b)) (sd D E fs (salt2 a b)).
Proof.
  intros D E fs a b HD.
  assert (Ha : sd D E fs a []) by (apply sd_has_nil; exact HD).
  assert (Hb : sd D E fs b []) by (apply sd_has_nil; exact HD).
  unfold salt2. destruct a; destruct b; cbn [sd] in *;
    first [ apply t_alt2_nil_l; assumption | apply t_alt2_nil_r; assumption | apply t_eq_refl' ].
Qed.
#[using="Type"] Lemma salt2_vars : forall b x y, shape_vars_lt b x = true -> shape_vars_lt b y = true -> shape_vars_lt b (salt2 x y) = true.
Proof.
  intros b x y Hx Hy. unfold salt2.
  destruct x; destruct y; cbn [shape_vars_lt] in *; rewrite ?Hx, ?Hy; try reflexivity; try assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition node1_stmt (pre : acs -> bool) (node : acs -> option acs) : Prop :=
  forall cs cs' E R FULL model T,
    cs_ok E cs R FULL model -> pre cs = true -> node cs = Some cs' ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS scfg (cfg R' (pc cs') FULL' model') T) ->
    srealizes SEGS scfg (cfg R (pc cs) FULL model) T.

Definition always (cs : acs) : bool := true.

(* [comment removed for export] *)
Definition sys_stmt (y : snode) : Prop := node1_stmt (is_ecall_at SEGS) (node_sys A nx0 y).
(* [comment removed for export] *)
Definition x_stmt (x : xnode) : Prop := forall args, node1_stmt always (node_x SEGS A nx0 rz x args).
(* [comment removed for export] *)
Definition fresh_stmt : Prop := forall r logc base, node1_stmt always (fun cs => node_fresh nx0 cs r logc base).
(* [comment removed for export] *)
Definition join_stmt : Prop := forall b off n, node1_stmt always (fun cs => node_join SEGS cs b off n).

(* [comment removed for export] *)
Definition brk2_stmt : Prop :=
  forall cs csa csb E R FULL model TA TB,
    cs_ok E cs R FULL model -> is_ecall_at SEGS cs = true -> node_brk2 A LIMIT cs = Some (csa, csb) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csa R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS scfg (cfg R' (pc csa) FULL' model') TA) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csb R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS scfg (cfg R' (pc csb) FULL' model') TB) ->
    srealizes SEGS scfg (cfg R (pc cs) FULL model) (t_alt2 TA TB).

(* [comment removed for export] *)
Definition exit_stmt : Prop :=
  forall cs code E R FULL model,
    cs_ok E cs R FULL model -> is_ecall_at SEGS cs = true -> node_exit cs = Some code ->
    srealizes SEGS scfg (cfg R (pc cs) FULL model) (t_exit (Z_to_bv 64 code) (m_fs model)).

(* [comment removed for export] *)
Definition ext_stmt : Prop := forall id args, node1_stmt always (XN id args).
(* [comment removed for export] *)
Definition ext2_stmt : Prop :=
  forall id args cs csa csb E R FULL model TA TB,
    cs_ok E cs R FULL model -> XB id args cs = Some (csa, csb) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csa R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS scfg (cfg R' (pc csa) FULL' model') TA) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csb R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS scfg (cfg R' (pc csb) FULL' model') TB) ->
    srealizes SEGS scfg (cfg R (pc cs) FULL model) (t_alt2 TA TB).
(* [comment removed for export] *)
Definition mm2_stmt (node : acs -> option (acs * acs)) : Prop :=
  forall cs csa csb E R FULL model TA TB,
    cs_ok E cs R FULL model -> is_ecall_at SEGS cs = true -> node cs = Some (csa, csb) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csa R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS scfg (cfg R' (pc csa) FULL' model') TA) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csb R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS scfg (cfg R' (pc csb) FULL' model') TB) ->
    srealizes SEGS scfg (cfg R (pc cs) FULL model) (t_alt2 TA TB).

Definition mm3_stmt (node : acs -> option (acs * acs * list acs)) : Prop :=
  forall cs csa csb cscs E R FULL model TA TB TC,
    cs_ok E cs R FULL model -> is_ecall_at SEGS cs = true -> node cs = Some (csa, csb, cscs) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csa R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS scfg (cfg R' (pc csa) FULL' model') TA) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csb R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS scfg (cfg R' (pc csb) FULL' model') TB) ->
    (forall csc E' R' FULL' model', In csc cscs ->
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csc R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS scfg (cfg R' (pc csc) FULL' model') TC) ->
    srealizes SEGS scfg (cfg R (pc cs) FULL model) (t_alt2 TA (t_alt2 TB TC)).

(* [comment removed for export] *)
Definition emit_stmt : Prop :=
  forall id args cs fd ps cs' E R FULL model T,
    cs_ok E cs R FULL model -> XE id args cs = Some (fd, ps, cs') -> T [] ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS scfg (cfg R' (pc cs') FULL' model') T) ->
    srealizes SEGS scfg (cfg R (pc cs) FULL model) (t_emit (Wp E fd ps) T).

(* [comment removed for export] *)
Definition holes_stmt : Prop :=
  forall h ch, HS h = Some ch ->
  forall E R FULL model, cs_ok E ch R FULL model ->
    srealizes SEGS scfg (cfg R (pc ch) FULL model) (HOLES h E (m_fs model)).

(* [comment removed for export] *)
Hypothesis node_sys_sound : forall y, sys_stmt y.
Hypothesis node_brk2_sound : brk2_stmt.
Hypothesis node_mmap2_sound : mm2_stmt (node_mmap2 A nx0 LIMIT).
Hypothesis node_mmapin_sound : forall hole : bool, mm3_stmt (node_mmapin A LIMIT hole).   (* [comment removed for export] *)
Hypothesis node_mprotect2_sound : mm2_stmt (node_mprotect2 A LIMIT).
Hypothesis node_exit_sound : exit_stmt.
Hypothesis node_x_sound : forall x, XON x = true -> x_stmt x.
Hypothesis node_join_sound : join_stmt.
Hypothesis node_ext_sound : ext_stmt.
Hypothesis node_emit_sound : emit_stmt.
Hypothesis node_ext2_sound : ext2_stmt.
Hypothesis HS_sound : holes_stmt.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma split_sound : forall cs e mid lo hi E R FULL model,
  cs_ok E cs R FULL model -> erange (kn cs) e = Some (lo, hi) ->
  (bv_unsigned (edenot E e) <= mid -> cs_ok E (set_kn cs (KRange e lo mid :: kn cs)) R FULL model)
  /\ (mid < bv_unsigned (edenot E e) -> cs_ok E (set_kn cs (KRange e (mid + 1) hi :: kn cs)) R FULL model).
Proof.
  intros cs e mid lo hi E R FULL model HC Hr.
  pose proof (erange_sound SEGS E _ (kn cs) e lo hi (co_know _ _ _ _ _ HC) Hr) as Hb.
  split; intros Hm; apply cs_ok_set_kn; [exact HC| |exact HC|];
    (constructor; [cbn [kentry_ok]; lia | exact (co_know _ _ _ _ _ HC)]).
Qed.

#[using="Type"] Lemma kn_contra_sound : forall E M k, know_ok SEGS E M k -> kn_contra k = true -> False.
Proof.
  intros E M k HK H. unfold kn_contra in H. apply existsb_exists in H as (K & Hin & HKb).
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  destruct K as [| | | | |e lo hi| | | |]; try discriminate. cbn [kentry_ok] in HKK.
  destruct (Z.ltb hi lo) eqn:Hlt; [apply Z.ltb_lt in Hlt; lia|].
  assert (GEN : forall c ts, lin_of e = (c, ts) ->
            match lin_range (erange k) c ts with
            | Some (a, b) => (Z.leb 0 a && Z.ltb b two64 && (Z.ltb b lo || Z.ltb hi a))%bool
            | None => false end = true -> False).
  { intros c ts Hle Hm.
    destruct (lin_range (erange k) c ts) as [[a b]|] eqn:Hlr; [|discriminate].
    apply andb_prop in Hm as [Hm Hd]. apply andb_prop in Hm as [Ha Hb].
    apply Z.leb_le in Ha. apply Z.ltb_lt in Hb. unfold two64 in Hb.
    pose proof (lin_range_sound E (erange k) (fun a lo hi Ha => erange_sound SEGS E M k a lo hi HK Ha) _ _ _ _ Hlr) as Hbd.
    pose proof (lin_of_sound E e) as [q Hq]. unfold lden, AX2S.uE in Hq. rewrite Hle in Hq. cbn [fst snd] in Hq.
    pose proof (u64_range (edenot E e)).
    assert (q = 0)%Z by nia. subst q.
    apply orb_prop in Hd as [Hd|Hd]; apply Z.ltb_lt in Hd; lia. }
  destruct e; try discriminate;
    (destruct (lin_of _) as [c [|t1 [|t2 ts]]] eqn:Hle; try discriminate; exact (GEN _ _ eq_refl HKb)).
Qed.

#[using="Type"] Lemma estart_SA : forall E b k, estart E (SA b k) = bv_unsigned (edenot E b) + k.
Proof. reflexivity. Qed.

#[using="Type"] Lemma xlo1_sound : forall E M k e lo, know_ok SEGS E M k -> xlo1 k e = Some lo -> lo <= bv_unsigned (edenot E e).
Proof.
  intros E M k e lo HK H. unfold xlo1 in H.
  assert (LIT : forall z, e = ELit z -> Some (zlit64 z) = Some lo -> lo <= bv_unsigned (edenot E e)).
  { intros z -> Hs. injection Hs as <-. cbn [edenot]. rewrite zlit64_eq, u_lit64. lia. }
  destruct e; [exact (LIT _ eq_refl H)|..]; clear LIT;
  (destruct (erange k _) as [[l1 h1]|] eqn:He; [pose proof (erange_sound SEGS E M k _ l1 h1 HK He)|];
   destruct (lin_brange k _) as [[l2 h2]|] eqn:Hb; [pose proof (lin_brange_sound SEGS E M k _ l2 h2 HK Hb)| |pose proof (lin_brange_sound SEGS E M k _ l2 h2 HK Hb)|];
   [..| (* [comment removed for export] *) destruct (lin_srange k _) as [[l3 h3]|] eqn:Hs; [pose proof (lin_srange_sound SEGS E M k _ l3 h3 HK Hs)|]];
   try discriminate; injection H as <-; lia).
Qed.

#[using="Type"] Lemma xhi1_sound : forall E M k e hi, know_ok SEGS E M k -> xhi1 k e = Some hi -> bv_unsigned (edenot E e) <= hi.
Proof.
  intros E M k e hi HK H. unfold xhi1 in H.
  assert (LIT : forall z, e = ELit z -> Some (zlit64 z) = Some hi -> bv_unsigned (edenot E e) <= hi).
  { intros z -> Hs. injection Hs as <-. cbn [edenot]. rewrite zlit64_eq, u_lit64. lia. }
  destruct e; [exact (LIT _ eq_refl H)|..]; clear LIT;
  (destruct (erange k _) as [[l1 h1]|] eqn:He; [pose proof (erange_sound SEGS E M k _ l1 h1 HK He)|];
   destruct (lin_brange k _) as [[l2 h2]|] eqn:Hb; [pose proof (lin_brange_sound SEGS E M k _ l2 h2 HK Hb)| |pose proof (lin_brange_sound SEGS E M k _ l2 h2 HK Hb)|];
   [..| (* [comment removed for export] *) destruct (lin_srange k _) as [[l3 h3]|] eqn:Hs; [pose proof (lin_srange_sound SEGS E M k _ l3 h3 HK Hs)|]];
   try discriminate; injection H as <-; lia).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma deand_sound : forall E e e' s, deand e = (e', s) ->
  0 <= s /\ exists rho, 0 <= rho <= s /\ bv_unsigned (edenot E e) = (bv_unsigned (edenot E e') - rho) mod 2 ^ 64.
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
ltac2:(KReplay.run1 (kr_t_AsanPlanSound ()) ["FPX_3"; "Sound"] "p'0h03rhoh11Hh21zi001zh32e'h41si011sh52Hdh64__x1h72Hah87__arithh94__ffh:8__varmaph;5__with<4__x2h=3IHbh>4__x3h?5heq_jh@6heq_m'hA6__sat3hB4__p1hC4__x4hD3IHahE6__sat1hF5heq_XhG1ni021nhH2opi032ophI6__sat2hJ6__sat4hK1ai041ahL6__sat5hM4__x5hN4__x6hO1bi051bhP2HthQ1mi061mhR4__p2hS6__sat6hT6__sat7hU6__sat8hV6__sat9hW5__x10hX5__x11hY5__x12hZ5__x13h[4__x7h\4__x8h]4__x9h^2b1h_2b2h`1ei071eha2H0hb2Hbhc1Xhd2a0i082a0he1pi091phf2sxi0:2sxhg2Eahh2H1hi3H10hj3H11hk3H12hl3H13hm3H14hn3H15ho3H16hp3H17hq3H18hr3H19hs2H2ht3H20hu3H21hv2H3hw2H4hx2H5hy2H6hz2H7h{2H8h|2H9h}2HXh~2Hji0;2Hmi0<3Hrai0=5__x14i0>2a'i0?2m'i0@1qi0A2q0i0B2q1i0C1ri0D2r0i0E2r1i0F2r2i0G2rai0H2A'i0I2A1i0J2B1i0K1Ei0L2Ebi0M3H22i0N3H23i0O3H24i0P3H25i0Q3H26i0R3H27i0S3HA'i0T3Hj0i0U3Hm'i0V2Hpi0W2Hri0X3Hr2i0Y3Hrbi0Z3Hs0i0[3Hs1i0\3Hs2i0]2b'i0^2bki0_2bni0`2boi0a2bwi0b6heq_A'i0c6heq_A1i0d6heq_B1i0e1ii0f1ji0g1ki0h2loi0i2q2i0j2q3i0k2r3i0l2rbi0m2s0i0n2s1i0o2s2i0p1ui0q1wi0r2b0i0s2e0i0t3op0i0u1xi0v2x'p%0p%1p%2p&0p&1p;2p;1p;3p;4p;6p;5p;:p;7p;8p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0g0038R5p4p710R6p9P0p1003Vp4p710R7p9P0p1004Np4p710R8p8P0p1004ep4p710p8P0p1005FR9p4p710p8P0P9p4p7210p8P0p1005cp4p710R0p8p100_Jp4p70R9g00;\R:p4p710R;p8P9P1p8P9P2p8P9g0079R<p4p710R=p8P9P4p8P9P3p4p710R3p8P9P7p8p1006?p4p710P6p8p100`:p4p70R9P;p8P9P1p8P9P2p8P9p100`hp4p7210p8P9P=p8P9P4p8P9P3p8P9P6p8P9P7p8p100aDp4p70P=p8p100bCp4p7210R9P1p8P9P2p8P9P=p8P9P4p8P9P3p8P9P7p8p1062Tp6051000R9P6p8P9p103VIp4p710R;p8P9p1063Vp4p710p8p106kQp6051000R9P8p8P9P6p8P9P;p8P9P0p8p107<2p6051000R9P8p8P9P;p8P9P0p8p100bop4p70R0P1p8P0P2p8P0P4p8P0P3p8P0P7p8p1006\p4p7210R7P=p8P7P6p8p1007Up4p7210P6p8p10082p4p73110P6p8p100cep4p710P6p8g00emS00k21wTg008Nj1;Tg00dlk11`Tg0093k100Tg018]j2?Tg04JVj1YTg00:Bj2LTg00E?k11]Tg00F?k11ZTg00]4k11VTg00G[k11UTg00H9k11TTg00Hdk20pTg00NNk21RTg00O0k20>Tg00OJk21QTg00P6k31PTg00PUk41NTg00>lS01j2FTg01=4j2<Tg00iHj28Tg00<lj29Tg06IOk102Tg06JQj3=Tg08n1j1pTg08nok10|Tg00JTj1VTg01POj2tTg01Plk20mTP:j3:Tg00=Lj25Tg00A:j1ITg00AYk21=Tg00J2k11STg00K9k21<Tg05C@k30xTg017fk10oTg01fij2iTg00^Vj27Tg01>6k20fk41oTg01>^k30dTg00;;k20LTg00<6k11:Tg00=ik208k31DTg00?Gk20QTg00>Pj2ATg00?nk20TTg00@Tk20YTg00:^j2~Tg00BBk11vTg00B`k219Tg01BIk20wTg01KEk20vTg01LWk31uTg00Ldk61tTg00MHk30uTg00<Ok20tTg07Onk21ITg00jOk40sTg01fOk418TP<k60lTg01QJk31sTg05bBk20{Tg05b_k21rTg01Qmk21qTg08oMk11pTg0902k41nTg01L1k21mTg090Rk20cTg0910k41iTg091Qk21hTg08\lk51gTg092:k41dTg08c<k11cTg093Ak21bTg06P4j3\Tg06Q6j3[Tg06R8j3ZTg06S:j4{Tg06T<k401Tg072hm:1^Tg01Gmk40@Tg016lS02k20qTg05XUk60zTg00IGk40\Tg00RFk70hTg00L@k71ATg07Pok31\TP5k614Tg094Bk11[Tg00Cjk30jTg00DSk21YTg00E_k30_Tg00F_k21lTg00G=k415Tg00Mkk31XTg00Rjk80ZTg00CAk31FTg01C2k31GTg00K\k61WTg00^3k31>Tg01IER5g00UMR<f1R:f0R6H0@p=Nf2R7%p:;:6p=Wg00VPR=/L6p=21L:6,F7p=S%;6#;p>17f4R0f3R3/<7'8/7:/96p=>1<7:,83=:<6,F0p=B20q<6,F:p=1P0P<P3P5P<P7P=H0@P:P6J0zp=PA:<=6p=kP0P5P3P5P<P7P=H0@P:P6J0zp=GA:5:6p=61<:6,87p=3A:<:6,F7p=R177:/969:<3,F0p=41L6=,F:p>1_P7g00SNS03g00SmR4P4g00TMS04P<P:g00YLR2P6H0\g00TmR1K0hp=]g00ZZR9g00[:R;7:6p=j176=p=OP7Q03P4P4Q04P:P6K1Ap>0XA:<:6p=0P<f7R8f6R>f5R?-0><1903&0o6:1\7:J14p=MP<P0P3P7P:&1[6J14p=KP<P>P=P?19379:<0P:P6H0sH18p=HP<P=P>P?20q<0P3P7H0sP:P6J0lp=JP5P0P3P7P:P6J0lp=Eg05ChS05?=:6p=|P5P<P715:6H0@p=nP5P<P6P=H0@p>0}g04Q:R@,96p=T17@6p=u1?:6-0{7p>0A17@6$0|p=y1?7:/76p=r1<>?,881<37,80/7:/965:<p=s1L7:,F3/F6p=zP0P<P3P7P:P6J0zp>13P0P5P3P7P:P6J0zp>1@Q05?=:6,<7,83p>1?1L=:20q<6'Fp=m20q<6p>0iQ05?=37,<0,8?/7:/96p>0<Q05?=7:,<3,80=:<6p>09157:,L3,F0/F6p=g187:/76p>0n19:69:<7p>0y21=<6p=QB0j<:6p>0[B0j<:6g00X9+1Yp=eg00VnRA@0_:6p>1221l<6p=oP<P7P:P6H15p>0B21<<6p=XB1X<:6p=^P>Q03P4P4Q04P?P0P3Q03P4P4Q04P7P:P6L0ZL0Zp=l1L=:/F6p>11B0_A:6:0_A7p>10P<P<P0P3P7H15P:P6H15p=hP<P:P2P6H0\p=xP3Q03P4P4Q04P7P:Q03P4P4Q04P6P1K0hK1Ap=w157:/96p>0g177:/96p=D197:=:<6p=q1737/9:/56p>0=1L=71A:6'Fp=_20><6p=C197:/56p>1O19:6,L=p=v1A=6p=`1503/9715:6'7p>0;A:<6=p>1;1~7:-0t3/569:<0p>0:1A7:1L6='Fp>071~:6=:<=p>0UB1F<7:>0j<6p>0bB0j<:6:0j<7p=b%;6#;#;#;#;#;#;#;p>1M%;6#;#;#;#;#;#;#;#;#;#;#;#;#;#;#;p=}B1G<:6p=dB1F<:6p>06P7Q03P4P4Q04P<P:g00XeR2P6H0\P1K0hp>0WP:Q03P4P4Q04P6J1Wp>0`P7Q03P4P4Q04P<P:g00Z3RBP6H0\P1K0hp=fB1><:6p>05P<P:P2P6H0\p>04P3Q03P4P4Q04P7P:P6L0Zp>0VP<P:PBP6H0\p>1LP0Q03P4P4Q04P3P7P:Q03P4P4Q04P6P1K0hL0Zp>0~P0Q03P4P4Q04P3Q03P4P4Q04P7P1K0hP:P6L0Zp>03P>Q03P4P4Q04P?Q03P4P4Q04P0P3P7L0ZP:P6L0Zp=U20t7:/56p>1K177:=:<6p=c1A:6,F7p>0S15:69:<7p>1JP<P0P3P7P:P6J14p>0RP320q<7P:P6H0sp>1Hg05DT?=:6p>0PP5P<P:P=H0@=:76p>0Og06U>?=:6p>0Eg06Uj?=:6p>0Ng06VV?=:6p>0?g06WB?=:6p>0Dg06Wn?=:6p>0Mg06XZ?=:6p>0Hg06YF?=:6p>0IP5P<g06Z2S06?=:6P=H0@p>0KQ06?=7:,<3,80=:<6p>0JQ06%Y67=:p>0r17:6,57p>0k1i6@p>0F15:6,L=p>1E19:6,57p>1615:6,L7p>1C15:6,77p>0CB1G<7:>0j<6p>0^%V6#V#V#Vp>1k%V6#V#V#V#V#V#V#Vp>0a%;6#;#;#;p>1jB0_A:6:0_A7:0_A3:0_A0p>0eP<B1><7:PBP6H0\p>1B1A7:/F6p>1f1L6=p>1eP5P<Q06?=7:P=H0@=:36p>0GQ06?=:6p=@Q06%Y67=:,<7p>1aQ06?=:6,<7,83p=aQ06?=:6,<7p>0]g00n`21w5<RB1N:6R17W7S07%2:R2%26RC?S67S08g00UkS09#;S0:#;S0;#;S0<#;S0=$17S0>$1`RDP>P0PDP>P3P6Q0:$00REQ0>$00S0?'?RFD>DBX0<'1[^4<^35X`5%Y7=WB1S0@PBQ00P5P<P<P6P6n2001109000120107100X`BRG%Y31N7:RHP6DP%k:S0APBQ00P5P<P5P6P:n2001109000120107100X`BRI%Y0S0B1N37S0CP:DGQ0B/63%Y?/60%Y>%k?RJ%2>S0DASC68S0Ef;RKf9RL#YS0F53DRMPDPKP7P6PFD>RN3RX0<'1[X35%k0S0GASC6:ROPMPMP6PFD4X0<,1CX4<1L==RM21_C6S0Hf:RPf8RQ#YS0I53DRRPRP6PFD4X0<RS&1]AS0J&1ZAS0K&1V<RA&1U<S0L&1T<RT20p<=RU;]URVQ04-1RTS0MP6P720>9;21Q67#jdB1P<=:H1NS0Nb9b:b;PMP6b8S0OPS1FMMRS%Y8S0P,<LR;,8DRW%OWRXPFQ0JQ0KPAQ0LB0XTVVQ0MQ0Nb9b:b;PSP6b8S0QPW196FRV,0RX2<PW10R6X2<PWPWPFPWPFP;GMPXPWDKFHP?P6FJW1P?P6DEW1P6O1b1P6O1b1W5X4<X35X2<g03D=S0R&027S0S=WB1S0TPBPG&023S0UPHP6DPQ0APBPI&020S0VQ0CP:DGQ0V/63&02?S0W/60&02>S0XQ0DQ0E&02L93DKRW;RNX0<'1\JX35Q0GPOPWPWP6PFD4X0<,1CX4<PMQ0H&02QS0Y93DPRWPWP6PFD4X0<RNQ0OPNPS&028S0Z,<LRN,8DRX%OXR;PFQ0QPX10WVX2<PX10W6X2<PXPXPFPXPFPNGMP;PXDKFHP?P6FJW1P?P6DEW1P6O1b1P6O1b1W5X4<X35WGg06Z^S0[Q07Q08PDP8P0PDP8P3P6PFD>DBX0<,12[^4<^35S0\Q07Q08PDPLP0PDPLP3P6PFD>DBX0<,12[^4<^35S0]A=>?3=WB1Q0[Q0[PBP6Q00P5P<PB%p8S0^Q00P5P<PBQ0^1|3:?n76RXn200110u00012010]10on200110u00012010>10nA=68?$0}R;P;P;P;P;P;P;P;P5PBP?P9PB%T6#uR;&0|;R;80AEQ09#VS0_#;S0`#;S0a$17$00RN,t;+0mS0bQ00P5P<PB%pQR;%T7S0c#yQ09$00RW5rE9n:6S0dn200110u00012010v101A=:Q>$0}RRn0100000020000PRA=3PQ$0}RRPRPRPRA=0KL$0}RRPRn01105000810106101023010t10810r3010t10810r3010t10810r3010t10810r4010:10h10210s4010:10g10e102n01103000:00000000000000000000Q0C5:B%23S0ePCP6P0PDf<RRA=7L8PDPRP?P6PFGsCzX0<'1]5P8Q00P5P<PB%p>RYQ00P5P<PBPYPXn200110u00012010]10on200110u00012010>10n=:BHQ0^PB20>B6S0fA:B;6Q00P5P<%pPS0g=:B6A:B31S0hQ08PDfBR;f?RYPDP;P3P6PFD>DBX0<,12[^4<^35Q00P5P<PBP7Q00P5P<PB%pRPXn200110u00012010]10on200110u00012010>10n1NQ8S0i5:B%2QS0jASC6LS0kPDfARXf>RZ/|RPDPXPPP6PFD>DBX0<'1]5]D]7P:f=R[#pR\=:B11N03S0l=:B1S0mQ08PDfER]P;PDP]P3P6PFD>DBX0<,12[^4<^35Q00P5P<PBP\1|?:?n06n200110u00012010]10o1NKPS0n5:B%pZPBQ0fAWBY6Q00P5P<%pXS0o=:B6Q0hQ08PDfKR\fFR^PDP\P3P6PFD>DBX0<,12[^4<^35Q00P5P<PBP71|K:?nP6n200110u00012010]10of@R_,NXR`5:B%2XS0pASC6;S0qPDfJRafGRb/|]PDPafCRcP6PFD>DBX0<'1]5]=]bP:fDRd=WB1Q0mQ08PDfNS0rfIRePDQ0rP3P6PFD>DBX0<,12[^4<^351|R3?nK71Ndc5:BPBPG1|[015R3Rf'N1N]dRgP6I1310fdPBPI1|Z?Rf?n[01N^]P:I1@16f^1|Y>/6b1|_815_8RffHRh'0ASC6aRiPDfRRjfOS0sfMRkH1?RlA3Dj7P6PFD4X0<,me[X3515Y>/0bP<PfPOPlPDPjPcPPH1?P6PFD4X0<,1CX4<PZPXP_20>B`O3PCP6PXPDfQR`Q0rPDP`P;P6PFGsCzX0<,m_Q01Q0pQ0qPDPjQ0sPDPjPcP6PFD>DBX0<$0i15;LPCP6PcPPPDfSS0tfPS0uQ0rPDQ0tPdPKP6PFJ0<I09DgX0<'mP6%2cASC6]RlPDfURfPjPDPfP^P6PFD>DBX0<$0iQ02P<ASC6^RmfVRnQ0t53DS0vA3DnbP6PFD4X0<15^[PCP6PbPZPDfWS0wfTS0xPjPDQ0wPhPYP6PFJ0<I09DgX0<'mP6PCP6PhPDfXS0yPfPDQ0yPeP6PFGsCzQ01AS2:efYRo=3DnS0z1<oa>0nD:<0yF15aXPCP6P\P;PDf[RpQ0yPnPDPpfLS0{PcP6PFJ0<I09DgX0<'mP6Q0e?S3\f\Rq=3DoS0|1<qk>0nD0<0yFP;P]Pd20>BgO3%2dS0}PlPDf^RlPoPDPlP^P6PFD>DBX0<'1Q01%2]S0~PmPDf_RmfZS10PDPmPbP6PFD>DBX0<$0iQ0s/5^PCP6Q0uPbPDf`S11f]RgPpPDQ11P`PhP6PFJ0<I09DgX0<'mP6%2bPCP6PePDfbS12PgPDQ12PaP6PFGsCzX0<$0iQ02P<PiPDfcS13PlPDQ13P\P6PFD>DBX0<Q0t/5aPCP6Q0xP\PDfdRifaRrPmPDPiPfQ0{P6PFJ0<I09DgX0<'mP6PCP6Q0{PDfeRsQ11PDPsPkP6PFGsCzQ01AS2:kPDffS14PrPDQ14Q0rP:PFGsQ0wQ0r'5PCP6Q0yQ0sPDfhS15PsQ13PDQ15PoQ0uP6PFJ0<I09DgX0<'mP6Q0eQ0s7S3PDfiS16PiPDQ16P`P0PFGsQ10/5`Rt#2PCP6PpPjPDfkS17Q15Q14PDQ17PqQ0tP6PFJ0<I09DgX0<Rug00WZRv#IRw#IRx#QS18%QwS1921=<vS1:+0[Rv'eQ0J+12Q0K%o7S1;@0B:AS1<Q0LPTQ0:#XRw9]TUS1=&1S4RyPTQ09-1<<Rz9]TUS1>Py1^zwS1?9]TUS1@FlQ0MQ0Nb9b:b;X6<X<<1573R{#2R|\2\2^6<^<<P6PjPpPPPbO4b8P<Pu15;?S1AQ1AQ1A/Lt+11PDfjS1BfgS1CPsPDQ1BPpPjQ1APFJ0<I09S1D%IxRx#IRt#QS1EQ18Q1:+0[S1F'e%QxS1G/evQ0J410Q0K%o0S1HP7PAP:%o3S1IDhQ0LPTPTQ1=PTQ0;#XRv,xwCwPyPTPTQ1>PTQ0_#XS1J,xzCwS1KPyPTQ1@PTQ1?Q1J/^v'xCwFlQ0MQ0Nb9b:b;X6<X<<X><XC<AS2:3Rx150?9S|{\x[^6<^<<^><^C<P6PjPpP>PcP7PYO6b8Q1BQ1C'<S1L,8DS1MQ1B/<sS1N,8DS1O<0gFQ05Q17/<qRxQ17Q0t'<R|40x15c>R{60nD>0y6FX2<Q1B/<pS1P,8DRuQ1B/<jS1Q,8DR}<0gFS1RQ17Q1553DQ17Q1453DR~'5AD6{F7qFX2<ADu;FS1S156~18DxRx18D|R~<0gF?D{FR{7qFX2<AD}?FS1TPxPcPFP6H0=?qF{X2<Q1P$0oA_uuF&0o|A_~~FflS1U=3DgP<fmS1V=3DfP<fnS1W=3DnR~#C106~R~eP~foS1XQ1153DR~#C107~R~eP~P3PhPFAD7KFH0=R~/iF%2~%2FS1Y17?aR~AD0[F81OF/vF[[1503R|/iF%2|Q1Y15>?/vF[[1i~F%2~Q1YQ0{,78/vF[[Q0?-0fES1Z%`ES1[Q0?#2%`FR~[[S1\%2ER|g0157RuQ0?>0dE:UW7S1]Q1Y\uS1^^7|S1_178_R{/iF%2{Q1YADL;FR{#2[[PLPQPFQ0rPXI0;Rx/iF%2xQ1YPKPPPFQ0uPcI0;/vF[[PPQ0sPFP{H0=00LF&1;FR{$1:S1`PKQ0uPFADPcFH0=RxPFPxPF19xFI0:[208xFPRP`PFADKdFH0=Rx/9FR}?_}F\~20QxF1AF=S1aP[PjPFADR]FH0=Rx/9FR}>07F}[20TxFPZQ0tPFAD[^FH0=Rx00UF\{20YxFPYQ0xPFADZbFH0=Rx?qFx\{1~xFP<AD_fFADYhF<0gFP<PXP_PFPnPeI0;00LFQ1`P;PXPFQ0wPaI0;RxPFPxPF19xFI0:[208xFPcP;PFQ0yP\I0;Rx/9FR}?_}F\~20QxFQ1aPdPcPFPoQ0{I0;Rx/9FR}>07F}[20TxFP]PdPFQ10PkI0;Rx00UF\{20YxFP^P]PFPpQ0rI0;Rx?qFx\{1~xFP<B0gb^FQ0s,5q;DFP<15hb00LFQ1`15ehRxPFPxPF19xFI0:[208xF15aeRx/9FR}?_}F\~20QxFQ1a15\aRx/9FR}>07F}[20TxFQ0{/5\Rx00UF\{20YxFQ0{,5kRx?qFx\{1~xFP<Q0r@0gkFP<Q0s/7i00LFQ1`Q0u/7sRxPFPxPF19xFI0:[208xFQ14,7`Rx/9FR}?_}F\~20QxFQ1aQ1C,7jRx/9FR}>07F}[20TxFQ0tQ15'7Rx00UF\{20YxFQ0xQ16'7Rx?qFx\{1~xFP<Q1B=DfFP<17fl00LFQ1`17nmRxPFPxPF19xFI0:[208xFQ0wQ11'7Rx/9FR}?_}F\~20QxFQ1aQ0y/7rRx/9FR}>07F}[20TxFQ12,7oRx00UF\{20YxFQ10Q13'7Rx?qFx\{1~xFP<ADpiFP<Q01%2q1AqF10k^Pl%2lS1b1AmFQ01%2r1ArF10`aQ13Q13#2S1c1AiFp-0Rx%ItS1d#IS1e#IS1f#IS1g#IRt#IS1h#IS1i#IR}#IS1j#IS1k#QS1l%Q}S1mQ09$1v-19<R}%QtRtQ1e#QS1eQ1GQ1:+0[S1n60b}40b3bQ0>#;$1M#}#}#}S0>#;S1o$00-0w<S1pQ1:'dS1qQ1k#IS1k#QS1r-06}S1sQ1j#QS1j-06}Q1h#QS1hQ1g#QS1gQ1f#QS1fQ1eQ1E-06}3b3b3b'e+0vQ1lQ1mQ1eQ1GQ1:60b}5bt60b}60b}Q1qQ1rQ1jQ1h-06}S1hQ1fQ1d#QS1dQ1E+0[60b}7bt3b'e+0vQ0J410Q0K%oPS1lP?PAP3%oZ@0BQADhP7%oRS1mP>PAP0PADhP:%oKS1t@0BZAPZPAPZ%o[S1uP8PAPZ%oLS1vDhDhDhQ0LPTPT20p<ES1w>1u<DRt:0WTUS1xPyQ0:#VS0:#;S1y#XS1z9]TU20`T_60XTPyPTPTPTQ03P4P4Q04AfTtUJ1tS1{PyQ0a#XS0aQ0<#XS1|+05Q1y#;#X:0u<tQ1z'^5fTPyPTPTQ1xPyQ0`#XS0`9]TUS1y20`TX60XTPyPTPTQ1{PyQ0:#V#XS1}005vQ0;#VS0;#V#X:0u<tQ0`'^5fTPyPTPTQ1xPyPTQ0_#VS0_#VS1~#XS209]TUPTQ20004tCwPyPTPTQ1{PyQ1}Q0a'^Q0;#;#X:0u<tS21Q20'^5fTPyPTPTQ1xPyPTQ1=PT204wtCwPyPTPTQ1{PyQ20Q1|,^v+05Q0<#V#X:0u<tS0</^w5fTPyPTPTQ1xPyQ1>B0WTztS2060XTS22H0VS23PyPTPTQ1{PyPTQ0`Q1z'^Q0=#XS0=:0u<t/^z+1LI0~PyPTPTQ0a,xUPyPTPTQ1},xUPyAfTzwI03I03FlFUFUFUFUFUFUFUFUQ0MQ0Nb9b:b;X6<X<<X><XC<XM<XN<X[<X\<X]<XW<XX<XY<XZ<Z0=<XBxWRQ0D/FY\~g00[Z\{S0aB1KFY89cL>[Q0D/F;\~Q0aB1KF_89cP>[%2[S24@0S[F\~Q0a15R[20tFXS25<1JZ[Q0j@0SQF\~Q0a15PR20tF;S26/5L5c_[%2LS271ALFS28'F\~Q0a15[Y20tFc<1JP[Q0pQ0p10R[[[[[[[[[[[[[^6<^<<^><^C<^M<^N<^[<^\<^]<^W<^X<^Y<^Z<`0=<^Bx^RxP61A_FQ28PPPXPhQ0sPnPbPsQ14PLQ1WP_f{Q0rPfPZPYP]P^Q0{PkQ0tQ0xQ10PpP>P7OLb8Y0RW1P:P6O2n2001000000121000000Y0QWaP:P6O2n2001000000121000000c0kc0jc0Pc0Oc0Nc0Mbuc0Fc0ibtbrbqbpboc0Ec0Bbnbmblbkbjc0Dc0Abib|b{bzbyc0Cc0@bxbwbvbsbhbAbJbLbSbTbUbVc0cc0dc0Jc0Ibab1Q1SQ1T'5Q1RQ1A;DF7qFeQ1OP6I0RQ1MP[I0RQ05Q1PQ1Q40x,8DQ1PQ1Q+1II0RQ05Q1LQ1N40x,8DQ1LQ1N+1II0RQ1DeH0sH18H1HY0LY0YP:P6O2n2001000000121000000W1Z0l<P:P6O2n200100000012110u000W1Y0\P:P6O2n2001000000121000000bdWgY0<P:P6O2n2001000000121000000W1Z0G<P:P6O2n200100000012110u000W1Y0[P:P6O2n2001000000121000000bdPhP6J0lW1PhP6DEW1P6O1b1P6O1b1W5W=WbZ0o<Z0]5P:P6O2n2001109000121107100P6PYP7O3bbbeW5WDW7Z0n<Z0>5P:P6O2n2001109000121107100P6PQP7O3b7beW520P>0>0OBHPBPG20P8?Q0CP6DP%k7S1DPBPI20PQ>S1NQ0lP:DGQ1N/6020PL8/6?20PPQ%k>S1N%28S05ASC6QS1Q20P[K93D_S1PPDP_P7P6PFD>S1O3RX0<'1[X35POQ1PQ1PP6PFD4X0<,1CX4<PMQ0H20PRP93DYS1PQ1PP6PFD4X0<S1RQ0OQ1RPS20PKL,<ZS1R,8DS1AQ1A#OS1TPFQ0QQ1AQ1P/0VX2<Q1AQ1P/06X2<Q1AQ1APFQ1APFQ1RGMQ1TQ1ADKFHP>P6FJX1JP>P6DEW1P6O1b1P6O1b1W520E>0>0OBHPBPG20E8?Q0CP6DPQ1DPBPI20EQ>S1AQ0lP:DGQ1A/6020EL8/6?20EPQQ1NQ05Q1Q20E[K93D_S1AQ1O3RX0<'1[X35POQ1AQ1AP6PFD4X0<,1CX4<PMQ0H20ERP93DYS1AQ1AP6PFD4X0<S1TQ0OQ1TPS20EKL,<ZS1T,8DS1RQ1R#OS1PPFQ0QQ1RQ1A/0VX2<Q1RQ1A/06X2<Q1RQ1RPFQ1RPFQ1TGMQ1PQ1RDKFHP>P6FJX1JP>P6DEW1P6O1b1P6O1b1W520N>0>0OBHPBPG20N8?Q0CP6DPQ1DPBPI20NQ>S1RQ0lP:DGQ1R/6020NL8/6?20NPQQ1NQ05Q1Q20N[K93D_S1RQ1O3RX0<'1[X35POQ1RQ1RP6PFD4X0<,1CX4<PMQ0H20NRP93DYS1RQ1RP6PFD4X0<S1PQ0OQ1PPS20NKL,<ZS1P,8DS1TQ1T#OS1APFQ0QQ1TQ1R/0VX2<Q1TQ1R/06X2<Q1TQ1TPFQ1TPFQ1PGMQ1AQ1TDKFHP>P6FJX1JP>P6DEW1P6O1b1P6O1b1W520?>0>0OBHPBPG20?8?Q0CP6DPQ1DPBPI20?Q>S1TQ0lP:DGQ1T/6020?L8/6?20?PQQ1NQ05Q1Q20?[K93D_S1TQ1O3RX0<'1[X35POQ1TQ1TP6PFD4X0<,1CX4<PMQ0H20?RP93DYS1TQ1TP6PFD4X0<S1AQ0OQ1APS20?KL,<ZS1A,8DS1PQ1P#OS1RPFQ0QQ1PQ1T/0VX2<Q1PQ1T/06X2<Q1PQ1PPFQ1PPFQ1AGMQ1RQ1PDKFHP>P6FJX1JP>P6DEW1P6O1b1P6O1b1W520D>0>0OBHPBPG20D8?Q0CP6DPQ1DPBPI20DQ>S1PQ0lP:DGQ1P/6020DL8/6?20DPQQ1NQ05Q1Q20D[K93D_S1PQ1O3RX0<'1[X35POQ1PQ1PP6PFD4X0<,1CX4<PMQ0H20DRP93DYS1PQ1PP6PFD4X0<S1RQ0OQ1RPS20DKL,<ZS1R,8DS1AQ1A#OS1TPFQ0QQ1AQ1P/0VX2<Q1AQ1P/06X2<Q1AQ1APFQ1APFQ1RGMQ1TQ1ADKFHP>P6FJX1JP>P6DEW1P6O1b1P6O1b1W520M>0>0OBHPBPG20M8?Q0CP6DPQ1DPBPI20MQ>S1AQ0lP:DGQ1A/6020ML8/6?20MPQQ1NQ05Q1Q20M[K93D_S1AQ1O3RX0<'1[X35POQ1AQ1AP6PFD4X0<,1CX4<PMQ0H20MRP93DYS1AQ1AP6PFD4X0<S1TQ0OQ1TPS20MKL,<ZS1T,8DS1RQ1R#OS1PPFQ0QQ1RQ1A/0VX2<Q1RQ1A/06X2<Q1RQ1RPFQ1RPFQ1TGMQ1PQ1RDKFHP>P6FJX1JP>P6DEW1P6O1b1P6O1b1W520H>0>0OBHPBPG20H8?Q0CP6DPQ1DPBPI20HQ>S1RQ0lP:DGQ1R/6020HL8/6?20HPQQ1NQ05Q1Q20H[K93D_S1RQ1O3RX0<'1[X35POQ1RQ1RP6PFD4X0<,1CX4<PMQ0H20HRP93DYS1RQ1RP6PFD4X0<S1PQ0OQ1PPS20HKL,<ZS1P,8DS1TQ1T#OS1APFQ0QQ1TQ1R/0VX2<Q1TQ1R/06X2<Q1TQ1TPFQ1TPFQ1PGMQ1AQ1TDKFHP>P6FJX1JP>P6DEW1P6O1b1P6O1b1W520I>0>0OBHPBPG20I8?Q0CP6DPQ1DPBPI20IQ>S1DQ0lP:DGQ1D/6020IL8/6?20IPQQ1NQ05Q1Q20I[K93D_S1DQ1O3RX0<'1[X35POQ1DQ1DP6PFD4X0<,1CX4<PMQ0H20IRP93DYS1DQ1DP6PFD4X0<S1OQ0OQ1OPS20IKL,<ZS1O,8DS0lQ0l#OS1TPFQ0QQ0lQ1D/0VX2<Q0lQ1D/06X2<Q0lQ0lPFQ0lPFQ1OGMQ1TQ0lDKFHP>P6FJX1JP>P6DEW1P6O1b1P6O1b1W5P5PBP0P9PBQ0bQ00P5P<PBQ0^Q0dn200110u00012010v10120K8?S0^n0100000020000Q0^20KL8S0^Q0^Q0^Q0^20KPQS0^Q0^n01105000810106101023010t10810r3010t10810r3010t10810r3010t10810r4010:10h10210s4010:10g10e102=:BHP5Q07Q08PDPYP0PDPYP3P6PFD>DBX0<,12[^4<^35P5PBP:P9PBQ0bQ00P5P<PBQ0gQ0dn200110u00012010v10120KP7S0dn0100000020000Q0d20KR0S0dQ0dQ0dQ0d20K[?S0dQ0dn01105000810106101023010t10810r3010t10810r3010t10810r3010t10810r4010:10h10210s4010:10g10e1021N?05:B%2?S0dPCP6P>PDPZPKP3PDPZP8P6PFD>I0JCzX0<'1]5]=P?Q0@Q08PDP_Q0BPDP_P3P6PFD>S0BDBX0<,12[^4<^35P9PB%T:#uS0@Q0@$0|S0@80AEQ0@/tN+0mQ00P5P<PBQ0g%T3#y=rEW9n:6n200110u00012010v101%Y:-0KPn01000000200001N>?S0g5:BQ0cP<%y6P<%u:@0AE61t6N+0mP920>96%u7@0AE:1t:N+0m=:96P9%u0@0AE31t3N+0m=:96P9PBP:Q00P5P<PBQ0oArE>W9n:6n200110u00012010v101Q0I-0KXS0In01000000200001N[RS0o5:BQ24PCP6PZPDP^20rcPS0cPDP^PYP6PFGsCzX0<'1]5]PP:%u3@0AE71t7N+0mS0@#jQ00P5P<PB%p_1?E?S0b/7W9n:6n200110u00012010v1011NRKS075:B%u?@0AE0S0^1t0NS0l<1s:Q0^#jQ0l#j'FQ01%u>Q0b+0{#j1t?N#j%2ZS0bASC6YS0lPDPb20rdKS0^PDPbP_P6PFD>DBX0<'1P6%uQ@0AE8#j1tQN#jQ0120{:6#j107:[S1T10:620{7:#jS1O[Q1O1037[21r:6P:n2001000000120000000XQ<XG<Q1T^Q<^G<P6%uKS1T1?EPS1OP7O3Q1TQ1O'0Q011t:6#j1L7:[S1O1L:61t7:#jS1T[Q1T1L37[21q:6P:n2001000000120000000XQ<XG<Q1O^Q<^G<P6PRPNP3O31LRN%uZ$1pQ24eQ24%p\PBQ0fQ0{=WB6Q00P5P<Q0r=WB6Q0hQ08Q0vA3Dn3P6PFD4X0<,12[^4<^35Q00P5P<PBP7ArE]W9n:6n200110u00012010v101Q0{/N\5:BQ0{#2S00PCP6PkPDPfPj%YePDPfQ0rP6PFD>I0JCzX0<'1]5]D]7P:AWB`1Q0mQ08Q0zA3Do3P6PFD4X0<,12[^4<^35ArE^W9n37Q0sQ0r'N5:BPBPG1?Eb>0k3WS0m,N0Q0uQ0s'NP6I13Q0mQ0s'0PBPIArEhW9n?0Q0u,N`P:I1@16?`16>jP81?E\>0k8WS0mQ0t'0Q0x#2S0zPCP6PfQ1000r`93DgS0h1<g7>0nD6<0yFCzX0<'1[X351?Ea>0k>W/0jP<Q0mQ0hPDPgPPP6PFD>S0m5ROX0<,1CX4<P?PQP8Q0i-0>BO3Q05Q1QQ0|A3DqLP6PFD4X0<'1Q01Q0jQ0kPDPgQ10Q0mDBX0<$0i1?Ek>0kLWPCP6PPQ0r=rEWPDPlPp%YjPDPlPKP6PFD>I0JDgX0<'mP6%2PASC6RS0mPDQ11PgPDQ11P[P6PFD>DBX0<$0iQ02P<PCP6P[PDPrPlPDPrPZP6PFGsCzX0<1?E`>0k[WPCP6PZArEjWPDQ12Pm%YnPDQ12PYP6PFD>I0JDgX0<'mP6Q0lPDQ13Q11PDQ13P_P6PFD>DBQ01AS2:_PDPiPrPDPiPXP:PFGs1?Ef>0kXWPCP6P;ArEnWPDQ14Q13Q10#YPDQ14PcP6PFD>I0JDgX0<'mP6Q0e?S3;PDQ1CPiPDQ1CPdP0PFGsPEQ0y%yoS0l#CQ0yQ0l'0S0leS02Q0l%TgS0k#CQ10Q0k'0S0keS0jQ0k&0FlS0|Q1b1L=@S1QQ11#TS0h#2[[S0vQ0JQ0KPAQ0LQ1w:0WTUS0fQ0MQ0Nb9b:b;Q1[P6b8bEb@b?Q02Q0lQ0jQ0kQ0|Q0vQ0JQ0K%o:S0vQ0LPTQ1>PyQ1>H0VQ0MQ0Nb9b:b;X6<P2\C^6<P6PqQ0rO2b8bEb@b?H1oQ0y,?E#`ArEoW-1E]PCP6P^Q10=rEWPDQ1BQ1C%YlPDQ1BPbP6PFD>I0JDgX0<Q10#yS0|#CQ0|,0oS0|eQ0|%TlS0|#CQ0|,0pS0|eQ0|&0Fm%2mQ1Q%TrS0|#2[[20fEqQ1[%2g1?ElS0k#`[[B0dEm:VuX7|1?EmS0j#2\u^7|Q1GQ1F'eQ0J+12Q0KQ1;Q1I80B:Q0LPTPTQ0fPyPTQ1J9]TUS1;PyPT204UwI0~PyPTQ1>PyPTQ1;Py20p<WS0l-05w,^z9]TUFlFUQ0MQ0Nb9b:b;X6<X<<X><Q1[Q0e%`3[[%20S02170W-1E3[\2[^6<^<<^><P6PmQ0jP\P7P_P`O6b8bEbIbAb@b?Q16Q1453DP<Q1L$0oQ1MQ1M;_F1?EpS1M%yqS1L#CQ1L,0pS1LeQ1LQ0h#CQ0h,0gS0heQ0hQ1VQ1B'<S0h,8DS1L#CQ1L,03S24eQ24Q12$0FQ12#2S24Q1Q%TiS1O#2[[Q1ZQ1\Q1]Q1_20fErQ1[Q24Q13,?ES1T#`[[B0dEi:VuX7|1?EiS24#2\u^7|Q0JQ0KQ1<Q0LPTPTQ0fPyPTQ1=PyB0WTUzS1<H0VS1DPyQ1DFUQ0MQ0Nb9b:b;X6<X<<S1DQ1[%27S1A%`7[S1P[Q1P[^6<^<<S1PP6PiQ24P7PnO4b8bEbIbAbJbLbFb@b?61D:Q1M,9:S1RQ1RQ1M3_P71?EqS1R%ygS1M#CQ1M,0qS1MeS1SQ1MQ0|#CQ0|,0lS29eS2:Q29Q1WQ1753DS2;#CQ2;,00S2<eS2=Q2<Q13$0FS2>Q1cQ1Q%Ts#2[[S2?Q1ZQ1\Q1]Q1_Q0JQ0KQ0vQ0LPTQ1>20`T360XTPyQ1>H0VQ0MQ0Nb9b:b;X6<XBx1FC:P2[^6<^BxP6Q28PLPQO3b8bEbIbAbFb@b?Q1SQ1MQ2:Q29Q2=Q2<Q2>Q2?Q1ZQ1\Q1]Q1_Q12-0fEQ1[Q1cQ24#`[[B0dEs:VuX7|1?EsS1c#2\u^7|Q1DQ1PP6PsQ1cP7Q0wO4b8bEbIbAbJbLbFb@b?H1nQ1R,97/L7P<PCP6PaQ0k/7WPDQ1WQ17Q12#YQ1W=3D\S1R?D6FI0JDgX0<1?EgS1c:16P3S1PQ1PQ1PQ1c/7W81Ce+11PDQ1VQ1B%YrPDQ1VPaQ1PPFD>S1PI0JS1c%ylS1D#CQ1D,0gS1DeS24Q1DQ12#TS2?#CQ2?,0mS2?eS2>Q2?Q1XQ1U53DS2<#CQ2<,0?S2<eS2=Q2<Q11,?ES29,i>Q0D1?ErS2:#2Q12,?ES12,vQ[[&0Fs%2sQ1QQ1C#T#2[[Q1ZQ1\Q1]Q1_ft/<`>0nDXS1M/iFS1SQ1M#2Q1YfvS1MQ0t'<>0nDc/vF[[S2820fEsS2@Q1[Q14#2S2AQ1C,?E#`[[S1CQ15>0dE:VuX7|S2BQ15,?ES2C#2\u^7|S2DQ1fQ1n'eQ1eQ1F'eQ0J410Q0K%o>@0B0AP7PAP:%o?:0BA3DhQ0LPTPTQ1|9]TUS1|PyPTA]TUvS1FPyQ1=H0VPyPTPT20`TQPT204wvCwPyPTQ1|20`TL60XTPyPTB0WTUvS1|PyPTQ1KPyPTPTQ0_#X,xUPyPTQ1@PTQ1?Q1JQ0l-05v'^'xCwI03FlFlFUQ0MQ0Nb9b:b;X6<X<<X><XC<XM<XN<XBxXRxQ0dQ02Q0e[[B0S870Q05/FL%`>Q02?S0>Q2715>8S0dQ0d17LW81CQ+11[[[[[[^6<^<<^><^C<^M<^N<^Bx^RxP61AZFQ2C,9ZS27#2PZQ15Q2CQ0xQ27P]P8PRP[PYPXQ10O>b8bAbJbLbSbTbUbVbFb@b?Q1L21mDrS27,8DS2C+0cQ1RQ0k:16K0;DFS1R,06X2<Q0|Q2;00c6Q1R'0X2<Q24Q1DQ2>Q2?Q2=Q2<&0Fi%2iQ1QQ14#T#2[[Q1ZQ1\Q1]Q1_Q0JQ0KPAQ0LQ1xQ0MQ0Nb9b:b;P~P6b8bEbIbAbFb@b?1A=@S2<e:1Dr@Q1b@0Sl@S1beQ1b17Fm$0|S1b#CQ1b,0lS1beQ1bQ13/9FS1b#CQ11Q1b'0S1beQ1bfpS1bQ1V53DS2=#CQ2=,0>S2=eQ2=Q2:,i8Q05Q12#2Q1T,vL[[Q1ZQ1\Q1]Q1_Q1SQ28Q2@Q1CQ2BQ2DQ17/iFQ17#2S2DQ1YQ1V/vF[[Q19-06}S19Q1:'eQ0J+12Q0KPAP7Q1HP:Q1IDhQ0LPTQ1y20`T>60XTPyPTQ1<PyPTQ1;PyPT205tw=fTzPy205tz=fTwFlFlQ0MQ0Nb9b:b;X6<X<<X><XC<XBxQ0e/F0%`:Q0217F0S0e/03Q0e/0?[[[[^6<^<<^><^C<^BxP61AYFPYQ16Q1BQ16,?EPZP_PpPlO9b8bAbJbLbSbTbUbVbFb@b?Q0k=cFmS0keQ0kP<Q0j,7FS0k20c>6Q1b=3DkS1bQ29:16[>;DFS29'0Z0?<Q0j,9?,7?Q29,06X2<Q1XQ0{'<S29$0oQ29,8DS29Q29;_FQ1bP<Q2:,98P<AD:YFS2:15_:=D7F9c6:Xc<P<PQB0SC6FS1bXc<P8Q2:PPJ0lQ2:Q2:;_FfsS2:Q0u53DS29#CQ29,07S29eQ29%ysRs#C10isRsePsQ16#TRs#CQ14/0sRsePsQ1MQ2:53DRs#C10RsRsePsQ17$0FQ2DQ1QQ1V#T#2[[178]Rs/iF%2sQ1Y17Lb/vF[[Q1ZQ1\Q1]Q1_B0CPhLRs/iF%2sQ1YB0CRaK/vF[[Q1U-0fEQ1[Q1V#2Q1W,?E#`[[Q1X>0dE:VuX7|Q1X,?E#2\u^7|17[\00LFQ1`Q0{,7ZRsPFPsPF19sFI0:[208sF17YkS1X/9FRs?_sF\~Q1X00QFQ1aQ0r,7_S1X/9FRs>07Fs[Q1X00TFQ0s,7XRs00UF\{20YsFQ0u,7;Rs?qFs\{1~sFP<ADc`FP<B0Cdjc00LFQ1`Q0t>0C]dRsPFPsPF19sFI0:[208sFQ0x>0C^]S0x/9FRs?_sF\~Q0x00QFQ1aB0Cbf^S0x/9FRs>07Fs[Q0x00TFB0ChnbRs00UF\{20YsFQ0w>0CehRs?qFs\{1~sFP<Q0y/5e=DaFP<p+01A00L@A:<@=Rs$1:p+01BR{P@P{P@%T{I0:[208{@Q2<p+01CS0x#TR{?_{@[Q0x00Q@1A@=p+01DS0x#TR{>07@{[Q0x00T@p+01ER{00U@\s20Y{@p+01FR{#T/0{\s1~{@P<p+01GR{#TP<Q01%2j1AjFAcYjQQ0tQ0z1AfFQ01p+01IRj#21Aj@AccnRPop+01KS0x#2p+01LRj/A@Q01%2o1?Ej,AoQ10=cb_Pm%2pp+01O,?E,AqQ01%2a1AaFAc\ldPqQ001AkFQ1[Q0wP6P{O2WKQ1[p+01U,?E#`]KQ1k#IR{#I#IRk#QRqQ1rQ1:+0[60b}RlQ1q%IkRk#IR\#IS1r#IRp#I#Q%Q\R\%QkRkQ1E%Q{R{-06}RjQ1i#Q-06}Q1fQ18-06}+0[3b3b3b'e+0vRs%QpQ1jQ1hQ193b'eRpPpPsPpPsQ1pQ1jQ1:'dS19'dQ1jAb\kjQ1jQ1gQ1G+0['d40^'e-0vlRlQ1sQ1:5bqQ1~$1k$0a$0a$0a$0a$0a$0a$0aRq$00-0w<RjQ1r#Q206}k;b{R{Q1j'd'dQ1o#;$17$1j$1M#}#}#}$00-0w<P<219<WQ09219<=H1i-1h<RWQ1:'dQ0>$00-0w<Rk1dW{Q1e,dWQ1d,dW%}q#}#}#}$00-0w<Q19Q1eQ1j'dQ1dQ1d'd,dk60^j40^60^k60^k40^40^'e+0vRkPlPkPkPlPkPlPsPpPsPpPpPsPlPkPlPkQ0JI0eI0eI0eI0eI0eI0eQ0KQ1tP[PAP0PADhP7Q1uPQPAP>Q1lDhP:Q1m@0B8AP?PAP3Q1v@0B[ADhDhQ0LPTPTAfTvUPyQ0_#;#XRAQ0=5fTPyPTPTB0WTvUPyB0WTvA20`TY60XTPyPTPTQ1|PyPTA]TUARkPT204AvCwPyPTPTQ1xPyPTQ1;PTQ1J004tCwPyPTPTQ1{PyQ1}Q0;#XRl/^w+05Q21Q1J'^5fTPyPTQ23PyPTPTQ1{PyPTQ1}Q0</^z81BlI0~PyPTPTQ1w9]TURlPyPTPTQ03P4P4Q04I1gR4PyQ1yH0VPyPTPTQ0fPyQ0`:0WTUPyPTPTPlPyPTP4PyPT1xUtI0~PyPTPTQ0=9]TUPyPTQ1FPyPkH0VPyPTPTQ0:#XRk01LAPyPTPT204kvPyPTPT1xUkPyPTPTQ1z,xwPyPTPTQ0`-04wPyPTQ1=PyPTQ20PyPTQ1>PyPTQ1z=fTzPyPTPTQ0`:1BvkPy205zwQ1J5fTI03FlFlI03I03I03I03I03FUFUFUFUFlFUFUFUFUFUQ0MQ0Nb9b:b;X6<X<<X><XC<XM<XN<X[<X\<X]<XW<XX<XY<XZ<XBx&1;310PK[1A0=B1f?KY[%`?A_RR>[Q0D@0S>F\~R~Q0a15K>Q25/585c[[Q0aQ26/589cY[[Q0b\u\|Q1[%`Z[Q1^\|Q0}Q0bQ0~[[10Yd1A_YQ0p1LY]1A_dQ0p1AXF%2;10acAcbheAc]^b[[[[[[[[[[[[[[[\~[[[[[^6<^<<^><^C<^M<^N<^[<^\<^]<^W<^X<^Y<^Z<^BxP6&1e;PaP`p+01ZP;PiQ17frp+01V,?Ep+01WP@PeQ13Q0uPdP^PbQ0rQ0sPfPnQ0wP:Q10PgPmPPPKQ15P>P8P7P3Q1VQ0xOSb8bJWuWtP:P6O2n2001000000121000000WrWqP:P6O2n2001000000121000000WpWoP:P6O2n2001000000121000000WnWmP:P6O2n2001000000121000000c0Fc0Bblbkbjbib|c0Ec0Ab{bzbybxbwc0Dc0@bvbsbhbab1bAbJbLbSbTbUbVbFb@b?c0bb}PQPPI0Rc0Cc0Hc0SQ0k-0c?P?PmQ11#yRg#C10mgRgeRmPgQ1O#CQ1O,0rRneRfPnfqQ1W53DR@#C108@R@eREP@Q14$0FRiQ2AQ1QQ15#T#2[[R`Q1ZQ1\Q1]Q1_Q0JQ0KQ0vQ0LPTQ1>PyPT20p<N9]TzPyPTQ1>PTQ0?-0p<-04zCwFlQ0MQ0Nb9b:b;X6<1L:NQ1AQ0?80S7[\C^6<P6Q14Q0yPoO3b8bEbIbAbFb@b?PmPgPfPnPEP@PiP`Q1ZQ1\Q1]Q1_Q0JQ0KQ0vQ0LPTQ22PyQ22H0VQ0MQ0Nb9b:b;X6<Q1bB0S2:F[^6<P6PRPKO2b8bEbIbAbFb@b?H1dI0RQ11P6J0lb1c0UQ0|-0c3Q1P'0eQ1LQ0|+0cQ1P'0eQ2C&1crI0RQ06Q0hQ2740x,8DQ0hQ27+1bI0RQ1ceH0sH18c0Xc0Wb}bcH1Hc0VWgY0<P:P6O2n2001000000121000000W1Z0G<P:P6O2n200100000012110u000W1Y0ZP:P6O2n2001000000121000000bdQ0tP6J0lW1Q0tP6DEW1P6O1b1P6O1b1W5WDW7Z0m<Z0>5P:P6O2n2001109000121107100P6Q0{PRO3b7bec0Tb~b1c0;b1W~Y0;P:P6O2n2001000000121000000bPW5WPQ0@g014W5:9PBP_Q0PQ07H0GPBPGQ0IQ0oP6I13%kRRrPBPIQ0F,@;Ry1NZ[RTP:DG16yZQ0c/6YQ0^%k_RyQ0pQ0q20rbZ93DaR`PDPaP7P6PFD>Ri3RX0<'1[X35%kYR@POP`P`P6PFD4X0<,1CX4<PMQ0H20r^[93DeR`P`P6PFD4X0<REQ0OPEPSB1ah]RRE,8DRn%OnRfPFQ0QPn10`VX2<Pn10`6X2<PnPnPFPnPFPEGMPfPnDKFHP_P6FJW1P_P6DEW1P6O1b1P6O1b1W5WPn0110500020101P6P0O2bPbOc0fc0?W5W=XQ<P6O1Q0RQ0TQ08PDP_Q0VQ0BDBX0<,12[^4<^35PBPP&02:Q0gH0GPBPGQ0S,@K1N8>P6DPQ1NPBPIQ0U,@RRnQ0iP:DG16nQQ0V,@[/6LQ0W,@Z%kPRnQ0mPDPdPXQ0YCaRfA3Dd7P6PFD4X0<,mK[X35%kLPOPfPfP6PFD4X0<,1CX4<PMQ0HPDPcP_Q0ZCaRfPfP6PFD4X0<REQ0OPEPSQ0X:0];YRE,8DR`%O`RgPFQ0QP`10fVX2<P`10f6X2<P`P`PFP`PFPEGMPgP`DKFHPPP6FJW1PPP6DEW1P6O1b1P6O1b1W5W=WGP6O1Q0[A=037R`=WB1Q08PDPdA=>?0RgPDPdP3P6PFD>REDBX0<,12[^4<^35PBPZA=37:1NPLRfH0GPBPG1@Y`Q0nP6DPPnPBPIA=?03,@_R`Q07P:DG16`R1@Xg/6[A=8>?,@;%kZRg%2YR`ASC6_RmPDPhP]A=PLQCaRoPDPhP7P6PFD>RN3RX0<'1[X35%k[RzPOPoPoP6PFD4X0<,1CX4<PMQ0HPDPbPdA=LQ8CaRoPoP6PFD4X0<RxQ0OPxPSA=Q8>:0]^cRx,8DR~%O~R|PFQ0QP~10oVX2<P~10o6X2<P~P~PFP~PFPxGMP|P~DKFHPZP6FJW1PZP6DEW1P6O1b1P6O1b1W5W=X_5X^5WHP7P:P6O3Q0[A\037R~=WB1Q08PDPdA\>?0R|PEDBX0<,12[^4<^35PBPZA\37:PfH0GPBPG1@Y~Q0nP6DPPnPBPIA\?03,@_R~Q07P:DG16~R1@X|/6[A\8>?,@;PDPhP]A\PLQCaR|=RmNX0<,1`\gX35POP|P|P6PFD4X0<,1CX4<PMQ0HPDPbPdA\LQ8CaR|P|P6PFD4X0<R~Q0OP~PSA\Q8>:0]^cR~,8DRx%OxRoPFQ0QPx10|VX2<Px10|6X2<PxPxPFPxPFP~GMPoPxDKFHPZP6FJX1zPZP6DEW1P6O1b1P6O1b1W5W=X_5X^5WHP7P:P6O3g06[JRxA[037Ro=WB1Q08PDPdA[>?0R~PEDBX0<,12[^4<^35PBPZA[37:PfH0GPBPG1@YoQ0nP6DPPnPBPIA[?03,@_RoQ07P:DG16oR1@X~/6[A[8>?,@;PDPhP]A[PLQCaR~=RmNX0<,1`\gX35POP~P~P6PFD4X0<,1CX4<PMQ0HPDPbPdA[LQ8CaR~P~P6PFD4X0<RoQ0OPoPSA[Q8>:0]^cRo,8DR|%O|RuPFQ0QP|10~VX2<P|10~6X2<P|P|PFP|PFPoGMPuP|DKFHPZP6FJX1zPZP6DEW1P6O1b1P6O1b1W5W=X_5X^5WHP7P:P6O3AZ037R|=WB1Q08PDPdAZ>?0RuPEDBX0<,12[^4<^35PBPZAZ37:PfH0GPBPG1@Y|Q0nP6DPPnPBPIAZ?03,@_RnQ07P:DG16nR1@Xu/6[AZ8>?,@;PDPhP]AZPLQCaRu=RmNX0<,1`\gX35POPuPuP6PFD4X0<,1CX4<PMQ0HPDPbPdAZLQ8CaRuPuP6PFD4X0<RgQ0OPgPSAZQ8>:0]^cRg,8DR`%O`RNPFQ0QP`10uVX2<P`10u6X2<P`P`PFP`PFPgGMPNP`DKFHPZP6FJX1zPZP6DEW1P6O1b1P6O1b1W5W=X_5X^5XHxP7P:P6O3Q0RQ0RP?P0P3P7C{Rz=WB1Q08PDP^P8P>P?P0C{R`PDP^P3P6PFD>RNDBX0<,12[^4<^35PBP_P0P3P7P:C{Q07H0GPBPG1@XzQ0oP6DPPrPBPIP>P?P0P3C{Rz,@;RgPTP:DG16gZ1@c`/6YPQP8P>P?C{Rg,@dQ0pQ0qPDPaPbPKPPPLPQC{RuCaRm;RiX0<'1\yX35POPmPmP6PFD4X0<,1CX4<PMQ0HPDPeP^PPPLPQP8C{RmCaRnPnP6PFD4X0<R|Q0OP|PSPLPQP8P>C{R|:0]h]Rf,8DRE%OERoPFQ0QPE10nVX2<PE10n6X2<PEPEPFPEPFPfGMPoPEDKFHP_P6FJX1@P_P6DEW1P6O1b1P6O1b1W5W=XO5WGY0hXf9P3P7P:P6O4Q0RQ0RP?P0P3P7H01RE=WB1RoQ08PDP^P8P>P?P0H01RfPNDBX0<,12[^4<^35PBP_P0P3P7P:H01Q07H0GPBPG1@XEQ0oP6DPPrPBPIP>P?P0P3H01Rr,@;R;PTP:DG16;Z1@cf/6YPQP8P>P?H01Rc,@dQ0pQ0qPDPaPbPKPPPLPQH01RbCaRa;RiX0<'1\yX35POPaPaP6PFD4X0<,1CX4<PMQ0HPDPeP^PPPLPQP8H01R^CaRePeP6PFD4X0<RaQ0OPaPSPLPQP8P>H01Ra:0]h]Rh,8DR]%O]RyPFQ0QP]10eVX2<P]10e6X2<P]P]PFP]PFPhGMPyP]DKFHP_P6FJX1@P_P6DEW1P6O1b1P6O1b1W5W=WGZ0e<Y0gXf9P3P7P:P6O4n0110701081110011102311031041053110310410531103104105311031041054110:10h1021074110:10g10e102P0P6O2W5n01104010:01010101010101010101P6O1W5X4<X35W=XO5WDXK5WHQ0[Q0\Q0]A\>?3=WB1PBPGA\8>0PHP6DPQ0APBPIA\Q8?R_Q0CP:DG16_3A\LQ>/60A\PL8Q0DQ0EA\[RP93DYR_PDPYP7P6PFD>R@3RX0<'1\JX35Q0GPOP_P_P6PFD4X0<,1CX4<PMQ0HA\RKL93DZR_P_P6PFD4X0<R]Q0OP]PSA\KPQ,<[R],8DRy%OyRhPFQ0QPy10_VX2<Py10_6X2<PyPyPFPyPFP]GMPhPyDKFHP?P6FJW1P?P6DEW1P6O1b1P6O1b1W5X4<X35W=XO5WDXK5WHQ0\Q0]A[>?3=WB1PBPGA[8>0PHP6DPQ0APBPIA[Q8?RyQ0CP:DG16y3A[LQ>/60A[PL8Q0DQ0EA[[RP93DYRy;R@X0<'1\JX35Q0GPOPyPyP6PFD4X0<,1CX4<PMQ0HA[RKL93DZRyPyP6PFD4X0<RhQ0OPhPSA[KPQ,<[Rh,8DR]%O]R_PFQ0QP]10yVX2<P]10y6X2<P]P]PFP]PFPhGMP_P]DKFHP?P6FJW1P?P6DEW1P6O1b1P6O1b1W5X4<X35W=XO5WDXK5XHxQ0\Q0]AZ>?3=WB1PBPGAZ8>0PHP6DPQ0APBPIAZQ8?R]Q0CP:DG16]3AZLQ>/60AZPL8Q0DQ0EAZ[RP93DYR8;R@X0<'1\JX35Q0GPOP8P8P6PFD4X0<,1CX4<PMQ0HAZRKL93DZR8P8P6PFD4X0<R>Q0OP>PSAZKPQ,<[RQ,8DR>%O>R]PFQ0QP>108VX2<P>1086X2<P>P>PFP>PFPQGMP]P>DKFHP?P6FJW1P?P6DEW1P6O1b1P6O1b1W5X4<X35W=XO5WDXK5XHxQ0RQ0RQ0]AWBz1PBPGP`PHP6DPQ0APBPIPgQ0CP:DG16g316|0PmQ0DQ0EP[PRPKPPC{93DYRY;R@X0<'1\JX35Q0GPOPYPYP6PFD4X0<,1CX4<PMQ0HPRPKPPPLC{93DZRYPYP6PFD4X0<R@Q0OP@PS1<[uRu,8DR@%O@RmPFQ0QP@10YVX2<P@10Y6X2<P@P@PFP@PFPuGMPmP@DKFHP?P6FJW1P?P6DEW1P6O1b1P6O1b1W5X4<X35WDXK5WfY0qZ0p9Q0RQ0RPBPGPrPHP6DPQ0APBPIPfQ0CP:DG16f316c0PaQ0DQ0EPRPKPPPLH0193DZRLA3DZ7P6PFD4X0<'1\JX35Q0GPOPLPLP6PFD4X0<,1CX4<PMQ0HA3D[bRbPbP6PFD4X0<R[Q0OP[PS1<R^R^,8DRD%ODRRPFQ0QPD10bVX2<PD10b6X2<PDPDPFPDPFP^GMPRPDDKFHP?P6FJW1P?P6DEW1P6O1b1P6O1b1X5oX4<X35Y0aZ0_<Y0`Z0^9P6N:1^X`5Y0Ko"). Qed.

#[using="Type"] Lemma deand_vars : forall bnd e e' s, deand e = (e', s) -> AP.expr_vars_lt bnd e = true -> AP.expr_vars_lt bnd e' = true.
Proof.
  intros bnd e. induction e as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|u w sx a IHa|bk bo bn bw];
    intros e' s Hd Hv; try (cbn [deand] in Hd; injection Hd as <- <-; exact Hv).
  cbn [deand] in Hd. fold (deand a) (deand b) in Hd.
  pose proof Hv as Hv0.
  cbn [AP.expr_vars_lt] in Hv. apply andb_prop in Hv as [Hva Hvb].
  destruct op; try (injection Hd as <- <-; exact Hv0).
  - destruct (deand a) as [a' s1] eqn:Ha. destruct (deand b) as [b' s2] eqn:Hb. injection Hd as <- <-.
    cbn [AP.expr_vars_lt]. rewrite (IHa a' s1 eq_refl Hva), (IHb b' s2 eq_refl Hvb). reflexivity.
  - destruct b as [m| | | | | | |]; try (injection Hd as <- <-; exact Hv0).
    cbv zeta in Hd.
    destruct (Z.eqb _ _ && Z.leb _ 48)%bool; [|injection Hd as <- <-; exact Hv0].
    destruct (deand a) as [a' s0] eqn:Ha. injection Hd as <- <-. exact (IHa a' s0 eq_refl Hva).
Qed.

#[using="Type"] Lemma xb2_sound : forall E M k e lo hi, know_ok SEGS E M k -> xb2 k e = Some (lo, hi) ->
  lo <= bv_unsigned (edenot E e) <= hi.
Proof.
  intros E M k e lo hi HK H. unfold xb2 in H.
  set (plain := match xlo1 k e, xhi1 k e with Some lo, Some hi => Some (lo, hi) | _, _ => None end) in H.
  assert (HP : forall lo hi, plain = Some (lo, hi) -> lo <= bv_unsigned (edenot E e) <= hi).
  { intros l h Hp. unfold plain in Hp.
    destruct (xlo1 k e) as [l1|] eqn:H1; [|discriminate]. destruct (xhi1 k e) as [h1|] eqn:H2; [|discriminate].
    injection Hp as <- <-. split; [eapply xlo1_sound; eassumption | eapply xhi1_sound; eassumption]. }
  destruct (deand e) as [e' s] eqn:Hd.
  destruct (deand_sound E e e' s Hd) as [Hs [rho [Hrho Ee]]].
  destruct (Z.eqb s 0); [exact (HP lo hi H)|].
  destruct (xlo1 k e') as [lo'|] eqn:H1; [|exact (HP lo hi H)].
  destruct (xhi1 k e') as [hi'|] eqn:H2; [|exact (HP lo hi H)].
  destruct (Z.leb s lo') eqn:Hsl; [|exact (HP lo hi H)]. apply Z.leb_le in Hsl.
  pose proof (xlo1_sound E M k e' lo' HK H1) as L1. pose proof (xhi1_sound E M k e' hi' HK H2) as L2.
  pose proof (u64_range (edenot E e')) as R'.
  assert (Hue : bv_unsigned (edenot E e) = bv_unsigned (edenot E e') - rho) by (rewrite Ee; apply Z.mod_small; lia).
  destruct plain as [[l0 h0]|].
  - specialize (HP l0 h0 eq_refl). injection H as <- <-. lia.
  - injection H as <- <-. lia.
Qed.

#[using="Type"] Lemma xlo2_sound : forall E M k e lo, know_ok SEGS E M k -> xlo2 k e = Some lo -> lo <= bv_unsigned (edenot E e).
Proof.
  intros E M k e lo HK H. unfold xlo2 in H. destruct (xb2 k e) as [[l h]|] eqn:Hb; [|discriminate].
  injection H as <-. exact (proj1 (xb2_sound E M k e l h HK Hb)).
Qed.

#[using="Type"] Lemma xhi2_sound : forall E M k e hi, know_ok SEGS E M k -> xhi2 k e = Some hi -> bv_unsigned (edenot E e) <= hi.
Proof.
  intros E M k e hi HK H. unfold xhi2 in H. destruct (xb2 k e) as [[l h]|] eqn:Hb; [|discriminate].
  injection H as <-. exact (proj2 (xb2_sound E M k e l h HK Hb)).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma residue_fact_sound : forall E E' M M' k e ne,
  know_ok SEGS E M k ->
  edenot E' ne = edenot E e ->
  (forall e' s, deand e = (e', s) -> edenot E' e' = edenot E e') ->
  know_ok SEGS E' M' (residue_fact k e ne).
Proof.
  intros E E' M M' k e ne HK Hne Hag. unfold residue_fact.
  destruct (deand e) as [e' s] eqn:Hd. destruct (Z.ltb 0 s) eqn:Hs; [|constructor].
  destruct (xlo1 k e') as [lo'|] eqn:H1; [|constructor]. destruct (xhi1 k e') as [hi'|] eqn:H2; [|constructor].
  destruct (Z.leb s lo') eqn:Hsl; [|constructor]. apply Z.leb_le in Hsl.
  constructor; [|constructor]. cbn [kentry_ok]. unfold esub. rewrite mkAlu_denot, u_sub64, Hne, (Hag e' s eq_refl).
  destruct (deand_sound E e e' s Hd) as [Hs0 [rho [Hrho Ee]]].
  pose proof (xlo1_sound E M k e' lo' HK H1) as L1. pose proof (u64_range (edenot E e')) as R'.
  assert (Hue : bv_unsigned (edenot E e) = bv_unsigned (edenot E e') - rho) by (rewrite Ee; apply Z.mod_small; lia).
  rewrite Hue. replace (bv_unsigned (edenot E e') - (bv_unsigned (edenot E e') - rho)) with rho by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

#[using="Type"] Lemma fact_ok_sound : forall E M k K, know_ok SEGS E M k -> fact_ok k K = true -> kentry_ok SEGS E M K.
Proof.
  intros E M k K HK H. destruct K as [| | | |e m|e lo hi| |[b1 k1] n1 [b2 k2] n2| |]; try discriminate; cbn [fact_ok] in H.
  - (* [comment removed for export] *) apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.ltb_lt in H1. apply Z.eqb_eq in H2. apply Z.leb_le in H3. cbn [kentry_ok]. split; [exact H1|].
    destruct (ealign_sound SEGS E M k e HK) as [Hr Hd].
    rewrite H2. apply Z.mod_divide; [lia|]. eapply Z.divide_trans; [|exact Hd]. apply pow2_divide_le. split; [apply Z.log2_nonneg | exact H3].
  - (* [comment removed for export] *) destruct (xlo2 k e) as [l|] eqn:Hl; [|discriminate]. destruct (xhi2 k e) as [h|] eqn:Hh; [|discriminate].
    apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof (xlo2_sound E M k e l HK Hl). pose proof (xhi2_sound E M k e h HK Hh). cbn [kentry_ok]. lia.
  - (* [comment removed for export] *) cbn [kentry_ok]. exact (ranges_apart_x_sound SEGS E M k b1 k1 n1 b2 k2 n2 HK H).
Qed.

#[using="Type"] Lemma fact_sound : forall E cs R FULL model K,
  cs_ok E cs R FULL model -> fact_ok (kn cs) K = true -> cs_ok E (add_kn cs [K]) R FULL model.
Proof.
  intros E cs R FULL model K HC H. unfold add_kn. apply cs_ok_set_kn; [exact HC|].
  constructor; [eapply fact_ok_sound; [exact (co_know _ _ _ _ _ HC) | exact H] | exact (co_know _ _ _ _ _ HC)].
Qed.

#[using="Type"] Lemma regs_ok_ext_eq : forall E sr sr' R, sr = sr' -> regs_ok E sr R -> regs_ok E sr' R.
Proof. intros; subst; assumption. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma entails_sound : forall E cs ch R FULL model,
  cs_ok E cs R FULL model -> entails cs ch = true -> cs_ok E ch R FULL model /\ pc ch = pc cs.
Proof.
  intros E cs ch R FULL model HC H. unfold entails in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  rename H into Hpc. apply Z.eqb_eq in Hpc. split; [|symmetry; exact Hpc].
  match goal with Hl : match s_log (a_ss ch) with _ => _ end = true |- _ => rename Hl into HL; destruct (s_log (a_ss ch)) eqn:HL'; [clear HL; rename HL' into HL|discriminate] end.
  match goal with Hr : list_eqb expr_eqb _ _ = true |- _ => apply (list_eqb_eq expr_eqb expr_eqb_eq) in Hr; rename Hr into Hregs end.
  match goal with Hm : list_eqb amap_eqb _ _ = true |- _ => apply (list_eqb_eq amap_eqb amap_eqb_eq) in Hm; rename Hm into Hmaps end.
  match goal with Ha : list_eqb pair_eqb (a_vis cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Ha; rename Ha into Hallow end.
  match goal with Hg : list_eqb pair_eqb (a_ghost cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hg; rename Hg into Hghost end.
  match goal with Hb : expr_eqb (a_brk cs) _ = true |- _ => apply expr_eqb_eq in Hb; rename Hb into Hbrk end.
  match goal with Hf : afd_eqb _ _ = true |- _ => apply afd_eqb_eq in Hf; rename Hf into Hfd end.
  match goal with Ht : Bool.eqb _ _ = true |- _ => apply eqb_prop in Ht; rename Ht into Htid end.
  match goal with Hk : forallb _ (kn ch) = true |- _ => rename Hk into Hkn end.
  repeat match goal with Hz : Z.leb _ _ = true |- _ => apply Z.leb_le in Hz end.
  assert (HA : allowA E ch = allowA E cs) by (unfold allowA; rewrite Hallow, Hghost; reflexivity).
  assert (HH : hid E ch model = hid E cs model) by (apply hid_ext; symmetry; exact Hallow).
  destruct HC; constructor; rewrite <- ?Hregs, <- ?Hmaps, <- ?Hallow, <- ?Hghost, <- ?Hbrk, <- ?Hfd, <- ?Htid, ?HA; try assumption.
  - unfold Mr. rewrite HH. unfold know_ok. apply Forall_forall. intros K Hin.
    pose proof (proj1 (forallb_forall _ _) Hkn K Hin) as HK. apply existsb_exists in HK as [K' [Hin' Heq]].
    apply kentry_eqb_eq in Heq. subst K'. exact (proj1 (Forall_forall _ _) co_know0 K Hin').
  - eapply holes_mono; [exact co_holes0 | lia].
  - lia.
  - destruct co_split0 as [Y HY]. exists Y. split; [lia | apply HY].
  - lia.
  - lia.
  - intros a. rewrite HH. replace (in_ghost E ch) with (in_ghost E cs) by (unfold in_ghost; rewrite Hghost; reflexivity). exact (co_zero0 a).
Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma ridx_lit : forall n, (n < 32)%nat -> ridx (Z_to_bv 5 (Z.of_nat n)) = n.
Proof.
  intros n Hn. unfold ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia. lia.
Qed.

#[using="Type"] Lemma reg_sound : forall E cs R FULL model n,
  cs_ok E cs R FULL model -> (0 < n < 32)%nat ->
  getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (reg cs n).
Proof.
  intros E cs R FULL model n HC Hn. rewrite (co_regs _ _ _ _ _ HC). unfold sr_get, reg.
  assert (Hnz : bv_eqb (Z_to_bv 5 (Z.of_nat n)) 0%bv = false).
  { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia.
    replace (bv_unsigned (0%bv : bv 5)) with 0%Z by reflexivity. lia. }
  rewrite Hnz. rewrite ridx_lit by lia. reflexivity.
Qed.

#[using="Type"] Lemma lit_of_sound : forall E e z, lit_of e = Some z -> edenot E e = Z_to_bv 64 z /\ (0 <= z < two64)%Z.
Proof.
  intros E e z H. destruct e; try discriminate. cbn [lit_of] in H. injection H as <-.
  split; [| unfold two64; apply Z.mod_pos_bound; lia].
  cbn [edenot]. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold two64.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

#[using="Type"] Lemma reg_lit_sound : forall E cs R FULL model n z,
  cs_ok E cs R FULL model -> (0 < n < 32)%nat -> reg_lit cs n = Some z ->
  getr R (Z_to_bv 5 (Z.of_nat n)) = Z_to_bv 64 z /\ (0 <= z < two64)%Z.
Proof.
  intros E cs R FULL model n z HC Hn H. unfold reg_lit in H.
  destruct (lit_of_sound E (reg cs n) z H) as [He Hz]. rewrite (reg_sound E cs R FULL model n HC Hn), He. auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma regs_ok_respell : forall E sr R n e,
  regs_ok E sr R -> (0 < n < 32)%nat -> edenot E e = edenot E (nth n sr (ELit 0)) ->
  regs_ok E (sr_upd sr n e) R.
Proof.
  intros E sr R n e HR Hn He.
  replace (sr_upd sr n e) with (sr_upd sr (ridx (Z_to_bv 5 (Z.of_nat n))) e) by (rewrite ridx_lit by lia; reflexivity).
  apply regs_ok_pin; [exact HR|].
  rewrite (HR (Z_to_bv 5 (Z.of_nat n))). unfold sr_get.
  assert (Hnz : bv_eqb (Z_to_bv 5 (Z.of_nat n)) 0%bv = false).
  { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia.
    replace (bv_unsigned (0%bv : bv 5)) with 0%Z by reflexivity. lia. }
  rewrite Hnz, ridx_lit by lia. symmetry. exact He.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma regs_ok_set_n : forall E sr R n e v,
  regs_ok E sr R -> (0 < n < 32)%nat -> edenot E e = v ->
  regs_ok E (sr_upd sr n e) (regupd R (Z_to_bv 5 (Z.of_nat n)) v).
Proof.
  intros E sr R n e v HR Hn He.
  replace (sr_upd sr n e) with (sr_upd sr (ridx (Z_to_bv 5 (Z.of_nat n))) e) by (rewrite ridx_lit by lia; reflexivity).
  apply regs_ok_set; [exact HR | | exact He].
  intros Hz. apply (f_equal bv_unsigned) in Hz. rewrite Z_to_bv_unsigned in Hz. unfold bv_wrap in Hz.
  change (bv_modulus 5) with 32%Z in Hz. rewrite Z.mod_small in Hz by lia.
  replace (bv_unsigned (0%bv : bv 5)) with 0%Z in Hz by reflexivity. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fresh_ok_parts : forall cs, fresh_ok nx0 cs = true ->
  AP.sr_vars_lt (nxt cs) (s_regs (a_ss cs)) = true /\ AP.kn_vars_lt (nxt cs) (kn cs) = true
  /\ maps_vars_lt (nxt cs) (a_maps cs) = true /\ pairs_vars_lt (nxt cs) (a_vis cs ++ a_ghost cs) = true
  /\ AP.expr_vars_lt (nxt cs) (a_brk cs) = true /\ fd_vars_lt (nxt cs) (a_fd cs) = true /\ (nx0 <= nxt cs)%nat.
Proof.
  intros cs H. unfold fresh_ok in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  apply Nat.leb_le in X. repeat split; try assumption.
  unfold pairs_vars_lt in *. rewrite forallb_app. apply andb_true_intro. split; assumption.
Qed.

#[using="Type"] Lemma allowA_agree : forall b E E' cs, env_agree b E E' -> pairs_vars_lt b (a_vis cs ++ a_ghost cs) = true -> allowA E' cs = allowA E cs.
Proof.
  intros b E E' cs Hag H. unfold allowA. rewrite !flat_map_concat_map. f_equal. apply map_ext_in. intros p Hin.
  pose proof (proj1 (forallb_forall _ _) H p Hin) as Hp. apply andb_prop in Hp as [H1 H2].
  unfold allow1, sh_lo, sh_hi, uE. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2). reflexivity.
Qed.

#[using="Type"] Lemma in_allow_agree : forall b E E' cs, env_agree b E E' -> pairs_vars_lt b (a_vis cs) = true -> in_allow E' cs = in_allow E cs.
Proof.
  intros b E E' cs Hag H. apply functional_extensionality. intros z. unfold in_allow, in_vis, in_sh. unfold pairs_vars_lt in H.
  induction (a_vis cs) as [|p l IH]; [reflexivity|]. cbn [existsb forallb] in H |- *.
  apply andb_prop in H as [Hp Hl]. apply andb_prop in Hp as [H1 H2].
  unfold sh_lo, sh_hi, uE in *. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2).
  pose proof (IH Hl) as E1. apply (f_equal negb) in E1. rewrite !negb_orb in E1.
  apply (f_equal negb) in E1. rewrite !negb_andb, !negb_involutive in E1.
  destruct (existsb _ l), (existsb _ l), (existsb _ l), (existsb _ l); cbn in E1 |- *; rewrite ?orb_true_r, ?orb_false_r; try reflexivity; try discriminate.
Qed.

#[using="Type"] Lemma in_ghost_agree : forall b E E' cs, env_agree b E E' -> pairs_vars_lt b (a_vis cs ++ a_ghost cs) = true ->
  in_ghost E' cs = in_ghost E cs.
Proof.
  intros b E E' cs Hag H. apply functional_extensionality. intros z. unfold in_ghost.
  unfold pairs_vars_lt in H. rewrite forallb_app in H. apply andb_prop in H as [_ H].
  induction (a_ghost cs) as [|p l IH]; [reflexivity|]. cbn [existsb forallb] in H |- *.
  apply andb_prop in H as [Hp Hl]. apply andb_prop in Hp as [H1 H2].
  unfold uE in *. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2), (IH Hl). reflexivity.
Qed.

#[using="argH_agree"] Lemma hid_agree : forall b E E' cs model, env_agree b E E' -> (nx0 <= b)%nat -> pairs_vars_lt b (a_vis cs ++ a_ghost cs) = true ->
  hid E' cs model = hid E cs model.
Proof.
  intros b E E' cs model Hag Hle H. apply functional_extensionality. intros a. unfold hid, vis.
  assert (H' : pairs_vars_lt b (a_vis cs) = true).
  { unfold pairs_vars_lt in *. rewrite forallb_app in H. apply andb_prop in H as [H _]. exact H. }
  rewrite (in_allow_agree b E E' cs Hag H'). rewrite (argH_agree E E' a) by (eapply env_agree_le; eassumption). reflexivity.
Qed.

#[using="Type"] Lemma maps_den_agree : forall b E E' ms, env_agree b E E' -> maps_vars_lt b ms = true -> map (amap_den E') ms = map (amap_den E) ms.
Proof.
  intros b E E' ms Hag H. apply map_ext_in. intros m Hin.
  pose proof (proj1 (forallb_forall _ _) H m Hin) as Hm. apply andb_prop in Hm as [H1 H2].
  unfold amap_den. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2). reflexivity.
Qed.

#[using="Type"] Lemma maps_match_agree : forall b E E' ms l, env_agree b E E' -> maps_vars_lt b ms = true ->
  maps_match E ms l -> maps_match E' ms l.
Proof.
  intros b E E' ms. induction ms as [|m ms IH]; intros l Hag H HM; cbn [maps_match] in *; [exact HM|].
  cbn [maps_vars_lt forallb] in H. apply andb_prop in H as [Hm Hr]. apply andb_prop in Hm as [H1 H2].
  unfold uE, amap_den in *. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2).
  destruct (is_fog m).
  - destruct HM as [HM|(iv & l' & -> & Hsz & HM)]; [left; exact (IH _ Hag Hr HM) | right].
    exists iv, l'. split; [reflexivity|]. split; [exact Hsz | exact (IH _ Hag Hr HM)].
  - destruct HM as (l' & -> & HM). exists l'. split; [reflexivity | exact (IH _ Hag Hr HM)].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma holes_agree : forall b E E' y l ms,
  env_agree b E E' -> maps_vars_lt b ms = true -> Forall (hole_ok E y l) ms -> Forall (hole_ok E' y l) ms.
Proof.
  intros b E E' y l ms Hag Hv H. apply Forall_forall. intros m Hin Hh.
  pose proof (proj1 (forallb_forall _ _) Hv m Hin) as Hm. apply andb_prop in Hm as [H1 H2].
  unfold hole_ok, uE in *. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2).
  exact (proj1 (Forall_forall _ _) H m Hin Hh).
Qed.

#[using="Type"] Lemma fds_ok_agree : forall b E E' f model,
  env_agree b E E' -> fd_vars_lt b f = true -> fds_ok E f model -> fds_ok E' f model.
Proof.
  intros b E E' f model Hag Hv H. destruct f as [|k len off|]; try exact H.
  cbn [fd_vars_lt] in Hv. apply andb_prop in Hv as [Hl Ho].
  destruct H as [p [c (H1 & H2 & H3 & H4 & H5)]]. exists p, c.
  unfold uE in *. rewrite <- (edenot_agree' b E E' _ Hag Hl), <- (edenot_agree' b E E' _ Hag Ho).
  destruct Hag as [_ Heb]. rewrite <- Heb. repeat split; assumption.
Qed.

#[using="argH_agree SINV_agree"] Lemma cs_ok_agree : forall E E' cs R FULL model,
  env_agree (nxt cs) E E' -> fresh_ok nx0 cs = true ->
  cs_ok E cs R FULL model -> cs_ok E' cs R FULL model.
Proof.
  intros E E' cs R FULL model Hag Hf HC.
  destruct (fresh_ok_parts cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (hid_agree (nxt cs) E E' cs model Hag Fle Fallow) as HH.
  pose proof (allowA_agree (nxt cs) E E' cs Hag Fallow) as HA.
  destruct HC; constructor; rewrite ?HA; try assumption.
  - eapply regs_ok_agree'; eassumption.
  - unfold Mr. rewrite HH. eapply know_ok_agree'; eassumption.
  - eapply fds_ok_agree; eassumption.
  - eapply maps_match_agree; [exact Hag | exact Fmaps | assumption].
  - eapply holes_agree; [exact Hag | exact Fmaps | assumption].
  - (* [comment removed for export] *) apply Forall_forall. intros m Hin Hk.
    pose proof (proj1 (forallb_forall _ _) Fmaps m Hin) as Hm. apply andb_prop in Hm as [H1 H2].
    unfold amap_den. rewrite <- (edenot_agree' (nxt cs) E E' _ Hag H1), <- (edenot_agree' (nxt cs) E E' _ Hag H2).
    exact (proj1 (Forall_forall _ _) co_none0 m Hin Hk).
  - apply Forall_forall. intros m Hin Hk a Ha.
    pose proof (proj1 (forallb_forall _ _) Fmaps m Hin) as Hm. apply andb_prop in Hm as [H1 H2].
    rewrite <- (edenot_agree' (nxt cs) E E' _ Hag H1), <- (edenot_agree' (nxt cs) E E' _ Hag H2) in Ha.
    exact (proj1 (Forall_forall _ _) co_kinds0 m Hin Hk a Ha).
  - rewrite <- (edenot_agree' (nxt cs) E E' _ Hag Fbrk). assumption.
  - intros a. rewrite HH, (in_ghost_agree (nxt cs) E E' cs Hag Fallow). exact (co_zero0 a).
  - eapply SINV_agree; [eapply env_agree_le; [exact Hag | exact Fle] | assumption].
Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma fresh_ok_mono : forall gb cs, (nx0 <= gb)%nat -> fresh_ok gb cs = true -> fresh_ok nx0 cs = true.
Proof.
  intros gb cs Hle H. unfold fresh_ok in *.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  apply Nat.leb_le in X.
  repeat (apply andb_true_intro; split); try assumption. apply Nat.leb_le. lia.
Qed.

#[using="IT_ok HS XN XE XB SEGS_wx SEGS_in_hull HULL_ok argH_high argH_agree SINV_frame SINV_agree"] Lemma run_block_sound : forall gb bfuel stops cs cs' E R FULL model T,
  (nx0 <= gb)%nat ->
  run_block SEGS IT gb KC bfuel stops cs = Some cs' -> cs_ok E cs R FULL model ->
  (forall E' R' FULL' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS scfg (cfg R' (pc cs') FULL' model') T) ->
  srealizes SEGS scfg (cfg R (pc cs) FULL model) T.
Proof.
  intros gb bfuel stops cs cs' E R FULL model T Hgb Hrb HC Hk.
  rewrite run_block_eq in Hrb. (* [comment removed for export] *) unfold run_block_ref in Hrb.
  destruct (fresh_ok gb cs) eqn:Hf0; [|discriminate].
  pose proof (fresh_ok_mono gb cs Hgb Hf0) as Hf.
  destruct (fresh_ok_parts cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (co_regs _ _ _ _ _ HC) as HR. pose proof (co_know _ _ _ _ _ HC) as HK.
  unfold kn in HK, Fkn. unfold nxt in Fsr, Fkn, Fmaps, Fallow, Fbrk, Ffd, Fle, Hk.
  destruct (a_ss cs) as [p sr log k nx rsv] eqn:Hss.
  cbn [s_know s_regs s_pc s_next] in Hrb, HR, HK, Fsr, Fkn, Fmaps, Fallow, Fbrk, Ffd, Fle, Hk.
  set (ss' := sym_execTX SEGS IT KC bfuel true stops (SS p sr [] k nx)) in Hrb.
  destruct (carry (s_log ss') (s_know ss') []) as [[kn' scs] hs] eqn:Hc.
  destruct scs; [|discriminate]. injection Hrb as <-.
  (* [comment removed for export] *)
  set (H := hid E cs model). set (MR := Mr E cs model FULL).
  rewrite sr_vars_lt_eq in Fsr. rewrite kn_vars_lt_eq in Fkn.
  pose proof (runTX_sound SEGS IT KC bfuel stops p sr k nx E MR (seg_rom SEGS) R IT_ok HR HK Fsr Fkn) as HX.
  cbn zeta in HX. fold ss' in HX. destruct HX as (E' & R' & Hag & Hle & HR' & Hlf & HK' & Hms & _).
  assert (Hagc : env_agree (nxt cs) E E') by (unfold nxt; rewrite Hss; exact Hag).
  pose proof (cs_ok_agree E E' cs R FULL model Hagc Hf HC) as HC'.
  assert (HH : hid E' cs model = H).
  { unfold H. eapply hid_agree; [exact Hagc | unfold nxt; rewrite Hss; exact Fle | unfold nxt; rewrite Hss; exact Fallow]. }
  unfold cfg_of, pc. rewrite Hss. cbn [a_ss s_pc].
  apply (srz_msteps_restricted_T SEGS scfg H (H_off_segments_cs E cs model) SEGS_wx (allowA E cs)
           (mkst R (Z_to_bv 64 p) FULL (seg_rom SEGS)) _ model T
           (lazy_cover_cs E cs R FULL model HC) (A_wf_allowA E cs) (co_minv _ _ _ _ _ HC) (co_halt _ _ _ _ _ HC) Hms).
  intros model' Hinv' Hsame Hclean.
  assert (HKc : know_ok SEGS E' (mem_denot E' MR (s_log ss')) kn').
  { eapply (carry_sound SEGS E' MR); [exact Hc | exact Hlf | exact HK' | constructor]. }
  set (FULL' := munrestrict H FULL (mem_denot E' MR (s_log ss'))).
  assert (Hmr' : Mr E' cs model FULL' = mem_denot E' MR (s_log ss')).
  { unfold Mr, FULL'. rewrite HH. apply mrestrict_munrestrict_clean. intros a Ha. exact (Hclean a Ha). }
  assert (Flec : (nx0 <= nxt cs)%nat) by (unfold nxt; rewrite Hss; exact Fle).
  assert (Fallowc : pairs_vars_lt (nxt cs) (a_vis cs ++ a_ghost cs) = true) by (unfold nxt; rewrite Hss; exact Fallow).
  specialize (Hk E' R' FULL' model' (conj (env_agree_le _ _ _ _ Hag Fle) Hag)).
  unfold cfg_of, pc in Hk. cbn [with_ss a_ss mk_ss s_pc] in Hk.
  replace (unrestrict H (ms_mem (mkst R (Z_to_bv 64 p) FULL (seg_rom SEGS)))
             (mkst R' (Z_to_bv 64 (s_pc ss')) (mem_denot E' MR (s_log ss')) (seg_rom SEGS)))
    with (mkst R' (Z_to_bv 64 (s_pc ss')) FULL' (seg_rom SEGS)) by reflexivity.
  apply Hk.
  - eapply cs_ok_frame; [exact HC' | exact Hsame | | exact HR' | reflexivity | | ].
    + rewrite (allowA_agree (nxt cs) E E' cs Hagc Fallowc). exact Hinv'.
    + cbn [mk_ss s_know]. rewrite Hmr'. exact HKc.
    + intros a Ha. rewrite HH in Ha. unfold FULL', munrestrict. rewrite Ha. reflexivity.
  - pose proof (same_but_materialized_frame _ _ Hsame) as Hfr. apply Hfr.
Qed.

#[using="IT_ok HS XN XE XB SEGS_wx SEGS_in_hull HULL_ok argH_high argH_agree SINV_frame SINV_agree"] Lemma run_block_gc_sound : forall gb bfuel stops cs cs' E R FULL model T,
  (nx0 <= gb)%nat ->
  run_block_gc SEGS IT gb KC bfuel stops cs = Some cs' -> cs_ok E cs R FULL model ->
  (forall E' R' FULL' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS scfg (cfg R' (pc cs') FULL' model') T) ->
  srealizes SEGS scfg (cfg R (pc cs) FULL model) T.
Proof.
  intros gb bfuel stops cs cs' E R FULL model T Hgb H HC Hk. unfold run_block_gc in H.
  destruct (run_block SEGS IT gb KC bfuel stops cs) as [cs1|] eqn:Hrb; [|discriminate]. injection H as <-.
  eapply run_block_sound; [exact Hgb | exact Hrb | exact HC |].
  intros E' R' FULL' model' Hag HC1 Hfs. rewrite <- (pc_cs_gc gb cs1). apply (Hk E' R' FULL' model'); [exact Hag | apply cs_gc_ok; exact HC1 | exact Hfs].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma u_small : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros. apply u64_lit. assumption. Qed.

#[using="Type"] Lemma nth_sr_vars_lt : forall b sr r, AP.sr_vars_lt b sr = true -> (r < 32)%nat -> AP.expr_vars_lt b (nth r sr (ELit 0)) = true.
Proof.
  intros b sr. induction sr as [|x t IH]; intros r H Hr; [destruct r; reflexivity|].
  cbn [AP.sr_vars_lt] in H. apply andb_prop in H as [H1 H2]. destruct r as [|r]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.

#[using="argH_agree SINV_agree"] Lemma node_fresh_sound_pf : fresh_stmt.
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
ltac2:(KReplay.run1 (kr_t_AsanPlanSound ()) ["FPX_3"; "Sound"] "p'0p'1h03Hr1h12Hah24__x1h31Hh44cstrh57__arithh62Hch74__ffh88__varmaph95__with:5heq_ch;4__x2h<1zi001zh=5cstr0h>5cstr1h?4Fle0h@7__sat65hA7__sat66hB7__sat67hC7__sat68hD7__sat69hE7__sat70hF4__x3hG4__x4hH1bi011bhI2HnhJ4__p1hK4__x5hL1ai021ahM5heq_vhN6heq_v0hO1mhP2H2hQ4__x6hR5cstr2hS1nhT7__sat41hU7__sat42hV2E'hW2H3hX2H4hY2H5hZ2H7h[3Hhih\3Hloh]4__p2h^7__sat72h_4__x7h`5FULL'ha2H1hb4Hdivhc2Hkhd2R'he7__sat43hf7__sat44hg7__sat71hh7__sat73hi6model'hj1xi031xhk1Ahl2H0hm3H10hn3H11ho3H12hp3H40hq2H6hr2H8hs2H9ht3Halhu3Hr0hv4Hr32hw1Phx1Yhy7__sat45hz7__sat46h{7__sat47h|7__sat48h}4__x8h~2b1i042b2i052csi063cs'i072e0i082ivi092l1i0:2l2i0;1oi0<2q0i0=2q1i0>2r0i0?2r1i0@1Ei0A4FULLi0B6Fallowi0C4Fbrki0D3Ffdi0E3Fkni0F3Flei0G5Fmapsi0H3Fsri0I2HCi0J3HC'i0K2HKi0L3HKfi0M3Hagi0N3Hbvi0O3Hc2i0P3Hcdi0Q3Hd1i0R6He_semi0S3Heai0T3Hevi0U6Hfreshi0V4Hhi'i0W4Hlo'i0X3Hnei0Y2Hqi0Z3Hq0i0[4Hq64i0\3Hrvi0]3Huei0^3Hvbi0_3Hvei0`1Ri0a1Ti0b2_Hi0c2a0i0d2b0i0e4basei0f1ci0g:co_abytes0i0h:co_bounds0i0i7co_brk0i0j9co_eager0i0k7co_fds0i0l6co_fs0i0m8co_halt0i0n9co_holes0i0o9co_kinds0i0p8co_know0i0q9co_lazyb0i0r9co_limit0i0s7co_log0i0t8co_maps0i0u8co_minv0i0v9co_nasub0i0w8co_none0i0x8co_regs0i0y7co_res0i0z8co_sbrk0i0{8co_seps0i0|8co_sinv0i0}9co_split0i0~7co_tid0i109co_totsz0i116co_wf0i128co_zero0i131ei142e1i152hii162loi174logci185modeli191qi1:1ri1;2s1i1<1vi1=1yi1>9co_abytesi1?9co_boundsi1@6co_brki1A8co_eageri1B6co_fdsi1C5co_fsi1D7co_halti1E8co_holesi1F8co_kindsi1G7co_knowi1H8co_lazybi1I8co_limiti1J6co_logi1K7co_mapsi1L7co_minvi1M8co_nasubi1N7co_nonei1O7co_regsi1P6co_resi1Q7co_sbrki1R7co_sepsi1S7co_sinvi1T8co_spliti1U6co_tidi1V8co_totszi1W5co_wfi1X7co_zerop%0p%1p%2p%3p&0p&1p&2p&3p;1p;2p;5p;3p;4p;;p;6p;7p;9p;:p;8p;Pp;<p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0g0038R5p4p710R6p9P0p1003Vp4p710R7p9P0g00_3R8p4p710R9p8P0g004eR:p4p710p8P0g00j2R;p4p710p8P0P;p4p7210p8P0p1005cp4p710R0p8p100_Jp4p70R<g00;\R=p4p710R>p8P<P1p8P<P2p8P<g0079R?p4p710R@p8P<P4p8P<P3p4p710R3p8P<P7p8p1006?p4p710P6p8g00`:S00p4p70R<P>p8P<P1p8P<P2p8P<p100`hp4p7210p8P<P@p8P<P4p8P<P3p8P<P6p8P<P7p8p100aDp4p70P@p8g00bCR<p4p7210R>P1p8P>P2p8P>P@p8P>P4p8P>P3p8P>P7p8p1062Tp6051000R>P6p8P>p103VIp4p710RAp8P>p1063Vp4p710p8p106kQp6051000R>P9p8P>P6p8P>PAp8P>P0p8p107<2p6051000R>P9p8P>PAp8P>P0p8p100bop4p70R0P1p8P0P2p8P0P4p8P0P3p8P0P7p8p1006\p4p7210R7P@p8P7P6p8p1007Up4p7210P6p8p10082p4p73110P6p8p100cep4p710P6p8g01SnS01k10sTg008Nj1ITg00JTk10}Tg00dlk10xTg00eJk10VTP<k23<Tg01TPS02k50]Tg0:X]S03k131Tg0:YZk51lTP=j30k12ATg07`]k303Tg05R^j12Tg00>lR=j2ATg02@ik10UTg0:3Pj5JTg04JVk12<Tg03ISj2dTg09<_k20lTg00A:j1RTg0:Z]j2CTg0093k10CTg01POj2DTg07AFj2FTg09_6k20TTg00O0j2lTg02X7j1>Tg099ek20@Tg09;bk20=Tg06IOj1VTg018]j29Tg0:[=j2STg07Zej2`Tg00J2k11:Tg09>]k305Tg01QJk30RTg07\bR<j2wTg0:\<k237Tg00:BR6j21Tg01Qmk235Tg00:^j2ETg030Ck21KTg00=Lj2BTg02W:j1tTg05TWk12tTg02P:j1}Tg02T7k12nTg05UWk12mTg035gk22kTg05VYk42jTg02^\j1]Tg02fVk11LTg02`\k10oTg02lFk11STg01ERj1~Tg01FPj1sTg02nCk11>Tg02jMk10?Tg02Y2k10XTg02Zlk11?Tg05WWm;2bTg05XUk62`Tg05SZk21CTg03M^k61aTg02S>j4zTg02U9k40yTg09DZk72YTg09E[k72XTg09@bk62WTg07X`k20\Tg09Ahk20gTg035GR7j14Tg00>PR@j28Tg03dFj1@Tg00E?k11YTg00F?k10dTg00]4k12KTg00G[k12JTg00H9k12ITg00Hdk20cTg00NNk22HTg00OJk22GTg00P6k33CTg00PUk43BTg00K9k22FTg01>6k43Aj2LTg01>^j3OTg0:\_k53@Tg09Blk33>Tg09D4k53=Tg01=4j27Tg017fk11VTg00iHj2<Tg04mIk23;Tg04mlk33:Tg03m1j4QTg00AYk22@Tg08\lk539Tg01LWk32>Tg00B`k21RTg0910k438Tg091Qk22;Tg01BIk229Tg00BBk136Tg00CAk31QTg01L1k20ETg07^8k31OTg0:]Fk334Tg09hkk233Tg07kHk21NTg07h<k20hTg09a]k20JTg00emk21MTg03jWR0j2xTg0:=\m932Tg08?dk610Tg013>k40~Tg047Mk422Tg0:^Gk52~Tg0:_Lk40jTg04oJk32}Tg00<Oj2^Tg00<lj2:Tg0:`6k32|Tg07Pok320Tg0:`Wk21ITg0:aUk22{Tg07]:k20zTg0:bVk31|TP5j6ZTg0:cTk32zTg0:dTk42vTg057nk41FTg09fck62uTg00jOk41ETg01GPj3eTP:j3[Tg05:6k42sTg03ETk32pk41oTg044Dj3mTg009Qk21vTg0:eXk32lTg016lS04k21HTg00;;k20|Tg00<6k11sTg00=ik219Tg00?Gk214Tg00?nk20vTg00@Tk21<Tg00Mkk311Tg00^3k31pTg00^Vk20:Tg0:f=k22iTg0:f^k12hTg09=\k21mTg05B?k32=Tg08n1k12gTg01Gmk42fTg0:g@k62eTg0:hAm:2dTg05A=k61iTg02Q<k32BTg02R=k11_Tg02A\k11hTg02Yok31XTg02BSk11gTg01_?j1TTg02[mk10ZTg02\gk12cTg02]ek11eTg01`6j1iTg02_[k31dTg00fMk31ZTg02aZk11cTg02bWk11bTP;k32aTg005Fk32_Tg01Z8k12^Tg01Y@k10eTg01aik10DTg01`lj2jTg02cWk12]Tg00mbk22\Tg02dWk21jTP8k31[Tg00jjk12[Tg00lck12ZTg01N7k11`Tg01Nok20wTg02eVk11^Tg02gVk11kTg02hQk31wTg02iXk11PTg02kKk11]Tg02E9k11nTg01C[k21GTg02mFk11rTg02O>k21xTg01UNk41zTg02oDk31uTg0488k62VTg041`k41\TP?k60{k72STg0:iJk32UTg07Onk22qTg0:j1k82rTg03:2mP2TTg0148k21BTg0:k7k22RTg03_dk12xTg0:MDk52yTg01Plj2YTg00E_k30;Tg09G`k21ATg0:l8k31@Tg04E9m<0_Tg00IGk40mTg00RFk70uTg00F_k22QTg00Rjk813Tg00G=k41TTg00L@k72PTg00Cjk30aTg01C2k317Tg00DSk22OTg00K\k62NTg00MHk32MTg09`7k22CTg09bbk22DTg05C@k32ETg00Ldk62LTg00ZZR?f0R8g00[:R;30p=6g01JGR:01K8p=Pf4R5f3R3f2R4$2xf1R2P8I2yp=G%R8#Rp>30%R8#R#R#Rp>0fg00VPR1/D8p=H%I8#Ip>1tg00WZR>/C3/Y4/Y2/Y8p>0B%>200\8,D4p=\1Y53/Y4/Y2/Y8p>0G20\28,D4p>1Uf6RAf5R9/B500:3/E41E283mp>09%>4@0528p>0bf7RBg03GPRC20l95?m11>0;C380;A+1A@1@4201C8p=o1C>8p=c1Y42/Y8p>18A0?2;/A8p>0Q1Y34/Y2/Y8=0?;p>0<1C>41C28'Yp>0`1F28=0?;p>0N1Y28=0?;p>161w>8p>281118p=3%>200\8p=N1B5300:4/E2=m98p>2720l42?m11>0;C8p>23B0;C53-1A9@1@4201C8p>0t20:42/E8p>0F1E289m34p>2120l53?m11%>4@052860;Cp>1}Am342>0;C8p>1{21A34@1@28p>2w1728,<4p==1112/A8p={g00UMRD/l8p=;g03D=REPDP<P7P@g07`;RFP9P51lD3P4P2P8N<0_p=q1w53P4P2P8CQp=b1818p=?1w>AP9PEPDP<P7P@PFP>P1P5P3P41lD2N<0_P8CQp>08P4g00SNS05g00SmRGPGg00TMRHPDP2g00XeP8H0mg00TmRIK0up=v22QD8p>0>P4Q05PGPGPHPDP2g00YLRJP8H0mPIK0up=XP3Q05PGPGPHP4P2P8L13p=pA0D28p=5PEPDP<P7P@PFP>P1P3P4P2P8N<0_p>1=1w>3P4P2P8CQp>1W1928,81p=gPEPDP<P7P@PFP9P5P3P4P2P8N<0_p>1;%48,11p=MPDP4P2P8H1Tp>0722FD8p>06P4Q05PGPGPHP2P8K2Pp=aPAQ05PGPGPHP9P5P3Q05PGPGPHP4P2P8L13L13p=K1128,A4p>3?1^2890D4p=u11141828'Ap>041lE8p>0SA0E28p=_PEPDP8P7P2P4P3P5P9PAPBf8RFN<0_p>0K22@D8p=rB0aD28p=hB17D28p>01B0aD28:0aD4p>2?B17D42>0aD8p>0qg00X9-2O8p>0Lg00VnR@@0;28p>0PP2Q05PGPGPHP8J2Np>15B2MD28p>0OP4Q05PGPGPHPDP2g00Z3R<P8H0mPIK0up>001928,11p>02%I8#I#I#Ip>2:%I8#I#I#I#I#I#I#Ip>0WB17D53B17D42>0aD860aDp>0n1828,A4p>0[Ae428-2C3p>0M&0X4-2D3=0?;1x28'Ap=f&0?2,F4=0?;/A8p>0kA0?4;A0?2;/A8'Ap=n&0?8,F2p>12%~2=e48p>2622C28=0?;p>2522D28=0?;p>24PEPDP0P7P6g04GiP9P5P3P4P2P8N<0_p>0APDPDP5P3P4H1TP2P8H1Tp>0^PDP2P<P8H0mp>1JP5Q05PGPGPHP3Q05PGPGPHP4PIK0uP2P8L13p>0iPDP5P3P4P2P8EZp=kPDP2PJP8H0mp>1~g05DTS06@2E28p>0IAm811p>2oB0;C28p>1y1142/A8p=|1B4200:8p=UA0D81p=W1181,A2p>0pP2Q05PGPGPHP8J2Lp>1q1181p>0rg014W90?8p=yg00oaS07?[28p>0Y1A28,A4p>1DA0?8;,A2p>1fg05ChS08@2E28p>0Hg01IES09$0sg00n`S0:g00UkS0;#IRJ$0}S0<$0x%IJS0=#IRI#IS0>#IR<#IS0?$0xR6$0VR7+3<R0&0xIS0@$0VS0A$0sS0B\7RIg01l\RKg08CjP5PAP3P4P2I0]&31B#6&0s:RLp,3nx0RMPFf;RNf:ROf9RPI1l%PB30Q0:B03MN3f=RQ#2RR@03N3'AP5PQP3P4P2I0]Q00&0U4RS&0UO30p,3bmKRTp,4SEGSRUp,4scfgRVPUP9f?RWP5P3DGPODJ[[[^iK^`I^d0]VQ01Q09Q09PNP8&2<1S0Cn10110e00021010100Q09f>RX,dN00l8Q09PW%R>RY#RS0D#RS0E#RS0F#RS0G#RS0H#RS0I#RS0J#RS0K#RS0L$30$0f$0f$0f$0f$0fRZ,CW%HXQ0<#IS0M$1tS0N$0CR[,DXH0Bf<S0O=\X8Q0O#2R\/F21F\8Q0O-0TMI0GP?1l?8f@R\1C\Z%HW1DW[H0BA\WQ21FR41FR220TMQI0G=0?8P?fBRR1CRZfAR]#H1D][H0B%>WR^>1U]3%2WR_/F51F_320TMWI0G=0?8P?PLP2Q01PDPL%>\R_00@5Q01PDPL%>]R`00=9PR%2R#VRaP2&0CJRbfDRc'9RdQ0;$0CRePdP8PdK09PA1SdaRdB0bRAdfES0P1`BdPYGo#P&1::S0Qn10110300021011500Q0Qn10110300021011600Q0Qn0100000020000%PWS0R50LPTPUPVPUPXP]PQQ0ODGPNDJS0S]I]6P2P]1C]Z%H\1D\[H0BA\\X4%2XRd/F31Fd420TMXI0GS0T#6Q01PDPL20@^3Q01PDPL20=_5P]%2]R^#VRdP2fCRa,9bRfPePfP8PfK09P91SfdRfB05`9fPc1`AfPYGo#PQ0Qn10110300021011500Q0Qn10110300021011600%PXS0U50L%ca1CaZ%HR4181DR[B1UR_5%2\R_/F91F_5I0GR_20TM\Rf<0R2%6f-0Q_P=Pc1CcZ%Ha1Da[H0BB1Ua`91F^A1F^9H0<20TM]#6PTPUPVPUPWPRPXPQDGQ0ODJP8fFS0VQ0V/CZQ0P#HQ0P/D[H0BQ0P?\aB%2aR^/FF1F^BH0<20TMc#6fHR^@0`^ZfGS0W#HQ0W/D[Q0WQ0P;\PQ0P#2R`/FOI0GR_1F`PR`<0R2%6`-0Q_P=fIS0X#cQ0X/CZ%H^4181D^[Q0V=\^OQ0V#2R_/FNH0<20N_OPTPUPVPUPcQ0WPaPRDGP]DJP8fKS0Y#cQ0Y/CZfJS0Z#H418Q0Z/D[Q0ZQ0O7\^%2^/FQH0<Q0X#200NQfMS0[#cQ0[/CZfLS0\#HQ0\/D[Q0\Q0Z;\XI0GR_Q0Z#2/FWR`<0R2%6`-0Q_P=fNS0]Q0]<0`ZQ0[#HQ0[/D[Q0[Q0Y;\WH0<Q0Y#200N\PTPUPVPUQ0XQ0\P^Q0WDGQ0VDJP8fPS0^Q0^<0`ZfOS0_#HQ0_/D[Q0_Q0[;\]H0<Q0]#200NafRR_1C_ZfQR`#H1D`[H0BRfQ0_=\`aRd<0R2%6d-0QfP=fSS0`#cQ0`/CZ%H_1D_[H0<Q0^=\_c#6PTPUPVPUQ0]P`Q0[Q0\DGQ0YDJP8fUS0a#cQ0a/CZfTS0b#HQ0b/D[H0<Q0aQ0`Q0W3\#6fWS0c#cQ0c/CZfVS0d#H418RfQ0d/D[Rd<0R2%6d-0QfP=fXRf@0`fZQ0c#H+16Q0c/D[#6PTPUPVPUQ0`Q0dP_P`DGQ0^DJP8fZRd@0`dZfYS0e#H+161Dd[#6f\Rg@0`gZRhf[S0f#HRi<0R2%6i-0QhP=f]Rh#c1ChZ+16%Hg#6PTPUPVPUPfQ0fQ0cQ0dDGQ0aDJP8f_S0g#cQ0g/CZ+16Q0g#H#6faS0h#cRiQ0h/CZRj<0R2%6j-0QiP=fbS0i#c#6Q0i/CZ#6PTPUPVPUPhf`S0jPgQ0fDGPdDJP8fdRg#c#6feRi/CZ#6P=1C28#61w42[Rj1w281C42#6Rk[1w34\k23728P2n2001000000120000000XOEXSERkPj^OE^SERjP8P>fgRlP4O3&28lPkPjP8fiS0kPZP3O3Q0k/wZP=1D28#61142[Rj11281D42#6Rk[1134\k23528P2n2001000000120000000XODXSDRkPj^OD^SDRjP8P1fjS0lPOO3Q0l#3PkPjP8flRmP[P]O311m[PkPjP8fnS0mQ0j,NmRjP^O3Q0m/1jfmS0n#>Q0h+0@&0sDS0oQ0o/l8RjQ0oQ0m#>Q0i+0@;08Q01PDQ0ofpS0p#>00@g;08Q01PDPLP2Q01PDPLfrS0q#>ffS0r+0=RkfsS0sQ0s#2#VRnP2fuS0t,9bRoPePo1E8oRpJ271SonRqQ0s#>Rr@05lq623lRsfvS0ufhS0v/`qRqPYJ0t#PQ0Qn10110300021011500Q0Qn10110300021011600Q0p#PS0w50LPTPUPVPUfoS0xQ0qQ0mQ0nDGPmDJS0y]I]\P2Q0ofqS0z#>00@i21KD8Rt30Q01PDPLPkQ0sPnP4PoPePoPpJ27PsQ0uPqPYJ0t#PQ0Qn10110300021011500Q0z#P50L20=rlQ0oPjQ0oftS0{#>Q0v+0=;08Q01PDQ0oQ0u#>Q0l+0=;08Q01PDPLP2fxRj%2j#VRrfzS0|,9bRq,BB@0FeqRsP8PqH21Pm1SqrRpPjPmPpI1}Rof{RnQ0n/`pRpPYJ0t#PQ0Qn10110300021011500Q0u#PS0}50LPTPUPVPUQ0tPjQ0{Q0sDGQ0qDJS0~]I][P2Q0ofwS10#>fkS11+0=;0tPjPrPsP2PqH21PoPnPpPYJ0t#PQ10#P50LPLP:Q01P:P:P8P8Q0|Q0|#2#VRpf|S12,9bRo,BP@0Feo1E3oQ0m1SopRoQ0|Q0mPoI1}H1{f}RpQ0x/`oH2wRo#tRq$2t%}q&2nq&2mq02kYH2j%]o&1Lo&0oo&1So%~o%so&1>o&0?o&0Xo&1?oN;2bn10110;00021010201Z07LfyRq%2q#VRsPF19bnRrPePrP4PrK09Q0n1SrsRrQ0n>0bqrQ12Q0m/`rPYGoRr#P%PjP8J2`A0:rj21CoY=0:qP:Pn%2n#VRoPO19bpRrPePrP5PrK09Q0x1SroRrQ0x>0bnrf~RoQ0p/`rPYGoQ0:B03Mo3p+01ARr#2Rs@03o3'AP5P9P3P4P2I0]Q00&0Up70SPTPUPVPUP9PBP5P3DGPpDJ[[[^iK^`I^d0]VPTPUPVPUQ0|PpPqPjDGQ10DJ]cZ06:Q0:B03Mp3p+01@Rt#2@03p3'AP5Pr%VsRsPWp+01CS13,9bRkPePkPPPkK09Q0{1SksRk%>rRsQ0{<05kp+01DS14Q0t/`kPYGoP3P4P2I0]Q00Q12$0U70SPTPUPVPUP9Q13Q13#2#VRSP]p+01ES15,9bRkPePkPNPkK09Q0u1SkSRkQ13#>RSQ0u<05kp+01FRuQ10/`kPYGoP5P3DGQ12DJ[[[^iK^`I^d0]V19boPD%2pPEQ12PoPnQ0|PqQ10J1aPUQ12Q12PoPqQ0|Cz%>oH0yPpPpPtQ0|PnCz%>tQ0sPXP8PQK2YQ0s9=6p,1XPoPoPrPnQ12CzPsQ0{PPP2PFK2XQ0{9=6o/1PPUPtPtp+01BRsQ12PpCz%>sR0Q0tP4J2WQ0t-0\0R0Q0?$0CRI,10'{19b0Q0t9=6t+0g'AP=Q0u-0\SRS11SI'{19bSQ0u9=6r+0gPTPUPVPUPrQ14PtPoDGPpDJP8Q15/NjRj11jI'{1Nuq,9bQ14==6q+0gPbp+01IRqp+01JRjPZ%4jRS&0C<R<'8R0PjPSPSPZP<%;<S16EqQ0_DbRSP0p+01KRK%4KRk#?Rv1lD1S17PKPkPkP_K08RkPvp+01LS18#@RwQ18#4Rx#3Ry&1Y@Rz&0d@S19&2KDR@&2JDS1:&2IDR{20cD1R|20cDbS1;3v22H{HS1<P8P41l?;22G84#6dB3CD12H3BS1=b7b8b9%?bR;P8b5S1>b4b0b0PSP0PkPvPwPyPzQ19&0>2S1?Q1:P{Q0;-2FDRy9X{|S1@&1:GRwQ1@CpQ1<Q1=b7b8b9X2D%38S1A%32S1B[^2DP8p+01MRvP`O2b5b4b0b0H3A%?PRkePkPbPjP[19bjRk#;15OkS1CeS1DQ1CQ18PZ18x<S1EQ18PxPxPZP<Q16EqP`DbS1FQ1EPv%4vRx#?RkQ17PvPx%;xS1GH1=Q0bH1WS1HPkp+01NS1I#@S1JQ1I#4R0#3S1KQ1I,LbS1Lp+01OS1M#3p+01PS1N,gb[\;S1O%3bRSg0157R?p+01QR}=Ob2UW1S1P19b}R~#3\?^1SS1QQ1>bTbUb4b0b0b:Q1DQ1CQ1FQ1EQ1HPkQ1JQ1KQ1LQ1OQ1PQ1QPzQ19Q1?Q1:P{20cD[9X{yRkPwPkCpQ1<Q1=b7b8b9X2D118[112[[^2DP8P}Q0`O2b5bTbUb4b0b0b:I3@19b[S1Q,1ORkePkPNQ12,NqS1P,9bS1Op+01GRkQ125=6S1LQ1P19bKS1K#;Q1K,5NS1KeQ1KPvPZ18x<S1KPvPxQ1GPZP<Q16J1;P_DbQ1KQ1I%?0RxQ17Q1IP0P0Q0aK08PxQ1M#@Q1M#MQ1M,LbQ1N#3%?~[\;p+01RS1K=Ob2V?X1SQ1K,9bS1G#3\?^1S1Lb[S1J%3[Q1Q#?[\;S1HAOb[2V?X1SS1EQ1Q#3\?^1SS1FPzQ19&0>4S1C@072@S1DQ1:P{&06JS1>9X{yS1RPwP{Q1@PwQ1@Q1R5a{FKQ1<Q1=b7b8b9X2DX;D1182Q1B%34S1S@3?43[[^2D^;DP8Q1K/Nup+01TRJQ0bPfO4b5bTbUbebfb4b0b0b:63>KQ1O-0gNeP4I3=Q1L-0gNQ04PDA=6qo?u8QX<DPTPUPVPUp+01HRfPKPkPuDGQ15DJP8A=6Kr?u8WQ18/7sR[$1V1<6[R[19bIRx804[%;~15]~R~eP~Q1N#2R~$0S1_]~R~eP~%2}S1L,_RS1O%4RR~Q1L#4R['5R0&2AES1P&2ADS1T%42%48'51_2823;2843:Z1=EXjES1UPRP~%;~Q1LP[%;[N90KP8CQP0p+01UR0PZ%40R[/8<R~P0P[P[PZP<Q16EqPdDbP~p+01VS1VQ1V#4S1W#?R~Q17Q1VQ1WQ1W#;S1XH1=PhH1WP~%2JS1Y#@Q1Y#Mp+01XR~#@%M~Q0W#@Q0W#Mp+01YRh,Lbp+01ZS1Z#3p+01[S1[,gb[\;p+01\S1\=Ob2V?X1SQ1\,9bS1]#3\?^1SQ1JQ1HQ1EQ1F1LbIS1^%3I%?x[\;S1_AObI2V?X1SS1`%3x\?S1a^1SS1bp+01]Rd/N},Lbp+01^S1cQ1K'NS1d#3p+01_S1ep+01SS1f'NS1g,gb[\;p+01`S1h/NJS1i=Ob2V?X1SQ1i,9bS1j#3\?^1Sp-0R[Q0G#rS0GQ0F#rS0F'hQ0H#rS0HQ0H22@D>R>Q0E#rS0E+01S1kQ0E<2?>+0140q$0L00PzQ19Q1C&0>5S1l&0>9S1m80738072S1CQ1:P{P{Q1;9X{|S1nPwP{P{Q05PGPGPHI39S05PwQ1;>2>D6S1o9X{|FKS1pPwP{Q0<$06S1q9X{|215{BS1r5a{PwP{Q1qQ0;$0}S1s$0}$06S1t-0Oy600{S1uPwP{Q1t9v{|S1vPwP{Q1s$06S1w9X{|S1x215{FS1y5a{S1zPwP{Q1>9X{|S1{PwQ1@FKFKFKQ1<Q1=b7b8b9X2DX;DXFDXGDXKDXJ[W]Q1a\SS1a%35S1|/AAAu94AS1}%?BS1~%3AS20/AOS21Q20Q20[[[[[[^2D^;D^FD^GD^KD^J[^][P8Q1i/1IQ1c==6JRH/8xP_PHQ1ip+01bS1iPaP3P]PRP^Q0ZQ0rO=b5bTbUbebfbybzb{b|b>b=b4b0b0bNbMb:Q1SQ1G#;Q1G,5RRHePHQ1L$0SQ1OeQ1OQ1K#2S1O,_a%4aRHQ1O#4RG'5S1LQ1PQ1TQ1UPaPH%;HQ1OPG%;GN90KP8CQQ1LQ1VPZQ1W/8<RGQ1VQ1WQ1XPZP<Q16J1;Q0fDbPGp+01WS0fQ0f#4RG#?RHQ17Q0fPGPGf^K08PH%20RH#@%MH%@h%Mh%@^%M^Q1Z,LbQ1[#3Q1]#?[\;AObd2V?X1S202bd\?^1SQ1JQ1HQ1EQ1FQ1^Q1_Q1`Q1bQ1d,LbQ1g#3Q1j#?[\;p+01aRG/N0S1j=Ob2V?X1SQ1j-02b\?^1SPD21RDeQ0;21RD1H38S1g-2;DS1dQ1kQ0?$1t$2:S0?$2:$0W$0W$0W$0W$0W$0W$0C-29DS1]Q0E+01<2?>Q1dQ0GQ0;$36-1RDS0;Q0F61QDS1d'hS0G229DbS1kQ0H001>S1X201>>S1W40qI0n$0L00PzQ19Q1CQ1:P{Q1pPwP{Q1rQ1qQ1o5v{5a{PwP{Q1uPwP{Q1vPwP{Q1zPwP{Q1{PwQ1o9v{yS1{FKFKFKQ1<Q1=b7b8b9X2DX;DXFDXGDXKDXJ[X][Q1aB0[A5xQ1}Q1~Q21Q2018Ax[[[[[[^2D^;D^FD^GD^KD^J[^][P8Q1j/1IQ1e==60S1}#3Q0`Q1}Q1jp+01cS1jPcP3PRPaQ0XQ0YPlO=b5bTbUbebfbybzb{b|b>b=b4b0b0bNbMb:183x20E65P7Q1N@1Oa8Q0:B34}c2B03c}8233JoQ1Y%tJ#}+1NQ1Y%>J+0hQ1Y%]J+0JQ1YQ09Q09+1MS0:%~J%sJH0MQ1YQ1YPJPMQ1YCf80kJ3n3nP=%t0#}-1NH#6%>0-0hH%]0-0JHPHQ0:%~0%s0H0M212H0PHP0PMPHCf3n3nPTPUPVPUQ1fQ1VQ1KP}DGQ1NDJP8Q0f#2Q0f#t#}+1N#6%2~RH%>~+0h%]~-0JHPHQ0:%~~%s~H0M212H~PHP~PMPHCf3n3nP=%2hRH%>h+0h#6%]h-0JHPHQ0:%~h%shH0MPHPhPMPHCf:0kHh3nPTPUPVPUQ0fQ1ZQ1VP0DGPJDJP8Q1[#2Q1[#>+0h#6Q1\#2RHQ1\#]+0JPHQ0:Q1\#~Q1\#sH0MQ1\PHQ1\PMPHCf60kH3nP=%2dRH%]d+0J#6PHQ0:%~d%sdH0M212HdPHPdPMPHCf3nPTPUPVPUQ1[Q1cQ1ZPhDGP~DJP8Q1e#2Q1e#]+0J#6Q1h#2RHQ0:Q1h#~Q1h#sH0MQ1h-12HPHQ1hPMPHCf3nP=%2GRHQ0:%sG826G+25PHPGPMPHCf:0kHGPTPUPVPUQ1eQ1iQ1cPdDGQ1\DJP8Q1j#2Q0:Q1jQ1j#s426+25p+01dS0:#2RHQ0:PHQ0:PMPHCf40kP=p+01eS1e#2RHQ1e$0?+0NPHQ1ePMPHCfPTPUPVPUQ1jp+01fS1YQ1iPGDGQ1hDJP8p+01gS1}#2Q1}$0?+0Np+01hRH#2S1~PHPMQ1~CfP=p+01iS1~#2S21Q1~$0X+24Q21,xMPTPUPVPUQ1}p+01jS21Q1YQ1eDGQ0:DJP8p+01kS1z#2Q1z$0X+24p+01lRV#2,xMQ1zQ0Zp+01mRTQ21Q1~PHQ0XP~Q1YN932Q0ZPTQ21Q1~PHI0]P7Q1i,7VS1vQ0YQ1i'7S1uQ0gPVQ0YQ1iQ0ZPJJ10H0~Q1uQ1v507P7Q0:,7TS1uQ0\Q0:'7RVQ0jPTQ0\Q0:Q0YQ1NJ10H0~Q1u907VP7p+01nS1up+020S0Yp+023S1v'dS1r'7S1CQ0[Q1r'7S1LQ0hQ1uQ0[Q1rQ0\Q0hQ0Y#t#}Q1vP^p+022S0\,9bRV#;Q0i/5VRVePVp+024RV/wZ%4VRT/8<PVPTPTPZP<Q16Eqp+021S1O#2S1G,xM%4MRTQ1G#4S22'1S23PMPT%;TS24Q1GQ22Q22#;J0AP5CQQ23p+025S23PZQ23#4S22/8<S1GQ23Q22Q22PZP<Q16EqQ0|DbQ1Gp+026S1GQ1G#4S22#?S25Q17Q1GQ22Q22PpK08Q25%2VS25#@Q25#4S22#3p+028S26#@Q26#4S27#3%@MS28%3TS29p+029S2:,Lbp+02:S2;#3p+02;S2<,gb[\;p+02<S2==Ob2V?X1SQ2=-02b\?^1SQ1JQ1HQ1EQ1FQ1^Q1_Q1`Q1bPzQ19Q1?Q1:P{20cD<9v{yS2>PwQ2>CpQ1<Q1=b7b8b9X2D188<182<S2?[^2DP8p+02AS2@#4PNO2b5b@bAbBbCbDbEb>b=b4b0b0b?H22b:I2~Q0hQ1r+0NeJ10H0~Q1LQ1C507P7P6g0:m8S1LQ0]fcS1C$2<S1r'7Q0]Q0i#VS2A'7H0jS2BQ0YQ1Y'7S1Y9078XH7P7Q0_P6Q1L20E6gS2CP8H0jQ1Y507XH7g050GS2D&0V8S2E&0V2S2FP=&0V4?0281<341<32'5S2G[1<421<48'5&0V3?042[S2HQ2G&0V5?034[B2}428P8n2001000000120000000Y04W~WSS2GQ2DQ2EQ2FQ2H_04]~]SS2DP8P6P6Q1LQ2CQ0a-0E6S2EH0jS2FQ1YQ2C,<6S2HQ2E,<6S2I'^/:xQ1OQ1}5=6S2J,58X<DS2KPgQ0d-0E6,<6,^8/:xQ2J'5X<DQ0a1^i8/:xQ2J'5X<DQ0a,^gS2JQ2K19bVS2K#;Q2K,5gS2KeS0dQ2KQ1v#2S2L,xMQ2L#4S2M,1TS2NPMPTQ24Q2LQ2MQ2M#;J0APACQS2MQ2Np+027S2OPZQ2O#4S2P/8<S2QQ2OQ2PQ2PPZP<Q16EqQ12DbS2PQ2QQ26Q27#?S2RQ17Q26Q27Q27PtK08S27Q2RQ1G#2S2S#@S2TQ2S#4S2U#3S2VQ2;#@S2WQ2;#4S2X#3S2YQ28Q29Q2<,LbS2ZQ2=#3p+02=S2[,gb[\;S2\p+02>S2]=Ob2V?X1SS2^Q2]-02b\?^1SS2_Q1JQ1HQ1EQ1FQ1^Q1_Q1`Q1bQ0;Q0D#rS0D61QD/h>$0L00PzQ19Q1lP4P@P2&0>3I0^Q1:P{P{Q1wQ1>00OyS2`+1JPwP{Q0=$069X{|S0=PwQ1>-0OyS2aQ1w600{CpI0iQ1<Q1=b7b8b9X2DX;DXFDXGDAu428Q1|1^43/55[[^2D^;D^FD^GDP8p+02BS1wQ2]==6VQ1CQ0qQ0iPkO6b5b@bAbBbCbDbEb>b=b4b0b0b?b:Q2J/:xQ2JQ0dQ2KQ2L$0SQ2L,_gS2LeQ2LQ25,_i%4iS2LQ22'5S2bQ1PQ1TQ1UPiQ2LQ2L#;Q25Q22Q22#;N90KP8CQQ2bQ23#2S2b,xMQ2b#4S22,1TS25PMPTQ24Q2bQ22Q22#;J0APFCQS22Q25Q2:PZQ2:#4S2L/8<S2cQ2:Q2LQ2LPZP<Q16EqPoDbS2LQ2cQ2;Q2X#?S2dQ17Q2;Q2XQ2XPsK08S2XQ2dQ26#2S2e#@S2fQ2e#MS2eQ2=#@S2gQ2=#4S2h#3S2iQ28Q29%@m%MmQ2],Lbp+02?S2j#3p+02@S2k,9bS2l#?[\;Q2@=Ob2V?X1SQ2@-02b\?^1SQ1JQ1HQ1EQ1FQ1^Q1_Q1`Q1bQ1wQ1G'N,Lbp+02CS2mQ2O'N#3p+02DS2nQ26'N,gb[\;p+02ES2oQ2:'NS2p=Ob2V?X1SQ2p-02b\?^1SQ0HQ0F'hS2qQ0I#rS0IQ0I001>S2r40q$0LQ1dQ0D'hS0DQ0DQ1kQ2qQ0D+01Q1s#IS1sQ1g62|D-2;DS1gQ0GQ1gP>Q1kQ2rQ1W40qI0nI0n$0L00Pz+0PQ19Q1lP4Q1mP2&0>AS2r:07@3I0^Q1:P{Q1pPwP{Q1s$06S1s9X{|S1WQ1sQ1o5v{5a{PwP{P{Q1sQ2`+1JPwP{Q0=Q1y5a{PwP{Q1sQ1t5X{S1yPwP{Q1xPwQ2a9X{|Q2aQ1o5v{5a{CpFKI0iFKQ1<Q1=b7b8b9X2DX;DXFDXGDXKDXQDXJ[Q1aB0499xAuA34Q20/AP11FPS2a%3BS1x1^ABS2`Q2`<04x[[[[[[^2D^;D^FD^GD^KD^QD^J[P8Q2p/1IPpQ2mQ2:5=6Q2pp+02GS2:Q0vQ10P3Q0rPlQ0xQ0sQ18O=b5b@bAbBbCbDbEbgb^bRb>b=b4b0b0b?bNbMb:820xDkQ2IQ0aQ0dQ2KQ2MQ2NQ2PQ2QQ27Q2RQ2TQ2VQ2WQ2YQ28Q29Q2ZQ2\Q2^Q2_Q1JQ1HQ1EQ1FQ1^Q1_Q1`Q1bPzQ19Q1?Q1:P{Q1{PwP{Q1@PwQ1@Q1{5a{S1{FKQ1<Q1=b7b8b9X2DS1@188xS2IQ1BQ1S@0[4xRp[[^2DS1SP8Q1CQ0gQ0jO3b5b@bAbBbCbDbEb>b=b4b0b0b?b:+1IDkQ2HQ0dQ2KQ2MQ2NQ2PQ2QQ27Q2RQ2TQ2VQ2WQ2YQ28Q29Q2ZQ2\Q2^Q2_Q1JQ1HQ1EQ1FQ1^Q1_Q1`Q1bPzQ19Q1?Q1:P{P{Q1;Q0N$0x62>D-1~yPwP{Av{|yS1;PwQ1{CpI0iQ1<Q1=b7b8b9X2DQ1Q,18%?2Pp[[^2DP8Q0qPlQ0vO3b5b@bAbBbCbDbEb>b=b4b0b0b?b:-1IgDkQ2F,<6Q2CQ2E+2{DkO4b3P6Q1LQ1C-0E6S2EQ0_H0jp+01oS2CQ1e'7Rp507eQ2CQ0iQ0_41OQ0i+0zQ2CQ0iQ0_41|EZP6Q1LQ2EQ0]Q0i+0zH0j=07peQ2B=07peQ0]Q1LQ1rQ2A42z'7Q0]Q1LQ1rQ2AH2vEZQ0]Q1CQ2A'S'7=07pRpePpQ0YQ06Q0\Q23'dRpQ1}H1FQ1YQ0Y/7pQ0YQ1}'7+0I507RpePpQ0rQ0^Q0YQ2CQ1uQ1OQ0^603MQ1OQ0^603gPMPgQ1OQ0^Q0_PAJ2uQ0_H1Eg010`p4p710S0_P[\8S1Y&0d2S0]&0d4S2AP=Ae3289[34A[534A[532'ARp[A[342A[348'AAe5429[53[S1rAe9349[95\pP3P4P2P8H2sP8n2001000000120000000Y0:Y09WwWkQ0_Q1YQ0]Q2AQ1r_0:_09]w]kP8PCP`PVQ2CQ0YCzS0_:2pU`S1Y%ViRpQ0qQ0r'BQ0r80FeS0]Q0r,EmS2A3mS1rQ0r/SpS1L-0lHS2B$2oS2E%>VS2FQ1L805HS1Q+1yS0N+1yRpQ2FQ1Y=[CpQ1YQ2F5[CPCQ1YQ1rQ0NP7P_Q0s/Bl@0FelS0N1<68RpQ0n/ElS0n,1p3|XH7Q0cQ0NQ0n,187|8X<DQ0]Q0c'1Q0cQ2A'1Q1G,9bS1G#;Q0rQ1G'5S1GeS2_Q1GQ2b$0SQ0rQ2b'_S2beS2^Q2bQ2S,_l%4lS2\Q2U'5S2ZQ1PQ1TQ1UPlQ2\Q2\#;Q2SQ2UQ2U#;N90KP8CQS2UQ2ZQ2O#2S2S,xMQ2S#4S2\,1TS2YPMPTQ24Q2SQ2\Q2\#;J0APOCQS2\Q2YQ2<PZQ2<#4S2S/8<S2WQ2<Q2SQ2SPZP<Q16EqPrDbS2SQ2WQ2=Q2h#?S2VQ17Q2=Q2hQ2hQ14K08S2hQ2VQ2;#2S2T#@S2RQ2T#MS2TQ2]#@S27Q2]#MS2QQ28Q29Q0m#@S2PQ0m#MS2NQ12Q0p;UeS2MQ0p+1vQ2M#3Q0z#3Q0q,BoQ0q80Fe#3[[Q2@,LbQ1w#3Q2m,9bS0q#?[\;Q2n=Ob2V?X1SQ2n-02b\?^1SQ1JQ1HQ1EQ1FQ1^Q1_Q1`Q1bQ2p,LbS2pp+02FS2nQ2;'N#3Q2:Q2<'N,9bS2M#?[\;S2Kp+02HQ2='NS0d=Ob2V?X1SS2HQ0d,9bS0d#3\?^1SS0jQ2MQ2oQ2<5=6Q0p42lS2MQ2nQ2=5=6Q0d;u8X<D-1HDS0dQ04PDQ2:Q2[5=6p+02IS2:Q2['N,9b;u8X<DS2n1Bfn@0Fen/1mP8Q2:Q2j5=6p+02KQ2j'N,9b;u8S2:AUKoe00|o%Wo$1sS2=Q18?UteS2oQ2o/Et,^tQ2o/:t'B'5[Q2o019t%?tS2oAUvreS2J/:rS10Q10<04r[Q2J014r18r1S2JQ1I?UseS10/:sS2`,8sQ2`+0p[Q1000vs%WsS10Q1MQ13;UeS2`Q13'E#W[Q2`Q13+1<Q13#WS2`Q1NQ14;UeS1kQ14':Q1k'5[Q1kQ14'EPDQ15=U}eQ15':PDQ1800|u%Wu$1sS1k1Evk,^k1:vk'B,5v[219vk%?kS1gQ1I/:fS0GQ0G<04f[Q1I014f18f1S0GQ1M/:qS0D,8qQ0D+0p[Q1M00vq%WqS1MQ1N/Ej#W[Q1N01<j%WjS1N1:}K/5}[1E}KPDQ1KQ18':PDP=p+02XS0Dp+02NS2q5=6S2s#3S2tQ2s/8xS2s11PoPnp+02ZS2up+02PS2v5=6#3S2wp+02[S2xp+02QS2y5=6/8xS2zPPPkO1S2{Q1|@0[5}S1|P]PfO1S2|Q0O#3S2}Q0OQ1K40[S2~P`P8PHO2XL;p+02cS30,gb^L;S31P=Q1x18BJS3211\uP4%3PS33Q0f,8OS34P=%3RS3518R~S3611cjP9%3cS37Q0PQ1['8S1[Q0L#rQ0;Q0K#r61QD'hQ0J#rS0JQ0JQ0F%rYS0;'hQ0JQ1]Q0E001>+01S1]80q>I0n$0L00PzQ19&0>FPFP@P3P@I0^P4Q2r@079@P2Q1l&0>BS0E@07F@807FI0^Q1:P{Q0>$06S0>Q0M$06R>5v{S0MPwP{Q0>9X{|PwP{P{B00{>|-1q{S1lPwQ1q>11D>20cDe61pD20O>yQ0>611D600{CpPwP{Q1pPwP{P{Q1nPwP{Q05PwQ0<$0}$06R}9X{|FKPwP{B00{>}PwP{Q1WPwP{Q1sQ1>00O>600{PwP{Av{|>S0<PwP{Q0=215{O5a{PwP{P{Q1qQ1s+1~PwQ1RI0iFKFKFKFKFKQ1<Q1=b7b8b9X2DX;DXFDXGDXKDXQDX_DX}DXJ[18B9%3FS1q%WBg00[ZS05[AUAFe1^F3/BO'5[Q1aQ2}\?\S15ON%3OQ0O9uNF%?Q1{N]11QXQ0O,1N[[[[[[[[[[[^2D^;D^FD^GD^KD^QD^_D^}D^J[P8p+02jR}#>S2}p+02^S1n+0\S0F/1IS0KQ0Wp+02lRI,9bS0LPdp+02hS38Q1n'7S39,<6S3:Q1~Q0FQ1IP^P2P4Q0[Q0aQ0ePiPQPvQ1fP0Q1ZODb5WYWPP2P8O2n2001000000121000000WXWWP2P8O2n2001000000121000000b^bPbZWoWnP2P8O2n2001000000121000000c0?c0=bmbsbrbZbqc0>c0<bYbXbWbPbaW3XjDP2P8O2n2001000000121103000bbb@bAbBbCbDbEbgb^bhbRb>b=b4b0b0b?bNbMb:Q2_Q1GQ2^Q2bQ2UQ2ZQ2\Q2YQ2SQ2WQ2hQ2VQ2RQ2TQ27Q2QQ28Q29Q2PQ2NQ2k,LbQ2@#3Q1w,gb[\;Q2m=Ob2V?X1SQ0q#3\?^1SQ1JQ1HQ1EQ1FQ0|Q0{+1vQ0|#3Q0t#3Q12Q0u'E#3[[Q1^Q1_Q1`Q1bQ2pQ2KQ2HQ0jQ2MQ0dQ04PDQ2n1Esn,1mP8Q2:Q1500|oQ2=1Eut,^t1:ut'B,5u[219utQ2o1:krRt@04tr[214krQ2J1:fsRt,8s00pt[20vfsQ10Q13,Eq#W[Q13-1<qQ2`Q14,:j/5j[Q14,EjPDQ15,:KPDQ1K?Uue00|uQ1kQ1f?UkeRs1Esk,^k1:sk'B'5[219skQ1gAUJfeRJ/:fRs@04sf[214JfQ0GAU0qeRJ/:qRs,8q00ps[20vJqQ1MQ1V?UjeRJ/Ej#W[21<JjQ1NQ0f?UKeRJ/:K/5J[1EJKPDQ18=U~eQ18':PDP=Q2tQ2s11oPPnQ2wQ2zQ2{Q1|Q2|Q2~P_P8PHO2XL;Q31P=Q1xQ3211u\P4Q33Q34P=Q35Q3611jcP9Q37Q1[Q0HQ1dQ0;'hQ0HQ0JQ0I'hQ1XQ1]'hI0n$0L00PzQ19Q0EPBP@P3P@I0^P4Q2r@075@P2Q1m:07@BI0^Q1:P{Q0MPwP{P{Q1lPwQ1tQ1>-0O>Q0>611D600{CpPwP{Q1pPwP{Q1WPwP{P{Q1s20Oy>+1JPwP{Q0<PwP{Q0=215{P5a{PwP{Q1yPwQ1RCpFKI0iFKFKQ1<Q1=b7b8b9X2DX;DXFDXGDXKDXQDX_DXJ[18A9%WAQ05[1^B3/BF,5A[Q1aQ20AuB5P%?OQ1q/AQ11ONQ2a[[[[[[[[^2D^;D^FD^GD^KD^QD^_D^J[P8Q0KQ0WPdQ1jQ3:Q0FP^Q1IP2Q0[Q0aPQPvQ1fP0PhO@b5WYWPP2P8O2n2001000000121000000WXWWP2P8O2n2001000000121000000bhbPbZWoWnP2P8O2n2001000000121000000c0?c0=bmbsbrbZbqc0>c0<bYbXbWbPbaW3XjDP2P8O2n2001000000121103000bbb@bAbBbCbDbEbgb^bhbRb>b=b4b0b0b?bNbMb:H1EQ0c-0E6,<6Q0cQ2_Q1GQ22Q25Q2LQ2cQ2XQ2dQ2fQ2eQ2gQ2iQ28Q29Q2[,LbRhQ2]#3Q2j,gb[\;R0Q2k=Ob2V?X1SR>Q2l#3\?^1SR=Q1JQ1HQ1EQ1FQ1^Q1_Q1`Q1bQ1@Q1SP8PiQ0hQ0iO3b5b@bAbBbCbDbEb>b=b4b0b0b?b:+1IDkQ0]1<6_RuQ2A,1u3|eQ0\@1Oi_00ziQ0\@1|i_EZQ0]20z`i,<6RuQ2A,1u3|ePUP`Q0_Q1rH1oePCQ1YQ2EQ1QP717`HRuQ1L,7`Rn+0I&0rp,{pXH7P7Q0\/7HR~Q1~,7_00I8,<6RJ&0rJ'{XH7P7P~Q1vQ1~'7-0I8,<6RJ&0rJ'{XH71<6~RJ00:JRs/:xQ1A00p8X<DRtPDP11:8xS1QQ1Q$0r'{X<DPDP1PtQ2_Q1GQ22Q25Q2LQ2cQ2XQ2dQ2fQ2eQ2gQ2iQ28Q29PhP0P>P=Q1JQ1HQ1EQ1FQ1^Q1_Q1`Q1bPzQ19P@Q1:AX{||Rt=a{tQ1<Q1=b7b8b91111Rt/AtP8b5b@bAbBbCbDbEb>b=b4b0b0b?b:1:1xQ2_Q1GQ22Q25Q2LQ2cQ2XQ2dQ2fQ2eQ2gQ2iQ28Q29PhP0P>P=Q1JQ1HQ1EQ1FQ1^Q1_Q1`Q1bPzQ19P@Q1:Q1o>00{|-1q{Q1<Q1=b7b8b9%WxQ05[P8b5b@bAbBbCbDbEb>b=b4b0b0b?b:-2ixEZPs&2hJEZ20I~~,<621m~~DkPuP9EZPnP4EZQ06Q1L82=H,7`P`Q06PHQ1LH1FEZQ2B9=6`Rn&0rn'{ePUP`Q0_Q2EH1oeQ0\P`Q0\PVQ2CQ0YCzQ0_Q2FPHQ1LPgP4Q09Q0901MDQ21$2gQ09PDP2P8H2f30P7Q23/74Q0b/74Q0vQ23Q0bP4Q0`Q0vQ1zP4P2P8PdJ2eJ10H0~Y0QZ1;DY14N:2dJ1iJ1iP`PVQ1OQ0YQ2CPAJ1aH1EO5b3PUQ0^Q0^Q1vQ1uQ2CCz%VgRgQ0z/Bi@0FeiQ11/EiQ1}1SigRgQ1v#>RiQ1}<05g423H1{=eCiH0yQ02P`PVQ1OQ0YQ2CP_Q23Q0r#VR_Q0NQ0n3mQ1~1Sl_R_Q23Q1~<0b_Q26Q21/`_PYGoQ0\Q1OQ0YI0]PAp+02OR_#t#}p+02LRV62Bmg03<7Rm$0dS0YQ2v#t$1_&1YmS2v30PUQ0mQ0mQ2yPVp+02MRVCzQ2y#>H0y&0s7S0m&1hV&1:7S1O30Q0pp+02SRV$0XQ2q41XQ00&0U_p,3FS0S2q30p+02UR_$1?#yQ0mQ2y$1gQ1O30[21M77Rm$0dS0\Q2y#T$0Z&2cUS2y30p+02R#T$1ep,5LIMITS26'5Q0tQ0D#]%TV#i41dQ0up+02YRV$0op+02T#TR`$0Z%i`5em41Z%]V+0Y%T_#i$1cp+02V$1bB2a778,<6R_#?B2_778,<6RVQ0?$0CR`':#W1:_`#Wp,1A$2^1BV_g01k_'17|VRV'A41DZ08mS0?p+02W#T#i5[mPVZ08mS0uQ0D$0e5[mQ2u#T$0D,j8#6Q2x#T#i,j2#6[^<DQ07g03=;RV&2]8R_g03>;30g03?;90V_+2\S2x21jo2p+02\#TRo$0D61[m[WOp+02_Ri#]+0YQ07g03@;90V_S2u&2[4S0D9=6rR_&2Z4S239=6r,B_,8p7|p1<62S0n%TiR_$0D'j#y&1`2S0N&0ei+0w+1f[^L7[WOp+02`RV#]+0Y&0Zo%io5em$1^p+02aS2C$1L'1Q30$0o1:8`#WS02Q1n#TR`$1k,<6,18&0Z`%i`5emg03A;S1}<1w841D7|8XxD-1HD&1P`Q30$0?,7r507&1]_,<6&1P_,<6'1&1nVp+02eR_$1S'1Q14p+02fRr+1G$1r&1>r'1Q15p+02gR`+1Gp+02bS15+1xPkp+02iRop+02dS14P8H1z#6Q0n%T_RC#iRg'j#61<64S1v%TrS11$0DS0^'j#y&1`3S1z&0e`+0w#6p+02mRn1<65S0`61uK#yQ0BP}P9O1Q0AQ0@00E1+1KS0A30[[[[[^L7p,4SINVS0@PkP_O2PfP}Q1\#VRkQ1~PdPePdQ1jPdK09Q1n1SdkRkQ2}Q1n<05kPn1`ikS1nPYGoR1P`PrP_Pf%t}#}S2}P`PnQ1nQ0ZQ0L#;Q0L,5dRuePup+02kRu#2R~$0S1_d~R~eP~p+02oR~$28RJ1w~ZRs'A%4~R|#?R@18|<R='APJPsP@P=Q17P~P|%;|R=H1=P~P|P=PZP<Q16J1;J2VQ1c%2IR='_Q1c#4R|%4=R@'5RsQ1PQ1TQ1UQ1cP|%;|P=P@%;@N90KP8CQPs%2nRs,xM%4sR@,1TR=PMPTQ24PsP@%;@J0AQ0pCQP=p+031R=PZ%4=R@/8<RsP=P@P@PZP<Q16EqQ2ODbPsp+032S2OQ2O#4Rs#?R@Q17Q2OPsPsQ2;K08P@p+030S0p#2R@#@%4@Rs#3p+034S0L#@Q0L#4R|#3Q28Q29Q1e#@Q1e#Mp+036S1e,Lbp+037S1j#3p+038S1\,gb[\;p+039RJ=Ob2V?X1S202bJ\?^1SQ1JQ1HQ1EQ1FQ1^Q1_Q1`Q1bPzQ19Q1?Q1:P{Q1;PwP{Q2>PwQ1;Q2>5a{FKQ1<Q1=b7b8b9X2D%?8Q2?%?4@0[4<[[^2DP8p+03>S2?#4PNQ0OO3b5b@bAbBbCbDbEbRb>b=b4b0b0b?bNH22bMb:P717fiS1;17fkS2>+0HQ09p+02nR>%tu#}Q0CH1\,7qR09078XH7P7Q3917qV00H8=070XH7P7Q38/7iS0b17oiRh-0H8=070XH7P7Q381d}nS1L'7R017oVRt00Hh=078XH7P7Q0b-0I020Ht81du>,7oR0507XH7Q2GQ2DP8P620I0tS2D-0HtS2GP01<6tS2FQ2D,<6S0_'B/:x1dI~9=6}S2E,58X<D1<60RhQ2F+0:/:xQ2C,7}S2C,<6R}/B8/:xQ2E'5X<D&1V0B04hhxQ2C$1VB04}}xQ159=6uR}Q0p,dn9=6uS1500:}S2C'BS2E/:x1d>=9=6IRh,58X<D19b~S2F#;Q1hQ2F'5S2FeQ2F%2>S2F$0SQ1hQ2F'_S2FeQ2F%2~S2F,_GS1h%4GS2BQ2F#4S06'5S1oQ1PQ1TQ1UPGQ2BQ2B#;Q2FQ06Q06#;N90KP8CQQ1o1xM@11TsS1oPMPTQ24P@Ps%;sS06J0AQ0sCQQ1oQ0LPZ18|<S1oQ0LP|P|PZP<Q16EqQ2;DbQ1op+035S1oQ1o#4R|#?S2;Q17Q1oP|%;|S0sH1=Q2[H1WQ2;p+033S2;#2S2[#@Q2[#MQ1j#@Q1j#MQ28Q29%@H%MH1LbJp+03:S1j#3p+03;S2[,gb[\;p+03<RJ=Ob2V?X1S19bJS2B#3\?^1SQ1JQ1HQ1EQ1FQ1^Q1_Q1`Q1bPzQ19Q1DQ1:Q1>Q1>:1pDy611D:00{yQ1<Q1=b7b8b9X2DX;D20:82,B2,58^2D^;DP8Q2;9=6JQ2?p+03A'd9=6JO2b5b@bAbBbCbDbEbRb>b=b4b0b0b?bNbMb:Q15Q2E'5PDPhQ1QQ2O,d~9=6nRJ'5X<DPh158JX<D%;h1:hxQ0p,9bRJ#;15GJRJePJQ2F$0SQ1heQ1hQ1i/_@Q1i#4RJ/5sRyQ1PQ1TQ1UQ1iPJ%;JP@PsQ06N90KP8CQPy%2=R=,xM%4=Ry,1TRsPMPTQ24P=Py%;yJ0AQ0{CQPsQ1oPZ18|<RsQ1oP|Q0sPZP<Q16J1;Q2<DbPsQ1eQ1e#4Rs#?R<Q17Q1ePsPsQ2]K08P<Q0L#2R<#@%M<Q1\#@Q1\#MQ28Q29Q1~#@Q1~#MQ1j,LbQ2[#3Q2B#?[\;p+03=R;=Ob2V?X1S202b;\?^1SQ1JQ1HQ1EQ1FQ1^Q1_Q1`Q1bPzQ19Q1?Q1:P{Q1{PwQ1{CpQ1<Q1=b7b8b9X2DQ1AQ2I'AQ1B@0[2x[^2DP8p+03?p+03B'd9=6;PaO2b5b@bAbBbCbDbEbRb>b=b4b0b0b?bNbMb::20hxDkQ309=6IR;20:h;'BP8J0{bPQ2C/:x,B}/:xQ2C@2U}xDkbab3Q0_21m0tDkQ2G,<6Q2D-2qtDkO4b3Q39PlEZQ1L,7fQ0kEZQ0bQ39+0HQ09PnQ2}Q0CH1\,7fRn507eQ1;Q0lEZQ2>Q0vEZQ08@2=ik,7fPfQ08PiPkH1FEZQ1n,7f=07neL2r%t1Rn#}>2Bf`eQ0YQ2v'lQ0Y&1_nQ2v30eQ0rPUPfPfP1P_PrCz%>1H0yeQ0WQ0m&1h_Q1O30eQ0V&0X1>1Xf_eQ0PQ00&0U_Q2q30ePc&1?1#yQ0m&1grQ1O30[ePaQ0\&0ZCRUQ2y30ePR&1eCQ26'5eP]%]1Rn>1dfgeP\&0o1AemUgRU61Zf00YnePW&1cgePX&1b_ePQQ0?=[mgeQ0OQ0u&0e_5[mePNQ0^,j8#6%T`R`#iRg,j2#6[^<DePOQ07Q2x21jj2&0D`61[m[WO00YnePPQ07Q2uQ0D9=6KR`Q239=6K,B`,8p7|pQ0n%To$0D'j#yQ0N&0eoRo+0w+1f[^L7[WO00YnePF&1^U&1L1'1ePBPu%VdRdQ21Q1cPeQ1cQ0:Q1cK09PiQ1c/SdRdB0buidP>1`VdPYGoRd$0oQ02Q11$1k,<6,18Q11$0ZQ11#i5emQ1}<1w841D7|8XxD-1HDePA&1PCRm&0?1,7f507eP9&1]C,<61<6m'1eP5&1n_&1S1'1eP321Gf1Rm$1r&1>1'1eP421xm_eP2PqPdPrP8H1z#6Q0n/jg#6Q1vQ38#T$0D'j#yQ1z00wo#6P~%VGRGQ1uQ1iPeQ1iPHQ1iK09Q30Q1i/SGRGQ30>0b~GQ2OQ14/`GPYGoQ0`61uv#yQ0BPIP9O1Q0A30[[[[[^L7eP8Q0@PfPrO2eNP2TY0|Y12Y0uY0gY0jY0zY0iY0}Y10Y0oY0wY0vY0qY0hY11Y0{Y0nY0tY0rY0yY0~Y0lY0kY0mY0pY0sY0xQ0ZQ0XP^Q0WQ0VQ0PPcPaPRP]P\PWPXPQQ0OPNPOPPPFPBPAP9P5P3P4P2P8OKn50000010000001K111O11J11G11D11B11C11U11P11I11K11E11R11W11?11H11M11N11F11V11T11@11Q11A11>11L11X11Sc0LQ00Q1u$0U'lO7c0Rc0Xc0\c0Nc0Tc0JY0FY0DP2P8O2n2001000000121000000W3Y0CP2P8O2n2001000000121000000W3Y0BP2P8O2n2001000000121000000W3Y0GP2P8O2n2001000000121000000W3Y0EP2P8O2n2001000000121000000W3Y0HP2P8O2n2001000000121000000c0cc0MbVbLc0[c0Zc0]Y0YZ19DP2P8O2n2001000000121103000c0Pc0Ob6WbY0SP2P8O2n2001000000121000000bLc0Vc0Wc0Kc1<c0fWcQ0|P8Q0zK2SW3P8O1b3WIW[Z15DP8O1Q0oQ0t#>Q0k+0=&1:DR530Q0QQ0t#P50LPLQ0QQ01P:P[P8Q05P?n10110;00021000000Z07LR?g015SR[Q0}P8J0{Q05Q0~01B8b3WIW[n10110;00021110000P8P4O2b[c0;WIW\Z16DP8O1Q0oQ0x#>Q1C+0@;05Q0QQ0x#P50LPLQ0QP?P[Q0wP8J0{Q05Q0y01B8b3WIW\n10110;00021110000P8Q0gO2b\c0;btb3bpb3blb3bvb3bub3WvWuP2P8O2n2001000000121000000b6WlW6P2P8O2n2001000000121000000b6WpW6P2P8O2n2001000000121000000b6WtW6P2P8O2n2001000000121000000b6Y0^W6P2P8O2n2001000000121000000b6Y0_W6P2P8O2n2001000000121000000b6Y0UW6P2P8O2n2001000000121000000b6WIW6Q0T#yQ0QQ0U50LPLQ0QP?P[Q0RP8J0{Q05Q0S01B8b3WIW6n0110101020100P8P9O2b6c0dc13bHWcWIY0bY0IY0aY18Y0AY0`Y0@Z06:Z05:Q03PMP8P3P4P2I1lZ05:+2ReY0eZ17DZ1:Eg0:mdeo"). Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma listZ_eqb_eq : forall x y, listZ_eqb x y = true -> x = y.
Proof.
  induction x as [|a x IH]; intros [|b y] H; cbn [listZ_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. rewrite (IH y H2), H1. reflexivity.
Qed.
#[using="Type"] Lemma spieces_eqb_eq : forall x y, spieces_eqb x y = true -> x = y.
Proof.
  induction x as [|a x IH]; intros [|b y] H; cbn [spieces_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. rewrite (IH y H2). f_equal.
  destruct a as [l|k], b as [l'|k']; cbn [spiece_eqb] in H1; try discriminate.
  - apply listZ_eqb_eq in H1. congruence.
  - apply Nat.eqb_eq in H1. congruence.
Qed.
#[using="Type"] Lemma shape_eqb_eq : forall x y, shape_eqb x y = true -> x = y.
Proof.
  induction x; intros y H; destruct y; cbn [shape_eqb] in H; try discriminate;
    repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end; try reflexivity.
  - apply Z.eqb_eq in H. congruence.
  - apply Z.eqb_eq in H. apply spieces_eqb_eq in X0. rewrite (IHx _ X). congruence.
  - rewrite (IHx1 _ H), (IHx2 _ X). reflexivity.
  - apply expr_eqb_eq in H. apply Z.eqb_eq in X1. rewrite (IHx1 _ X0), (IHx2 _ X). congruence.
  - apply Nat.eqb_eq in H. congruence.
Qed.

#[using="Type"] Lemma find_disj_sound : forall E M k b1 b2 c1 o1 n1 c2 o2 n2,
  know_ok SEGS E M k -> find_disj k b1 b2 = Some (c1, o1, n1, c2, o2, n2) ->
  estart E (SA c1 o1) + elenZ E n1 <= estart E (SA c2 o2) \/ estart E (SA c2 o2) + elenZ E n2 <= estart E (SA c1 o1).
Proof.
  intros E M k b1 b2 c1 o1 n1 c2 o2 n2 HK. induction k as [|K k IH]; intros H; [discriminate|].
  inversion HK as [|K' k' HKK HK']; subst.
  cbn [find_disj] in H.
  destruct K as [| | | | | | |[d1 p1] m1 [d2 p2] m2| |]; try exact (IH HK' H).
  destruct (expr_eqb d1 b1 && expr_eqb d2 b2)%bool.
  - injection H as <- <- <- <- <- <-. exact HKK.
  - destruct (expr_eqb d1 b2 && expr_eqb d2 b1)%bool; [|exact (IH HK' H)].
    injection H as <- <- <- <- <- <-. cbn [kentry_ok] in HKK. lia.
Qed.

#[using="Type"] Lemma disj_side_fact_sound : forall E M k cA oA nA cB oB K,
  know_ok SEGS E M k -> disj_side_fact k cA oA nA cB oB = Some K ->
  0 <= estart E (SA cA oA) -> estart E (SA cB oB) < 2 ^ 64 ->
  estart E (SA cA oA) + elenZ E nA <= estart E (SA cB oB) ->
  kentry_ok SEGS E M K.
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
ltac2:(KReplay.run1 (kr_t_AsanPlanSound ()) ["FPX_3"; "Sound"] "p'0h01Hh11zi001zh24__x1h34__x2h44__x3h54__x4h64__x5h72H0h84__x6h93Hbrh:2Hth;2Hnh<7__arithh=4__ffh>6__sat2h?6__sat3h@8__varmaphA5__withB1bi011bhC6heq_uAhD6heq_uBhE6heq_uNhF1ni021nhG2H1hH2HahI1KhJ4__p1hK4__x7hL1ehM1mhN1oi031ohO2BhhP1EhQ2E1hR2E2hS2HAhT2HBhU2HKhV3HlehW2LnhX1MhY2RAhZ2RBh[3RnAh\2_Hh]3bhii043bhih^3bloh_2cAh`2cBha1ki051khb2nAhc2oAhd2oBhe1pi061phf2uAhg2uBhh2uNi071xp%0p&0p;1p;4p;6p;3p;2p;7p;9p;8p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0g0038R5p4p710R6p9P0p1003Vp4p710R7p9P0p1004Np4p710R8p8P0p1004ep4p710p8P0p1005FR9p4p710p8P0P9p4p7210p8P0p1005cp4p710R0p8p100_Jp4p70R9g00;\R:p4p710R;p8P9P1p8P9P2p8P9g0079R<p4p710R=p8P9P4p8P9P3p4p710R3p8P9P7p8p1006?p4p710P6p8p100`:p4p70R9P;p8P9P1p8P9P2p8P9p100`hp4p7210p8P9P=p8P9P4p8P9P3p8P9P6p8P9P7p8p100aDp4p70P=p8p100bCp4p7210R9P1p8P9P2p8P9P=p8P9P4p8P9P3p8P9P7p8p1062Tp6051000R9P6p8P9p103VIp4p710R;p8P9p1063Vp4p710p8p106kQp6051000R9P8p8P9P6p8P9P;p8P9P0p8p107<2p6051000R9P8p8P9P;p8P9P0p8p100bop4p70R0P1p8P0P2p8P0P4p8P0P3p8P0P7p8p1006\p4p7210R7P=p8P7P6p8p1007Up4p7210P6p8p10082p4p73110P6p8p100cep4p710P6p8g008Nj1NTg00dlj1}Tg00eJj1yTg01SnR6j1aTg00F?j1|Tg02U9k40KTg0;>ek60FTP:j31Tg03iTj2]Tg03fQj2ZTg0093j1qTg018]k20NTg00>Pj2>Tg03gQk20LTg00=Lj20Tg00:Bj22Tg099ej2WTg00O0j2VTg00emR:k20ETg06]5j2MTg0;?lj24Tg044Dj3eTg00J2j1^Tg03ETj4GTg030Cj2[Tg01Gmk409Tg05XUk606Tg01POj2ITg01QJk301Tg00>lR7j2LTg01Qmk200Tg09DZj7~Tg06`9m90MTg01=4j28Tg017fj1pTg00iHj25Tg04JVj1dTg05B?j3bTg05C@j3HTg00<lj2DTg01L1j2oTg01>6k20JTg01>^k30ITg00A:j1UTg00AYj2PTg00E?k10DTg00]4k10CTg00F_j2`Tg00G[k10ATg00H9k10@Tg00JTj1jTg00K9j2zTg00Hdj2xTg01LWk30?Tg00NNk20>Tg00OJk20=Tg00P6k30<Tg00PUk40;Tg07Poj3hTg0:iJj3sTg00^Vj2\Tg00^3j3rTg00K\k608Tg08c<j1uTg07Onj2tTg09=\k207Tg057nj4gTP5j6_TP<j6fTg0148j2kTg01Plk205Tg09<_j2{Tg00Cjk304Tg00DSk20BTg00E_k303Tg00G=k402Tg00IGj4mTg00RFj7nTg00Mkk30GTg00L@k70HTg00Rjj8YTg03GPR<f0R5'[p=6g00VPR=/25p=9f2R0,I=f1R3/I5+05p=C1403/{5p=wf3R4/{0?e35p=Bg00ZZR2g00[:S00715p=?1I=5p=l1835,50p=312401235'Lp=71\03/D5p=A1003/D5p=K1D03,04/D5p=Jg00UMR1?135p=:1V15p=FB04135p=;g00X9-0B5p=Sg00VnR9@0335p=RP1P0P3P5H02p=E1z15p=QP0g00SNR;g00SmR8P8g00TMR>P1P3g00YLR?P5Cmg00TmR@Fnp==B0G135p=<P1P3g00XeP5Cmp=iP3P;P8P8P>P5P@Fnp=vP1P3P?P5Cmp=XP0P;P8P8P>P3P5K0Hp=cf4R?P;P8P8P>P4P;P8P8P>P0P@FnP3P5GYp=Of6R@P;P8P8P>f5RAP?P4P;P8P8P>P0P3P5GYGYp=TP1P?P4P0P3P5E_p=@P4P;P8P8P>P0P3P5GYp>0:g00n`g00UkRB#NRC#NS01#NRD#N#N#NRE#}RF#yRG%}D#y#a[%|<g01IES02Q02Q02p,4SEGSRDf8RHf7RIP@H0K%a<RJPIP@PAP?P4P0J0F%6331f:RK1]I@'Z#9f;RL1]A?'Z%qCRM%qERE+0NRN'>f<ROf9RP/]H'Z20LOI'01]@A,ZO'21WLH%a1RQ1VQ51WOP=1Q5P6P1f>RR/WL=1Q5P6P1PJP3P620E11RSPJf@RT/MORUP:P1P1PJP5P2PJ105RRV9C44f?RWfBRXfARY'47wRRZ?e4V#6%^<R[n0100000020000n2001106000120100104P[n10110700021010600P[n10110700021010200%6PS0351JPDPXPYPKCGS04]0];P31WWO1[1551QP6PSPJPUP:P1P1PJP5P2PJAC??VAeZ?V#6P[n0100000020000n2001106000120100104P[n10110700021010600%6K51Jf=RZ,MY%aSRV1VV51MXR=1V5P6PSfDRU/MT=1V5P6PSPJP3P:P1P1PJP5P2PJfCR\,05R]9CPP14U\fGR^fFR_'4PPP]CB#6P[n0100000020000n2001106000120100104P[n10110700021010600%6WS0551JPDfHR]P^PTCGS06]0]9P3P:P1P11M_X1[S551VP:P1P1PJP3P2PJ105UR:9CKKfER`/4U14]^PKP:CB#6P[n0100000020000n2001106000120100104%6Y51JPDfJR:fIRaPXCG]0]9P51Ma`P1P1P3P5H09,[S51VP2PJ103`Rb9CLL14_`14a]PLPbCB#6P[n0100000020000%6U51J100_9COOP21V25104^9CZZ=125P210AaR^9CWW=125P2PJP3fKRb/4:fNRLfMRc'4PT10@:CBRd#6ReP[n0100000020000%6aS0751JPDfRRffQRgP:CGS08]0]:P310?]9CRRS09#?14:afLRh,4cRiPWP^CB#6%6]S0:51JPJP<P6P<P<P5P514hbfOR^/4LRjPY10IbCBRkn10110300021010500XLJPeQ07P5J06A1<daA1<k:P<PifPS0;/4^PX10HhRhCBPDfTR^fSRiP5CGXI<%lXRk1IXhRh<014%?k%?h'LP7%l\#?10Pc,I\#?PDfUS0<P^Pj14fgPU10KLCBCGP5%l`#?Q0;,0O,I_#?P71I35#?1203[RO12351I03#?Rg[1240\g20035P3n2001000000120000000XM1XF1RgPO^M1^F1ROP5P=P]P0O3%9]PgPOP5P:10T^RTP4O312:Tf\RTf[ROfZRgfWRjPbPiP:F~A3FTj,2bPDf]RcPTPOPjP\PXP^PYN90MP\A3FcjRjPjPXC7P7f^R7fXRj53FRh,2U12h\PDf_RhP7fY/4j14TOPL10UjCBCGP5f`Rj=3Fg,2_faRL=3FO/2_fbR_/8cRO#p15FORO#91>ON'LPGg05DTROfcRkg05ChRd%dTS0=7bcS0>'8S0?%dhS0@9bdjS0A,8kS0B3HPi15F5RePe10acRaC7XBGPG18kcS0CQ0=,8kS0D5HdRePifdRl%djRm9bdL'89HO5,5FRnPnPaC7XBGPG18kjRnQ0@,8kS0E5HdRoPi18l7Rp%dc,8lRq5Hd=HO5,5FRrPrPaC7XBG15FeS0F15FoS0G;ANPiP5P5PaC7X11Q0C,5FS0HQ0D,5F;KNS0IPi18lLRG18lm5Hd,5F=A5NRmPmPaC7X1115FnRmQ0E,5F;KNS0JPi15FpRr15Fq;KN?A5NRqPqPaC7X11g04Q:Rq,DTS0KPiAKr5N15FGRG1oFj,5F;KN;ANRsPsPaC7X111DhqS0LPiPrPcPqPNCJAKG5N;ANRGPGPaC7X11%pn%9m1>mN'L%pp%9r1>rN'LfeRr=3F_S0MP1ffS0N=3FjP1fgRp=3F_P1103LRa/DN100_,:5X11fhS0O=3FkRG#F1:5GRGePGfiRG=3FkRi#F1:0iRiePifjRi=3FpRs#F1:?sRsePs20JMES0P1>=M%9E1>=N[[S0Q%9MRsg0157S0RB0IME3UWHS0SQ0R%9N[^HsS0Tg00WZRs#URE#URt#US0U#URu#U,P1S0V1P1uRu1P1tS0W1P1E1P1sS0X';Rs';S0Y';';#S&0D9RE'R%|9S0Z&0C1S0[1`1AR97E01`1?Rt1`1@S0\7E47E3S0]&0A1S0^&0@1Rv%jBRw#QRx%jw#QRy5=vS0_%^8RzPv%jC#QR{%Nw#QRw'<R|/<y1z1BRB%QCRC'<R}5=vPzPv1x1M>0?1FRM,i},vvS0`PzPv1x1=R~==v|PzPvPv1X~xPzA=v~}S0aQ0`5cvDOS0bFTFT20>v>S0cP5P0Q00,V220=50#?dB0<1=3H0;S00b=b@bAX21X31X41X51X61X81120AS0d10?AS0e/0@1030R='21004/>NS0f10@IS0g#9S0h%9@10A@R|#9S0i1>|N'L[S0j[[[[^21^31^41^51^61^81P5P@PiPHPcPpPIPYPLP_PkPUO;b<b>b?bCbDbE9haNP3PLPNPNCJRUAsL3ND@1:Ua104rRU/DNQ0N,0?S0k,:5X11A3FGlRa#F1:3aRaePaA3FilRa#F1:4aRaePafkS0lQ0O53FRa#F1:AaRaePaQ0PQ0QQ0SQ0TQ0VQ0U,P1Ra/;s,;u';#S/REQ0ZQ0]Q0^PvQ0_PzPv1<}y1<w{RY5=vPzPvPv1iYMPzPvQ0aPzQ0bH0:DOFTQ0cQ00b=b@bAX21X31X41X51X61X81Q0d10=@10A?'210@A/>N104?RY#9Q0j[[[[^21^31^41^51^61^81P5PIPHQ0OP7Q0lPPPXP_PkPlP`O;b<b>b?bCbDbE9hUNP4PrPNPNCJR`Asr4ND@1:`U104kR`PgPAPpPNPNCJ=A5NRpPpQ0;/0lRpC7X11Q0kPg10?l?A5NRUPUPpC7X11Q0k,\`R`PgP5P5PpC7X11A3FirRi#F1:0iRieS0kPiQ0l=3FrRp#F1:?pRpeS0lPpflRg=3FGRU#F1:@URUeRXPUQ0PQ0QQ0SQ0TQ0WQ0X';,;a#S1;us#S/RE'RQ0ZQ0\9Et01`1I9E947E3Q0^PvPv1XCwPzPvPv1XByPzPvPvQ01#QRs/<{R{/<y1<CxRC'XPzPvPv1X~{PzAr1C{RC9=vB1<wx9=vC5cvDODODODOQ0cQ00b=b@bAX21X31X41X51X61X81XK1123A123I10|H/2YQ0hP?10IH,\|R|P|10P@C7[[[[^21^31^41^51^61^81^K1P5PHQ0<PgPKPGPPPhPRP\PkPrO;b<b>b?bCbDbE1D`NQ0kPiQ0lPpPXPUQ0PQ0QQ0SQ0Tp-0RUQ0X,;a,;u#SQ0Y#S/RE'RQ0ZQ0[9Et0Q0[?E497E3Q0^PvA=v~yPvP;P8P8P>PIJ085cvPzPv1<xsRs/<y==v}PzPvQ0`PzPvA=v~sPzAr1}sRs9=v~1isM,vv5cvFTFTQ0cQ00b=b@bAX21X31X41X51X61WJ%9?/LA10YA/2=Q0fQ0iQ0eQ0g'\R=#91>=N'L[[[[^21^31^41^51^61^JUP51>HNPHPgPKPGPPPZPkPlPrO:b<b>b?bCbDbE9h`ND@P?Q0NPNPNCJP5D@P4PkPNPNCJP3D@bRbQbhbgbfP^A3FrhP7PqPNCJQ0MPLPqPNCJ;ANRqPq10:7C7ebZbYPfQ0HQ0K;KNQ0L=KmN;ANRmPm10]TR]C7RmePme1oFh,5F%uhD@1oFT,5F%uTD@PfQ0IQ0J;ANRNPNP]C7eQ0GQ0E,tnD@Q0FQ0CQ0D'tD@AHOeo,5F207eoD@Q0BPkPdPjQ0@CgE_Q0?PkPdPcQ0=CgE_Q0>Q0A5bO,8kPkPOQ0>Q0ACgE_Pf14jh9wcTRc93FkRFPFP]C7ePDPkP_Aecf]CGeb[WOW\P3P5O2n2001000000121000000b0bWbGb0b7b0WGW7P3P5O2n2001000000121000000b:PbP5EfW0P5O1b7W0W:Q09g014W512Q0:91J[PJP[P6P<PUP5g00[ZRUQ0Rn10110300021000000XLJR6g015SR2Q07P5EfPUQ08/k5b7W0W:n0110100020100P5P0O2b:bBW0W9X]1X^1P3P5O2n2001106000121100100XeSP5O11M\W%^S51V%6R91J[PJP[P6P2Q05P5EfPUQ06/k5b7W0W9n10110300021110600P5P0O2b9bNW0W;XF1P5O11WZK%^151Q%6H91J[PJP[P6P2Q03P5EfPUQ04/k5b7W0W;n10110300021110000P5PAO2b;bNWVWTWSW0WUXI<Xd1W`WbXc1W_WaWXWPo"). Qed.

#[using="Type"] Lemma casedisj_sound : forall cs b1 b2 csa csb E R FULL model,
  cs_ok E cs R FULL model -> node_casedisj cs b1 b2 = Some (csa, csb) ->
  (cs_ok E csa R FULL model /\ pc csa = pc cs) \/ (cs_ok E csb R FULL model /\ pc csb = pc cs).
Proof.
  intros cs b1 b2 csa csb E R FULL model HC H. unfold node_casedisj in H.
  pose proof (co_know _ _ _ _ _ HC) as HK.
  destruct (find_disj (kn cs) b1 b2) as [[[[[[c1 o1] n1] c2] o2] n2]|] eqn:Hf; [|discriminate].
  destruct (flat_x (kn cs) c1 o1 n1) eqn:F1; [|discriminate].
  destruct (flat_x (kn cs) c2 o2 n2) eqn:F2; [|cbn in H; discriminate].
  destruct (disj_side_fact (kn cs) c1 o1 n1 c2 o2) as [K1|] eqn:D1; [|discriminate].
  destruct (disj_side_fact (kn cs) c2 o2 n2 c1 o1) as [K2|] eqn:D2; [|discriminate].
  injection H as <- <-.
  pose proof (flat_x_sound E _ (kn cs) c1 o1 n1 HK F1) as (A1 & A2 & A3).
  pose proof (flat_x_sound E _ (kn cs) c2 o2 n2 HK F2) as (B1 & B2 & B3).
  unfold elenZ in *.
  destruct (find_disj_sound E _ (kn cs) b1 b2 c1 o1 n1 c2 o2 n2 HK Hf) as [Hd|Hd].
  - left. split; [|reflexivity]. unfold add_kn. apply cs_ok_set_kn; [exact HC|]. constructor; [|exact HK].
    eapply disj_side_fact_sound; [exact HK | exact D1 | lia | unfold elenZ in *; lia | exact Hd].
  - right. split; [|reflexivity]. unfold add_kn. apply cs_ok_set_kn; [exact HC|]. constructor; [|exact HK].
    eapply disj_side_fact_sound; [exact HK | exact D2 | lia | unfold elenZ in *; lia | exact Hd].
Qed.

#[using="SHADOW_ok"] Lemma shadow_of_val : forall E M k b n sb sk sn,
  know_ok SEGS E M k -> shadow_of A k b n = (sb, sk, sn) ->
  flat_x k sb sk sn = true ->
  estart E (SA sb sk) = (bv_unsigned (edenot E b) / 8 + shadow_off A) mod 2 ^ 64
  /\ elenZ E sn = bv_unsigned (edenot E n) / 8.
Proof.
  intros E M k b n sb sk sn HK Hs Hf. unfold shadow_of in Hs.
  destruct (split_lit (eadd (mkSrl k b 3) (ELit (shadow_off A)))) as [sb' sk'] eqn:Hsp. injection Hs as E1 E2 E3. subst sb' sk'. rewrite <- E3 in *.
  pose proof (flat_x_sound E _ k sb sk (mkSrl k n 3) HK Hf) as (F1 & F2 & F3).
  pose proof (split_lit_denot E _ sb sk Hsp) as Hd.
  assert (S3 : forall x, bv_unsigned (edenot E (mkSrl k x 3)) = bv_unsigned (edenot E x) / 8).
  { intros x. rewrite (mkSrl_denot SEGS E _ k x 3 (Z_to_bv 64 3) HK) by reflexivity.
    rewrite u_srl64. rewrite u64_lit by lia. reflexivity. }
  split.
  - unfold eadd in Hd. rewrite mkAlu_denot in Hd. apply (f_equal bv_unsigned) in Hd.
    rewrite u_add64, S3 in Hd. cbn [edenot] in Hd. rewrite (u64_lit (shadow_off A)) in Hd by (pose proof SHADOW_ok as SO; unfold shadow_ok in SO; lia).
    rewrite Z_to_bv_unsigned in Hd. unfold bv_wrap, bv_modulus in Hd. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hd.
    unfold estart; cbn [a_base a_off].
    pose proof (u64_range (edenot E (mkSrl k n 3))). unfold elenZ, estart in *; cbn [a_base a_off] in *.
    unfold two64 in *. rewrite (Z.mod_small (bv_unsigned (edenot E sb) + sk)) in Hd by lia.
    rewrite <- Hd. reflexivity.
  - unfold elenZ. apply S3.
Qed.

#[using="SHADOW_ok"] Lemma shdisj_sound : forall cs b1 n1 b2 n2 cs' E R FULL model,
  cs_ok E cs R FULL model -> node_shdisj A cs b1 n1 b2 n2 = Some cs' -> cs_ok E cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros cs b1 n1 b2 n2 cs' E R FULL model HC H. rewrite node_shdisj_eq in H. (* [comment removed for export] *) unfold node_shdisj_ref in H.
  pose proof (co_know _ _ _ _ _ HC) as HK.
  destruct (split_lit b1) as [c1 o1] eqn:S1. destruct (split_lit b2) as [c2 o2] eqn:S2.
  destruct (shadow_of A (kn cs) b1 n1) as [[sb1 sk1] sn1] eqn:H1. destruct (shadow_of A (kn cs) b2 n2) as [[sb2 sk2] sn2] eqn:H2.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection H as <-.
  apply andb_prop in Hc as [Hc Hap]. apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hc Fs2]. apply andb_prop in Hc as [Hc Fs1].
  apply andb_prop in Hc as [Hc F2]. apply andb_prop in Hc as [Hc F1].
  apply andb_prop in Hc as [Hc Ln2]. apply andb_prop in Hc as [Hc Lb2]. apply andb_prop in Hc as [Lb1 Ln1].
  apply Z.leb_le in Lb1. apply Z.leb_le in Ln1. apply Z.leb_le in Lb2. apply Z.leb_le in Ln2.
  split; [|reflexivity]. unfold add_kn. apply cs_ok_set_kn; [exact HC|]. constructor; [|exact HK].
  destruct (xhi (kn cs) b1) as [h1|] eqn:Xh1; [|discriminate]. destruct (xhi (kn cs) n1) as [m1|] eqn:Xm1; [|discriminate].
  destruct (xhi (kn cs) b2) as [h2|] eqn:Xh2; [|discriminate]. destruct (xhi (kn cs) n2) as [m2|] eqn:Xm2; [|discriminate].
  apply andb_prop in Hhi as [Y1 Y2]. apply Z.leb_le in Y1. apply Z.leb_le in Y2.
  pose proof (xhi_sound SEGS E _ (kn cs) b1 h1 HK Xh1) as B1. pose proof (xhi_sound SEGS E _ (kn cs) n1 m1 HK Xm1) as M1.
  pose proof (xhi_sound SEGS E _ (kn cs) b2 h2 HK Xh2) as B2. pose proof (xhi_sound SEGS E _ (kn cs) n2 m2 HK Xm2) as M2.
  pose proof (flat_x_sound E _ (kn cs) c1 o1 n1 HK F1) as (A1 & A2 & A3).
  pose proof (flat_x_sound E _ (kn cs) c2 o2 n2 HK F2) as (C1 & C2 & C3).
  pose proof (u64_range (edenot E n1)) as Rn1. pose proof (u64_range (edenot E n2)) as Rn2.
  pose proof (u_of_split E b1 c1 o1 S1 ltac:(lia)) as U1. pose proof (u_of_split E b2 c2 o2 S2 ltac:(lia)) as U2.
  pose proof (ranges_apart_x_sound SEGS E _ (kn cs) c1 o1 n1 c2 o2 n2 HK Hap) as AP0.
  destruct (shadow_of_val E _ (kn cs) b1 n1 sb1 sk1 sn1 HK H1 Fs1) as [V1 L1].
  destruct (shadow_of_val E _ (kn cs) b2 n2 sb2 sk2 sn2 HK H2 Fs2) as [V2 L2].
  pose proof SHADOW_ok as SO; unfold shadow_ok in SO.
  cbn [kentry_ok]. rewrite V1, V2, L1, L2.
  destruct (ealign_sound SEGS E _ (kn cs) b1 HK) as [_ D1]. destruct (ealign_sound SEGS E _ (kn cs) n1 HK) as [_ D2].
  destruct (ealign_sound SEGS E _ (kn cs) b2 HK) as [_ D3]. destruct (ealign_sound SEGS E _ (kn cs) n2 HK) as [_ D4].
  assert (P8 : forall e, 3 <= ealign (kn cs) e -> (2 ^ ealign (kn cs) e | bv_unsigned (edenot E e)) -> (8 | bv_unsigned (edenot E e))).
  { intros e He Hd. eapply Z.divide_trans; [|exact Hd]. change 8 with (2 ^ 3). apply pow2_divide_le. lia. }
  pose proof (P8 _ Lb1 D1) as [q1 Q1]. pose proof (P8 _ Ln1 D2) as [q2 Q2]. pose proof (P8 _ Lb2 D3) as [q3 Q3]. pose proof (P8 _ Ln2 D4) as [q4 Q4].
  unfold elenZ in AP0. rewrite <- U1, <- U2 in AP0.
  pose proof (u64_range (edenot E b1)) as Rb1. pose proof (u64_range (edenot E b2)) as Rb2.
  generalize dependent AP0. rewrite Q1, Q2, Q3, Q4. rewrite Q1 in Rb1, B1. rewrite Q2 in Rn1, M1. rewrite Q3 in Rb2, B2. rewrite Q4 in Rn2, M2.
  rewrite !Z.div_mul by lia. intros AP0.
  rewrite (Z.mod_small (q1 + shadow_off A)) by lia. rewrite (Z.mod_small (q3 + shadow_off A)) by lia.
  clear - AP0 Rb1 Rb2 Rn1 Rn2 SO. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma expr_vars_lt_mono : forall b b' e, AP.expr_vars_lt b e = true -> (b <= b')%nat -> AP.expr_vars_lt b' e = true.
Proof.
  intros b b' e H Hle. induction e; cbn [AP.expr_vars_lt] in *; try reflexivity;
    try (apply andb_prop in H as [H1 H2]; rewrite (IHe1 H1), (IHe2 H2); reflexivity); try (apply IHe; exact H).
  apply Nat.ltb_lt in H. apply Nat.ltb_lt. lia.
Qed.
#[using="Type"] Lemma sr_vars_lt_mono : forall b b' sr, AP.sr_vars_lt b sr = true -> (b <= b')%nat -> AP.sr_vars_lt b' sr = true.
Proof.
  intros b b' sr H Hle. induction sr; cbn [AP.sr_vars_lt] in *; [reflexivity|].
  apply andb_prop in H as [H1 H2]. rewrite (expr_vars_lt_mono _ _ _ H1 Hle), (IHsr H2). reflexivity.
Qed.
#[using="Type"] Lemma sr_vars_lt_upd : forall b sr n e, AP.sr_vars_lt b sr = true -> AP.expr_vars_lt b e = true -> AP.sr_vars_lt b (sr_upd sr n e) = true.
Proof.
  intros b sr n e. revert sr. induction n as [|n IH]; intros sr Hsr He.
  - destruct sr; cbn [sr_upd AP.sr_vars_lt]; cbn [AP.sr_vars_lt] in Hsr; rewrite He; [reflexivity|].
    apply andb_prop in Hsr as [_ H2]. rewrite H2. reflexivity.
  - destruct sr; cbn [sr_upd AP.sr_vars_lt]; cbn [AP.sr_vars_lt] in Hsr.
    + rewrite IH by (reflexivity || exact He). reflexivity.
    + apply andb_prop in Hsr as [H1 H2]. rewrite H1, (IH _ H2 He). reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint ext_list (E : env) (nx : nat) (vals : list word) : env :=
  match vals with
  | [] => E
  | v :: rest => ext_list (ext1 E nx v) (Datatypes.S nx) rest
  end.

#[using="Type"] Lemma ext_list_agree : forall E nx vals, env_agree nx E (ext_list E nx vals).
Proof.
  intros E nx vals. revert E nx. induction vals as [|v rest IH]; intros E nx; cbn [ext_list].
  - apply env_agree_refl.
  - eapply env_agree_trans; [apply ext1_agree|]. eapply env_agree_le; [apply IH | lia].
Qed.

#[using="Type"] Lemma ext_list_at : forall E nx vals i, (i < length vals)%nat -> ev (ext_list E nx vals) (nx + i) = nth i vals (Z_to_bv 64 0).
Proof.
  intros E nx vals. revert E nx. induction vals as [|v rest IH]; intros E nx i Hi; cbn [length] in Hi; [lia|].
  cbn [ext_list]. destruct i as [|i].
  - rewrite Nat.add_0_r. pose proof (ext_list_agree (ext1 E nx v) (Datatypes.S nx) rest) as [Hag _].
    rewrite <- Hag by lia. cbn [nth]. apply ext1_at.
  - replace (nx + Datatypes.S i)%nat with (Datatypes.S nx + i)%nat by lia. cbn [nth]. apply IH. lia.
Qed.

#[using="Type"] Lemma regs_ok_sr_fresh : forall E sr R rs nx,
  regs_ok E sr R -> AP.sr_vars_lt nx sr = true -> Forall (fun r => 0 < r < 32)%nat rs ->
  regs_ok (ext_list E nx (map (fun r => getr R (Z_to_bv 5 (Z.of_nat r))) rs)) (sr_fresh sr rs nx) R.
Proof.
  intros E sr R rs. revert E sr. induction rs as [|r rest IH]; intros E sr nx HR Hsr Hrs; cbn [sr_fresh map ext_list].
  - exact HR.
  - apply Forall_cons_iff in Hrs as [Hr Hrest].
    apply IH.
    + apply regs_ok_respell.
      * eapply regs_ok_agree'; [apply ext1_agree | exact Hsr | exact HR].
      * exact Hr.
      * cbn [edenot]. rewrite ext1_at.
        pose proof (regs_ok_agree' nx E (ext1 E nx (getr R (Z_to_bv 5 (Z.of_nat r)))) sr R (ext1_agree _ _ _) Hsr HR) as HR'.
        etransitivity; [exact (HR' (Z_to_bv 5 (Z.of_nat r)))|]. unfold sr_get.
        assert (Hnz : bv_eqb (Z_to_bv 5 (Z.of_nat r)) 0%bv = false).
        { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
          change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia.
          replace (bv_unsigned (0%bv : bv 5)) with 0%Z by reflexivity. lia. }
        rewrite Hnz, ridx_lit by lia. reflexivity.
    + apply sr_vars_lt_upd; [eapply sr_vars_lt_mono; [exact Hsr | lia] |]. cbn [AP.expr_vars_lt]. apply Nat.ltb_lt. lia.
    + exact Hrest.
Qed.

#[using="argH_agree SINV_agree"] Lemma havoc_sound : forall E cs R FULL model rs cs',
  cs_ok E cs R FULL model -> node_havoc nx0 cs rs = Some cs' ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok E' cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros E cs R FULL model rs cs' HC H. unfold node_havoc in H.
  destruct (fresh_ok nx0 cs && forallb (fun r => Nat.ltb 0 r && Nat.ltb r 32) rs)%bool eqn:Hc; [|discriminate].
  injection H as <-. apply andb_prop in Hc as [Hf Hrs].
  destruct (fresh_ok_parts cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (E' := ext_list E (nxt cs) (map (fun r => getr R (Z_to_bv 5 (Z.of_nat r))) rs)).
  assert (Hag : env_agree (nxt cs) E E') by apply ext_list_agree.
  exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
  pose proof (cs_ok_agree E E' cs R FULL model Hag Hf HC) as HC'.
  destruct HC'; constructor; cbn [with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset]; try assumption; [|reflexivity].
  apply regs_ok_sr_fresh; [exact (co_regs _ _ _ _ _ HC) | exact Fsr |].
  apply Forall_forall. intros r Hr. pose proof (proj1 (forallb_forall _ _) Hrs r Hr) as Hb.
  apply andb_prop in Hb as [H1 H2]. apply Nat.ltb_lt in H1. apply Nat.ltb_lt in H2. lia.
Qed.

(* [comment removed for export] *)
Fixpoint kn_bigexprs (K : nat) (k : list kentry) : list expr :=
  match k with
  | [] => []
  | KWord a w v :: r => if bigb K v then v :: kn_bigexprs K r else kn_bigexprs K r
  | _ :: r => kn_bigexprs K r
  end.

#[using="Type"] Lemma kentry_vars_lt_mono : forall b b' K, AP.kentry_vars_lt b K = true -> (b <= b')%nat -> AP.kentry_vars_lt b' K = true.
Proof.
  intros b b' K H Hle.
  assert (E1 : forall e, AP.expr_vars_lt b e = true -> AP.expr_vars_lt b' e = true) by (intros; eapply expr_vars_lt_mono; eassumption).
  assert (A1 : forall a, AP.saddr_vars_lt b a = true -> AP.saddr_vars_lt b' a = true) by (intros [? ?]; unfold AP.saddr_vars_lt; apply E1).
  destruct K; cbn [AP.kentry_vars_lt] in *;
    repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end;
    repeat match goal with
    | Y : AP.expr_vars_lt b ?e = true |- _ => rewrite (E1 e Y); clear Y
    | Y : AP.saddr_vars_lt b ?a = true |- _ => rewrite (A1 a Y); clear Y
    end; reflexivity.
Qed.
#[using="Type"] Lemma kn_vars_lt_mono' : forall b b' k, AP.kn_vars_lt b k = true -> (b <= b')%nat -> AP.kn_vars_lt b' k = true.
Proof.
  intros b b' k H Hle. induction k as [|K k IH]; [reflexivity|]. cbn [AP.kn_vars_lt] in *. apply andb_prop in H as [H1 H2].
  rewrite (kentry_vars_lt_mono b b' K H1 Hle), (IH H2). reflexivity.
Qed.

#[using="Type"] Lemma kn_bigsubst_len : forall K k nx, snd (kn_bigsubst K k nx) = length (kn_bigexprs K k).
Proof.
  intros K k. induction k as [|x r IH]; intros nx; [reflexivity|].
  cbn [kn_bigsubst kn_bigexprs]. destruct x as [a w v| | | | | | | | |]; try (specialize (IH nx); destruct (kn_bigsubst K r nx); cbn in *; exact IH).
  destruct (bigb K v).
  - specialize (IH (Datatypes.S nx)). destruct (kn_bigsubst K r (Datatypes.S nx)). cbn in *. rewrite IH. reflexivity.
  - specialize (IH nx). destruct (kn_bigsubst K r nx). cbn in *. exact IH.
Qed.

#[using="Type"] Lemma kn_bigsubst_sound : forall K k nx E2 M,
  know_ok SEGS E2 M k -> AP.kn_vars_lt nx k = true ->
  (forall i, (i < length (kn_bigexprs K k))%nat -> ev E2 (nx + i) = edenot E2 (nth i (kn_bigexprs K k) (ELit 0))) ->
  know_ok SEGS E2 M (fst (kn_bigsubst K k nx)).
Proof.
  intros K k. induction k as [|x r IH]; intros nx E2 M HK Hv Hvals; [constructor|].
  inversion HK as [|x' r' Hx Hr]; subst. cbn [AP.kn_vars_lt] in Hv. apply andb_prop in Hv as [Hvx Hvr].
  cbn [kn_bigsubst]. cbn [kn_bigexprs] in Hvals.
  assert (DFLT : (forall i, (i < length (kn_bigexprs K r))%nat -> ev E2 (nx + i) = edenot E2 (nth i (kn_bigexprs K r) (ELit 0))) ->
                 know_ok SEGS E2 M (fst (let '(r', c) := kn_bigsubst K r nx in (x :: r', c)))).
  { intros Hvals'. pose proof (IH nx E2 M Hr Hvr Hvals') as IH'. destruct (kn_bigsubst K r nx) as [r' c]. cbn [fst] in *. constructor; [exact Hx | apply IH']. }
  destruct x as [a w v| | | | | | | | |]; try (apply DFLT; exact Hvals).
  destruct (bigb K v) eqn:Hb; [|apply DFLT; exact Hvals]. clear DFLT.
  pose proof (IH (Datatypes.S nx) E2 M Hr ltac:(eapply kn_vars_lt_mono'; [exact Hvr | lia])) as IH'.
  destruct (kn_bigsubst K r (Datatypes.S nx)) as [r' c] eqn:Hs. cbn [fst]. constructor.
  - cbn [kentry_ok] in Hx |- *. destruct Hx as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
    rewrite H3. f_equal. f_equal. cbn [edenot]. symmetry. replace nx with (nx + 0)%nat by lia. rewrite (Hvals 0%nat ltac:(cbn; lia)). reflexivity.
  - apply IH'. intros i Hi. replace (Datatypes.S nx + i)%nat with (nx + Datatypes.S i)%nat by lia. rewrite (Hvals (Datatypes.S i) ltac:(cbn; lia)). reflexivity.
Qed.

#[using="Type"] Lemma node_havoc_nxt : forall cs rs cs1, node_havoc nx0 cs rs = Some cs1 -> nxt cs1 = (nxt cs + length rs)%nat /\ pc cs1 = pc cs.
Proof.
  intros cs rs cs1 H. unfold node_havoc in H.
  destruct (fresh_ok nx0 cs && forallb (fun r : nat => Nat.ltb 0 r && Nat.ltb r 32) rs)%bool; [|discriminate].
  injection H as <-. split; reflexivity.
Qed.

#[using="argH_agree SINV_agree"] Lemma havocbig_sound : forall E cs R FULL model K cs',
  cs_ok E cs R FULL model -> node_havocbig nx0 cs K = Some cs' ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok E' cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros E cs R FULL model K cs' HC H. unfold node_havocbig in H.
  destruct (node_havoc nx0 cs _) as [cs1|] eqn:Hh; [|discriminate].
  destruct (fresh_ok nx0 cs1) eqn:Hf1; [|discriminate].
  destruct (kn_bigsubst K (kn cs1) (nxt cs1)) as [k' c] eqn:Hs. injection H as <-.
  destruct (havoc_sound E cs R FULL model _ cs1 HC Hh) as (E1 & [Hag0 Hag1] & HC1 & Hpc1).
  destruct (fresh_ok_parts cs1 Hf1) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (vals := map (edenot E1) (kn_bigexprs K (kn cs1))).
  set (E2 := ext_list E1 (nxt cs1) vals).
  assert (Hag2 : env_agree (nxt cs1) E1 E2) by apply ext_list_agree.
  assert (Hnx : (nxt cs <= nxt cs1)%nat).
  { destruct (node_havoc_nxt cs _ cs1 Hh) as [-> _]. lia. }
  exists E2. split; [|split; [|rewrite <- Hpc1; reflexivity]].
  { split; (eapply env_agree_trans; [|eapply env_agree_le; [exact Hag2 | lia]]); assumption. }
  pose proof (cs_ok_agree E1 E2 cs1 R FULL model Hag2 Hf1 HC1) as HC2.
  replace (with_ss cs1 (mk_ss (pc cs1) (s_regs (a_ss cs1)) k' (nxt cs1 + c))) with (set_kn (bump cs1 c) k') by reflexivity.
  apply cs_ok_set_kn.
  - destruct HC2; constructor; cbn [bump with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset];
      try assumption; reflexivity.
  - replace k' with (fst (kn_bigsubst K (kn cs1) (nxt cs1))) by (rewrite Hs; reflexivity).
    unfold Mr. change (hid E2 (bump cs1 c) model) with (hid E2 cs1 model).
    apply kn_bigsubst_sound; [exact (co_know _ _ _ _ _ HC2) | rewrite kn_vars_lt_eq; rewrite <- kn_vars_lt_eq; exact Fkn |].
    intros i Hi. unfold E2. rewrite ext_list_at by (unfold vals; rewrite length_map; exact Hi).
    unfold vals. change (Z_to_bv 64 0) with (edenot E1 (ELit 0)). rewrite map_nth.
    eapply (edenot_agree' (nxt cs1)); [apply ext_list_agree|].
    (* [comment removed for export] *)
    clear - Fkn Hi. revert i Hi. generalize (kn cs1) Fkn. intros k Hk.
    induction k as [|x r IH]; intros i Hi; [cbn in Hi; lia|].
    cbn [AP.kn_vars_lt] in Hk. apply andb_prop in Hk as [Hx Hr]. cbn [kn_bigexprs] in Hi |- *.
    destruct x as [a w v| | | | | | | | |]; try (apply IH; assumption).
    destruct (bigb K v); [|apply IH; assumption].
    destruct i as [|i]; cbn [nth]; [cbn [AP.kentry_vars_lt] in Hx; apply andb_prop in Hx as [_ Hx]; exact Hx | apply IH; [exact Hr | cbn [length] in Hi; lia]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition upd (E : env) (J : nat) (w : word) : env := Env (fun n => if Nat.eqb n J then w else ev E n) (eb E).

#[using="Type"] Lemma esubst_denot : forall E J e x, edenot E (esubst J e x) = edenot (upd E J (edenot E e)) x.
Proof.
  intros E J e x. induction x as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n];
    cbn [esubst edenot]; try reflexivity.
  - cbn [upd ev]. destruct (Nat.eqb n J); reflexivity.
  - rewrite mkAlu_denot, IHa, IHb. reflexivity.
  - rewrite mkAluw_denot, IHa, IHb. reflexivity.
  - rewrite mkMd_denot, IHa, IHb. reflexivity.
  - rewrite mkMdw_denot, IHa, IHb. reflexivity.
  - rewrite IHa. reflexivity.
Qed.

#[using="Type"] Lemma upd_agree : forall E J w, env_agree J E (upd E J w).
Proof. intros E J w. split; [|reflexivity]. intros n Hn. cbn [upd ev]. destruct (Nat.eqb_spec n J); [lia|reflexivity]. Qed.
#[using="Type"] Lemma upd_at : forall E J w, ev (upd E J w) J = w.
Proof. intros. cbn [upd ev]. rewrite Nat.eqb_refl. reflexivity. Qed.
#[using="Type"] Lemma upd_same : forall E J, upd E J (ev E J) = E.
Proof. intros [f g] J. unfold upd. cbn [ev eb]. f_equal. apply functional_extensionality. intros n. destruct (Nat.eqb_spec n J); [subst; reflexivity|reflexivity]. Qed.
#[using="Type"] Lemma upd_upd : forall E J w w', upd (upd E J w) J w' = upd E J w'.
Proof. intros [f g] J w w'. unfold upd. cbn [ev eb]. f_equal. apply functional_extensionality. intros n. destruct (Nat.eqb n J); reflexivity. Qed.

#[using="Type"] Lemma estart_asubst : forall E J e a, estart E (asubst J e a) = estart (upd E J (edenot E e)) a.
Proof. intros E J e [b o]. unfold asubst, estart. cbn [a_base a_off]. rewrite esubst_denot. reflexivity. Qed.
#[using="Type"] Lemma adenot_asubst : forall E J e a, adenot E (asubst J e a) = adenot (upd E J (edenot E e)) a.
Proof. intros E J e [b o]. unfold asubst, adenot. cbn [a_base a_off]. rewrite esubst_denot. reflexivity. Qed.

#[using="Type"] Lemma kentry_ok_ksubst : forall E J e M K,
  kentry_ok SEGS E M (ksubst J e K) <-> kentry_ok SEGS (upd E J (edenot E e)) M K.
Proof.
  intros E J e M K. set (E' := upd E J (edenot E e)).
  destruct K as [a w v|a n|a n k|lo hi|x m|x lo hi|a n|a1 n1 a2 n2|a n c|a n]; cbn [ksubst kentry_ok];
    unfold flat, elenZ; rewrite ?estart_asubst, ?adenot_asubst, ?esubst_denot; fold E'; tauto.
Qed.

#[using="Type"] Lemma know_ok_ksubst : forall E J e M k,
  know_ok SEGS E M (map (ksubst J e) k) <-> know_ok SEGS (upd E J (edenot E e)) M k.
Proof.
  intros E J e M k. unfold know_ok. induction k as [|K k IH]; [split; intros; constructor|].
  cbn [map]. split; intros H; inversion H; subst; constructor; try (apply IH; assumption);
    apply (kentry_ok_ksubst E J e M K); assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma inst_allowA : forall E J e inv, allowA E (inst inv J e) = allowA (upd E J (edenot E e)) inv.
Proof.
  intros E J e inv. unfold allowA, inst. cbn [a_vis a_ghost]. rewrite <- map_app, flat_map_concat_map, flat_map_concat_map, map_map.
  f_equal. apply map_ext. intros [b n]. unfold allow1, psubst, sh_lo, sh_hi, uE. cbn [fst snd]. rewrite !esubst_denot. reflexivity.
Qed.

#[using="Type"] Lemma existsb_map' : forall {X Y} (f : Y -> bool) (g : X -> Y) l, existsb f (map g l) = existsb (fun x => f (g x)) l.
Proof. intros X Y f g l. induction l as [|x l IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

#[using="Type"] Lemma inst_in_allow : forall E J e inv, in_allow E (inst inv J e) = in_allow (upd E J (edenot E e)) inv.
Proof.
  intros E J e inv. apply functional_extensionality. intros z. unfold in_allow, in_vis, in_sh, inst. cbn [a_vis].
  rewrite !existsb_map'. f_equal; f_equal; apply functional_extensionality; intros [b n];
    unfold psubst, sh_lo, sh_hi, uE; cbn [fst snd]; rewrite !esubst_denot; reflexivity.
Qed.

#[using="Type"] Lemma inst_in_ghost : forall E J e inv, in_ghost E (inst inv J e) = in_ghost (upd E J (edenot E e)) inv.
Proof.
  intros E J e inv. apply functional_extensionality. intros z. unfold in_ghost, inst. cbn [a_ghost].
  induction (a_ghost inv) as [|[b n] l IH]; [reflexivity|]. cbn [map existsb fst snd psubst].
  unfold uE in *. cbn [fst snd]. rewrite !esubst_denot, IH. reflexivity.
Qed.

#[using="argH_agree"] Lemma inst_hid : forall E J e inv model, (nx0 <= J)%nat ->
  hid E (inst inv J e) model = hid (upd E J (edenot E e)) inv model.
Proof.
  intros E J e inv model HJ. apply functional_extensionality. intros a. unfold hid, vis.
  rewrite inst_in_allow. rewrite (argH_agree E (upd E J (edenot E e)) a); [|eapply env_agree_le; [apply upd_agree | exact HJ]].
  unfold inst. cbn [a_maps]. reflexivity.
Qed.

#[using="Type"] Lemma inst_maps : forall E J e inv, map (amap_den E) (a_maps (inst inv J e)) = map (amap_den (upd E J (edenot E e))) (a_maps inv).
Proof.
  intros. unfold inst. cbn [a_maps]. rewrite map_map. apply map_ext. intros m. unfold amap_den, msubst. cbn [am_base am_len].
  rewrite !esubst_denot. reflexivity.
Qed.

#[using="Type"] Lemma maps_match_msubst : forall E J e ms l,
  maps_match E (map (msubst J e) ms) l <-> maps_match (upd E J (edenot E e)) ms l.
Proof.
  intros E J e ms. induction ms as [|m ms IH]; intros l; cbn [maps_match map]; [tauto|].
  unfold is_fog, msubst, uE, amap_den. cbn [am_kind am_base am_len]. rewrite !esubst_denot.
  destruct (is_tok_kind (am_kind m)).
  - split; (intros [HM|(iv & l' & -> & Hsz & HM)]; [left; apply IH; exact HM | right; exists iv, l'; split; [reflexivity|]; split; [exact Hsz | apply IH; exact HM]]).
  - split; (intros (l' & -> & HM); exists l'; split; [reflexivity | apply IH; exact HM]).
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma holes_msubst : forall E J e y l ms,
  Forall (hole_ok E y l) (map (msubst J e) ms) <-> Forall (hole_ok (upd E J (edenot E e)) y l) ms.
Proof.
  intros E J e y l ms. induction ms as [|m ms IH]; cbn [map].
  - split; intros; constructor.
  - rewrite !Forall_cons_iff, IH.
    assert (X : hole_ok E y l (msubst J e m) <-> hole_ok (upd E J (edenot E e)) y l m).
    { unfold hole_ok, is_hole, msubst, uE. cbn [am_kind am_base am_len]. rewrite !esubst_denot. tauto. }
    rewrite X. tauto.
Qed.
#[using="Type"] Lemma inst_maps_match : forall E J e inv l,
  maps_match E (a_maps (inst inv J e)) l <-> maps_match (upd E J (edenot E e)) (a_maps inv) l.
Proof. intros. unfold inst. cbn [a_maps]. apply maps_match_msubst. Qed.

#[using="Type"] Lemma regs_ok_inst : forall E J e sr R,
  regs_ok E (map (esubst J e) sr) R <-> regs_ok (upd E J (edenot E e)) sr R.
Proof.
  intros E J e sr R. unfold regs_ok, sr_get.
  assert (G : forall r, edenot E (if bv_eqb r 0 then ELit 0 else nth (ridx r) (map (esubst J e) sr) (ELit 0))
                     = edenot (upd E J (edenot E e)) (if bv_eqb r 0 then ELit 0 else nth (ridx r) sr (ELit 0))).
  { intros r. destruct (bv_eqb r 0); [reflexivity|].
    replace (ELit 0) with (esubst J e (ELit 0)) at 1 by reflexivity. rewrite map_nth. apply esubst_denot. }
  split; intros H r; [rewrite <- G | rewrite G]; apply H.
Qed.

#[using="Type"] Lemma fds_ok_inst : forall E J e f model, fds_ok E (fsubst J e f) model <-> fds_ok (upd E J (edenot E e)) f model.
Proof.
  intros E J e f model. destruct f as [|k l o|]; cbn [fsubst fds_ok]; try tauto.
  unfold uE. rewrite !esubst_denot. cbn [eb upd]. tauto.
Qed.

#[using="argH_agree SINV_agree"] Lemma cs_ok_inst : forall E J e inv R FULL model, (nx0 <= J)%nat -> s_log (a_ss inv) = [] ->
  cs_ok E (inst inv J e) R FULL model <-> cs_ok (upd E J (edenot E e)) inv R FULL model.
Proof.
  intros E J e inv R FULL model HJ Hlog.
  pose proof (inst_hid E J e inv model HJ) as HH. pose proof (inst_allowA E J e inv) as HA. pose proof (inst_maps E J e inv) as HM.
  pose proof (inst_in_ghost E J e inv) as HG.
  assert (AG : env_agree nx0 E (upd E J (edenot E e))) by (eapply env_agree_le; [apply upd_agree | exact HJ]).
  split; intros HC; destruct HC; constructor;
    cbn [inst a_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset mk_ss] in *;
    rewrite <- ?HA, <- ?HM; try assumption.
  - apply regs_ok_inst. assumption.
  - unfold Mr. rewrite <- HH. apply know_ok_ksubst. exact co_know0.
  - apply fds_ok_inst. assumption.
  - apply (proj1 (maps_match_msubst E J e _ _)). assumption.
  - apply (proj1 (holes_msubst E J e _ _ _)). assumption.
  - (* [comment removed for export] *) apply Forall_forall. intros m Hin Hk.
    pose proof (proj1 (Forall_forall _ _) co_none0 (msubst J e m) ltac:(apply in_map; exact Hin) Hk) as X.
    unfold amap_den, msubst in X |- *. cbn [am_base am_len am_kind] in X. rewrite !esubst_denot in X. exact X.
  - apply Forall_forall. intros m Hin Hk a Ha.
    pose proof (proj1 (Forall_forall _ _) co_kinds0 (msubst J e m) ltac:(apply in_map; exact Hin) Hk a) as X.
    unfold msubst in X. cbn [am_base am_len] in X. rewrite !esubst_denot in X. exact (X Ha).
  - rewrite <- esubst_denot. assumption.
  - intros a. unfold Mr in *. rewrite <- HH. first [rewrite HG | rewrite <- HG]. exact (co_zero0 a).
  - eapply SINV_agree; [exact AG | assumption].
  - apply regs_ok_inst. assumption.
  - reflexivity.
  - unfold Mr in *. rewrite HH. apply know_ok_ksubst. assumption.
  - apply fds_ok_inst. assumption.
  - apply (proj2 (maps_match_msubst E J e _ _)). assumption.
  - apply (proj2 (holes_msubst E J e _ _ _)). assumption.
  - apply Forall_forall. intros m' Hin Hk. apply in_map_iff in Hin as [m [<- Hin]].
    pose proof (proj1 (Forall_forall _ _) co_none0 m Hin Hk) as X.
    unfold amap_den, msubst. cbn [am_base am_len am_kind]. rewrite !esubst_denot. exact X.
  - apply Forall_forall. intros m' Hin Hk a Ha. apply in_map_iff in Hin as [m [<- Hin]].
    unfold msubst in Ha, Hk. cbn [am_base am_len am_kind] in Ha, Hk. rewrite !esubst_denot in Ha.
    exact (proj1 (Forall_forall _ _) co_kinds0 m Hin Hk a Ha).
  - rewrite esubst_denot. assumption.
  - rewrite HA. assumption.
  - rewrite HA. assumption.
  - intros a. unfold Mr in *. rewrite HH. first [rewrite <- HG | rewrite HG]. exact (co_zero0 a).
  - eapply SINV_agree; [|eassumption]. destruct AG as [AG1 AG2]. split; [intros n Hn; symmetry; apply AG1; exact Hn | symmetry; exact AG2].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma kentry_eqb_h_sound : forall E M k X K,
  know_ok SEGS E M k -> kentry_ok SEGS E M X -> kentry_eqb_h X K = true -> kflat_h k K = true -> kentry_ok SEGS E M K.
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
ltac2:(KReplay.run1 (kr_t_AsanPlanSound ()) ["FPX_3"; "Sound"] "p'0h03Hflh13Heqh21Hh31ai001ah41ni011nh52b'h62o'h72n'i022n'h81ih92HXh:1zh;1mi031mh<1Xh=2Hsh>1bi041bh?1ei051eh@2hii062hihA2loi072lohB1ohC1ci081chD2c'i092c'hE1ki0:1khF3kk'hG1vi0;1vhH2v'i0<2v'hI1wi0=1whJ2w'i0>2w'hK2H1hL2EShM2H2hN2X0hO4__x1hP4__x2hQ2a1i0?2a1hR2a2i0@2a2hS1dhT2n1i0A2n1hU2n2i0B2n2hV2HfhW2e0hX4__x3hY3hi0hZ3lo0h[7__arithh\4__ffh]6__sat4h^6__sat5h_8__varmaph`5__witha2a'i0C2a'hb2H3hc2Hahd4__p1he4__x4hf4__x5hg4__x6hh2b1hi2b2hj2nehk2ADhl1Ehm2E1hn2E2ho2F1hp2F2hq2F3hr2H0hs2HKht2Hehu3Hf'hv1Khw1Mhx3SADhy6__sat6hz6__sat7h{6__sat8h|6__sat9h}2a0i0D2a0h~2a3i0E2e1i0F2kki0G2m0i0H2n0i0I2n3i0J1xi0K6a_basei0L5a_offi0M2k'i0N1si0O1yp%0p%1p%2p&0p;1p;4p;2p;3p;7p;6p;8p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0g0038R5p4p710R6p9P0p1003Vp4p710R7p9P0p1004Np4p710R8p8P0p1004ep4p710p8P0p1005FR9p4p710p8P0P9p4p7210p8P0p1005cp4p710R0p8p100_Jp4p70R9g00;\R:p4p710R;p8P9P1p8P9P2p8P9g0079R<p4p710R=p8P9P4p8P9P3p4p710R3p8P9P7p8p1006?p4p710P6p8p100`:p4p70R9P;p8P9P1p8P9P2p8P9p100`hR;p4p7210R>p8P9P=p8P9P4p8P9P3p8P9P6p8P9P7p8p100aDp4p70P=p8p100bCp4p7210R9P1p8P9P2p8P9P=p8P9P4p8P9P3p8P9P7p8p1062Tp6051000R9P6p8P9p103VIp4p710R?p8P9p1063Vp4p710p8p106kQp6051000R9P8p8P9P6p8P9P?p8P9P0p8p107<2p6051000R9P8p8P9P?p8P9P0p8p100bop4p70R9P1p8P9P2p8P9P4p8P9P3p8P9P7p8p1006\p4p7210R7P=p8P7P6p8p1007Up4p7210P6p8p10082p4p73110P6p8p10<9lR7p60521000R=P>p8P=P0p8P7p6051001R7P;p4p710p8P7P?p8P7P0p8p100cep4p710P6p8g008Nj1oTg00dlk10XTg00eJj1mTg01Snk10LTg00F?k10ETg02U9k40xTg03ETj41Tg0<Qek20jTg05c?k20<Tg0<Rjj2=Tg05^Pj2>Tg01Plj2?Tg05bBj2WTg01bck30TTg00mbR6k20RTg09L:k30oTP:j35TP5k70Ck60UTg03iTj24Tg03k1j3;Tg06\6j4lTg05]Kk20ATg0;?lj2jTg05_Tk30aTg05XUk60?Tg03fQj2@Tg00O0k20:Tg05`Zj3~Tg01=4j27Tg04JVj1XTg05B?k30FTg00iHj2<Tg057nk40[TP<j6Vj7wTg0093k10ZTg018]k20~Tg07Onk20VTg01L1j2FTg00<lj2ETg08c<k10WTg07CLk80pTg00>lR<j26Tg017fk10DTg00>Pj2\Tg00=Lj2HTg01>6k20nTg01>^k30mTg00E?k10lTg00F_j2zTg00]4k10kTg00G[k10iTg00H9k10hTg00Hdk20QTg00K9j2sTg00Mkk30BTg00IGj4yTg01LWk30gTg00K\k60fTg00J2k10PTg00NNk20eTg00OJk20dTg00P6k30cTg00PUk40bTg07Pok30OTg0:iJk30NTg00A:j1cTg00AYk204Tg00DSk20>Tg00E_k30=Tg00JTk10MTg01fik203Tg00BBk10_Tg00B`k20^Tg00CAk30;Tg05>_k107Tg05?ak100Tg03koj2GTg04oJk30]Tg06LFj2xTg06NPk20JTg03hPj3RTg03a`j2ITg01QJj3qTg05a_k20\Tg035Gj1KTg03jWj2pTg03e`k40ITg00jOj4hTg03nXj2aTg03o\j3YTg042<k209Tg043@k202Tg044Dk305Tg045Hj2`Tg04@ek406Tg04Aij3UTg04Bmj2_Tg03gQj29Tg030Cj2}Tg036>j2DTg041@k10}Tg00:Bj2^Tg04E^j4{Tg05b_k20{Tg00<6j1|Tg0<Snk20zTg05C@k30wTg00G=k40vTg00RFk70uTg00L@k70rTg00Rjk80sTg00Cjk30tTg04D1k20YTg0148k20qTg040`k20yTg041`k40STg00ZZR5f0R:g00[:S0035p=2f1R000z:Q00555p=0f2R71I0:'?p=u1>0:,?7p=ng00UMR?f3R;/@71@0:35p=TA5?0:p=:g01IER=?50:p=r1@0:95?7p>0K170:,<7p=81<0:95?7p=fg05ChR>@0w0:p=v1H70/E:p=A1H70/^:p=Qg00VPR9/\:p=g1^90/6:p=P1^9:p=C1770,<;/H:p=[P?P7P0P:H0vp=tP0g00SNS01g00SmR3P3g00TMR4P:g00TmK0up=eP7Q01P3P3P4P0P:K0rp>0@P;Q01P3P3P4P7P0P:L0sp=kP?f4R2P;P7P0P:J0Up=JB0t?0:p=i1E0:,H7p>0`P?P0g00Z3P:Cyp>011H0:,F7p=N1?0:Q00555p=Lf7R1f6R8f5R@P2P;H0I20Y0:,}735p=d160:,67p=M170:-0Y7p>0H1}0:95;7p=]140:,@7p>081@70=5?:p>0GP5g014WRAP0g015SQ00P:EVp=OP2P;P7P0C100q:p=31\0:,67p=B1@70/H:,F;p=b20y70#K=5?:p=SP;P7P0P:H0S,}2958@p=ZP;P7P0P:H0S,}2p>0|g00n`g00UkRB#oRC#oS02#oRD#o#o#oRE$0XRF#mRG&0XDRD#mRH$0LRI[g03GPRJ$0Ep,4SEGSRKP2P;P7H0xPKP@P2P7C120j;7#210@;20<@2RLPJP5P@PJP5P11=@7RM?u201>;:S03'?S04PAPAPAPAPAPAPAPAPAn0110O000:3010C10>10<2010D1013010D10110:2010710620105103301051071062010D1014010?10A10@10B3010D1011082010D101PJP5P8PA1=;0?n7:RNPAPAPAPAPAPAPAPAn0110O000:3010D10=10;2010C1023010D10H10:2010710620105103301051071062010D10H4010?10A10@10B3010D10H1082010D10HPJP5P1PAPAAnM20RM?u;:S05PAPAPAPAPAPAPAn0110O000:3010D10=10;2010D10H3010C10210M2010710620105103301051071062010D10H4010?10A10@10B3010D10H1082010D10HPAPAPAPJP5P8PAPAPAPAPAPAPNPAPAPAn0110O000:3010D10=10;2010D10H3010D10H10:2010710620105103301051071062010C1024010?10A10@10B3010D10H1082010D10HPAPJP5P1PAPAPAPAPAPAPAPA1W;:,?MS06PAn0110O000:3010D10=10;2010D10H3010D10H10:2010710620105103301051071062010D10H4010?10A10@10B3010C1021092010D10HPJP5P8PAPAPAPAPAPAPAPAPAPNn0110O000:3010D10=10;2010D10H3010D10H10:2010710620105103301051071062010D10H4010?10A10@10B3010D10H1082010C102n0110J000:3010010=10;201001013010010110:201071062010510330105107106201001014010?10A10@10B3010010110820100101RM<0T0%2L%2M+0RP620<8@#2PJP5P8PJP5f8RMQ04PAPAPAPAPAPAPAPAPAn0110O000:3010C10>10<2010D1013010D10110:2010710620105103301051071062010D1014010?10A10@10B3010D1011082010D101PJP5P1PAPNPAPAPAPAPAPAPAPAn0110O000:3010D10=10;2010C1023010D10H10:2010710620105103301051071062010D10H4010?10A10@10B3010D10H1082010D10HPJP5PMPAPAQ05PAPAPAPAPAPAPAn0110O000:3010D10=10;2010D10H3010C10210M2010710620105103301051071062010D10H4010?10A10@10B3010D10H1082010D10HPAPAPAPJP5P1PAPAPAPAPAPAPNPAPAPAn0110O000:3010D10=10;2010D10H3010D10H10:2010710620105103301051071062010C1024010?10A10@10B3010D10H1082010D10HPAPJP5PMPAPAPAPAPAPAPAPAQ06PAn0110O000:3010D10=10;2010D10H3010D10H10:2010710620105103301051071062010D10H4010?10A10@10B3010C1021092010D10HPJP5P1PAPAPAPAPAPAPAPAPAPNn0110O000:3010D10=10;2010D10H3010D10H10:2010710620105103301051071062010D10H4010?10A10@10B3010D10H1082010C102n0110J000:3010010=10;201001013010010110:201071062010510330105107106201001014010?10A10@10B3010010110820100101#2PKf:RLf9ROP8C1P:20<18#2B0oM1:A5JM1PJPMPKf=RPf<RQP:C1PKf>RRPPPLC1]9X<JPKPQf;RSPMC1P:W9POP:P8K0Cb1W1P:O1PJP5P1PJP5POQ04PAPAPAPAPAPAPAPAPAn0110O000:3010C10>10<2010D1013010D10110:2010710620105103301051071062010D1014010?10A10@10B3010D1011082010D101PJP5PMPAPNPAPAPAPAPAPAPAPAn0110O000:3010D10=10;2010C1023010D10H10:2010710620105103301051071062010D10H4010?10A10@10B3010D10H1082010D10HPJP5POPAPAQ05PAPAPAPAPAPAPAn0110O000:3010D10=10;2010D10H3010C10210M2010710620105103301051071062010D10H4010?10A10@10B3010D10H1082010D10HPAPAPAPJP5PMPAPAPAPAPAPAPNPAPAPAn0110O000:3010D10=10;2010D10H3010D10H10:2010710620105103301051071062010C1024010?10A10@10B3010D10H1082010D10HPAPJP5POPAPAPAPAPAPAPAPAQ06PAn0110O000:3010D10=10;2010D10H3010D10H10:2010710620105103301051071062010D10H4010?10A10@10B3010C1021092010D10HPJP5PMPAPAPAPAPAPAPAPAPAPNn0110O000:3010D10=10;2010D10H3010D10H10:2010710620105103301051071062010D10H4010?10A10@10B3010D10H1082010C102n0110J000:3010010=10;201001013010010110:201071062010510330105107106201001014010?10A10@10B3010010110820100101#214@2RT14;7RU'=#2S07fBRV148@RW;;7S08fARXP@P2P7Cl#2S0914M1S0:00AWRY1jM1RZ1j8@'>R[<0T7%2Y%2[+0RP614OMR61418R[+0A#21jOMRY1j18'>#2fFR\Q0:P\14LOS0;CTP:Q0;Q0:+0A#214SLS0<@0a6:g04HoR]Q0<;56P]P?P]P?P:P:n0110N00012010K10LX?]14QSR^Q0;P:J0?1:SOP]P=P]P=P:P0n0110N00012010K10LX?]14PQS0=Q0<P0J0?1rPS1rRQP=PPfLR_f?R`,4:;;Qf@Ra/:RfNRb14a`S0>'@Rc147X80Kb[]VX>=fKRd14PR;;S1:`PP?PR14a:=;bRfORe14XaS0?'@Rf14X080Ke]VXB?fMRg14`RRh;;P20:?cWVPaP:P0K0CW2WVP`P:PMK0CW2P:O1b2P:O1b2b=W=P:O11jLORc/>Z#21jSLRZ?~Y:1rZYP=P?fIRZ=8F:Z0J=1jQSRYPcP:J0?fHRi=8FY17ic7fFPG%XQRc:0F>P,7Z1<F:RYfJRj%XSRk:0F>Q'7Rl7fFX>GP:17ZP17Zc'vRmPZP>PPPcH0[EV1<Fm%XL:0F>S,7Z7fFPGPl17d`Rl%XR,7dRm'v,<FRn/:YX>GP:17jQ17jk'vRYPjP>PQPkH0[EV17jR%XPRk,7j'v,<F?fFYP?Pn17_RRn17_kRk'v,<FRY,::X:?P:1<Fl1<Fm&0ZCR>&0ZERE+0~Ro3ARp20VlmEV17dP17dc'v9fpFP?PYA8FgXRY%Xa98Fg;Ao/::X:?P:1<Fn1<Fk;AoRp20VnkEVA8F_a%X`98F_;Ao/:pP?1FFa,<FA8FbVRp?A:oA8FbaRk1FF`,<FRn;Ao':X:?P:g04Q:Rc,EaRm&0WaEVAAYmoA8Fg`1FFR,<F;Ao':P?PnfCRn98Fe1EVc;AoA8FeX?A:o':X:?P:1E`cRm&0W`EV1EXc=ApoAAkmo':PePbPgPXPaPRPjPSL0pA8FeRRm=Qfo%gm'6,PfP<fPRf14VXS0@'@Rm#CA8Ff`Rk=Qmo%gk'6fQRk14nVPkfERmfDRp'4S0ACTP:fRRc14pnRY'@#CfSRlQ0A'@A8FlVRq;Qo%gq'6P<fTRq14\mS0B'@A8FqnRr;Qo%grfURrfGRs/4\S0CPr14ZiS0DCTP:fVRt14isS0E'@A8Ftm;QofWRu=8F\#gfXRv/7sRw$0D1<FwRw1\wo'PfYRw/7gRx$0D1<FxRx1\xo'PfZS0F/7_Rx$0D1<FxRx1\xo'Pf[S0G=8FeRx/HbRy/EoPFf\RzPfPeC[,::X:?20n>ES0H%g>%CE%go[[S0I%C>R{g0157S0JB0m>E0UWcS0KQ0J%CoRE[^c{S0Lp-0S0Mg00VnR{$0lS0N&0E{S0O1z?7&0k?R|7t0&0i?S0P&0h?R}P?20Q?9S0Qg00YLS0R1s?B1s?C60B?R~Cy,e}S0SP?P~g00XeS0T20Q?>>0g?FS0UCy,e}R>P}Q01P3P3P4P2J0f60@}60@}&0P3R3Q0S>0@}>S01Ck20e}4S0VP:P7Q00-0:520d:7#2dB0c?90H0bS0Wb\b_b`XO?XP?WdQ0M1H:0S0XQ0X/\o/67'P1H07R41\4o'P[^O?^P?]dP:%CbS0Yf^S0Z=8FcS0[/Hk?Qbo'6PkQ0[PdO4b[b]b^:0Oyo1Ebo=AxoR>B0NbxoDJ1:>yA8FzbR>/HgS0\/EoPFf]S0]PePbC[,::X:?Q0\Q0HQ0IQ0KQ0Lg00WZRy#cS0^#cRx#cS0_-04?S0`204?xS0a204?yS0b'i'ig00X9S0c+0>Q0N60={Q0O1z?;9t|7?t0|Q0PP}P?Q0QQ0T&0MBS0T#o,s?RyCy,e}P3P}P?B0B?~yQ0RQ0UCy,e}P3P}Q0SP3Q01CkCkCkQ0VQ0Wb\b_b`XO?XP?XX?%g7AQ4;o1H7;#C1H;2R41\4o'P[[[^O?^P?^X?P:f_Rx=8FbPfA8FxkP1PMPQO6b[b]b^80Oo1Ego=A>oS01B0Ng>oDJQ01Q0\':203boQ0Y1Efo#C\E[Q0[@0`koR>003o%C>f`S0[=8Fq1Elo;Ao#C\E[Q0HQ0IQ0KQ0LPFfaS0LPl1EcoC[R>003o%C>fcR>=8Fr1Eqo;Ao#C\E[203ro%Cr1EuoS0K#C\E[&0_B-0^?RBQ0`60;?Q0aQ0^-04?RE:0;?BQ0b'i'i'iQ0c+0>Q0`Q0a:0;?BQ0b,iE'i'iQ0c+0>Q0N60={60={Q0O1z?21z?87t71z?@?t;|7t0Q0PP}201y~,e}P3P}&0MC,s?RCQ0T,s?Q02,s?60B?R|+01,e}P3P}201Cy,e}P3201~|,e}CkCkCkQ0VQ0Wb\b_b`XO?XP?XX?Xe?Xf?Xg?Q0X,:@1:@41:811H@8,:4[[[^O?^P?^X?^e?^f?^g?P:fdR4=8FtR}1Ero;AoA8F4vR|Q0K;AoPuP|PrP}P1PMPmO9b[b]b^bybzb{b|bnbmbKbrPFPw14djR}$07&00}C[PFPw14g_R|$07&00|C[':ePwP}PwP|CTeb2WqWpP0P:O2n2001000000121000000W2WoP0P:O2n2001000000121000000b2b=b=b=b=b=b=b=b=W=P:O1n200100000021000011000b=PpPWPpQ0:CTR|eWuWVW=Xj=X4?X6?X5=XB?X>=Q07Q08Q09P|[[[^j=^4?^6?^5=^B?^>=P]P`P:P`P0CT1Ga01Ga755G[^a]P:P]PnP:PnPUCT1Gp0142;R|,Gp55G[P:P\140:P\PWCTg050GR~%m:R3%m0RCP<%m7?50:1<;7?f;0Ry[1<70?f7:%m;?570[R{%m2?5;7\yB0]70:P:n2001000000120000000WiWhW4P{^iC^h3^4~P:PFPFPiP;P7C[R~,FFR3PFPiPMP1C[RC,FFR{1xF~PFPZPOPMC[Ry,FF9f:FX:?1xFCREPFPZP2P;C[,xF/::X:?PC1xF:1xFy':X:?20:?EP~P0DJ1<F{20JFCDJ1<F320JF~DJO4b21470R~$0798Fs&00~5NF&07[98Fs&00[5NF55Ge1Gs~1Gs[55GeWtX6?X5=P0P:O2n0110N00012110K10LXa]XB?X>=P0P:O2n0110N00012110K10LX3]PRP:PRP0CT1G`01G`755G[^a]^3]PJPKPRPPP:C1PJP5P0PJP5PRQ04PAPAPAPAPAPAPAPAPAn0110O000:3010C10>10<2010D1013010D10110:2010710620105103301051071062010D1014010?10A10@10B3010D1011082010D101PJP5PPPAPNPAPAPAPAPAPAPAPAn0110O000:3010D10=10;2010C1023010D10H10:2010710620105103301051071062010D10H4010?10A10@10B3010D10H1082010D10HPJP5PRPAPAQ05PAPAPAPAPAPAPAn0110O000:3010D10=10;2010D10H3010C10210M2010710620105103301051071062010D10H4010?10A10@10B3010D10H1082010D10HPAPAPAPJP5PPPAPAPAPAPAPAPNPAPAPAn0110O000:3010D10=10;2010D10H3010D10H10:2010710620105103301051071062010C1024010?10A10@10B3010D10H1082010D10HPAPJP5PRPAPAPAPAPAPAPAPAQ06PAn0110O000:3010D10=10;2010D10H3010D10H10:2010710620105103301051071062010D10H4010?10A10@10B3010C1021092010D10HPJP5PPPAPAPAPAPAPAPAPAPAPNn0110O000:3010D10=10;2010D10H3010D10H10:2010710620105103301051071062010D10H4010?10A10@10B3010D10H1082010C102n0110J000:3010010=10;201001013010010110:201071062010510330105107106201001014010?10A10@10B3010010110820100101#2PKPaP`PQC1]1]9PLP]g03D=RNPKPpPnAR70:S06C1PJP5PX1=87S051I@0R3'?1>2:RC'?PAPAPAPAPAPAPAPAPAn0110O000:3010C10>10<2010D1013010D10110:2010710620105103301051071062010D1014010?10A10@10B3010D1011082010D101#2PKP\PmPVC1S04]1]9^G=]IP:PKPsP\ARU0:S07C1PJP5Pp1=[7S08/?3/?CPAPAPAPAPAPAPAPAPAn0110O000:3010C10>10<2010D1013010D10110:2010710620105103301051071062010D1014010?10A10@10B3010D1011082010D101#2PJPJP5P:1=67S09?u10?n8:PAPAPAPAPAPAPAPAPAn0110O000:3010C10>10<2010D1013010D10110:2010710620105103301051071062010D1014010?10A10@10B3010D1011082010D101#210Z0PKP_PdP7C1]0S0K]1PmP]1=^7S0X?uL01>O:'LAR;70S0W,0ePKPcPkAR2;7S0VC1]0S02]1^G=^INP:1=hUS0T?uP01>Q:'LAR|70S0P,0cS0OQ0?/=TS0N1I`;S0c'?RC1>R7R3;q0%2C%23'6P<Q0@/=WS0`1Ia2'L1>`;S0b#2PKPuPtAR[@2C1P:Q0:,=YS0:1IV8S0a'L1>V8S0^#2Q0BQ0;'=S0;1IpMR3;q0Q0;#2S0I%23'6P<Q0CQ0<'=#2S0<1ImO#2PKPzQ0GAR^LOC1P:Q0DQ0='=#2S0=1IiQ#2P<1I0:#2A5N70[R3A5N0:1I70#2RC[A5N;7\C20\0:P0n2001000000120000000X;NX4NS0HP3^;N^4NS0YP:PjPRP0O3A5NjRA~jR11rjRPNP_Q0LPnPV%K:#XCl#2Q0_#c#c#c#c#cR3,p0%K0S0_9;4Y&0EHRC$0LR{PKP>1G4YREP0PCP0174XGd3M]0XJNQ0[PVPX%K_#XCl#2P=P_1pb3Ry%Kb9;4YRBP{PKP>PEPbH0IREPCB0Hb4:C]3MXH=P<1pg314ebS01%Kg5;>P{PKfbQ01,G>PgPCPg17>_Gd'6P{PEPCB0Hb4gC]9MyBPd1pe3ffRB14ckRy%Kf3;P{PKfeS0\1GByPfPCPf17BeGd'6P<fgRy14lcS0S%Kk3;P{PKPBQ0S,GyPkPCPk17yfGd1pc3fhREQ0E%Kc3;P{PKPyQ0E,GEPcPCPc17EkGd3MP:fiS0U14rqS0R%Kl3;P{PKQ0UfjS0Q14tr'GPqPCPqQ0Q/7lGdPxPuPtPdPj%KrS0dQ0d#XPPP0PMO9fkS0dQ0d@08ut80G}S0e1pt3flR314_dS0f%Kt3;S0gP{PKQ0dQ0f,G3S0hPtPCPt173rGdR}'6P8Q0gP}14vuS0i,@3S0j%C:R}1\:oS0k%KuS0lQ0l=Q:o'P3MX:?P7Q0f,@3S0lP:DJQ0gePGQ0i,G3P{PKP3P:PuPCPufmS0g/7tGdX>GP0Q0hPxQ0iQ0fP:O3J0UChChbLWbWMP0P:O2n2001000000121000000W2WKP0P:O2n2001000000121000000PaP0EVW0PaP0PPFwb<bNb2PKPxQ0ZARhPQC1eWNW1P0P:O2n2001000000121000000b1W<W1P0P:O2n2001000000121000000b1W0W1XH=XJNX6?X5=P0P:O2n0110N00012110K10LX3]P7P0P:O3P]Q00955ARG1a70S00,0gPKPfPe1a;7S0iC1]0]1^4=P:1aU0S0h,0fP5Q0MP:g00[ZRCQ0Jn0110400020000S0JX?5S0M/O0R{PCPKPqPl1aT;S0mP:D3b2W0X1GX7=X6?X5=P0P:O2n0110N00012010K10LX3]P0P:O2S0nP]AY;70S0o,0ePKPcPkAY2;7S0pC1]0S0q^1G^EN^4=P:AY|70S0r,0cS0sP{PCPKPtPrAYW2;S0tP:D3b2W0X1GXFNX7=X6?X5=P0P:O2n0110N00012010K10LX3]P7P0P:O3S0u20970S0v,0_P{PCPKPfPe2092;S0wP:D3b2W0X1GX@?XA?P0P:O2S0x20270S0y,0_Q0JXW5S0z/O0S0{PCPKPfPe2022;S0|P:D3b2W0X1GX;?X?=P0P:O2S0}B05;70S0~,0bQ0{PCPKPcPkB05@2;S10P:D3b2W0X1GX@?XA?X?=P7P0P:O3S11P]1`70S12,0gPKPfPe1`;7S13C1]0^1G^4=P:1`U0S14,0fP{PCPKPqPl1`T;S15P:D3b2W0X1GX7=X6?X5=P0P:O2n0110N00012010K10LX3]P0P:O2S16P2P;P7P0H06S17,0fP{PCPKPqPlP8P@P2P;H06S18P:D3b2W0X1GXU=XR]XT=XQ]P;P7P0P:O4S19P]AU;70S1:,0ePKPcPkAU2;7S1;C1]0S1<^1G^C?^4=P:AU|70S1=,0cS1>P{PCPKPtPrAUW2;S1?P:D3b2W0X1GXD?X7=X6?X5=P0P:O2n0110N00012010K10LX3]P7P0P:O3S1@P]1_70S1A,0gPKPfPe1_;7S1BC1]0^1G^4=P:1_U0S1C,0fP{PCPKPqPl1_T;S1DP:D3b2W0X1GX7=X6?X5=P0P:O2n0110N00012010K10LX3]P0P:O2S1En0110:000:3110010=10;201001013010010110:201071062010510330105107106201001014010?10A10@10B3010010110820100101P:PXO2W1W9XG=XINXB?X>=P0P:O2n0110N00012110K10LX3]P7P0P:O3P]PKPVPX1a0:S1FC1PJP5P`PA1=20Q03'?S1GPAPAPAPAPAPAPAPAn0110O000:3010D10=10;2010C1023010D10H10:2010710620105103301051071062010D10H4010?10A10@10B3010D10H1082010D10H#2PKPpPnPaC1S1H]1]9^4=P:PKPmPp1a~:S1IC1PJP5PVPA1=T0Q03'?S03PAPAPAPAPAPAPAPAn0110O000:3010D10=10;2010C1023010D10H10:2010710620105103301051071062010D10H4010?10A10@10B3010D10H1082010D10H#2PJPJP5P:PA1=[0?n@:S1JPAPAPAPAPAPAPAPAn0110O000:3010D10=10;2010C1023010D10H10:2010710620105103301051071062010D10H4010?10A10@10B3010D10H1082010D10H#210s0PKPjPZP7C1]0S1K]1PnP]Q0W,0gPKPfPeQ0VC1]0^1G^G=^INP:Q0P,0fP{PCPKPqPlARW2;S0PP:D3b2W0X1GXH=XJNX6?X5=P0P:O2n0110N00012010K10LX3]P7P0P:O3S0VP]1=601>1:'LS1LQ00,0dPKPbPgQ0iC1]0S0i]1^4=P:1=^~1>L:'LS1MQ0h,0bS0h14RPS1N/=|S1O1>Q7S1P;q0S1QQ1O#2Q1P#2'6S1PP<1=hT#2S1O1>P;#2S1RPKPlPc1aW2C1P:Q0?/=[#2S0?1>a8#2S1SA~X1:S1T1rX1S1UP=PVPtPSPLP:Cl#2S1V19w09;w^S1WQ0F/979B}:S1XQ0FPFQ0GQ1NP0CbO1S1N1FD9R9,}HS1Y55IS1Z[^8?'6]0X7=PrPLPOPVCl#2S1[P<Q0A19vn5;vS0A19wpS1\9B}:S1]PwPFQ0FQ0CP0CbO1S1^Q1Y55I[^8?Q1\9;w^S1\Q0F/9mS1_9B}:S1`Q1Z[^8?'6PVQ0FQ0CQ1_3;S1_19zsS1Z9B}:S1aPzQ0]14jZS1b'@S1c=NF0O1S1dQ1Y55I[^8?PfPZPiP`PRQ1ZPsP1P0P2O9S1eQ0D,@zS0D:0GzhS1fQ0]Q0>Q0]/9i3;S1gQ0Z/9ZS1h9B}:S1iQ0ZPFPxQ0@P0CbO1S0@Q1Y55I[^8?Q1cQ0kQ1hQ1h=Q:o'P5M}X:?P7Q0]Q0>'@S0]P:DJQ1geS0>Q1c19xj9B}:S1jPxANF70S1kO1S1lQ1Y55I[^8?X:?P0Q0]P:DJChbLWMWKP0P:O2n2001000000121000000W0PMP:P8Fwb<PKPtPr1a61C1eW<W1P0P:O2n2001000000121000000b1W0W1X7=X6?X5=P0P:O2n0110N00012110K10LX3]P0P:O2P]Q0o,0gPKPfPeQ0pC1]0^1G^EN^4=P:Q0r,0fP{PCPKPqPlQ0tP:D3b2W0X1GXFNX7=X6?X5=P0P:O2n0110N00012010K10LX3]P7P0P:O3S0tQ0v,0jP{PCPKPbPgQ0wP:D3b2W0X1GX@?XA?P0P:O2S0wQ0y,0jQ0{PCPKPbPgQ0|P:D3b2W0X1GX;?X?=P0P:O2S0|Q0~,0_Q0{PCPKPfPeQ10P:D3b2W0X1GX@?XA?X?=P7P0P:O3S10P]Q12,0dPKPbPgQ13C1]0S13^1G^4=P:Q14,0bS14P{PCPKPcPkQ15P:D3b2W0X1GX7=X6?X5=P0P:O2n0110N00012010K10LX3]P0P:O2S15Q17,0bP{PCPKPcPkQ18P:D3b2W0X1GXU=XR]XT=XQ]P;P7P0P:O4S18P]Q1:,0gPKPfPeQ1;C1]0^1G^C?^4=P:Q1=,0fP{PCPKPqPlQ1?P:D3b2W0X1GXD?X7=X6?X5=P0P:O2n0110N00012010K10LX3]P7P0P:O3S1?P]Q1A,0dPKPbPgQ1BC1]0S1B^1G^4=P:Q1C,0bS1CP{PCPKPcPkQ1DP:D3b2W0X1GX7=X6?X5=P0P:O2n0110N00012010K10LX3]P0P:O2S1Dn0110:000:3010010=10;211001013010010110:201071062010510330105107106201001014010?10A10@10B3010010110820100101P:P`O2W1W9X4=XB?X>=P0P:O2n0110N00012110K10LX3]P0P:O2P]PKPpPnAY70:S1=C1PJP5PXPAPAQ051>@0S1;'?S051I2:S17'?PAPAPAPAPAPAPAn0110O000:3010D10=10;2010D10H3010C10210M2010710620105103301051071062010D10H4010?10A10@10B3010D10H1082010D10H#2Q04]1]9^EN^4=P:PKPsP\AYU0:S0{C1PJP5PpPAPAQ08Q1;'?S1;Q17'?PAPAPAPAPAPAPAn0110O000:3010D10=10;2010D10H3010C10210M2010710620105103301051071062010D10H4010?10A10@10B3010D10H1082010D10H#2PJPJP5P:PAPAQ09?n10S09?u8:PAPAPAPAPAPAPAn0110O000:3010D10=10;2010D10H3010C10210M2010710620105103301051071062010D10H4010?10A10@10B3010D10H1082010D10H#2Q0K]1PmP]Q02^1G^G=^INP:Q0OP{PCPKPtPrQ0PP:D3b2W0X1GXH=XJNX6?X5=P0P:O2n0110N00012010K10LX3]P7P0P:O3S0OQ0nP]Q0X?nL0S0X1IO:'LQ0q]1^EN^4=P:Q0T?nP0S0T1IQ:'LQ0sQ0NQ0b'?S0b1IR7S0N;q0Q0b#2S0qQ0N#2'6P<Q0`1>a2'LS0`Q0c#2PKPuPtAY[@2C1P:Q0:Q0^'LS0^Q0a#2Q0;1>pMS0a;q0S0;Q0IQ0a#2'6S0IP<Q0<1>mO#2S0aPKPzQ0GAY^LOC1P:Q0=1>iQ#2S0:Q0HQ0YP:PZPPP8O3S0YA5NZPA~d`7S0H1rd`S0cP=P_Q0LPnPVP:Cl#2S0N1940S0P9;4YS021D4XQ0P5SHQ0\/979B}:S0PPIQ0\PFPBQ0BP0CbO1S0BPHPH&0}0S171DBnP9FZ[^8?3M]0X7=Q0[PVPXP_Cl#2S08PNP_194bS0~9;4YS0y1D4:Q0~5SHQ0\/9eS0v9B}:S0rPIQ0BPHPHQ171DB7P9FZ[^8?3MXFNP<Q0119>gS0p5;>S011D>_Q0p5SHQ0~9B}:S0pPIP4PFQ0\14kfR>P0CbO1S1YPHPHQ17Q0\/DbP9FZ[^8?'6Q0y1D4gQ0~5SHQ0rPIQ0BPHPHQ171DBeR4P9FZ[^8?3MPdQ0\Q0v7;>S0v19Bf9SH419ykS0\9B}:S0~PIPyB08EqlS1m=NF0O1S1nPHPHQ171DEkR4P9FZ[^8?'6P<1DyfQ0\5SH19EcRB9B}:PIPEPFQ0UQ0RP0CbO1PHPHQ17Q0U/DcR>P9FZ[^8?Q0E=;EBS0RASH4BQ0U/9lRB9B}:S1oPIQ0UPFQ0QQ1bP0CbO1S1bPHPHQ17Q0Q/DlP9FZ[^8?3MP:ASH>BQ0d/9rR>9B}:PIQ0dQ0j=NF0O1PHPHQ171D3rR4P9FZ[^8?PxPuPtPdPjP>PrPPP@PMO9Q0eQ0f193tR>5;3S0eASH4>S0dQ0g/9uR>9B}:S0UQ0gfnR4@08bg=NF0O1PHPHQ171D4uP9I0|R355I[^8?'6Q0jQ0kAQ:>o,P>5M}X:?P8Q0lP:DJQ0eeQ0jQ0g/Dt=SH>194v9B}:PIP4Q1kO1PHPHQ17fo/DvP9FZ[^8?'6X:?Q0dQ0UQ0gQ0F>084w=NF0O1=5I3[^8?P7P0ChQ0lP:DJChbLWbWMP0P:O2n2001000000121000000W2WKP0P:O2n2001000000121000000PaP7EVW0PaP:PPFwbNb<b2PKPxQ0ZAYhPQC1eWNW1P0P:O2n2001000000121000000b1W<W1P0P:O2n2001000000121000000b1W0W1XFNX7=X6?X5=P0P:O2n0110N00012110K10LX3]P7P0P:O3Q0xQ0}Q11Q16Q19Q1@Q1En0110:000:3010010=10;201001013110010110:201071062010510330105107106201001014010?10A10@10B3010010110820100101P:PXO2W1W9Z0FNX4=XB?X>=P0P:O2n0110N00012110K10LX3]P7P0P:O3PKPXPa2090:R3C1PJ10V:PKPmPpP0C1]0S1@P`P]Q06,0iPKPdPjQ0WC1]0^G=^INS0sP:Q07,0dS0lQ0M/OSS0UPCPKPePbART;7S0FP:D3S0gb2W0XH=XJNX6?X5=P0P:O2n0110N00012010K10LX3]P7P0P:O3P]Q1F,0\PKPZPiQ00C1]0^4=S0dP:Q1I,0ZS17Q0M/OOR4PCPKPgP_1a|7S0jP:D3S0eb2W0X7=X6?X5=P0P:O2n0110N00012010K10LX3]P0P:O2P]Q1=,0iPKPdPjQ0oC1]0^EN^4=S1pP:Q0{,0dS1qQ0UPCPKPePbAYT;7S1rP:D3S1sb2W0XFNX7=X6?X5=P0P:O2n0110N00012010K10LX3]P7P0P:O310m3S1tQ0M/O@S0MPCPKPZPi209;7S1uP:D3S1vb2W0XY?XZ?P0P:O22020:S1w,0mS1xQ0z/O@S1yPCPKPZPi202;7S1zP:D3S1{b2W0X;?X?=P0P:O2B0570:Rw,0sS1|Q0z/O1S1}PCPKPdPjB052;7S1~P:D3S20b2W0XY?XZ?X?=P7P0P:O3P]1`0:R9,0\PKPZPiQ12C1]0^4=S21P:1`~:Rv,0ZS22P4PCPKPgP_1`|7S23P:D3S24b2W0X7=X6?X5=P0P:O2n0110N00012010K10LX3]P0P:O2P;P7P0P:H06R>,0ZS25P4PCPKPgP_P@P2P;P7H06S26P:D3S27b2W0XU=XR]XT=XQ]P;P7P0P:O4P]AU70:S28,0iPKPdPjQ1:C1]0^C?^4=S29P:AUU0:RU,0dS2:Q0UPCPKPePbAUT;7S2;P:D3S2<b2W0XD?X7=X6?X5=P0P:O2n0110N00012010K10LX3]P7P0P:O3P]1_0:RT,0\PKPZPiQ1AC1]0^4=S2=P:1_~:S2>,0ZS2?P4PCPKPgP_1_|7S2@P:D3S2Ab2W0X7=X6?X5=P0P:O2n0110N00012010K10LX3]P0P:O2n0110:000:3010010=10;201001013010010110:201071062010510330105107106201001014010?10A10@10B3010010110820100101PSO1X1GW9X@?XA?P0P:O2PKPXPaQ1wC1PJQ1@P`P]Q0sP:Q0lQ0z/OSR|PCQ0gb2W0XH=XJNX6?X5=P0P:O2n0110N00012010K10LX3]P7P0P:O3P]Q0dP:Q17Q0z/OOR~PCQ0eb2W0X7=X6?X5=P0P:O2n0110N00012010K10LX3]P0P:O2P]Q1pP:Q1qP|PCQ1sb2W0XFNX7=X6?X5=P0P:O2n0110N00012010K10LX3]P7P0P:O3Q1tQ1yPCQ1vb2W0X@?XA?P0P:O2Q1xQ0JZ0E5S0J/O@S1tPCQ1{b2W0Z0G?XW=P0P:O2Q1|Q0J/O1S0JPCQ20b2W0X@?XA?XW=P7P0P:O3P]Q21P:Q22P~PCQ24b2W0X7=X6?X5=P0P:O2n0110N00012010K10LX3]P0P:O2Q25P~PCQ27b2W0XU=XR]XT=XQ]P;P7P0P:O4P]Q29P:Q2:P|PCQ2<b2W0XD?X7=X6?X5=P0P:O2n0110N00012010K10LX3]P7P0P:O3P]Q2=P:Q2?P~PCQ2Ab2W0X7=X6?X5=P0P:O2n0110N00012010K10LX3]P0P:O2n0110:000:3010010=10;201001013010010110:201071062010510330105107106201001014010?10A10@10B3010010110820100101PSO1X1GW9X;?X?=P0P:O2PKPnPVPwC1PJ10p:PKPsP\P0C1]0PXP]Q06,0jPKPgP_Q0WC1]0^G=^INP:Q07,0gP|PCPKPkPfQ0FP:D3b2W0XH=XJNX6?X5=P0P:O2n0110N00012010K10LX3]P7P0P:O3P]Q1F,0iPKPdPjQ00C1]0^4=P:Q1I,0dP~PCPKPePbQ0jP:D3b2W0X7=X6?X5=P0P:O2n0110N00012010K10LX3]P0P:O2P]Q1=,0jPKPgP_Q0oC1]0^EN^4=P:Q0{,0gP|PCPKPkPfQ1rP:D3b2W0XFNX7=X6?X5=P0P:O2n0110N00012010K10LX3]P7P0P:O310s3Q1yPCPKPdPjQ1uP:D3b2W0XY?XZ?P0P:O2Q1w,0sQ1tPCPKPdPjQ1zP:D3b2W0X;?XW=P0P:O210ZwQ0JPCPKPgP_Q1~P:D3b2W0XY?XZ?XW=P7P0P:O3P]10i9PKPdPjQ12C1]0^4=P:10dvP~PCPKPePbQ23P:D3b2W0X7=X6?X5=P0P:O2n0110N00012010K10LX3]P0P:O210d>P~PCPKPePbQ26P:D3b2W0XU=XR]XT=XQ]P;P7P0P:O4P]Q28,0jPKPgP_Q1:C1]0^C?^4=P:10gUP|PCPKPkPfQ2;P:D3b2W0XD?X7=X6?X5=P0P:O2n0110N00012010K10LX3]P7P0P:O3P]10iTPKPdPjQ1AC1]0^4=P:Q2>,0dP~PCPKPePbQ2@P:D3b2W0X7=X6?X5=P0P:O2n0110N00012010K10LX3]P0P:O2n0110:000:3010010=10;201001013010010110:201071062010510330105107106201001014010?10A10@10B3010010110820100101PPO1X1GW9X@?XA?X?=P7P0P:O3P]PKPVPXP9C1PJP5P`PAPAPAPAPAPAQ1GPAPAPAn0110O000:3010D10=10;2010D10H3010D10H10:2010710620105103301051071062010C1024010?10A10@10B3010D10H1082010D10H#2Q1H]1]9^4=P:PKPmPpPvC1PJP5PVPAPAPAPAPAPAQ03PAPAPAn0110O000:3010D10=10;2010D10H3010D10H10:2010710620105103301051071062010C1024010?10A10@10B3010D10H1082010D10H#2PJPJP5P:PAPAPAPAPAPAQ1JPAPAPAn0110O000:3010D10=10;2010D10H3010D10H10:2010710620105103301051071062010C1024010?10A10@10B3010D10H1082010D10H#2Q1K]1PnQ0VP]Q0i^1G^4=P:Q0hP{PCPKPcPkQ0mP:D3b2W0X1GX7=X6?X5=P0P:O2n0110N00012010K10LX3]P0P:O2R{Q0tQ0wQ0|Q10P]Q1LQ13]1^4=P:Q1MQ14Q1QQ1PP<Q1OQ1RPKPlPc1`W2C1P:Q0?Q1SQ1TQ1UP=PVQ1VQ1W%C0R~Q0_,H7R|19z2'^PKPzQ0]=NF;P7C{#2RS[[^;N^S?'6]0X7=Q1[P<Q0AQ0G/9\,^|PKQ0GQ0D=NF;P7C{#2[\~^;N^S?Q1\Q1Z,^|PS[\~^;N^S?'6PVQ1_Q1h,^|PKQ0ZPFPxQ0fP;CbP7C{#2[\~^;N^S?Q1eQ1fQ1gQ0[/9d,^|PKQ0[PFQ0LPYP;CbP7C{#2[\~^;N^S?Q0>Q1cQ0L/9_,^|PKQ0LANF2;P7C{#2[\~^;N^S?X:?P0Q0]P:DJChbLWMWKP0P:O2n2001000000121000000W0PMP:P8Fwb<PKPtPr1`61C1eW<W1P0P:O2n2001000000121000000b1W0W1X7=X6?X5=P0P:O2n0110N00012110K10LX3]P0P:O2Q18Q1?Q1Dn0110:000:3010010=10;201001013010010110:201071062010510330105107106211001014010?10A10@10B3010010110820100101P:P`O2W1W9X4=XB?X>=P0P:O2n0110N00012110K10LX3]P0P:O2PKPmPpP>C1PJ10\:PKPZPiP0C1]0PnP]Q06,0_PKPePbQ0WC1]0^G=^INP:Q07,0eQ0UPCPKPlPcQ0FP:D3b2W0XH=XJNX6?X5=P0P:O2n0110N00012010K10LX3]P7P0P:O3P]Q1F,0jPKPgP_Q00C1]0^4=P:Q1I,0gP4PCPKPkPfQ0jP:D3b2W0X7=X6?X5=P0P:O2n0110N00012010K10LX3]P0P:O2P]Q1=,0_PKPePbQ0oC1]0^EN^4=P:Q0{,0eQ0UPCPKPlPcQ1rP:D3b2W0XFNX7=X6?X5=P0P:O2n0110N00012010K10LX3]P7P0P:O310Z3Q0MPCPKPgP_Q1uP:D3b2W0X@?XA?P0P:O2Q1w,0ZQ1yPCPKPgP_Q1zP:D3b2W0X;?X?=P0P:O210dwQ1}PCPKPePbQ1~P:D3b2W0X@?XA?X?=P7P0P:O3P]10j9PKPgP_Q12C1]0^4=P:10gvP4PCPKPkPfQ23P:D3b2W0X7=X6?X5=P0P:O2n0110N00012010K10LX3]P0P:O210g>P4PCPKPkPfQ26P:D3b2W0Z0I=X~]Z0H=X}]P;P7P0P:O4P]Q28,0_PKPePbQ1:C1]0^C?^4=P:10eUQ0UPCPKPlPcQ2;P:D3b2W0XD?X7=X6?X5=P0P:O2n0110N00012010K10LX3]P7P0P:O3P]10jTPKPgP_Q1AC1]0^4=P:Q2>,0gP4PCPKPkPfQ2@P:D3b2W0X7=X6?X5=P0P:O2n0110N00012010K10LX3]P0P:O2n0110:000:3010010=10;201001013010010110:201071062010510330105107106201001014010?10A10@10B3010010110820100101P`O1X1GW9XU=XR]XT=XQ]P;P7P0P:O4P]PKPpPnQ28C1PJP5PXPAPAPAPAPAPAPAPAQ051W2:RG'?PAn0110O000:3010D10=10;2010D10H3010D10H10:2010710620105103301051071062010D10H4010?10A10@10B3010C1021092010D10H#2Q04]1]9^C?^4=P:PKPsP\PUC1PJP5PpPAPAPAPAPAPAPAPAQ1;/?GPAn0110O000:3010D10=10;2010D10H3010D10H10:2010710620105103301051071062010D10H4010?10A10@10B3010C1021092010D10H#2PJPJP5P:PAPAPAPAPAPAPAPAQ091W8:'?PAn0110O000:3010D10=10;2010D10H3010D10H10:2010710620105103301051071062010D10H4010?10A10@10B3010C1021092010D10H#2Q0K]1PmQ0OQ0nQ0uQ0xQ0}Q11Q16Q19P]Q0X1WO:'LQ1<]1^C?^4=P:Q0T1WQ:'LQ1>Q0b1WR7RR;q0Q0q%2R'6P<Q0`1W`;#2PKPuPtAU[@2C1P:Q0^1WV8#2Q0;Q0IP<Q0<Q0aPKPzQ0GAU^LOC1P:Q0=Q0:P<1W0:#21:70[R^1:0:1W70#2RL[1:;7\L20{0:P0n2001000000120000000X;?X4?P^^;?^4?Q0Y1:ZPQ0HQ0cP=P_Q0NQ02Q0PPIQ0BPH1FDnC][^8?'6]0X7=Q08P?P_Q0yQ0rPIQ0BPH1FD7C][^8?'6XD?P<Q01Q0pPIQ1YPH1FDbC][^8?Q0yQ0rPIQ0BPH1FDeC][^8?'6PdQ0vQ0~PIQ1nPH1FDkC][^8?Q0GPlPcPsP\Q0\PkPOP0P2O9PyQ0CPyQ0SCTQ0RQ1oPIQ1bPH1FDlC][^8?Q1mQ0kAQ:Bo,PB5M}X:?P7Q0E,@EREP:DJQ0ReQ1mQ0Q/9q9B}:PIQ0QQ1kO1PH1FDqC][^8?X:?P0PEP:DJChbLWMWKP0P:O2n2001000000121000000PaP7EVW0PaP:PPFwbNb<b2PKPxQ0ZAUhPQC1eWNW1P0P:O2n2001000000121000000b1W<W1P0P:O2n2001000000121000000b1W0W1XD?X7=X6?X5=P0P:O2n0110N00012110K10LX3]P7P0P:O3Q1En0110:000:3010010=10;201001013010010110:201071062010510330105107106201001014010?10A10@10B3110010110820100101P:PXO2W1W9XC?X4=XB?X>=P0P:O2n0110N00012110K10LX3]P7P0P:O3P]PKPVPXPTC1PJP5P`PAPAPAPAPAPAPAPAPAQ1Gn0110O000:3010D10=10;2010D10H3010D10H10:2010710620105103301051071062010D10H4010?10A10@10B3010D10H1082010C102#2Q1H]1]9^4=P:PKPmPpQ2>C1PJP5PVPAPAPAPAPAPAPAPAPAQ03n0110O000:3010D10=10;2010D10H3010D10H10:2010710620105103301051071062010D10H4010?10A10@10B3010D10H1082010C102#2PJPJP5P:PAPAPAPAPAPAPAPAPAQ1Jn0110O000:3010D10=10;2010D10H3010D10H10:2010710620105103301051071062010D10H4010?10A10@10B3010D10H1082010C102#2Q1K]1PnQ0VP{Q0tQ0wQ0|Q10Q15Q18Q1?P]Q1LQ1B]1^4=P:Q1MQ1CQ1QQ1PP<Q1OQ1RPKPlPc1_W2C1P:Q0?Q1SQ1TQ1UP=PVQ1VQ1WQ1XQ1N&0PHRH55I#|RW[^8?'6]0X7=Q1[P<Q0AQ1]Q1^=5IH#|[^8?Q1\Q1`PW[^8?'6PVQ1_Q1aQ1d=5IH#|[^8?Q1eQ1fQ1gQ1iQ0@=5IH#|[^8?Q0>Q1cQ1jQ1l=5IH#|[^8?X:?P0Q0]P:DJChbLWMWKP0P:O2n2001000000121000000W0PMP:P8Fwb<PKPtPr1_61C1eW<W1P0P:O2n2001000000121000000b1W0W1X7=X6?X5=P0P:O2n0110N00012110K10LX3]P0P:O2n0110:000:3010010=10;201001013010010110:201071062010510330105107106201001014010?10A10@10B3010010110821100101P:P`O2W1W9X4=XB?X>=P0P:O2n0110N00012110K10LX3]P0P:O2n0110:000:3110010=10;211001013110010110:211071062110510331105107106211001014110?10A10@10B3110010110821100101P1P7O2bkbxW1P:O1n200100000021000011000b1W0W1W9WsXvJX<JWEWwWlo"). Qed.

(* [comment removed for export] *)
#[using="SEGS_in_hull"] Lemma seg_rom_off_hull : forall a : word, in_hull A (bv_unsigned a) = false -> seg_rom SEGS a = None.
Proof.
  intros a Ha. unfold seg_rom.
  rewrite (memory_read1_hidden SEGS (fun x => negb (in_hull A (bv_unsigned x)))); [reflexivity| |].
  - intros x Hx. apply SEGS_in_hull. apply negb_true_iff in Hx. exact Hx.
  - rewrite Ha. reflexivity.
Qed.

#[using="SEGS_in_hull"] Lemma rdn_bytes_some : forall M (a : word) w bs,
  rdn SEGS M a w = Some bs ->
  forall x : word, (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat w)%Z ->
  in_hull A (bv_unsigned x) = false -> M x <> None.
Proof.
  intros M a w. revert a. induction w as [|w IH]; intros a bs Hr x Hx Hh; [lia|].
  cbn [rdn] in Hr.
  destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
  - assert (x = a) by (apply bv_eq; exact Heq). subst x.
    destruct (M a) eqn:HMa; [congruence|]. rewrite (seg_rom_off_hull a Hh) in Hr. discriminate.
  - destruct (match M a with Some b => Some b | None => seg_rom SEGS a end) as [b|]; [|discriminate].
    destruct (rdn SEGS M (a + 1)%bv w) as [rest|] eqn:Hr2; [|discriminate].
    pose proof (u64_range x).
    assert (Hu1 : bv_unsigned (a + 1)%bv = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
    eapply (IH (a + 1)%bv rest Hr2); [rewrite Hu1; lia | exact Hh].
Qed.

#[using="SEGS_in_hull"] Lemma cover1_sound : forall E M k b i e,
  know_ok SEGS E M k -> cover1 k b i = Some e ->
  (i < e)%Z /\ forall j, (i <= j < e)%Z -> in_hull A (uE E b + j) = false ->
     (0 <= uE E b + j < 2 ^ 64)%Z /\ M (Z_to_bv 64 (uE E b + j)) <> None.
Proof.
  intros E M k b i e HK. induction k as [|K r IH]; intros H; [discriminate|].
  inversion HK as [|K' r' HKK Hr]; subst. cbn [cover1] in H.
  match type of H with (match ?h with Some e0 => Some e0 | None => _ end = _) => destruct h as [e1|] eqn:Hhit end;
    [injection H as <- | exact (IH Hr H)].
  clear IH Hr HK.
  assert (ZF : forall kb kk l (P : option byte -> Prop),
            (flat E (SA kb kk) (elenZ E (ELit l)) /\ forall i0, (0 <= i0 < elenZ E (ELit l))%Z -> P (M (Z_to_bv 64 (estart E (SA kb kk) + i0)))) ->
            (forall x, P x -> x <> None) ->
            (if (expr_eqb b kb && Z.leb 0 l && Z.ltb l two64 && Z.leb kk i && Z.ltb i (kk + l))%bool then Some (kk + l)%Z else None) = Some e1 ->
            (i < e1)%Z /\ forall j, (i <= j < e1)%Z -> in_hull A (uE E b + j) = false ->
               (0 <= uE E b + j < 2 ^ 64)%Z /\ M (Z_to_bv 64 (uE E b + j)) <> None).
  { intros kb kk l P [Hfl Hall] HP Hc.
    destruct (expr_eqb b kb && Z.leb 0 l && Z.ltb l two64 && Z.leb kk i && Z.ltb i (kk + l))%bool eqn:Hcnd; [|discriminate].
    injection Hc as <-.
    repeat match type of Hcnd with (_ && _)%bool = true => apply andb_prop in Hcnd as [Hcnd ?X] end.
    apply expr_eqb_eq in Hcnd. subst kb. apply Z.leb_le in X2. apply Z.ltb_lt in X1. apply Z.leb_le in X0. apply Z.ltb_lt in X.
    unfold two64 in X1. rewrite (elenZ_lit E l) in Hfl, Hall by lia.
    destruct Hfl as (F1 & F2 & F3 & F4). unfold estart in *; cbn [a_base a_off] in *. unfold uE.
    split; [lia|]. intros j Hj Hh. split; [lia|].
    replace (bv_unsigned (edenot E b) + j)%Z with (bv_unsigned (edenot E b) + kk + (j - kk))%Z by lia.
    apply HP. apply Hall. lia. }
  destruct K as [[kb kk] w v|[kb kk] [l| | | | | | |]|[kb kk] [l| | | | | | |] bk| | | | | |[kb kk] [l| | | | | | |] fc|[kb kk] [l| | | | | | |]];
    try discriminate.
  - (* [comment removed for export] *)
    destruct (expr_eqb b kb && Z.leb kk i && Z.ltb i (kk + Z.of_nat w))%bool eqn:Hcnd; [|discriminate]. injection Hhit as <-.
    apply andb_prop in Hcnd as [Hcnd X]. apply andb_prop in Hcnd as [Hb X0].
    apply expr_eqb_eq in Hb. subst kb. apply Z.leb_le in X0. apply Z.ltb_lt in X.
    cbn [kentry_ok] in HKK. destruct HKK as (Hw & Hfl & Hrd).
    pose proof (flat_u E _ _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4). unfold estart in *; cbn [a_base a_off] in *. unfold uE.
    split; [lia|]. intros j Hj Hh. split; [lia|].
    apply (rdn_bytes_some M _ w _ Hrd); rewrite ?Hu, ?u64_lit by lia; [lia | exact Hh].
  - (* [comment removed for export] *) eapply (ZF kb kk l (fun x => x = Some (Z_to_bv 8 0))); [exact HKK | intros x ->; discriminate | exact Hhit].
  - (* [comment removed for export] *) cbn [kentry_ok] in HKK. destruct HKK as (Hfl & Hlen & Hall).
    eapply (ZF kb kk l (fun x => exists b0, x = Some b0)); [split; [exact Hfl | intros i0 Hi0; eexists; apply Hall; exact Hi0] | intros x [b0 ->]; discriminate | exact Hhit].
  - (* [comment removed for export] *) eapply (ZF kb kk l (fun x => x = Some (Z_to_bv 8 fc))); [exact HKK | intros x ->; discriminate | exact Hhit].
  - (* [comment removed for export] *) eapply (ZF kb kk l (fun x => x <> None)); [exact HKK | intros x Hx; exact Hx | exact Hhit].
Qed.

#[using="SEGS_in_hull"] Lemma cover_x_sound : forall fuel E M k b i stop,
  know_ok SEGS E M k -> cover_x fuel k b i stop = true ->
  forall j, (i <= j < stop)%Z -> in_hull A (uE E b + j) = false ->
    (0 <= uE E b + j < 2 ^ 64)%Z /\ M (Z_to_bv 64 (uE E b + j)) <> None.
Proof.
  induction fuel as [|f IH]; intros E M k b i stop HK H j Hj Hh; [discriminate|].
  cbn [cover_x] in H. destruct (Z.leb_spec stop i); [lia|].
  destruct (cover1 k b i) as [e|] eqn:Hc; [|discriminate].
  destruct (Z.ltb_spec i e); [|discriminate].
  destruct (cover1_sound E M k b i e HK Hc) as [_ Hcov].
  destruct (Z.lt_ge_cases j e).
  - apply Hcov; [lia | exact Hh].
  - eapply IH; [exact HK | exact H | lia | exact Hh].
Qed.

#[using="SEGS_in_hull HULL_ok"] Lemma kunk_covered_sound : forall E M k K, know_ok SEGS E M k -> kunk_covered A k K = true -> kentry_ok SEGS E M K.
Proof.
  intros E M k K HK H. unfold kunk_covered in H.
  destruct K as [| | | | | | | | |[b o] [n| | | | | | |]]; try discriminate.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  apply Z.ltb_lt in H. apply Z.leb_le in X3. apply Z.leb_le in X2.
  pose proof (flat_x_sound E M k b o (ELit n) HK X1) as (F1 & F2 & F3).
  pose proof (ranges_apart_x_sound SEGS E M k _ _ _ _ _ _ HK X0) as AP0.
  cbn [edenot] in F2, F3. rewrite u64_lit in F2, F3 by lia.
  pose proof HULL_ok as HU; unfold hull_ok, KHI in HU.
  rewrite (elenZ_lit E n) in AP0 by lia. rewrite (elenZ_lit E (img_hi A - img_lo A)) in AP0 by lia.
  unfold estart in AP0; cbn [a_base a_off edenot] in AP0. rewrite u_lit0 in AP0.
  cbn [kentry_ok]. rewrite elenZ_lit by lia. split.
  - unfold flat, estart in *; cbn [a_base a_off] in *. lia.
  - intros i Hi. unfold estart in *; cbn [a_base a_off] in *.
    replace (bv_unsigned (edenot E b) + o + i)%Z with (uE E b + (o + i))%Z by (unfold uE; lia).
    apply (cover_x_sound _ E M k b o (o + n) HK X); [lia|].
    unfold in_hull, uE. apply andb_false_iff.
    destruct AP0 as [AP0|AP0]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
Qed.

#[using="SEGS_in_hull HULL_ok"] Lemma kn_incl_h_sound : forall E M k tk, know_ok SEGS E M k -> kn_incl_h A k tk = true -> know_ok SEGS E M tk.
Proof.
  intros E M k tk HK H. unfold kn_incl_h in H. apply Forall_forall. intros K Hin.
  pose proof (proj1 (forallb_forall _ _) H K Hin) as HK1. unfold kn_incl1_h in HK1.
  destruct (existsb (fun X => kentry_eqb X K) k) eqn:Hex1.
  { apply existsb_exists in Hex1 as [X [HinX Heq]]. apply kentry_eqb_eq in Heq. subst. exact (proj1 (Forall_forall _ _) HK K HinX). }
  (* [comment removed for export] *)
  assert (IMG : kimg_sub_covered k K = true -> kentry_ok SEGS E M K).
  { intros Hc. unfold kimg_sub_covered in Hc. destruct K as [| | |lo hi| | | | | |]; try discriminate.
    apply existsb_exists in Hc as [X [HinX HX]]. destruct X as [| | |lo' hi'| | | | | |]; try discriminate.
    apply andb_prop in HX as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof (proj1 (Forall_forall _ _) HK _ HinX) as HKX. cbn [kentry_ok] in HKX |- *.
    destruct HKX as (Ha & Hb & Hc). split; [lia|]. split; [lia|]. intros i Hi. apply Hc. lia. }
  destruct (kflat_h k K) eqn:Hfl.
  - destruct (existsb (fun X => kentry_eqb_h X K) k) eqn:Hex.
    + apply existsb_exists in Hex as [X [HinX Heq]].
      eapply kentry_eqb_h_sound; [exact HK | exact (proj1 (Forall_forall _ _) HK X HinX) | exact Heq | exact Hfl].
    + destruct (kimg_sub_covered k K) eqn:Himg; [exact (IMG eq_refl)|]. eapply kunk_covered_sound; [exact HK | exact HK1].
  - destruct (kimg_sub_covered k K) eqn:Himg; [exact (IMG eq_refl)|]. eapply kunk_covered_sound; [exact HK | exact HK1].
Qed.

(* [comment removed for export] *)
Definition is_havoc (lo hi : nat) (t : expr) : option nat :=
  match t with EVar v => if (Nat.leb lo v && Nat.ltb v hi)%bool then Some v else None | _ => None end.

Fixpoint henv (lo hi : nat) (E : env) (rs ts : list expr) : env :=
  match rs, ts with
  | r :: rs', t :: ts' =>
      let E1 := henv lo hi E rs' ts' in
      match is_havoc lo hi t with Some v => upd E1 v (edenot E r) | None => E1 end
  | _, _ => E
  end.

#[using="Type"] Lemma is_havoc_range : forall lo hi t v, is_havoc lo hi t = Some v -> t = EVar v /\ (lo <= v < hi)%nat.
Proof.
  intros lo hi t v H. destruct t; try discriminate. cbn [is_havoc] in H.
  destruct (Nat.leb lo n && Nat.ltb n hi)%bool eqn:Hc; [|discriminate]. injection H as <-.
  apply andb_prop in Hc as [H1 H2]. apply Nat.leb_le in H1. apply Nat.ltb_lt in H2. split; [reflexivity | lia].
Qed.

#[using="Type"] Lemma henv_agree : forall lo hi E rs ts, env_agree lo E (henv lo hi E rs ts).
Proof.
  intros lo hi E rs. induction rs as [|r rs IH]; intros [|t ts]; cbn [henv]; try apply env_agree_refl.
  destruct (is_havoc lo hi t) as [v|] eqn:Hv; [|apply IH].
  apply is_havoc_range in Hv as [_ Hv]. eapply env_agree_trans; [apply IH|]. eapply env_agree_le; [apply upd_agree | lia].
Qed.

#[using="Type"] Lemma henv_high : forall lo hi E rs ts n, (hi <= n)%nat -> ev (henv lo hi E rs ts) n = ev E n.
Proof.
  intros lo hi E rs. induction rs as [|r rs IH]; intros [|t ts] n Hn; cbn [henv]; try reflexivity.
  destruct (is_havoc lo hi t) as [v|] eqn:Hv; [|apply IH; exact Hn].
  apply is_havoc_range in Hv as [_ Hv]. cbn [upd ev]. destruct (Nat.eqb_spec n v); [lia|]. apply IH. exact Hn.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma regs_match_h_char : forall lo hi seen rs ts, regs_match_h lo hi seen rs ts = true ->
  length rs = length ts /\
  forall i, (i < length ts)%nat ->
    (exists v, is_havoc lo hi (nth i ts (ELit 0)) = Some v /\ ~ In v seen /\
               forall i', (i' < i)%nat -> is_havoc lo hi (nth i' ts (ELit 0)) <> Some v)
    \/ (is_havoc lo hi (nth i ts (ELit 0)) = None /\ nth i ts (ELit 0) = nth i rs (ELit 0) /\ AP.expr_vars_lt lo (nth i ts (ELit 0)) = true).
Proof.
  intros lo hi seen rs. revert seen. induction rs as [|r rs IH]; intros seen [|t ts] H; cbn [regs_match_h length] in H |- *; try discriminate.
  - split; [reflexivity | intros i Hi; lia].
  - assert (STEP : forall seen', regs_match_h lo hi seen' rs ts = true -> (forall v, In v seen -> In v seen') ->
              (forall v, is_havoc lo hi t = Some v -> In v seen') ->
              length rs = length ts /\ forall i, (Datatypes.S i < Datatypes.S (length ts))%nat ->
                (exists v, is_havoc lo hi (nth (Datatypes.S i) (t :: ts) (ELit 0)) = Some v /\ ~ In v seen /\
                   forall i', (i' < Datatypes.S i)%nat -> is_havoc lo hi (nth i' (t :: ts) (ELit 0)) <> Some v)
                \/ (is_havoc lo hi (nth (Datatypes.S i) (t :: ts) (ELit 0)) = None /\ nth (Datatypes.S i) (t :: ts) (ELit 0) = nth (Datatypes.S i) (r :: rs) (ELit 0)
                    /\ AP.expr_vars_lt lo (nth (Datatypes.S i) (t :: ts) (ELit 0)) = true)).
    { intros seen' Hm Hsub Ht. destruct (IH seen' ts Hm) as [Hlen Hc]. split; [exact Hlen|].
      intros i Hi. cbn [nth]. destruct (Hc i ltac:(lia)) as [[v (Hv & Hns & Hbefore)]|Hn]; [left|right; exact Hn].
      exists v. split; [exact Hv|]. split; [intros Hin; apply Hns; apply Hsub; exact Hin|].
      intros [|i'] Hi'; cbn [nth].
      - intros Heq. apply Hns. apply Ht. exact Heq.
      - apply Hbefore. lia. }
    destruct (is_havoc lo hi t) as [v|] eqn:Hv.
    + destruct t as [|w| | | | | |]; try discriminate. cbn [is_havoc] in Hv.
      destruct (Nat.leb lo w && Nat.ltb w hi)%bool eqn:Hr; [|discriminate]. injection Hv as Hwv. subst v.
      apply andb_prop in H as [Hnew Hm]. apply negb_true_iff in Hnew.
      assert (Hns : ~ In w seen).
      { intros Hin. enough (existsb (Nat.eqb w) seen = true) by congruence. apply existsb_exists. exists w. split; [exact Hin | apply Nat.eqb_refl]. }
      destruct (STEP (w :: seen) Hm ltac:(intros; right; assumption) ltac:(intros v' Hv'; injection Hv' as <-; left; reflexivity)) as [Hlen Hc].
      split; [rewrite Hlen; reflexivity|]. intros [|i] Hi; [|exact (Hc i Hi)].
      left. exists w. cbn [nth is_havoc]. rewrite Hr. split; [reflexivity|]. split; [exact Hns|]. intros i' Hi'. lia.
    + assert (Hm : (expr_eqb r t && AP.expr_vars_lt lo t && regs_match_h lo hi seen rs ts)%bool = true).
      { destruct t; try exact H. cbn [is_havoc] in Hv. destruct (Nat.leb lo n && Nat.ltb n hi)%bool; [discriminate | exact H]. }
      apply andb_prop in Hm as [Hm1 Hm]. apply andb_prop in Hm1 as [He Hvl]. apply expr_eqb_eq in He. subst t.
      destruct (STEP seen Hm ltac:(intros; assumption) ltac:(intros v' Hv'; discriminate Hv')) as [Hlen Hc].
      split; [rewrite Hlen; reflexivity|]. intros [|i] Hi; [|exact (Hc i Hi)].
      right. cbn [nth]. split; [exact Hv|]. split; [reflexivity | exact Hvl].
Qed.

#[using="Type"] Lemma henv_havoc : forall lo hi E rs ts i v,
  length rs = length ts -> (i < length ts)%nat ->
  is_havoc lo hi (nth i ts (ELit 0)) = Some v ->
  (forall i', (i' < i)%nat -> is_havoc lo hi (nth i' ts (ELit 0)) <> Some v) ->
  ev (henv lo hi E rs ts) v = edenot E (nth i rs (ELit 0)).
Proof.
  intros lo hi E rs. induction rs as [|r rs IH]; intros [|t ts] i v Hlen Hi Hv Hbefore; cbn [length] in *; try lia.
  cbn [henv]. destruct i as [|i]; cbn [nth] in *.
  - rewrite Hv. apply upd_at.
  - destruct (is_havoc lo hi t) as [v'|] eqn:Ht.
    + cbn [upd ev]. destruct (Nat.eqb_spec v v').
      * subst v'. exfalso. exact (Hbefore 0%nat ltac:(lia) Ht).
      * apply IH; [lia | lia | exact Hv |]. intros i' Hi'. exact (Hbefore (Datatypes.S i') ltac:(lia)).
    + apply IH; [lia | lia | exact Hv |]. intros i' Hi'. exact (Hbefore (Datatypes.S i') ltac:(lia)).
Qed.

#[using="Type"] Lemma regs_match_h_sound : forall lo hi E rs ts R,
  regs_match_h lo hi [] rs ts = true -> length ts = 32%nat -> regs_ok E rs R -> regs_ok (henv lo hi E rs ts) ts R.
Proof.
  intros lo hi E rs ts R H Hlen HR. destruct (regs_match_h_char lo hi [] rs ts H) as [Hl Hc].
  intros r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0; [exact (eq_trans (HR r) ltac:(unfold sr_get; rewrite Hr0; reflexivity))|].
  pose proof (ridx_range r) as Hlt. specialize (HR r). unfold sr_get in HR. rewrite Hr0 in HR. rewrite HR.
  destruct (Hc (ridx r) ltac:(lia)) as [[v (Hv & _ & Hbefore)]|(Hn & Heq & Hvl)].
  - destruct (is_havoc_range _ _ _ _ Hv) as [Et _]. rewrite Et. cbn [edenot]. symmetry. apply (henv_havoc lo hi E rs ts (ridx r) v Hl ltac:(lia) Hv Hbefore).
  - rewrite Heq in Hvl |- *. eapply (edenot_agree' lo); [apply henv_agree | exact Hvl].
Qed.

(* [comment removed for export] *)
#[using="argH_agree SINV_agree"] Lemma cs_ok_reenv : forall b E E' cs sr' R FULL model,
  cs_ok E cs R FULL model -> env_agree b E E' -> (nx0 <= b)%nat ->
  AP.kn_vars_lt b (kn cs) = true -> maps_vars_lt b (a_maps cs) = true -> pairs_vars_lt b (a_vis cs ++ a_ghost cs) = true ->
  AP.expr_vars_lt b (a_brk cs) = true -> fd_vars_lt b (a_fd cs) = true ->
  regs_ok E' sr' R ->
  cs_ok E' (set_regs cs sr') R FULL model.
Proof.
  intros b E E' cs sr' R FULL model HC Hag Hb Hkn Hmaps Hallow Hbrk Hfd HR.
  pose proof (hid_agree b E E' cs model Hag Hb Hallow) as HH.
  rewrite <- (hid_ext E' cs (set_regs cs sr') model eq_refl) in HH.
  pose proof (allowA_agree b E E' cs Hag Hallow) as HA.
  assert (HA2 : allowA E' (set_regs cs sr') = allowA E' cs) by reflexivity. rewrite <- HA2 in HA. clear HA2.
  destruct HC; constructor; cbn [set_regs with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset] in *;
    rewrite ?HA; try assumption; try reflexivity.
  - unfold Mr in *. rewrite HH. eapply know_ok_agree'; eassumption.
  - eapply fds_ok_agree; eassumption.
  - eapply maps_match_agree; [exact Hag | exact Hmaps | assumption].
  - eapply holes_agree; [exact Hag | exact Hmaps | assumption].
  - apply Forall_forall. intros m Hin Hk.
    pose proof (proj1 (forallb_forall _ _) Hmaps m Hin) as Hm. apply andb_prop in Hm as [H1 H2].
    unfold amap_den. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2).
    exact (proj1 (Forall_forall _ _) co_none0 m Hin Hk).
  - apply Forall_forall. intros m Hin Hk a Ha.
    pose proof (proj1 (forallb_forall _ _) Hmaps m Hin) as Hm. apply andb_prop in Hm as [H1 H2].
    rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2) in Ha.
    exact (proj1 (Forall_forall _ _) co_kinds0 m Hin Hk a Ha).
  - rewrite <- (edenot_agree' b E E' _ Hag Hbrk). assumption.
  - intros a. rewrite HH. change (in_ghost E' (set_regs cs sr')) with (in_ghost E' cs). rewrite (in_ghost_agree b E E' cs Hag Hallow). exact (co_zero0 a).
  - eapply SINV_agree; [eapply env_agree_le; [exact Hag | exact Hb] | assumption].
Qed.

#[using="SEGS_in_hull HULL_ok argH_agree SINV_agree"] Lemma entails_h_sound : forall lo hi E cs T R FULL model,
  cs_ok E cs R FULL model -> entails_h A lo hi cs T = true -> (nx0 <= lo)%nat -> length (s_regs (a_ss T)) = 32%nat ->
  exists E', env_agree lo E E' /\ (forall n, (hi <= n)%nat -> ev E' n = ev E n) /\ cs_ok E' T R FULL model /\ pc T = pc cs.
Proof.
  intros lo hi E cs T R FULL model HC H Hlo Hlen. unfold entails_h in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  rename H into Hpc. apply Z.eqb_eq in Hpc.
  match goal with Hl : match s_log (a_ss T) with _ => _ end = true |- _ => rename Hl into HL; destruct (s_log (a_ss T)) eqn:HL'; [clear HL; rename HL' into HL|discriminate] end.
  match goal with Hl : match s_resv (a_ss T) with _ => _ end = true |- _ => rename Hl into HRV; destruct (s_resv (a_ss T)) eqn:HRV'; [discriminate|clear HRV; rename HRV' into HRV] end.
  match goal with Hr : regs_match_h _ _ _ _ _ = true |- _ => rename Hr into Hregs end.
  match goal with Hm : list_eqb amap_eqb _ _ = true |- _ => apply (list_eqb_eq amap_eqb amap_eqb_eq) in Hm; rename Hm into Hmaps end.
  match goal with Ha : list_eqb pair_eqb (a_vis cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Ha; rename Ha into Hallow end.
  match goal with Hg : list_eqb pair_eqb (a_ghost cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hg; rename Hg into Hghost end.
  match goal with Hb : expr_eqb (a_brk cs) _ = true |- _ => apply expr_eqb_eq in Hb; rename Hb into Hbrk end.
  match goal with Hf : afd_eqb _ _ = true |- _ => apply afd_eqb_eq in Hf; rename Hf into Hfd end.
  match goal with Ht : Bool.eqb _ _ = true |- _ => apply eqb_prop in Ht; rename Ht into Htid end.
  match goal with Hk : kn_incl_h _ _ (kn T) = true |- _ => rename Hk into Hkn end.
  repeat match goal with Hz : Z.leb _ _ = true |- _ => apply Z.leb_le in Hz end.
  set (E' := henv lo hi E (s_regs (a_ss cs)) (s_regs (a_ss T))).
  exists E'. split; [apply henv_agree|]. split; [intros; apply henv_high; assumption|]. split; [|symmetry; exact Hpc].
  (* [comment removed for export] *)
  set (Tc := set_regs T (s_regs (a_ss cs))).
  assert (Evis : a_vis Tc = a_vis cs) by (unfold Tc; cbn [set_regs with_ss a_vis]; symmetry; exact Hallow).
  assert (HA : allowA E Tc = allowA E cs) by (unfold allowA; unfold Tc; cbn [set_regs with_ss a_vis a_ghost]; rewrite Hallow, Hghost; reflexivity).
  assert (HH : hid E Tc model = hid E cs model) by (apply hid_ext; exact Evis).
  assert (HC1 : cs_ok E Tc R FULL model).
  { destruct HC; constructor; rewrite ?HA;
      try (unfold Tc; cbn [set_regs with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset];
           rewrite <- ?Hmaps, <- ?Hallow, <- ?Hghost, <- ?Hbrk, <- ?Hfd, <- ?Htid; first [assumption | reflexivity | lia]).
    - unfold Mr. rewrite HH. eapply kn_incl_h_sound; [exact co_know0 | exact Hkn].
    - unfold Tc. cbn [set_regs with_ss a_maps a_ylo]. rewrite <- Hmaps. eapply holes_mono; [exact co_holes0 | lia].
    - destruct co_split0 as [Y HY]. exists Y. split; [unfold Tc; cbn [set_regs with_ss a_ylo]; lia | apply HY].
    - intros a. rewrite HH. replace (in_ghost E Tc) with (in_ghost E cs) by (unfold in_ghost, Tc; cbn [set_regs with_ss a_ghost]; rewrite Hghost; reflexivity).
      exact (co_zero0 a). }
  (* [comment removed for export] *)
  assert (ET : T = set_regs Tc (s_regs (a_ss T))).
  { subst Tc. clear - HL HRV. destruct T as [[p sr lg k nx rv] m t y e v g ab br f ti]. cbn in HL, HRV. subst lg rv. reflexivity. }
  rewrite ET at 1. eapply (cs_ok_reenv lo); try eassumption.
  - apply henv_agree.
  - unfold pairs_vars_lt, Tc. cbn [set_regs with_ss a_vis a_ghost]. rewrite forallb_app. apply andb_true_intro; split; assumption.
  - apply regs_match_h_sound; [exact Hregs | exact Hlen | exact (co_regs _ _ _ _ _ HC)].
Qed.

(* [comment removed for export] *)
#[using="SEGS_in_hull HULL_ok argH_agree SINV_agree"] Lemma diamond_join_sound : forall nx joinpc rs ca cb csj,
  node_diamond_join A nx0 nx joinpc rs ca cb = Some csj ->
  (forall E R FULL model, cs_ok E ca R FULL model ->
     exists E', (env_agree nx0 E E' /\ env_agree nx E E') /\ cs_ok E' csj R FULL model /\ pc csj = pc ca)
  /\ (forall E R FULL model, cs_ok E cb R FULL model ->
     exists E', (env_agree nx0 E E' /\ env_agree nx E E') /\ cs_ok E' csj R FULL model /\ pc csj = pc cb).
Proof.
  intros nx joinpc rs ca cb csj H. unfold node_diamond_join in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-.
  repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
  match goal with Hl : Nat.eqb (length ?l) 32 = true |- _ => apply Nat.eqb_eq in Hl; rename Hl into Hlen end.
  match goal with Hl : Nat.leb nx0 ?v = true |- _ => apply Nat.leb_le in Hl; rename Hl into Hn0 end.
  split; intros E R FULL model HC.
  - match goal with Hea : entails_h A ?lo ?hi ca ?T = true |- _ =>
      destruct (entails_h_sound lo hi E ca T R FULL model HC Hea Hn0 Hlen) as (E' & Hag & _ & HC' & Hpc) end.
    exists E'. split; [split; eapply env_agree_le; [exact Hag | lia | exact Hag | lia] | split; [exact HC' | exact Hpc]].
  - match goal with Hea : entails_h A ?lo ?hi cb ?T = true |- _ =>
      destruct (entails_h_sound lo hi E cb T R FULL model HC Hea Hn0 Hlen) as (E' & Hag & _ & HC' & Hpc) end.
    exists E'. split; [split; eapply env_agree_le; [exact Hag | lia | exact Hag | lia] | split; [exact HC' | exact Hpc]].
Qed.

#[using="Type"] Lemma loop_ok_facts : forall cs J N inv nhi,
  loop_ok nx0 cs J N inv = Some nhi ->
  fresh_ok nx0 cs = true /\ (nxt cs <= J)%nat /\ (J < nxt inv)%nat /\ s_log (a_ss inv) = [] /\
  length (s_regs (a_ss inv)) = 32%nat /\ AP.expr_vars_lt (nxt cs) N = true /\
  xhi (kn cs) N = Some nhi /\ nhi < two64.
Proof.
  intros cs J N inv nhi H. unfold loop_ok in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  destruct (xhi (kn cs) N) as [h|] eqn:Hx; [|discriminate]. destruct (Z.ltb h two64) eqn:Hlt; [|discriminate]. injection H as <-.
  apply Z.ltb_lt in Hlt.
  repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
  apply Nat.leb_le in X12. apply Nat.ltb_lt in X11.
  destruct (s_log (a_ss inv)); [|discriminate]. apply Nat.eqb_eq in X7.
  repeat split; try assumption; reflexivity.
Qed.

#[using="Type"] Lemma pc_inst : forall inv J e, pc (inst inv J e) = pc inv.
Proof. reflexivity. Qed.
#[using="Type"] Lemma nxt_inst : forall inv J e, nxt (inst inv J e) = nxt inv.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma check_all_ok : forall (chk : acs -> plan -> cres) k css s,
  check_all A rz chk k css = COk s ->
  (exists cs1, In cs1 css /\ chk cs1 k = COk s /\ True) /\ (forall cs, In cs css -> chk cs k = COk s).
Proof.
  intros chk k css s H. unfold check_all in H. destruct css as [|cs0 rest]; [discriminate|].
  destruct (chk cs0 k) as [s0|] eqn:H0; [|discriminate].
  match type of H with fold_left ?F rest (COk s0) = _ =>
  assert (GEN : forall l acc, fold_left F l acc = COk s ->
                 acc = COk s /\ forall cs, In cs l -> chk cs k = COk s) end.
  { induction l as [|c l IHl]; intros acc Hf; cbn [fold_left] in Hf.
    - split; [exact Hf | intros ? []].
    - destruct acc as [s1|c1 q1 r1].
      + destruct (chk c k) as [s'|] eqn:Hc'; [| apply IHl in Hf as [Hf _]; discriminate].
        destruct (shape_eqb s1 s') eqn:Hse; [| apply IHl in Hf as [Hf _]; discriminate].
        apply IHl in Hf as [E1 Hl]. injection E1 as ->. apply shape_eqb_eq in Hse. subst s'.
        split; [reflexivity|]. intros cs [<-|Hin]; [exact Hc' | apply Hl; exact Hin].
      + apply IHl in Hf as [Hf _]. discriminate. }
  apply GEN in H as [E0 Hrest]. injection E0 as ->.
  split; [exists cs0; split; [left; reflexivity | split; [exact H0 | exact I]]|].
  intros cs [<-|Hin]; [exact H0 | apply Hrest; exact Hin].
Qed.

#[using="Type"] Lemma check_vars : forall bfuel fuel lc p cs s,
  CHECK bfuel fuel lc cs p = COk s -> shape_vars_lt nx0 s = true.
Proof.
  intros bfuel fuel. induction fuel as [|fuel IH]; intros lc p cs s Hc; [discriminate|].
  cbn [AP.check] in Hc.
  match type of Hc with (if ?g then _ else _) = _ => destruct g; [discriminate|] end.
  destruct p as [stops k|e mid k1 k2|ce cmid ck1 ck2|db1 db2 dk1 dk2|sb1 sn1 sb2 sn2 k| |K k|jb joff jn k|ixs k|db dn k|gws k|bm k|hrs k|hbK k|r logc fb k|y k|ma mb|ia ib ic|qa qb|ka kb|x args k|xid xargs k|eid eargs k|bid bargs kb1 kb2|lJ lN linv lbody lk| |h| | |fi fsz fk|gi gsz gk|gb gn gk2|ub un uk|hlo hhi hk|ilo ihi ik|djp drs dk|rnm rnk|cpk|vj vjs vlo vka vk|mj|ab an ak|hws hwk|rsr rse rsk|iha ihb ihc].
  - destruct (run_block_gc SEGS IT _ KC bfuel (stops ++ STOPS A) cs) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (AP.expr_vars_lt nx0 e) eqn:Hv; [|discriminate].
    destruct (erange (kn cs) e) as [[lo hi]|]; [|discriminate].
    destruct (Z.leb lo mid && Z.ltb mid hi)%bool.
    2: { destruct (Z.leb hi mid); [exact (IH _ k1 _ s Hc) | exact (IH _ k2 _ s Hc)]. }
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange e lo mid :: kn cs)) k1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange e (mid+1) hi :: kn cs)) k2) as [s2|] eqn:H2; [|discriminate].
    injection Hc as <-. cbn [shape_vars_lt]. rewrite Hv, (IH _ k1 _ s1 H1), (IH _ k2 _ s2 H2). reflexivity.
  - destruct (erange (kn cs) ce) as [[lo hi]|]; [|discriminate].
    destruct (Z.leb lo cmid && Z.ltb cmid hi)%bool.
    2: { cbn [negb] in Hc. destruct (Z.leb hi cmid); [exact (IH _ ck1 _ s Hc) | exact (IH _ ck2 _ s Hc)]. }
    cbn [negb] in Hc. cbv zeta in Hc.
    destruct (kn_contra (kn (set_kn cs (KRange ce lo cmid :: kn cs)))); [exact (IH _ ck2 _ s Hc)|].
    destruct (kn_contra (kn (set_kn cs (KRange ce (cmid + 1) hi :: kn cs)))); [exact (IH _ ck1 _ s Hc)|].
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange ce lo cmid :: kn cs)) ck1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange ce (cmid+1) hi :: kn cs)) ck2) as [s2|] eqn:H2; [|discriminate].
    destruct (shape_eqb s1 s2); [|discriminate]. injection Hc as <-. exact (IH _ ck1 _ s1 H1).
  - destruct (node_casedisj cs db1 db2) as [[csa csb]|]; [|discriminate].
    destruct (CHECK bfuel fuel lc csa dk1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb dk2) as [s2|] eqn:H2; [|discriminate].
    destruct (shape_eqb s1 s2); [|discriminate]. injection Hc as <-. exact (IH _ dk1 _ s1 H1).
  - destruct (node_shdisj A cs sb1 sn1 sb2 sn2) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (kn_contra (kn cs)); [|discriminate]. injection Hc as <-. reflexivity.
  - destruct (fact_ok (kn cs) K); [|discriminate]. exact (IH _ k _ s Hc).
  - destruct (node_join SEGS cs jb joff jn) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - exact (IH _ k _ s Hc).
  - exact (IH _ k _ s Hc).
  - exact (IH _ k _ s Hc).
  - destruct (node_bump cs bm) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (node_havoc nx0 cs hrs) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (node_havocbig nx0 cs hbK) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (node_fresh nx0 cs r logc fb) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_sys A nx0 y cs) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_mmap2 A nx0 LIMIT cs) as [[csa csb]|]; [|discriminate].
    destruct (CHECK bfuel fuel lc csa ma) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb mb) as [sb|] eqn:H2; [|discriminate].
    injection Hc as <-. apply salt2_vars; [exact (IH _ ma _ sa H1) | exact (IH _ mb _ sb H2)].
  - destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_mmapin A LIMIT false cs) as [[[csa csb] cscs]|]; [|discriminate].
    destruct (CHECK bfuel fuel lc csa ia) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb ib) as [sb|] eqn:H2; [|discriminate].
    destruct (check_all A rz (CHECK bfuel fuel lc) ic cscs) as [sc|] eqn:H3; [|discriminate].
    injection Hc as <-.
    destruct (check_all_ok _ _ _ _ H3) as [(cs1 & Hin1 & Hc1 & _) _].
    apply salt2_vars; [exact (IH _ ia _ sa H1) | apply salt2_vars; [exact (IH _ ib _ sb H2) | exact (IH _ ic _ sc Hc1)]].
  - destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_mprotect2 A LIMIT cs) as [[csa csb]|]; [|discriminate].
    destruct (CHECK bfuel fuel lc csa qa) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb qb) as [sb|] eqn:H2; [|discriminate].
    injection Hc as <-. apply salt2_vars; [exact (IH _ qa _ sa H1) | exact (IH _ qb _ sb H2)].
  - destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_brk2 A LIMIT cs) as [[csa csb]|]; [|discriminate].
    destruct (CHECK bfuel fuel lc csa ka) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb kb) as [sb|] eqn:H2; [|discriminate].
    injection Hc as <-. apply salt2_vars; [exact (IH _ ka _ sa H1) | exact (IH _ kb _ sb H2)].
  - destruct (XON x); [|discriminate]. destruct (node_x SEGS A nx0 rz x args cs) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (XN xid xargs cs) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
  - destruct (XE eid eargs cs) as [[[fd ps] cs1]|]; [|discriminate].
    destruct (CHECK bfuel fuel lc cs1 k) as [s1|] eqn:H1; [|discriminate].
    injection Hc as <-. cbn [shape_vars_lt]. exact (IH _ k cs1 s1 H1).
  - destruct (XB bid bargs cs) as [[csa csb]|]; [|discriminate].
    destruct (CHECK bfuel fuel lc csa kb1) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb kb2) as [sb|] eqn:H2; [|discriminate].
    injection Hc as <-. cbn [shape_vars_lt]. rewrite (IH _ kb1 _ sa H1), (IH _ kb2 _ sb H2). reflexivity.
  - destruct (loop_ok nx0 cs lJ lN linv) as [nhi|]; [|discriminate].
    destruct (Z.eqb (pc linv) (pc cs) && entails_h A (Datatypes.S lJ) (nxt linv) cs (inst linv lJ (ELit 0)))%bool; [|discriminate].
    destruct (CHECK bfuel fuel (Some (LC (pc cs) (inst linv lJ (eaddz (EVar lJ) 1)) (Datatypes.S lJ) (nxt linv))) (loop_body_state lJ lN nhi linv) lbody) as [sb|]; [|discriminate].
    destruct sb; try discriminate. exact (IH _ lk _ s Hc).
  - destruct lc as [[h nx lo hi|j' js' sk' b' lo']|]; [|discriminate|discriminate].
    destruct (Z.eqb (pc cs) h && entails_h A lo hi cs nx)%bool; [|discriminate]. injection Hc as <-. reflexivity.
  - destruct (HS h) as [ch|]; [|discriminate]. destruct (entails cs ch); [|discriminate]. injection Hc as <-. reflexivity.
  - destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_exit cs); [|discriminate]. injection Hc as <-. reflexivity.
  - discriminate.
  - destruct (node_fog cs fi fsz) as [cs1|]; [|discriminate]. exact (IH _ fk cs1 s Hc).
  - destruct (node_fognew cs gi gsz) as [cs1|]; [|discriminate]. exact (IH _ gk cs1 s Hc).
  - destruct (node_ghost LIMIT cs gb gn) as [cs1|]; [|discriminate]. exact (IH _ gk2 cs1 s Hc).
  - destruct (node_unvis A cs ub un) as [cs1|]; [|discriminate]. exact (IH _ uk cs1 s Hc).
  - destruct (node_havocbrk nx0 cs hlo hhi) as [cs1|]; [|discriminate]. exact (IH _ hk cs1 s Hc).
  - destruct (node_intro nx0 cs ilo ihi) as [cs1|]; [|discriminate]. exact (IH _ ik cs1 s Hc).
  - destruct (branch_probe IT cs) as [e|]; [|discriminate].
    destruct (erange (kn cs) e) as [[lo hi]|]; [|discriminate].
    destruct (Z.ltb hi 1 || Z.ltb 0 lo)%bool.
    { destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) cs) as [cs1|]; [|discriminate].
      destruct (Z.eqb (pc cs1) djp); [|discriminate]. exact (IH _ dk cs1 s Hc). }
    cbv zeta in Hc.
    destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) (set_kn cs (KRange e lo 0 :: kn cs))) as [ca|]; [|discriminate].
    destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) (set_kn cs (KRange e 1 hi :: kn cs))) as [cb|]; [|discriminate].
    destruct (node_diamond_join A nx0 (nxt cs) djp drs ca cb) as [csj|]; [|discriminate]. exact (IH _ dk csj s Hc).
  - destruct (node_rename _ cs rnm) as [cs1|]; [|discriminate]. exact (IH _ rnk cs1 s Hc).
  - destruct (node_compact _ cs) as [cs1|]; [|discriminate]. exact (IH _ cpk cs1 s Hc).
  - destruct (via_ok nx0 cs vjs vlo); [|discriminate].
    destruct (CHECK bfuel fuel lc vjs vk) as [sk|]; [|discriminate]. exact (IH _ vka _ s Hc).
  - destruct lc as [[h nx lo hi|j' js' sk' b' lo']|]; [discriminate| |discriminate].
    destruct (Nat.eqb mj j' && Z.eqb (pc cs) (pc js') && shape_vars_lt nx0 sk' && entails_h A lo' (nxt js') cs js')%bool eqn:Ht; [|discriminate].
    injection Hc as <-. apply andb_prop in Ht as [Ht _]. apply andb_prop in Ht as [_ Hsv]. exact Hsv.
  - destruct (node_abstractcell A cs ab an) as [cs1|]; [|discriminate]. exact (IH _ ak cs1 s Hc).
  - destruct (node_havocwords nx0 cs hws) as [cs1|]; [|discriminate]. exact (IH _ hwk cs1 s Hc).
  - destruct (node_respell cs rsr rse) as [cs1|]; [|discriminate]. exact (IH _ rsk cs1 s Hc).
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_mmapin A LIMIT true cs) as [[[csa csb] cscs]|]; [|discriminate].
    destruct (CHECK bfuel fuel lc csa iha) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb ihb) as [sb|] eqn:H2; [|discriminate].
    destruct (check_all A rz (CHECK bfuel fuel lc) ihc cscs) as [sc|] eqn:H3; [|discriminate].
    injection Hc as <-.
    destruct (check_all_ok _ _ _ _ H3) as [(cs1 & Hin1 & Hc1 & _) _].
    apply salt2_vars; [exact (IH _ iha _ sa H1) | apply salt2_vars; [exact (IH _ ihb _ sb H2) | exact (IH _ ihc _ sc Hc1)]].
Qed.

(* [comment removed for export] *)
Lemma list_set_nth_maps_match : forall E ms l i m sz,
  nth_error ms i = Some m -> is_fog m = false -> 0 <= sz < two64 ->
  bv_unsigned (edenot E (am_len m)) <= sz ->
  maps_match E ms l -> maps_match E (list_set_nth i (fog_token sz) ms) l.
Proof.
  intros E ms. induction ms as [|m0 ms IH]; intros l i m sz Hn Hf Hsz Hle HM; [destruct i; discriminate|].
  destruct i as [|i]; cbn [nth_error] in Hn; cbn [list_set_nth maps_match] in *.
  - injection Hn as ->. rewrite Hf in HM. destruct HM as (l' & -> & HM).
    unfold fog_token, is_fog. cbn [am_kind am_len mkind_eqb]. right. exists (amap_den E m), l'.
    split; [reflexivity|]. split; [|exact HM]. unfold uE, amap_den. cbn [snd edenot]. rewrite u64_lit by (unfold two64 in Hsz; lia). exact Hle.
  - destruct (is_fog m0).
    + destruct HM as [HM|(iv & l' & -> & Hs & HM)]; [left; eapply IH; eassumption | right].
      exists iv, l'. split; [reflexivity|]. split; [exact Hs | eapply IH; eassumption].
    + destruct HM as (l' & -> & HM). exists l'. split; [reflexivity | eapply IH; eassumption].
Qed.

#[using="Type"] Lemma list_insert_nth_maps_match : forall E ms l i sz,
  maps_match E ms l -> maps_match E (list_insert_nth i (fog_token sz) ms) l.
Proof.
  intros E ms. induction ms as [|m0 ms IH]; intros l i sz HM.
  - destruct i; cbn [list_insert_nth maps_match]; unfold fog_token, is_fog; cbn [am_kind mkind_eqb]; left; exact HM.
  - destruct i as [|i]; cbn [list_insert_nth].
    + cbn [maps_match]. unfold fog_token at 1. unfold is_fog at 1. cbn [am_kind mkind_eqb]. left. exact HM.
    + cbn [maps_match] in *. destruct (is_fog m0).
      * destruct HM as [HM|(iv & l' & -> & Hs & HM)]; [left; apply IH; exact HM | right].
        exists iv, l'. split; [reflexivity|]. split; [exact Hs | apply IH; exact HM].
      * destruct HM as (l' & -> & HM). exists l'. split; [reflexivity | apply IH; exact HM].
Qed.

#[using="Type"] Lemma In_list_set_nth : forall {T} (l : list T) i x y, In y (list_set_nth i x l) -> y = x \/ In y l.
Proof.
  intros T l. induction l as [|a l IH]; intros i x y H; [destruct i; cbn in H; destruct H|].
  destruct i; cbn in H; destruct H as [H|H]; try (right; left; exact H); try (left; symmetry; exact H).
  - right. right. exact H.
  - destruct (IH _ _ _ H) as [->|H']; [left; reflexivity | right; right; exact H'].
Qed.
#[using="Type"] Lemma In_list_insert_nth : forall {T} (l : list T) i x y, In y (list_insert_nth i x l) -> y = x \/ In y l.
Proof.
  intros T l. induction l as [|a l IH]; intros i x y H.
  - destruct i; cbn in H; destruct H as [H|[]]; left; symmetry; exact H.
  - destruct i; cbn in H; destruct H as [H|H]; try (left; symmetry; exact H); try (right; left; exact H).
    + right. exact H.
    + destruct (IH _ _ _ H) as [->|H']; [left; reflexivity | right; right; exact H'].
Qed.

#[using="Type"] Lemma cs_ok_with_maps : forall E cs R FULL model ms',
  cs_ok E cs R FULL model ->
  maps_match E ms' (vm_maps (m_vmmaps model)) ->
  (forall m, In m ms' -> m = fog_token (match am_len m with ELit z => z | _ => 0 end) \/ In m (a_maps cs)) ->
  cs_ok E (with_maps cs ms') R FULL model.
Proof.
  intros E cs R FULL model ms' HC HM Hsub.
  assert (HMr : Mr E (with_maps cs ms') model FULL = Mr E cs model FULL) by reflexivity.
  assert (HA : allowA E (with_maps cs ms') = allowA E cs) by reflexivity.
  destruct HC; constructor; unfold with_maps; rewrite ?HMr, ?HA;
    cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn] in *; try assumption.
  - (* [comment removed for export] *) apply Forall_forall. intros m Hin Hk. destruct (Hsub m Hin) as [Hm|Hm].
    + rewrite Hm in Hk. cbn in Hk. discriminate.
    + exact (proj1 (Forall_forall _ _) co_holes0 m Hm Hk).
  - (* [comment removed for export] *) apply Forall_forall. intros m Hin Hk. destruct (Hsub m Hin) as [Hm|Hm].
    + rewrite Hm in Hk. cbn in Hk. destruct Hk; discriminate.
    + exact (proj1 (Forall_forall _ _) co_none0 m Hm Hk).
  - (* [comment removed for export] *) apply Forall_forall. intros m Hin Hk. destruct (Hsub m Hin) as [Hm|Hm].
    + rewrite Hm in Hk. cbn in Hk. discriminate.
    + exact (proj1 (Forall_forall _ _) co_kinds0 m Hm Hk).
Qed.

#[using="Type"] Lemma fog_sound : forall E cs R FULL model i sz cs',
  cs_ok E cs R FULL model -> node_fog cs i sz = Some cs' -> cs_ok E cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros E cs R FULL model i sz cs' HC H. unfold node_fog in H.
  destruct (nth_error (a_maps cs) i) as [m|] eqn:Hn; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-. split; [|reflexivity].
  apply andb_prop in Hc as [Hc Hx]. apply andb_prop in Hc as [Hc Hs2]. apply andb_prop in Hc as [Hnf Hs1].
  apply negb_true_iff in Hnf. apply Z.leb_le in Hs1. apply Z.ltb_lt in Hs2.
  destruct (xhi (kn cs) (am_len m)) as [h|] eqn:Hh; [|discriminate]. apply Z.leb_le in Hx.
  pose proof (xhi_sound SEGS E _ (kn cs) (am_len m) h (co_know _ _ _ _ _ HC) Hh) as Hh'.
  apply cs_ok_with_maps; [exact HC | |].
  - eapply list_set_nth_maps_match; [exact Hn | exact Hnf | lia | lia | exact (co_maps _ _ _ _ _ HC)].
  - intros m' Hin. destruct (In_list_set_nth _ _ _ _ Hin) as [->|Hin']; [left; reflexivity | right; exact Hin'].
Qed.

#[using="Type"] Lemma fognew_sound : forall E cs R FULL model i sz cs',
  cs_ok E cs R FULL model -> node_fognew cs i sz = Some cs' -> cs_ok E cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros E cs R FULL model i sz cs' HC H. unfold node_fognew in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-. split; [|reflexivity].
  apply cs_ok_with_maps; [exact HC | apply list_insert_nth_maps_match; exact (co_maps _ _ _ _ _ HC) |].
  intros m' Hin. destruct (In_list_insert_nth _ _ _ _ Hin) as [->|Hin']; [left; reflexivity | right; exact Hin'].
Qed.

#[using="Type"] Lemma page_allowedb_app_l : forall l1 l2 p, page_allowedb l1 p = true -> page_allowedb (l1 ++ l2) p = true.
Proof. intros. unfold page_allowedb in *. rewrite existsb_app, H. reflexivity. Qed.
#[using="Type"] Lemma MInv_app_r : forall l1 l2 m, MInv l1 m -> eager_used m + A_bytes (l1 ++ l2) <= vm_limit (m_vmmaps m) -> MInv (l1 ++ l2) m.
Proof.
  intros l1 l2 m [N1 N2 N3 N4 N5] Hb. constructor; try assumption.
  intros p Hp. apply page_allowedb_app_l. apply N3. exact Hp.
Qed.
#[using="HS XN XE XB SHADOW_ok KC"] Lemma allow1_cost : forall E b n nhi, bv_unsigned (edenot E n) <= nhi -> A_bytes (allow1 E (b, n)) <= vis_cost nhi.
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
ltac2:(KReplay.run1 (kr_t_AsanPlanSound ()) ["FPX_3"; "Sound"] "h04__p1h14__x1h24__x2h34__x3h44__x4h54__x5h64__x6h74__x7h82Hah97__arithh:4__ffh;4__p2h<6__sat4h=8__varmaph>5__with?4__x8h@4__x9hA6__sat2hB6__sat3hC6__sat5hD6__sat6hE6__sat7hF1HhG2H0hH2H1hI3H10hJ3H11hK3H12hL2H2hM2H3hN2H4hO2H5hP2H6hQ2H7hR2H8hS2H9hT4__p3hU6__sat8hV6__sat9hW5__x10hX5__x11hY1qhZ2q0h[1rh\2r0h]1Eh^2G1h_2G2h`2G3ha3H13hb3H14hc3H15hd3H16he3H17hf2Hnhg2Rbhh2Rnhi2Sohj6__sat0hk6__sat1hl7__sat10hm1bhn1nho3nhihp2q1hq2r1p%0p&0p;1p;2p;3p;4p;6p;7p;8p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0p10038p4p710R5p9P0p1003Vp4p710R6p9P0p1004Np4p710R7p8P0p1004ep4p710p8P0g005FR8p4p710p8P0P8p4p7210p8P0p1005cp4p710R0p8p100_Jp4p70R9g00O0R:p4p710R;p8P9P1p8P9P2p8P9p10079p4p710R<p8P9P4p8P9P3p4p710R3p8P9P6p8p1006?p4p710P5p8p100`:p4p70R9P;p8P9P1p8P9P2p8P9p100`hR=p4p7210R>p8P9P<p8P9P4p8P9P3p8P9P5p8P9P6p8p100aDp4p70P<p8p100bCp4p7210R9P1p8P9P2p8P9P<p8P9P4p8P9P3p8P9P6p8p1062Tp6051000R9P5p8P9p103VIp4p710R?p8P9p1063Vp4p710p8p106kQp6051000R9P7p8P9P5p8P9P?p8P9P0p8p107<2p6051000R9P7p8P9P?p8P9P0p8p100bop4p70R9P1p8P9P2p8P9P4p8P9P3p8P9P6p8p1006\p4p7210R6P<p8P6P5p8p1007Up4p7210P5p8p10082p4p73110P5p8p10<9lR6p60521000R<P>p8P<P0p8P6p6051001R6P=p4p710p8P6P?p8P6P0p8p10>VRp6051000R0P;p8P0P7p8P0P5p8P0P?p8P0p10>WXp4p710p8p10>Xbp6051000R0P;p8P0P7p8P0P5p8P0P?p8P0p10>Ykp4p710p8p100cep4p710P5p8g008Nj1;Tg00dlk10CTg00:Bj28Tg01=4j2gTg017fj1xTg00iHj2cTg0093j1JTg018]j2sTg00>Pj22Tg00JTj1CTg01>6j2{Tg01>^j3zTg00E?j1yTg00F?k10GTg00]4k10FTg00G[k10@Tg00H9k10>Tg00Hdj2_Tg00J2k107Tg00K9j2vTg00NNk201TP:k200Tg00OJj2~Tg00;\j3bTg00P6j3}Tg00PUk40JTg07FSj3|Tg00\7j1@Tg00QGj1>Tg01AFk10ITg009Qj2HTg00=Lj23Tg00:^j24Tg00;;j2^Tg00<6k10HTg00<Oj2ETg00<lj25Tg00=ij2\Tg00?Gj2[Tg00>lS00j2DTg00?nj2ZTg00@Tj2WTg00A:j1MTg00BBk10ETg00B`k20BTg00CAj3wTg01BIk20ATg00AYj2uTg01C2k30?Tg00DSj2mTg00E_j3]Tg00Ldk60=Tg00MHj3lTg00^3j3VTg00^Vj2dTg00kjj2TTg01Gmj4jTP8k30<Tg00j2k30;Tg01:6k208Tg019:k209Tg00emk20:Tg02mFj1rTg015ok206Tg07BKk105Tg00F_k204Tg00G=j4nTg00IGj4fTg00RFj7qTg00K\k603Tg00L@k70DTg00Mkk302Tg00Rjj8YTg00Cjj3pTf0R8#;#;p=`f2R:f1R5/g8'cp=0g00VPR0/85/D8p=?f3R?1g58,c:'3p=7%C8#Cp=a1808p=1g00UMR70048p=FP7P:P5P8Cnp=K1v78p=9P:g00SNR;g00SmR6P6g00TMR=P7P5g00YLR<P8Cfg00TmR>Fqp=:P5P;P6P6P=P8J03p=QP:P;P6P6P=P5P8K0Dp=LB02758p=6P7P5P<P8Cfp=of4R<P;P6P6P=P?P:P5P;P6P6P=P8P>FqGYp=h1358,8:p=P1d:5/38p=B1d:5/88p=I1458,3:p=GAb780p=R13589b7:p=<Ab758p=X1u78p=NAp758p=tAp7589p7:p=OP7P7P<P?P:CnP5P8Cnp=UP7P5g00XeP8Cfp=eP5P;P6P6P=P8P>Fqp==P7P5g00Z3P8Cfp=Sf6R>P;P6P6P=f5R9P<P?P;P6P6P=P:P5P8GYGYp=kP>P;P6P6P=P9P;P6P6P=P<P?P:GYP5P8GYp=A1258,D:p=ig00n`g01IER3g00UkR4#;R2#;R1#;S01#;#`S02$0CR@?0?5/881g<?RA#x1c@ARA%J2RBQ02#JRC'sRD,2A'?1g9?RA#x1c@ARA12AD'?p,9SHADOW_okg07[bf7RA=0@>REPEP@PAP9C7RF%C2S03#CS04#a#JRG,{BS05120BRH%1G1sBGRI,20[[S06%1BRJg0157RKAzBG5UW8S07%1I\K^8JS081{BCS09%1C120D[\HS0:AzBC5VKX8JS0;%1D\K^8JS0<p-0RJg00VnRK#yRC&0GKS0=%F:&0F7RB7K5&0@7S0>&0>7RH1_70RI%92R25:H1QH<5LH&076RGPH1v74RL16L2RM'oDh201H=S0?P8P:g00ZZRNg00[:RO+001~8:=bNOdA}705H0JS0@b:b=b>X17X27W01?5:AP55:[^17^27^0JP8f<ROf:RN50@RP/2DPPf;RQ90@ORRP>O4b9bjbkbAbB3|%@F%>E%C4RS#CS0A#C#a#a#a#a#;#JRT9BFE3Ip,1A$0IRFf8RE=0@ARUQ01#JRV3GRWPUP@PEP>C7=GFVRUQ05Q06Q07Q08f9RX90@NP@PNPEC7RY/HV%1Y%1VRY13RPS0B/4V#1[[Q09Q0:Q0;Q0<f=RR=0@OS0C/HVQ0C#1f?RPf>RZ50@R[/4VR\#1\Y[A0@ZRR]/^V%RVR^$0HR_1EV\15[V5<[[1\[V120VR\f@R`=0@PRa/5VRb12bV'?[1[aV12V0RbfARc=0@`Rd/5VRe,2V18e0'D[1ZdVfBRe=0@cRf/4VS0D#R\^1WfVfCRg=0@eRh/5V/Xh\^14hVP7fDRi=0@gS0E/5VP7fERj=0@iP@PjPgC7Rk/^VfFRl=0@jP@PlPiC7Rm14mV,EV15mVS0F3<\_1\mVfGRm=0@lS0GP@PmPjC7Rj/5VRn12nV'?\\1[jVfHRj=0@mRnP@PjPlC7Ro/5VRp,2V18p0'D\b1ZoVfIRo=0@jRpP@PoPmC7Rq/4V#R\^1WqVfJRq=0@oRrP@PqPjC7Rs/5V/Xs\^14sVP7fKRs=0@qRtP@PsPoC7/5VP7Q00fLRu=0@qRq#112qD13FX?PF:PlfNRq=0@u#1fORvfMRw50@/2DQ00fPRx=0@vRy#112yD13FR?PF>PsfRRyfQS0H50@#1fSS0I=0@y/2DPlP5O1%1cS0J\YS0Kg00WZRy#MS0L#MRz#MR{#MR|#MR}#MS0M#NS0N%N}S0O%N|S0P&0E4-0B7S0Q%N{S0R5w7%NzS0S20A7V1u7yS0T60?7S0U't3O3Og00X9S0V'm=]KCQ0=%F<P:%FAS0W?K9BP5%F>PAPBP?PBDUDUQ0>PHPH1_7VRy,eI,=HRzPG1QHXQ03#;#9R{/ey,=H5LHPGPHPHPHP;P6P6P=1SyI,=HJ0=R=PG%;SR6#9R;%91R|'6S0X%9SRS9l7yS0Y/6{'S,=HPGPHPHPzPG%C1#9R19:HI1QHN5LHPGPHPHP=PGAl7y2S0Z/61,S;,=HPGPHA:HI|PGPHA:HI;PG16LS9:HMFkFAFAFAFAQ0?Q0@b:b=b>X17X27X37X47X57X67X77X0JX;JAiEAV\\g00[Z\^RM13>91EV<S0[;<E[1?EQ\\1EV9S0\=<EX\M%1A%1X13>A?P>E[[[[[[^17^27^37^47^57^67^77^0J^;JP812cV%1NS0]PNPcfVR}fUR~50@fTS0^90@}PQPePFPPP`PlPmPAP?O?b9bAWKWJP5P8O2n2001000000121000000WIWSP5P8O2n2001000000121000000b\bZbRbQbPbObNb[bYbMbLbHbGbFbAbBb<bCbDbE3|%@U%>WABUWT3IQ05Q06Q07Q08A0@QNP@PQPXC7RU/HV%1UQ0CP@PRPQC7/4V#1\Y[Q09Q0:Q0;Q0<1H]V%1]14aV#1\Y[1HOV%1O14ZV#1\Y[PaP@P`PZC7/^VPdP@PcPPC7Ra14aV,EV15aV3<\_1\aVA0@e`Ra,3fRU/5VRW12WV'?\\1[UVPhP@PgPcC7Rg/5VRh,2V18h0'D\b1ZgVQ0EP@PiPeC7Rg/4V#R\^1WgV15kV/Xk\^14kVP7Q0FP7Q0G/^V14nV,EV15nV5<n\_1\nV15pVRn12nV'?\\1[pV15rVRp,2V18p0'D\b1ZrV14tV#R\^1WtVA0@usRt/5V/Xt\^14tVP7A0@wu/5VP71^sV14uV,EV15uV5<u\_1\uV15wVRu12uV'?\\1[wV15qVRu,2V18u0'D\b1ZqV14vV#R\^1WvV15xV/Xx\^14xVP7Q0H/5VP7Q00Q0I90@~Rx#112xD%J4R4,3:9I`XPvfW=0@~#1fXR~=0@}/2DQ00fY=0@~R~#112~D13>49IiRQ0^f[RifZ50@#1f\R~=0@i/2DPqP5O1Q0KQ0M#M#NQ0NQ0OQ0PQ0RQ0QQ0S5w7Q0L#NR}Q0U't3O3O3OQ0V'm=]KCQ0=Q0W9KB<P:%FXRv9KB>P5PBP9%FERxP?PBDUDUQ0>PHPHPzPG1QHQQ0A#;#9R^/ey,=H5LHPGPHPHP=PGQ03#9RbQ0Y/6^'S,=HPGPHPHPzPG1QHO%C6#9R^/ey,=H5LHPGPHPHP=PGQ0Z/6^,S;,=HPGPHPHPzPG%;6#9R69:HI1QHRRz5LHPGPHPHP=PGQ0XAl7yL/66'S,=HPGPHA:H|bPGPHAV7L2RL1_74R2,6S'oDhFAFAFAFAFAFAQ0?Q0@b:b=b>X17X27X37X47X57X67X77X?7X@7X0JX;JXTJAiNXV\\Q0[=<>N\MAiRNV\\Q0\=<XQ\M1?Q`\\13QX1EV>;<O\M18XN1dAERM?PX4[[[[[[[^17^27^37^47^57^67^77^?7^@7^0J^;J^TJP812jVQ0JQ0]PNPcPjf_Rjf^50@P~f]90@jPQPePoPPP`PlPmPwPqPiOCb9b<WeWdP5P8O2n2001000000121000000WcWbP5P8O2n2001000000121000000bqbpbabKbJbIbSb\bZbRbQbPbObNb[bYbMbLbHbGbFbBb<bCbDbEbUbVA0@XERiP@PXPAC7/4V14iV14>V/343IQ05Q06Q07Q08Q0B/HVQ0B#1P]P@PZPOC7/4V#1\Y[Q09Q0:Q0;Q0<1H[V%1[14dV#1\Y[1HRV%1R14PVRd#1\Y[Q0OQ0PQ0RQ0T7O}3OQ0V'm=]KCQ0=AKx<BP:%FN?K>BP5PvP9PBP?%FQ?KABDUDUQ0>PHQ04#9RB9V7{16;25:HPGPHAV7S|RS161{161B5V71_7TRB'65:HPGPHQ01#9R1Q0A#9R{'6=V71/6B9:HLPGPHA:HI1=LHzPGPHA:H{bPGPH16SI,6L16b;Q02#`#`#`#`#JRb,_7'6'oDhFkFkQ0?Q0@b:b=b>X17X27X37X47X57X67X77X?7X@7XW7XX7X0J13949IXN13XNR413XQ;BT9I?<13XE?BXT9I:?Q0]/DZ18NE13M09B9>?P4b[[[[[^17^27^37^47^57^67^77^?7^@7^W7^X7^0JP812fDQ0D14UVRDPFPfPaPdPPQ0D,3F#>13FD#@%>f%@UPEPXPNPRPZOAb9b<bCbDbEbUbVblb`b_b^bi1T>9R91T><'3R>#@%>9AGF>V#@AGF9V#>;B03BAG??V;Pbebhbg1T<?R91T<:'3#@%>9'dR9P3P3P?P:CjR::0<33,T<R?B0;33:,T<'3R>=GFV#@AGF?V#>;B0'3AG55V/3bRb'8e208<:#@RV209<:#>RF;B0,39/8be20:77R9P7P7%>?%@>CjP7P7PFPVCj%y95]93]#r/8be206<:#r&055'8eWfXo7Xn3WmW]o"). Qed.

#[using="HS XN XE XB SHADOW_ok KC"] Lemma ghost_sound : forall E cs R FULL model b n cs',
  cs_ok E cs R FULL model -> node_ghost LIMIT cs b n = Some cs' -> cs_ok E cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros E cs R FULL model b n cs' HC H. unfold node_ghost in H.
  destruct (xhi (kn cs) n) as [nhi|] eqn:Hx; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-. split; [|reflexivity].
  apply andb_prop in Hc as [Hc Hb]. apply Z.leb_le in Hb.
  pose proof (xhi_sound SEGS E _ (kn cs) n nhi (co_know _ _ _ _ _ HC) Hx) as Hn.
  set (cs' := ACS _ _ _ _ _ _ _ _ _ _ _).
  assert (HMr : Mr E cs' model FULL = Mr E cs model FULL) by reflexivity.
  assert (HA : allowA E cs' = allowA E cs ++ allow1 E (b, n)).
  { unfold allowA, cs'. cbn [a_vis a_ghost]. rewrite app_assoc, !flat_map_app. cbn [flat_map]. rewrite app_nil_r. reflexivity. }
  assert (HAB : A_bytes (allowA E cs') <= A_bytes (allowA E cs) + vis_cost nhi).
  { rewrite HA, A_bytes_app. pose proof (allow1_cost E b n nhi Hn). lia. }
  pose proof (co_limit _ _ _ _ _ HC) as HL. pose proof (co_eager _ _ _ _ _ HC) as HE. pose proof (co_abytes _ _ _ _ _ HC) as HAB0.
  destruct HC; constructor; unfold cs'; rewrite ?HMr;
    cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn] in *; try assumption.
  - fold cs'. lia.
  - fold cs'. rewrite HA. apply MInv_app_r; [exact co_minv0|]. rewrite <- HA. fold cs' in HAB. rewrite HL. lia.
  - intros a H1 H2 H3 H4 H5. apply (co_zero0 a H1 H2 H3 H4).
    unfold in_ghost in H5 |- *. cbn [a_ghost] in H5. rewrite existsb_app in H5. apply orb_false_iff in H5 as [H5 _]. exact H5.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma kzero_x_sound0 : forall E M allkn k b off n,
  know_ok SEGS E M allkn ->
  know_ok SEGS E M k -> kzero_x allkn k b off n = true ->
  (forall i, 0 <= i < elenZ E n -> M (Z_to_bv 64 (estart E (SA b off) + i)) = Some (Z_to_bv 8 0))
  /\ 0 <= estart E (SA b off) /\ estart E (SA b off) + elenZ E n <= 2 ^ 64.
Proof.
  intros E M allkn k b off n Hall HK H. induction k as [|K rest IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hrest].
  destruct K; try exact (IH Hrest H).
  lazymatch type of H with context [KZero ?za ?zl :: rest] => destruct za as [zb zk]; rename zl into zn end.
  cbn [kzero_x] in H.
  assert (H2w : forall c1 c2 : bool, (if c1 then true else if c2 then true else kzero_x allkn rest b off n) = true ->
                 (c1 || c2)%bool = true \/ kzero_x allkn rest b off n = true)
    by (intros [|] [|]; cbn; auto).
  apply H2w in H. destruct H as [H|H]; [|exact (IH Hrest H)].
  cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hz]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
  unfold estart in Hz, F1, F2, F4 |- *. cbn [a_base a_off] in Hz, F1, F2, F4 |- *.
  pose proof (u64_range (edenot E n)) as Hnr.
  assert (CORE : bv_unsigned (edenot E zb) + zk <= bv_unsigned (edenot E b) + off ->
                 bv_unsigned (edenot E b) + off + elenZ E n <= bv_unsigned (edenot E zb) + zk + elenZ E zn ->
                 (forall i, 0 <= i < elenZ E n -> M (Z_to_bv 64 (bv_unsigned (edenot E b) + off + i)) = Some (Z_to_bv 8 0))
                 /\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + elenZ E n <= 2 ^ 64).
  { intros A0 B0. split; [|unfold elenZ in *; lia]. intros i Hi.
    replace (bv_unsigned (edenot E b) + off + i) with (bv_unsigned (edenot E zb) + zk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E zb) + zk) + i)) by lia.
    apply Hz. lia. }
  apply orb_prop in H as [H|H].
  - destruct (expr_eqb b zb && Z.leb zk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
    apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst zb.
    destruct (xhi allkn n) as [nh|] eqn:Hxh; [|discriminate].
    destruct (xlo allkn zn) as [zl|] eqn:Hxl; [|discriminate]. apply Z.leb_le in H.
    pose proof (xhi_sound SEGS E M allkn n nh Hall Hxh). pose proof (xlo_sound SEGS E M allkn zn zl Hall Hxl).
    apply CORE; unfold elenZ in *; lia.
  - pose proof (xinside_sound SEGS E M allkn b off n zb zk zn Hall H) as [A0 B0].
    unfold estart in A0, B0. cbn [a_base a_off] in A0, B0. apply CORE; lia.
Qed.

#[using="Type"] Lemma A_bytes_fm_split : forall E (f : expr * expr -> bool) l,
  A_bytes (flat_map (allow1 E) l)
  = A_bytes (flat_map (allow1 E) (List.filter f l)) + A_bytes (flat_map (allow1 E) (List.filter (fun p => negb (f p)) l)).
Proof.
  intros E f l. induction l as [|p l IH]; cbn [flat_map List.filter]; [reflexivity|].
  rewrite A_bytes_app, IH. destruct (f p); cbn [negb flat_map]; rewrite ?A_bytes_app; lia.
Qed.

#[using="Type"] Lemma A_bytes_allow1_nonneg : forall E p, 0 <= A_bytes (allow1 E p).
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
ltac2:(KReplay.run1 (kr_t_AsanPlanSound ()) ["FPX_3"; "Sound"] "h02H3h12Hah24__x1h35__x10h45__x11h54__x2h64__x3h74__x4h84__x5h94__x6h:4__x7h;4__x8h<4__x9h=1Eh>1Hh?2H0h@2H1hA3H10hB3H11hC3H12hD3H13hE3H14hF2H2hG2H4hH2H5hI2H6hJ2H7hK2H8hL2H9hM7__arithhN4__ffhO6__sat4hP6__sat5hQ6__sat6hR6__sat7hS8__varmaphT5__withU1phV1qhW2q0hX1rhY2r0p&0p;2p;1p;3p;6p;4p;7p;8p-1R0p10000p4p710R1p9P0p1000Sp4p710R2p9P0p1001?R3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0p1001]R3p4p7210R4p9P0p1002Qp4p710p9P0p10038p4p710R5p9P0p1003Vp4p710R6p9P0p1004Np4p710R7p8P0p1004ep4p710p8P0g005FR8p4p710p8P0P8p4p7210p8P0p1005cp4p710R0p8p100_Jp4p70R9g00;\R:p4p710R;p8P9P1p8P9P2p8P9p10079p4p710R<p8P9P4p8P9P3p4p710R3p8P9P6p8p1006?p4p710P5p8p100`:p4p70R9P;p8P9P1p8P9P2p8P9p100`hR=p4p7210R>p8P9P<p8P9P4p8P9P3p8P9P5p8P9P6p8p100aDp4p70P<p8p100bCp4p7210R9P1p8P9P2p8P9P<p8P9P4p8P9P3p8P9P6p8p1062Tp6051000R9P5p8P9p103VIp4p710R?p8P9p1063Vp4p710p8p106kQp6051000R9P7p8P9P5p8P9P?p8P9P0p8p107<2p6051000R9P7p8P9P?p8P9P0p8p100bop4p70R9P1p8P9P2p8P9P4p8P9P3p8P9P6p8p1006\p4p7210R6P<p8P6P5p8p1007Up4p7210P5p8p10082p4p73110P5p8p10<9lR6p60521000R<P>p8P<P0p8P6p6051001R6P=p4p710p8P6P?p8P6P0p8p10>VRp6051000R0P;p8P0P7p8P0P5p8P0P?p8P0p10>WXp4p710p8p10>Xbp6051000R0P;p8P0P7p8P0P5p8P0P?p8P0p10>Ykp4p710p8p100cep4p710P5p8g00emj2sTg00kjj2GTg01;2j1dTg00QGj1:Tg00:Bj25Tg00=Lj20Tg01<4j1hTg00\7j17Tg019:j2[Tg01:6j2STg017fk10BTg008Nj1=Tg00dlk10>Tg00iHj2CTg0093j1NTg018]k208Tg00>Pj22Tg00>lR5j2ATg009Qj2jTg00:^j2@Tg01>6j2}Tg01>^j3zTg00;;j2nTg00<6j1vTg00<Oj2RTg00<lj29Tg00=ij2cTg00?Gj2bTg00?nj2`Tg00@Tj2_Tg00^Vj2JTg01AFk10@Tg00A:j13Tg00BBk10?Tg00B`k20=Tg00CAk30<Tg00JTj1KTg01BIj2pTg00AYj2oTg00DSk20:Tg00E?j1mTg00E_j3DTg00F?k109Tg00F_j2PTg00]4k107Tg00G[k106Tg00H9k105Tg00Hdj2lTg00J2k104Tg00Ldk602Tg00MHj3iTg00K9j2gTg00^3j3fTg00NNj2~Tg00O0j2|Tg00OJj2{TP:j3UTg00P6k300Tg00PUk401Tg01Gmj4qTg02mFj1eTg015oj2yTP8j3WTg00j2j3OTg01=4j2FTg01C2j3xTg00Cjj3YTg00G=j4wTg00IGj4]Tg00RFj7rTg00L@j7uTg00Rjj8\Tg00Mkj3tTg01IER8f0R:7W8p=^AO88:p=Xf1R0AO88:'Fp=ag00VPR?/5:p=1f2R71F0:'Cp>03AW88:,F0,C7p=6f5R;f4R6f3R=9W88'F'CAO88:,F0,C7'0p=<g00UMR<?U:?p=ZAU<0:p=HAO88:,F0,C7p=M1C0:,07p>0A1o<:p=;Ax<0:p=IAY<0:p>0;AY<0:9Y<7p=QP<P7P0P:Cwp=BP<P0g00XeP:C]p=VP0g00SNR>g00SmR9P9g00TMR3P:g00TmR4Frp=E1g<:p=8P7P>P9P9P3P<P0g00YLP:C]P4Frp=4P7P>P9P9P3P0P:Fup=kP=P>P9P9P3P7P0P:G\p=LP<P0g00Z3P:C]p=TAt<0:p=>f6R4P>P9P9P3P;P6P=P>P9P9P3P7P0P:G\G\p=?g00n`1s88%^:,G0R8#d%:8R2/58%^0,G7%X0,G7'0R1#h%71,511[=7R1#d%:1/511S6=R1#h%71,511a;6R1$0Bg00UkR@#=RA#=RB#=RC#=#=#=RD$0>RE/C1R1#1%NARF%NDRD+08RG,21'A%^;R1:03E4RH%NCRI'j%1H%1IRHf8RJf7RK56E/@I#1[[1}FD12?F%1D12?G[[%1FRLg0157RMAzFD0UW1%1G\M^1LPEf9RLPJPEPLPJE<RM/jI%1MPEf;RMf:RDPEPMPDE<RF/@IRN#1\H[PEPDPLPEPDPLE</nI%ZIRO#vRP1RIN19FI'0,HF[1cFI12?IRFPEf<RNPMPEPNPME<RQ/9IRR#112RI'A[1bQI12I?RQPEf=RRPNPEPRPNE<RS/9IRT,2I15T?'A[1`SIPEf>RSPRPEPSPRE<RT/@I#Z\O1_TIPEf?RTPSPEPTPSE<RU/9I/HU\O1@UIP<PEf@RUPTPEPUPTE</9IP<fARV=6EU/nIfBRU=6EVRW1@WI,RI19WI'0'H\P1cWIfCRW=6EURP/9IRX#112XI'A\F1bPIfDRP=6EWRX/9IRY,2I15Y?'A\Q1`XIfERX=6EPRP/@I#Z\O1_PIfFRP=6EXRX/9I/HX\O1@XIP<fGRX=6EP/9IP<P5fHR5=MEXRX#112XGfIRX=6E5RQ1aX580AE#7%:Q'Jp,1A$0@RQ/0L#710Q7#:'J/0?'0#1PUfJRY=MEX#1fKRZ=MEY/2Gg00VnRGg00WZR[#3R\#3R]#3R^#3R_#3R`#3#3#3Ra#3Rb#3#3Rc#3#3#;&0?@-0=<%;c60<<%;b%;a%KBRa#N,p<%;`'I1p<IR`%;_'I%;^,I`%;],I`%;\,I`1o<[,I`+0;3Q3Q3Q3Qg00X9+0:R`%mG9DG`9DG`9DG`3D&09G1P<J&07<RG7B61P<D?B4G7B71P<L?B;G1P<M?BKG7B=7B0&06<&05<R=P=1l<?RG1l<IRK'V,E=R6&049R`%KAR[#K#8R\94=G1V\K,E=5k=CLP`P=P=P=P>P9P9P31TKG,E=J02R9P`%8[R>%8CRC9i<K/>\'T,E=CLP`P=P=P6P`%=[#8R[94=G1V[K,E=5k=CLP`P=P=P9P`%K@R9#=#8R6,>>R\%8aRa9i<K/>['T,E=CLP`P=P=A4=G\P`P=A4=GKRKP`A4=GaF?P`P=P=A4=G>P`P=PKP`A4=GCF?P`P=A4=G6P`P=%K9#8R6/>a%89R954=P`P=%8BRB1>6C54=P`P=1g<@R@94=\P`P=%8ARA=4=>P`Af<@AAf<9B/>G'>94=GCLF?F?F?F?F?1~=3P:P7g00ZZR=g00[:R3'|1{:7=U=3dB00<?0H01bNbSbTX2<X5<X6<X7<X8<X9<X:<X;<X<<X3<X4<%1MR312MI'A\Fg00[Z\ORO1RIL/0N,H4[%1N12NI'A\F10JLRJ1RIN/0R'H\O%1J%1S\HRH[%1LPH[10RT/5L10ST,5M10RS/5L15MS1JMN1JRS/0?'0#1[[[[\3[[[[[[^2<^5<^6<^7<^8<^9<^:<^;<^<<^3<^4<P:P;PNPRP4PQfMRNfLR35MERSA6EN3R310Q4#:10QR#7%:3103S#7PDPMPVPUPWPPP7P5PXPYPZOFbMWEW0P0P:O2n2001000000121000000bYbWbDbCbBbAbLbXbVbKbJbIbHbGbObPbQbR1G41R1%X;,G4'0#7%:1'J1S4;#71[4;#:'J/0?'0#1eb0bFb@b?b>1s<<R?P<P<P2%X:,G0,08#7CqP<P<1[0:#:1S0:#7Cq%m?5D?3D#e#1e1y0:#e#1eWUW=o"). Qed.

#[using="Type"] Lemma vis_here_eq : forall b n p, vis_here b n p = true -> p = (b, n).
Proof.
  intros b n [pb pn] H. unfold vis_here in H. cbn [fst snd] in H. apply andb_prop in H as [H1 H2].
  apply expr_eqb_eq in H1. apply expr_eqb_eq in H2. subst. reflexivity.
Qed.

#[using="Type"] Lemma A_bytes_fm_here : forall E b n l,
  Forall (fun p => p = (b, n)) l -> A_bytes (flat_map (allow1 E) l) = Z.of_nat (length l) * A_bytes (allow1 E (b, n)).
Proof.
  intros E b n l H. induction l as [|p l IH]; [reflexivity|].
  apply Forall_cons_iff in H as [-> H]. cbn [flat_map length]. rewrite A_bytes_app, (IH H). rewrite Nat2Z.inj_succ. lia.
Qed.

#[using="SHADOW_ok"] Lemma unvis_sound : forall E cs R FULL model b n cs',
  cs_ok E cs R FULL model -> node_unvis A cs b n = Some cs' -> cs_ok E cs' R FULL model /\ pc cs' = pc cs.
Proof.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
ltac2:(KReplay.run1 (kr_t_AsanPlanSound ()) ["FPX_3"; "Sound"] "p'0p'1p'2h01pi001ph11Hh21xi011xh32Hah44__x1h54__x2h61zi021zh74HinKh87__arithh96__sat6h:6__sat7h;6__sat8h<4__x3h=6__sat4h>6__sat5h?1li031lh@3HKKhA2HhhB4HimghC5heq_ShD6heq_ubhE6heq_unhF1ai041ahG4__ffhH8__varmaphI5__withJ2HqhK2HchL1ihM1AhN4__p1hO1bi051bhP1mi061mhQ2b0hR1qhS5HinK0hT1fhU1KhV2HbhW3HzqhX2n0hY3HivhZ7__sat10h[6__sat9h\1ni071nh]2H1h^4__x4h_1ei081eh`2Hxha2Z2hb7__sat11hc7__sat12hd7__sat13he7__sat14hf7__sat15hg2ivhh2F2hi3Hinhj2Hzhk2Z1hl2b1hm2b2hn2hii092hiho2loi0:2lohp1Bhq2H5hr3Ha'hs2Hpht1Xhu2_Hhv1yhw2F1hx2FFhy4GONEhz2H0h{2H2h|2H6h}3Haph~3Hbhi0;5Hkeepi0<3Hnhi0=3Hshi0>2Hvi0?2Z0i0@4__x5i0A4__x6i0B4__x7i0C2F3i0D2HBi0E3HS0i0F3HSSi0G3HSni0H4Hbh'i0I3Hdbi0J3Hdni0K4Hnh'i0L3Hspi0M5Hzeroi0N2L1i0O2Rbi0P1Si0Q1Yi0R3cs'i0S5lemmai0T1oi0U2pgi0V2H3i0W2H4i0X3Hpgi0Y3Hs'i0Z3Hv'i0[2L2i0\2Mxi0]1Pi0^2X1i0_2X3i0`2X4i0a4__p2i0b5__x10i0c5__x11i0d5__x12i0e4__x8i0f4__x9i0g2a1i0h2a2i0i1ci0j4cstri0k1ki0l2n1i0m2n2i0n1si0o2ubi0p2uni0q1vi0r1wi0s8ALLOW_eqi0t9ALLOW_subi0u3D8bi0v3D8ni0w1Ei0x4FULLi0y3H10i0z3H11i0{3H12i0|3H13i0}3H14i0~3H15i102H7i112H8i122H9i132HAi143HA0i153HABi164HAB0i172HCi186HID_eqi198HID_monoi1:2HKi1;3HK1i1<3HK2i1=3HKii1>3HMIi1?3HPGi1@3HZ0i1A3Hbdi1B3Hcsi1C3Hexi1D2Hii1E2Hni1F4Hrb0i1G4Hrn0i1H5Hshhii1I3Hz1i1J3Hz2i1K2I1i1L2I2i1M2I3i1N3IMGi1O2L0i1P1Mi1Q2M'i1R4M_eqi1S6M_nonei1T4Mmidi1U9Mmid_nonei1V8Mmid_outi1W2N1i1X2N2i1Y2N3i1Z2N4i1[2N5i1\2NAi1]1Qi1^1Ri1_2Soi1`2X0i1a2X2i1b3_H0i1c2bbi1d2bhi1e2bki1f:co_abytes0i1g:co_bounds0i1h7co_brk0i1i9co_eager0i1j7co_fds0i1k6co_fs0i1l8co_halt0i1m9co_holes0i1n9co_kinds0i1o8co_know0i1p9co_lazyb0i1q9co_limit0i1r7co_log0i1s8co_maps0i1t8co_minv0i1u9co_nasub0i1v8co_none0i1w8co_regs0i1x7co_res0i1y8co_sbrk0i1z8co_seps0i1{8co_sinv0i1|9co_split0i1}7co_tid0i1~9co_totsz0i206co_wf0i218co_zero0i222csi232e0i242k1i255modeli262nhi272q0i282q1i292qbi2:2qni2;1ri2<2r0i2=2r1i2>2sbi2?2ski2@2sni2A1ti2B9co_abytesi2C9co_boundsi2D6co_brki2E8co_eageri2F6co_fdsi2G5co_fsi2H7co_halti2I8co_holesi2J8co_kindsi2K7co_knowi2L8co_lazybi2M8co_limiti2N6co_logi2O7co_mapsi2P7co_minvi2Q8co_nasubi2R7co_nonei2S7co_regsi2T6co_resi2U7co_sbrki2V7co_sepsi2W7co_sinvi2X8co_spliti2Y6co_tidi2Z8co_totszi2[5co_wfi2\7co_zeroi2]<minv_alignedi2^<minv_allowedi2_;minv_budgeti2`9minv_lazyi2a:minv_nodupp%0p%1p%2p%3p%4p&0p&1p&2p&3p&4p;1p;2p;5p;4p;6p;3p;;p;8p;>p;:p;7p;<p;Pp-1R0g0<>`R1p4p710R2p9P0p1000Sp4p710R3p9P0g001?R4p4p710p9P0P4p4p7210p9P0P4p4p73110p9P0p1001]R5p4p7210R6p9P0g0>iHR7p4p710p9P0g0038R8p4p710R9p9P0g0>j7R:p4p710R;p9P0g00_3R<p4p710R=p8P0g004eR>p4p710p8P0g005FR?p4p710p8P0P?p4p7210p8P0g005cR0p4p710R@p8p100_Jp4p70RAg00;\RBp4p710RCp8PAP2p8PAP3p8PAg0079RDp4p710REp8PAP6p8PAP5p4p710R5p8PAP;p8g0>ahRAp4p710P9p8g00`:S00p4p70RFPCp8PFP2p8PFP3p8PFp100`hRGp4p7210RHp8PFPEp8PFP6p8PFP5p8PFP9p8PFP;p8p100aDp4p70PEp8g00bCRFp4p7210RIP2p8PIP3p8PIPEp8PIP6p8PIP5p8PIP;p8p1062Tp6051000RIP9p8PIp103VIp4p710RJp8PIp1063Vp4p710p8p106kQp6051000RIP=p8PIP9p8PIPJp8PIP@p8p107<2p6051000RIP=p8PIPJp8PIP@p8p100bop4p70RIP2p8PIP3p8PIP6p8PIP5p8PIP;p8p1006\p4p7210R;PEp8P;P9p8g007US01p4p7210S02P9p8p10082p4p73110P9p8p10<9lR;p60521000REPHp8PEP@p8P;p6051001R;PGp4p710p8P;PJp8P;P@p8p10>VRp6051000R;PCp8P;P=p8P;P9p8P;PJp8P;p10>WXp4p710p8p10>Xbp6051000R;PCp8P;P=p8P;P9p8P;PJp8P;p10>Ykp4p710p8p100cep4p710P9p8g008Nj1_Tg00JTk10?Tg00dlk12>Tg00eJk13?TPFk241Tg01SnS03k11}Tg01TPS04j5cTg0=XRk42qTg0>jYk43TTg0>k`k43QTPDk60ATg03JOk12DTg00emRDk222Tg00O0j2zTPBj30Tg02X7j12Tg07@Dk41OTg06_:k20[Tg01ERj17Tg0093k10wTg00=Lj21Tg06\6j4QTg0>gGk50;Tg02W:j1HTg02^\j1CTg02fVj1NTg02`\j1DTg02lFj1KTg03FWj3JTg00E?k12:Tg02nCj1FTg02jMj1LTg02Y2j1OTg02Zlj1MTg05WWl;TTg00J2k126Tg03_dk107Tg01Gmk41@Tg01Plj2GTg030Ck21jTg0>lfk13rTg05TWk12{Tg02P:k11yTg0>mhk13pTg0>nhk42wTg05UWk12tTg0>ook43nTg0?12k13lTg0?26k13hTg0?3;k13gTg0?4>k13fTg0?5Ck13dTg0?6Fk13cTg01GPj3?Tg0?7Kk13`Tg0?8Qk13_Tg0?9Tk13^Tg0?:Vk13\Tg0?;\m;3[Tg013>k42oTg05XUk63ZTg01QJk30rTg07X`j2XTg0>hGk20Ij3[Tg00:BRBj23Tg01Qmk23STg03M^k63RTg02S>k41^Tg02U9k41:Tg06bFk82kTg07CLk83PTg018]k20Fk13oTg03iTk21STg03fQk20_Tg06cIk53FTg01=4k21DTg01L1k216Tg00iHj2@Tg01>6k21ITg01>^k308Tg00A:RFk10@Tg00AYk23>Tg00DSk21zTg00E_k30ETg00F?S05k11ATg00]4k14HTg00G[k14CTg00H9k14BTg00Hdk21kTg00K9k233Tg01LWk33=Tg00NNk240Tg00OJk23~Tg00P6k33}Tg00PUk431Tg01M:k23|Tg05>_k13{Tg05?ak13zTP8j6}m;3km>3jk82Mk749Tg0;GTm;3yTg01AFk13xTg03gQj2wTg017fk13wTg00:^j2=Tg00<lj2iTg009Qj3vk20CTg01fik21NTg00;;k22XTg00<6j1|Tg00<Oj2^Tg00=ik22WTg00?Gk22VTg00>Pj2ETg00?nk22UTg00@Tk22TTg00BBk13uTg00B`k23tTg00CAk33sTg01BIk230Tg00MHk32|Tg07Pok33qTg09@bk62zTg00>lR8j2PTg00^Vk20xTg00^3k32xTg06fik82vTg0?<_k52uTg01fOk41;Tg09D4k52sTg09Ahk22rTg0;HXk32PTg0?=Bk33mTg0?=km:3iTP>k30<TP<j39Tg00gKk32<Tg03G2k43eTg0??0k42OTg01j`k309Tg01VHj2uTg00mbS06j2]Tg06>Ak23bTg00kjj2>TP0j3mTg016lS07j2~Tg01Olk33]Tg01c?k20cTg01X@j1jTg01f5k32;Tg019:k20iTg01:6k21HTg01hCk31tTg01Vek23XTg01POj2bTg01c\k23WTg0148k20vTg01UNj4VTg01WFk40NTg020Vk13VTg06@Fk73UTg01^Ak22nTg01_?j1eTg01`6k10DTg01`lk200Tg01aik10kTg01N7k12JTg01Y@k111Tg01Nok21CTg0?@2k41YTg042<k21qTg03ETj4Ak314Tg00jOk41pTg0?A4k10`Tg04URj4gTg04Xkk602Tg00hmk62HTg01bck32lTg03hPk31VTg03nXk21bTg03o\k31aTg043@k21lTg044Dk31UTg045Hk21eTg04@ek41cTg04Aik31TTg04Bmk21gTg04P3k52jTg04^?k52iTg04TJm<2hTg01gZk32gTg015oj1xk21QTQ01j4fTg01FPk10TTPAk43OTg0>`ik23NTg0>aGk52FTg01C[j2RTg02mFj1ITg09f@k13LTg0?B3k53KTg040`k20XTg035GRAk11RTg03jWR0k212Tg03dFk12cTg047Mk43HTg0?BRk23GTg03m1k43JTg08\lk53ETg0?C^k53DTg0?Ddk33MTg07V_k22GTg01i]k22ETg04onS08k22LTg0=7mS09k23CTP:k73Bk44UTg0?Ekk42NTg0?FJk33ATP4k44WTP1k42CTg0?G;k24VTg0?Ghk83@TP7k74TTg0<?Gk34STg0<@=k44RTg0<A0m;4NTg017Fk54MTg0:Bak64LTg02O>S0:k225Tg0>eFk64KTg07T\k64JTg02oDk31xTg02Q<k32bTg02R=k12aTg02A\k13<Tg02Yok32RTg02@ik13;Tg02BSk12~Tg02[mk11fTg02\gk14ITg02]ek12ATg02_[k32`Tg00fMk32_Tg02aZk13:Tg02bWk139Tg00j2k32^TP?k32[Tg01Z8k14GTg02cWk14FTg02dWk238Tg00jjk14ETg00lck14DTg02eVk137Tg02gVk136Tg02hQk332Tg02iXk12\Tg02kKk135Tg02E9k12BTg06BCk123Tg06CCk24ATg06Dik74@Tg06Ack44?Tg07ICk14=Tg0?H[k24<Tg06:eS0;k234Tg0?I?k24;Tg06H<k24>Tg03:2mP4:Tg05VYk448Tg00Cjk32ZTg00F_k247Tg00G=k427Tg00IGk41_Tg00Mkk346Tg00RFk71wTg00L@k745Tg00Rjk81vTg01C2k344Tg00K\k643Tg00Ldk64OTg00n<k74PTg04F^m<42Tg04E9m<4QTf0R?#_#_p>2If2R7f1R1g01JGS0<01j?30p>0>%2100[?p>2@1X1?,b7p=Zf7R4f6R:f5R<+0If4R>3mf3R91X71'b'G/G?p>0Sg01k_S0=,b?p>3aP:P<P>P9CQ,G4/G7/G1/G?p>0tP:P<P>P9H1YP7P1P?H1Yp>0H&2{9&1y7P1&2t?H48p=SA[71?#jp=:&0T>g01IER;P;P7P1H1@>0E9?5?<p=YQ0<01j?p>01g00UMRJ?01?,P7p>1B20[71=09?p>1?20I<>=m:91X1?,b7'Gp>0~1X71,b9,G>/G?p>211G71/G?p>20Q0=,b?,G1p>2Y111?Q0='bp>0Bg00ZZR=?01?p=`%2:P<P>P9H1YP7P1P?H1Yp=t%7?9J71p=aP;P;P7P1H1@>0E9?p>1~&0T1=?7?p>2}g00[:RC90=?p=5A0J1?p=41G>9/G7/G1/G?p>3YA0=1CA0=?C'Pp>0s20I71%7?5m9p>1Z1G4:/G<P>P9P7P1CQ'G/G?p>2K1G1?=0=Cp=s1b1?=0=Cp>0G%21/X?p=UAm71?=0=Cp=W21D1?,@7p=621S1?-0_7p=og00VPRG/E?p>0:1371/P?p>0l13G1/P?p>0V13G?p=81171/3?p=\111?-167p>151171=0J?p>0Y1zJ?p=;23>J?p>0]B2ZJ1?:2ZJ7p>1M247J?p>0\PJP7P1P?H27p>0j233J?p>05PJP1g00XeREP?H1_p>24B46J1?p=pP7g00SNS0>g00SmS0?Q0?g00TMS0@PJP1g00YLRHP?H1_g00TmS0AK1wp=kP7Q0>Q0?Q0?Q0@PJP1PEP?H1_Q0AK1wp>1KP7Q0>Q0?Q0?Q0@P1P?K45p>0ZP9Q0>Q0?Q0?Q0@P7P1P?L1vp>0QP<Q0>Q0?Q0?Q0@P>Q0>Q0?Q0?Q0@PJP9PHP7H1_Q0AK1wP1P?L1vp={P>Q0>Q0?Q0?Q0@P9Q0>Q0?Q0?Q0@P7Q0AK1wP1P?L1vp>1P13G71E1?'Pp>10PJP>P9P7P1P?E}p>06PJP>P9P7P1P?J0Ap>1>21D71,@9/=?p>0}1171/i?p>0R1=1?,17p=n&0??$0?p>3v1=1?,3Gp=lP7Q0>Q0?Q0?Q0@PJP1g00Z3RHP?H1_Q0AK1wp>1i1=71/1?p>1hA0J?Gp>0|111?90J7p>0{131?,P7p>2?B44J1?p>0yB2ZJ1?p>2SPJPJP>P9P7H27P1P?H27p>1=P1Q0>Q0?Q0?Q0@P?J43p>1|P1Q0>Q0?Q0?Q0@P?J4Op>1d&0??$0?$0?$0?p>1{%_?#_#_#_p>2Q%_?#_#_#_#_#_#_#_p>1<P:Q0>Q0?Q0?Q0@P<P>P9Q0>Q0?Q0?Q0@P7P1P?L1vL1vp>1L20F7102r?p>0e1X1?-0F7p>2y1171/=?p>1`1E1?,P7p>0g1P1?,P7p>1uP;P;P1P?H1@p=h20I71=J9?p>19AJ71?99>9p>0dA9971A0=?C'Pp>0aB2[;;?p>1]B2^;;?p>1\1b<>1>1?,17-0c9'Gp=d20i<>/b921H1?-0c7'Gp=y1u1?=0=Cp>1JA0=?C,P1p>041>1?,17-0c9p>0^1b71/G?=0=C,P9p>181>1?,17p>1[1b71/G?=0=Cp>0O1b9720c1?'Gp>0=%j?=0=Cp>0bA9971/P?p>0uP9A0=7CP1P?H1pp>0f21H1?-0c7p>0m20i71/b?p>1G13>9111?,E7'Pp>0Jg014WS0B90=?p=BAm71?Q0B50=p>1720c1?=0=Cp>0qP=P9P7P1PCP?J0Ap>1s1X1?-1I7p>1E1X1?,3Gp>0h20F1?,EGp>0L20F1?,3Gp>0K111?,E7p>1F1b>9111?-0c7'Gp>1r111?-0c7p>29P7Q0>Q0?Q0?Q0@P1P?K4Pp>2m13971E1?'Pp>13P<P>P9P7P1P?J02,u:p>0Mg03GPRE?J1?p>1XA9E1?p=<B0<E1?p>1W&0`?=0=Cp>0WP=&0`7P1g015SS0CPCP?J0Ap=rP>P9P7P1CA00v?p=qP=P>P9P7P1P?J0Ap>1mP;P;P1P?H1@-1Q7p>1oP9P7P1&0T?Cfp>0UP<P>P9AJ71?Cfp>0og03D=S0DQ0DPJPJPFPAPAP9g04HKP7P1P?N<42p>3IQ0DPJP0PAPBg04GiP<P>P9P7P1P?N<4Qp>2dPJP>P9PJP7P1P?H27H27p>2ePJP1PHP?H1_p>2fB2[JJ?p>28B2^JJ?p>2=g01HMS0E,11/b?p>0z1b71/G?p>1nA9971/]?p>0PA971?,]9p>2pP9P7P1P?Cf99<>p>0n21Q1?9997p>03g00oaS0F@0<1?p>0pP=P9P7P1Q0BP?J0Ap>2]g00n`Q0<g00UkS0G#_RH$0?S0H$2>%_HS0I#_S0J#_S0K$2IS0L$2>RB$3?RA+41Q0J$2>S0M$3?S0N$1}R0\AS0Og01l\Q0<P4P:P<P>P9DcQ0<$1}RFp,1AS0PP4P9P7H2q<0>1PFQ0Pf8RIP>P9H2qB0>F?9Z0TFP?Q0PPIP>P9H3TR5Q0PPIP>P9H3QJ0AB0>F57&2D<222;JS0QQ0Q/z?Q0Q&2D:;0?PDP;PJQ0Q&2DI;0?PDP;PJPFP1PDQ0QP;PFQ0Pf?R5#2f;R6f:R3H1OPDP;PJPFP1Q03PJPFfCR202@5Q03PJPFfDRK#2RL00[5P=PF222;;RMfARNf@ROfERP#7RQQ0G$0?S0R$0wRR%2PRSPNAZRSOL0SPSP4P:PO111?RT$3aRUPSP9P7P>CQPSPSP9P7P>I0;L0t%HPRVPVPSP4P:POP9P7P>K0HPVCS%CP%NP%DP%KPfBRV?:N?X0M=JMQPMPPPMPNPO&2:MRQEY%FP%LP%OP%MPM;T$01Q0<$26S0Sn0100000020000Q0Sn10110100021012600Q0Sn10110100021011d00n200110000012012>12?n200110100012010012@n200110100012011c11e>0>F4P5PIf=RWf<RXP6Dc&07If>RY$0741B]1_0LP1Q0Q&2D6P;PJP1P?H1@30PDQ0QP;PFQ0P%2OPXP6H1OPDP;PJPFP1Q03PJPF20[LOQ03PJPF20[SOP=PFPMPVPNfFRS#7RZPR%2SR[PVAZR[NL0SP[PIP4PNPUP[P9P7P>CQP[P[P9P7P>I0;L0t%HSR\P\P[PIP4PNP9P7P>K0HP\CS%CS%NS%DS%KSA:2V?X0M=JMZPMPSPMPVPNPQEY%FS%LS%OS%MSM;T$01Q0Sn0100000020000Q0Sn10110100021012600Q0Sn10110100021011d00n200110000012012>12?n200110100012010012@>0>F3Q0P%2NPWPXH1OQ0Q022;RZ1zZ?Q0P%2VPYPWH1O=0Z?PDQ0QP;Q0PPLPOP5H1O=0Z?PDQ0QP;PFP1PDP;PJPFP1Q03PJPFfIRL02@PQ03PJPFfJR\02@PP=PFPMfGR[PSfKR]#7R^PR%2]R_P[AZR_SL0SP_PWPXPSPUP_P9P7P>CQP_P_P9P7P>I0;L0t%H]R`P`P_PWPXPSP9P7P>K0HP`CS%C]%N]%D]%K]fHR`?:[?X0M=JM^PMP]PMP[PSPQEY%F]%L]%O]%M]M;T$01Q0Sn0100000020000Q0Sn10110100021012600Q0Sn10110100021011d00n200110000012012>12?n200110100012010012@>0>F5P[POPPPKP2Dc&07O&07S41B]1_0=P1Q0QPDP;PJQ0P%2`PKP2H1OQ0QP;P1P?H1@50ZPDP;PJPFP7Q03PJPF20[_[Q03PJPFfLS0T#2RD00[[P=PFPMPLP`fMR^#7RaPR%2^RbPLAZRb`L0SPbP5PYP`PUPbP9P7P<CQPbPbP9P7P<I0;L0t%H^RcPcPbP5PYP`P9P7P<K0HPcCS%C^%N^%D^%K^A:\L?X0M=JMaPMP^PMPLP`PQEY%F^%L^%O^%M^M;T$01Q0Sn0100000020000Q0Sn10110100021012600Q0Sn10110100021011d00n200110000012012>12?>0>F2P]PKPLP`P[Dc&07K&07\41B]1_0=^_;P?Q0PP_P[PSH1OQ0QP;P;PJP7P1H1@P?H1@50ZQ03PJPF20[D`Q03PJPF20[b`P=PFPMP\PLfNRD#7RZPR%2DR_P\AZR_LL0SP_POP5PLPUP_P<P>P9CQP_P_P<P>P9I0;L0t%HDRaPaP_POP5PLP<P>P9K0HPaCS%CD%ND%DD%KDA:]\?X0M=JMZPMPDPMP\PLPQEY%FD%LD%OD%MDM;T$01Q0Sn0100000020000Q0Sn10110100021012600Q0Sn10110100021011d00>0>FS20[bL&1}JS0UQ0U/z?RbQ0UP_P\P?H1?Q03PJQ0UfPS0V#2Q0TP?H1?Q03PJPFP1Q03PJPFfRS0W02@^R_P=PFPMfOS0XPDfSRZ#7RaPR%2ZRcQ0XK0~PRPcPDPcPPPKPDCQI21Rd/GUPcP3f9RUPICQRePcPcP3PUPII0;Rf420%HZRgPgPcPPPKPDP3PUPIK0HPgCS%CZ%NZ%DZ%KZQ0VQ0X;:?X0M=JMaPMPZPMQ0XPDPQEY%FZ%LZ%OZ%MZM;T$01RaQ0Sn0100000020000Q0Sn10110100021012600Q0Sn10110100021011d00&01]S0Y50FPZQ0TfQS0ZQ0VQ0XDcQ0T$07Q0W$07Rg41BS0[]1]~P1Q0UQ0Z#2P^21jJ?RhH1?Q03PJPFP_P=PF117?-2Yd@20efPaQ0Sn0100000020000Q0Sn10110100021012600Q0T60>F20[cDQ0UPbQ0UfTS0\#2Q0XP?H1?Q03PJQ0UfVS0]#2Q0ZP?H1?Q03PJPFP1P=PFPMQ0\PZfXRb#7RcPR%2bRaQ0\K0~PRPaPZPaP\PLPZCQI21Rf114?+2YPaP5PYPWCQRePaPaP5PYPWI0;Rd420%HbR_P_PaP\PLPZP5PYPWK0HP_CS%Cb%Nb%Db%KbfUS0^Q0\;:?X0M=JMcPMPbPMQ0\PZPQEY%Fb%Lb%Ob%MbM;T$01RcQ0Sn0100000020000Q0Sn10110100021012600Q0Z$01S0_50FfYS0`Q0WfWS0aQ0]Q0^Dc&07bR_81BgS0b]1_0<P1Q0UQ0a#2Q0WPhH1?P=PF1141-2Yf@20edPcQ0Sn0100000020000Q0W60>FPMQ0^Q0\Q0`#7PRQ0`#2RcQ0^Q0\9ZRcL0SPcP]P\Q0\20BI7PcPOP5PYCQPcPcPOP5PYI0;L0tP=1z=?S0cPMQ0]Q0^fZS0d#7PRQ0d#2RcQ0]Q0^9ZRcL0SPcQ0TP]Q0^20BU9PcPNPOP5CQPcPcPNPOP5I0;L0t/`?P=PMPbQ0af\Rc#7RdPR%2cRePbQ0a9ZReL0SPePDP^Q0a20B6<PeP2PVPNCQPePeP2PVPNI0;L0t/`?P=PFP1f]Rf#HRhPhPfQ0XPDPbPKP2PVFtPhCS%Cf%Nf%Df%KfQ0dQ0`;:?X0MRh=aMfPMQ0`PbPQH1~Rg:2}Mf%Ff%Lf%Of%MfM;TRa$01Q0Sn0100000020000Q0a$01S0e50Ff_RiPbPfPcf[S0fDcf^Rj$0781B_S0g]1]KP1PMQ0aQ0]Q0f#7PRQ0f#2R_Q0aQ0]9ZR_L0SP_P^Q0TQ0]20B3>P_PVPNPOCQP_P_PVPNPOI0;L0tS0h#5%HcR_P_PePDP^Q0aP2PVPNK0HP_CS%Cc%Nc%Dc%KcQ0`?:b?X0M=JMdPMPcPMPbQ0aPQEY%Fc%Lc%Oc%McM;T$01Q0]$01S0i50Fg0?IcRd$1}R_Q0<Q03PdQ0<P?P?Pbn10110T00021000000Z2A_Q0a-1jdRe&3rfRk$2{&1yk&3pfQ0XPDPbH2wPKP2PVH2w&2tkH3n&3lf&3hf&3gf&3ff&3df9JMh&3cf=?Mg&3`f&3_f&3^f&3\fN;3[-1jdRdP_PdPeP?H2oJ3ZQ0<Q0a;0aQ0<%HjRaPaPjQ0VQ0XQ0`PPPKP2FtPaCS%Cj%Nj%Dj%KjQ0fQ0d;:?X0M=aMjPMPjPMQ0dQ0`PQEY%Fj%Lj%Oj%MjM;TRaQ0<%HiRePe%2iRdQ0ZQ0VQ0dPSPPPKK0HPeCS%Ci%Ni%Di%KiQ0f=:c?X0M%7iRe5JMPMPiPMQ0fQ0dPQEY%Fi%Li%Oi%MiM;TR_$01>0>F?faRgP1PiPjPfDc&071f`S0j$0741B]1Y0R&01aRa=0FaQ0jP_PjPfPcDc&07_&07iS0k'4PMQ0fQ0dPePRPdQ0fK0~Q0d9ZRdPdQ0ZQ0VQ0dCQ20BYIPdPSPPPKCQI3YRePdPdPSPPPKI0;Rd<0r920sedP8PMPcQ0fQ0jH1ZQ0j#2Rd=ZRcQ0f9ZRdPdQ0WQ0ZQ0f20B5UL2KPdP[PSPPCQ'sPdPdP[PSPPI0;#5fbS0l%HgRdPdPgPZQ0WPcP`P[PSFtPdCS%Cg%Ng%Dg%KgA:jf?X0M=aMgPMPgPMPfPcPQEY%Fg%Lg%Og%MgM;TQ0jPiPjDcP?PMPjPfQ0lH1ZQ0l#2Rd=ZRjAZRdfPdQ0\PZPf20BN6L2KPdPLP`P[CQ'sfcS0m#2RdPdP\PLP`I0;#5PMQ0jPifdS0nH1ZQ0n#2RdQ0j5ZRAZRdiPdQ0]Q0^Pi20B2WL2KRePdP]P\PLCQRd<0r120sedP8PMPgQ0jfeS0o#7PRQ0o#2RdPgK0~PRPdQ0jPdQ0aQ0]Q0jCQI2120BKY'sPdQ0TP]P\CQ#5fgS0pffS0q#HRdPdQ0qPbQ0aPgP^Q0TP]FtPdCSQ0q#CQ0q#NQ0q#DQ0q#KQ0mQ0l;:?X0MQ0q5aMPMQ0qPMQ0lPgPQEYQ0q#FQ0q#LQ0q#OQ0q#MM;TQ0oQ0nQ0mDcP?PMQ0mQ0lQ0p#7PRQ0p#2RdQ0mK0~PRPdQ0lPdQ0`PbQ0lCQI2120BSO'sfhS0r#2Q0XPDP^CQ#5PMQ0oQ0nfiS0s#7PRQ0s#2RdQ0oK0~PRPdQ0nPdQ0fQ0dQ0nCQI21Rd20B`VRe<0r120sdeP8PMQ0qQ0ofjS0t#7PRQ0t#2ReQ0qQ0o9ZReL0SPePcQ0fQ0oCQ's20BL2#5flS0ufkS0v#HRePeQ0vPfPcQ0qQ0WQ0ZQ0VFtPeCSQ0v#CQ0v#NQ0v#DQ0v#KQ0rQ0p;:?X0MQ0v5aMPMQ0vPMQ0pQ0qPQEYQ0v#FQ0v#LQ0v#OQ0v#MM;TQ0tQ0sQ0rDcP?PMQ0rQ0pQ0u#7PRQ0u#2ReQ0rQ0p9ZReL0SPePjPfQ0pCQ'sQ0T00BS#5PMQ0tQ0sfnS0w#7PRQ0w#2ReQ0tQ0s9ZReL0SRdPeQ0jPiQ0sCQRe<0r120sdeP8PMQ0vQ0tfoS0x#7PRQ0x#2ReQ0vK0~Q0t9ZRe'sPePgQ0jQ0tCQ#5fqS0yfpS0z#HRePeQ0zQ0lPgQ0vQ0aQ0]Q0^FtPeCSQ0z#CQ0z#NQ0z#DQ0z#KfmS0{Q0u;:?X0MQ0z5aMPMQ0zPMQ0uQ0vPQEYQ0z#FQ0z#LQ0z#OQ0z#MM;TQ0xQ0wQ0{DcP?PMQ0{Q0uQ0y#7PRQ0y#2ReQ0{K0~Q0u9ZRe'sfrS0|#2Q0nQ0mQ0{CQ#5PMQ0xQ0wfsS0}#7PRQ0}#2ReQ0xK0~RdQ0w9ZReRe<0r120sdeP8PMQ0zQ0xftS0~H1ZQ0~#2ReQ0z5ZR'sQ0x,Xe-0GRfvS10fuS11#HRePeQ11Q0pQ0qQ0zPcQ0fQ0dFtPeCSQ11#CQ11#NQ11#DQ11#KQ0|Q0y;:?X0MQ115aMPMQ11PMQ0yQ0zPQEYQ11#FQ11#LQ11#OQ11#MM;TQ0~Q0}Q0|DcP?PMQ0|Q0yQ10H1ZQ10#2Q0|5ZR'sfwS12Q0|'U-0GRPMQ0~Q0}fxS13H1ZReQ13#2Q0~5ZRRd<0r120sedP8Q11Q0~+0IfyS14#75WMQ14Q11'U-0GRf{RdfzRe#HR_P_PeQ0uQ0vQ11PgQ0jPiFtP_CS%Ce%Ne%De%KeQ12Q10;:?X0M=aMePMPePMQ10Q11PQEY%Fe%Le%Oe%MeM;TQ14Q13Q12DcP?Q12Q10+0I%7d5WMf|S15Q13'U-0GRP820G1?1371S16[S17131?20G71R_[S181397\_23S1?S19P1n2001000000120000000XPJX\JS1:Q17^PJ^\JS1;P?PRf~S1</UeR_P1O313R_Q1:Q1;P?PRp+01AS1=/UdR_PIO313R_Q1:Q1;P?Q0f,1gR_Q0=PKO3Q0=,3_p+01ES1>p+01DS1?p+01CS1@p+01BS1AQ1=Q15J3Rp,4SEGSR_Q1>Q1>Q1?Q1=Q1AH1^Q1?#2H1:p+01FS1BQ1>Q1AQ1@H1^Q0OP_p+01GS1CP?Q1B#2Q1AQ0nP1Q0mL2kQ1CQ1A56BQ0n'3P_p+01HS1DP1Q1C#2Q1APiP7PjL2kQ1DQ1A56B/3ip+01IS1EP7Q1D#2Q14Q13Q1@P9PKL3PQ1EQ14Q133oRaQ1EQ1@56BRh,1a&0wHRaQ0L$0wRk+0FRl&0:h40l+0VP8p+01JS1FQ147oeRh#8Q1FQ1?56BRm,1h&0:m80llp+01KS1GQ1F#HRmPmQ1FPdPeQ1>Q0zQ0xQ0wFtPmCSQ1F#CQ1F#NQ1F#DQ1F#KQ1CQ1B;:?X0MQ1F5aMPMQ1FPMQ1BQ1>PQEYQ1F#FQ1F#LQ1F#OQ1F#MM;TQ1EQ1DQ1CDcP?p+01LS1HQ15;od#8p+01MS1If}S1JQ15+1SRm+0_Q1IQ1C56BRh'1&0:h80llP8p+01NS1KQ1<Q1J+1SRh+0_Q1KQ1D56BRn;\l&0:np+01OS1LQ1K#HRnPnQ1Kp+01@S1MQ1<Q1EQ0~Q0}Q0|FtPnCSQ1K#CQ1K#NQ1K#DQ1K#KQ1GQ1F;:?X0MQ1K5aMPMQ1KPMQ1FQ1EPQEYQ1K#FQ1K#LQ1K#OQ1K#MM;TQ1IQ1HQ1GDcP?p+01PS1NQ1=Q1M+1SRn+0_Q1NQ1F56B;\lp+01QS1OQ1G56B$0:p+01RS1PQ1IQ1@Q1AQ1=I3FQ1PQ1I+1DQ1PQ1@56BQ1A615B50Ap+01SS1QQ1K56BPJp+01TS1RQ1K56BPJPAp+01URoQ1B56BQ1>'1Rp-16BRqp+01VS1SQ1CQ1B3oRr1@B?S1T'4XOAPpQ1SQ1C56BQ1B<0Y?X6J%;p1@BqRqQ1L96BoRs#;14?sRsePsQ1SQ1O56BRs#;147sRsePs21IakS1U&0:aS1V%8k&0:lRs[[S1W%8aRtg0157RuB08ak1UW3S1X%8lS1Y\uS1Z^3tS1[g00VnS1\g00WZRv$0@S1]$0@Rw$0@Rx$0]S1^&0]wS1_23>JvS1`41Mg00X9S1a+1zQ1\$2:S1b40EQ1\$1AS1c&0\7S1d&0\9S1e&4HJS1f80j9S1gQ1f80j9S1h80j1&4CJS1i&4BJRvPv21kJGS1jQ0I$0?S1k$05Rw+24Q0?$26RyPvPvQ0G-33JS1l&05HS1m'pS1n/pw21kJaS1o>3=JBS1pPyPvQ1jQ1n5kvRwPyQ1nQ1p61Kv:0ZvwS1qH0QE{I1PQ0@-40vS1rP?P71z=CS1s23~?7#5dB3}JG1S1tH31S1ubGbHbIX4JX5JX<J&0:7S1v1117S1w?\9l1179S1x#8119>Rw@10wl[[[^4J^5J^<JP?P<Q1Fp+01ZS1yQ1G56BPIPUPWO6b8b=b>bDbE-3|pI06Q1BQ1>+1SRp$3{96Bo&3zp<0Yqe20_opRp/4qeQ1N-1DoP7E}14p1RpePpPr11?7S1z/3lX6JP<P7P?I1>1171S1{/3lp+01WRrQ1DQ1C3o%8?S1|X6JP3P9P1I1>%89S1}p+01XRpPN%2rQ1QQ1PQ1JQ15PdPVPePfN;3y20_pmPBPpQ1QQ0J$0wRmH0}Q0P$3xRq<0Rl'41wpdPBPpQ1PPmH0}41BP8p+01YRw00_hPBPwQ1RPmH0}@0Rql'4Q15,wwPBPwQ1QPmH0}'4Q1y%HwRhPhPwQ1GQ1FQ1RQ1MQ1<Q1JFtPhCS%Cw%Nw%Dw%KwQ1S?:o?X0M=aMwPMPwPMPoQ1RPQEY%Fw%Lw%Ow%MwM;TPpPrQ1SDcP?p+01[Rh00_nPBPhQ1SPmH0}@0Rql'4p+01\RnQ1M'wPBPnQ1SPmH0}'4p,9SHADOW_okg07[bp+01^S1~01DwRH$3w1@BHRH@10Hl1=6mS20/1qRH/ilS21AnqXmS22,4?X6JRzPHPzp+01_S23=6BwRz#;143zRzeS24Pzp+01`S25=6BhR{#;14X{R{eS26P{Q0H$0?S27$3vS28$0wR|-1IaS29Q1V%8|20Fa|S2:$0:[[S2;B08a|1VuX3tS2<Q2:#8\u^3tS2=Av5m6R|%8mR}1lOm[R~Q1UQ1WQ1XQ1[Q1bQ1cQ1dQ1f80j1S2>Q1iQ1nQ1mQ1l'p61ivQ1rQ1ubGbHbIX4JX5J11?1S2?/4T^4J^5JP?Pq1=2mO2b8b=b>b9b:b;bDbEQ21Q24PzQ26P{Q29Q2;Q2<Q2=P|P~Q1UQ1WQ1XQ1[B1hVmqR~01Nl%8~Q1Y1=KmR~@0Rql#8[[20CVm%8V%8~\}[22XKm&0|mR~#|R|1=Pm,^m1iPm60{P[22WPm&0:mR{1iSmRz@10zm[22VSm1EmGRz1i[mRT,Em@2?TG[22U[m1=`mS26$0|\~22T`m1iLm/4L\~1=LmS24PJ1i\mPJ22X\m1=]m,^m1i]m60{]\|22W]mQ0T/imR|@10|m\{Q0T02Vm1i^mR|,Em@2?|G\z22U^m1=DmS21$0|\~22TDmQ0X/imQ0X'4\~Q0X/=mPJQ0V/imPJ11Iq02Xl&0|lRz#|11UqR|1=|l,^l1i|l40{[22W|l113qR|/ilRT@10Tl\s22V|l1ElG116qR|/ilRs,El@2?sG[22U|l11XqR|/=l$0|\z22T|l11WqR|/il/4|\z1=|lPJB0RYqlPJP8Q0`#8Q0`/El11OqR|@10|lPDQ0f#81Eclp-0R|Q1\&0@xRx$0@Rz$0@Rs$0@RT$0]&0]sQ1`41MQ1a+1zQ1\&0@TRT$0@S2@$0]Q0G$3u-3tJ&0]TS2A63sJ230JmRT&0]z+0y&0]xQ1^Q1_Q1]$0]S2BQ1`-0yT+2S41M41M41MQ1a+1zQ1b40E40EQ1c&0\4P:Q1fP4Q1fI1=P7&0\>S1^P1Q1e&0\<80j4I1=Q1iPvPvPvQ1j21kJmRT+24PyQ1jQ0K$05S0K5kv21|vU60ZvI1PPyPvPvQ1j:1ivT-1dvS2CPyQ0R$0?Rx$05S2DQ1l:2|JTQ0K'p61ivH0QPyPvPvQ1j=kvTS2EPyQ1jQ1l5kvS2FH0QPyPvQ1jQ1m5kvQ1mQ1oQ28$2>63=J5kv60ZvPyPvPvQ1jQ0J$05RT+24PyPvPvPTQ0R#_S28$05S2GPyPvPvQ2DQ0H$05S2HPyPvPvQ2HQ2G'p&1{x$1{$1{#_$1{$1{#_$2I$2Q$1<$1<$0wRx-1kJPyQ1qE{E{E{I1PK1LK1LQ1rQ1ubGbHbIX4JX5JX<JX^JZ0@JZ0AJZ0BJWN20V4I\{g00[ZR{\~S1q1^m7>0{:I[Q1}\}%8>S1}Q2:82?>&0:U133IR~A\U3x11IURx@10xl[\~[[[[[[^4J^5J^<J^^J`0@J`0AJ`0BJ^N|P?1E2mP2PfPjQ1yQ25PqPKP`PLPDQ0\Q0jQ0sQ0tQ0{O@b8Y0~Y0}P1P?O2n2001000000121000000c2=c28c0|c0{c0zc0yc12c2<c27c11c10b|bqc0Wc2;bRc0Vb{b]bzb1b=b>b9b:b;b[bZbDbE:3qHlI06Q23Q1>Q1?3oRHP9I06Q20:0{HqQ22PJP_p+01aRHP\Q25#2R~PnP]J2z1X~nR~13~k+0VA6BHn:0ea~'PP8p+01]R~,UHRx13xk+0Vp+01bRT=6B~:0eaxp+01cS22%HTRxPxPTQ1RQ1QP~Q1EQ1DQ1CFtPxCS%CT%NT%DT%KTQ23Q1~;:?X0M=aMTPMPTPMQ1~P~PQEY%FT%LT%OT%MTM;TPHQ25Q23DcP?Q22Q23'URx13xk+0Vp+01dS20Q25'Up+01eS2IQ2556B60eaP_p+01fS2JQ0XQ2I#2RxQ25Q0VJ2zQ25,XxRx13xk+0VQ2JQ2556B:0eax'PP8Q2J/UHRx13xk+0Vp+01gRz=6BH:0eaxp+01hS2K%HzRxPxPzPwPpPTQ1KQ1IQ1HFtPxCS%Cz%Nz%Dz%KzQ20Q22;:?X0M=aMzPMPzPMQ22PTPQEY%Fz%Lz%Oz%MzM;TQ2JQ2IQ20DcP?Q2KQ22'URT13Tk+0Vp+01iS2LQ20'Up+01jS2MQ2056B60eaPmQ2MQ2J'URT-0FaP[PJp+01kS2N#2S2O>2yazRk1^?mRx'4X6J20xTRS2P-0FaS2QQ2P/1RRs-0Fa14k?X6JPJPJ&3oaRkPkPTPsPJ\J/zkS2RAnq[mRs#;143sS2SeS2TQ2Sp+01lS2UQ2J56BRs#;14[sS2VeS2WQ2Vp+01mS2XQ2K56BRs#;14LsS2YeS2ZQ2YQ29Q2;Q2<Q2=Q0T?vm`S2[1l^m\}S2\Q1UQ1WQ1XQ1[Q1bQ1c&0\1S2]Q1iQ1lQ1l21kJRS2^62xJS2_Q2^'p61ivQ1rQ1ubGbHbIX4JS2`20x?R>0{?R^4JS2aP?p+023Rs#2S2bp+01oRT'XS2cO1b8b=b>b9b:b;bDbEbCL2vQ2Q20FaRS2d'^PaQ2PPRQ2TQ2SQ2WQ2VQ2ZQ2YQ29Q2;Q2<Q2=Q2[Q2\Q1UQ1WQ1XQ1[Q1bQ1cQ2]Q1iPvPvQ2^Q1lPyQ1jQ2_5kvE{Q1rQ1ubGbHbIX4JS2_13R?20x1R#8[^4JS2PP?Q2cQ0mO2b8b=b>b9b:b;bDbEbCQ2TQ2SQ2WQ2VQ2ZQ2YQ29Q2;Q2<Q2=Q2[Q2\Q1UQ1WQ1XQ1[Q1bQ1cQ1fQ1iQ1jQ2^5kvQ1rQ1ubGbHbI%8RP?b8b=b>S2\b9b:b;bDbEbCI2uI1>H1;P<I2s22rm[S2[PmQ2OQ2J'XS2O-0FaP[PJQ2U#2>2yazS2Y/4xX6JQ2O00xRS2Z-0FaS2VQ2Z/1RS2W-0FaQ2Y/4?X6JPJPJPkPkQ2OQ2WQ2RQ26,1qRk#;146kS2ReS2WQ2RQ2X=6BzRz#;14`zRzeS2OPzp+01nS2YQ2L56BRk#;14\kRkeS2SPkQ29Q2;Q2<Q2=Av^mLS2TQ21#8\}S21Q1UQ1WQ1XQ1[Q2`Q2aP?p+024S2a/UTS2`O1b8b=b>b9b:b;bDbEbCL2vQ2VQ2d'^PaQ2ZPRQ2WQ2RQ2OPzQ2SPkQ29Q2;Q2<Q2=Q2TQ21Q1UQ1WQ1XQ1[Q2_Q2PP?Q2`Q0lO2b8b=b>b9b:b;bDbEbCQ2WQ2RQ2OPzQ2SPkQ29Q2;Q2<Q2=Q2TQ21Q2\b9b:b;bDbEbCI2uI1>H1;P1I2sQ2[Q07PJ14\xX6JB1`\LmAnq\mQ24'160YqP1Q0T/4xPJ1^1mRkQ1N,3?%81Q0X=\7lp+025S24Q2JQ2I3o/49p+026S2[?onhS2\1=>m@0Rql'4%8<S21@0g<lAnq:mPJp+029RzQ23Q1~3o/4?%2zS2TQ24'X>0eaIQ0]>1`UmAnqUmQ0]/=mS2S'160Yq_0I_0Fc0P_0O_0E_0D]h]w_0HZ0oJQ1L,3k1^7mS2O#81^9mS2R?\DlQ2aQ2IQ203o1^>mS2W'4Q24Q1y7ohS2`1^<mS2P/=m@0Rql'41^:mS2_Q2_<10l1^4mS2Z/=mS2V,1qPJp+028S2dQ1~;o~/4?Q2dQ2a'U1^Um60eaQ07PJQ0]/4xX6J1^6mRhQ0]<1`mAnqhmQ2S'160YqPW14bxPJPk13?r1^Om?\1lQ1vp+02BRxQ2J'w1=9m'4p+02=S2S,Ux>0ea>1^KmS2c@1`<mQ2c=nqm?n<m60Yq_0J_0G_0C]h_0KZ0pJQ1S,3k1^5mQ2O;\lQ2R$0:p+02ARkQ2I'wQ2W/=m'4%2kS2Wp+02<Rh'XQ2P60eaP2Q2cQ2Z<1`m11q?S2ZQ2V'160YqX6J112:S2P/^mS2R1=?m11qKS2OQ2V'1S2V60YqX6JQ2PQ2ZQ2V'4X6JP:11K4Q2O/1?60YqX6J1^2mS2O/=mS2V,1qS2Z#;Q2Z,46S2ZeS1vQ2ZQ2c?vmNS2c1^Pm/lm\}S2QQ29Q2;Q2<Q2=Q1UQ1WQ1XQ1[Q1bQ1cQ1dQ1e80j1S2eQ1iQ1lQ1mQ0R$05S0R'pS2f'pS2gQ1nQ0R'p61ivQ1rQ1ubGbHbIX4JX5JX<JQ1wQ2?/1760Y?^4J^5J^<JP?PWP\PqO3b8b=b>b9b:b;bCQ2_/=mQ1vQ2ZQ2cQ2QQ29Q2;Q2<Q2=Q1UQ1WQ1XQ1[Q1bQ1cQ1fQ1iQ2CQ1rQ1ubGbHbIQ1qP?b8b=b>b9b:b;bCS1q:2P:mI06Q2R/=mQ2PQ1q82PmI06Q2OQ2_'1B3m2:mI1>Q2VQ1q:2P2mI06Y0JY0GY0CWhY0KQ0`P?Q0oP3PcQ0ZP2N;3kW1Z2:JP1P?O2n2001000000121101000Y0IY0Fc0PY0OY0EY0DWhWwY0HP^P?Q0`PLP\P]PPPVPNP6N>3jW1Z29JP1P?O2n2001000000121101000B1`L`mQ26,1X60YqS26eQ26Q2YQ0aQ2X#2S26Q26Q1RQ1QQ1PPbPbQ13N:3iQ1|Q1Q,wTS2680g?Q0`p+020S1qQ1S;oo>15B1O1Q0NQ0M016G+1jRG500[^LJQ2YQ1RQ1Q3oS1Q#8Q1QQ2YQ1P'w;\l41uP8Q1|Q1qQ1R'w80g?Q0dp+021S1QQ1S7or>15B1O1=00G[^LJQ1R9oToS1PQ1PQ26;\l+0VQ1q%HTS1PQ1PPTPHQ25Q2MQ1SPoQ1RFtQ1PCS%CT%NT%DT%KTQ2UQ2N;:?X0M=aMTPMPTPMQ2NQ2MPQEY%FT%LT%OT%MTM;TQ2YQ2XQ2UDcP?Q1|p+022S1PQ1S'wS2680g?PcAoswpRo>15B1O1=00G[^LJQ1P?oprRHQ26=\Hl+0VP8%8o1wsr=\olQ2a%HsRoPoQ2bQ2IQ20Q2YQ1yPwPpK0HPoCS%Cs%Ns%Ds%KsQ1q?:T?X0M=aMsPMPsPMPTQ2YPQEY%Fs%Ls%Os%MsM;TQ1PQ1QQ1qDcP?Q2`#8Q2\Q2[Q1y'w;\lp+027S2\?o~nQ1|1wz~80g?Q0mQ1{-16BO1=00G[^LJX6JP<PSP[I1>Q1|Q2d/wnRn80g?Q0lB15B`1O1=00G[^LJPnQ1|@0g?1Q0nB15B\1O1=00G[^LJX6JP?1=ZmP]I1>Q1|Q0\/=m80g?Q0mB15BL1O1=00G[^LJg010`p4p710RnP|\?R~&1A1S1{P8B0<71?A9>?7S1yP>P1O1S2`[^29Ro[A99?1S2bP9P1O1[^27B0<971[RpB0<>97\oB2<71?P?n2001000000120000000W?Y0]WMS26Q1{Pp]?`0]~^MnS0MP?PMQ2[Q24'h90M?X0MPMQ24Q2a%7zRnH19PMP?PMQ2[Q24+0Ip+02:S2V#7I0dP=\?S2O&1A7S2_P8P9P1P9P7P?I0dP>P7P1P9P7O1H0aS2P[S2RP9P1P?P7P1O1S2CH0aP>P7P>P9P1I0dR~[S2QP<P9P7P>P9O1H0a\~P9P7P1P?H3eS2cP1n2001000000120000000W?X21WTXM@S2ZQ2OQ2_Q2R]?^21]T^M@S1vP?PMQ2dQ2\+0IP7%7hR~P1O5PMP7P~Q2dQ2\;[7H0aP8Q2S#7R~99M9Q2d=[z9#5Q2V/hz90M>P?p+02?S2h#7Rp99M<p+02;S2i=[h:#5Q2SPhP4P?H2OWsWuP1P?O2n2001000000120000000bsb1WsX0MO4b1Q24Q2a'hRo90M?X0MPMQ2aPsQ2d#7H1960<M%HzRwPwQ2TQ2NQ2MQ2aQ25Q23Q1~K0HPwCS%Cz%Nz%Dz%KzQ2[Q24;:?X0M=JMnB0EMoQ:2}Mz%Fz%Lz%Oz%MzM;TQ0<B09h1?#5S1~P81u1?S23#5%57Ro%51Rn']Rw[Rr%5?S2T,]n1u71S2j#5Rn[RH%59/]o\n23b1?S2kP1n2001000000120000000Xm=Xl=S2lPr^m=^l=S2mP?Q2h&1]?Rn'>RoP9P9PoQ2h&1\?S2nEdX0MQ2V?:z?X0M=JM~R~5mMRoQ2hP?P9P9Q2hP?EyX0M=mM~R~P1O3%5o%5~']P8PrPH21J97\wQ2kP?n2001000000120000000Xm=Xl=S2kPH^m=^l=S2oP?1>knRHP<P<PHPkQ2nEdX0MRH=mMpPkP?P<P<PkP?EyX0MRw=mMpQ06Q2i=:h?X0M=JMpRp9WMHAWMwp1>xnRpP:P:PpPxQ2nEdX0MRpp+02@S2p#7Rw5WMPxP?P:P:PxP?EyX0MS2q=WMw']P1Q2S?:h?X0M=JMwS2r9WMpp+02CRp/>nRwP4P4PwPpQ2nEdX0M%7kRw5WMS2sPpP?P4P4PpP?EyX0M=WMwS2tQ2OQ1{P8AW71?Q1yP9P?O1S2u+04X29,~9S1y[S2vQ2bP7P?O1+04X27,~7AW971Rw[S2bP<P?P9P>P?O1S2wH0aX2>,~>\wB3]71?S2xP1n2001000000120000000W?WTXM@S2yQ2OQ1{Q2v]?]T^M@S2zP?PMp+02DRw/>nRHPIPIPHPwQ2nEdRHX0MQ2hp+02>S2{;:?X0M=aMxS2|P1O4PMP?PMQ2pQ2h;:?X0M%7pI0dS2}004HX2M,~MQ07PMPMP?PMQ2p=:k?X0M%7wS2~I0dS30p+02ERH/>nRrPUPUPrPHQ2nH0^H18X2Mp+02FRr/>nR~P3P3P~PrQ2nEdX0MQ2~5WMP?A:px?X0M=aMrS3199M?S32p+02GS33/>nS34P6Q34Q33Q2n41[S35-0c6H18P8PMP1PMA:wp?X0MQ33#7I0dS36p+02HR~&1]1S37'>RoPXPoP~&1\1S38H0^80OXp+02JS39/>nS3:PYPYQ3:Q39Q2n41[S3;H0=X0M%7~S3<5WMP?A:rH?X0Mp+02IS3=#7S3>5JMS3?99M9S3@p+02KRo&1]>S3A'>S3BP5Q3BPo&1\>S3BH0^80O5Q2ZQ1vP?PMQ3=?[~?S3C#jX0MS3DP:p+02LS3E#7S3FP7O5S3GPMP:Q3FQ33=[~:$0bH0uS3HP8p+02MS3I#7S3J99M4S3KQ3=?[~4$0bS3Lp+02PS3M/>nS3NPKPKQ3NQ3MQ2n41[S3OH0=X0Mp+02NS3P#7S3Q5WMP?p+02OS3R#799MUS3SQ3E?[o3$0bS3TQ2OQ1{P8Q2vQ2bQ1yAW>97[Q2xP?n2001000000120000000W?WTXM@S2xQ2OQ1{Q2b]?]T^M@S2bP?PMp+02TS1y/>nS2vP`P`Q2vQ1yQ2nEdS2vX0Mp+02RS3U#7S3VPMp+02SS3W#7S3X99M?S3YQ2v+04X2MPXQ3V99MXS2vQ3W&1]X'>S3ZP[P[Q3ZQ3W&1\XEdP7P4H0fH1;O4b1WuWJP1P?O2n2001000000121000000bJb1WWWJP1P?O2n2001000000121000000W1XRMP1P?O2n2001000000121101000bjb142;WjP?O1Q2qQ2r5WMQ2sQ2tQ2yQ2zP?PMPwP?PIPIPwP?EyS2rX0MQ2|P1O4Q2}Q2r+04X2M,~MQ07PMQ3020iH?PUB0mUH?H18X2MPrP?P3P3PrP?EyX0MQ2~5WMP?Q32Q3300i?S32P6Q3301H?S2~-0c6H18P8Q36B1G~1XB0mX~1'sQ39P?PYPYQ39P?EyX0MQ3<5WMP?Q3@B1Go>5B0m5o>'sQ2ZQ1vQ3GQ3HP8Q3KQ3LQ3M00i?S3LPKPKQ3M01H?S3KH0=X0MQ3Q5WMP?Q3SQ3TQ2xQ2bP?PMQ1yP?P`P`Q1yP?EyS3HX0MQ3VPMQ3YQ3H+04X2MPXQ2vQ3WPXP[P[Q3WPXEyP7P4H0fH1;O4b1WuWJP1P?O2n2001000000120000000bJb1WWWJP1P?O2n2001000000121000000W1XRMP1P?O2n2001000000121101000bjb141tWjP?O1n200100000021100011000O3b1bjb1Q2S@09h1#5S2teWjX6JQ1~Q2t[^6JQ0`P?P?Q0`PbI0J#|S1~P^P1P1P^Q0`/=mI0J#|S2tQ2h@09>7S2sP=Q0cQ2p@09<9/`?P=B09x4</`?B09px:S3@,`1]rP1B09k:>S3S#5P=B09xk<S3TPCP:P<P?O2H2oWrQ3S#BQ3TP=Q0cQ3@/`?P=B09HwI/`?Q0B=0=1]3P1B09wp4S3@#5Q0B=0=CS3TP8Q23#B%B7S23%B1S3S'P[S2vQ3S%B?S3H'PQ2j#BS2j[Q2j%B9Q23'P[23X1?P1n2001000000120000000Xm=Xl=S2jQ2v^m=^l=S2vP?Q34P3P3Q35H0=X0MA:xk?X0M=aMHS355mMS34Q32P3P3Q2~H0=X0MQ355mMS35P>O3Q34#BQ35#B'PP81>~nS35P6P6Q35P~Q2nEdX0MQ31617MP~P?P6P6P~P?EyX0MQ31617MP{P?Q3:PWPWQ3;H0=X0MA:Hw?X0MQ3<5JMS3<617MPoP?PYPYPoP?EyX0MQ3?617M%7oS3;99M?S3:Q33=[~1#BS31Q2OQ2_P8Q2RQ2QQ2PP<P9P<P>P7I0d[Q2cP?n2001000000120000000W?X21WTXM@S2cQ2OQ2_Q2Q]?^21]T^M@S2OP?PMQ39=:o?X0MP9Q3QQ3Q99M9Q39Q3=;[9R@#jP7P=Q0B&0b?S2QXO=S2PQ1sP@P1E}H0fO5b1WAWJXRMQ3:Q31PMP7PMQ39Q3=;[?S2R#jX0MQ3JI0d[[^RMQ2lQ2mP?Q3P/>nR@PNPNP@Q3PQ2nEdX0MQ3F5mMS3:Q3PP?PNPNQ3PP?EyX0MQ3F5mMR@PIO3Q3:#5%5@']Q06Q3R/>nR@PVPVP@Q3RQ2nEdX0MQ3J5WMQ3RP?PVPVQ3RP?EyX0MQ3J5WMP{P?Q3NP2P2Q3OH0=X0MQ3Q5WMQ2yQ2zP?PMQ3U/>nR@PPPPP@Q3UQ2nEdR@X0MQ3M#7S3OP1O4p+02QS3N#7S3:99M?S31004@X2M,~MQ07PMQ3V99M?S35Q3W/>nR@PSPSP@Q3WQ2nH0^H18X2MP{P?Q1y#799M?S34p+02US2~/>nR@P`P`P@Q2~Q2nH0^H18P8Q2~#7S3299M1S3Yp+02VS3GQ37'>R@PLP@Q3GQ38H0^80OLP{P?p+02WS36#799M9S30p+02YR@Q3A'>S3AQ0TQ0TQ3AP@Q3BH0^40OQ2~Q1y;[<S3BP=Q0cQ3GQ2~;[:/`?S3AP=p+02XS2rQ36;[I/`?P{]AS2}P1Q36Q3G;[4S2|#5S2qQ2rQ36PIP?H2OS3ZQ2rQ36'hS3[90MIS3\PMQ2r,h@S3]p+02^S3^#7S3_99M?S3`p+02`S3aQ37'>S37PZQ37Q3aQ38H0^80OZP{]W]JXRMQ3]p+02]S38#7S3759MS3bp+02_S3cp+02ZS3d/h@S3e$1]'>S3fQ0WQ0WQ3fQ3cQ3e$1\H0^40OQ3ap+02[S3f'>S3g/bZS3hPZQ3gQ3aQ3dH0^S3g<0r?Q3hQ3g+0sP8p+02aS3gp+02\S3h'>S3iQ0\+0GQ0\Q3iQ3gQ3f41[+0qP{P?p+02cS3iQ3^'>Q0]+0GQ0ap+02dS3jQ3c'>Q3jQ3^41[+0qQ1:Q1;P?p+02fS3kQ3g'>S3lQ0`P7O3Q3lQ0`'3P820q1?1E71S3l[S3m1E1?S3n20q71S3o[S3pQ3o1E97[23W1?S3oP1n2001000000120000000XPJX\JS3qQ3m^PJ^\JS3rP?Q0fp+02hS3sQ3i'>Q3sp+02bS3t41[S3uP9O3Q0fQ3u'EQ0fQ1B/=mS3u,1qS3v#;Q13Q3v'4S3weQ3wp+02jS3wQ3j56BS3x#;Q1BQ3x'4S3xeQ3xp+02kS3xQ3k56BS3y#;Q1DQ3y'4S3yeQ3yQ29Q2;Q2<Q2=Q1GQ1C7vmQ1H/lm\}Q1UQ1WQ1XQ1[Q1bQ1cQ2eQ1iPvQ1mQ1lQ0R'pS3y61KvS3zPyPvQ1lQ1m5kvS3{PyQ3{Q3z60ZvS3|K1LQ1rQ1ubGbHbIX4JX5JX<JQ1z,E1S3}1317S3~1379S40117>80g9[[^4J^5J^<JP?p+032S41p+02lS4256BQ0oQ41p+02mS4356BPUP6O5b8b=b>b9b:b;bDbEbCQ1BPcPcQ1BQ1>I0JeO1bab1bkb1WaWkP1P?O2n2001000000121000000bWWWWJPUP?P<P>L2MbAWAQ2|#BS2|Q2xQ2bP?PMQ3c/>nS44Q0WQ0WQ44Q3cQ2nEdS44X0MS45Q3d?:@?X0MQ375JMS46PMPMP?PMQ3fQ3d;:?X0MQ3_I0dS3_Q44+04X2MPUQ4699MUS44Q3^&1]U'>S47Q0ZQ0ZQ47Q3^&1\UEdPVPUP<P1O3S47P>H0fH1;O4b1Q3^/>nS48Q0ZQ0ZQ48Q3^Q2nEdX0MQ2r=:@?S48X0MQ3h#7S495JMS4:5WMQ45Q465mMQ3HXO=S45PKP?H1sQ0B90=CS4;P=PCP=P|P?PuP{n0110500020000X_=Q0CQ0BP?J0AS4<P{20v{?b1S4=c0ZbtWAn0110500020101P?O1bAbQWWWJP1P?O2n2001000000121000000W1XRMP1P?O2n2001000000121101000b3b1W3P?O1Q3LP2P2Q3KH0=X0MQ3Q5WMQ2yQ2zP?PMQ3UP?PPPPQ3UP?EyS3KX0MQ3OP1O4Q31Q3K+04X2M,~MQ07PMQ35Q3W00i?PSQ3W>0mS?H18X2MP{P?Q34Q2~00i?P`Q2~>0m`?H18P8Q3YQ3G@1G1LQ3G>0mL1'sP{P?Q30Q0T:1G@>Q0T@0m@>'sQ3BP=Q0cQ3AP=Q2}P1Q2qQ3ZQ3\PMQ3]Q3`Q3a@1G1ZQ3a>0mZ1'sP{]W]JXRMQ3bQ3cQ3eQ0W41GQ0WQ3cQ3e40m'sQ3aQ3fQ3d'hS3e<1GZS3]Q3aQ3e60mZS3\<0r?Q3]Q3\+0sP8Q3gQ3hQ3f'hS3\+0iQ0\+0GQ0\Q3gQ3\+1H+0qP{P?Q3iQ3^Q38'h+0iQ0]+0GQ0aQ3jQ3cQ3^'hS0]+1H+0qQ1:Q1;P?Q3kQ3gQ3a'h+0iS3\Q0`P7O3Q3\Q0`'3Q3qQ3rP?Q0fQ3sQ3iQ3t'h+1HS3\P9O3Q0fQ3\'EQ0dp+02iS3\Q3j56BQ3\Q3i56BS0`'1=nqm1Ef?X6JP?Q13Q0`;nmS0`Q0vI1>Q0`,EcQ3wp+02eS0`56B=nqmS3]#;Q14Q3]'4S3]eQ3]Q29Q2;Q2<Q2=Q43Q3s56B@1hmqS3]01NlQ3]#8Q1YPBp+02oS3]Q3wPmH0}@0Rql#8[[p+02nS3ZQ3\56BQ3ZQ3s56B'1S2}00CmQ2}#8p+030S2}Q3x56BQ2}Q3w56B'1/lm\}[Q3]Q3\56BS3A00CmQ3A#8p+031S3AQ3x56B/lm\}[Q1UQ1WQ1XQ1[Q3A#2Q4261EaQ1VQ41#2Q43+0hp+033S3BQ3Z'U-0La[[p+034S3Y#2S34Q3]'XS35>08a1VuX3tQ35-0Ka\u^3tQ3YQ3]56BQ1I7vmp+035S35Q2}56B/lm\}Q34Q2}61EaQ1VQ35#2Q3A+0hp+036S34Q41'U-0La[[p+037S3KQ3B'US31>08a1VuX3tQ31-0Ka\u^3tQ1bQ1cQ1^P7Q1fP1Q1eI1=Q1iPvQ0RQ1nQ0I$05S0I'p61KvS31PyPvQ1nQ0R5kvS1nPyQ1nQ3160ZvK1LQ1rQ1ubGbHbIX4JX5JX<JX^JQ2?>1F79Q1w/39Q1x/3>S31Q1x/1<80g>[[^4J^5J^<J^^JP?PBp+038S3LQ41PmH0}Q0vPBQ3LQ3BPmH0}PqPYPNO6b8b=b>b9b:b;b[bZbbbcbdbebfbCbaQ3vPcPcQ3vQ1>/=mS3vI0JeQ13PcPcQ13Q3vI0JeO1bab1bkb1WaWkP1P?O2n2001000000121000000bWWWWJPUP?P<P>L2MbAWAQ2|Q2xQ2bP?PMQ3cP?Q0WQ0WQ3cP?EyRcX0MS2qQ46PMQ3_004cX2MPUQ44Q3^PUQ0ZQ0ZQ3^PUEyQ47P>H0fH1;O4b1Q3^P?Q0ZQ0ZQ3^P?EyX0MQ4:5WMQ2qQ465mMQ45P2P?H1sQ4;Q4=c0YbtWAn0110500020101P?O1bAbQWWWJP1P?O2n2001000000121000000W1XRMP1P?O2n2001000000121101000b3b1W3P?O1n200100000021100011000b3b1c1]Y0YY0ZP1P?O2n2001000000121000000brb1+0vW3Q3@#BQ0B,z=S3@W3n0110500020100P?O1b3bQWrn0110500020001P?O1brbQY1JY1IX6JQ1~Q2tQ2sQ2hQ2{<097'`[[^6JQ2{Q2SQ2VP?CV#5S1~Q2lQ2mP?p,4argHRcQ2pP7O2S2mQ2pQ2hPhP7H0N#jS2lP1O3Q2m#5Q2l#5']Q2kQ2oP?PcPxP>O2S2oPxP4Q2{P>H0N#jQ06Q2o#5PxPkQ2{P>H0N$0bPcPpP<O2#5S2oPpPIQ2hP<H0N$0b']P1Q2oPcPwP:O2#5S2kPwPUQ2pP:H0N$0bS2l<2;?W3P?O1PpPxQ2hP<H0N$0bQ2kQ2lP8Q2QQ3S[S2QQ3H&0b1S2o[S3HQ2oQ23[&3V?S2oP1n2001000000120000000XO=Q2Q^O=P?PHPwPkP4H0NS23P1O2Q23#BP8Q2QQ3HQ3S&0b7[Q2oP?n2001000000120000000XO=Q3H^O=P?Q33PXPpPUH0NS3HQ3HP=Q0cP~PWPwP3H0N/`?P=Q39P5PrPXH0N/`?Q3S_0>P1Q3=PYPHP6H0NS3S#5Q39Q3=PrPXH0NQ45P>Q39P5Q3=PrPXPYP?K3UH1sQ4;Q4<P{Q4;00v?b1b3Y0>Q3S#BQ3@Y0>n0110500020000P?O1c0>bQO2b1b3b141tW3P?O1n200100000021000011000O3b1b3b1Q2hP>Q2iP1CV#5S2leW3XFAQ1~Q2l[^FAQ0fQ1TQ1TQ0fQ0dI0J#|S0dQ0X1@B1S1~Q1~Q0XQ0f/=mI0J#|S0fP=Q2p1@B7S2l609kS2kPcPxP9O2S3@Q0P1@B9S3S+2nQ0=Q3S'b'uS4<Q3SQ2{#eS3H$0D+00Q3SQ3H$0k+00#j'GS3H&2J9S2oQ2{$11+1C#jS2Q/u?'G'u#j'uQ3@Q4<Q3HQ2QQ3S:09xk'u'G'u#j'u'`XO=PcPkP7O2Q0PQ2l+2nQ0=Q2l'b'uQ2lQ2S#eRc$0D+00Q2l&0kc+00#j&2J7Q2S$11+1C#jQ2k'u420'u#j'u,z=Q2l:09k:P>Q2lP1P?O3E}PkP:Q2SP7CVPkQ2pQ2SP7CV'`RceW{W]XFAQ0dQ0fPc[[^FAQ2hP>Q2iPhH1^Q0OQ0tP?O1Q0N$26Rc500S0NPxPkQ2{P1CVP=Q0cPpPxQ2hP7CV/`?P=PHPwPkP>CV/`?P=P0P1PcPpP<O1n0100000020000=00cP=P0Q33PXPpP:CVPcPwP:O1S0On0100000020000=00c]`]AP1PwPpQ2pP9CVS0d#5A00ccP=PCP=P0P?PcQ0On0100000020000=00cXO=1z0cS0OPrP6PxP<CVS0fPIP<P1O2E}W`WAQ0d#BPxP>O1=00cQ0fP=P=P=P0P?PcPHP4O1n0100000020000=00cP?Q0OP1n0110500020000bQW`WAn0110500020000P?P7O2bAbQQ2C=00cS0OeW`X2AQ0NQ0O[^2APjQ1TQ1TPjPfI0J#|S0NQ0WQ1~Q1~Q0W1=jmI0J#|RjP=PwPpQ2pP7CVS0fP=P0P?PcPxP9O1S0dn0100000020000P=P0PHPwPkP9CVPcQ0dn0100000020000500XO=P=P0Q0fPcPkP7O1n0100000020000,z0PwPUQ2pP7CVP<P7P1P?O3E}P>P7O1Q0{P7O1500S0feW{W]X2AQ0NQ0f\j[^2AQ2WPsQ1PPhH1Y&1AEP=P0Q0jQ1TQ1TQ0jPiI1rQ2wQ0{P?O1n0100000020000X2AP0^2AS0jQ1T/EgQ2h,wHQ1T5\g']S2WQ0lQ1~Q1~Q0lPgI1rP=Q0cQ0mQ2lQ2lQ0mQ0lI1r/`?P=Q0o1@B>Ri'bS0lQ0oQ0n629iRj'G/`?P=P0P1P3P<O1Q0}P<O1S0Nn0100000020000Q0N500]VP1Q0nQ3SQ3SQ0nQ0m'1S0mH0=S0N#5Q0l@0rj?Q0l00sjP8Q0q1@B<S0l+0GQ0lQ0qQ0o'1+0qP6P:O1Q0~P:O1500P?Q0r1@B4S0o+0G1@BIS0fQ0sQ0r'1+0qQ1:Q1;P?Q0v1@B3S1;P7O3Q0vQ1;'3Q3qQ3rP?1@BXS3rQ0{Q0u'1RjP9O3Q3r/EjQ0w=nqmRj#;14gjRjePjQ3WQ3I56BRj#;Q0w/4jRjePjQ1yQ3R56BRj#;Q0z/4jRjePjQ29Q2;Q2<Q2=Q0}Q0x7vmQ0~/lm\}Q0~Q0}'1S3q00CmQ3q#8Q10Q11'1S1:/lm\}[Q1UQ1WQ1XQ1[Q3dQ2~'US0s-1IaQ1VQ3f#2S0dQ3G'XS2k#8Q3h#2S3@Q36'X-0La[[Q38#2S4<Q2r'XRj>08a1VuX3t20Kaj\u^3tQ14/=mS3H/1qS2Q01NlQ2Q#8Q1Y1=dmS23@0Rql#8[[Q1400CmQ14#8Q23#8\}[Q3^#2S2mQ3d'XS2t-1IaQ1VQ3c#2S2sQ3f'XS30#8Q3a#2S2|Q3h'X-0La[[Q3gQ38'URj>08a1VuX3t20Kaj\u^3tQ1bQ1cQ1hP9Q2]P9Q1fQ1d80j9I1=Q1iPvPvQ0KQ2GQ2D'pRj+24PyPvPvQ2GQ0KPyPvQ0KQ2G61KvQ0K9kvj62mvPy21|v<S0KH0QE{I1PQ1rQ1ubGbHbIX4JX5JX<JXN|Q2?,E71319S2?1E>7Q31']P:[[[^4J^5J^<J^N|P?Q0WP^O1Q1HP^O15001@B^Q1JQ1<POPVQ0TO7b8b=b>b9b:b;b[bZbbbcbdbebfbDbEbCbab1bkb1WaWkP1P?O2n2001000000121000000bVWVQ0N#BQ0|P>O1,z0WVn0110500020100P?O1bVbQQ2CQ0xP1O1500RjeW`X2AQ2WPj[^2AQ0jQ0|P?O1=00cQ0O[^2AS0OP_Q3=Q0|21q97S2WCAS2CP8Q1}P<P?P?P>H13Q11216B1RjO1=00c[^LJ:0l9lQ2113>lP:P?P?P<H13P<PjO1=00c[^LJ41uP?%8:S21PIP?P?P4H13Q13PjO1=00c[^LJ:0l:lP8134lPUP?P?PIH13Q14PjO1=00c[^LJP3P?P?PUH13PUPjO1=00c[^LJ:0lIl-0VUP?13UlPXP?P?P6H13Q15PjO1=00c[^LJ%8XS1}136lS0NPWP?P?PXH13RgPXPjO1=00c[^LJS1H'PP<Q0NQ1HP1P6PjP7P1P?O2O2Z1DgXLJH1pH1pY1MY1LP1P?O2n2001000000121000000W1Y1KP1P?O2n2001000000121000000P_Q39P721q>9S1HCARgeY1=Y1EY0\XnJXoJQ0jQ0OQ2CPg[[_0\^nJ^oJQ0zP?O1=00cRgQ0nQ1~Q1~Q0mH0=P=P=P=P0P?P3P9O1Q0}P9O1n0100000020000=00cP?PIP7P1O2P1n0110500020000bQQ2`=00cRjeW`X2APj\g^2AQ26Q0MP?PEB14_~>&0`?S2`%2~S0mQ0mQ2VPzPpCgQ2VPzPpP?K0MXUEQ33#2S0n+1XQ2`Q3=#2RgPgQ2iQ2VPwCgQ2iQ2VPwP?K0MXUEQ0m+1X,<?Q2ZQ1vP?PEQ2`%2oRgPgQ2SPhPrCgS0jQ2SPhPrP?K0MXUEP7Q39#2RjP1O51<7j&0`7S0OPjPjPhQ2iPHCgPhQ2iPHP7K0M+04P81<9g&0`9S2CPgQ0jQ2SPhPrP9J02+1JP_Q3IPUP>CAP?Q3I#2,<<&0`:S0jQ3P#2RgPgQ2pQ2hQ3=CgQ2pQ2hQ3=P:J02+1JQ3MQ14614_S0NQ3R#2Rg+1WQ3N#2S0W,<?P_Q3WQ15P1CA[^2E[Q3M#2Rj,<?P_Q3UPdP1CA[^2EQ3N>14_e01Wj[Q0N>2<EgPeP4P1J2HP_Q3MQ14P4CA&0`IRgPjPjPxPkPoCgPxPkPoPIJ02Rj<2l1%5g%5j']Q06&0`US0N#5S2DQ0WQ0WPpPxQ3ECgPpPxQ3EPUJ02#5P_Q3WP5P3CAP?&0`3S1h#5S2qPEQ1y#2S46,<?&0W1S47P_Q36Q1=P7CAP_Q2rPKP9CA]@]B]7P6g04HoRjQ0DB1V71?S44%2@S3_'<B1V971$0WS3bP_Q3hQ1BB1V>97S3vCAB1V<>9S4>P=P|P?P{Pun0110500020000S4?X_=Rg;r1P{P_Q3^P\B1V:<>S4@P?Dqb1W@WBW7Z0q;Y0rWFP7P1P?O321b1?S4AQ36#2S4B'<21b71$0WS4CP_Q3dQ1?21b97S4DCA21b>9S4E?rg1P{P_Q3hP`21b<>S4FP?Dqb1W@WBW7XX;XFjP1P?O2Q0DB1a71?S4GQ3_'<B1a971$0WS4HP_Q3hQ1BB1a>97S4ICAB1a<>9S4J?rg1P{P_Q3^P\B1a:<>S4KP?Dqb1W@WBW7Y0kXX;XFjP7P1P?O321q1?S4LQ4B'<21q71$0WS4MP_Q3dQ1?Q2WCAPPP>P9P[PKP?O5W@WBW7XnJXoJP1P?O221l1?S4NQ4B'<21l71$0WS4OP_Q3dQ1?21l97S4PCA21l>9S4QQ4?Z23=S4?;r1P{P_Q3hP`21l<>S4RP?Dqb1W@WBW7XPJX_;P1P?O2B1U71?S4SQ3_'<B1U971$0WS4TP_Q3hQ1BB1U>97S4UCAB1U<>9S4VQ4?;r1P{P_Q3^P\B1U:<>S4WP?Dqb1W@WBW7XnJXoJX_;P7P1P?O321e1?S4XQ4B'<21e71$0WS4YP_Q3dQ1?21e97S4ZCA21e>9S4[?rg1P{P_Q3hP`21e<>S4\P?Dqb1W@WBW7XX;XFjP1P?O2P9P7P1P?H1cS4]Q0d'<P>P9P7P1H1c$0WS0dP_Q3^Q1DP<P>P9P7H1cS4^CAP:P<P>P9H1cS4_?rg1P{P_Q3aQ0TP4P:P<P>H1cS4`P?Dqb1W@WBW7Z0m;Z0hjZ0l;Z0gjP9P7P1P?O4B1T71?S4aQ3_'<B1T971$0WS4bP_Q3hQ1BB1T>97S4cCAB1T<>9S4d?rg1P{P_Q3^P\B1T:<>S4eP?Dqb1W@WBW7Z0iJXX;XFjP7P1P?O321g1?S4fQ4B'<21g71$0WS4BP_Q3dQ1?21g97S4gCA21g>9S4h?rg1P{P_Q3hP`21g<>S4iP?Dqb1W@WBW7XX;XFjP1P?O2n0110k000:3010410r10q201041073010410710k2010:109201081063010810:109201041074010g10l10h10m3010410710i20104107P<P?P9O3WBP?O1Q3U#2S4jQ4jPwPpQ3ICgS4kPwPpQ3IP3J02#5Q3W#2S4lQ4lPHPwQ3PCgS4mPHPwQ3PP6J02Q2TXO=S2TP?Q4lPHPwQ3PP6I2jS4nQ4lPHPwQ3PP6I2iI1mQ4n#5Q2~Q1<PNQ46PXPrPHQ3RQ1MP>P?Q0yQ1T/E1S4nQ36Q3N'wQ1T5\1']PKP1O1Q1AP1O1500[^2AX6JPOQ2~21SrHS4o+0_Q0xI06N<2hb}W}P?O1n200100000021100010000c0;b@Y0;W7P1P?O2n2001000000121000000b7b1W7XUEO4b1P_Q33P9Q2`Q0nQ0nPzQ2dPxCgPzQ2dPxP?K0MXUE%2r+1XH1:eP_Q33P9P>H1:S0neQ0nQ26Q0MP?PEQ3=>14_UQ2`P4P4Q1qPTQ2YCgQ1qPTQ2YP?K0MXUE01X:Q2`PIPIQ1QQ1qPTCgQ1QQ1qPTP?K0MXUE01X4,<?Q2ZQ1vP?PEQ2`P3P3PsQ1PQ1QCgS0MPsQ1PQ1QP?K0MXUEP7PUP1O51<7UQ0OPUPUQ1PQ1QQ1qCgQ1PQ1QQ1qP7K0M+04P81<93Q2CP3Q0MPsQ1PQ1QP9J02+1JP_Q3PPYP>CAP?1<<XQ0jPWPWQ2[Q24Q2aCgQ2[Q24Q2aP:J02+1JQ3N>14_WS0j01WY1<?OP_Q1yPOP1CA[^2E[1<?5P_Q3WP5P1CA[^2EQ3U>14_Y01W5[Q0j>2<EYPUP4P1J2HP_Q3NPWP4CAQ2ZQ1vP?PEQ2`Q4lQ4mPHPwQ3PP?K0MXUEPUQ4jP9O5Q4j,<UQ0NQ4jQ4kPwPpQ3IPUK0M+04P8Q4l,<3Q1hQ4lQ4mPHPwQ3PP3J02+1JQ46,<6P?Q2~#2,<X&0`WQ3G#2S46Q46P~Q33Q3NCgP~Q33Q3NPWJ02+1JP1WuW7P1P?O2n2001000000120000000b7b1Q0W,<IQ0NPOPOPzQ2dQ2\CgPzQ2dQ2\PUJ02S0W<2l7Q2DQ0W#5']Q06Q2qPNPNQ2VPzQ2dCgQ2VPzQ2dP3J02#5P_Q2~PPP6CAP?&0W6PE1<?KQ47P_P@PPP7CAQ3_,<9P_Q3fP]P>CA]S]@]B]7PXQ0DQ44/<LQ3bP_Q3^P\Q3vCAQ4>Q2m'<Q4@?rg7P{P_Q3gQ0ZB1V4:<P?Dqb1WSW@WBW7Z0q;Y0rXFjP7P1P?O3Q4A/<[Q4CP_Q3hP`Q4DCAQ4EQ3@'<Q4F?rg7P{P_Q3cQ0X21b:<P?Dqb1WSW@WBW7XX;XFjP1P?O2Q0DQ4G/<LQ4HP_Q3^P\Q4ICAQ4JQ2m'<Q4K?rg7P{P_Q3gQ0ZB1a4:<P?Dqb1WSW@WBW7Y0kXX;XFjP7P1P?O3Q4L/<[Q4MP_Q3hP`Q2WCAQ1HQ3@'<P`P<P>PDP^Q3^Q1D614_S1HQ4<+1WQ2s,<?P_Q3gQ1GP1CA[^2E[Q2m,<?P_Q3aQ1FP1CA[^2EQ3cQ1E614_Q2m+1W[Q1HQ4<62<EQ1E21q<>P?J2HO5WSW@WBW7XnJXoJP1P?O2Q4N/<[Q4OP_Q3hP`Q4PCAQ4QQ3@'<Q4RQ4?;r7P{P_Q3cQ0X21l:<P?Dqb1WSW@WBW7XPJX_;P1P?O2Q4S/<LQ4TP_Q3^P\Q4UCAQ4VQ2m'<Q4WQ4?;r7P{P_Q3gQ0ZB1U4:<P?Dqb1WSW@WBW7XnJXoJX_;P7P1P?O3Q4X/<[Q4YP_Q3hP`Q4ZCAQ4[Q3@'<Q4\?rg7P{P_Q3cQ0X21e:<P?Dqb1WSW@WBW7XX;XFjP1P?O2Q4]/<]Q0dP_Q3aQ0TQ4^CAQ4_Q2|'<Q4`?rg7P{P_Q3iPZPIP4P:P<H1cP?Dqb1WSW@WBW7Z0m;Z0hjZ0l;Z0gjP9P7P1P?O4Q4a/<LQ4bP_Q3^P\Q4cCAQ4dQ2m'<Q4e?rg7P{P_Q3gQ0ZB1T4:<P?Dqb1WSW@WBW7Z0iJXX;XFjP7P1P?O3Q4f/<[Q4BP_Q3hP`Q4gCAQ4hQ3@'<Q4i?rg7P{P_Q3cQ0X21g:<P?Dqb1WSW@WBW7XX;XFjP1P?O2n0110k000:3010410r10q201041073010410710k2010:109201081063010810:109201041074010g10l10h10m3010410710i20104107P:P?P>P9O4WBP?O1PVPVQ2iQ2VPzCgQ2iQ2VPzP6J02#5P2P2PhQ2iQ2VCgPhQ2iQ2VPXJ02Q2TP?P2PhQ2iQ2VPXI2jRjP2PhQ2iQ2VPXI2iI1m%5jQ36P2P[PKPWQ2SPhQ2iP5P<P?Q0qQ4nQ2S,w@Q1T5\1']P\P1O1PSP1O1500Rj[^2AX6JQ0|/=mS4nQ1TQ0r'EQ0rQ1T7\1']Pj[^2AX6JQ1TQ0p'EQ0pQ0}/=mQ1T3\']Q11Q1~Q1~Q11Q0~I1rP=Q0cQ10Q2lQ2lQ1:H0=/`?P=Q13PiPiQ13Q12'1RjH0=/`?P^P<O1R^P=P0P1P^Q1CP<O1n0100000020000500]VP1Q12Q3SQ3SQ12Q10I1rR^#5Q0TP>O1,z0WV%B^P\P>Q13PiPiPjH13S10Q14Q0l'bRjQ0lQ14Q13429R^%5jP^P8Q17Q18Q1620G97[Q19P?n2001000000120000000XPJX\JS19Q18^PJ^\JS18P?Pe1@B:S17AnqemRZ#;Q0{/4ZS1CeS1:Q1CQ3c=6B@RZ#;14eZS0~eS0qQ0~Q3aQ3f56BRZ#;Q15/4ZRZeS4BPZQ29Q2;Q2<Q2=Q1M?vmdS4iQ1=/lm\}S4hQ1UQ1WQ1XQ1[Q1bQ1cQ2>Q1iPvQ3{21|v>60ZvS4gPyQ3{H0QQ1rQ1ubGbHbIX4JX5JXN|S4f13?1S4b/P7Q3~[^4J^5J^N|S4eP?1@B5S4dQ1?Q1@41FQ4dQ1?P3O4b8b=b>b9b:b;bDbEbCO3b1P8Q3mQ3pQ3l20q97[Q3oP?n2001000000120000000XPJX\JS3oQ3p^PJ^\JS3pP?Q17Q14,1eS3lQ1:Q1CQ0qQ0~Q4BPZQ29Q2;Q2<Q2=Q4iQ4hQ1UQ1WQ1XQ1[Q1bQ1cQ2eQ1iPvQ0KQ1lQ2f61KvS2f60ZvPyQ2fH0QQ1rQ1ubGbHbIX4JX5JX<JXN|S4hQ1w,E?S1w,P9Q1x,E1[^4J^5J^<J^N|S1xP?Q1?Q4d'3Q1@Q1?Q4dP3O5b8b=b>b9b:b;bDbEbCO3b1H0f42g1sj^PeQ17Q17Q3lH0=Q45P7P?H1sQ4;Q4=bVbtWiQ10#|eQ13=nqmR^#;Q0v/4^R^eP^Q38Q3656BR^#;Q13/4^R^eP^Q3^=6B@R^#;14e^R^eP^Q29Q2;Q2<Q2=Q1JQ147vmQ1</lm\}Q1<Q1J'1R^00Cm%8^Q1=Q1M'1/lm\}[Q1UQ1WQ1XQ1[Q3j#2Q3c61EaQ1VQ0`#2Q3a+0hQ3kQ3g'U-0La[[p+02gR^Q3t'URe>08a1VuX3t20Kae\u^3tQ1?@1hmqRe01Nl%8eQ1YQ3u@0Rql#8[[Q1?00CmQ1?#8Q3u#8\}[Q3s#2Q3j61EaQ1VQ3\#2Q0`+0hQ3wQ3k'U-0La[[Q3x/U^Re>08a1VuX3t20Kae\u^3tQ1bQ1cQ2eQ1iPvQ1mQ1l61KvQ3yQ1m5kv62mvPyQ3|-1dvH0QQ1rQ1ubGbHbIX4JX5JX<JQ3nQ1z/31']Q3~B1F719S3n'PP{[[^4J^5J^<JP?Q1D/=m1@BKS1DPdP2O4b8b=b>b9b:b;b[bZbbbcbdbebfbDbEbCO3WVn0110500020001P?O1bVbQPLP1O1PPP1O1500eW`X2AQ36Q2i'wQ0tI06Q36Q2S;ohQ0pI06N<2hb}W}P?O1n200100000021100011000c0;bSb@Y0;W7P1P?O2n2001000000121000000b7b1W7XUEO4b1P_P~PIQ2`P:P:PTQ2YQ2XCgPTQ2YQ2XP?K0MXUE01X<H1:eP_P~PIP<Q2YQ2XQ2UH1YH1:REePE222JJRE$1ARePMPEQ3=#xRjQ3<CfRZPMPEPj&0T~S2`1hwpS0p>0EMQS1z5?MS3|CfS3y5?EPMPEQ39#xS3uQ3?CfS3?PMPEQ3uQ3=$0TS1?CfS0vQ39@1oHw5?E5?ES1090e?X?ePePMPEPjQ2`CfS3lPMPEPjQ1zCf5?ES4iQ3?=?E?Q1050eX?ePeQ3=Q0p+1QRwQ3?Q0v=?E?5?EQ1050eX?ePeQ3l9?EZ=?EwS10A0e??X?eQ10,zeQ3l=?Ew9?EZS10PEPZQ3lPwH3OE}&2:E9?Ew23NEwE}Q4i9?EZQ1050eeQ3yPMPEPjQ2`Q1zI2FE}PMPEPjQ3<Q3|5?MCfPMPEPjQ3<Q3|I2FE}PMPEPj%H~RjPjQ0mQ2VPzPpPTQ2YQ2XK0HPjCS%C~%N~%D~%K~Q3<Q3|%F~%L~%O~%M~M;TRj#7&0Tj5?MCfQ1050eeQ3=/RYQ1050eRjePjPePMPEQ3uQ3>CfQ0v5?ERjPMPE%xoRZQ39#7RwCfS0vPMPEPZQ39H0US105?ES3|90e?X?e1zejPMPEQ3uQ3>Q1?5?MCfPMPEQ3uQ3>Q1?I2FE}Q39Q3='R=0ejRjePjPePMPEPZPMQ33?[r?S1?#jS3>X0MS3uPwJ0oS3<Q10B1oorHS0m5?ES1z5?ES2`%I?S3yQ3E/Ro#I'3X?ePeQ3|PMPEQ3E#xS4iPMQ33=:~?S3lX0MQ3;J0oS3?PMPEQ4iPoH0URjQ3EQ33<1orS0p5?E5?E#IQ3y'3X?eQ3<#IS3yQ1z#IS4B'1PMPEQ4iQ3;Cf=?Ej#IS0~,3?X6JQ10#IS0qQ0m#I'1Q3?#IS3?Q0~7\?X6JQ0v#IS0~Q0q'1Q3?%IjS0qQ0p#IS0p'1'1Rj/3?X6JQ3yPMPEPZQ3>#jX0MRZ=JMwS3>Cf#I'1Q0q,1?,3jX6JPMPZ20IrHRZQ1?$3LXRMPwI3K&1AMRjQ3>AJMZw30PjPMQ33PrQ3;H19S3>PMPEQ3I#xS1?PMQ3DQ3FJ0o#IS3DPMPEQ1?Q3EH0U#IRZQ3IQ33,h~S0q+1Q#IS3y'1'1S3?Q3DPMPEQ1?P?Cf#I'1/1Z'3X?jQ3>-0XMS1?$1RQ0p'^Q3?Q3D/1?/1Z'3X6JQ2yQ2zP?PMQ33-0I~Q3FQ1MO4PMP?Q3JQ3CH0aX2M,~MQ07PMPMP?Q3QQ2RH0aX2MQ1]PMQ39Q3=Q3QH19-0XM+12P?PMP?Q3OQ3E?[o?H0aP8Q3:99M1Q3IQ3E;[1#5Q1]PMQ3PQ3IQ3VH19-0XM+12P?Q3X99M9Q3MQ3R;[>#5Q2cQ2OP?PMQ3UQ3N+0IS3XP:Q3G#7RZA9M:ZQ3UQ3N;[:P7P1H0fO5b1PMP<PMQ3NQ3M+0IQ32I0dQ3X=JMZPjQ05PMQ2~Q1y'hS0590M?X0M>0<M?Q3GQ2~;:?S3X#jX0M%7@S325JM=0j1A9M37Q1]20XM9+12]i]x]yP?Q1yQ3W'hS3V90M?X0M>0<MQQ2~Q1y;:?S3Q#jX0MQ2r#7S2R5JM=0jQA9MUQP{Q1]20XMQ+12P?n010000000WiWxWyQ3[90M?X0MB0EM1?60<MQ48#jX0MQ495JMB0EM7150jB0EM9799MWQ23,1qRZ#;Q0w/4ZRZePZQ3aQ3d56BRZ#;14dZRZePZQ3gQ3h56BRZ#;Q1J/4ZRZePZQ1]20XM:S0w$0@S23+12Q0G$0wRZQ0w$1RS0G/1ZS49'3Q1]PZ%;ZS48Q23Q4911?ZX2JQ0wQ0GQ0G#;H3IJ2dQ0w$2cQ0G#8Q29Q2;Q2<Q2=Q1AQ1J7vmQ1@/lm\}Q1UQ1WQ1XQ1[Q1bQ1cQ2]Q1iPvQ2FPy21kJZS2FQ1lQ2F'p5kvH0QQ1rQ1ubGbHbIX4JQ1|111Z,3Z[^4JP?20XMW$1RP:O2b8b=b>b9b:b;c0jH3HbDbEbCQ1]B0EM>9-0XM+12eWiWxWyX?jX0MP1P?O2n10110300020021100103PDPXP1O3b?biWAWJP1P?O2n2001000000121000000W1XRMP1P?O2n2001000000121101000c1Cb1Q1]Q1?+12Q3IQ0q+3GQ3y#8Q0t=nqmRj#;14fjRjePjQ3RQ3=56BRj#;Q0t/4jRjePjQ3M=6BoRj#;Q0u/4jRjePjQ1]PMQ3EPoQ3OH19-0XMRj+12&1RjRf,3ZS3OQ1]PZQ48PjPf%;fJ2dP>H3JQ3OPMQ3IQ3EQ3:H19-0XMRf$2c&1Rf#8Q29Q2;Q2<Q2=Q0yQ0{7vmQ4n#8\}Q0|Q0y'1Rf00Cm%8fQ3q/lm\}[Q1UQ1WQ1XQ1[Q2r#2Q3W61EaQ1VQ3_Q1y+0hQ0s-0La[[Q2k>08a1VuX3tQ2k-0Ka\u^3tQ12@1hmqRf01Nl%8fQ1YQ2Q/il#8[[Q1200CmQ12#8Q3H#8\}[Q3@Q2r61EaQ1VQ4<00h@Q2t-0La[[Q30>08a1VuX3tQ30-0Ka\u^3tQ1\Q2@$0@Rf$0@$0@$0]Rj&0]fRf+0yQ1`-0yjQ0L$2I$2QS0L$2Q$1<$1<$1<$1<$1<$1<$0w-30JRjQ2A-0yfQ2A+2S-0yf+0yQ1`-0yf-0yj+2S41MQ1a+1zQ1b40EQ1cQ1fP>&0\XPXQ1fI2eP7&0\6P4Q1fP:Q1fI1=P1&0\3Q1f80jXP<&0\UP9&0\IQ1f80jXI1=I1=Q1iPvPvPvQ1jQ1oPyPvPvQ0>Q0?Q0?Q0@I3EPyQ1jQ1p5kvH0QE{PyPvPvQ2EPyQ1jQ0H#_S0H#_$05Rj5kvH0QPyPvPvQ2FQ0IPyPvPvQ1k#_$05RfQ0J$0?$05S0J/pj+2fPyPvPvQ1jQ0RPyPvPvQ28$0?$0502ffPyPvQ1jQ0H$05S0H5kv21|vY60ZvPyPvQ1jQ0J5kv21|v560ZvPyPvPvQ1jQ27$05S27+24PyPvPvQ0HQ27'pQ1pPyPvPvQ2^Q2GPyPvPvQ2^Q2HPyQ2gQ1lQ0IQ0R62|J'pQ1m'p5kvE{E{E{I1PK1LI1PE{I1PE{K1LQ1rQ1ubGbHbIX4JX5JX<JX^JZ0@JZ0AJZ0BJZ0eJZ0fJZ0bJZ0cJZ0dJXN|Z0a|Q1Z\t%8W\}13Z<B0{WXYQ2114W5Q1}/PV20VOK&0:5A\5Ol13R5RR11WY1^5Y,1X/1W5\X\R[[[[[[[[[[[^4J^5J^<J^^J`0@J`0AJ`0BJ`0eJ`0fJ`0bJ`0cJ`0dJ^N|`0a|P?Q2:,3qQ15/ElQ15/=mQ0xPqQ3aQ4o+0_PdQ15Q2sQ3d'XQ30PMQ3fQ3dQ3c#7S30H19-0XM$1RQ3aQ3e+1QS3e#IPMPEQ3a#xRRQ3cH0US2s#IPMPEPRPMQ3hQ3f;:?X0MQ30J0oS4o#IP4P3PYPNPVQ0zQ0yQ0|Q1<Q14Q1KQ1NOJb8b=b>b9b:b;b[bZbbbcbdbebfc0jc1ObDbEbCb1c0NPMPEQ4iQ3>Cf#IQ3EQ33PrQ3>PVI3DI06Q3l#jX0MQ3;5JMP?E}bxQ0~Q3u>3MowI06Q3|#IQ0vQ10+2GI06Q4BQ10Q0m+2GI06Q2`#IQ3<Q1z+2GI06Q39,RoRwP?E}1RoORRP1E}%IR%Iw'3Q3IQ3E'RS1z02E?#5S3<Q2yQ2zP?PE&28?RwQ3SQ3S&2=?RR+0z41nRZXgEQ3RQ3P'RP1O4PEP?Q3MQ3R'RPZH0aX2E,~EQ07PEPEP?Q3NQ3M'R20ziR:0OwiH0uX2EQ0lQ0l00zR61nwXgEQ3N/RS5WEP?PEP?Q3WQ3U'RQ17Q1700zR60OwH0uP8Q1yQ3W'R99E1&281Q0oQ0o&2=1+0z40O1@BUS0oQ0o00zR61nwXgEQ2~/R\5WEP?Q3GQ2~'R99E9&28>Q1;Q1;&2=>+0z40OQ2xQ2bP?PE1@BWS2bQ2b00zR61nwRwXgE1R@DRDPEPEP?Q3dQ0X'RPwH0aX2EP:A9E:D&28:Q3rQ3r&2=:+0z41nPePMPE%x@RwPMQ3QX0MQ2RJ0oPMPEPwQ2rH0URRQ3V-1Q@5?E5?EA9E4?X?eRZPeQ2r,R@PZP7PMPEPwQ2RCf=?ERRRPYJ0AA9E:RPMPEQ3d#xRRPMQ3XX0MQ32J0oRwPMPEPRP@H0UR@Q3dQ05+1Q5?ERZ5?E99E4PEP4PwA9E4ZH0P+2LP|Q0823C?1Xv|X2|S05g0?JfS3XPMPEQ3f#xRePMQ36Q3G;:?X0MQ3d#7S2RJ0oS3VPMPEPeQ3dH0URfQ3fQ3GQ2~41oS2~5?ERj5?E99EIPEPIQ3VA9EIjRjH0PP?K3BY0SPEPwPZP4H2NPMPEPRQ32CfRR=?E@99E4PEP4PRA9E4@H0PRZ+2LPMPEPeQ2RCfRe=?Ef99EIA9EIeS2RA9EIfRe']<3A?Y0SPEPRP@P4H2NP?O2PZPePEPIQ2~H2p-2LjP|P|^p|RjQ08P|P|Q08P|P|P|Q09H4WRZH2CR@Q06Pj\|P|P|\|Q08P|P|Q08Q08H2CRRH2CQ06g0?K\P|PjQ08P@H2CQ0AP|PjQ08Q08Q08-4V|RjPRP@P|P|Q08Q08PjQ08PZP|Q08Q05Q3XH4UL3@L3@K4TPEPUPMPEQ3h#xRZQ2rQ36;:?X0MQ3f#7Rj5JMJ0nR@P|Q08Q08g0<CO64S|P@H4RPMPEPZQ3fH0URRQ3hQ36Q3G41oRw5?E99EUA9EURS36PEPUPwH2pRwP?N;4NY0SPEPfQ2~PIH2NQ06Q2RPe1]@wP?PEPUPMPEPZPjJ0nQ01p4p710RjQ02Q1{\1RZQ2_P8P9P?P>P9P7P1J0nP:P?P9Q2w99<7H0uX2<,~<S2w[S1{P<P?P7Q2u99>1H0uX2>,~>P>P1P<P>P9P7J0nRw[S2uP4P?P>P<P?O199:9H0uX2:,~:\wP>P9P7P1P?I4MS01P1n2001000000120000000Xv7W?WTWpWMQ02Q2_Q1{^v7]?^TZ]p^MjP?PMPEQ3^#xQ37P6P1O6Q3`PEPXQ3cP?H03'PX2M,~MQ07PMPMP?Q30PEPWQ3aP?H03H0uX2MPEPWQ4oPEPWQ2sQ3e99EWH0PH0PP?PMP?Q3g#7PEP5Q3tP?H03H0uP8Q3t#799M1PEPOQ3iP1H03PEPNPMPEQ3j#xRwPMQ3aQ3c;:?X0MQ3i#7J0oPEPNPMPEPwQ3iH0UPEPNQ3jQ0]H03H0PH0PP?Q3j#799M9PEP2Q3kP>H03Q3tQ3g;[<P=Q0cQ3iQ3t;[:/`?P=Q0`Q3j;[I/`?PEP`PMPEQ3x#xS3tQ3k=:^?X0MQ3w#7Rw5JMR@CfPEP`PMPEQ3tQ3wH0UPEP`Q3xQ3kQ0`'hReH03H0PH0P]AP1Q3jQ3i;[4Rf#5Q0`Q3jPIP?H2OQ0`Q3j'hS3j90MIPMPeQ3x#7RR99M?PEP\Q43P1H03PEP]PMPEQ3Z#xS3iPMQ3wQ3\;:?X0MQ43#7J0oPEP]PMPEQ3iQ43H0UPEP]Q3ZQ3\Q3s'hH03H0PH0P]Y]JXRMA9MewPEPLQ42Q3k,h^H03PEP\PMPEQ43#xReQ3\Q3s;:?X0MQ425aMJ0nPEP\PMPEPeQ42$0TJ0nRePEP\Q43Q3s/h^H03Rw']B1tew?41tWYWJPUP?P<P>L2MbAWA%BfPEP[PMPEQ3w#xRfQ3kQ0`;:?X0MQ3\5aMJ0nPEP[PMPEPfQ3\H0UPEP[Q3wQ3jH03H0PQ02Q2_P8Q1{Q2uQ2wP<P7P:P<P>P9J0n[Q01P?n2001000000120000000Xv7W?XTZWpXMjQ02Q2_Q2u^v7]?^TZ]p^MjP?PMPEQ3tP@P`PMPMP?Q3s?:^?X0MRj=JMRPEPLQ42P?H03H0uX2MPUA9MU@PEP`Q3xPUH03Q2cQ2OP?PMPjP3PRA9M3RQ3k=[^3R^#jP:P=Q0BQ2PQ1sP^P7E}H0fO5b1P>H1pH1;O6b142;WAn0110500020101P?O1bAbQWYWJP1P?O2n2001000000121000000W1XRMP1P?O2n2001000000121101000bYb1WYP?O1Q36PEP3PMPEQ38#xR^Q4:J0nPEP3PMPEP^Q3h$0TJ0nR^PEP3Q38Q3[H03RR']B2;^R?41tWYP?O1n200100000021100010000O2bYO2bYPDP5E}P1H0fH1;O4b1Y0XWYP1P?O2n2001000000121000000W1XgEP1P?O2n2001000000121101000bsb1Q3P/R202E1#5REeWsZ0UAQ3<PE[`0UAQ3IQ3EPoQ39Q3=PHJ4LQ1zQ3=+25Q3PQ3IQ3EPoQ39PrJ4KQ3PQ3I'R#IQ3I#F'3Q3RQ3PQ3IQ3EPoQ33J4JQ3MQ3RQ3EP?CV#5Q1~Q3I#e$0D+00#5Q2lQ3P#e$0k+00#BQ2oQ3R$11+1C#5Q1yQ3W<1xi#BQ3UP<O1=00G[[[[[^FAQ04Q3MQ3RQ3PQ3IQ3EQ3NPSQ3RQ3PQ3IDcP~Q3xQ3w#H$1yQ3\42bg03<7RE$1AS3IQ3x#H$2a&2:ES3P30P_Q43Q43Q42Q3\Q3wH1^Q42#2H1:&1}AS3\Q3w$3<&26AS3R30Q3]Q3Z#OQ3x42RQ00Q42$3;p,3FS0S3N30Q2}#M#BQ3\Q3Z$2~Q3R30[222AARE$1AS3MQ3Z#e$1f&4I_S3Z30Q3]#e$2Ap,5LIMITS04'4Q3YQ3B#CQ2}#e$0D42`Q35Q3Y#DQ3A#eRD$1f&0DD5?E42_Q3Y#C+0pQ41#e$0D$3:Q3B$39B2^AA?,@BRD$0:B2[AA?,@BRRQ0L$0wR^'i$0|1iD^$0|Q0P$4GQ0=9\RD80lRRR'P41uXgES0=Q3Y#e$0D60<EPRXgES3YQ35$1160<EQ3K#e$0k-00?#5Q3L#e$0D-001#5[^6JQ0Fg03=;RR&4F?RDg03>;30g03?;90RD']S35p+03=Rj0381p+039#eR@$0k59E[WPp+03:#C+0pQ0Fg03@;90RDS0Pp+03?RD&4E7S0L56BRRQ1TQ1TPR&4D7S3B96BDI0JQ1~p+03<S41#eRR$0k+00#B&2J1S3UQ41$11+1C+04[^FA[WPp+03;S3W#C+0p&1f@&0D@5?E$37Q41#N'3p+03>R@#D1i?^$0|S1yQ3W#eR^$36,@B,3?&1f^&0D^5?Eg03A;S1z<32?41u80l?Z0QJ,~J&2\^%L@-1DD50A&35R,@B&2\R,@B'3&2Bjp+03@S3=#K'3p+03BRjp+03ARR'R#I%FR'3p+03CR@/Rj025Dp+03ERDp+03DR^PRP?CV#5Q1~%ejS3<$0DRZ+00#5Q2l%e@S36$0kS3[+00#BQ2o&11^+1C#5p+03IS38p+03HS3h<1xi#Bp+03GRfP<O1=00G[[[[[^FAp,4SINVS4:PDPjO2p+03FRwPdP^P@PjP\%HDRePePDQ3KQ34Q3=Q42Q3xQ3wFtPeCS%CD%ND%DD%KDA:jR?X0M=aMDPMPDPMPRQ3=PQEY%FDS3=%LD%OD%MDM;TRe#HS3w$1y>2bw^e%HdS34$1y>2bw^eQ3IQ3P'zQ3IQ3w$2aQ3P30eQ3IQ34$2aQ3P30eQ0{P_PwPwPePjP@H1^%2eH1:eP_PwPwPdPjP@H1^%2dH1:eP[Q3\&3<jQ3R30R_eP_ePS%Oe>2Rwje%Od>2RwjePPQ00&3;jQ3N30R_eP_ePK%Me#BQ3\&2~@Q3R30R_[e%Md#BP_[eP2Q3MQ3<$1fS3RQ3Z30R_eP_ePVQ3<$2AQ04'4R_eP_ePN%CeS04>2`wZe%CdR_>2`wZePO%DeQ3R=?EZS3R62_wQ04+0pe%DdQ3R62_w00p_eP5&3:ZS3ZeQ3ZePY&39jS3ZeQ3ZePWQ0=>0<EZRZePZePXQ3Y&11j60<ERZePZeP6Q3[-00?#5%e^R^$0DS3[-001#5[^6JRZePZeP3Q0FQ35Q3h0381&0k^59E[WPR^Q04+0pe20p^_ePUQ0FQ0PQ38Q0L56BR^Q1TQ1TP^Q38Q3B56BI0JQ1~%ew$0k+00#BQ3U&11wS3B+1C+04[^FA[WPR^Q04+0pe20p^_ePIQ3R$37R^%Ne'3e%Nd,3^eP4%HwR^P^PwQ3LQ3KPRQ43Q42Q3xFtP^CS%Cw%Nw%Dw%KwA:@j?X0M=aMwPMPwPMPjPRPQEY%Fw%Lw%Ow%MwM;TS3x#DQ1yQ36$36,@B,3?Q36$1fQ36$0D5?EQ1z<32?41uRE80l?Z0QJ,~JeQ15#D@0l?EZ0QJ,~JeP:Q3<$2\RE%Le-1Dw50Ae%Ld-1Dw90AEeP<Q3<$35,@B1@BE'3REePEeP>&2BjRE%Ke'3e%Kd,3EeQ22=nqmRE#;Q1S/4EREePEA6BfRRR#;Q22/4RRRePRQ3h=6B@RR#;Q2I/4RRRePRQ29Q2;Q2<Q2=Q2KQ207vmQ2L/lm\}Q1UQ1WQ1XQ1[Q1\Q1_Q2BQ1`41MQ1a+1zQ1b40ERRQ1cQ1dP1Q1fP9Q1gI2eQ1iPvPvQ27Q1mPyPvPvQ1lQ27PyQ3{E{E{Q1rQ1ubGbHbIX4JX5JX<JQ16Q2?Q40[[^4J^5J^<JP?p+03OREp+03NS2?'RR^#IR_Q2?#FQ1>,RE#IQ0zQ0}O5b8b=b>b9b:b;bDbEbC1RweS0}#IRZQ3='3e%Fe,3Ze1RwdS3=#I%Fd'3eQ0:1RwDPjQ15,Rf025@Q0r&23f-4AAQ38$2399A?Q1~Q0E'i$0|[^0Ap+03JRd$2399A?22E^1#5[^0Ap+03KR^$2399A?p+03LS0E$11-1C1#5[^0A&2B^%e^$2A7\_p+03PR_Q1B'RQ0EP>P9p+03MRZ$2399A?Q11P1P>P1P?O2O2Y0XZ0UAP1Q2X=nqmRe#;Q25/4eReePep+03QS25=6B^Re#;Q2X/4eReePep+03RS11=6BZRe#;14TeReePeQ29Q2;Q2<Q2=Q1PQ2Y7vm1=smS1B#8\}Q1UQ1WQ1XQ1[PRQ1cQ1fP7Q1^Q1f80j>P1Q1eI1=Q1iPvPvQ1lQ0H'pQ0RPyPvPvQ1mQ0HPyQ1nE{E{Q1rQ1ubGbHbIX4JX5JX<JX^JA\?97137>Q31[[^4J^5J^<J^^JP?p+03YS31p+03XRR'R#Ip+03URe#e$2AQ31Q1L'R#I&2BePUQ1JO6b8b9b:b;b[bZbDbEbCK4@Y1[Y1ZY1YY1XY1WP>P9P7P1P?O5n200100000015112a12]12^12`12_Q0}025jS0}eQ0}eQ3=025jePfQ15P@P?CV#5S15Q1~Q3[+00#5S3[Q2l%eD$0k+00#BS2lQ2oQ3B+1C#5S3BQ1=>1x^i#BS1=1>ZnRjQ17Q17PjPZQ2nEdX0MRj&0T^S17PMPfPwPQH1~S2o5?M5mMQ45P?Q179mMjQ2o9mMj'uS1~PMPjQ17Q2oH4?I1mQ1~#BQ2jQ2vP?1>EnRjQ0fQ0fPjPEQ2nEdX0MRj&0TZ5mMS0fPMQ38Q3hPQH1~9mMjRjP1O3Q0f#B%Bj'PP81>_nR8Q0oQ0oP8P_Q2nEdX0MR8Q2?$0T617MPMPdQ38PQH1~:17M8PZPUO1=00GP?Q11/>nR81@B6RjPjP8Q11Q2nEdX0M&0T_617Mp+03SR8/>nRnQ3rQ3rPnP8Q2nEdX0MPMPZQ0EPQH1~617MQ2?,>8RnQ3rQ3rPnP8PZEdRZQ0B'uQ45P?PZ&4=ZI1m%BZQ1QQ2bQ2bQ1QQ1qI0JS2bQ1P1@BYRZ'bRnQ1PQ1Q629ZRj%5nPjQ19Q18P?PsQ4dQ1B,1qRj#;Q2J/4jS2JeS1BQ2Jp+03WRjQ2556BRn#;14snS18eS19Q18A6BR8Rn#;Q24/4nS24eS1QQ24Q29Q2;Q2<Q2=Q2dQ2a7vmS2a1=zmS3r#8\}S2?Q1UQ1WQ1XQ1[Q4fQ4eP?1@B`RnQ2i81FhPnPhP3O4b8b=b>b9b:b;bDbEbCO3b1Q3oQ3pP?Q4dQ1P,1sQ1BQ2JQ19Q18Q1QQ24Q29Q2;Q2<Q2=Q2aQ2?Q1UQ1WQ1XQ1[Q4hQ1xP?13hnQ2iPhPnP3O5b8b=b>b9b:b;bDbEbCO3b1H0f42gA6Be_RsA6BeE:29Zs80OZe1>e_RsPZPsPePEH0^80OZRZePZp+03VRZQ25'>REQ4dQ4dPEPZP_EdQ45P7P?H1sQ4;Q4=b|btWiQ2b#|R_eP_Pep+03TR_Q25PYCVP=Q0cPZPeQ11P5CV/`?P=PRPjP_PNCV/`?PZPVO1=00G]AP1PjPZP8POCVR8#5Q13PNP?P5PYPWP:1@BNR_:1xRj#BeO6WA%B8Q2K04<_Q2K/3_R_%|_+34Q0;Q2L1@BV'3R_%|_PjP2O1=00GP?Q2M1@B2'3S2MQ1DQ2NQ2\;nmR_+4;Q1D/E_R_%|_+34Q0;1@BPQ2UQ2d/=mS0;41FR_%|_p+03ZR_PSO1=00GP?1@BSQ2XQ3r41FS3rQ1S1@B[Q2Y+0xS1SQ2i=nqmR8#;S2XQ2Y/48S2UeQ2Up+03_S1DQ3156BR8#;S31Q2i/48S2\eQ2\p+03`R8p+03[Re56BRE#;S2LQ2S/4ES2KeQ2KQ29Q2;Q2<Q2=Q2p?vmhS131lkm\}S11Q2p,1kRE00CmS0c%8E11px/lm\}[S25Q1UQ1WQ1XQ1[p+03fS2bp+03aS4='URE-1IaS4;Q1Vp+03gS45#2S4dp+03bS1x+0hp+03hS4h#2S2?p+03cS2a'X-0La[[S24p+03iS1Q#2S18p+03dS19'XRs>08a1VuX3tS2J20Kas\u^3tS1BB1hrmqRs01NlS1P%8sQ1Y1=~mRs@0Rql#8[[S3p20CrmS3o%8r%8s\}[S4ep+03jQ2b'URs-1IaS2bQ1Vp+03k#2Q45+0hp+03lQ4h'U-0La[[S4hp+03mQ1Q'URr>08a1VuX3tS1Q20Kar\u^3tS45Q1bQ1cQ2eQ1iPvQ2fPyPvQ1mQ1l5kvPyQ1jQ1lQ1m62xJRr5kvQ0R:1Kvr60ZvK1LQ1rQ1ubGbHbIX4JX5JX<JQ1wQ1620x79S0RQ0R<10>[[^4J^5J^<JP?Q39/=mS1wQ2{Q0a,@BS0aPOP2O5b8b=b>b9b:b;b[bZbbbcbdbebfbDbEbCO2P~Q2YQ1S615BO1=00GAnqhmR~#;14T~R~eP~A6B8_R~#;14h~R~eP~Q4=p+03\R~56BRh#;Q2{/4hRhePhQ29Q2;Q2<Q2=Q2S9vkm1lxm\}Q1UQ1WQ1XQ1[Q1bQ1cQ2>Q1iQ1lQ1m/pr61ivQ1rQ1ubGbHbIX4JX5J20x?1:0{?1^4J^5JP?Q2dQ0Z,@BO2b8b=b>b9b:b;bDbEbC20xnT:0{nTQ1q1@BLRnQ1q+0x'1Po216B?O1=00GX6JP1PnP?I06Q39216BnO1=00GPA1@B\-16BQ3EP?O1=00GXOAP?P\24>B\J0APoP\O1=00GQ1xQ4=p+03^RoP]CVP=P0P?PcP8Q0TO1n0100000020000=00GXO=P?P3H2]Q1DP]O1=00GP?c0?c0?c0?b1c0?Y0[P?O1Q3r#|PoQ1RP_P[CVQ2TPSPop+03]RcP_P[CVRnQ1NP[PUQ2XQ2UQ31Q2\Q2LQ2KQ29Q2;Q2<Q2=Q13Q11Q0cQ25Q1UQ1WQ1XQ1[Q4;Q24Q2JQ1BQ1PQ3pQ3oQ4eQ2bQ4hQ1QQ45Q1bQ1cQ2eQ1iPvQ3z-1dvPyQ0KQ3z60Zv-1dvH0QQ1rP?P7Q1sQ1tH31RTbGbHbIX4JX5JX<JXN|Q3}P{[Q3n,P>P{[[^4J^5J^<J^N|P?Q2{Q0a'3Q1wQ0aQ2{POO5b8b=b>b9b:b;b[bZbbbcbdbebfbDbEbCO3I1m%5nQ1DPoPeP`CVQ2TP?P4H2]Q3TP=Q0BPgQ0CPCP?J0ARCP{PoP\O1=00G00v?b1b]b]Y0[P?O1n200110n00021110311107c0nY0NP?O1Q2M#|PeQ1OPjPKCVQ2TP2PeP_PjPKCVRjQ1IPKP:Q0;,1qR_#;Q2N/4_A6B~ZRZ#;Q2d/4ZA6BcRRc#;Q2V/4cQ29Q2;Q2<Q2=Q2S?vmzQ2{/lm\}Q2{Q2S'1Rz00Cm%8zQ2pQ2h'1/lm\}[Q1UQ1WQ1XQ1[Q2a#2>1EaoQ1VQ19#2Q1D+0hp+03eRo/U8-0La[[B08aE1VuX3t20KaE\u^3tB1hpmqRE01Nl%8EQ1Y1=HmRH@0Rql#8[[20Cpm%8p%8H\}[Q4dQ2a61EaQ1VQ2?Q19+0hQ18/Xo-0La[[B08as1VuX3t20Kas\u^3tQ1bQ1cQ2>Q1iPvQ3{-1dvPyQ4g-1dvH0QQ1rPTbGbHbIX4JX5JXN|Q4bP{[Q3~/P9P{[[^4J^5J^N|P?Q0\,@BRBQ2iQ33/=m41FPBQ2iPOO4b8b=b>b9b:b;b[bZbbbcbdbebfbDbEbCO3I1m%5jP~PePRPPCVQ2TP?P>H2]Q3TPCP{PeP[O1=00G00v?b1b]b]Y0NP?O1n200110n00021110311107c0nWAn0110500020001P?O1bAbQc1\b|W|WqP1P?O2n2001000000121000000bqb1bqWqY0WY0VW{W]XFAPfQ3xP@P?CV#5Q3[Q2lQ3B%HdRePePdQ41Q3WPDQ3AQ2}Q3]FtPeCS%Cd%Nd%Dd%KdA:fw?X0M=aMdPMPdPMPwPDPQEY%Fd%Ld%Od%MdM;T>1x^i#BQ38P<O1=00GRG[[[[[^FAR0eP0eQ15Q3[Q2lQ3BQ1=PG[[[[[^FAeP?Q4:PwP@O2R@eP@eNP4:Y1{Y21Y1tY1fY1iY1yY1hY1|Y1~Y1nY1vY1uY1pY1gY20Y1zY1mY1sY1qY1xY1}Y1kY1jY1lY1oY1rY1wP\PLP`P[PSPPPKP2PVPNPOP5PYPWPXP6P3PUPIP4P:P<P>P9P7P1P?OKn50000010000001K112S12N12K12H12F12G12Y12T12M12O12I12V12[12C12L12Q12R12J12Z12X12D12U12E12B12P12\12Wc1@c16c1>c1?c15c14c13c1<c1;c1Uc1Nc1Vc1Tc24c1Rc1Sc1Qc18c19c0sc0tc0Rbyc0Mc0MY1bWuP1P?O2n2001000000121000000W1Y0MP1P?O2n2001000000121000000b1c1Hc0vc0uY0JY1GP1P?O2n2001000000121000000b1Y0IY1FP1P?O2n2001000000121000000b1c0Pc0Fc0Oc1_Y0GY0EP1P?O2n2001000000121000000b1bwbhc0Dc0pc0oc1AY0CWhP1P?O2n2001000000121000000W1WwP1P?O2n2001000000121000000b1c0Kc0Hc1Pc1:c0^b1c0_b1c0`b1Y0`WKP1P?O2n2001000000121000000bKY0_WKP1P?O2n2001000000121000000bKY1aWKP1P?O2n2001000000121000000bKY0^WKP1P?O2n2001000000121000000bKY1`WKP1P?O2n2001000000121000000bKWtWKP1P?O2n2001000000121000000bKQ0k#;H1pW1PbP?P1K49c1BW1WKQ0h#BQ0SQ0i50FPFQ0SQ03Q0<P|P?P{Pun10110T00021000000X_FRuQ0CQ0eP?J0AP{Q0g00v?bzW1WKn0110500020100P?P7O2bKbQW1Y0<Z26JP?O1Q0UQ0^#2Q0V&26JR|H1?Q0SQ0V60>FPFQ0SPuQ0CQ0_P?J0AP{Q0b00v?bzW1Y0<n10110T00021110200P?P7O2c0<c0TW1W~Z1dJP?O1Q0UQ0X#2P]P|H1?Q0S>0>F\PFQ0SPuQ0CQ0YP?J0AP{Q0[00v?bzW1W~n10110T00021110200P?P7O2b~c0TW1Y0=Z2@;Z2?JZ2>;P1P?O2n2001100000121108102W0P1P?O2n2001100000121100108P?P7O2c0=b0W1Y0LZ1eJZ1c;P1P?O2n2001100000121108102P?P7O2c0Lb0b1W1Y17Y0RX\;XO;Y25Y0xY1^Y22Y0wo"). Qed.

#[using="argH_agree SINV_agree"] Lemma havocbrk_sound : forall E cs R FULL model lo hi cs',
  cs_ok E cs R FULL model -> node_havocbrk nx0 cs lo hi = Some cs' ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok E' cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros E cs R FULL model lo hi cs' HC H. unfold node_havocbrk in H.
  destruct (xlo (kn cs) (a_brk cs)) as [l|] eqn:Hl; [|discriminate].
  destruct (xhi (kn cs) (a_brk cs)) as [h|] eqn:Hh; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-.
  apply andb_prop in Hc as [Hc H2]. apply andb_prop in Hc as [Hf H1]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (xlo_sound SEGS E _ (kn cs) (a_brk cs) l (co_know _ _ _ _ _ HC) Hl) as L1.
  pose proof (xhi_sound SEGS E _ (kn cs) (a_brk cs) h (co_know _ _ _ _ _ HC) Hh) as L2.
  destruct (fresh_ok_parts cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (v := nxt cs). set (E' := ext1 E v (vm_brk (m_vmmaps model))).
  assert (Hag : env_agree v E E') by apply ext1_agree.
  pose proof (cs_ok_agree E E' cs R FULL model Hag Hf HC) as HC'.
  exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
  assert (Hv : edenot E' (EVar v) = vm_brk (m_vmmaps model)) by (cbn [edenot]; unfold E'; apply ext1_at).
  pose proof (co_brk _ _ _ _ _ HC) as HB0.
  set (cs' := ACS _ _ _ _ _ _ _ _ _ _ _).
  assert (HMr : Mr E' cs' model FULL = Mr E' cs model FULL) by reflexivity.
  assert (HA : allowA E' cs' = allowA E' cs) by reflexivity.
  destruct HC'; constructor; unfold cs'; rewrite ?HMr, ?HA;
    cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn mk_ss s_regs s_log s_know s_pc s_next] in *;
    try assumption; try reflexivity.
  - (* [comment removed for export] *) constructor; [|exact co_know0]. cbn [kentry_ok]. rewrite Hv, HB0. lia.
  - (* [comment removed for export] *) symmetry. exact Hv.
Qed.

(* [comment removed for export] *)
#[using="argH_agree SINV_agree"] Lemma intro_sound : forall E cs R FULL model lo hi cs',
  cs_ok E cs R FULL model -> node_intro nx0 cs lo hi = Some cs' ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok E' cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros E cs R FULL model lo hi cs' HC H. unfold node_intro in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-.
  apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [Hc H2]. apply andb_prop in Hc as [Hf H1].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
  destruct (fresh_ok_parts cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (v := nxt cs). set (E' := ext1 E v (Z_to_bv 64 lo)).
  assert (Hag : env_agree v E E') by apply ext1_agree.
  pose proof (cs_ok_agree E E' cs R FULL model Hag Hf HC) as HC'.
  exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
  assert (Hv : bv_unsigned (edenot E' (EVar v)) = lo).
  { cbn [edenot]. unfold E'. rewrite ext1_at. unfold two64 in H3. apply u_small. lia. }
  set (cs' := with_ss _ _).
  assert (HMr : Mr E' cs' model FULL = Mr E' cs model FULL) by reflexivity.
  assert (HA : allowA E' cs' = allowA E' cs) by reflexivity.
  destruct HC'; constructor; unfold cs'; rewrite ?HMr, ?HA;
    cbn [with_ss a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn mk_ss s_regs s_log s_know s_pc s_next] in *;
    try assumption; try reflexivity.
  - (* [comment removed for export] *) constructor; [|exact co_know0]. cbn [kentry_ok]. rewrite Hv. lia.
Qed.

(* [comment removed for export] *)
Section Rename.
  Variable m : list (nat * nat).
  Variables fw bw : list (option nat).
  Hypothesis Hfw : mk_fwd m = Some fw.
  Hypothesis Hbw : mk_bwd m = Some bw.

  #[using="Type"] Lemma mk_fwd_spec_gen : forall m0 t, mk_fwd m0 = Some t -> forall s d, nt_get t s = Some d <-> In (s, d) m0.
Proof.
    induction m0 as [|[s0 d0] rest IH]; intros t H s d; cbn [mk_fwd] in H.
    - injection H as <-. unfold nt_get. cbn. split; [destruct s; discriminate | tauto].
    - destruct (mk_fwd rest) as [t0|] eqn:E0; [|discriminate].
      destruct (nt_get t0 s0) eqn:Eg; [discriminate|]. injection H as <-.
      rewrite nt_get_set. specialize (IH t0 eq_refl).
      destruct (Nat.eqb_spec s s0) as [->|NE].
      + split.
        * intros X. injection X as <-. left. reflexivity.
        * intros [X|X]; [congruence|]. apply IH in X. congruence.
      + rewrite IH. cbn. split; [tauto|]. intros [X|X]; [congruence|exact X].
  Qed.
  Lemma mk_bwd_spec_gen : forall m0 t, mk_bwd m0 = Some t -> forall s d, nt_get t d = Some s <-> In (s, d) m0.
  Proof.
    induction m0 as [|[s0 d0] rest IH]; intros t H s d; cbn [mk_bwd] in H.
    - injection H as <-. unfold nt_get. cbn. split; [destruct d; discriminate | tauto].
    - destruct (mk_bwd rest) as [t0|] eqn:E0; [|discriminate].
      destruct (nt_get t0 d0) eqn:Eg; [discriminate|]. injection H as <-.
      rewrite nt_get_set. specialize (IH t0 eq_refl).
      destruct (Nat.eqb_spec d d0) as [->|NE].
      + split.
        * intros X. injection X as <-. left. reflexivity.
        * intros [X|X]; [congruence|]. apply IH in X. congruence.
      + rewrite IH. cbn. split; [tauto|]. intros [X|X]; [congruence|exact X].
  Qed.
  Lemma fw_in : forall s d, nt_get fw s = Some d <-> In (s, d) m.
  Proof. exact (mk_fwd_spec_gen m fw Hfw). Qed.
  Lemma bw_in : forall s d, nt_get bw d = Some s <-> In (s, d) m.
  Proof. exact (mk_bwd_spec_gen m bw Hbw). Qed.

  Definition ren_env (E : env) : env :=
    Env (fun w => match nt_get bw w with Some s => ev E s | None => ev E w end) (eb E).
  Definition ren_ok (v : nat) : bool :=
    match nt_get fw v with Some _ => true | None => match nt_get bw v with Some _ => false | None => true end end.

  Lemma edenot_rename : forall E e, evars_all ren_ok e = true -> edenot (ren_env E) (erename fw e) = edenot E e.
  Proof.
    intros E e. induction e; cbn [evars_all erename edenot]; intros H;
      try reflexivity;
      try (apply andb_prop in H as [H1 H2]; rewrite (IHe1 H1), (IHe2 H2); reflexivity);
      try (rewrite (IHe H); reflexivity).
    unfold ren_ok in H. destruct (nt_get fw n) as [d|] eqn:Ef.
    - cbn [edenot ren_env ev]. destruct (nt_get bw d) as [s|] eqn:Eb.
      + apply bw_in in Eb. apply fw_in in Ef. pose proof (proj2 (fw_in _ _) Eb) as Ef'.
        assert (s = n) by (apply bw_in in Eb; apply bw_in in Ef; congruence). subst s. reflexivity.
      + exfalso. apply fw_in in Ef. apply (proj2 (bw_in _ _)) in Ef. congruence.
    - cbn [edenot ren_env ev]. destruct (nt_get bw n) as [s|] eqn:Eb; [discriminate|reflexivity].
  Qed.
End Rename.

Section RenameCS.
  Variable m : list (nat * nat).
  Variables fw bw : list (option nat).
  Hypothesis Hfw : mk_fwd m = Some fw.
  Hypothesis Hbw : mk_bwd m = Some bw.
  Variable gb : nat.
  Hypothesis Hgb : (nx0 <= gb)%nat.
  Hypothesis Hm : forallb (fun p => Nat.leb gb (fst p) && Nat.leb gb (snd p)) m = true.

  Let ER := edenot_rename m fw bw Hfw Hbw.

  #[using="m Hbw Hm"] Lemma ren_agree : forall E, env_agree gb E (ren_env bw E).
Proof.
    intros E. split; [|reflexivity]. intros n Hn. cbn [ren_env ev].
    destruct (nt_get bw n) as [s|] eqn:Eb; [|reflexivity].
    apply (bw_in m bw Hbw) in Eb. exfalso.
    pose proof (proj1 (forallb_forall _ _) Hm (s, n) Eb) as X. cbn [fst snd] in X.
    apply andb_prop in X as [_ X]. apply Nat.leb_le in X. clear Hgb. lia.
  Qed.

  Lemma uE_rename : forall E e, evars_all (ren_ok fw bw) e = true -> uE (ren_env bw E) (erename fw e) = uE E e.
  Proof. intros. unfold uE. rewrite (ER E e H). reflexivity. Qed.

  Lemma regs_ok_rename : forall E sr R, forallb (evars_all (ren_ok fw bw)) sr = true -> regs_ok E sr R -> regs_ok (ren_env bw E) (map (erename fw) sr) R.
  Proof.
    intros E sr R Hsr HR r. rewrite (HR r). unfold sr_get. destruct (bv_eqb r 0); [reflexivity|].
    revert Hsr. generalize (ridx r) as i. clear HR r.
    induction sr as [|e t IH]; intros i Hsr; [destruct i; reflexivity|].
    cbn [forallb] in Hsr. apply andb_prop in Hsr as [He Ht].
    destruct i as [|i]; cbn [map nth]; [symmetry; exact (ER E e He) | apply IH; exact Ht].
  Qed.

  Lemma eb_ren : forall E, eb (ren_env bw E) = eb E.
  Proof. reflexivity. Qed.

  Lemma kentry_ok_rename : forall E M K, kvars_all (ren_ok fw bw) K = true -> kentry_ok SEGS E M K -> kentry_ok SEGS (ren_env bw E) M (krename fw K).
  Proof.
    intros E M K HK Hk.
    destruct K as [[ab ak] w v|[ab ak] n|[ab ak] n k|lo hi|ae am|re rlo rhi|[ab ak] wn|[b1 k1] dn1 [b2 k2] dn2|[ab ak] n fc|[ab ak] n];
      unfold krename, arename in *; cbn [kvars_all kentry_ok a_base a_off] in *;
      repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H as [? H] end;
      unfold flat, estart, elenZ, adenot in *; cbn [a_base a_off] in *;
      rewrite ?eb_ren; rewrite ?(ER E) by assumption; exact Hk.
  Qed.

  Lemma know_ok_rename : forall E M k, forallb (kvars_all (ren_ok fw bw)) k = true ->
    know_ok SEGS E M k -> know_ok SEGS (ren_env bw E) M (map (krename fw) k).
  Proof.
    intros E M k. induction k as [|K rest IH]; intros Hv Hk; [constructor|].
    cbn [forallb] in Hv. apply andb_prop in Hv as [H1 H2]. apply Forall_cons_iff in Hk as [HK Hr].
    cbn [map]. constructor; [apply kentry_ok_rename; assumption | apply IH; assumption].
  Qed.

  Definition pvars_all (l : list (expr * expr)) : bool :=
    forallb (fun p => evars_all (ren_ok fw bw) (fst p) && evars_all (ren_ok fw bw) (snd p)) l.

  Lemma allowA_rename : forall E cs nx,
    pvars_all (a_vis cs) = true -> pvars_all (a_ghost cs) = true ->
    allowA (ren_env bw E) (rename_cs fw cs nx) = allowA E cs.
  Proof.
    intros E cs nx Hv Hg. unfold allowA. cbn [rename_cs a_vis a_ghost]. rewrite <- map_app, !flat_map_concat_map, map_map. f_equal.
    apply map_ext_in. intros p Hin.
    assert (Hp : (evars_all (ren_ok fw bw) (fst p) && evars_all (ren_ok fw bw) (snd p))%bool = true).
    { apply in_app_iff in Hin as [Hin|Hin]; [exact (proj1 (forallb_forall _ _) Hv p Hin) | exact (proj1 (forallb_forall _ _) Hg p Hin)]. }
    apply andb_prop in Hp as [H1 H2].
    unfold allow1, sh_lo, sh_hi, prename. cbn [fst snd]. rewrite !(uE_rename E) by assumption. reflexivity.
  Qed.

  Lemma existsb_map : forall (X Y : Type) (f : X -> Y) (P : Y -> bool) l, existsb P (map f l) = existsb (fun x => P (f x)) l.
  Proof. intros X Y f P l. induction l as [|x r IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.
  Lemma existsb_ext_in : forall (X : Type) (P Q : X -> bool) l, (forall x, In x l -> P x = Q x) -> existsb P l = existsb Q l.
  Proof. intros X P Q l H. induction l as [|x r IH]; [reflexivity|]. cbn. rewrite (H x (or_introl eq_refl)), IH; [reflexivity|]. intros y Hy. apply H. right. exact Hy. Qed.

  Lemma in_allow_rename : forall E cs nx, pvars_all (a_vis cs) = true ->
    in_allow (ren_env bw E) (rename_cs fw cs nx) = in_allow E cs.
  Proof.
    intros E cs nx Hv. apply functional_extensionality. intros z. unfold in_allow, in_vis, in_sh. cbn [rename_cs a_vis].
    rewrite !existsb_map. f_equal; apply existsb_ext_in; intros p Hin;
      pose proof (proj1 (forallb_forall _ _) Hv p Hin) as Hp; apply andb_prop in Hp as [H1 H2];
      unfold sh_lo, sh_hi, prename; cbn [fst snd]; rewrite !(uE_rename E) by assumption; reflexivity.
  Qed.

  Lemma in_ghost_rename : forall E cs nx, pvars_all (a_ghost cs) = true ->
    in_ghost (ren_env bw E) (rename_cs fw cs nx) = in_ghost E cs.
  Proof.
    intros E cs nx Hg. apply functional_extensionality. intros z. unfold in_ghost. cbn [rename_cs a_ghost].
    rewrite existsb_map. apply existsb_ext_in. intros p Hin.
    pose proof (proj1 (forallb_forall _ _) Hg p Hin) as Hp. apply andb_prop in Hp as [H1 H2].
    unfold prename. cbn [fst snd]. rewrite !(uE_rename E) by assumption. reflexivity.
  Qed.

  Lemma hid_rename : forall E cs nx model, pvars_all (a_vis cs) = true ->
    hid (ren_env bw E) (rename_cs fw cs nx) model = hid E cs model.
  Proof.
    intros E cs nx model Hv. apply functional_extensionality. intros a. unfold hid, vis.
    rewrite (in_allow_rename E cs nx Hv). rewrite <- (argH_agree E (ren_env bw E) a); [reflexivity|].
    eapply env_agree_le; [apply ren_agree | exact Hgb].
  Qed.

  Lemma maps_match_rename : forall E ms l,
    forallb (fun m0 => evars_all (ren_ok fw bw) (am_base m0) && evars_all (ren_ok fw bw) (am_len m0)) ms = true ->
    maps_match E ms l -> maps_match (ren_env bw E) (map (mrename fw) ms) l.
  Proof.
    intros E ms. induction ms as [|[mb ml mk] ms IH]; intros l H HM; cbn [maps_match map] in *; [exact HM|].
    cbn [forallb am_base am_len] in H. apply andb_prop in H as [Hm0 Hr]. apply andb_prop in Hm0 as [H1 H2].
    unfold mrename, is_fog, amap_den in *. cbn [am_kind am_base am_len] in *.
    rewrite ?(uE_rename E) by assumption. rewrite ?(ER E) by assumption.
    destruct (is_tok_kind mk).
    - destruct HM as [HM|(iv & l' & -> & Hsz & HM)]; [left; exact (IH _ Hr HM) | right].
      exists iv, l'. split; [reflexivity|]. split; [exact Hsz | exact (IH _ Hr HM)].
    - destruct HM as (l' & -> & HM). exists l'. split; [reflexivity | exact (IH _ Hr HM)].
  Qed.
  (* [comment removed for export] *)
  Lemma holes_rename : forall E y l ms,
    forallb (fun m0 => evars_all (ren_ok fw bw) (am_base m0) && evars_all (ren_ok fw bw) (am_len m0)) ms = true ->
    Forall (hole_ok E y l) ms -> Forall (hole_ok (ren_env bw E) y l) (map (mrename fw) ms).
  Proof.
    intros E y l ms H HF. apply Forall_forall. intros m0 Hin Hk. apply in_map_iff in Hin as (m1 & <- & Hin).
    pose proof (proj1 (forallb_forall _ _) H m1 Hin) as Hmm. apply andb_prop in Hmm as [H1 H2].
    unfold hole_ok, is_hole, mrename in *. cbn [am_base am_len am_kind] in *. rewrite !(uE_rename E) by assumption.
    exact (proj1 (Forall_forall _ _) HF m1 Hin Hk).
  Qed.

  Lemma fds_ok_rename : forall E f model,
    match f with FdFile _ l o => evars_all (ren_ok fw bw) l && evars_all (ren_ok fw bw) o | _ => true end%bool = true ->
    fds_ok E f model -> fds_ok (ren_env bw E) (frename fw f) model.
  Proof.
    intros E f model Hv H. destruct f as [|k len off|]; try exact H.
    apply andb_prop in Hv as [Hl Ho]. cbn [frename].
    destruct H as [p [c (H1 & H2 & H3 & H4 & H5)]]. exists p, c.
    rewrite !(uE_rename E) by assumption. rewrite !(ER E) by assumption. rewrite eb_ren. repeat split; assumption.
  Qed.

  Lemma cs_ok_rename : forall E cs R FULL model nx,
    csvars_all (ren_ok fw bw) cs = true -> s_log (a_ss cs) = [] ->
    cs_ok E cs R FULL model -> cs_ok (ren_env bw E) (rename_cs fw cs nx) R FULL model.
  Proof.
    intros E cs R FULL model nx Hv Hlog HC.
    unfold csvars_all in Hv.
    apply andb_prop in Hv as [Hv Hfd]. apply andb_prop in Hv as [Hv Hbrk]. apply andb_prop in Hv as [Hv Hgh].
    apply andb_prop in Hv as [Hv Hvis]. apply andb_prop in Hv as [Hv Hmaps]. apply andb_prop in Hv as [Hregs Hkn].
    pose proof (hid_rename E cs nx model Hvis) as HH.
    pose proof (allowA_rename E cs nx Hvis Hgh) as HA.
    assert (HMr : Mr (ren_env bw E) (rename_cs fw cs nx) model FULL = Mr E cs model FULL) by (unfold Mr; rewrite HH; reflexivity).
    destruct HC; constructor; cbn [rename_cs a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn mk_ss s_regs s_log s_know s_pc s_next] in *;
      rewrite ?HA, ?HMr; try assumption.
    - apply regs_ok_rename; assumption.
    - reflexivity.
    - apply know_ok_rename; assumption.
    - apply fds_ok_rename; assumption.
    - apply maps_match_rename; assumption.
    - apply holes_rename; assumption.
    - (* [comment removed for export] *) apply Forall_forall. intros m0 Hin Hk. apply in_map_iff in Hin as (m1 & <- & Hin).
      pose proof (proj1 (forallb_forall _ _) Hmaps m1 Hin) as Hmm. apply andb_prop in Hmm as [H1 H2].
      unfold amap_den, mrename in *. cbn [am_base am_len am_kind] in *. rewrite !(ER E) by assumption.
      exact (proj1 (Forall_forall _ _) co_none0 m1 Hin Hk).
    - (* [comment removed for export] *) apply Forall_forall. intros m0 Hin Hk a Ha. apply in_map_iff in Hin as (m1 & <- & Hin).
      pose proof (proj1 (forallb_forall _ _) Hmaps m1 Hin) as Hmm. apply andb_prop in Hmm as [H1 H2].
      unfold mrename in *. cbn [am_base am_len am_kind] in *. rewrite !(ER E) in Ha by assumption.
      exact (proj1 (Forall_forall _ _) co_kinds0 m1 Hin Hk a Ha).
    - rewrite (ER E) by assumption. assumption.
    - intros a. rewrite HH, (in_ghost_rename E cs nx Hgh). exact (co_zero0 a).
    - eapply SINV_agree; [eapply env_agree_le; [apply ren_agree | exact Hgb] | assumption].
  Qed.
End RenameCS.

#[using="argH_agree SINV_agree"] Lemma rename_sound : forall gb E cs R FULL model m cs',
  (nx0 <= gb)%nat -> cs_ok E cs R FULL model -> node_rename gb cs m = Some cs' ->
  exists E', env_agree gb E E' /\ cs_ok E' cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros gb E cs R FULL model m cs' Hgb HC H. unfold node_rename in H.
  destruct (forallb (fun p => Nat.leb gb (fst p) && Nat.leb gb (snd p)) m) eqn:Hm; [|discriminate].
  destruct (mk_fwd m) as [fw|] eqn:Hfw; [|discriminate].
  destruct (mk_bwd m) as [bw|] eqn:Hbw; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-. apply andb_prop in Hc as [Hv Hlog].
  exists (ren_env bw E). split; [exact (ren_agree m bw Hbw gb Hm E)|]. split; [|reflexivity].
  match goal with |- cs_ok _ (with_ss _ (mk_ss _ _ _ ?NX)) _ _ _ =>
    change (cs_ok (ren_env bw E) (rename_cs fw cs NX) R FULL model) end.
  apply (cs_ok_rename m fw bw Hfw Hbw gb Hgb Hm); [exact Hv | exact (co_log _ _ _ _ _ HC) | exact HC].
Qed.

#[using="argH_agree SINV_agree"] Lemma compact_sound : forall gb E cs R FULL model cs',
  (nx0 <= gb)%nat -> cs_ok E cs R FULL model -> node_compact gb cs = Some cs' ->
  exists E', env_agree gb E E' /\ cs_ok E' cs' R FULL model /\ pc cs' = pc cs.
Proof. intros gb E cs R FULL model cs' Hgb HC H. unfold node_compact in H. eapply rename_sound; eassumption. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="SEGS_in_hull HULL_ok"] Lemma abstractcell_sound : forall E cs R FULL model b n cs',
  cs_ok E cs R FULL model -> node_abstractcell A cs b n = Some cs' -> cs_ok E cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros E cs R FULL model b n cs' HC H. unfold node_abstractcell in H.
  destruct (split_lit b) as [bb bo]. cbv zeta in H.
  destruct (kunk_covered A (kn cs) (KUnk (SA bb bo) (ELit n))) eqn:Hcov; [|discriminate].
  injection H as <-. split; [|apply pc_set_kn].
  apply cs_ok_set_kn; [exact HC|]. constructor.
  - eapply kunk_covered_sound; [exact (co_know _ _ _ _ _ HC) | exact Hcov].
  - eapply know_ok_cutout; [exact (co_know _ _ _ _ _ HC) | intros; reflexivity].
Qed.

#[using="Type"] Lemma hw_apply_true_incl : forall r a x K, In K (hw_apply r a x true) -> In K r.
Proof.
  induction r as [|X r IH]; intros a x K H; [exact H|]. cbn [hw_apply] in H.
  destruct X as [a' w v| | | | | | | | |]; cbn in H;
    try (destruct H as [H|H]; [left; exact H | right; eapply IH; exact H]).
  destruct (saddr_eqb a' a); [right; eapply IH; exact H|].
  destruct H as [H|H]; [left; exact H | right; eapply IH; exact H].
Qed.

#[using="Type"] Lemma hw_apply_true_vars : forall r a x b, AP.kn_vars_lt b r = true -> AP.kn_vars_lt b (hw_apply r a x true) = true.
Proof.
  induction r as [|X r IH]; intros a x b H; [reflexivity|]. cbn [AP.kn_vars_lt] in H. apply andb_prop in H as [HX Hr].
  cbn [hw_apply]. destruct X as [a' w v| | | | | | | | |]; cbn [AP.kn_vars_lt]; rewrite ?HX, ?(IH a x b Hr); try reflexivity.
  destruct (saddr_eqb a' a); [exact (IH a x b Hr)|]. cbn [AP.kn_vars_lt]. rewrite HX, (IH a x b Hr). reflexivity.
Qed.

#[using="Type"] Lemma hw_apply_ok : forall E M k a x,
  know_ok SEGS E M k -> AP.kn_vars_lt x k = true ->
  know_ok SEGS (upd E x (edenot E (hw_val k a))) M (hw_apply k a x false)
  /\ AP.kn_vars_lt (Datatypes.S x) (hw_apply k a x false) = true.
Proof.
  intros E M k a x. induction k as [|X r IH]; intros HK Hv.
  - split; [constructor | reflexivity].
  - apply Forall_cons_iff in HK as [HX Hr]. cbn [AP.kn_vars_lt] in Hv. apply andb_prop in Hv as [HvX Hvr].
    assert (AG : forall e, env_agree x E (upd E x e)) by (intros; apply upd_agree).
    assert (KEEP : forall e, kentry_ok SEGS (upd E x e) M X).
    { intros e. apply (@Forall_inv _ (kentry_ok SEGS (upd E x e) M) X []).
      eapply (know_ok_agree' x); [apply AG | | constructor; [exact HX | constructor]].
      cbn [AP.kn_vars_lt]. rewrite HvX. reflexivity. }
    assert (KEEPV : AP.kentry_vars_lt (Datatypes.S x) X = true) by (eapply kentry_vars_lt_mono; [exact HvX | lia]).
    cbn [hw_apply hw_val].
    destruct X as [a' w v| | | | | | | | |];
      try (destruct (IH Hr Hvr) as [IH1 IH2]; split; [constructor; [apply KEEP | exact IH1] | cbn [AP.kn_vars_lt]; rewrite KEEPV, IH2; reflexivity]).
    destruct (saddr_eqb a' a) eqn:Hs.
    + (* [comment removed for export] *)
      split.
      * constructor.
        -- cbn [kentry_ok] in HX |- *. destruct HX as (Hw & Hf & Hrd).
           cbn [AP.kentry_vars_lt AP.saddr_vars_lt] in HvX. apply andb_prop in HvX as [Hva Hvv].
           assert (Ea : adenot (upd E x (edenot E v)) a' = adenot E a').
           { unfold adenot. rewrite <- (edenot_agree' x E _ (a_base a') (AG _) Hva). reflexivity. }
           assert (Es : estart (upd E x (edenot E v)) a' = estart E a').
           { unfold estart. rewrite <- (edenot_agree' x E _ (a_base a') (AG _) Hva). reflexivity. }
           split; [exact Hw|]. split; [unfold flat in *; rewrite ?Es; exact Hf|].
           rewrite Ea. cbn [edenot]. rewrite upd_at. exact Hrd.
        -- eapply (know_ok_agree' x); [apply AG | apply hw_apply_true_vars; exact Hvr |].
           apply Forall_forall. intros K HK'. apply hw_apply_true_incl in HK'. exact (proj1 (Forall_forall _ _) Hr K HK').
      * cbn [AP.kn_vars_lt AP.kentry_vars_lt]. cbn [AP.kentry_vars_lt] in KEEPV. apply andb_prop in KEEPV as [Ka _].
        rewrite Ka. cbn [AP.expr_vars_lt]. replace (Nat.ltb x (Datatypes.S x)) with true by (symmetry; apply Nat.ltb_lt; lia). cbn [andb].
        eapply kn_vars_lt_mono'; [apply hw_apply_true_vars; exact Hvr | lia].
    + destruct (IH Hr Hvr) as [IH1 IH2]. split; [constructor; [apply KEEP | exact IH1] | cbn [AP.kn_vars_lt]; rewrite KEEPV, IH2; reflexivity].
Qed.

#[using="Type"] Lemma hw_go_ok : forall bs E M k x,
  know_ok SEGS E M k -> AP.kn_vars_lt x k = true ->
  exists E', env_agree x E E' /\ know_ok SEGS E' M (hw_go k bs x) /\ AP.kn_vars_lt (x + length bs)%nat (hw_go k bs x) = true.
Proof.
  induction bs as [|b r IH]; intros E M k x HK Hv.
  - exists E. split; [apply env_agree_refl|]. cbn [hw_go length]. rewrite Nat.add_0_r. split; assumption.
  - cbn [hw_go length]. destruct (hw_apply_ok E M k (sa_of b) x HK Hv) as [H1 H2].
    destruct (IH _ M _ (Datatypes.S x) H1 H2) as (E' & Hag & HK' & Hv').
    exists E'. split; [|split; [exact HK' | rewrite <- Nat.add_succ_comm; exact Hv']].
    apply (env_agree_trans _ _ (upd E x (edenot E (hw_val k (sa_of b)))) _); [apply upd_agree | eapply env_agree_le; [exact Hag | lia]].
Qed.

#[using="argH_agree SINV_agree"] Lemma havocwords_sound : forall E cs R FULL model bs cs',
  cs_ok E cs R FULL model -> node_havocwords nx0 cs bs = Some cs' ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok E' cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros E cs R FULL model bs cs' HC H. unfold node_havocwords in H.
  destruct (fresh_ok nx0 cs) eqn:Hf; [|discriminate]. injection H as <-.
  destruct (fresh_ok_parts cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  destruct (hw_go_ok bs E (Mr E cs model FULL) (kn cs) (nxt cs) (co_know _ _ _ _ _ HC)) as (E' & Hag & HK' & _).
  { rewrite kn_vars_lt_eq. rewrite <- kn_vars_lt_eq. exact Fkn. }
  exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
  pose proof (cs_ok_agree E E' cs R FULL model Hag Hf HC) as HC2.
  replace (with_ss cs (mk_ss (s_pc (a_ss cs)) (s_regs (a_ss cs)) (hw_go (s_know (a_ss cs)) bs (s_next (a_ss cs))) (s_next (a_ss cs) + length bs)))
    with (set_kn (bump cs (length bs)) (hw_go (kn cs) bs (nxt cs))) by reflexivity.
  apply cs_ok_set_kn.
  - destruct HC2; constructor; cbn [bump with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset];
      try assumption; reflexivity.
  - unfold Mr. change (hid E' (bump cs (length bs)) model) with (hid E' cs model).
    rewrite (hid_agree (nxt cs) E E' cs model Hag Fle Fallow). exact HK'.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma respell_ok_sound : forall E M k a e,
  know_ok SEGS E M k -> respell_ok k a e = true -> edenot E a = edenot E e.
Proof.
  intros E M k a e HK H. unfold respell_ok in H.
  destruct (decide_branch k BC_EQ a e) as [[|]|] eqn:Hd.
  - pose proof (decide_branch_sound SEGS E M k BC_EQ a e true HK Hd) as Heq. cbn [branch_taken] in Heq. apply bv_eqb_eq in Heq. exact Heq.
  - destruct (erange k (mkAlu ALU_SUB a e)) as [[lo hi]|] eqn:Hr; [|discriminate].
    apply andb_prop in H as [H0 H1]. apply Z.eqb_eq in H0. apply Z.eqb_eq in H1. subst lo hi.
    pose proof (erange_sound SEGS E M k _ 0 0 HK Hr) as Hb. rewrite mkAlu_denot in Hb.
    cbn [alu64 alu] in Hb. rewrite bv_sub_unsigned in Hb. unfold bv_wrap in Hb.
    pose proof (u64_range (edenot E a)) as Ra. pose proof (u64_range (edenot E e)) as Re.
    apply bv_eq. change (bv_modulus 64) with (2 ^ 64)%Z in Hb. unfold two64 in *.
    assert (Hm : ((bv_unsigned (edenot E a) - bv_unsigned (edenot E e)) mod 2 ^ 64 = 0)%Z) by lia.
    apply Z.mod_divide in Hm; [|lia]. destruct Hm as [q Hq]. assert (q = 0)%Z by nia. subst q. lia.
  - destruct (erange k (mkAlu ALU_SUB a e)) as [[lo hi]|] eqn:Hr; [|discriminate].
    apply andb_prop in H as [H0 H1]. apply Z.eqb_eq in H0. apply Z.eqb_eq in H1. subst lo hi.
    pose proof (erange_sound SEGS E M k _ 0 0 HK Hr) as Hb. rewrite mkAlu_denot in Hb.
    cbn [alu64 alu] in Hb. rewrite bv_sub_unsigned in Hb. unfold bv_wrap in Hb.
    pose proof (u64_range (edenot E a)) as Ra. pose proof (u64_range (edenot E e)) as Re.
    apply bv_eq. change (bv_modulus 64) with (2 ^ 64)%Z in Hb. unfold two64 in *.
    assert (Hm : ((bv_unsigned (edenot E a) - bv_unsigned (edenot E e)) mod 2 ^ 64 = 0)%Z) by lia.
    apply Z.mod_divide in Hm; [|lia]. destruct Hm as [q Hq]. assert (q = 0)%Z by nia. subst q. lia.
Qed.
#[using="Type"] Lemma respell_sound : forall E cs R FULL model r e cs',
  cs_ok E cs R FULL model -> node_respell cs r e = Some cs' -> cs_ok E cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros E cs R FULL model r e cs' HC H. unfold node_respell in H.
  destruct (Nat.ltb 0 r && Nat.ltb r 32 && AP.expr_vars_lt (nxt cs) e && respell_ok (kn cs) (reg cs r) e)%bool eqn:Hc; [|discriminate].
  injection H as <-.
  apply andb_prop in Hc as [Hc Hok]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [H1 H2]. apply Nat.ltb_lt in H1. apply Nat.ltb_lt in H2.
  pose proof (respell_ok_sound E _ (kn cs) (reg cs r) e (co_know _ _ _ _ _ HC) Hok) as Heq.
  split; [|reflexivity].
  destruct HC; constructor; cbn [set_reg with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset]; try assumption; try reflexivity.
  apply regs_ok_respell; [assumption | lia | unfold reg in Heq; symmetry; exact Heq].
Qed.

#[using="Type"] Lemma self_jump_word : forall ms,
  ms_svc_pending ms = None -> fetch_word SEGS (ms_pc ms) = Some (Z_to_bv 32 SPIN_WORD) ->
  is_self_jump SEGS ms = true.
Proof. intros ms Hs Hf. unfold is_self_jump. rewrite Hs, Hf. vm_compute. reflexivity. Qed.

Definition LCOK (lc : option loopctx) (D : TSet) (E : env) (fs : Fs.Fs) : Prop :=
  match lc with
  | None => True
  | Some (LC h nx lo hi) => ((nx0 <= lo)%nat /\ (lo <= hi)%nat /\ length (s_regs (a_ss nx)) = 32%nat) /\
              forall E' R' F' m', env_agree lo E E' -> cs_ok E' nx R' F' m' -> m_fs m' = fs ->
                srealizes SEGS scfg (cfg R' h F' m') D
  (* [comment removed for export] *)
  | Some (JC j js sk b lo) => ((nx0 <= b)%nat /\ (b <= lo)%nat /\ length (s_regs (a_ss js)) = 32%nat) /\
              forall E' R' F' m', env_agree b E E' -> cs_ok E' js R' F' m' -> m_fs m' = fs ->
                srealizes SEGS scfg (cfg R' (pc js) F' m') (sd D E' fs sk)
  end.

#[using="Type"] Lemma LCOK_bnd : forall lc D E fs, LCOK lc D E fs -> (nx0 <= match lc with Some c => lc_bnd c | None => nx0 end)%nat.
Proof. intros [[h nx lo hi|j js sk b lo]|] D E fs HL; cbn [LCOK lc_bnd] in *; [destruct HL as [(H1 & H2 & _) _]; lia | destruct HL as [(H1 & _ & _) _]; lia | lia]. Qed.

Definition lc_guard (lc : option loopctx) (cs : acs) : bool :=
  match lc with Some c => Nat.leb (lc_bnd c) (nxt cs) | None => true end.

#[using="Type"] Lemma LCOK_agree : forall lc D E E' fs cs,
  LCOK lc D E fs -> lc_guard lc cs = true -> env_agree (nxt cs) E E' -> LCOK lc D E' fs.
Proof.
  intros [[h nx lo hi|j js sk b lo]|] D E E' fs cs HL Hg Hag; [| |exact I]; cbn [LCOK lc_guard lc_bnd] in *;
  apply Nat.leb_le in Hg; destruct HL as [(Hn0 & Hlh & Hlen) HL]; (split; [split; [exact Hn0 | split; [exact Hlh | exact Hlen]]|]);
  intros E2 R' F' m' Hag2; apply HL; (eapply env_agree_trans; [eapply env_agree_le; [exact Hag | lia] | exact Hag2]).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma LCOK_agree_gb : forall lc D E E' fs,
  LCOK lc D E fs -> env_agree (match lc with Some c => lc_bnd c | None => nx0 end) E E' -> LCOK lc D E' fs.
Proof.
  intros [[h nx lo hi|j js sk b lo]|] D E E' fs HL Hag; [| |exact I]; cbn [LCOK lc_bnd] in *;
  destruct HL as [(Hn0 & Hlh & Hlen) HL]; (split; [split; [exact Hn0 | split; [exact Hlh | exact Hlen]]|]);
  intros E2 R' F' m' Hag2; apply HL; (eapply env_agree_trans; [eapply env_agree_le; [exact Hag | lia] | exact Hag2]).
Qed.

(* [comment removed for export] *)
#[using="HOLES_agree"] Lemma cont_agree : forall bfuel fuel lc k cs cs' s E model D,
  CHECK bfuel fuel lc cs' k = COk s ->
  LCOK lc D E (m_fs model) -> lc_guard lc cs = true -> D [] ->
  (forall E R FULL model, cs_ok E cs' R FULL model -> LCOK lc D E (m_fs model) -> D [] ->
     srealizes SEGS scfg (cfg R (pc cs') FULL model) (sd D E (m_fs model) s)) ->
  forall E' R' FULL' model',
    env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
    srealizes SEGS scfg (cfg R' (pc cs') FULL' model') (sd D E (m_fs model) s).
Proof.
  intros bfuel fuel lc k cs cs' s E model D Hc HL Hg HD IH E' R' FULL' model' [Hag Hag2] HC' Hfs.
  rewrite (sd_agree D E E' (m_fs model) s Hag (check_vars _ _ _ _ _ _ Hc)), <- Hfs.
  apply (IH E' R' FULL' model' HC'); [|exact HD]. rewrite Hfs. eapply LCOK_agree; [exact HL | exact Hg | exact Hag2].
Qed.

#[using="IT_ok SEGS_wx SEGS_in_hull HULL_ok SHADOW_ok argH_high argH_agree SINV_frame SINV_agree HOLES_agree HOLES_nil node_sys_sound node_brk2_sound node_mmap2_sound node_mmapin_sound node_mprotect2_sound node_exit_sound node_x_sound node_join_sound node_ext_sound node_emit_sound node_ext2_sound HS_sound"] Theorem check_sound : forall fuel bfuel lc p cs s,
  CHECK bfuel fuel lc cs p = COk s ->
  forall E R FULL model D, cs_ok E cs R FULL model -> LCOK lc D E (m_fs model) -> D [] ->
  srealizes SEGS scfg (cfg R (pc cs) FULL model) (sd D E (m_fs model) s).
Proof.
  induction fuel as [|fuel IH]; intros bfuel lc p cs s Hc E R FULL model D HC HL HD; [discriminate|].
  cbn [AP.check] in Hc.
  match type of Hc with (if negb ?g then _ else _) = _ => destruct g eqn:Hg; [|discriminate] end. cbn [negb] in Hc.
  assert (CONT : forall k cs' s', CHECK bfuel fuel lc cs' k = COk s' ->
            forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' ->
            m_fs model' = m_fs model -> srealizes SEGS scfg (cfg R' (pc cs') FULL' model') (sd D E (m_fs model) s')).
  { intros k cs' s' Hk. eapply cont_agree; [exact Hk | exact HL | exact Hg | exact HD | intros; eapply IH; eassumption]. }
  assert (SAME : forall k cs' s', CHECK bfuel fuel lc cs' k = COk s' -> cs_ok E cs' R FULL model ->
            srealizes SEGS scfg (cfg R (pc cs') FULL model) (sd D E (m_fs model) s')).
  { intros k cs' s' Hk HC'. refine (CONT k cs' s' Hk E R FULL model (conj (env_agree_refl _ _) (env_agree_refl _ _)) HC' eq_refl). }
  destruct p as [stops k|e mid k1 k2|ce cmid ck1 ck2|db1 db2 dk1 dk2|sb1 sn1 sb2 sn2 k| |K k|jb joff jn k|ixs k|db dn k|gws k|bm k|hrs k|hbK k|r logc fb k|y k|ma mb|ia ib ic|qa qb|ka kb|x args k|xid xargs k|eid eargs k|bid bargs kb1 kb2|lJ lN linv lbody lk| |h| | |fi fsz fk|gi gsz gk|gb gn gk2|ub un uk|hlo hhi hk|ilo ihi ik|djp drs dk|rnm rnk|cpk|vj vjs vlo vka vk|mj|ab an ak|hws hwk|rsr rse rsk|iha ihb ihc].
  - (* [comment removed for export] *)
    destruct (run_block_gc SEGS IT _ KC bfuel (stops ++ STOPS A) cs) as [cs1|] eqn:Hrb; [|discriminate].
    pose proof (LCOK_bnd lc D E (m_fs model) HL) as Hgb.
    eapply run_block_gc_sound; [exact Hgb | exact Hrb | exact HC |].
    intros E' R' FULL' model' Hag HC1 Hfs. exact (CONT k cs1 s Hc E' R' FULL' model' Hag HC1 Hfs).
  - (* [comment removed for export] *)
    destruct (AP.expr_vars_lt nx0 e) eqn:Hv; [|discriminate].
    destruct (erange (kn cs) e) as [[lo hi]|] eqn:Hr; [|discriminate].
    destruct (Z.leb lo mid && Z.ltb mid hi)%bool.
    2: { (* [comment removed for export] *)
         pose proof (erange_sound SEGS E _ (kn cs) e lo hi (co_know _ _ _ _ _ HC) Hr) as Hb.
         destruct (Z.leb_spec hi mid) as [Hle|Hgt]; [exact (SAME k1 _ s Hc HC) | exact (SAME k2 _ s Hc HC)]. }
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange e lo mid :: kn cs)) k1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange e (mid+1) hi :: kn cs)) k2) as [s2|] eqn:H2; [|discriminate].
    injection Hc as <-. cbn [sd].
    destruct (split_sound cs e mid lo hi E R FULL model HC Hr) as [HCl HCr].
    destruct (Z.leb_spec (bv_unsigned (edenot E e)) mid) as [Hle|Hgt].
    + exact (SAME k1 _ s1 H1 (HCl Hle)).
    + exact (SAME k2 _ s2 H2 (HCr ltac:(lia))).
  - (* [comment removed for export] *)
    destruct (erange (kn cs) ce) as [[lo hi]|] eqn:Hr; [|discriminate].
    destruct (Z.leb lo cmid && Z.ltb cmid hi)%bool.
    2: { cbn [negb] in Hc. destruct (Z.leb hi cmid); [exact (SAME ck1 _ s Hc HC) | exact (SAME ck2 _ s Hc HC)]. }
    cbn [negb] in Hc. cbv zeta in Hc.
    destruct (split_sound cs ce cmid lo hi E R FULL model HC Hr) as [HCl HCr].
    destruct (kn_contra (kn (set_kn cs (KRange ce lo cmid :: kn cs)))) eqn:Hk1.
    { destruct (Z.leb_spec (bv_unsigned (edenot E ce)) cmid) as [Hle|Hgt].
      - exfalso. exact (kn_contra_sound E _ _ (co_know _ _ _ _ _ (HCl Hle)) Hk1).
      - exact (SAME ck2 _ s Hc (HCr ltac:(lia))). }
    destruct (kn_contra (kn (set_kn cs (KRange ce (cmid + 1) hi :: kn cs)))) eqn:Hk2.
    { destruct (Z.leb_spec (bv_unsigned (edenot E ce)) cmid) as [Hle|Hgt].
      - exact (SAME ck1 _ s Hc (HCl Hle)).
      - exfalso. exact (kn_contra_sound E _ _ (co_know _ _ _ _ _ (HCr ltac:(lia))) Hk2). }
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange ce lo cmid :: kn cs)) ck1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc (set_kn cs (KRange ce (cmid+1) hi :: kn cs)) ck2) as [s2|] eqn:H2; [|discriminate].
    destruct (shape_eqb s1 s2) eqn:Hse; [|discriminate]. injection Hc as <-. apply shape_eqb_eq in Hse. subst s2.
    destruct (Z.leb_spec (bv_unsigned (edenot E ce)) cmid) as [Hle|Hgt].
    + exact (SAME ck1 _ s1 H1 (HCl Hle)).
    + exact (SAME ck2 _ s1 H2 (HCr ltac:(lia))).
  - (* [comment removed for export] *)
    destruct (node_casedisj cs db1 db2) as [[csa csb]|] eqn:Hn; [|discriminate].
    destruct (CHECK bfuel fuel lc csa dk1) as [s1|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb dk2) as [s2|] eqn:H2; [|discriminate].
    destruct (shape_eqb s1 s2) eqn:Hse; [|discriminate]. injection Hc as <-. apply shape_eqb_eq in Hse. subst s2.
    destruct (casedisj_sound cs db1 db2 csa csb E R FULL model HC Hn) as [[HC' Hpc]|[HC' Hpc]]; rewrite <- Hpc.
    + exact (SAME dk1 _ s1 H1 HC').
    + exact (SAME dk2 _ s1 H2 HC').
  - (* [comment removed for export] *)
    destruct (node_shdisj A cs sb1 sn1 sb2 sn2) as [cs1|] eqn:Hn; [|discriminate].
    destruct (shdisj_sound cs sb1 sn1 sb2 sn2 cs1 E R FULL model HC Hn) as [HC' Hpc]. rewrite <- Hpc.
    exact (SAME k _ s Hc HC').
  - (* [comment removed for export] *)
    destruct (kn_contra (kn cs)) eqn:Hk; [|discriminate]. exfalso.
    exact (kn_contra_sound E _ (kn cs) (co_know _ _ _ _ _ HC) Hk).
  - (* [comment removed for export] *)
    destruct (fact_ok (kn cs) K) eqn:Hf; [|discriminate].
    exact (SAME k _ s Hc (fact_sound E cs R FULL model K HC Hf)).
  - (* [comment removed for export] *)
    destruct (node_join SEGS cs jb joff jn) as [cs1|] eqn:Hn; [|discriminate].
    eapply (node_join_sound jb joff jn cs cs1 E R FULL model); [exact HC | reflexivity | exact Hn |]. exact (CONT k cs1 s Hc).
  - (* [comment removed for export] *)
    exact (SAME k _ s Hc (forget_sound E cs R FULL model ixs HC)).
  - (* [comment removed for export] *)
    assert (Hpc : pc (node_droprange cs db dn) = pc cs) by (unfold node_droprange; destruct (split_lit db); reflexivity).
    rewrite <- Hpc. exact (SAME k _ s Hc (droprange_sound E cs R FULL model db dn HC)).
  - (* [comment removed for export] *)
    rewrite <- (pc_set_kn cs (kn_keep (kn cs) gws)).
    exact (SAME k _ s Hc (cs_ok_set_kn E cs R FULL model _ HC (know_ok_filter E _ _ (kn cs) (co_know _ _ _ _ _ HC)))).
  - (* [comment removed for export] *)
    destruct (node_bump cs bm) as [cs1|] eqn:Hn; [|discriminate].
    destruct (bump_sound E cs R FULL model bm cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc.
    exact (SAME k _ s Hc HC1).
  - (* [comment removed for export] *)
    destruct (node_havoc nx0 cs hrs) as [cs1|] eqn:Hn; [|discriminate].
    destruct (havoc_sound E cs R FULL model hrs cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    exact (CONT k cs1 s Hc E' R FULL model Hag HC1 eq_refl).
  - (* [comment removed for export] *)
    destruct (node_havocbig nx0 cs hbK) as [cs1|] eqn:Hn; [|discriminate].
    destruct (havocbig_sound E cs R FULL model hbK cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    exact (CONT k cs1 s Hc E' R FULL model Hag HC1 eq_refl).
  - (* [comment removed for export] *)
    destruct (node_fresh nx0 cs r logc fb) as [cs1|] eqn:Hn; [|discriminate].
    eapply (node_fresh_sound_pf r logc fb cs cs1 E R FULL model); [exact HC | reflexivity | exact Hn |]. exact (CONT k cs1 s Hc).
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_sys A nx0 y cs) as [cs1|] eqn:Hn; [|discriminate].
    eapply (node_sys_sound y cs cs1 E R FULL model); [exact HC | exact Hec | exact Hn |]. exact (CONT k cs1 s Hc).
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_mmap2 A nx0 LIMIT cs) as [[csa csb]|] eqn:Hn; [|discriminate].
    destruct (CHECK bfuel fuel lc csa ma) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb mb) as [sb|] eqn:H2; [|discriminate].
    injection Hc as <-.
    eapply srz_conseq; [| apply sd_salt2; exact HD].
    eapply (node_mmap2_sound cs csa csb E R FULL model); [exact HC | exact Hec | exact Hn | exact (CONT ma csa sa H1) | exact (CONT mb csb sb H2)].
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_mmapin A LIMIT false cs) as [[[csa csb] cscs]|] eqn:Hn; [|discriminate].
    destruct (CHECK bfuel fuel lc csa ia) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb ib) as [sb|] eqn:H2; [|discriminate].
    destruct (check_all A rz (CHECK bfuel fuel lc) ic cscs) as [sc|] eqn:H3; [|discriminate].
    injection Hc as <-.
    pose proof (proj2 (check_all_ok _ _ _ _ H3)) as Hall.
    eapply srz_conseq; [| eapply t_eq_trans; [| apply sd_salt2; exact HD]; apply t_eq_alt2; [apply t_eq_refl' | apply sd_salt2; exact HD]].
    eapply (node_mmapin_sound false cs csa csb cscs E R FULL model);
      [exact HC | exact Hec | exact Hn | exact (CONT ia csa sa H1) | exact (CONT ib csb sb H2) |].
    intros csc E' R' FULL' model' Hin. exact (CONT ic csc sc (Hall csc Hin) E' R' FULL' model').
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_mprotect2 A LIMIT cs) as [[csa csb]|] eqn:Hn; [|discriminate].
    destruct (CHECK bfuel fuel lc csa qa) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb qb) as [sb|] eqn:H2; [|discriminate].
    injection Hc as <-.
    eapply srz_conseq; [| apply sd_salt2; exact HD].
    eapply (node_mprotect2_sound cs csa csb E R FULL model); [exact HC | exact Hec | exact Hn | exact (CONT qa csa sa H1) | exact (CONT qb csb sb H2)].
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_brk2 A LIMIT cs) as [[csa csb]|] eqn:Hn; [|discriminate].
    destruct (CHECK bfuel fuel lc csa ka) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb kb) as [sb|] eqn:H2; [|discriminate].
    injection Hc as <-.
    eapply srz_conseq; [| apply sd_salt2; exact HD].
    eapply (node_brk2_sound cs csa csb E R FULL model); [exact HC | exact Hec | exact Hn | exact (CONT ka csa sa H1) | exact (CONT kb csb sb H2)].
  - (* [comment removed for export] *)
    destruct (XON x) eqn:HXon; [|discriminate].
    destruct (node_x SEGS A nx0 rz x args cs) as [cs1|] eqn:Hn; [|discriminate].
    eapply (node_x_sound x HXon args cs cs1 E R FULL model); [exact HC | reflexivity | exact Hn |]. exact (CONT k cs1 s Hc).
  - (* [comment removed for export] *)
    destruct (XN xid xargs cs) as [cs1|] eqn:Hn; [|discriminate].
    eapply (node_ext_sound xid xargs cs cs1 E R FULL model); [exact HC | reflexivity | exact Hn |]. exact (CONT k cs1 s Hc).
  - (* [comment removed for export] *)
    destruct (XE eid eargs cs) as [[[fd ps] cs1]|] eqn:Hn; [|discriminate].
    destruct (CHECK bfuel fuel lc cs1 k) as [s1|] eqn:H1; [|discriminate]. injection Hc as <-. cbn [sd].
    eapply (node_emit_sound eid eargs cs fd ps cs1 E R FULL model); [exact HC | exact Hn | apply sd_has_nil; exact HD |]. exact (CONT k cs1 s1 H1).
  - (* [comment removed for export] *)
    destruct (XB bid bargs cs) as [[csa csb]|] eqn:Hn; [|discriminate].
    destruct (CHECK bfuel fuel lc csa kb1) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb kb2) as [sb|] eqn:H2; [|discriminate].
    injection Hc as <-. cbn [sd].
    eapply (node_ext2_sound bid bargs cs csa csb E R FULL model); [exact HC | exact Hn | exact (CONT kb1 csa sa H1) | exact (CONT kb2 csb sb H2)].
  - (* [comment removed for export] *)
    destruct (loop_ok nx0 cs lJ lN linv) as [nhi|] eqn:Hlo; [|discriminate].
    destruct (Z.eqb (pc linv) (pc cs) && entails_h A (Datatypes.S lJ) (nxt linv) cs (inst linv lJ (ELit 0)))%bool eqn:Ht; [|discriminate].
    apply andb_prop in Ht as [Hpc Hent]. apply Z.eqb_eq in Hpc.
    destruct (CHECK bfuel fuel (Some (LC (pc cs) (inst linv lJ (eaddz (EVar lJ) 1)) (Datatypes.S lJ) (nxt linv))) (loop_body_state lJ lN nhi linv) lbody) as [sb|] eqn:Hbody; [|discriminate].
    destruct sb; try discriminate. rename Hc into Hk.
    destruct (loop_ok_facts cs lJ lN linv nhi Hlo) as (Ffr & FJ & FJh & Flog & Flen & FvN & FxN & Fnhi).
    destruct (fresh_ok_parts cs Ffr) as (_ & _ & _ & _ & _ & _ & Fle).
    pose proof (xhi_sound SEGS E _ (kn cs) lN nhi (co_know _ _ _ _ _ HC) FxN) as HNv.
    set (Nv := bv_unsigned (edenot E lN)) in *. pose proof (u64_range (edenot E lN)) as RN. fold Nv in RN.
    set (D0 := sd D E (m_fs model) s).
    assert (HD0 : D0 []) by (apply sd_has_nil; exact HD).
    set (h := pc cs) in *.
    (* [comment removed for export] *)
    assert (Q : forall m j E' R' F' m', j = Nv - Z.of_nat m -> 0 <= j -> env_agree (nxt cs) E E' ->
               cs_ok E' (inst linv lJ (ELit j)) R' F' m' -> m_fs m' = m_fs model ->
               srealizes SEGS scfg (cfg R' h F' m') D0).
    { induction m as [|m IHm]; intros j E' R' F' m' Hj Hj0 Hag HCj Hfs.
      - (* [comment removed for export] *)
        assert (HNe : edenot E' lN = edenot E' (ELit j)).
        { cbn [edenot]. rewrite <- (edenot_agree' (nxt cs) E E' lN Hag FvN). apply bv_eq. rewrite u_small by lia. cbn in Hj. lia. }
        assert (HCN : cs_ok E' (inst linv lJ lN) R' F' m').
        { apply (proj2 (cs_ok_inst E' lJ lN linv R' F' m' ltac:(lia) Flog)). rewrite HNe.
          apply (proj1 (cs_ok_inst E' lJ (ELit j) linv R' F' m' ltac:(lia) Flog)). exact HCj. }
        unfold D0. rewrite (sd_agree D E E' (m_fs model) s ltac:(eapply env_agree_le; [exact Hag | exact Fle]) (check_vars _ _ _ _ _ _ Hk)).
        rewrite <- Hfs. replace h with (pc (inst linv lJ lN)) by (unfold h; rewrite pc_inst; exact Hpc).
        apply (IH bfuel lc lk _ s Hk E' R' F' m' D HCN); [|exact HD].
        rewrite Hfs. eapply LCOK_agree; [exact HL | exact Hg | exact Hag].
      - (* [comment removed for export] *)
        set (E'' := upd E' lJ (Z_to_bv 64 j)).
        assert (Hjlt : j < Nv) by lia.
        assert (HCinv : cs_ok E'' linv R' F' m').
        { unfold E''. replace (Z_to_bv 64 j) with (edenot E' (ELit j)) by reflexivity.
          apply (proj1 (cs_ok_inst E' lJ (ELit j) linv R' F' m' ltac:(lia) Flog)). exact HCj. }
        assert (Hag'' : env_agree (nxt cs) E E'').
        { eapply env_agree_trans; [exact Hag|]. eapply env_agree_le; [apply upd_agree | exact FJ]. }
        assert (HNE'' : edenot E'' lN = edenot E lN) by (symmetry; eapply (edenot_agree' (nxt cs)); [exact Hag'' | exact FvN]).
        assert (HJ'' : ev E'' lJ = Z_to_bv 64 j) by (unfold E''; apply upd_at).
        assert (HCb : cs_ok E'' (loop_body_state lJ lN nhi linv) R' F' m').
        { unfold loop_body_state, add_kn. apply cs_ok_set_kn; [exact HCinv|]. apply Forall_app. split; [|exact (co_know _ _ _ _ _ HCinv)].
          constructor; [|constructor; [|constructor]]; cbn [kentry_ok edenot].
          - rewrite HJ'', u_small by lia. lia.
          - unfold esub. rewrite mkAlu_denot, u_sub64. cbn [edenot]. rewrite HNE'', HJ''. fold Nv. rewrite u_small by lia.
            rewrite Z.mod_small by lia. lia. }
        replace h with (pc (loop_body_state lJ lN nhi linv)) by exact Hpc.
        refine (IH bfuel _ lbody _ SNext Hbody E'' R' F' m' D0 HCb _ HD0).
        (* [comment removed for export] *)
        cbn [LCOK]. split.
        { split; [lia|]. split; [lia|]. unfold inst. cbn [a_ss s_regs mk_ss]. rewrite length_map. exact Flen. }
        intros E3 R3 F3 m3 Hag3 HC3 Hfs3.
        assert (HJ3 : ev E3 lJ = Z_to_bv 64 j) by (rewrite <- HJ''; symmetry; apply (proj1 Hag3); lia).
        assert (Hnext : edenot E3 (eaddz (EVar lJ) 1) = Z_to_bv 64 (j + 1)).
        { unfold eaddz. rewrite mkAlu_denot. cbn [edenot]. rewrite HJ3. apply bv_eq. rewrite u_add64, !u_small by lia. rewrite Z.mod_small by lia. reflexivity. }
        set (E4 := upd E3 lJ (Z_to_bv 64 (j + 1))).
        apply (IHm (j + 1) E4 R3 F3 m3); [lia | lia | | | rewrite Hfs3; exact Hfs].
        + eapply env_agree_trans; [exact Hag''|]. eapply env_agree_trans; [eapply env_agree_le; [exact Hag3 | lia]|].
          eapply env_agree_le; [apply upd_agree | exact FJ].
        + apply (proj2 (cs_ok_inst E4 lJ (ELit (j + 1)) linv R3 F3 m3 ltac:(lia) Flog)).
          unfold E4. cbn [edenot]. rewrite upd_upd. rewrite <- Hnext.
          apply (proj1 (cs_ok_inst E3 lJ (eaddz (EVar lJ) 1) linv R3 F3 m3 ltac:(lia) Flog)). exact HC3. }
    (* [comment removed for export] *)
    destruct (entails_h_sound (Datatypes.S lJ) (nxt linv) E cs (inst linv lJ (ELit 0)) R FULL model HC Hent ltac:(lia)
                ltac:(unfold inst; cbn [a_ss s_regs mk_ss]; rewrite length_map; exact Flen)) as (E1 & Hag1 & _ & HC1 & _).
    unfold D0 in Q. apply (Q (Z.to_nat Nv) 0 E1 R FULL model); [lia | lia | eapply env_agree_le; [exact Hag1 | lia] | exact HC1 | reflexivity].
  - (* [comment removed for export] *)
    destruct lc as [[h nx lo hi|j' js' sk' b' lo']|]; [|discriminate|discriminate].
    destruct (Z.eqb (pc cs) h && entails_h A lo hi cs nx)%bool eqn:Ht; [|discriminate]. injection Hc as <-. cbn [sd].
    apply andb_prop in Ht as [Hpc Hent]. apply Z.eqb_eq in Hpc.
    cbn [LCOK] in HL. destruct HL as [(Hn0 & Hlh & Hlen) HL]. cbn [lc_guard lc_bnd] in Hg. apply Nat.leb_le in Hg.
    destruct (entails_h_sound lo hi E cs nx R FULL model HC Hent Hn0 Hlen) as (E' & Hag & _ & HC' & Hpc').
    rewrite Hpc. exact (HL E' R FULL model Hag HC' eq_refl).
  - (* [comment removed for export] *)
    destruct (HS h) as [ch|] eqn:Hh; [|discriminate].
    destruct (entails cs ch) eqn:He; [|discriminate]. injection Hc as <-. cbn [sd].
    destruct (entails_sound E cs ch R FULL model HC He) as [HC' Hpc].
    rewrite <- Hpc. exact (HS_sound h ch Hh E R FULL model HC').
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_exit cs) as [code|] eqn:Hn; [|discriminate]. injection Hc as <-. cbn [sd].
    eapply node_exit_sound; eassumption.
  - (* [comment removed for export] *)
    discriminate.
  - (* [comment removed for export] *)
    destruct (node_fog cs fi fsz) as [cs1|] eqn:Hn; [|discriminate].
    destruct (fog_sound E cs R FULL model fi fsz cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc. exact (SAME fk _ s Hc HC1).
  - (* [comment removed for export] *)
    destruct (node_fognew cs gi gsz) as [cs1|] eqn:Hn; [|discriminate].
    destruct (fognew_sound E cs R FULL model gi gsz cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc. exact (SAME gk _ s Hc HC1).
  - (* [comment removed for export] *)
    destruct (node_ghost LIMIT cs gb gn) as [cs1|] eqn:Hn; [|discriminate].
    destruct (ghost_sound E cs R FULL model gb gn cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc. exact (SAME gk2 _ s Hc HC1).
  - (* [comment removed for export] *)
    destruct (node_unvis A cs ub un) as [cs1|] eqn:Hn; [|discriminate].
    destruct (unvis_sound E cs R FULL model ub un cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc. exact (SAME uk _ s Hc HC1).
  - (* [comment removed for export] *)
    destruct (node_havocbrk nx0 cs hlo hhi) as [cs1|] eqn:Hn; [|discriminate].
    destruct (havocbrk_sound E cs R FULL model hlo hhi cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    exact (CONT hk cs1 s Hc E' R FULL model Hag HC1 eq_refl).
  - (* [comment removed for export] *)
    destruct (node_intro nx0 cs ilo ihi) as [cs1|] eqn:Hn; [|discriminate].
    destruct (intro_sound E cs R FULL model ilo ihi cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    exact (CONT ik cs1 s Hc E' R FULL model Hag HC1 eq_refl).
  - (* [comment removed for export] *)
    destruct (branch_probe IT cs) as [e|] eqn:Hbp; [|discriminate].
    destruct (erange (kn cs) e) as [[lo hi]|] eqn:Hr; [|discriminate].
    pose proof (LCOK_bnd lc D E (m_fs model) HL) as Hgb.
    destruct (Z.ltb hi 1 || Z.ltb 0 lo)%bool eqn:Hdec.
    { (* [comment removed for export] *)
      destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) cs) as [cs1|] eqn:Hrb; [|discriminate].
      destruct (Z.eqb (pc cs1) djp); [|discriminate].
      eapply run_block_gc_sound; [exact Hgb | exact Hrb | exact HC |].
      intros E' R' FULL' model' Hag HC1 Hfs. exact (CONT dk cs1 s Hc E' R' FULL' model' Hag HC1 Hfs). }
    cbv zeta in Hc.
    destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) (set_kn cs (KRange e lo 0 :: kn cs))) as [ca|] eqn:Hra; [|discriminate].
    destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) (set_kn cs (KRange e 1 hi :: kn cs))) as [cb|] eqn:Hrb; [|discriminate].
    destruct (node_diamond_join A nx0 (nxt cs) djp drs ca cb) as [csj|] eqn:Hj; [|discriminate].
    destruct (split_sound cs e 0 lo hi E R FULL model HC Hr) as [HCl HCr].
    destruct (diamond_join_sound (nxt cs) djp drs ca cb csj Hj) as [Ja Jb].
    destruct (Z.leb_spec (bv_unsigned (edenot E e)) 0) as [Hle|Hgt].
    + rewrite <- (pc_set_kn cs (KRange e lo 0 :: kn cs)).
      eapply run_block_gc_sound; [exact Hgb | exact Hra | exact (HCl Hle) |].
      intros E' R' FULL' model' [Hag0 Hag1] HC1 Hfs.
      destruct (Ja E' R' FULL' model' HC1) as (E'' & [Hag2a Hag2b] & HC2 & Hpc2). rewrite <- Hpc2.
      change (env_agree (nxt cs) E E') in Hag1.
      exact (CONT dk csj s Hc E'' R' FULL' model'
               (conj (env_agree_trans _ _ _ _ Hag0 Hag2a) (env_agree_trans _ _ _ _ Hag1 Hag2b)) HC2 Hfs).
    + rewrite <- (pc_set_kn cs (KRange e 1 hi :: kn cs)).
      eapply run_block_gc_sound; [exact Hgb | exact Hrb | exact (HCr ltac:(lia)) |].
      intros E' R' FULL' model' [Hag0 Hag1] HC1 Hfs.
      destruct (Jb E' R' FULL' model' HC1) as (E'' & [Hag2a Hag2b] & HC2 & Hpc2). rewrite <- Hpc2.
      change (env_agree (nxt cs) E E') in Hag1.
      exact (CONT dk csj s Hc E'' R' FULL' model'
               (conj (env_agree_trans _ _ _ _ Hag0 Hag2a) (env_agree_trans _ _ _ _ Hag1 Hag2b)) HC2 Hfs).
  - (* [comment removed for export] *)
    destruct (node_rename _ cs rnm) as [cs1|] eqn:Hn; [|discriminate].
    pose proof (LCOK_bnd lc D E (m_fs model) HL) as Hgb.
    destruct (rename_sound _ E cs R FULL model rnm cs1 Hgb HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    rewrite (sd_agree D E E' (m_fs model) s (env_agree_le _ _ _ _ Hag Hgb) (check_vars _ _ _ _ _ _ Hc)).
    eapply IH; [exact Hc | exact HC1 | eapply LCOK_agree_gb; [exact HL | exact Hag] | exact HD].
  - (* [comment removed for export] *)
    destruct (node_compact _ cs) as [cs1|] eqn:Hn; [|discriminate].
    pose proof (LCOK_bnd lc D E (m_fs model) HL) as Hgb.
    destruct (compact_sound _ E cs R FULL model cs1 Hgb HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    rewrite (sd_agree D E E' (m_fs model) s (env_agree_le _ _ _ _ Hag Hgb) (check_vars _ _ _ _ _ _ Hc)).
    eapply IH; [exact Hc | exact HC1 | eapply LCOK_agree_gb; [exact HL | exact Hag] | exact HD].
  - (* [comment removed for export] *)
    destruct (via_ok nx0 cs vjs vlo) eqn:Hv; [|discriminate].
    destruct (CHECK bfuel fuel lc vjs vk) as [sk|] eqn:Hk; [|discriminate].
    unfold via_ok in Hv. repeat match type of Hv with (_ && _)%bool = true => apply andb_prop in Hv as [Hv ?X] end.
    match goal with Hl : match s_log (a_ss vjs) with _ => _ end = true |- _ => clear Hl end.
    match goal with Hl : Nat.eqb (length _) 32 = true |- _ => apply Nat.eqb_eq in Hl; rename Hl into Hlen end.
    repeat match goal with Hl : Nat.leb _ _ = true |- _ => apply Nat.leb_le in Hl end.
    pose proof (LCOK_bnd lc D E (m_fs model) HL) as Hgb.
    assert (Hgb' : (match lc with Some c => lc_bnd c | None => nx0 end <= nxt cs)%nat).
    { destruct lc as [c|]; [apply Nat.leb_le; exact Hg | lia]. }
    apply (IH bfuel (Some (JC vj vjs sk (nxt cs) vlo)) vka cs s Hc E R FULL model D HC); [|exact HD].
    cbn [LCOK]. split; [split; [lia | split; [lia | exact Hlen]]|].
    intros E' R' F' m' Hag HC' Hfs. rewrite <- Hfs.
    apply (IH bfuel lc vk vjs sk Hk E' R' F' m' D HC'); [|exact HD].
    rewrite Hfs. eapply LCOK_agree_gb; [exact HL|]. eapply env_agree_le; [exact Hag | exact Hgb'].
  - (* [comment removed for export] *)
    destruct lc as [[h nx lo hi|j' js' sk' b' lo']|]; [discriminate| |discriminate].
    destruct (Nat.eqb mj j' && Z.eqb (pc cs) (pc js') && shape_vars_lt nx0 sk' && entails_h A lo' (nxt js') cs js')%bool eqn:Ht; [|discriminate].
    injection Hc as <-.
    apply andb_prop in Ht as [Ht Hent]. apply andb_prop in Ht as [Ht Hsv]. apply andb_prop in Ht as [_ Hpc]. apply Z.eqb_eq in Hpc.
    cbn [LCOK] in HL. destruct HL as [(Hn0 & Hbl & Hlen) HJ].
    destruct (entails_h_sound lo' (nxt js') E cs js' R FULL model HC Hent ltac:(clear -Hn0 Hbl; lia) Hlen) as (E' & Hag & _ & HC' & Hpc').
    assert (Hn0l : (nx0 <= lo')%nat) by lia.
    rewrite (sd_agree D E E' (m_fs model) sk' (env_agree_le nx0 lo' E E' Hag Hn0l) Hsv). rewrite Hpc.
    exact (HJ E' R FULL model (env_agree_le _ _ _ _ Hag Hbl) HC' eq_refl).
  - (* [comment removed for export] *)
    destruct (node_abstractcell A cs ab an) as [cs1|] eqn:Hn; [|discriminate].
    destruct (abstractcell_sound E cs R FULL model ab an cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc. exact (SAME ak _ s Hc HC1).
  - (* [comment removed for export] *)
    destruct (node_havocwords nx0 cs hws) as [cs1|] eqn:Hn; [|discriminate].
    destruct (havocwords_sound E cs R FULL model hws cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
    exact (CONT hwk cs1 s Hc E' R FULL model Hag HC1 eq_refl).
  - (* [comment removed for export] *)
    destruct (node_respell cs rsr rse) as [cs1|] eqn:Hn; [|discriminate].
    destruct (respell_sound E cs R FULL model rsr rse cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc. exact (SAME rsk _ s Hc HC1).
  - (* [comment removed for export] *)
    destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_mmapin A LIMIT true cs) as [[[csa csb] cscs]|] eqn:Hn; [|discriminate].
    destruct (CHECK bfuel fuel lc csa iha) as [sa|] eqn:H1; [|discriminate].
    destruct (CHECK bfuel fuel lc csb ihb) as [sb|] eqn:H2; [|discriminate].
    destruct (check_all A rz (CHECK bfuel fuel lc) ihc cscs) as [sc|] eqn:H3; [|discriminate].
    injection Hc as <-.
    pose proof (proj2 (check_all_ok _ _ _ _ H3)) as Hall.
    eapply srz_conseq; [| eapply t_eq_trans; [| apply sd_salt2; exact HD]; apply t_eq_alt2; [apply t_eq_refl' | apply sd_salt2; exact HD]].
    eapply (node_mmapin_sound true cs csa csb cscs E R FULL model);
      [exact HC | exact Hec | exact Hn | exact (CONT iha csa sa H1) | exact (CONT ihb csb sb H2) |].
    intros csc E' R' FULL' model' Hin. exact (CONT ihc csc sc (Hall csc Hin) E' R' FULL' model').
Qed.

End Sound.
End FPX_3.

End APS.
