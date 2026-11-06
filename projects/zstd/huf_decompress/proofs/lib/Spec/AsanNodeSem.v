(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import NodesA.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Cfg MmEd.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Placement.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed Monad RSim AsanProgDeps AsanTotalCore AsanInv.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AsanNodeSem () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode8mmap_lenC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K59OSSVerify5KrLib3Lib5Nodes4node0:C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA6nstepAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4MmEd@mmap_corner_freeC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap:check_mmapK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result01C59OSSVerify5KrLib3Lib5Nodes5mm_nsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA?nstepA_mmap_iffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4MmEd=check_mmap_edC1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib3Lib5Nodes:pure_inputC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4MmEdAforced_of_ns_mmapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4MmEdAcheck_mmap_ed_fwdC1?~~~~~~~~~~~~~~~I6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C59OSSVerify5KrLib3Lib4MmEdCns_of_check_mmap_edC1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem6Checks?ExecutableSpecs=check_syscallC4ELinuxProcessSemantics?LinuxProcessSem3RunDspurious_refusal_cfgC47Corelib4Init5Logic3notC4ELinuxProcessSemantics?LinuxProcessSem5State6in_argC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys?DispatchComputeBcheck_syscall_mmapK47Corelib4Init5Logic3and01I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00C59OSSVerify5KrLib3Lib3Cfg4ACFGC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareC59OSSVerify5KrLib4Spec7AsanInv5ACEILC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv8ATOP_MAXC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic2or00C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;mmap_anon_bC47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib4Spec8AsanCtrl6F_ANONC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7F_FIXEDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:F_FIXNORESC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backing_usedC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC59OSSVerify5KrLib3Lib9Placement@vm_gap_availableC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_fixed_rw_bC59OSSVerify5KrLib3Lib4MmEdGmmap_corner_free_not_rwC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;AsanNodeSem>nstepA_mmap_edC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_off_aligned_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_pglen_ok_bC4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude>check_ret_onlyC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5w_is0C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapAmmap_plain_anon_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>mmap_modeled_bI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapHmmap_noreserve_backed_okK47Corelib4Init9Datatypes4prod01C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude:listNN_eqbC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_noaccess_bC59OSSVerify5KrLib3Lib9PlacementFmmap_reserve_refusableC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEmmap_fixed_noaccess_bC4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeC4ELinuxProcessSemantics?LinuxProcessSem5State<map_containsC47Corelib4Init9Datatypes4andbC59OSSVerify5KrLib3Lib4MmEd6w_nilbC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<errno_ret_inC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapImmap_fixed_destroyed_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapCwith_mmap_destroyedC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC4ELinuxProcessSemantics?LinuxProcessSem5State=maps_subtractC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapMmmap_fixed_noaccess_span_nextC59OSSVerify5KrLib3Lib9PlacementKmmap_fixed_commit_refusableC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_budget_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_fixed_rw_nextC59OSSVerify5KrLib3Lib9PlacementJmmap_fixed_fresh_refusableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9PlacementImmap_fixed_span_refusableC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapLmmap_fixed_rw_span_budget_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_span_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapImmap_noreplace_noaccess_bC47Corelib4Init9Datatypes3orbC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapCmmap_noreplace_rw_bK47Corelib4Init5Logic2or01C59OSSVerify5KrLib3Lib5Nodes9w_is0_litC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqK46Stdlib9micromega5Tauto8GFormula03C47Corelib4Init5Logic6eq_symC47Corelib4Init9Datatypes3appc59OSSVerify5KrLib4Spec;AsanNodeSem;mmap_len_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init5Logic5proj2C59OSSVerify5KrLib3Lib9PlacementDmmap_grant_refusableC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedK4ELinuxProcessSemantics?LinuxProcessSem5State7VmState01C4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State6m_timeK4ELinuxProcessSemantics?LinuxProcessSem5State5Model01C4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsK4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C59OSSVerify5KrLib4Spec7AsanInv;grant_modelC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude=listNN_eqb_eqC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapAwith_mmap_backingC59OSSVerify5KrLib3Lib6MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode<mmap_addr_okC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib6Decode8mmap_ans02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode6avoidsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode8dec_mmapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode=dec_mmap_noneC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_add_lazyK47Corelib4Init5Logic2ex01C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib3Lib9Placement@mmap_errnos_whenC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEwith_mmap_replacementC59OSSVerify5KrLib4Spec9AsanEmbed9adec_mmapC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeC4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64C59OSSVerify5KrLib4Spec8AsanCtrl7PROT_RWC1?~~~~~~~~~~~~~~~K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result02K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics?LinuxProcessSem5State6EINVALK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result03I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I47Corelib4Init9Datatypes3nat00C4ELinuxProcessSemantics?LinuxProcessSem5State6ENOMEMC59OSSVerify5KrLib3Lib9PlacementGmmap_destructive_errnosC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State6EEXISTI59OSSVerify5KrLib3Lib6Decode8mmap_ans00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9PlacementEvm_gap_available_findC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9Placement<vm_find_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9PlacementBvm_find_base_soundC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegc59OSSVerify5KrLib4Spec;AsanNodeSemAnstepA_mmap_of_edC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:eff_unmapsK47Corelib4Init5Logic2or02C47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indc59OSSVerify5KrLib4Spec;AsanNodeSem;fixed_shapeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;AsanNodeSem?mmap_len_boundsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_gtC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z<pos_div_euclC56Stdlib6ZArith6BinInt1Z3oppC57Corelib7BinNums6PosDef3Pos4landC56Stdlib6ZArith6BinInt1Z4of_NC57Corelib7BinNums6PosDef3Pos6pred_NC57Corelib7BinNums6NatDef1N5ldiffC57Corelib7BinNums6NatDef1N3lorC57Corelib7BinNums6NatDef1N8succ_posC57Corelib7BinNums6PosDef3Pos3eqbC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_forget_rangeC4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap=MAP_NORESERVEC4ELinuxProcessSemantics?LinuxProcessSem5State7map_hasK59OSSVerify5KrLib3Lib5Nodes4node0;C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nstepC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap<check_munmapC59OSSVerify5KrLib3Lib5Nodes@nstep_munmap_iffC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:map_removeC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>munmap_free_okC56Stdlib6ZArith6BinInt1Z6ltb_geC59OSSVerify5KrLib4Spec9AsanEmbed;adec_munmapC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateBpage_outside_rangeC46Stdlib5Lists4List6filterK59OSSVerify5KrLib3Lib6Decode9range_ans02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv<munmap_modelC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9TASK_SIZEC59OSSVerify5KrLib3Lib5Nodes=TASK_SIZE_valC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib6Decode9range_ans00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?with_vm_backingC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm7MadviseEmadvise_dontneed_nextI4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State7VmState00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00K59OSSVerify5KrLib3Lib5Nodes4node0=C1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm7Madvise=check_madviseC59OSSVerify5KrLib3Lib5NodesAnstep_madvise_iffC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm7MadviseBmadvise_dontneed_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm7MadviseCmadvise_dontneed_okC59OSSVerify5KrLib4Spec9AsanEmbed<adec_madviseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode8errno_ofC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;AsanNodeSemBmadvise_next_canonC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4RSim4STOTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5texitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;AsanNodeSem3aokC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl3aev01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl3aev02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl3aev03C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C59OSSVerify5KrLib3Lib5Nodes5nexitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;AsanNodeSem=grant_answersC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv;fixed_modelC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_reflc59OSSVerify5KrLib4Spec;AsanNodeSem<grant_existsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;AsanNodeSem=fixed_answersC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;AsanNodeSem<fixed_existsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl3aev04C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;AsanNodeSem>munmap_answersC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;AsanNodeSem5apostC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;AsanNodeSem=munmap_existsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl3aev05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl3aev06C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;AsanNodeSem?madvise_answersC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;AsanNodeSem>madvise_existsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl3aev07C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec=AsanTotalCore:node_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec=AsanTotalCore8aev_nodeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl3aev00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6aundef00C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Lemma mmap_len_eq : forall len, 0 <= len < 2^63 -> page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) = mmap_len len.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodeSem ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with53lenh61zp;2p;1p;3p;4p;8p;6p;7p10000p4p70R0p1000`p4p710R1p8P0p1001<p4p710R2p8P0p1001Zp4p7210R3p8P0g0027R0p4p710R4p8p1002Up4p70R5P1p8P5P2p8P5P3p8P5P4p8p1003Cp4p70R5P1p8P5P2p8P5P3p8P5P4p8g0049j2>Tg004Uj10Tg005:j15Tg005Xj11Tg006=j2?Tg006Zj2<Tg0076j2;Tg007Qj12Tg008Oj36Tg008ij2=Tg009Cj1:Tg009aj2ATg00:Gj2@Tg00;1j1RTg00;Qj1QTg00<1j2PTg00<Oj1MTg00<mj1LTg00=Xj27Tg00>;j2ITg00>^j43Tg00?Ij39Tg00?lj1FTg00@Nj8ETg00A2j2GTg00ATj2HTg00B@j3DTg00B_j4JTg00CQj2KTP0j6CTg00DMj1BTg00EEj7NTg00Eij7OTf1R0g00FMR4g00FlR5P5g00GLR3f0R2g00GlFNp=4f2R1P4P5P5P3P0P2FOp=8g00HLR6g00HjR7/>2g00IHR8#0R9#5R:%18#1#1#1#1R;#5'?,<2';R<P6P0%22%21566X66%20,=6%09#0#0#0#0R9#:R=1A=0'@R>g00ImR?#R%Q?1P60%M6%L6R?P4P5P5P3P61767g00JY1I68R8C3,4?R4P6P8g00K@R@176:RA%:;596C3,4?58?%F5P6P8P@A96A=C3,4?98?4GE1G?3P2P1g00KgR?g00LGR3'=1H21=6?3dAD670CJb2b3b4X061>70%59,?:,<0';\<^06P2P1P0O2b1,K0EC%2>%B0566eUW5o"). Qed.
Lemma mmap_len_bounds : forall l, 0 < l -> l <= mmap_len l < l + 4096.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodeSem ()) [] "h07__arithh14__ffh28__varmaph35__with44__x1h54__x2h64__x3h72H0h82H1h91lp;2p;1p;4p;6p;3p;7p;8g006Zj21Tg004Uj19Tg005:j1BTg00Lgj24Tg00MDj2<Tg00;1j1XTg00;Qj1STg00Maj1RTg00<Oj1OTg00<mj1NTg00=Xj2>Tg00>^j42Tg00N?j6aTg00A2j2_Tg008ij2[Tg00ATj2YTg008Oj3:Tg00B@j3WTg00B_j4VTg00Ncj3UTg00ODj2ETg00Oaj2?Tg00P>j2=Tg00P^j3QTg0049j26Tg0076j27Tg00QEj1;Tg00Qdj28Tg00RMj35Tg00S6j2DTg00Sbj1MTg00T@j2LTg00Taj3PTg00UJj3CTg00<1j2HTg00Ujj4KTg005Xj1TTg00>;j2ATg00?lj1bTg00VHj3ITg00Vkj3`Tg00WNj3FTg00DMj1^Tg00EEj7\Tg00Eij7ZTg00@Nj8]Tf0R0#9#9p=3f1R1g00FMR2g00FlR3P3g00GLR4P0g00GlF\p=0g00HLR5P1g00K@P0C2p=@f2R6P2P3P3P4P1P0FZp=Jf3R7P2P3P3P4P6P1P0G]p=Gg00HjR8/10g00IHR9#9R:#9#3#3#3#3#3#BR;,41R<%B9R='<R>g00ImR?#XR@%S?RA%R5RB%O5RC%N5RDP2P3P3P4P51>5;R2g00X1RE1>58RFC2,0DEa1_D4R4P0P6g00KgRGg00LGRH'[1Y06=:GHdAW581CVRHb1b2b3A:5;8g00XX[P0b07U;1E>;,?;1=>;'49:5>146;RG/<=RIP@PAPBPC1@F2,0DP4PHb1b2b3118;P0b07Q;1=I;RI,6811I;'7g00Y5RI#;RB#;RJ,85185BRB185IRI555555g00YTRK'D%;J,85%M9,L5=P5B=55I555/DK=C?@5C?PAP51H56P11H57CKPCPDP5PFg00JYRF%T9,A5RCC2,0D1@C2,0D5JD%b3R3PDP51A59R9=I52RA1>5=5`5PE1A5:R:9F52=I5CC2,0DP3P5P9PFAF5:2R:C2,0D1@:A,0D5JDCGCGP4PHb1b2b3X45X55X651686116;'71?;6/479:5>1?7;R7,66117G'7[[^45^55^65P0f4R0/4;/<=R=/=;1E=;P0P1P6O5b0b8b7%^1R6,61116<'7eUX95o"). Qed.

Lemma nstepA_mmap_ed : forall addr len prot flags mo eff mo' evs,
  nstepA (NMmap addr len prot flags) mo eff mo' evs ->
  mmap_corner_free (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) mo eff ->
  check_mmap_ed (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
                (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo = CheckOk mo' evs.
Proof.
  intros addr len prot flags mo eff mo' evs H Hcf. apply nstepA_mmap_iff in H as [H Hns].
  cbn [mm_ns node_input] in Hns.
  apply check_mmap_ed_fwd; [exact H| | exact Hcf].
  exact (forced_of_ns_mmap (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags;
                                            Z_to_bv 64 (-1); Z_to_bv 64 0]) mo eff ltac:(reflexivity) Hns).
Qed.

Lemma nstepA_mmap_of_ed : forall addr len prot flags mo eff mo' evs,
  check_mmap_ed (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
                (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo = CheckOk mo' evs ->
  nstepA (NMmap addr len prot flags) mo eff mo' evs.
Proof.
  intros addr len prot flags mo eff mo' evs H.
  destruct (ns_of_check_mmap_ed
              (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags;
                               Z_to_bv 64 (-1); Z_to_bv 64 0]) mo eff mo' evs ltac:(reflexivity) H) as [Hc Hns].
  apply nstepA_mmap_iff. split; [|exact Hns].
  rewrite check_syscall_mmap in Hc by reflexivity. exact Hc.
Qed.

Section NodeSem.
Variable atop : Z.                         (* [comment removed for export] *)
Hypothesis Hatop : atop_ok atop.           (* [comment removed for export] *)

Let atop_lt : atop < 2^47.
Proof. destruct Hatop as [_ H]. unfold ATOP_MAX in H. lia. Qed.

(* [comment removed for export] *)
Let G_off : negb (mmap_off_aligned_b (Z_to_bv 64 0)) = false. Proof. reflexivity. Qed.
Let G_anon : forall flags, (flags = F_ANON \/ flags = F_FIXED \/ flags = F_FIXNORES) -> negb (mmap_anon_b (Z_to_bv 64 flags)) = false.
Proof. intros flags [-> |[-> | ->]]; reflexivity. Qed.

Lemma grant_answers : forall len mo rsp mo' evs,
  0 < len <= 2^40 -> alloc_top (m_vmmaps mo) = atop ->
  vm_backing_used mo + mmap_len len <= vm_limit (m_vmmaps mo) ->
  vm_gap_available (m_vmmaps mo) (mmap_len len) = true ->
  nstepA (NMmap 0 len PROT_RW F_ANON) mo rsp mo' evs ->
  evs = [] /\ exists z, adec_mmap atop len PROT_RW rsp = Some z
   /\ z mod 4096 = 0 /\ 0 < z /\ z + mmap_len len <= atop
   /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 z) (Z_to_bv 64 (mmap_len len)) = true
   /\ mo' = grant_model mo z (mmap_len len).
Proof.
  intros len mo rsp mo' evs Hlen Htop Hbud Hgap Hst.
  apply nstepA_mmap_ed in Hst; [| apply mmap_corner_free_not_rw; vm_compute; reflexivity].
  unfold check_mmap_ed in Hst.
  rewrite G_off, (G_anon F_ANON ltac:(auto)) in Hst.
  rewrite w_is0_lit in Hst by lia. replace (len =? 0) with false in Hst by (symmetry; apply Z.eqb_neq; lia).
  change (mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 F_ANON) (Z_to_bv 64 0)) with true in Hst.
  cbv iota beta in Hst. rewrite mmap_len_eq in Hst by lia.
  assert (Hnr : mmap_grant_refusable (Z_to_bv 64 F_ANON) mo (mmap_len len) = false).
  { unfold mmap_grant_refusable. rewrite Hgap. unfold mmap_noreserve_backed_ok.
    change (mmap_noreserve_b (Z_to_bv 64 F_ANON)) with false. cbv iota. rewrite (proj2 (Z.leb_le _ _) Hbud). reflexivity. }
  rewrite Hnr in Hst. change (mmap_errnos_when false) with (@nil Z) in Hst. cbn [errno_ret_in existsb] in Hst.
  destruct rsp as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
  destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
  cbv zeta in Hst.
  match type of Hst with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
  injection Hst as <- <-. split; [reflexivity|].
  apply andb_prop in E as [E Hzs]. apply andb_prop in E as [E Hb]. apply andb_prop in E as [E Hrf].
  apply andb_prop in E as [E Htp]. apply andb_prop in E as [Hal Hpos].
  apply Z.eqb_eq in Hal. apply Z.ltb_lt in Hpos. apply Z.leb_le in Htp. apply listNN_eqb_eq in Hzs.
  rewrite Htop in Htp. unfold page_size in Hal.
  subst zs. exists (bv_unsigned r).
  assert (Hr : Z_to_bv 64 (bv_unsigned r) = r) by apply Z_to_bv_bv_unsigned.
  rewrite Hr. split.
  - unfold adec_mmap. change (PROT_RW =? 0) with false. cbv iota. unfold dec_mmap.
    rewrite !bv_eqb_refl.
    replace (mmap_addr_ok atop len [] (bv_unsigned r)) with true; [reflexivity|].
    symmetry. unfold mmap_addr_ok. cbn [avoids forallb]. unfold page_size. rewrite Hal, (proj2 (Z.ltb_lt _ _) Hpos), (proj2 (Z.leb_le _ _) Htp). reflexivity.
  - split; [exact Hal|]. split; [exact Hpos|]. split; [exact Htp|]. split; [exact Hrf|].
    unfold grant_model, with_mmap_backing. change (mmap_noreserve_b (Z_to_bv 64 F_ANON)) with false. cbv iota.
    rewrite Hr. reflexivity.
Qed.

Lemma grant_exists : forall len mo,
  0 < len <= 2^40 -> alloc_top (m_vmmaps mo) = atop ->
  vm_backing_used mo + mmap_len len <= vm_limit (m_vmmaps mo) ->
  vm_gap_available (m_vmmaps mo) (mmap_len len) = true ->
  exists rsp mo' evs, nstepA (NMmap 0 len PROT_RW F_ANON) mo rsp mo' evs.
Proof.
  intros len mo Hlen Htop Hbud Hgap.
  destruct (vm_gap_available_find _ _ Hgap) as [a Hf].
  pose proof (vm_find_base_sound _ _ _ Hf) as (A1 & A2 & A3 & A4).
  eexists (mkEffectU a [] [(a, Z_to_bv 64 (mmap_len len))] [] [] []), _, [].
  apply nstepA_mmap_of_ed. unfold check_mmap_ed.
  rewrite G_off, (G_anon F_ANON ltac:(auto)).
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  change (mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 F_ANON) (Z_to_bv 64 0)) with true.
  cbv iota beta. rewrite mmap_len_eq by lia.
  assert (Hnr : mmap_grant_refusable (Z_to_bv 64 F_ANON) mo (mmap_len len) = false).
  { unfold mmap_grant_refusable. rewrite Hgap. unfold mmap_noreserve_backed_ok.
    change (mmap_noreserve_b (Z_to_bv 64 F_ANON)) with false. cbv iota. rewrite (proj2 (Z.leb_le _ _) Hbud). reflexivity. }
  rewrite Hnr. change (mmap_errnos_when false) with (@nil Z). cbn [errno_ret_in existsb]. cbv zeta.
  rewrite A1, (proj2 (Z.ltb_lt _ _) A2), (proj2 (Z.leb_le _ _) A3), A4.
  unfold mmap_noreserve_backed_ok. change (mmap_noreserve_b (Z_to_bv 64 F_ANON)) with false. cbv iota. rewrite (proj2 (Z.leb_le _ _) Hbud).
  cbn [andb]. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma fixed_shape : forall flags, (flags = F_FIXED \/ flags = F_FIXNORES) ->
  mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false
  /\ mmap_fixed_rw_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true.
Proof. intros flags [-> | ->]; repeat split; reflexivity. Qed.

Lemma fixed_answers : forall addr len flags mo rsp mo' evs,
  (flags = F_FIXED \/ flags = F_FIXNORES) -> 0 < len <= 2^40 -> 0 < addr -> addr mod 4096 = 0 ->
  alloc_top (m_vmmaps mo) = atop -> addr + mmap_len len <= atop ->
  let n := Z_to_bv 64 (mmap_len len) in
  region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  mmap_fixed_rw_budget_ok (Z_to_bv 64 flags) mo (Z_to_bv 64 addr) n = true ->
  nstepA (NMmap addr len PROT_RW flags) mo rsp mo' evs ->
  evs = [] /\ adec_mmap atop len PROT_RW rsp = Some addr
  /\ mo' = with_mmap_replacement (Z_to_bv 64 flags) (Z_to_bv 64 addr) n (with_vmmaps (mmap_fixed_rw_next (m_vmmaps mo) (Z_to_bv 64 addr) n) mo).
Proof.
  intros addr len flags mo rsp mo' evs Hfl Hlen Ha Hal Htop Hce n Hrf Hmc Hbud Hst.
  apply nstepA_mmap_ed in Hst;
    [| unfold mmap_corner_free; intros _; right; rewrite mmap_len_eq by lia; fold n; rewrite Hrf, Hmc;
       split; [reflexivity| exact Hbud]].
  unfold check_mmap_ed in Hst.
  rewrite G_off, (G_anon flags ltac:(tauto)) in Hst.
  rewrite w_is0_lit in Hst by lia. replace (len =? 0) with false in Hst by (symmetry; apply Z.eqb_neq; lia).
  destruct (fixed_shape flags Hfl) as (S1 & S2 & S3 & S4). rewrite S1, S2, S3, S4 in Hst. cbv iota beta in Hst.
  rewrite mmap_len_eq in Hst by lia. pose proof (mmap_len_bounds len ltac:(lia)) as ML. rewrite (unsigned_lit addr) in Hst by lia.
  cbv zeta in Hst.
  replace (two_pow_64 <=? addr + mmap_len len) with false in Hst by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia).
  rewrite Htop, (proj2 (Z.leb_le _ _) Hce) in Hst. unfold page_size in Hst. rewrite Hal in Hst. rewrite (proj2 (Z.ltb_lt _ _) Ha) in Hst.
  cbn [negb Z.eqb] in Hst. fold n in Hst. rewrite Hrf, Hmc in Hst. cbn [andb] in Hst.
  assert (Hnr : mmap_fixed_commit_refusable (Z_to_bv 64 flags) mo (Z_to_bv 64 addr) n = false).
  { unfold mmap_fixed_commit_refusable. rewrite Hbud. reflexivity. }
  rewrite Hnr in Hst. change (mmap_errnos_when false) with (@nil Z) in Hst. change mmap_destructive_errnos with (@nil Z) in Hst.
  cbn [errno_ret_in existsb andb] in Hst. cbv iota in Hst.
  destruct rsp as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  destruct us; [|discriminate].
  match type of Hst with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
  injection Hst as <- <-. split; [reflexivity|].
  apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2]. apply bv_eqb_eq in E1. apply listNN_eqb_eq in E2. subst r zs.
  split; [|reflexivity].
  unfold adec_mmap. change (PROT_RW =? 0) with false. cbv iota. unfold dec_mmap. fold n. rewrite !bv_eqb_refl.
  rewrite unsigned_lit by lia.
  replace (mmap_addr_ok atop len [] addr) with true; [reflexivity|].
  symmetry. unfold mmap_addr_ok. cbn [avoids forallb]. unfold page_size. rewrite Hal, (proj2 (Z.ltb_lt _ _) Ha), (proj2 (Z.leb_le _ _) Hce). reflexivity.
Qed.

Lemma fixed_exists : forall addr len flags mo,
  (flags = F_FIXED \/ flags = F_FIXNORES) -> 0 < len <= 2^40 -> 0 < addr -> addr mod 4096 = 0 ->
  alloc_top (m_vmmaps mo) = atop -> addr + mmap_len len <= atop ->
  let n := Z_to_bv 64 (mmap_len len) in
  region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  mmap_fixed_rw_budget_ok (Z_to_bv 64 flags) mo (Z_to_bv 64 addr) n = true ->
  exists rsp mo' evs, nstepA (NMmap addr len PROT_RW flags) mo rsp mo' evs.
Proof.
  intros addr len flags mo Hfl Hlen Ha Hal Htop Hce n Hrf Hmc Hbud.
  eexists (mkEffectU (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, n)] [] [] []), _, [].
  apply nstepA_mmap_of_ed. unfold check_mmap_ed.
  rewrite G_off, (G_anon flags ltac:(tauto)).
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct (fixed_shape flags Hfl) as (S1 & S2 & S3 & S4). rewrite S1, S2, S3, S4. cbv iota beta.
  rewrite mmap_len_eq by lia. pose proof (mmap_len_bounds len ltac:(lia)) as ML. rewrite (unsigned_lit addr) by lia.
  cbv zeta.
  replace (two_pow_64 <=? addr + mmap_len len) with false by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia).
  rewrite Htop, (proj2 (Z.leb_le _ _) Hce). unfold page_size. rewrite Hal. rewrite (proj2 (Z.ltb_lt _ _) Ha).
  cbn [negb Z.eqb]. fold n. rewrite Hrf, Hmc. cbn [andb].
  assert (Hnr : mmap_fixed_commit_refusable (Z_to_bv 64 flags) mo (Z_to_bv 64 addr) n = false).
  { unfold mmap_fixed_commit_refusable. rewrite Hbud. reflexivity. }
  rewrite Hnr. change (mmap_errnos_when false) with (@nil Z). change mmap_destructive_errnos with (@nil Z).
  cbn [errno_ret_in existsb andb]. cbv iota. rewrite !bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl), Hbud. reflexivity.
Qed.

Lemma munmap_answers : forall addr len mo rsp mo' evs,
  0 < len <= 2^40 -> 0 <= addr -> addr mod 4096 = 0 -> addr + mmap_len len <= atop ->
  let n := Z_to_bv 64 (mmap_len len) in
  map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  nstepA (NMunmap addr len) mo rsp mo' evs ->
  evs = [] /\ adec_munmap addr len rsp = Some 0
  /\ mo' = munmap_model mo addr (mmap_len len).
Proof.
  intros addr len mo rsp mo' evs Hlen Ha Hal Hce n Hmh Hst.
  pose proof (mmap_len_bounds len ltac:(lia)) as ML. pose proof TASK_SIZE_val as TS.
  cbn [nstepA] in Hst. apply nstep_munmap_iff in Hst. unfold check_munmap in Hst.
  rewrite (unsigned_lit addr) in Hst by lia. unfold page_size in Hst. rewrite Hal in Hst.
  rewrite w_is0_lit in Hst by lia. replace (len =? 0) with false in Hst by (symmetry; apply Z.eqb_neq; lia). cbn [negb orb Z.eqb] in Hst.
  rewrite mmap_len_eq in Hst by lia. cbv zeta in Hst.
  replace (TASK_SIZE <? addr + mmap_len len) with false in Hst by (symmetry; apply Z.ltb_ge; lia).
  fold n in Hst. rewrite Hmh in Hst.
  destruct rsp as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  match type of Hst with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
  injection Hst as <- <-. split; [reflexivity|].
  apply andb_prop in E as [E1 E2]. unfold w_is0 in E1. apply bv_eqb_eq in E1. apply listNN_eqb_eq in E2. subst r us.
  split.
  - unfold adec_munmap, dec_munmap. rewrite (unsigned_lit 0) by lia. cbn [Z.eqb]. fold n. rewrite !bv_eqb_refl. reflexivity.
  - unfold munmap_model. fold n. subst n. rewrite (unsigned_lit (mmap_len len)) by lia. reflexivity.
Qed.

Lemma munmap_exists : forall addr len mo,
  0 < len <= 2^40 -> 0 <= addr -> addr mod 4096 = 0 -> addr + mmap_len len <= atop ->
  let n := Z_to_bv 64 (mmap_len len) in
  map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  exists rsp mo' evs, nstepA (NMunmap addr len) mo rsp mo' evs.
Proof.
  intros addr len mo Hlen Ha Hal Hce n Hmh.
  pose proof (mmap_len_bounds len ltac:(lia)) as ML. pose proof TASK_SIZE_val as TS.
  eexists (mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, n)] [] []), _, [].
  cbn [nstepA]. apply nstep_munmap_iff. unfold check_munmap.
  rewrite (unsigned_lit addr) by lia. unfold page_size. rewrite Hal.
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb orb Z.eqb].
  rewrite mmap_len_eq by lia. cbv zeta.
  replace (TASK_SIZE <? addr + mmap_len len) with false by (symmetry; apply Z.ltb_ge; lia).
  fold n. rewrite Hmh. rewrite w_is0_lit by lia. cbn [Z.eqb]. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma madvise_next_canon : forall mo a n, m_vm_materialized mo = [] -> madvise_dontneed_next mo a n = mo.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodeSem ()) ["NodeSem"] "p'0h01Hh11lh21ah32fdh42fsh52ioh62lmh72lzh86m_fsysi006m_fsysh94m_ioi014m_ioh:5m_limi025m_limh;6m_proci036m_proch<6m_timei046m_timeh=4m_vmi054m_vmh>2moh?2mph@2mthA1nhB2prhC2tmi061mi074m_fdi081vi099vmst_lazyi0:9vmst_mapsi0;Avmst_materializedp;1p;3p;2p;7p;6g004Uj11Tg009Cj1DTg00aij1=Tg00;Qj1:Tg025jj10Tg00;1j1BTg008Oj34Tg0252j15Tg00:Gj27Tg00Lgj2;Tg0350j29Tg0361j38Tg03;4j33Tg02;hj76Tg01IUj2CTg026jj3<Tg008ij2ATg000`j6?Tg0027j6>Tg03<2j3@Tg00fMR0f1R1f0R234p=2g00IH#1#1#1#1#1#1#DR3#=R4%:4R5f2R6#0%B4R734P5P7f4R8#5R9f3R:,73R;1736R<,;;'9=842;38/28X15P5%0:R;A3928/28X15P0%02=457%51%01;31/21]0P:g03=?g03>7R9P9g03>oR9g03?gR=g03@_R>g03AYR?g03BRR@f7RAf5RBP8P:P6P1P2F6#0=457f8RCf6RDPBP8P:P6P1F6RE#5%0E;3E/2E]0]<]:];]8]9P2g03CL1C44#:f<A<ADBP8P:P6P1P2F6#0=457f=A<CADPBP8P:P6P1F6,A0W0XC@X6?XB>X4=X59X@5W7W?P6P1P2O3n0110800013010:10910;W=W3PDPBP8P:P6P1P2O7n01106000170107105101100103102104P2O1P7P2E?%5:1731,;<,9<=847;3:/2:eP;P2E>A@:61/2:eW0XA4W2X>0o"). Qed.

Lemma madvise_answers : forall addr len mo rsp mo' evs,
  0 < len <= 2^40 -> 0 <= addr -> addr mod 4096 = 0 -> addr + mmap_len len <= 2^47 ->
  let n := Z_to_bv 64 (mmap_len len) in
  m_vm_materialized mo = [] ->
  madvise_dontneed_ok (m_vmmaps mo) (Z_to_bv 64 addr) n = true ->
  nstepA (NMadvise addr len) mo rsp mo' evs ->
  evs = [] /\ adec_madvise addr len rsp = Some 0 /\ mo' = mo.
Proof.
  intros addr len mo rsp mo' evs Hlen Ha Hal Hce n Hcan Hok Hst.
  pose proof (mmap_len_bounds len ltac:(lia)) as ML.
  cbn [nstepA] in Hst. apply nstep_madvise_iff in Hst. unfold check_madvise in Hst.
  rewrite (unsigned_lit addr) in Hst by lia. unfold page_size in Hst. rewrite Hal in Hst.
  change (negb (madvise_dontneed_b (Z_to_bv 64 4))) with false in Hst.
  rewrite w_is0_lit in Hst by lia. replace (len =? 0) with false in Hst by (symmetry; apply Z.eqb_neq; lia). cbn [negb Z.eqb] in Hst. cbv iota in Hst.
  rewrite mmap_len_eq in Hst by lia.
  replace (two_pow_64 <=? addr + mmap_len len) with false in Hst by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia).
  cbv zeta iota in Hst. fold n in Hst. rewrite Hok in Hst.
  destruct rsp as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  match type of Hst with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
  injection Hst as <- <-. split; [reflexivity|].
  apply andb_prop in E as [E1 E2]. unfold w_is0 in E1. apply bv_eqb_eq in E1. apply listNN_eqb_eq in E2. subst r zs.
  split.
  - unfold adec_madvise, dec_madvise, dec_mprotect. rewrite (unsigned_lit 0) by lia. cbn [Z.eqb]. fold n. rewrite !bv_eqb_refl.
    replace (errno_of (Z_to_bv 64 0)) with (@None Z) by reflexivity. reflexivity.
  - apply madvise_next_canon. exact Hcan.
Qed.

Lemma madvise_exists : forall addr len mo,
  0 < len <= 2^40 -> 0 <= addr -> addr mod 4096 = 0 -> addr + mmap_len len <= 2^47 ->
  let n := Z_to_bv 64 (mmap_len len) in
  madvise_dontneed_ok (m_vmmaps mo) (Z_to_bv 64 addr) n = true ->
  exists rsp mo' evs, nstepA (NMadvise addr len) mo rsp mo' evs.
Proof.
  intros addr len mo Hlen Ha Hal Hce n Hok.
  pose proof (mmap_len_bounds len ltac:(lia)) as ML.
  eexists (mkEffectU (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, n)] [] [] []), _, [].
  cbn [nstepA]. apply nstep_madvise_iff. unfold check_madvise.
  rewrite (unsigned_lit addr) by lia. unfold page_size. rewrite Hal.
  change (negb (madvise_dontneed_b (Z_to_bv 64 4))) with false.
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb Z.eqb]. cbv iota.
  rewrite mmap_len_eq by lia.
  replace (two_pow_64 <=? addr + mmap_len len) with false by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia).
  cbv zeta iota. fold n. rewrite Hok. rewrite w_is0_lit by lia. cbn [Z.eqb]. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition aok (e : aev) (mo : Model) : Prop :=
  match e with
  | AMmap addr len prot flags =>
      prot = PROT_RW /\ 0 < len <= 2^40 /\ alloc_top (m_vmmaps mo) = atop /\
      if addr =? 0 then
        flags = F_ANON /\ vm_backing_used mo + mmap_len len <= vm_limit (m_vmmaps mo)
        /\ vm_gap_available (m_vmmaps mo) (mmap_len len) = true
      else
        (flags = F_FIXED \/ flags = F_FIXNORES) /\ 0 < addr /\ addr mod 4096 = 0 /\ addr + mmap_len len <= atop
        /\ region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)) = true
        /\ map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)) = true
        /\ mmap_fixed_rw_budget_ok (Z_to_bv 64 flags) mo (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)) = true
  | AMunmap addr len =>
      0 < len <= 2^40 /\ 0 <= addr /\ addr mod 4096 = 0 /\ addr + mmap_len len <= atop
      /\ map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)) = true
  | AMadvise addr len =>
      0 < len <= 2^40 /\ 0 <= addr /\ addr mod 4096 = 0 /\ addr + mmap_len len <= 2^47
      /\ m_vm_materialized mo = []
      /\ madvise_dontneed_ok (m_vmmaps mo) (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)) = true
  | _ => False
  end.

Definition apost (e : aev) (mo : Model) (z : Z) (mo' : Model) : Prop :=
  match e with
  | AMmap addr len prot flags =>
      if addr =? 0 then
        z mod 4096 = 0 /\ 0 < z /\ z + mmap_len len <= atop
        /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 z) (Z_to_bv 64 (mmap_len len)) = true
        /\ mo' = grant_model mo z (mmap_len len)
      else z = addr /\ mo' = fixed_model mo flags addr (mmap_len len)
  | AMunmap addr len => z = 0 /\ mo' = munmap_model mo addr (mmap_len len)
  | AMadvise addr len => z = 0 /\ mo' = mo
  | _ => False
  end.

Theorem asan_node_sound : node_sound atop nstepA aok apost.
Proof.
  intros e mo Hok. destruct e as [t|b|addr len prot flags|addr len|a l p|addr len|w]; try (destruct Hok; fail); try contradiction.
  -
    cbn [aok] in Hok. destruct Hok as (-> & Hlen & Htop & Hc).
    exists (NMmap addr len PROT_RW flags), (adec_mmap atop len PROT_RW). split; [reflexivity|].
    destruct (Z.eqb_spec addr 0) as [->|Hnz].
    + destruct Hc as (-> & Hbud & Hgap). split; [|split].
      * intros rsp mo' evs Hst. destruct (grant_answers len mo rsp mo' evs Hlen Htop Hbud Hgap Hst) as (-> & z & Hd & H1 & H2 & H3 & H4 & ->).
        split; [reflexivity|]. exists z. split; [exact Hd|]. cbn [apost]. rewrite Z.eqb_refl. repeat split; auto.
      * apply grant_exists; auto.
      * intros code mo' Hx. exact Hx.
    + destruct Hc as (Hfl & Ha & Hal & Hce & Hrf & Hmc & Hbud). split; [|split].
      * intros rsp mo' evs Hst. destruct (fixed_answers addr len flags mo rsp mo' evs Hfl Hlen Ha Hal Htop Hce Hrf Hmc Hbud Hst) as (-> & Hd & ->).
        split; [reflexivity|]. exists addr. split; [exact Hd|]. cbn [apost]. replace (addr =? 0) with false by (symmetry; apply Z.eqb_neq; lia). split; reflexivity.
      * apply (fixed_exists addr len flags mo); auto.
      * intros code mo' Hx. exact Hx.
  -
    cbn [aok] in Hok. destruct Hok as (Hlen & Ha & Hal & Hce & Hmh).
    exists (NMunmap addr len), (adec_munmap addr len). split; [reflexivity|]. split; [|split].
    + intros rsp mo' evs Hst. destruct (munmap_answers addr len mo rsp mo' evs Hlen Ha Hal Hce Hmh Hst) as (-> & Hd & ->).
      split; [reflexivity|]. exists 0. split; [exact Hd|]. cbn [apost]. split; reflexivity.
    + apply (munmap_exists addr len mo); auto.
    + intros code mo' Hx. exact Hx.
  -
    cbn [aok] in Hok. destruct Hok as (Hlen & Ha & Hal & Hce & Hcan & Hmok).
    exists (NMadvise addr len), (adec_madvise addr len). split; [reflexivity|]. split; [|split].
    + intros rsp mo' evs Hst. destruct (madvise_answers addr len mo rsp mo' evs Hlen Ha Hal Hce Hcan Hmok Hst) as (-> & Hd & ->).
      split; [reflexivity|]. exists 0. split; [exact Hd|]. cbn [apost]. split; reflexivity.
    + apply (madvise_exists addr len mo); auto.
    + intros code mo' Hx. exact Hx.
Qed.

(* [comment removed for export] *)
Corollary atotal_STOT_asan : forall {R} (t : AM R) (s : APS) mo (Post : R -> Model -> Prop),
  aps_atop s = atop ->
  atotal aok apost t mo Post ->
  STOT (St:=APS) nstepA (fun R0 => texit (R:=R0) nstepA nexit) (alift t s) mo (fun r s' mo' => s' = s /\ Post r mo').
Proof. intros. apply (atotal_STOT atop nstepA aok apost asan_node_sound); assumption. Qed.
End NodeSem.
