(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (a fresh grant at Linux's placement (grant_check; the NULL hint is never declined); 3 recorded proofs replaced by written proofs (mmap_len_eq, mmap_len_bounds, madvise_next_canon); grant_answers, grant_exists, munmap_answers restated for the revision's model; adds aligned_not_errno, nstepA_mmap_of_nonrefusal, nstepA_mmap_nonrefusal and 3 more; drops nstepA_mmap_ed, nstepA_mmap_of_ed; aok redefined for the revision's model; imports; requires Cfg (Cfg.refusal_b_215)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import NodesA.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Placement.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed Monad RSim AsanProgDeps AsanTotalCore AsanInv.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AsanNodeSem () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode8mmap_lenC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K59OSSVerify5KrLib3Lib5Nodes4node0:C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA6nstepAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4MmEd@mmap_corner_freeC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap:check_mmapK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result01C59OSSVerify5KrLib3Lib5Nodes5mm_nsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA?nstepA_mmap_iffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4MmEd=check_mmap_edC1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib3Lib5Nodes:pure_inputC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4MmEdAforced_of_ns_mmapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4MmEdAcheck_mmap_ed_fwdC1?~~~~~~~~~~~~~~~I6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C59OSSVerify5KrLib3Lib4MmEdCns_of_check_mmap_edC1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem6Checks?ExecutableSpecs=check_syscallC4ELinuxProcessSemantics?LinuxProcessSem3RunDspurious_refusal_cfgC47Corelib4Init5Logic3notC4ELinuxProcessSemantics?LinuxProcessSem5State6in_argC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys?DispatchComputeBcheck_syscall_mmapK47Corelib4Init5Logic3and01I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00C59OSSVerify5KrLib3Lib3Cfg4ACFGC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareC59OSSVerify5KrLib4Spec7AsanInv5ACEILC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv8ATOP_MAXC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic2or00C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;mmap_anon_bC47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib4Spec8AsanCtrl6F_ANONC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7F_FIXEDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:F_FIXNORESC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backing_usedC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC59OSSVerify5KrLib3Lib9Placement@vm_gap_availableC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_fixed_rw_bC59OSSVerify5KrLib3Lib4MmEdGmmap_corner_free_not_rwC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;AsanNodeSem>nstepA_mmap_edC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_off_aligned_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_pglen_ok_bC4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude>check_ret_onlyC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5w_is0C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapAmmap_plain_anon_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>mmap_modeled_bI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapHmmap_noreserve_backed_okK47Corelib4Init9Datatypes4prod01C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude:listNN_eqbC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_noaccess_bC59OSSVerify5KrLib3Lib9PlacementFmmap_reserve_refusableC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEmmap_fixed_noaccess_bC4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeC4ELinuxProcessSemantics?LinuxProcessSem5State<map_containsC47Corelib4Init9Datatypes4andbC59OSSVerify5KrLib3Lib4MmEd6w_nilbC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<errno_ret_inC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapImmap_fixed_destroyed_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapCwith_mmap_destroyedC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC4ELinuxProcessSemantics?LinuxProcessSem5State=maps_subtractC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapMmmap_fixed_noaccess_span_nextC59OSSVerify5KrLib3Lib9PlacementKmmap_fixed_commit_refusableC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_budget_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_fixed_rw_nextC59OSSVerify5KrLib3Lib9PlacementJmmap_fixed_fresh_refusableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9PlacementImmap_fixed_span_refusableC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapLmmap_fixed_rw_span_budget_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_span_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapImmap_noreplace_noaccess_bC47Corelib4Init9Datatypes3orbC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapCmmap_noreplace_rw_bK47Corelib4Init5Logic2or01C59OSSVerify5KrLib3Lib5Nodes9w_is0_litC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqK46Stdlib9micromega5Tauto8GFormula03C47Corelib4Init5Logic6eq_symC47Corelib4Init9Datatypes3appc59OSSVerify5KrLib4Spec;AsanNodeSem;mmap_len_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init5Logic5proj2C59OSSVerify5KrLib3Lib9PlacementDmmap_grant_refusableC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedK4ELinuxProcessSemantics?LinuxProcessSem5State7VmState01C4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State6m_timeK4ELinuxProcessSemantics?LinuxProcessSem5State5Model01C4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsK4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C59OSSVerify5KrLib4Spec7AsanInv;grant_modelC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude=listNN_eqb_eqC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapAwith_mmap_backingC59OSSVerify5KrLib3Lib6MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode<mmap_addr_okC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib6Decode8mmap_ans02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode6avoidsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode8dec_mmapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode=dec_mmap_noneC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_add_lazyK47Corelib4Init5Logic2ex01C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib3Lib9Placement@mmap_errnos_whenC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEwith_mmap_replacementC59OSSVerify5KrLib4Spec9AsanEmbed9adec_mmapC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeC4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64C59OSSVerify5KrLib4Spec8AsanCtrl7PROT_RWC1?~~~~~~~~~~~~~~~K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result02K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics?LinuxProcessSem5State6EINVALK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result03I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I47Corelib4Init9Datatypes3nat00C4ELinuxProcessSemantics?LinuxProcessSem5State6ENOMEMC59OSSVerify5KrLib3Lib9PlacementGmmap_destructive_errnosC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State6EEXISTI59OSSVerify5KrLib3Lib6Decode8mmap_ans00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9PlacementEvm_gap_available_findC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9Placement<vm_find_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9PlacementBvm_find_base_soundC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegc59OSSVerify5KrLib4Spec;AsanNodeSemAnstepA_mmap_of_edC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:eff_unmapsK47Corelib4Init5Logic2or02C47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indc59OSSVerify5KrLib4Spec;AsanNodeSem;fixed_shapeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;AsanNodeSem?mmap_len_boundsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_gtC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z<pos_div_euclC56Stdlib6ZArith6BinInt1Z3oppC57Corelib7BinNums6PosDef3Pos4landC56Stdlib6ZArith6BinInt1Z4of_NC57Corelib7BinNums6PosDef3Pos6pred_NC57Corelib7BinNums6NatDef1N5ldiffC57Corelib7BinNums6NatDef1N3lorC57Corelib7BinNums6NatDef1N8succ_posC57Corelib7BinNums6PosDef3Pos3eqbC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_forget_rangeC4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap=MAP_NORESERVEC4ELinuxProcessSemantics?LinuxProcessSem5State7map_hasK59OSSVerify5KrLib3Lib5Nodes4node0;C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nstepC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap<check_munmapC59OSSVerify5KrLib3Lib5Nodes@nstep_munmap_iffC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:map_removeC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>munmap_free_okC56Stdlib6ZArith6BinInt1Z6ltb_geC59OSSVerify5KrLib4Spec9AsanEmbed;adec_munmapC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateBpage_outside_rangeC46Stdlib5Lists4List6filterK59OSSVerify5KrLib3Lib6Decode9range_ans02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv<munmap_modelC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9TASK_SIZEC59OSSVerify5KrLib3Lib5Nodes=TASK_SIZE_valC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib6Decode9range_ans00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?with_vm_backingC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm7MadviseEmadvise_dontneed_nextI4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State7VmState00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00K59OSSVerify5KrLib3Lib5Nodes4node0=C1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm7Madvise=check_madviseC59OSSVerify5KrLib3Lib5NodesAnstep_madvise_iffC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm7MadviseBmadvise_dontneed_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm7MadviseCmadvise_dontneed_okC59OSSVerify5KrLib4Spec9AsanEmbed<adec_madviseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode8errno_ofC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;AsanNodeSemBmadvise_next_canonC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4RSim4STOTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5texitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;AsanNodeSem3aokC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl3aev01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl3aev02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl3aev03C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C59OSSVerify5KrLib3Lib5Nodes5nexitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;AsanNodeSem=grant_answersC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv;fixed_modelC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_reflc59OSSVerify5KrLib4Spec;AsanNodeSem<grant_existsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;AsanNodeSem=fixed_answersC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;AsanNodeSem<fixed_existsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl3aev04C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;AsanNodeSem>munmap_answersC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;AsanNodeSem5apostC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;AsanNodeSem=munmap_existsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl3aev05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl3aev06C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;AsanNodeSem?madvise_answersC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec;AsanNodeSem>madvise_existsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl3aev07C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec=AsanTotalCore:node_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec=AsanTotalCore8aev_nodeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl3aev00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6aundef00C1?~~~~~~~~~~~~~~~".
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Cfg.
Import ListNotations.
Open Scope Z_scope.

Lemma mmap_len_eq : forall len, 0 <= len < 2^63 -> page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) = mmap_len len.
Proof. intros. unfold mmap_len. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma mmap_len_bounds : forall l, 0 < l -> l <= mmap_len l < l + 4096.
Proof. intros. unfold mmap_len, page_round_up_Z, page_size. pose proof (Z.div_mod (l + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (l + 4096 - 1) 4096 ltac:(lia)). lia. Qed.

Lemma aligned_not_errno : forall a, bv_unsigned a mod page_size = 0 -> errno_ret_in mmap_errnos a = false.
Proof.
  intros a H. unfold errno_ret_in, mmap_errnos. cbn [existsb]. rewrite orb_false_r.
  destruct (bv_eqb a (errno_ret ENOMEM)) eqn:E; [|reflexivity].
  apply bv_eqb_eq in E. subst a. vm_compute in H. discriminate H.
Qed.

(* The no-refusal reading of the mmap node, by the nonspurious condition [mm_ns] of [nstepA_mmap_iff]. *)
Lemma nstepA_mmap_of_nonrefusal : forall addr len prot flags m eff m' evs,
  check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff m = CheckOk m' evs ->
  errno_ret_in mmap_errnos (eff_ret eff) = false ->
  nstepA (NMmap addr len prot flags) m eff m' evs.
Proof.
  intros addr len prot flags m eff m' evs Hc Hnr. apply nstepA_mmap_iff. split; [exact Hc|].
  cbn [mm_ns node_input]. apply LinuxProcessSemantics.LinuxProcessSem.Run.spurious_refusal_not_refusal. rewrite refusal_b_222 by reflexivity. exact Hnr.
Qed.

Lemma nstepA_mmap_nonrefusal : forall addr len prot flags m eff m' evs effg mg evsg,
  nstepA (NMmap addr len prot flags) m eff m' evs ->
  check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) effg m = CheckOk mg evsg ->
  errno_ret_in mmap_errnos (eff_ret effg) = false ->
  errno_ret_in mmap_errnos (eff_ret eff) = false.
Proof.
  intros addr len prot flags m eff m' evs effg mg evsg Hn Hg Hgr. apply nstepA_mmap_iff in Hn as [_ Hns].
  cbn [mm_ns node_input] in Hns.
  assert (E : bv_unsigned (in_sysno (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags;
                                                     Z_to_bv 64 (-1); Z_to_bv 64 0])) = 222) by reflexivity.
  change (errno_ret_in mmap_errnos (eff_ret eff)) with (LinuxProcessSemantics.LinuxProcessSem.Run.ret_in_errnos mmap_errnos (eff_ret eff)).
  rewrite <- (refusal_b_222 _ m _ E).
  apply (nonspurious_not_refusal_of_grant ACFG _ m eff effg mg evsg).
  - exact (acfg_family_off_222 _ E).
  - exact Hns.
  - apply check_syscall_ok_iff. dispatch_pure 222. exact Hg.
  - rewrite (refusal_b_222 _ m _ E). exact Hgr.
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

(* LPS 727298f3: a fresh grant takes the one address Linux places the request at ([mmap_place_found],
   read at the hint), so the no-refusal premise is that Linux places the request, where it was that
   some free base exists; the NULL hint is never declined ([place_declined_b_null]). *)
Lemma grant_check : forall len mo,
  0 < len <= 2^40 -> alloc_top (m_vmmaps mo) = atop ->
  vm_backing_used mo + mmap_len len <= vm_limit (m_vmmaps mo) ->
  mmap_place_found mo (Z_to_bv 64 0) (mmap_len len) = true ->
  exists eff mo', check_mmap (Z_to_bv 64 0) (Z_to_bv 64 len) (Z_to_bv 64 PROT_RW) (Z_to_bv 64 F_ANON) (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
                             eff mo = CheckOk mo' []
                  /\ errno_ret_in mmap_errnos (eff_ret eff) = false.
Proof.
  intros len mo Hlen Htop Hbud Hpf.
  pose proof (mmap_len_bounds len ltac:(lia)) as MLB.
  assert (HnA : mmap_len len mod page_size = 0) by (unfold mmap_len, page_round_up_Z; apply Z_mod_mult).
  assert (HnP : 0 < mmap_len len) by lia.
  destruct (place_found_witness mo (Z_to_bv 64 0) (mmap_len len) HnP HnA Hpf) as (a & Pl & A1).
  exists (mkEffectU a [] [(a, Z_to_bv 64 (mmap_len len))] [] [] []). eexists. split; [|exact (aligned_not_errno a A1)].
  unfold check_mmap, check_mmap_fixed_overflow.
  rewrite G_off, (G_anon F_ANON ltac:(auto)).
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  change (mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 F_ANON) (Z_to_bv 64 0)) with true.
  cbv iota beta. rewrite place_declined_b_null. cbv iota beta. rewrite mmap_len_eq by lia.
  rewrite (aligned_not_errno a A1). cbv iota zeta.
  rewrite Pl.
  unfold mmap_noreserve_backed_ok. change (mmap_noreserve_b (Z_to_bv 64 F_ANON)) with false. cbv iota. rewrite (proj2 (Z.leb_le _ _) Hbud).
  cbn [andb]. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma grant_answers : forall len mo rsp mo' evs,
  0 < len <= 2^40 -> alloc_top (m_vmmaps mo) = atop ->
  vm_backing_used mo + mmap_len len <= vm_limit (m_vmmaps mo) ->
  mmap_place_found mo (Z_to_bv 64 0) (mmap_len len) = true ->
  nstepA (NMmap 0 len PROT_RW F_ANON) mo rsp mo' evs ->
  evs = [] /\ exists z, adec_mmap atop len PROT_RW rsp = Some z
   /\ z mod 4096 = 0 /\ 0 < z /\ z + mmap_len len <= atop
   /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 z) (Z_to_bv 64 (mmap_len len)) = true
   /\ mo' = grant_model mo z (mmap_len len).
Proof.
  intros len mo rsp mo' evs Hlen Htop Hbud Hpf Hst.
  destruct (grant_check len mo Hlen Htop Hbud Hpf) as (effg & mg & Hg & Hgr).
  pose proof (nstepA_mmap_nonrefusal _ _ _ _ _ _ _ _ _ _ _ Hst Hg Hgr) as Hnr.
  apply nstepA_mmap_iff in Hst as [Hst _]. unfold check_mmap, check_mmap_fixed_overflow in Hst.
  rewrite G_off, (G_anon F_ANON ltac:(auto)) in Hst.
  rewrite w_is0_lit in Hst by lia. replace (len =? 0) with false in Hst by (symmetry; apply Z.eqb_neq; lia).
  change (mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 F_ANON) (Z_to_bv 64 0)) with true in Hst.
  cbv iota beta in Hst. rewrite place_declined_b_null in Hst. cbv iota beta in Hst. rewrite mmap_len_eq in Hst by lia.
  destruct rsp as [r ws zs us cs ci]. cbn [eff_ret] in Hnr. destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
  destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
  cbv iota in Hst. rewrite Hnr in Hst. cbv iota zeta in Hst.
  match type of Hst with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
  injection Hst as <- <-. split; [reflexivity|].
  apply andb_prop in E as [E Hzs]. apply andb_prop in E as [EP Hb].
  pose proof (mmap_len_bounds len ltac:(lia)) as MLB.
  assert (HnA : mmap_len len mod page_size = 0) by (unfold mmap_len, page_round_up_Z; apply Z_mod_mult).
  assert (HnP : 0 < mmap_len len) by lia.
  destruct (LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.linux_place_is_admissible _ _ _ _ _ HnP HnA EP)
    as (Hal & Hpos & Htp & Hrf).
  apply listNN_eqb_eq in Hzs.
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
  mmap_place_found mo (Z_to_bv 64 0) (mmap_len len) = true ->
  exists rsp mo' evs, nstepA (NMmap 0 len PROT_RW F_ANON) mo rsp mo' evs.
Proof.
  intros len mo Hlen Htop Hbud Hpf.
  destruct (grant_check len mo Hlen Htop Hbud Hpf) as (effg & mg & Hg & Hgr).
  exists effg, mg, []. apply nstepA_mmap_of_nonrefusal; [exact Hg| exact Hgr].
Qed.

Lemma fixed_shape : forall flags, (flags = F_FIXED \/ flags = F_FIXNORES) ->
  mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false
  /\ mmap_fixed_rw_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true.
Proof. intros flags [-> | ->]; repeat split; reflexivity. Qed.

Lemma fixed_check : forall addr len flags mo,
  (flags = F_FIXED \/ flags = F_FIXNORES) -> 0 < len <= 2^40 -> 0 < addr -> addr mod 4096 = 0 ->
  alloc_top (m_vmmaps mo) = atop -> addr + mmap_len len <= atop ->
  let n := Z_to_bv 64 (mmap_len len) in
  region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  mmap_fixed_rw_budget_ok (Z_to_bv 64 flags) mo (Z_to_bv 64 addr) n = true ->
  exists eff mo', check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 PROT_RW) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
                             eff mo = CheckOk mo' []
                  /\ errno_ret_in mmap_errnos (eff_ret eff) = false.
Proof.
  intros addr len flags mo Hfl Hlen Ha Hal Htop Hce n Hrf Hmc Hbud.
  pose proof atop_lt as AT. pose proof (mmap_len_bounds len ltac:(lia)) as ML.
  assert (AN : errno_ret_in mmap_errnos (Z_to_bv 64 addr) = false).
  { apply aligned_not_errno. rewrite unsigned_lit by lia. exact Hal. }
  exists (mkEffectU (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, n)] [] [] []). eexists. split; [|exact AN].
unfold check_mmap, check_mmap_fixed_overflow.
  rewrite G_off, (G_anon flags ltac:(tauto)).
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct (fixed_shape flags Hfl) as (S1 & S2 & S3 & S4). rewrite S1, S2, S3, S4. cbv iota beta.
  rewrite mmap_len_eq by lia. rewrite (unsigned_lit addr) by lia.
  cbv zeta.
  replace (two_pow_64 <=? addr + mmap_len len) with false by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia).
  rewrite Htop, (proj2 (Z.leb_le _ _) Hce). unfold page_size. rewrite Hal. rewrite (proj2 (Z.ltb_lt _ _) Ha).
  cbn [negb Z.eqb]. fold n. rewrite Hrf, Hmc. cbn [andb].
  rewrite AN. cbv iota. rewrite !bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl), Hbud. reflexivity.
Qed.

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
  pose proof atop_lt as AT.
  destruct (fixed_check addr len flags mo Hfl Hlen Ha Hal Htop Hce Hrf Hmc Hbud) as (effg & mg & Hg & Hgr).
  pose proof (nstepA_mmap_nonrefusal _ _ _ _ _ _ _ _ _ _ _ Hst Hg Hgr) as Hnr.
  apply nstepA_mmap_iff in Hst as [Hst _]. unfold check_mmap, check_mmap_fixed_overflow in Hst.
  rewrite G_off, (G_anon flags ltac:(tauto)) in Hst.
  rewrite w_is0_lit in Hst by lia. replace (len =? 0) with false in Hst by (symmetry; apply Z.eqb_neq; lia).
  destruct (fixed_shape flags Hfl) as (S1 & S2 & S3 & S4). rewrite S1, S2, S3, S4 in Hst. cbv iota beta in Hst.
  rewrite mmap_len_eq in Hst by lia. pose proof (mmap_len_bounds len ltac:(lia)) as ML. rewrite (unsigned_lit addr) in Hst by lia.
  cbv zeta in Hst.
  replace (two_pow_64 <=? addr + mmap_len len) with false in Hst by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia).
  rewrite Htop, (proj2 (Z.leb_le _ _) Hce) in Hst. unfold page_size in Hst. rewrite Hal in Hst. rewrite (proj2 (Z.ltb_lt _ _) Ha) in Hst.
  cbn [negb Z.eqb] in Hst. fold n in Hst. rewrite Hrf, Hmc in Hst. cbn [andb] in Hst.
  destruct rsp as [r ws zs us cs ci]. cbn [eff_ret] in Hnr.
  destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  cbv iota in Hst. rewrite Hnr in Hst. cbv iota in Hst.
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
  destruct (fixed_check addr len flags mo Hfl Hlen Ha Hal Htop Hce Hrf Hmc Hbud) as (effg & mg & Hg & Hgr).
  exists effg, mg, []. apply nstepA_mmap_of_nonrefusal; [exact Hg| exact Hgr].
Qed.

(* LPS 727298f3: the exact arm's granted answer; munmap's next state subtracts the range
   from [vm_maps] ([mmap_fixed_destroyed_next]). *)
Lemma munmap_grant : forall addr len mo,
  0 < len <= 2^40 -> 0 <= addr -> addr mod 4096 = 0 -> addr + mmap_len len <= atop ->
  let n := Z_to_bv 64 (mmap_len len) in
  map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  check_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, n)] [] []) mo
  = CheckOk (with_mmap_destroyed (Z_to_bv 64 addr) n (mmap_fixed_destroyed_next (m_vmmaps mo) (Z_to_bv 64 addr) n) mo) [].
Proof.
  intros addr len mo Hlen Ha Hal Hce n Hmh.

pose proof (mmap_len_bounds len ltac:(lia)) as ML. pose proof TASK_SIZE_val as TS.
  unfold check_munmap.
  rewrite (unsigned_lit addr) by lia. unfold page_size. rewrite Hal.
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb orb Z.eqb].
  rewrite mmap_len_eq by lia. cbv zeta.
  replace (TASK_SIZE <? addr + mmap_len len) with false by (symmetry; apply Z.ltb_ge; lia).
  fold n. rewrite Hmh.
  replace (errno_ret_in munmap_errnos (Z_to_bv 64 0)) with false by (vm_compute; reflexivity).
  rewrite w_is0_lit by lia. cbn [Z.eqb]. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma munmap_answers : forall addr len mo rsp mo' evs,
  0 < len <= 2^40 -> 0 <= addr -> addr mod 4096 = 0 -> addr + mmap_len len <= atop ->
  let n := Z_to_bv 64 (mmap_len len) in
  map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  maps_subtract (vm_maps (m_vmmaps mo)) addr (addr + mmap_len len) = map_remove (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) ->
  nstepA (NMunmap addr len) mo rsp mo' evs ->
  evs = [] /\ adec_munmap addr len rsp = Some 0
  /\ mo' = munmap_model mo addr (mmap_len len).
Proof.
  intros addr len mo rsp mo' evs Hlen Ha Hal Hce n Hmh Hex Hst.
  cbn [nstepA] in Hst.
  (* the exact arm has a grant, so a non-spurious step is no refusal *)
  pose proof (nstep_munmap_nonrefusal _ _ _ _ _ _ _ _ _ Hst (munmap_grant addr len mo Hlen Ha Hal Hce Hmh)
                ltac:(vm_compute; reflexivity)) as Hnr.

pose proof (mmap_len_bounds len ltac:(lia)) as ML. pose proof TASK_SIZE_val as TS.
  apply nstep_munmap_iff in Hst as [Hst _]. unfold check_munmap in Hst.
  rewrite (unsigned_lit addr) in Hst by lia. unfold page_size in Hst. rewrite Hal in Hst.
  rewrite w_is0_lit in Hst by lia. replace (len =? 0) with false in Hst by (symmetry; apply Z.eqb_neq; lia). cbn [negb orb Z.eqb] in Hst.
  rewrite mmap_len_eq in Hst by lia. cbv zeta in Hst.
  replace (TASK_SIZE <? addr + mmap_len len) with false in Hst by (symmetry; apply Z.ltb_ge; lia).
  fold n in Hst. rewrite Hmh in Hst.
  destruct rsp as [r ws zs us cs ci]. cbn [eff_ret] in Hnr.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  cbv iota in Hst. rewrite Hnr in Hst. cbv iota in Hst.
  match type of Hst with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
  injection Hst as <- <-. split; [reflexivity|].
  apply andb_prop in E as [E1 E2]. unfold w_is0 in E1. apply bv_eqb_eq in E1. apply listNN_eqb_eq in E2. subst r us.
  split.
  - unfold adec_munmap, dec_munmap. rewrite (unsigned_lit 0) by lia. cbn [Z.eqb]. fold n. rewrite !bv_eqb_refl. reflexivity.
  - unfold munmap_model, mmap_fixed_destroyed_next. subst n.
    rewrite (unsigned_lit (mmap_len len)) by lia. rewrite (unsigned_lit addr) by lia. rewrite Hex. reflexivity.
Qed.

Lemma munmap_exists : forall addr len mo,
  0 < len <= 2^40 -> 0 <= addr -> addr mod 4096 = 0 -> addr + mmap_len len <= atop ->
  let n := Z_to_bv 64 (mmap_len len) in
  map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) n = true ->
  exists rsp mo' evs, nstepA (NMunmap addr len) mo rsp mo' evs.
Proof.
  intros addr len mo Hlen Ha Hal Hce n Hmh.
  eexists (mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, n)] [] []), _, [].
  cbn [nstepA]. apply nstep_munmap_iff.
  split; [exact (munmap_grant addr len mo Hlen Ha Hal Hce Hmh)|].
  apply LinuxProcessSemantics.LinuxProcessSem.Run.spurious_refusal_not_refusal; rewrite Cfg.refusal_b_215 by reflexivity; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma madvise_next_canon : forall mo a n, m_vm_materialized mo = [] -> madvise_dontneed_next mo a n = mo.
Proof.
  intros mo a n H. unfold madvise_dontneed_next. rewrite H. cbn [List.filter]. rewrite <- H.
  destruct mo as [fd [mp lz mt] io fs pr lm tm]. reflexivity.
Qed.

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
        (* LPS 727298f3: Linux places the request (it goes where Linux puts it). *)
        /\ mmap_place_found mo (Z_to_bv 64 0) (mmap_len len) = true
      else
        (flags = F_FIXED \/ flags = F_FIXNORES) /\ 0 < addr /\ addr mod 4096 = 0 /\ addr + mmap_len len <= atop
        /\ region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)) = true
        /\ map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)) = true
        /\ mmap_fixed_rw_budget_ok (Z_to_bv 64 flags) mo (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)) = true
  | AMunmap addr len =>
      0 < len <= 2^40 /\ 0 <= addr /\ addr mod 4096 = 0 /\ addr + mmap_len len <= atop
      /\ map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (mmap_len len)) = true
      (* LPS 727298f3: munmap subtracts the range from [vm_maps]; here that is one entry *)
      /\ maps_subtract (vm_maps (m_vmmaps mo)) addr (addr + mmap_len len) = map_remove (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr)
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
  - (* [comment removed for export] *)
    cbn [aok] in Hok. destruct Hok as (Hlen & Ha & Hal & Hce & Hmh & Hex).
    exists (NMunmap addr len), (adec_munmap addr len). split; [reflexivity|]. split; [|split].
    + intros rsp mo' evs Hst. destruct (munmap_answers addr len mo rsp mo' evs Hlen Ha Hal Hce Hmh Hex Hst) as (-> & Hd & ->).
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
