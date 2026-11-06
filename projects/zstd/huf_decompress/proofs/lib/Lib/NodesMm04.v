(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Cfg ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import MmapComplete.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Placement.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_NodesMm04 () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib6Decode8errno_ofC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<errno_ret_inC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude9errnos_okC4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeAerrno_ret_in_trueC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude?errnos_ok_rangeK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib3Lib6DecodeBerrno_of_errno_retC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List2InK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic5False00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib3Lib9Placement@mmap_errnos_whenC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01c59OSSVerify5KrLib3Lib9NodesMm04@errno_ret_in_nilC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State6ENOMEMI47Corelib4Init5Logic2or00c59OSSVerify5KrLib3Lib9NodesMm04Fmmap_errnos_when_falseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9PlacementDmprotect_errnos_whenC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3addC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC4ELinuxProcessSemantics?LinuxProcessSem5State>alloc_top_roomC56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib3Lib6Decode>errno_of_smallC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizeC4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqC56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegC4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC47Corelib4Init9Datatypes3orbC59OSSVerify5KrLib3Lib8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;mmap_errnosC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8Mprotect?mprotect_errnosc59OSSVerify5KrLib3Lib9NodesMm04Gerrno_of_None_not_errnoC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3appK47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics?LinuxProcessSem5State:iv_overlapC47Corelib4Init9Datatypes4negbC4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeC47Corelib4Init9Datatypes9andb_propC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes8list_indK59OSSVerify5KrLib3Lib5Nodes4node0:C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nstepC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums1Z03C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap:check_mmapK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result01C4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap@mmap_noreserve_bC59OSSVerify5KrLib3Lib5Nodes>nstep_mmap_iffC1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem6Checks?ExecutableSpecs=check_syscallK4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01C4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specC5ELinuxProcessSemantics?LinuxProcessSem6Checks?ExecutableSpecsDcheck_syscall_ok_iffC47Corelib4Init5Logic5proj1C4ELinuxProcessSemantics?LinuxProcessSem5State6in_argC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys?DispatchComputeBcheck_syscall_mmapC4ELinuxProcessSemantics?LinuxProcessSem3RunCinjected_family_offC59OSSVerify5KrLib3Lib3CfgPnonspurious_not_refusal_of_grantC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9refusal_bC59OSSVerify5KrLib3Lib3CfgCacfg_family_off_222C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run=ret_in_errnosC59OSSVerify5KrLib3Lib3Cfg=refusal_b_222C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes:pure_inputC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunDspurious_refusal_cfgC47Corelib4Init5Logic3notI6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result00C59OSSVerify5KrLib3Lib3Cfg4ACFGC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00K59OSSVerify5KrLib3Lib5Nodes4node0<C1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm8Mprotect>check_mprotectC59OSSVerify5KrLib3Lib5NodesBnstep_mprotect_iffC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys?DispatchComputeFcheck_syscall_mprotectC59OSSVerify5KrLib3Lib3CfgCacfg_family_off_226C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Cfg=refusal_b_226C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC4ELinuxProcessSemantics?LinuxProcessSem5State<alloc_top_ltC59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib<MmapCompleteIvm_gap_available_completeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backing_usedC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC59OSSVerify5KrLib3Lib9Placement@vm_gap_availableC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init5Logic5proj2C59OSSVerify5KrLib3Lib9PlacementDmmap_grant_refusableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9PlacementFmmap_reserve_refusableC1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5w_is0C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqC59OSSVerify5KrLib3Lib6Decode8mmap_lenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib3Lib5Nodes9w_is0_litC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K46Stdlib9micromega=RingMicromega3Op201C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;mmap_anon_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>mmap_modeled_bC46Stdlib4Bool4Bool=orb_false_iffC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapHmmap_noreserve_backed_okC46Stdlib4Bool4Bool>negb_false_iffC59OSSVerify5KrLib3Lib9PlacementEvm_gap_available_findC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9Placement<vm_find_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9PlacementBvm_find_base_soundC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib3Lib6Decode>mmap_len_boundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9NodesMm04Berrno_of_below_topC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9NodesMm04Gerrno_ret_in_mmap_smallC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01C4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapAwith_mmap_backingC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapAmmap_plain_anon_bC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude>check_ret_onlyC56Stdlib6ZArith6BinInt1Z3ltbC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude:listNN_eqbC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_noaccess_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEmmap_fixed_noaccess_bC4ELinuxProcessSemantics?LinuxProcessSem5State<map_containsC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_fixed_rw_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_budget_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_fixed_rw_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEwith_mmap_replacementC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapLmmap_fixed_rw_span_budget_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_span_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapImmap_noreplace_noaccess_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapCmmap_noreplace_rw_bC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude=listNN_eqb_eqC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z6eqb_eqK47Corelib4Init5Logic2ex01c59OSSVerify5KrLib3Lib9NodesMm04>anon_len_factsC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I47Corelib4Init9Datatypes3nat00K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result03C4ELinuxProcessSemantics?LinuxProcessSem5State6EINVALK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result02C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapImmap_fixed_destroyed_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapCwith_mmap_destroyedC4ELinuxProcessSemantics?LinuxProcessSem5State=maps_subtractC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapMmmap_fixed_noaccess_span_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_off_aligned_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_flags_coreC56Stdlib6ZArith6BinInt1Z4landC46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z5ldiffC56Stdlib6ZArith6BinInt1Z:ldiff_specC56Stdlib6ZArith6BinInt1Z9land_specC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_pglen_ok_bc59OSSVerify5KrLib3Lib9NodesMm04Eerrno_ret_in_mmap_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9NodesMm04=anon_rw_grantC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9NodesMm04Instep_mmap_grant_no_errnoC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi9PROT_READC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi:PROT_WRITEC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi;MAP_PRIVATEC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi=MAP_ANONYMOUSC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap=MAP_NORESERVEC4ELinuxProcessSemantics?LinuxProcessSem5State6EEXISTc59OSSVerify5KrLib3Lib9NodesMm04Herrno_ret_in_mmap_ENOMEMC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9NodesMm04?anon_none_grantC1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi9PROT_NONEC56Stdlib6ZArith6BinInt1Z6leb_gtc59OSSVerify5KrLib3Lib9NodesMm04?fixed_len_factsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9NodesMm04>page_size_4096C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapFmmap_noreplace_flags_bC46Stdlib4Bool4Bool8orb_propK47Corelib4Init5Logic2or02C46Stdlib4Bool4Bool<andb_false_rC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi9MAP_FIXEDC5ELinuxProcessSemantics?LinuxProcessSem3Sys4UapiCMAP_FIXED_NOREPLACEc59OSSVerify5KrLib3Lib9NodesMm04?fixed_shape_preC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9NodesMm04@fixed_gate_alignC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9NodesMm04?fixed_gate_wrapC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9NodesMm04Aregion_free_app_lC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9NodesMm04@fixed_none_grantC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z<pos_div_euclC56Stdlib6ZArith6BinInt1Z3oppC57Corelib7BinNums6PosDef3Pos4landC56Stdlib6ZArith6BinInt1Z4of_NC57Corelib7BinNums6PosDef3Pos6pred_NC57Corelib7BinNums6NatDef1N5ldiffC57Corelib7BinNums6NatDef1N3lorC57Corelib7BinNums6NatDef1N8succ_posC57Corelib7BinNums6PosDef3Pos3eqbC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_forget_rangeC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_add_lazyC46Stdlib4Bool4Bool;orb_false_rI47Corelib7Numbers7BinNums8positive00C46Stdlib4Bool4Bool:orb_true_rc59OSSVerify5KrLib3Lib9NodesMm04Cnoreplace_not_fixedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9PlacementJmmap_fixed_fresh_refusableC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9NodesMm04Herrno_ret_in_mmap_EEXISTC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9NodesMm04?noreplace_grantC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9PlacementBmprotect_refusableC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectBmprotect_budget_okC59OSSVerify5KrLib3Lib6Decode<errno_of_litC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9NodesMm04Kerrno_ret_in_mprotect_smallC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectCmprotect_model_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectBmprotect_modeled_bC47Corelib4Init5Logic6eq_symc59OSSVerify5KrLib3Lib9NodesMm04Ierrno_ret_in_mprotect_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9NodesMm04>mprotect_grantC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9NodesMm04Mnstep_mprotect_grant_no_errnoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9NodesMm04Lerrno_ret_in_mprotect_ENOMEMC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateDm_vmmaps_with_vmmaps".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma errno_of_None_not_errno : forall r es, errno_of r = None -> errno_ret_in es r = true ->
  errnos_ok es = true -> False.
Proof.
ltac2:(KReplay.run1 (kr_t_NodesMm04 ()) [] "p'0h01eh11Hh22Hnh31rh42esh53Hinh64__x1h72H1h82H2h93HInh:3Hokh;7__arithh<4__ffh=8__varmaph>5__with?2e0h@1oi001oi011xp;1p;3p;2p;4p;7p;6p;8p10000p4p70R0g000`R1p4p710R2p8P0p1001<p4p710R3p8P0p1001Zp4p7210R0p8p10027p4p70R4P2p8P4P3p8P4P0p8p1002ep4p70R4P2p8P4P3p8P4P0p8g003[j14Tg004@j1[Tg004^j1PTg005Aj1@Tg005aR0j1ZTg006Cj18Tg007;j1ATg007]j30Tg0087j2:Tg009?j1HTg00:Dj15Tg00;<R4j23Tg00;WR3j29Tg00<1j2UTg00=>j4STg00>Ij1CTg00>gj21Tg00?Cj1;Tg00?hj2BTg00@Jj1OTg00@jj2NTg00AHj1LTg00Afj1KTg00BQj2JTg00C4j2=Tg00CWj4<Tg00DBj7ITg00Dfj2GTg00EHj2MTg00Ebj2FTg00FNj3QTg00Fmj4RTg00G_j2ETP1j6DTg00Haj2TTg00I@j7YTg00I^j3XTg00J5j7WTg00JYj8VTg00K=R1f0R2g00K]R530p=7g00L=R6f1R7;X2p=2%;2#;p=6P7g00L[R8g00M:R9P9g00MZR:P2g00N:FWp=>f3R;P8P9P9P:f2R<P7P2GVp=?g00NZR=#4#4#4#4#4#4#[#PR>%@6R?%Z6R@%87%A6RA301:7<#7%H<#7P41:72#7122;%52RB90><'3X06,96[RC122<A0>7B'3X06,961:<7#7RD[f4RE,22A0>;B'3X06,96\D1U72P7n2001000000120000000X3>X4?PC^3>^4?P2PEf5R?P<O3122?f6RC=0>B'3X06,96P3P6122Cf7R3=0>B'3X06g00O?RDP2f8,22f9RF=0>B'3P4127Ff:RB%5750>PDP2f;RG,2;f=%5E50>P>%5?RE%82=0@APD]2X3>%8E=0@Af>REPCPGP<CS%C=R>/1C%;=#6#6#6#6#6#CR;,1C'3P411>3113;PDP211>F11B;P@%5G#8A0@2AX@@P?1B6GR?g00O\RB#O%@B1N67%L6%K6RBP61J6=R=g00PHRF1=6;C<,>BR3%A9R4PBP61=6>PFP=C<,>BR=P4PBP8P9P9P:P=P3FIC?C?1GB:P2P<1M151F2<#7dg00Po=Q67CRb<b=b>X66112;11>711><11<;'3[[^66P2f<R;P7P<O3b;,EGEDA0@?AP@1B6;P0P6p-0P2g00QMPDn10110000021000000X?@g00QiPAP2EDPD1TD2b1b2W8W7P7P2O2n2001000000121000000b1W2PEP2P;FYW1W9P7P2O2n2001000000121000000W1X06P7P2O2n2001000000121101000b5b1W:W5W2W4W3o"). Qed.

Lemma errno_ret_in_nil : forall r, errno_ret_in [] r = false.
Proof.
ltac2:(KReplay.run1 (kr_t_NodesMm04 ()) [] "h01rp;1p;2g003[j10Tg004@j13Tg004^j12Tg00EHj21Tg00NZ#0#0#0#0#0#0#3#2g00K=g00RE'1W0o"). Qed.

Lemma mmap_errnos_when_false : mmap_errnos_when false = [].
Proof.
ltac2:(KReplay.run1 (kr_t_NodesMm04 ()) [] "p;1p;2g005Aj12Tg00@Jj11Tg00EHj20Tg00L=R0#2%10'0o"). Qed.

Lemma mmap_destructive_errnos_nil : mmap_destructive_errnos = [].
Proof.
ltac2:(KReplay.run1 (kr_t_NodesMm04 ()) [] "p;1p;2g005Aj12Tg00@Jj11Tg00EHj20Tg00L=R0#2%10'0o"). Qed.

(* [comment removed for export] *)
Lemma errno_ret_in_when : forall b r, errno_ret_in (mmap_errnos_when b) r = true -> b = true /\ r = errno_ret ENOMEM.
Proof.
  intros [|] r H; [|rewrite mmap_errnos_when_false, errno_ret_in_nil in H; discriminate].
  split; [reflexivity|]. apply errno_ret_in_true in H as (e & HIn & ->). destruct HIn as [<-|[]]. reflexivity.
Qed.

Lemma errno_ret_in_mprotect_when : forall b r,
  errno_ret_in (mprotect_errnos_when b) r = true -> b = true /\ r = errno_ret ENOMEM.
Proof.
  intros [|] r H; [|cbn in H; discriminate].
  split; [reflexivity|]. apply errno_ret_in_true in H as (e & HIn & ->). destruct HIn as [<-|[]]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma errno_of_below_top : forall r h nZ, 0 <= nZ -> bv_unsigned r + nZ <= alloc_top h -> errno_of r = None.
Proof.
ltac2:(KReplay.run1 (kr_t_NodesMm04 ()) [] "h04__x1h14__x2h24__x3h32Hbh42Hnh51Rh67__arithh74__ffh88__varmaph95__with:1hh;2nZh<1rp;1p;2p;3p;4p;7p;8g003[j10Tg004@j1\Tg004^j1KTg00>gj23Tg00Xej2CTg00YOj24Tg00Ylj19Tg00Zdj1JTg00[aj2=Tg00\=j1;Tg00\\j26Tg00]Ej3<Tg00]nj2DTg00@Jj1[Tg00^Zj3UTg005Aj1TTg00@jj2ATg00_:j4OTg00AHj1NTg00Afj1MTg00?Cj1LTg00BQj27Tg00>Ij11Tg00C4j22Tg00_Xj3@Tg00`;j3>Tg00`^j3ITg00CWj4?Tg007;j1HTg00aAj3GTg00Dfj2FTg00EHj2ETg00Ebj2PTg007]j3QTg00FNj3RTg00Fmj4STg00adj2BTg00bAj2ZTg00b^j2YTg00c;j2XTg00J5j7VTg00JYj8WTf1R0g00L[R1g00M:R2P2g00MZR3f0R4g00N:FVp=5g00L=R5P0g00PHP4C?p=8f3R6P1P2P2P3f2R1P0P4GWp=:g00NZR7#0R8#0#0R9#0#0#0R:#\R;#Kg00d9g00PoR</341C;6/40%91'3%J6%96g00e0'4g00em'=f5R=g00O\R>g00ffR?#;R@#;RA#;,65165A165@165?5<55<55<5g00gE'D%[>3U%T>P51A51P01A56CO%N5%M5R>P5%L7,75R?%19R9,25%0:#0#0#0R@#1RA,25RB5@5=@5B5>5g00h1%18RB,25=I5;RCC?,5>%H2R2P>1757R71758R85>5/8?,5>P2P>125</88,5>P2%0@#0#1R@,259G5C,87,5>C:C:C:1F>3P4P1g00K=R>g00K]R3'E1P41=Q>3dAR5<0CSb7b8b9X05X15X251B9A/BA,41%1:,ZBRB'=1401/3613<61YB@,36[[[^05^15^25P4%9=f4f6,C;P0P1P6O6b6'Xb5W3W4X;5W:W<o"). Qed.

(* [comment removed for export] *)
Lemma bv_eqb_errno_small : forall e (aw : word), errno_of aw = None -> 1 <= e <= 4095 ->
  bv_eqb (errno_ret e) aw = false.
Proof.
ltac2:(KReplay.run1 (kr_t_NodesMm04 ()) [] "p'0h01Eh12Hnh21bi001bh31Hh44__x1h51ah62awh72Heh87__arithh94__ffh:8__varmaph;5__with<1eh=2e0h>1oi011op;1p;3p;2p;6p;4p;7p;8g003[j14Tg004@j1UTg004^j1JTg005aR0j1ETg006Cj1:Tg007;j1ATg007]j30Tg00>Ij1>Tg00>gj22Tg00?Cj18Tg00;<R1j27Tg00:Dj11Tg00hXj33Tg00EHj29Tg00iEj3TTg00I@j6STg00?hj2@Tg00@Jj1RTg005Aj1QTg00@jj2OTg00AHj1ITg00Afj1HTg00C4j2<Tg00BQj2GTg00CWj4=Tg00DBj7FTg00JYj8KTg00Dfj2LTg00Ebj2DTg00FNj3MTg00Fmj4NTg00G_j2CTg000`j6?Tg00Haj2PTg00J5j7BTf0R2#8#8p=5g00K=R3g00K]R4702p=6f1R5g00L[R6g00M:R7P7g00MZR8P2g00N:FBp=;g00L=R9g00NZR:#4#4#4#4#4#4#UR;#JR<%E9R=%:2%A9R>30R?%>:R@f2RA'2%8:#5#5#5#5#5#>RB,2A'7f3RC#1=3;AP31932f4RD#1=3;C=032P3f6RE#1f5RF53;=032g00RERG9035]0P5%1F=3;DRD#6P1A3;52#6A0<A5[R1A0<52A3;A5#6RF[A0<CA\FAT;52P5n2001000000120000000X2<X5<P1^2<^5<P2f7R1#1R;PEP5O3A0<;EP<P1P?X6<PEf8#1REP2ES%:E=0=>P=f9RE#1#:A0=2>X>=P21@9ER<g00O\R?#R%Q?1O95%I9%H9R?P6P7P7P8P?P6P7P7P8P91<9@g00PHR61G9:R:C=,;?P9P:P61<9BC=,;?FFR6%A7P6GK1L?8P2PA19341D2A#6dg00Po=M95CNb9b:b;X4912@2122B'712@5125B'7[^49P2f:RBP1O2b8,CEE?A0=<>P=1@9BP0P9p-0P2g00QMg00O?R9n10110100021000000X==g00QiP>P2E?P9A034G/P2b3b1b1b0b3W0A03DG193GW0n0110000020100P2O1b0b2W7W1W6W<o"). Qed.

Lemma page_round_up_Z_nonneg' : forall z, 0 <= z -> 0 <= page_round_up_Z z.
Proof.
ltac2:(KReplay.run1 (kr_t_NodesMm04 ()) [] "h07__arithh14__ffh28__varmaph35__with44__x1h52Hzh61zp;2p;1p;3p;8p;4p;7g00>gj21Tg00>Ij16Tg00YOj29Tg00b^j2PTg00j:j2NTg00@Jj1?Tg005Aj1>Tg00@jj2<Tg00AHj1;Tg00Afj18Tg00C4j23Tg00BQj2:Tg007;j1OTg00`;j3MTg00aAj3KTg00JYj8FTg00Dfj2@Tg00EHj2ATg00Ebj2BTg007]j3=Tg00FNj3CTg00Fmj4DTg00jWj1ETg00CWj45Tg00[aj2GTg00k5j4HTg00kVj4ITg00lAj1JTg003[j17Tg00J5j7LTf0R0#7#7p=0g00L=R1f1R2g00PHP0C5p=4P2g00L[R3g00M:R4P4g00MZR5P0g00N:FLp=2g00PoR6/10R7g00NZR8#0#0#0#0#0#0#6R9,92%68R:'PR;/N9P9P;P9g00O\R<#?R=%><R<1<12%;1R>%81R?P3P4P4P51316R31:18R8'4,2?%O41319R49M18131:5K1,43,2?GF1@?5R5P0f2R:g00K=R8g00K]R@'A1B0:==8@dAC162CDR@b1b2b3X41116;\7^41P0P:P2O2b0P=P<%E1R:P>P1P3g00h1P4C5,2?P5P@b1b2b31G69P0b0CHP=P<P:P>1434,2?P5P@b1b2b31169P0b0CI%J2,16eW5X61o"). Qed.

Lemma page_size_4096 : page_size = 4096.
Proof.
ltac2:(KReplay.run1 (kr_t_NodesMm04 ()) [] "p;1p;2g00>Ij13Tg00EHj22Tg003[j11Tf0#1#1p=0g00L=g00NZ#0#0#0#0#0#0#3'2o"). Qed.

Lemma errno_ret_in_mmap_ENOMEM : errno_ret_in mmap_errnos (errno_ret ENOMEM) = true.
Proof. unfold errno_ret_in, mmap_errnos. cbn [existsb]. rewrite bv_eqb_refl. reflexivity. Qed.

Lemma errno_ret_in_mprotect_ENOMEM : errno_ret_in mprotect_errnos (errno_ret ENOMEM) = true.
Proof. unfold errno_ret_in, mprotect_errnos. cbn [existsb]. rewrite bv_eqb_refl. reflexivity. Qed.

Lemma errno_ret_in_mmap_inv : forall r, errno_ret_in mmap_errnos r = true -> r = errno_ret ENOMEM.
Proof. intros r H. apply errno_ret_in_true in H as (e & HIn & ->). destruct HIn as [<-|[]]. reflexivity. Qed.

Lemma errno_ret_in_mprotect_inv : forall r, errno_ret_in mprotect_errnos r = true -> r = errno_ret ENOMEM.
Proof. intros r H. apply errno_ret_in_true in H as (e & HIn & ->). destruct HIn as [<-|[]]. reflexivity. Qed.

Lemma errno_ret_in_mmap_small : forall r, errno_of r = None -> errno_ret_in mmap_errnos r = false.
Proof.
  intros r Hn. destruct (errno_ret_in mmap_errnos r) eqn:E; [|reflexivity].
  exfalso. exact (errno_of_None_not_errno r mmap_errnos Hn E eq_refl).
Qed.

Lemma errno_ret_in_mprotect_small : forall r, errno_of r = None -> errno_ret_in mprotect_errnos r = false.
Proof.
  intros r Hn. destruct (errno_ret_in mprotect_errnos r) eqn:E; [|reflexivity].
  exfalso. exact (errno_of_None_not_errno r mprotect_errnos Hn E eq_refl).
Qed.

Lemma region_free_app_l : forall l1 l2 lo n, region_free (l1 ++ l2) lo n = true -> region_free l1 lo n = true.
Proof.
  induction l1 as [|[b s] r IH]; intros l2 lo n H; [reflexivity|].
  cbn [app region_free] in *. apply andb_prop in H as [H1 H2]. rewrite H1, (IH l2 lo n H2). reflexivity.
Qed.

Lemma nstep_mmap_grant_no_errno : forall addr len prot flags mo eff mo' evs eg mg evg,
  nstep (NMmap addr len prot flags) mo eff mo' evs ->
  check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
             (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eg mo = CheckOk mg evg ->
  errno_ret_in mmap_errnos (eff_ret eg) = false ->
  errno_ret_in mmap_errnos (eff_ret eff) = false.
Proof.
  intros addr len prot flags mo eff mo' evs eg mg evg H Hg Hng.
  apply nstep_mmap_iff in H as (_ & _ & Hns).
  pose proof (proj1 (check_syscall_ok_iff (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot;
                                                         Z_to_bv 64 flags; Z_to_bv 64 (-1); Z_to_bv 64 0]) eg mo mg evg)) as Hs.
  rewrite check_syscall_mmap in Hs by reflexivity. specialize (Hs Hg).
  pose proof (fun Hoff => nonspurious_not_refusal_of_grant ACFG _ mo eff eg mg evg Hoff Hns Hs) as X.
  specialize (X ltac:(apply acfg_family_off_222; reflexivity)).
  rewrite !refusal_b_222 in X by reflexivity. exact (X Hng).
Qed.

Lemma nstep_mprotect_grant_no_errno : forall addr len prot mo eff mo' evs eg mg evg,
  nstep (NMprotect addr len prot) mo eff mo' evs ->
  check_mprotect (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) eg mo = CheckOk mg evg ->
  errno_ret_in mprotect_errnos (eff_ret eg) = false ->
  errno_ret_in mprotect_errnos (eff_ret eff) = false.
Proof.
  intros addr len prot mo eff mo' evs eg mg evg H Hg Hng.
  apply nstep_mprotect_iff in H as (_ & Hns).
  pose proof (proj1 (check_syscall_ok_iff (pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot]) eg mo mg evg)) as Hs.
  rewrite check_syscall_mprotect in Hs by reflexivity. specialize (Hs Hg).
  pose proof (fun Hoff => nonspurious_not_refusal_of_grant ACFG _ mo eff eg mg evg Hoff Hns Hs) as X.
  specialize (X ltac:(apply acfg_family_off_226; reflexivity)).
  rewrite !refusal_b_226 in X by reflexivity. exact (X Hng).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma gap_available_of_free_base : forall h nZ g,
  0 <= nZ -> g mod 4096 = 0 -> 0 < g -> g + nZ <= alloc_top h ->
  region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true ->
  vm_gap_available h nZ = true.
Proof.
  intros h nZ g Hn Hal Hpos Htop Hfree. pose proof (alloc_top_lt h) as T. unfold two_pow_64 in T.
  assert (Hg : bv_unsigned (Z_to_bv 64 g) = g) by (apply unsigned_lit; lia).
  apply (MmapComplete.vm_gap_available_complete h nZ (Z_to_bv 64 g)); rewrite ?Hg; assumption.
Qed.

Lemma grant_refusable_false_intro : forall flags m nZ,
  mmap_noreserve_b flags = false ->
  vm_backing_used m + nZ <= vm_limit (m_vmmaps m) ->
  vm_gap_available (m_vmmaps m) nZ = true ->
  mmap_grant_refusable flags m nZ = false.
Proof.
  intros flags m nZ Hnr Hb Hg. unfold mmap_grant_refusable, mmap_noreserve_backed_ok.
  rewrite Hnr, Hg. rewrite (proj2 (Z.leb_le _ _) Hb). reflexivity.
Qed.

Lemma reserve_refusable_false_intro : forall m nZ,
  vm_gap_available (m_vmmaps m) nZ = true -> mmap_reserve_refusable m nZ = false.
Proof. intros m nZ Hg. unfold mmap_reserve_refusable. rewrite Hg. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AnonMmap.
Variables (addr len prot flags : Z).
Hypothesis Hlen : 0 < len < 2^64.

Let lenw := Z_to_bv 64 len.
Let nZ := mmap_len len.

Lemma anon_len_facts : w_is0 lenw = false /\ page_round_up_Z (bv_unsigned lenw) = nZ.
Proof.
ltac2:(KReplay.run1 (kr_t_NodesMm04 ()) ["AnonMmap"] "h06__sat1h14__x1h22Hah37__arithh44__ffh54__p1h66__sat0h78__varmaph85__with96heq_nZh:1xh;1yh<1Hh=1bh>1zp;1p;2p;3p;4p;6p;7p;8g01gfj1BTg003[j11Tg004@j1FTg00Xej2ATg00lAj1@Tg007]j30Tg01h`j25Tg01N8j1;Tg01i=j2GTg01i^j1ETg00EHj28Tg00>Ij1?Tg01jVj2^Tg00[aj22Tg00>gj27Tg00bAj2WTg01k>j3VTg01kbj2UTg00@Jj1STg005Aj1RTg00@jj2QTg00AHj1KTg00Afj1JTg00C4j2<Tg00BQj2HTg00CWj44Tg01lCj6ITg007;j1LTg01lgj6MTg00Dfj2NTg00Ebj2DTg00FNj3OTg00Fmj4PTg00;<R0j29Tg019Aj2CTg00`^j3TTg01mKj2]Tg00I@j6>Tg01]Lj2\Tg00Shj4[Tg00J5j7ZTg00DBj7YTg00JYj8XTg00K=R1f0R2g00RE30p=3f1R3g00L[R4g00M:R5P5g00MZR6P2g00N:FZp=6f2R7P4P5P5P6P3P2FYp=:f3R8P4P5P5P6P7P3P2GXp==p,4lenwR9#B#3g00L=R:g00NZR;#1R<#1#1#1#1#1R=#FR>/A9#@p,2nZR930P1p,3lenR?g00PoR@'5%32X=1P01532#3A0:73#;R0[A0:32#;1573#3[RA1587#3\01G32P2n2001000000120000000X;:X::PA^;:^::P2P?P@%E?RA,8:R0A0:9AR9eRBP9%?<R<%?=R='^RC12@<RD17@=1W<=RE,2@[RF[RG17@<RHg00QMRIAV<=3UW2R=17@E\I^2HRHP3g01nC1U@<'8PDeO1RDPFp-0RIg00O\RJ#SRK%RJRJ1Q:3RL%K:RM%J:RNP:1<:@ROg00h1RP1H:;R;C4,6NRQPNP4P5P5P6P8EI5:N%L5R8PNP4P5P5P6P:P;g01niPOC4,6NEMC=1NN6R6P2P7g00K]R5,811D27=015dAO:@3CPR5b4b7b8X1:W512@2R1/93A0:3@g00O?[[^1:^5IP212?EP?p,4HlenRIO3b3b0b6b0b9O3b<1C>?R7#BPBP9PCPGP=PHPDPFPKPJPLPMPNP:P;PP1<:<=T:>C4,6NR<9:NQP8P:POg00PHP;C4,6N=:N<C=P6P5b4b7b8X1:122E,9117@3123E'9[^1:P2P?PIO2b3b0b6b0RIb9,]?E>P:P?%@2=0:AX>:P01A>71\?IE>C[o"). Qed.

Lemma anon_rw_grant : forall mo,
  negb (mmap_anon_b (Z_to_bv 64 flags)) = false ->
  mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  mmap_grant_refusable (Z_to_bv 64 flags) mo nZ = false ->
  exists eg mg, check_mmap (Z_to_bv 64 addr) lenw (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eg mo
                = CheckOk mg [] /\ errno_ret_in mmap_errnos (eff_ret eg) = false.
Proof.
  intros mo G2 Hshape R. destruct anon_len_facts as [L0 L1].
  unfold mmap_grant_refusable in R. apply orb_false_iff in R as [R1 R2]. apply negb_false_iff in R1, R2.
  destruct (vm_gap_available_find _ _ R2) as [b Hfind].
  destruct (vm_find_base_sound _ _ _ Hfind) as (B1 & B2 & B3 & B4).
  pose proof (mmap_len_bound len ltac:(lia)) as LB. fold nZ in LB.
  assert (NB : errno_ret_in mmap_errnos b = false)
    by (apply errno_ret_in_mmap_small; apply (errno_of_below_top b (m_vmmaps mo) nZ); [lia | exact B3]).
  exists (mkEffectU b [] [(b, Z_to_bv 64 nZ)] [] [] []). eexists. split; [|exact NB].
  unfold check_mmap. change (negb (mmap_off_aligned_b (Z_to_bv 64 0))) with false.
  rewrite G2, L0, Hshape. cbv iota beta. rewrite NB. cbv zeta. rewrite L1.
  rewrite (proj2 (Z.eqb_eq _ _) B1), (proj2 (Z.ltb_lt _ _) B2), (proj2 (Z.leb_le _ _) B3), B4, R1.
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma anon_none_grant : forall mo,
  negb (mmap_anon_b (Z_to_bv 64 flags)) = false ->
  mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false ->
  mmap_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  mmap_reserve_refusable mo nZ = false ->
  exists eg mg, check_mmap (Z_to_bv 64 addr) lenw (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eg mo
                = CheckOk mg [] /\ errno_ret_in mmap_errnos (eff_ret eg) = false.
Proof.
  intros mo G2 G3 Hshape R. destruct anon_len_facts as [L0 L1].
  unfold mmap_reserve_refusable in R. apply negb_false_iff in R.
  destruct (vm_gap_available_find _ _ R) as [b Hfind].
  destruct (vm_find_base_sound _ _ _ Hfind) as (B1 & B2 & B3 & B4).
  pose proof (mmap_len_bound len ltac:(lia)) as LB. fold nZ in LB.
  assert (NB : errno_ret_in mmap_errnos b = false)
    by (apply errno_ret_in_mmap_small; apply (errno_of_below_top b (m_vmmaps mo) nZ); [lia | exact B3]).
  exists (mkEffectU b [] [] [(b, Z_to_bv 64 nZ)] [] []). eexists. split; [|exact NB].
  unfold check_mmap. change (negb (mmap_off_aligned_b (Z_to_bv 64 0))) with false.
  rewrite G2, L0, G3, Hshape. cbv iota beta. rewrite NB. cbv zeta. rewrite L1.
  rewrite (proj2 (Z.eqb_eq _ _) B1), (proj2 (Z.ltb_lt _ _) B2), (proj2 (Z.leb_le _ _) B3), B4.
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma nstep_mmap_rw_err_refusable : forall mo rsp mo' evs e,
  mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  nstep (NMmap addr len prot flags) mo rsp mo' evs ->
  errno_of (eff_ret rsp) = Some e ->
  e = ENOMEM /\ mmap_grant_refusable (Z_to_bv 64 flags) mo nZ = true /\ mo' = mo /\ evs = [].
Proof.
  intros mo rsp mo' evs e Hshape H He. pose proof H as Hst. destruct anon_len_facts as [L0 L1].
  apply nstep_mmap_iff in H as (_ & H & _). unfold check_mmap in H. fold lenw in H.
  assert (G1 : negb (mmap_off_aligned_b (Z_to_bv 64 0)) = false) by reflexivity.
  assert (G2 : negb (mmap_anon_b (Z_to_bv 64 flags)) = false).
  { unfold mmap_modeled_b in Hshape. apply andb_prop in Hshape as [Hs _]. apply andb_prop in Hs as [_ Hs].
    unfold mmap_anon_b. apply Z.eqb_eq in Hs. unfold mmap_flags_core in Hs.
    apply negb_false_iff. apply negb_true_iff. apply Z.eqb_neq. intros Z0.
    assert (T : Z.testbit (Z.ldiff (bv_unsigned (Z_to_bv 64 flags)) MAP_NORESERVE) 5 = true) by (rewrite Hs; reflexivity).
    rewrite Z.ldiff_spec in T. apply andb_prop in T as [T _].
    assert (T' : Z.testbit (Z.land (bv_unsigned (Z_to_bv 64 flags)) MAP_ANONYMOUS) 5 = true) by (rewrite Z.land_spec, T; reflexivity).
    rewrite Z0 in T'. discriminate. }
  rewrite G1, G2, L0, Hshape in H. cbv iota beta in H.
  destruct rsp as [r ws zs us cs ci]. cbn [eff_ret] in He.
  destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
  destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
  rewrite L1 in H. fold nZ in H.
  case_errno_in_eqn H Herr.
  - apply errno_ret_in_mmap_inv in Herr. subst r. destruct zs; [|discriminate]. injection H as <- <-.
    rewrite errno_of_errno_ret in He by (unfold ENOMEM; lia). injection He as <-. split; [reflexivity|]. split; [|auto].
    destruct (mmap_grant_refusable (Z_to_bv 64 flags) mo nZ) eqn:R; [reflexivity|]. exfalso.
    destruct (anon_rw_grant mo G2 Hshape R) as (eg & mg & Hg & Hng).
    pose proof (nstep_mmap_grant_no_errno _ _ _ _ _ _ _ _ _ _ _ Hst Hg Hng) as X. cbn [eff_ret] in X.
    rewrite errno_ret_in_mmap_ENOMEM in X. discriminate X.
  - exfalso. cbv zeta in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
    apply andb_prop in E as [E _]. apply andb_prop in E as [E _]. apply andb_prop in E as [E _]. apply andb_prop in E as [_ E].
    apply Z.leb_le in E. pose proof (mmap_len_bound len ltac:(lia)). fold nZ in H.
    rewrite (errno_of_below_top r (m_vmmaps mo) nZ ltac:(lia) E) in He. discriminate.
Qed.

(* [comment removed for export] *)
Lemma nstep_mmap_none_err_refusable : forall mo rsp mo' evs e,
  mmap_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  nstep (NMmap addr len prot flags) mo rsp mo' evs ->
  errno_of (eff_ret rsp) = Some e ->
  e = ENOMEM /\ mmap_reserve_refusable mo nZ = true /\ mo' = mo /\ evs = [].
Proof.
  intros mo rsp mo' evs e Hshape H He. pose proof H as Hst. destruct anon_len_facts as [L0 L1].
  apply nstep_mmap_iff in H as (_ & H & _). unfold check_mmap in H. fold lenw in H.
  assert (G1 : negb (mmap_off_aligned_b (Z_to_bv 64 0)) = false) by reflexivity.
  assert (Hs0 := Hshape). unfold mmap_noaccess_b in Hs0. apply andb_prop in Hs0 as [Hs0 _]. apply andb_prop in Hs0 as [Hp Hf].
  assert (G2 : negb (mmap_anon_b (Z_to_bv 64 flags)) = false).
  { unfold mmap_anon_b. apply Z.eqb_eq in Hf. unfold mmap_flags_core in Hf.
    apply negb_false_iff. apply negb_true_iff. apply Z.eqb_neq. intros Z0.
    assert (T : Z.testbit (Z.ldiff (bv_unsigned (Z_to_bv 64 flags)) MAP_NORESERVE) 5 = true) by (rewrite Hf; reflexivity).
    rewrite Z.ldiff_spec in T. apply andb_prop in T as [T _].
    assert (T' : Z.testbit (Z.land (bv_unsigned (Z_to_bv 64 flags)) MAP_ANONYMOUS) 5 = true) by (rewrite Z.land_spec, T; reflexivity).
    rewrite Z0 in T'. discriminate. }
  assert (G3 : mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false).
  { unfold mmap_modeled_b. apply Z.eqb_eq in Hp. rewrite Hp. reflexivity. }
  rewrite G1, G2, L0, G3, Hshape in H. cbv iota beta in H.
  destruct rsp as [r ws zs us cs ci]. cbn [eff_ret] in He.
  destruct ws; [|discriminate]. destruct zs; [|discriminate].
  destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
  rewrite L1 in H. fold nZ in H.
  case_errno_in_eqn H Herr.
  - apply errno_ret_in_mmap_inv in Herr. subst r. destruct us; [|discriminate]. injection H as <- <-.
    rewrite errno_of_errno_ret in He by (unfold ENOMEM; lia). injection He as <-. split; [reflexivity|]. split; [|auto].
    destruct (mmap_reserve_refusable mo nZ) eqn:R; [reflexivity|]. exfalso.
    destruct (anon_none_grant mo G2 G3 Hshape R) as (eg & mg & Hg & Hng).
    pose proof (nstep_mmap_grant_no_errno _ _ _ _ _ _ _ _ _ _ _ Hst Hg Hng) as X. cbn [eff_ret] in X.
    rewrite errno_ret_in_mmap_ENOMEM in X. discriminate X.
  - exfalso. cbv zeta in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
    apply andb_prop in E as [E _]. apply andb_prop in E as [E _]. apply andb_prop in E as [_ E].
    apply Z.leb_le in E. pose proof (mmap_len_bound len ltac:(lia)). fold nZ in H.
    rewrite (errno_of_below_top r (m_vmmaps mo) nZ ltac:(lia) E) in He. discriminate.
Qed.
End AnonMmap.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FixedMmap.
Variables (a len prot flags : Z).
Hypothesis Hlen : 0 < len < 2^64.
Hypothesis Ha : 0 <= a.
Hypothesis Hal : a mod 4096 = 0.
Hypothesis Hwrap : a + mmap_len len < 2^64.

Let aw := Z_to_bv 64 a.
Let lenw := Z_to_bv 64 len.
Let nZ := mmap_len len.
Let nw := Z_to_bv 64 nZ.

Lemma fixed_len_facts : w_is0 lenw = false /\ page_round_up_Z (bv_unsigned lenw) = nZ /\ bv_unsigned aw = a.
Proof.
ltac2:(KReplay.run1 (kr_t_NodesMm04 ()) ["FixedMmap"] "h06__sat1h14__x1h24__p1h37__arithh44__ffh56__sat0h66__sat2h78__varmaph85__with96heq_nZh:2Hah;4__p2h<4__x2h=4__x3h>1xh?1yh@1HhA2H0hB1bhC1zp;1p;2p;3p;4p;6p;7p;8g01i^j1oTg00EHj2ATg003[j1:Tg00>Ij1ETg026oj3^Tg01ZAj2[Tg01jVj2XTg00[aj20Tg00bAj2RTg01k>j3QTg01kbj2nTg00@Jj1mTg005Aj1gTg00@jj2LTg00AHj1aTg00Afj1_Tg00C4j2MTg00BQj2FTg007;j1ZTg00Dfj2YTg00Ebj2WTg007]j3;Tg00FNj3VTg00Fmj4UTg00;<R0j22Tg027`j2TTg00>gj2@Tg00YOj2HTg01gfj1GTg004@j1STg00Xej2BTg00lAj1PTg01h`j2?Tg01N8j1OTg01i=j2lTg00CWj4=Tg01lgj6kTg019Aj2fTg00`^j3eTg01mKj2dTg00I@j6KTg01]Lj2JTg00\=j1>Tg00\\j2<Tg00]Ej3DTg00]nj2`Tg00^Zj3bTg00jWj1cTg00_:j4ITg00`;j3]Tg00Shj4NTg00J5j7hTg01lCj6\Tg00DBj7iTg00JYj8jTg00L=R1f1R2f0R33;p=5%:3#:p=7g00PoR4/@3p=1P1P2g00h1P3C=p=9P2g00L[R5g00M:R6P6g00MZR7P3g00N:Fhp=3P2P5P6P6P7P3E\p=Cf2R8P5P6P6P7P2P3Fip=6f3R9P5P6P6P7P8P2P3Gjp=4g00K=R:g00RE7;3p=8p,3lenR;%o;R<,A1R=p,2nZR>/5<R?eR@P?p,1aRAg00NZRB#:RC#:RD#7#7RE#7#7#7#ERFp,2HaRG3^RH%1F1[AF#1[RI%ECRJ%EERK'XRL104JRM%1K1RJKRN,04[RO[RP%1JRQg00QMRRAQJK2UW:RK%1N\R^:QRQP2g01nC1n4J'APMeO1RMPOp-0RRg00O\RS#mRT%gSRU1L12RV%a1RW%_1RX1M14RY1F1BRB'9,3XRZ1CX956XR[%Z6R\PZC41YX7R]P3P8g00K]R^,A:1W38=;:^dAV142CUR^b4b7b8X11W21043R_/22R`1042[^11^2RP310;NRaP;p,4HlenRbO3Rcb3b0b5b0b6b9'T1@;<1H;F,0<RF'2p,4lenwRd#G#8%SERE/Bd#P/5>R>p,2aw,BE/5ARd'2P:1?;4%83XB:P01?23#81582#OR0[1523#O1?82#8[R:1?98#8\01l23P3n2001000000120000000X?1X>1P:^?1^>1P3P;P4P@P?PHPIPLPPPKPQPMPOPTPUPVPWPXP[P\PXP5P6P6P7P1PBg01niPYC=,3XEkC4P]P^b4b7b8X11X2RA;124g00O?[\`^11^2RPcb3b0b5b0b6b9O3bA1fE;Rc#GP@P?PHPIPLPPPKPQPMPOPTPUPVPWPX1M1J=e1ERJ,9B,3XRV96XZP\P1PYg00PHRZPBC=,3XR`=6XVRVC4P]P^b4b7b8X11103N,2_%12102N'2[^11P3P;PbO2b3b0b5b0b6R_b9,d;EKP>PdP1P;%P3/5<XC1P=1BEc1J;_EKP@P?PHPIPLPPPKPQPMPOg00ffRO#>RM#>#>RQ#>,<11<1Q1<1M1<1O5D15D15D1g00gE'`=bSTPUP1P11L19P8%c1RUCIP2PUCIPWPXP11F1CRCPZ1F1DRDC=,3Xf5,CX56XP\PXA]1BD/9J,3XP\PXP`P\PX19YC,3Xf6RC,CX56XP\PVC4C4C4C4P]P^b4b7b8X11X<1X=1X2RX;R1@28/291H29/0N%18f4R8,04f7'2%18108N'2[[[[^11^<1^=1^2R^;RP3PaPFP<P;PAPCp,5HwrapPGPbO9b3b0b5b0b6b9,JACNCNb@o"). Qed.

(* [comment removed for export] *)
Lemma fixed_gate_wrap : (two_pow_64 <=? bv_unsigned aw + page_round_up_Z (bv_unsigned lenw)) = false.
Proof.
ltac2:(KReplay.run1 (kr_t_NodesMm04 ()) ["FixedMmap"] "h01Hh12Hah26__sat1h34__x1h44__x2h51xh61yh71zh82_Hh97__arithh:4__ffh;6__sat0h<6__sat2h=8__varmaph>5__with?2a0p;1p;2p;3p;4p;7p;8p;6g01gfj1ZTg003[j17Tg004@j1YTg00Xej2<Tg00lAj1LTg007]j36Tg00;<R0j29Tg00YOj22Tg01d>j23Tg00[aj21Tg033]j2>Tg00>Ij18Tg026oj3VTg00>gj25Tg01ZAj2UTg01jVj2TTg00bAj2NTg01k>j3KTg01kbj2ITg00EHj2:Tg00@Jj1ETg005Aj1DTg00@jj2FTg00jWj1CTg00_:j4GTg00AHj1HTg00Afj1BTg00BQj2;Tg00`;j3JTg00C4j2ATg00`^j3@Tg00CWj4MTg00J5j7?Tg007;j1OTg00JYj8PTg00Dfj2QTg00Ebj2RTg00FNj3STg00Fmj4XTg01i^j1WTg00I@j6=Tg00K=R1f0R2g00RE36p=0%72#7p=4g034=p,4lenwR3#Z#0R4g00L=R5g00NZR6#7R7#7#4#4R8#YR9/<3#LR3p,2nZR:36R;p,2aw,<9R<p,1aR=565R>'9R?'9P0P4P?g00emR@12<3'3#0RAP2P0P;P>PAP2P5P:f1RA,2<,3@#0\>X75P5P=122:,3@#0X75P013A2#0f2R0,1ARB[112A130A#0[RCf3/30#0\B1>A2P2n2001000000120000000X65X55PC^65^55P2P@12=:R:%48#4#4#8RCp,2Ha5V=g00PoRB/5C1U=C,5B[%87RC%88R8'T11BCRD15B81NC8RE,1B[RF[15BCRGg00QMRHAKC8AUW115BE\H^1GPAg01nC1IBC':PDeO1PFg00O\RF#E%DFP51F50PA%C5CG%H5%B5RFg00L[RDg00M:RGPGg00MZRHPFPDPGPGPHP51;561;575J5g00h11A5C=@59CMg00N:F?R9%OGP9GP1QFHP2P0g00K]RH,:11R20=61HdAS5BACXb:b=b>X35X45122A/1E12A0/1E[^35^45P2p,3len#WP=p,5HwrapO3b9b2b;b2b<11:@eO3b0P<P2E=X0>P3P2E=X0;PAP2O2n2001000000121000000X0?X84PAP2O2n2001000000121000000b?o"). Qed.
Lemma fixed_gate_align : negb (Z.eqb (bv_unsigned aw mod page_size) 0) = false.
Proof.
ltac2:(KReplay.run1 (kr_t_NodesMm04 ()) ["FixedMmap"] "h01zh11Hh22_Hh33_H0h42a0p;1p;2p;3p;6g01gfj1>Tg004@j1<Tg00Xej29Tg00lAj1=Tg007]j36Tg00;<R0j27Tg01ZAj23Tg01h`j22Tg014]j14Tg00>Ij1;Tg00EHj2:Tg00I@j65Tg003[j18Tg00K=R1f0R2g00RER336p=1%82#8p=0g034=p,4lenwR4#>#1R5g00L=R6g00NZ#0#0#0R7#<R8/94#=p,2nZ36R4p,2aw,98R8p,1aR9566R:'7R;'7P0P5P;g01_WR<,38g00PoR='2#4#1R>P2P0P4P:P>P2P6P9132</2=#4#1X06P6%07#0#0#;R71392/2=#4#1X06P6P=122=#4#1X061:131397p,3HalE5P<g035?E5P8P2E5X1:X34f1R4P2O2n2001000000120000000X1;X25P4P2O2n2001000000121000000b4o"). Qed.

(* [comment removed for export] *)
Lemma fixed_shape_pre :
  mmap_fixed_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)
  || mmap_fixed_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)
  || mmap_noreplace_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)
  || mmap_noreplace_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  negb (mmap_off_aligned_b (Z_to_bv 64 0)) = false
  /\ negb (mmap_anon_b (Z_to_bv 64 flags)) = false
  /\ mmap_modeled_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false.
Proof.
ltac2:(KReplay.run1 (kr_t_NodesMm04 ()) ["FixedMmap"] "p'0h01Hh12Hsh21bi001bh32_Hh42Hch52S1h62S2h72S3h82S4h93BITh:2T'h;1mh<1nh=1xh>1yh?1zh@4COREhA2NEhB2Z0hC1ep;1p;2p;3p;6p;4g003[j1=Tg004@j1dTg019Aj2BTg02H7j3STg02J<j3cTg02Q:j3[Tg02RHj3XTg00EHj2GTg007]j36Tg02a?j1OTg00YOj2?Tg00V;R0j2CTg00Xej2LTg01h`j25Tg016Xj22Tg01gfj1YTg0165j37Tg00;<R1j23Tg02U9j2WTg036@j3JTg00m?j28Tg036Zj1VTg037ej3UTg038Aj3FTg00Haj2KTg00?Cj1RTg00>Ij1QTg02cBj29Tg02ccj2PTg014]j1:Tg02dBj3NTg000`j6ATg02`8j1TTg01oPj1bTg020Pj3aTg02G3j3`Tg023Aj1_Tg02bCj2^Tg02baj1]Tg01N8j1HTg01i=j2\Tg00I@j6@Tg02dfj3ZTg00Shj4DTg038[j1MTf2R2f1R3'8f0R4'8p=<g00K=R51834g00K]R636p=4g00L=R7?634p=>A6546p=0g00RER89654p=1P5P2P3g00QiP6P4EAp=IP7f4f3R9P2P3P4E@p=;P5P8P9P2P3P4E@p=Eg00NZ#=R:#=#=#=#=#=#dR;p,4prot'BR<p,5flags,B;R=g00PoR>,B;R?3SR@Ac<=?RAA[<=?RB3<AX<=?RC'4P@P51G54RDA65@4REP5A<3AB/4C%O=RFg02lbg02m_RG'?RHg039;'?RI'>RJg03:6RK,?HRL,>FRM1?IKRK,>FRN'CRO'CRP]1^5EP3%0@A<6AB/4C1L;<REg032b'5RQ15FIRR'2RS%Y?RT;73%0SRS%0TRU'3P1PSPUPPP4A7QR3%0QRV%0RRW'3P1PVPWPPP4P11534RX#01>23RY[RZ1>34R[1523R\#0R][1>92\]1W34P3n2001000000120000000X;7X<7R]PZ^;7^<7RZP4PFPIP3O3PJAJJO4b4b0X4WR^X3VP3P4O2n2001000000121000000b5X3UX5SP3P4O2n2001000000121000000b5W1W5%1@A<8AB/4CPAP5PDA65A4R@P5A<83B/4CPP]1^6@P3%0AA<86B/4Cg02jkg02kf'?,5ERE/2RR@?7T3%0@R@/3UP1P@PUPPP4A7ER3%0ERR/3WP1PRPWPPP4P^X3RP3P4O2n2001000000121000000b6X3UX6@P3P4O2n2001000000121000000b6W1W6%1A1888RA/8B/4CPBP5PDA65B4R@P518A3/4CPP]1^7@P3%0B18A6/4C%V=R@,2QR^?7T3%0^R^/3UP1P^PUPPP4A7Q@3%0@RW,3VP1PVPWPPP415FLRS15FKR_;U4%0SRS%0_R_'CP0PSP_PPP4P]PZP4PFPLP3O3PMAJMN49FJOb4b0X4SP4O1P]PZP4PFPKP3O3PNAFMN49FJOb4b0X4_P4O1n200100000021100011000b4X4WR_X3VP3P4O2n2001000000121000000b7X3UX7^P3P4O2n2001000000121000000b7W1W7%1B18A8RA/4CPCP5PDA65C4RDP514A3PP]1^8DP3%0C14A612E@RD?7T3%0DRD/3UP1PDPUPPP4A7E@313RWP1PRPWPPP4P_X3RP3P4O2n2001000000121000000b8X3UX8DP3P4O2n2001000000121000000b8W1W8%1C18A8RA#0P5p-0P4g00O?RCg00QMn0110000020000XC5RD=IA4PC1KP4b0W1W8n0110000020100P4P2O2b8b2W1W7n0110000020101P4P2O2b7b2W1W6n0110000020101P4P2O2b6b2W1W5n0110001020101P4P2O2b5b2PPP0PJPO%R:#QR:,9F#0RPP4PI194:#0X?7RA1G56RUPFP4D;X0JP4O1P0PMPNPPP4PLPAPUPFP4D;X0MP4O1PKPAPUPFP4D;X0NP4O1n200100000021000010000X0OP4O1n200100000021000011000PPP51L;=R;g02n^RP'P/9:%04RRX25R_P419;:RW19P:#:R@'2RBAN;P:EA%0BA7W@4%0WRB%0@R@'3P1PBP@%T?#:#1RP%b=#:#1R^Aa<=?#1A`<=?#1'3R?'3R='3P4PPP=1G58R=P^P?P1%:4RP#1%03R<[%:3RV#1\RRR%:2RZ#1\<%_4P4n2001000000120000000X25PR^25P41^;GRR/5>R<#:P1%0P%13RP[%14%0V[RV%0Z\P%]4P4n2001000000120000000X25PV^25P4P<P1%1X%HYRY[%H[%1\[R\1592#1\Y1\34P4n2001000000120000000X>7X=7P\^>7^=7P4PRP>A67R>R\P519G:RY,2WP_P5P6124Y#0X25PUPWf5E@19R:RWAZ;G:E@%0WP7PRPAP4P>P3EA19>:R:#0AI:D4PC1KC4b0b:b:WB%H\eO3b0O2b0O2b0P^eP0PJPO15FHR^#1R\f7PI154H#1X?7R7P=PFP4D;X0JP4O1P0PMPNP\P4PLP7P=PFP4D;X0MP4O1PKP7P=PFP4D;X0NP4O1n200100000021000010000X0OP4O1n200100000021000011000P\12E4/2T#112Q4/2T#1'3X25124T#1R\12Q8RO/2T#1'3X25128T#1RT/3\X25PTPTP=P=CDPO%MQCE12E8%MECEP^P4CEP?ebACDCDX3@X9BP3P4O2n2001000000121000000b9b9b9b@W1o"). Qed.

Lemma fixed_none_grant : forall mo,
  mmap_fixed_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  a + nZ <= alloc_top (m_vmmaps mo) -> negb (0 <? bv_unsigned aw) = false ->
  region_free (vm_reserved (m_vmmaps mo)) aw nw = true ->
  exists eg mg, check_mmap aw lenw (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eg mo
                = CheckOk mg [] /\ errno_ret_in mmap_errnos (eff_ret eg) = false.
Proof.
  intros mo Hshape Htop Hpos Hres. destruct fixed_len_facts as (L0 & L1 & La).
  destruct (fixed_shape_pre ltac:(rewrite Hshape; reflexivity)) as (G1 & G2 & G3 & G4).
  pose proof (mmap_len_bound len ltac:(lia)) as LB.
  assert (NE : errno_ret_in mmap_errnos aw = false).
  { apply errno_ret_in_mmap_small. apply (errno_of_below_top aw (m_vmmaps mo) nZ); [subst nZ; lia| rewrite La; exact Htop]. }
  exists (mkEffectU aw [] [] [(aw, nw)] [] []).
  destruct (region_free (vm_reserved (m_vmmaps mo)) aw nw && map_contains (vm_maps (m_vmmaps mo)) aw nw) eqn:S1.
  2: destruct (region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) aw nw) eqn:S2.
  all: eexists; split; [|exact NE].
  all: unfold check_mmap; rewrite G1, G2, L0, G3, G4, Hshape; cbv iota beta zeta.
  all: rewrite fixed_gate_wrap, fixed_gate_align, Hpos, L1, La; rewrite (proj2 (Z.leb_le _ _) Htop).
  all: cbn [negb]; cbv iota; fold nw; rewrite S1; try rewrite S2; try rewrite Hres.
  all: cbv iota; rewrite NE, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma nstep_mmap_fixed_none_no_err : forall mo rsp mo' evs,
  mmap_fixed_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  nstep (NMmap a len prot flags) mo rsp mo' evs ->
  errno_of (eff_ret rsp) = None /\ eff_ret rsp = aw /\ evs = [].
Proof.
(* [comment removed for export] *)
  intros mo rsp mo' evs Hshape H. pose proof H as Hst. destruct fixed_len_facts as (L0 & L1 & La).
  destruct (fixed_shape_pre ltac:(rewrite Hshape; reflexivity)) as (G1 & G2 & G3 & G4).
  apply nstep_mmap_iff in H as (_ & H & _). unfold check_mmap in H. fold lenw aw in H.
  rewrite G1, G2, L0, G3, G4, Hshape in H. cbv iota beta in H. cbv zeta in H.
  rewrite fixed_gate_wrap in H.
  destruct (negb (bv_unsigned aw + page_round_up_Z (bv_unsigned lenw) <=? alloc_top (m_vmmaps mo))) eqn:Gt; [discriminate|].
  rewrite fixed_gate_align in H.
  destruct (negb (0 <? bv_unsigned aw)) eqn:Gp; [discriminate|].
  apply negb_false_iff, Z.leb_le in Gt. rewrite L1, La in Gt.
  pose proof (mmap_len_bound len ltac:(lia)) as LB.
  assert (NOERR : errno_of aw = None) by (apply (errno_of_below_top aw (m_vmmaps mo) nZ); [subst nZ; lia| rewrite La; exact Gt]).
  rewrite L1 in H. fold nw in H.
  assert (Hres : region_free (vm_reserved (m_vmmaps mo)) aw nw = true).
  { destruct (region_free (vm_reserved (m_vmmaps mo)) aw nw) eqn:R3; [reflexivity|]. exfalso.
    destruct (region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) aw nw) eqn:R2;
      [rewrite (region_free_app_l _ _ _ _ R2) in R3; discriminate R3|].
    cbn [andb] in H. cbv iota in H. discriminate H. }
  destruct (fixed_none_grant mo Hshape Gt Gp Hres) as (eg & mg & Hg & Hng).
  pose proof (nstep_mmap_grant_no_errno _ _ _ _ _ _ _ _ _ _ _ Hst Hg Hng) as NE.
  destruct rsp as [r ws zs us cs ci]. cbn [eff_ret] in NE |- *.
  destruct (region_free (vm_reserved (m_vmmaps mo)) aw nw && map_contains (vm_maps (m_vmmaps mo)) aw nw) eqn:S1.
  2: destruct (region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) aw nw) eqn:S2.
  3: destruct (region_free (vm_reserved (m_vmmaps mo)) aw nw) eqn:S3; [|discriminate].
  all: destruct ws; [|discriminate]; destruct zs; [|discriminate];
       destruct cs; [|destruct us; discriminate]; destruct ci; [|destruct us; discriminate].
  all: rewrite NE in H; cbv iota in H.
  all: destruct (bv_eqb r aw && _) eqn:E; [|discriminate]; apply andb_prop in E as [E _]; apply bv_eqb_eq in E; subst r.
  all: injection H as _ <-; auto.
Qed.

(* [comment removed for export] *)
Ltac noreplace_gate H L1 La GT aw lenw mo :=
  cbv zeta in H; rewrite fixed_gate_wrap in H;
  destruct (negb (bv_unsigned aw + page_round_up_Z (bv_unsigned lenw) <=? alloc_top (m_vmmaps mo))) eqn:GT; [discriminate|];
  rewrite fixed_gate_align in H;
  destruct (negb (0 <? bv_unsigned aw)) eqn:?Gp; [discriminate|];
  apply negb_false_iff, Z.leb_le in GT; rewrite L1, La in GT; rewrite L1 in H.

Lemma noreplace_not_fixed :
  mmap_noreplace_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)
  || mmap_noreplace_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  mmap_fixed_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false
  /\ mmap_fixed_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false.
Proof.
  intros Hshape.
  assert (CORE : Z.eqb (mmap_flags_core (Z_to_bv 64 flags)) (MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED) = false).
  { assert (NR : mmap_noreplace_flags_b (Z_to_bv 64 flags) = true).
    { destruct (mmap_noreplace_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)) eqn:S3.
      - unfold mmap_noreplace_noaccess_b in S3. apply andb_prop in S3 as [S3 _]. apply andb_prop in S3 as [_ S3]. exact S3.
      - cbn [orb] in Hshape. unfold mmap_noreplace_rw_b in Hshape.
        apply andb_prop in Hshape as [Hs _]. apply andb_prop in Hs as [_ Hs]. exact Hs. }
    unfold mmap_noreplace_flags_b in NR. apply orb_prop in NR as [NR|NR]; apply Z.eqb_eq in NR; rewrite NR; reflexivity. }
  unfold mmap_fixed_noaccess_b, mmap_fixed_rw_b. rewrite CORE, !andb_false_r. auto.
Qed.

Lemma errno_ret_in_mmap_EEXIST : errno_ret_in mmap_errnos (errno_ret EEXIST) = false.
Proof.
  unfold errno_ret_in, mmap_errnos. cbn [existsb]. rewrite orb_false_r.
  destruct (bv_eqb (errno_ret EEXIST) (errno_ret ENOMEM)) eqn:E; [|reflexivity].
  apply bv_eqb_eq in E. apply (f_equal errno_of) in E.
  rewrite !errno_of_errno_ret in E by (unfold EEXIST, ENOMEM; lia). discriminate E.
Qed.

Lemma noreplace_grant : forall mo,
  mmap_noreplace_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)
  || mmap_noreplace_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  a + nZ <= alloc_top (m_vmmaps mo) -> negb (0 <? bv_unsigned aw) = false ->
  (mmap_noreplace_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = false ->
   region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) aw nw = true ->
   mmap_fixed_fresh_refusable (Z_to_bv 64 flags) mo nZ = false) ->
  exists eg mg, check_mmap aw lenw (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eg mo
                = CheckOk mg [] /\ errno_ret_in mmap_errnos (eff_ret eg) = false.
Proof.
  intros mo Hshape Htop Hpos Hfresh. destruct fixed_len_facts as (L0 & L1 & La).
  destruct (fixed_shape_pre
              ltac:(destruct (mmap_noreplace_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)),
                              (mmap_noreplace_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0));
                    rewrite ?orb_true_r, ?orb_false_r; first [reflexivity | discriminate Hshape]))
    as (G1 & G2 & G3 & G4).
  destruct (noreplace_not_fixed Hshape) as [G5 G6].
  pose proof (mmap_len_bound len ltac:(lia)) as LB.
  assert (NE : errno_ret_in mmap_errnos aw = false).
  { apply errno_ret_in_mmap_small. apply (errno_of_below_top aw (m_vmmaps mo) nZ); [subst nZ; lia| rewrite La; exact Htop]. }
  destruct (region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) aw nw) eqn:S2;
    destruct (mmap_noreplace_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)) eqn:SN;
    [ exists (mkEffectU aw [] [] [(aw, nw)] [] [])
    | exists (mkEffectU aw [] [(aw, nw)] [] [] [])
    | exists (mkEffectU (errno_ret EEXIST) [] [] [] [] [])
    | exists (mkEffectU (errno_ret EEXIST) [] [] [] [] []) ];
    eexists; (split; [| first [exact NE | exact errno_ret_in_mmap_EEXIST]]);
    unfold check_mmap; rewrite G1, G2, L0, G3, G4, G5, G6, SN; [| cbn [orb] in Hshape; rewrite Hshape | | cbn [orb] in Hshape; rewrite Hshape];
    cbv iota beta zeta;
    rewrite fixed_gate_wrap, fixed_gate_align, Hpos, L1, La; rewrite (proj2 (Z.leb_le _ _) Htop);
    cbn [negb]; cbv iota; fold nw; rewrite S2; cbv iota.
  - rewrite NE, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  - pose proof (Hfresh eq_refl eq_refl) as R. unfold mmap_fixed_fresh_refusable in R. apply negb_false_iff in R.
    rewrite NE, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl), R. reflexivity.
  - rewrite errno_ret_in_mmap_EEXIST, bv_eqb_refl. reflexivity.
  - rewrite errno_ret_in_mmap_EEXIST, bv_eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma nstep_mmap_noreplace_err : forall mo rsp mo' evs e,
  mmap_noreplace_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)
  || mmap_noreplace_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true ->
  nstep (NMmap a len prot flags) mo rsp mo' evs ->
  errno_of (eff_ret rsp) = Some e ->
  let h := m_vmmaps mo in
  mo' = mo /\ evs = []
  /\ ( (region_free (vm_reserved h ++ vm_maps h) aw nw = false /\ e = EEXIST)
     \/ (region_free (vm_reserved h ++ vm_maps h) aw nw = true /\ e = ENOMEM
         /\ mmap_noreplace_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0) = true
         /\ mmap_fixed_fresh_refusable (Z_to_bv 64 flags) mo nZ = true)).
Proof.
  intros mo rsp mo' evs e Hshape H He. pose proof H as Hst. destruct fixed_len_facts as (L0 & L1 & La).
  destruct (fixed_shape_pre
              ltac:(destruct (mmap_noreplace_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)),
                              (mmap_noreplace_rw_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0));
                    rewrite ?orb_true_r, ?orb_false_r; first [reflexivity | discriminate Hshape]))
    as (G1 & G2 & G3 & G4).
  destruct (noreplace_not_fixed Hshape) as [G5 G6].
  apply nstep_mmap_iff in H as (_ & H & _). unfold check_mmap in H. fold lenw aw in H.
  rewrite G1, G2, L0, G3, G4, G5, G6 in H. cbv iota beta in H.
  pose proof (mmap_len_bound len ltac:(lia)) as LB.
  destruct rsp as [r ws zs us cs ci]. cbn [eff_ret] in He.
  destruct (mmap_noreplace_noaccess_b (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 0)) eqn:SN;
    [| cbn [orb] in Hshape; rewrite Hshape in H]; noreplace_gate H L1 La GT aw lenw mo; fold nw in H;
    (assert (NOERR : errno_of aw = None) by (apply (errno_of_below_top aw (m_vmmaps mo) nZ); [subst nZ; lia| rewrite La; exact GT]));
    destruct (region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) aw nw) eqn:S2.
  -
    exfalso. destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
    destruct (noreplace_grant mo ltac:(rewrite SN; reflexivity) GT ltac:(assumption)
                (fun Hn _ => ltac:(rewrite SN in Hn; discriminate Hn))) as (eg & mg & Hg & Hng).
    pose proof (nstep_mmap_grant_no_errno _ _ _ _ _ _ _ _ _ _ _ Hst Hg Hng) as NE. cbn [eff_ret] in NE.
    rewrite NE in H. cbv iota in H.
    destruct (bv_eqb r aw) eqn:E; [| cbn [andb] in H; cbv iota in H; discriminate]. apply bv_eqb_eq in E. subst r. rewrite NOERR in He. discriminate.
  -
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (noreplace_grant mo ltac:(rewrite SN; reflexivity) GT ltac:(assumption)
                (fun _ Hr => ltac:(rewrite S2 in Hr; discriminate Hr))) as (eg & mg & Hg & Hng).
    pose proof (nstep_mmap_grant_no_errno _ _ _ _ _ _ _ _ _ _ _ Hst Hg Hng) as NE. cbn [eff_ret] in NE.
    rewrite NE in H. cbn [orb] in H.
    destruct (bv_eqb r (errno_ret EEXIST)) eqn:E; [|discriminate]. apply bv_eqb_eq in E. subst r. injection H as <- <-.
    rewrite errno_of_errno_ret in He by (unfold EEXIST; lia). injection He as <-. repeat split; try reflexivity. left. auto.
  -
    destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate]. destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
    fold nZ in H. case_errno_in_eqn H Herr.
    + apply errno_ret_in_mmap_inv in Herr. subst r. rewrite errno_of_errno_ret in He by (unfold ENOMEM; lia). injection He as <-.
      destruct zs; [|discriminate]. injection H as <- <-. repeat split; try reflexivity. right.
      split; [exact S2|]. split; [reflexivity|]. split; [exact Hshape|].
      destruct (mmap_fixed_fresh_refusable (Z_to_bv 64 flags) mo nZ) eqn:R; [reflexivity|]. exfalso.
      destruct (noreplace_grant mo ltac:(rewrite SN; exact Hshape) GT ltac:(assumption) (fun _ _ => R))
        as (eg & mg & Hg & Hng).
      pose proof (nstep_mmap_grant_no_errno _ _ _ _ _ _ _ _ _ _ _ Hst Hg Hng) as X. cbn [eff_ret] in X.
      rewrite errno_ret_in_mmap_ENOMEM in X. discriminate X.
    + exfalso. destruct (bv_eqb r aw) eqn:E; [| cbn [andb] in H; cbv iota in H; discriminate].
      apply bv_eqb_eq in E. subst r. rewrite NOERR in He. discriminate.
  -
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (noreplace_grant mo ltac:(rewrite SN; exact Hshape) GT ltac:(assumption)
                (fun _ Hr => ltac:(rewrite S2 in Hr; discriminate Hr))) as (eg & mg & Hg & Hng).
    pose proof (nstep_mmap_grant_no_errno _ _ _ _ _ _ _ _ _ _ _ Hst Hg Hng) as NE. cbn [eff_ret] in NE.
    rewrite NE in H. cbn [orb] in H.
    destruct (bv_eqb r (errno_ret EEXIST)) eqn:E; [|discriminate]. apply bv_eqb_eq in E. subst r. injection H as <- <-.
    rewrite errno_of_errno_ret in He by (unfold EEXIST; lia). injection He as <-. repeat split; try reflexivity. left. auto.
Qed.
End FixedMmap.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Mprotect.
Variables (a len : Z).
Hypothesis Hlen : 0 < len < 2^64.
Hypothesis Ha : 0 <= a.
Hypothesis Hal : a mod 4096 = 0.
Hypothesis Hwrap : a + mmap_len len < 2^64.

Let aw := Z_to_bv 64 a.
Let nZ := mmap_len len.
Let nw := Z_to_bv 64 nZ.

Lemma mprotect_grant : forall mo,
  map_contains (vm_noaccess (m_vmmaps mo)) aw nw = true -> map_contains (vm_maps (m_vmmaps mo)) aw nw = true ->
  mprotect_refusable mo aw nw = false ->
  exists eg mg, check_mprotect aw (Z_to_bv 64 len) (Z_to_bv 64 (PROT_READ + PROT_WRITE)) eg mo = CheckOk mg []
                /\ errno_ret_in mprotect_errnos (eff_ret eg) = false.
Proof.
  intros mo C1 C2 R. unfold mprotect_refusable in R. apply negb_false_iff in R.
  pose proof (mmap_len_bound len ltac:(lia)) as LB.
  assert (La : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; lia).
  assert (Ll : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  assert (N0 : errno_ret_in mprotect_errnos (Z_to_bv 64 0) = false)
    by (apply errno_ret_in_mprotect_small; apply errno_of_lit; lia).
  exists (mkEffectU (Z_to_bv 64 0) [] [(aw, nw)] [] [] []). eexists. split; [|exact N0].
  unfold check_mprotect.
  change (mprotect_grows_conflict_b (Z_to_bv 64 (PROT_READ + PROT_WRITE))) with false.
  rewrite La, page_size_4096, Hal. cbn [Z.eqb negb].
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite Ll. fold (mmap_len len). fold nZ.
  replace (two_pow_64 <=? a + nZ) with false by (symmetry; apply Z.leb_gt; unfold two_pow_64; subst nZ; lia).
  change (negb (mprotect_modeled_b (Z_to_bv 64 (PROT_READ + PROT_WRITE)))) with false. cbv iota zeta. fold nw.
  rewrite C1, C2. cbn [andb]. cbv iota. rewrite N0, R. change (w_is0 (Z_to_bv 64 0)) with true.
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma nstep_mprotect_err_refusable : forall mo rsp mo' evs e,
  nstep (NMprotect a len (PROT_READ + PROT_WRITE)) mo rsp mo' evs ->
  errno_of (eff_ret rsp) = Some e ->
  let h := m_vmmaps mo in
  e = ENOMEM /\ mo' = mo /\ evs = []
  /\ map_contains (vm_noaccess h) aw nw = true /\ map_contains (vm_maps h) aw nw = true
  /\ mprotect_refusable mo aw nw = true.
Proof.
  intros mo rsp mo' evs e H He. pose proof (mmap_len_bound len ltac:(lia)) as LB.
  pose proof H as Hst. apply nstep_mprotect_iff in H as [H _]. unfold check_mprotect in H. fold aw in H.
  assert (La : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; lia).
  assert (Ll : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  change (mprotect_grows_conflict_b (Z_to_bv 64 (PROT_READ + PROT_WRITE))) with false in H.
  rewrite La, page_size_4096, Hal in H. cbn [Z.eqb negb] in H.
  rewrite w_is0_lit in H by lia. replace (len =? 0) with false in H by (symmetry; apply Z.eqb_neq; lia).
  rewrite Ll in H. fold (mmap_len len) in H. fold nZ in H.
  replace (two_pow_64 <=? a + nZ) with false in H by (symmetry; apply Z.leb_gt; unfold two_pow_64; subst nZ; lia).
  change (negb (mprotect_modeled_b (Z_to_bv 64 (PROT_READ + PROT_WRITE)))) with false in H. cbv iota zeta in H. fold nw in H.
  destruct rsp as [r ws zs us cs ci]. cbn [eff_ret] in He.
  destruct (map_contains (vm_noaccess (m_vmmaps mo)) aw nw && map_contains (vm_maps (m_vmmaps mo)) aw nw) eqn:S1.
  - apply andb_prop in S1 as [C1 C2].
    destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate]. destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
    case_errno_in_eqn H Herr.
    + apply errno_ret_in_mprotect_inv in Herr. subst r. rewrite errno_of_errno_ret in He by (unfold ENOMEM; lia). injection He as <-.
      destruct zs; [|discriminate]. injection H as <- <-. repeat split; auto.
      destruct (mprotect_refusable mo aw nw) eqn:R; [reflexivity|]. exfalso.
      destruct (mprotect_grant mo C1 C2 R) as (eg & mg & Hg & Hng).
      pose proof (nstep_mprotect_grant_no_errno _ _ _ _ _ _ _ _ _ _ Hst Hg Hng) as X. cbn [eff_ret] in X.
      rewrite errno_ret_in_mprotect_ENOMEM in X. discriminate X.
    + exfalso. destruct (mprotect_budget_ok mo aw nw && w_is0 r && _) eqn:E; [|discriminate].
      apply andb_prop in E as [E _]. apply andb_prop in E as [_ E]. unfold w_is0 in E. apply bv_eqb_eq in E. subst r.
      rewrite errno_of_lit in He by lia. discriminate.
  - exfalso. destruct (map_contains (vm_maps (m_vmmaps mo)) aw nw && region_free (vm_noaccess (m_vmmaps mo)) aw nw); [|discriminate].
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (w_is0 r) eqn:E; [|discriminate]. unfold w_is0 in E. apply bv_eqb_eq in E. subst r.
    rewrite errno_of_lit in He by lia. discriminate.
Qed.

(* [comment removed for export] *)
Lemma mprotect_refusable_false_intro : forall mo,
  vm_backing_used (mprotect_model_next mo aw nw) <= vm_limit (m_vmmaps mo) ->
  mprotect_refusable mo aw nw = false.
Proof.
  intros mo Hb. unfold mprotect_refusable, mprotect_budget_ok, vm_backing_within_limit.
  unfold mprotect_model_next in *. rewrite m_vmmaps_with_vmmaps. cbn [vm_limit].
  rewrite (proj2 (Z.leb_le _ _) Hb). reflexivity.
Qed.
End Mprotect.
