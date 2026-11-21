(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: changed In_lranges, KL2, KL2_brk0 and 54 more; added KL2_meta_page_free, Zify, k2_img_in and 5 more; removed region_free_above; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/CJ/Bridge/KLink.v, 524 lines within its lines 25-885. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC. From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap Mprotect. From LinuxProcessSemantics.LinuxProcessSem.Checks Require ExecutableSpecs. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Nodes. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require ITree. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require Nodes. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module BrNodes.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Nodes. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.SimInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.AllocSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.FileSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.Scfg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.DivergeSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlgX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Nodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.AgentNodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.SpecConsts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require ITree. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.MState OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.ITree.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require Nodes.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BrNodes () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List7map_mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingK47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputC4ELinuxProcessSemantics?LinuxProcessSem3RunFalloc_budget_refused_bK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelC4ELinuxProcessSemantics?LinuxProcessSem3Run6cfg_msI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?accessed_rangesC4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00I47Corelib4Init9Datatypes4list00K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01C4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specC4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesI47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or02I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib2CJ3Lib5Nodes4aregC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic4True01I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC47Corelib4Init5Logic7f_equalC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib7Mh_00438AgentLib7u64_litC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyK69OSSVerify5KrLib2CJ3Lib5Nodes4node09C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkK4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C69OSSVerify5KrLib2CJ3Lib5ITree4nretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprc79OSSVerify5KrLib2CJ6Bridge7Mh_01087BrNodes9gpr_areg0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00948RefNodes@srz_brk_query_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I47Corelib4Init9Datatypes3nat00c79OSSVerify5KrLib2CJ6Bridge7Mh_01087BrNodes4u214C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C56Stdlib6ZArith6BinInt1Z6moduloC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;brk_grow_okK47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01C4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC59OSSVerify5KrLib7Mh_00948RefNodes?srz_brk_grow_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeK47Corelib4Init9Datatypes4bool02K69OSSVerify5KrLib2CJ3Lib5Nodes4node0:C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZK47Corelib4Init9Datatypes3nat02c79OSSVerify5KrLib2CJ6Bridge7Mh_01087BrNodes9gpr_areg1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSim=page_round_upC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01087BrNodes7lit_ne0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01087BrNodes9gpr_areg5C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01087BrNodes9gpr_areg4C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01087BrNodes9gpr_areg3C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01087BrNodes9gpr_areg2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSim<mmap_args_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcC59OSSVerify5KrLib7Mh_00367SpinAlg8srz_mmapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSim8grant_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSim:mmap_modelC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01087BrNodes4u222C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00948RefNodesEmmap_noaccess_args_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00948RefNodesDsrz_mmap_noaccess_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00948RefNodes;grant_ok_naC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00948RefNodes>noaccess_modelC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeC4ELinuxProcessSemantics?LinuxProcessSem5State<map_containsC59OSSVerify5KrLib7Mh_00948RefNodesDfixed_noaccess_modelC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib7Mh_00388AllocSimFpage_round_up_Z_boundsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC4ELinuxProcessSemantics?LinuxProcessSem5State>alloc_top_roomK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib7Mh_00948RefNodesBmmap_fixed_args_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00948RefNodesJsrz_mmap_fixed_noaccess_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t03C4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizeC4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64C4ELinuxProcessSemantics?LinuxProcessSem5StateBstack_max_size_valK46Stdlib9micromega:ZMicromega;ZArithProof01K69OSSVerify5KrLib2CJ3Lib5Nodes4node0<C1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectBmprotect_budget_okC59OSSVerify5KrLib7Mh_00948RefNodes>mprotect_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00948RefNodes?srz_mprotect_atC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01087BrNodes4u226C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2CJ3Lib5Nodes4node0;C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSim<munmap_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSim>munmap_args_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387MmapSim:munmap_effC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg:srz_munmapC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7map_hasC4ELinuxProcessSemantics?LinuxProcessSem5State9TASK_SIZEc79OSSVerify5KrLib2CJ6Bridge7Mh_01087BrNodes4u215C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode5bm_onC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC4ELinuxProcessSemantics?LinuxProcessSem5State6in_argC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapDbrk_budget_refused_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm6MremapGmremap_budget_refused_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEmmap_budget_refused_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectImprotect_budget_refused_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_off_aligned_bC47Corelib4Init9Datatypes4negbC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;mmap_anon_bC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5w_is0C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>mmap_modeled_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapHmmap_noreserve_backed_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_noaccess_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEmmap_fixed_noaccess_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_fixed_rw_bC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_budget_okC47Corelib4Init9Datatypes3appC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapLmmap_fixed_rw_span_budget_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapImmap_noreplace_noaccess_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapCmmap_noreplace_rw_bC49OSSVerify5KrLib8PropExec:bv_eqb_neqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap@mmap_noreserve_bC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backing_usedC4ELinuxProcessSemantics?LinuxProcessSem5State7in_argsC47Corelib5Lists7ListDef3nthC4ELinuxProcessSemantics?LinuxProcessSem5State8in_sysnoc79OSSVerify5KrLib2CJ6Bridge7Mh_01087BrNodesIbudget_refused_at_of_markC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg<srz_brefusedC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectImprotect_grows_conflict_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectBmprotect_modeled_bC56Stdlib6ZArith6BinInt1Z6leb_gt".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation cjnode := OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Nodes.node.
Notation cj_at_node := OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Nodes.at_node.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Nodes (NBrk, NMmap, NMunmap, NMprotect, areg).

Section WithSegs.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma budget_refused_at_of_mark : forall ms model x8,
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  alloc_budget_refused_b (sys_input segs ms x8) model = true ->
  budget_refused_at segs (mkCfg ms model).
Proof.
  intros ms model x8 Hh Hsvc Hb. split; [exact Hh|]. right. exists x8. split; [exact Hsvc|]. left. exact Hb.
Qed.

(* [comment removed for export] *)
Lemma gpr_areg0 : forall ms, ms_gpr ms 0 = areg ms 10.
Proof. reflexivity. Qed.
Lemma gpr_areg1 : forall ms, ms_gpr ms 1 = areg ms 11.
Proof. reflexivity. Qed.
Lemma gpr_areg2 : forall ms, ms_gpr ms 2 = areg ms 12.
Proof. reflexivity. Qed.
Lemma gpr_areg3 : forall ms, ms_gpr ms 3 = areg ms 13.
Proof. reflexivity. Qed.
Lemma gpr_areg4 : forall ms, ms_gpr ms 4 = areg ms 14.
Proof. reflexivity. Qed.
Lemma gpr_areg5 : forall ms, ms_gpr ms 5 = areg ms 15.
Proof. reflexivity. Qed.

Lemma u214 : bv_unsigned (Z_to_bv 64 214) = 214.
Proof. reflexivity. Qed.
Lemma u215 : bv_unsigned (Z_to_bv 64 215) = 215.
Proof. reflexivity. Qed.
Lemma u222 : bv_unsigned (Z_to_bv 64 222) = 222.
Proof. reflexivity. Qed.
Lemma u226 : bv_unsigned (Z_to_bv 64 226) = 226.
Proof. reflexivity. Qed.

Lemma lit_ne0 : forall z, 0 < z < 2 ^ 64 -> Z_to_bv 64 z <> Z_to_bv 64 0.
Proof.
  intros z Hz Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bn_brk_query : forall ms model K,
  m_halted model = None -> m_vm_lazy model = [] ->
  cj_at_node segs (NBrk 0) ms ->
  srealizes segs scfg (mkCfg (nret ms (mkEffectU (vm_brk (m_vmmaps model)) [] [] [] [] [])) model) K ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros ms model K Hh Hlazy [Hsvc H10] Hc.
  apply (srz_brk_query_at segs scfg ms model (Z_to_bv 64 214) K Hh Hlazy Hsvc u214); [| exact Hc].
  rewrite gpr_areg0. exact H10.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bn_brk_grow : forall ms model (d : Z) K,
  m_halted model = None -> m_vm_lazy model = [] ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  cj_at_node segs (NBrk (bv_unsigned b + d)) ms ->
  bv_unsigned b mod page_size = 0 -> d mod page_size = 0 -> 0 < d ->
  0 < bv_unsigned b -> bv_unsigned b + d < 2 ^ 64 ->
  bv_unsigned (vm_start_brk h) <= bv_unsigned b + d ->
  (* [comment removed for export] *)
  srealizes segs scfg (mkCfg (nret ms (mkEffectU b [] [] [] [] [])) model) K ->
  (* [comment removed for export] *)
  (Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->
   srealizes segs scfg (mkCfg (nret ms (mkEffectU (Z_to_bv 64 (bv_unsigned b + d)) [] [(b, Z_to_bv 64 d)] [] [] []))
                        (with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                                                   (vm_noaccess h) (vm_start_brk h)
                                                   (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) model)) K) ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros ms model d K Hh Hlazy h b [Hsvc H10] Hbal Hdal Hd Hb0 Hnw Hs HA HB.
  apply (srz_brk_grow_at segs scfg ms model (Z_to_bv 64 214) d K Hh Hlazy Hsvc u214 Halloc Hbal Hdal Hd Hb0 Hnw Hs);
    [rewrite gpr_areg0; exact H10 | intros _; exact HA | exact HB].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bn_mmap_rw : forall ms model (len : Z) K,
  m_halted model = None -> m_vm_lazy model = [] ->
  cj_at_node segs (NMmap 0 len 3 34) ms -> 0 < len < 2 ^ 64 ->
  let n := page_round_up_Z len in
  (exists a, grant_ok (Z_to_bv 64 0) model a n = true) ->
  (forall a, grant_ok (Z_to_bv 64 0) model a n = true ->
     srealizes segs scfg (mkCfg (nret ms (mkEffectU a [] [(a, Z_to_bv 64 n)] [] [] []))
                               (mmap_model a (Z_to_bv 64 n) model)) K) ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros ms model len K Hh Hlazy (Hsvc & H10 & H11 & H12 & H13 & H14 & H15) Hlen n Hex HB.
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite gpr_areg1, H11; apply u64_lit; lia).
  assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 n) by (unfold page_round_up; rewrite Hu1; reflexivity).
  assert (Hargs : mmap_args_ok ms).
  { unfold mmap_args_ok. rewrite gpr_areg1, gpr_areg2, gpr_areg3, gpr_areg4, gpr_areg5, H11, H12, H13, H14, H15.
    repeat split; try reflexivity. apply lit_ne0. lia. }
  assert (H0 : ms_gpr ms 0 = Z_to_bv 64 0) by (rewrite gpr_areg0; exact H10).
  (* [comment removed for export] *)
  eapply (srz_mmap segs scfg ms model (Z_to_bv 64 222) K Hh Hlazy Hsvc u222 Hargs
            ltac:(rewrite H0; apply place_declined_b_null) Halloc).
  - intros a Ha. rewrite Hpr. rewrite H0, Hu1 in Ha. apply HB. exact Ha.
  - rewrite H0, Hu1. exact Hex.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bn_mmap_none : forall ms model (len : Z) K,
  m_halted model = None -> m_vm_lazy model = [] ->
  cj_at_node segs (NMmap 0 len 0 34) ms -> 0 < len < 2 ^ 64 ->
  let n := page_round_up_Z len in
  (exists a, grant_ok_na (Z_to_bv 64 0) model a n = true) ->
  (forall a, grant_ok_na (Z_to_bv 64 0) model a n = true ->
     srealizes segs scfg (mkCfg (nret ms (mkEffectU a [] [] [(a, Z_to_bv 64 n)] [] []))
                               (noaccess_model a (Z_to_bv 64 n) model)) K) ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros ms model len K Hh Hlazy (Hsvc & H10 & H11 & H12 & H13 & H14 & H15) Hlen n Hex HB.
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite gpr_areg1, H11; apply u64_lit; lia).
  assert (Hargs : mmap_noaccess_args_ok ms).
  { unfold mmap_noaccess_args_ok. rewrite gpr_areg1, gpr_areg2, gpr_areg3, gpr_areg4, gpr_areg5, H11, H12, H13, H14, H15.
    repeat split; try reflexivity. apply lit_ne0. lia. }
  assert (H0 : ms_gpr ms 0 = Z_to_bv 64 0) by (rewrite gpr_areg0; exact H10).
  (* [comment removed for export] *)
  apply (srz_mmap_noaccess_at segs scfg ms model (Z_to_bv 64 222) K Hh Hlazy Hsvc u222 Hargs
           ltac:(rewrite H0; apply place_declined_b_null) Halloc);
    rewrite H0, Hu1; [exact Hex | exact HB].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bn_mmap_fixed : forall ms model (addr len : Z) K,
  m_halted model = None -> m_vm_lazy model = [] ->
  cj_at_node segs (NMmap addr len 0 50) ms ->
  addr mod page_size = 0 -> 0 < addr -> 0 < len ->
  addr + page_round_up_Z len <= alloc_top (m_vmmaps model) ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) (Z_to_bv 64 addr) n = true ->
  map_contains (vm_maps (m_vmmaps model)) (Z_to_bv 64 addr) n = true ->
  srealizes segs scfg (mkCfg (nret ms (mkEffectU (Z_to_bv 64 addr) [] [] [(Z_to_bv 64 addr, n)] [] []))
                            (fixed_noaccess_model (Z_to_bv 64 addr) n model)) K ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros ms model addr len K Hh Hlazy (Hsvc & H10 & H11 & H12 & H13 & H14 & H15) Hal Hpos Hlen Htop n Hrf Hmc HB.
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as Hprb.
  assert (Htop' : alloc_top (m_vmmaps model) < 2 ^ 64) by (alloc_top_bounds; unfold two_pow_64 in *; lia).
  assert (Haddr : bv_unsigned (Z_to_bv 64 addr) = addr) by (apply u64_lit; lia).
  assert (Hargs : mmap_fixed_args_ok ms).
  { unfold mmap_fixed_args_ok. rewrite gpr_areg1, gpr_areg2, gpr_areg3, gpr_areg4, gpr_areg5, H11, H12, H13, H14, H15.
    repeat split; try reflexivity. apply lit_ne0. lia. }
  apply (srz_mmap_fixed_noaccess_at segs scfg ms model (Z_to_bv 64 222) (Z_to_bv 64 addr) len K Hh Hlazy Hsvc u222 Hargs Halloc);
    rewrite ?gpr_areg0, ?gpr_areg1, ?Haddr; first [exact H10 | exact H11 | exact HB | assumption | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bn_mprotect : forall ms model (addr len : Z) K,
  m_halted model = None -> m_vm_lazy model = [] ->
  cj_at_node segs (NMprotect addr len 3) ms ->
  addr mod page_size = 0 -> 0 < len -> 0 <= addr ->
  addr + page_round_up_Z len < two_pow_64 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  (* [comment removed for export] *)
  region_free (vdso_reserved (m_kernel model) (vdso_top (m_vmmaps model))) (Z_to_bv 64 addr) n = true ->
  map_contains (vm_noaccess (m_vmmaps model)) (Z_to_bv 64 addr) n = true ->
  map_contains (vm_maps (m_vmmaps model)) (Z_to_bv 64 addr) n = true ->
  mprotect_budget_ok model (Z_to_bv 64 addr) n = true ->
  srealizes segs scfg (mkCfg (nret ms (mkEffectU (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, n)] [] [] []))
                            (mprotect_model (Z_to_bv 64 addr) n model)) K ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros ms model addr len K Hh Hlazy (Hsvc & H10 & H11 & H12) Hal Hlen Ha0 Hnw n Hvd Hna Hma Hbud HB.
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as Hpr.
  assert (Haddr : bv_unsigned (Z_to_bv 64 addr) = addr) by (apply u64_lit; unfold two_pow_64 in Hnw; lia).
  apply (srz_mprotect_at segs scfg ms model (Z_to_bv 64 226) (Z_to_bv 64 addr) len K Hh Hlazy Hsvc u226 Halloc);
    rewrite ?gpr_areg0, ?gpr_areg1, ?gpr_areg2, ?Haddr; first [exact H10 | exact H11 | exact H12 | exact HB | assumption | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bn_munmap : forall ms model (a len : Z) K,
  m_halted model = None -> m_vm_lazy model = [] ->
  cj_at_node segs (NMunmap a len) ms ->
  a mod page_size = 0 -> 0 <= a -> 0 < len ->
  a + page_round_up_Z len <= TASK_SIZE ->
  map_has (vm_maps (m_vmmaps model)) (Z_to_bv 64 a) (Z_to_bv 64 (page_round_up_Z len)) = true ->
  srealizes segs scfg (mkCfg (nret ms (mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 a, Z_to_bv 64 (page_round_up_Z len))] [] []))
                      (munmap_model (Z_to_bv 64 a) (Z_to_bv 64 (page_round_up_Z len)) model)) K ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros ms model a len K Hh Hlazy (Hsvc & H10 & H11) Hal Ha0 Hlen Hnw Hhas Hc.
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as Hpr.
  assert (HTS : TASK_SIZE < 2 ^ 64) by (unfold TASK_SIZE; lia).
  assert (Haddr : bv_unsigned (Z_to_bv 64 a) = a) by (apply u64_lit; lia).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite gpr_areg1, H11; apply u64_lit; lia).
  assert (Hprr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 (page_round_up_Z len)) by (unfold page_round_up; rewrite Hu1; reflexivity).
  assert (H0 : ms_gpr ms 0 = Z_to_bv 64 a) by (rewrite gpr_areg0; exact H10).
  assert (Hargs : munmap_args_ok ms model).
  { unfold munmap_args_ok. rewrite H0, Hu1, Hprr, Haddr. repeat split; try assumption.
    intro Hz. apply (f_equal bv_unsigned) in Hz. rewrite Hu1 in Hz. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hz. lia. }
  eapply (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg.srz_munmap segs scfg ms model (Z_to_bv 64 215) K Hh Hlazy Hsvc u215 Hargs Halloc).
  unfold munmap_eff. rewrite H0, Hprr. exact Hc.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bn_mmap_rw_refused : forall ms model (len : Z) K,
  bm_on = true ->
  m_halted model = None ->
  cj_at_node segs (NMmap 0 len 3 34) ms -> 0 < len < 2 ^ 64 ->
  (vm_backing_used model + page_round_up_Z len <=? vm_limit (m_vmmaps model)) = false ->
  K [] ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros ms model len K Hon Hh (Hsvc & H10 & H11 & H12 & H13 & H14 & H15) Hlen Hfit HK.
  apply (srz_brefused segs scfg (mkCfg ms model) K Hon);
    [| exact (RomBase.sys_rob_memfree segs ms model _ Hsvc ltac:(rewrite u222; exact RomBase.memfree_222)) | exact HK].
  apply (budget_refused_at_of_mark ms model (Z_to_bv 64 222) Hh Hsvc).
  unfold alloc_budget_refused_b. cbn [in_sysno sys_input]. rewrite u222. cbn [Z.eqb Pos.eqb].
  unfold in_arg. cbn [in_args sys_input syscall_args nth].
  rewrite gpr_areg0, gpr_areg1, gpr_areg2, gpr_areg3, gpr_areg4, gpr_areg5, H10, H11, H12, H13, H14, H15.
  unfold mmap_budget_refused_b.
  replace (mmap_off_aligned_b (Z_to_bv 64 0)) with true by reflexivity.
  replace (mmap_anon_b (Z_to_bv 64 34)) with true by reflexivity.
  replace (w_is0 (Z_to_bv 64 len)) with false by (symmetry; unfold w_is0; apply bv_eqb_neq; apply (lit_ne0 len Hlen)).
  replace (mmap_modeled_b (Z_to_bv 64 3) (Z_to_bv 64 34) (Z_to_bv 64 0)) with true by reflexivity.
  cbn [negb]. unfold mmap_noreserve_backed_ok.
  replace (mmap_noreserve_b (Z_to_bv 64 34)) with false by reflexivity.
  rewrite (u64_lit len) by lia. rewrite Hfit. reflexivity.
Qed.

Lemma bn_mprotect_refused : forall ms model (addr len : Z) K,
  bm_on = true ->
  m_halted model = None ->
  cj_at_node segs (NMprotect addr len 3) ms ->
  addr mod page_size = 0 -> 0 < len -> 0 <= addr ->
  addr + page_round_up_Z len < two_pow_64 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  (* [mprotect_budget_refused_b] answers [false] on a range meeting the vdso/vvar pair
     (LPS 727298f3), before its ledger test, as for [bn_mprotect] *)
  region_free (vdso_reserved (m_kernel model) (vdso_top (m_vmmaps model))) (Z_to_bv 64 addr) n = true ->
  map_contains (vm_noaccess (m_vmmaps model)) (Z_to_bv 64 addr) n = true ->
  map_contains (vm_maps (m_vmmaps model)) (Z_to_bv 64 addr) n = true ->
  mprotect_budget_ok model (Z_to_bv 64 addr) n = false ->
  K [] ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros ms model addr len K Hon Hh (Hsvc & H10 & H11 & H12) Hal Hlen Ha0 Hnw n Hvd Hna Hma Hbud HK.
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as Hpr.
  assert (Haddr : bv_unsigned (Z_to_bv 64 addr) = addr) by (apply u64_lit; unfold two_pow_64 in Hnw; lia).
  assert (Hulen : bv_unsigned (Z_to_bv 64 len) = len) by (apply u64_lit; unfold two_pow_64 in Hnw; lia).
  apply (srz_brefused segs scfg (mkCfg ms model) K Hon);
    [| exact (RomBase.sys_rob_memfree segs ms model _ Hsvc ltac:(rewrite u226; exact RomBase.memfree_226)) | exact HK].
  apply (budget_refused_at_of_mark ms model (Z_to_bv 64 226) Hh Hsvc).
  unfold alloc_budget_refused_b. cbn [in_sysno sys_input]. rewrite u226. cbn [Z.eqb Pos.eqb].
  unfold in_arg. cbn [in_args sys_input syscall_args nth].
  rewrite gpr_areg0, gpr_areg1, gpr_areg2, H10, H11, H12.
  unfold mprotect_budget_refused_b.
  replace (mprotect_grows_conflict_b (Z_to_bv 64 3)) with false by reflexivity.
  rewrite Haddr, Hal. cbn [Z.eqb negb].
  replace (w_is0 (Z_to_bv 64 len)) with false by (symmetry; unfold w_is0; apply bv_eqb_neq; apply (lit_ne0 len ltac:(unfold two_pow_64 in Hnw; lia))).
  rewrite Hulen. replace (two_pow_64 <=? addr + page_round_up_Z len) with false by (symmetry; apply Z.leb_gt; lia).
  replace (mprotect_modeled_b (Z_to_bv 64 3)) with true by reflexivity.
  fold n. rewrite Hna, Hma. cbn [andb]. rewrite Hbud, Hvd. reflexivity.
Qed.

End WithSegs.
End BrNodes.
From Stdlib Require ZArith NArith List Lia Bool Permutation. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Specs Run. From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require PropExec. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require ITree Nodes Decode. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0004. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec Require Monad. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0029. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0046. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require RunP.
Module KLink.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require ITree Nodes Decode. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.MState OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.ITree OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Nodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Decode.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0004. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec Require Monad. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0029. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0046. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0004.Prelim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Monad OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0004.STree OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0029.Malloc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0046.Prog OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0046.KInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0046.KStep.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_KLink () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List7map_mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00I79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv6pwdisj00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic9False_indC79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv5edisjC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalK47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00C79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv3eloC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv3ehiC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib7Numbers7BinNums1Z00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01C47Corelib4Init9Datatypes3appK47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics?LinuxProcessSem5State:iv_overlapC47Corelib4Init9Datatypes4negbC4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeC47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib2CJ3Lib6Decode>region_free_InC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv4vmwfC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05c79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink@region_free_disjC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv6pwdisj02C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01I47Corelib4Init9Datatypes:comparison00K46Stdlib9micromega=RingMicromega3Op205C46Stdlib5Lists4List6filterC46Stdlib5Lists4List9filter_InK79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv6pwdisj01C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbC4ELinuxProcessSemantics?LinuxProcessSem5State:map_removeC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbc79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink=pwdisj_filterC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_app_orC4ELinuxProcessSemantics?LinuxProcessSem5State;iv_subtractC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3maxC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z8min_specC56Stdlib6ZArith6BinInt1Z3minK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr04C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState<unsigned_litC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula03I47Corelib7Numbers7BinNums1N00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega8ZifyInst7Inj_Z_ZK47Corelib4Init9Datatypes3nat01C4ELinuxProcessSemantics?LinuxProcessSem5State=maps_subtractI47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01C56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z6ltb_geC79OSSVerify5KrLib2CJ3Lib7Mh_00396MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z5min_lC56Stdlib6ZArith6BinInt1Z5max_lK47Corelib4Init9Datatypes4bool02C46Stdlib5Lists4List9in_or_appc79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLinkDiv_subtract_disjointC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink?iv_subtract_subC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLinkBiv_subtract_pwdisjC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink@maps_subtract_InC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink:pwdisj_appC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv4wcovC1?~~~~~~~~~~~~~~~i79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink3KL200C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink:phase_inv2C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv9set_brkphC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv7ld_resvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC56Stdlib6ZArith6BinInt1Z6moduloC4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib2CJ3Lib4RunP=alloc_ceilingC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv9ld_groupsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib6Decode8mmap_lenC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv4wentC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv8brk_disjC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv8ld_metasC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00I47Corelib4Init9Datatypes6option00C79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv9ld_brkregC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv6ld_brkC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spk79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink3KL201C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv4mled00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv9brk_phase00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv3wwZC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc4PGSZC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv7LEN_MAXC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink;KL2_rephaseC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv9brk_phase05C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv8set_liveC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc4cptrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00465KStep@alloc_ceiling_ltC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink9k2_groupsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indc79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink8k2_metasC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00465KStep;mmap_len_geC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00465KStep8elo_wentC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00465KStep8ehi_wentC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC46Stdlib5Lists4List:in_app_iffC79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv7lrangesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC46Stdlib5Lists4List:in_map_iffC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Program6Basics4implC47Corelib7Classes>Morphisms_Prop?or_iff_morphismC47Corelib7Classes?RelationClasses=iff_Reflexivec79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLinkAregion_free_app_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc;ranges_freeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC46Stdlib5Lists4List>forallb_forallC79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc;iv_disjointC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink:In_lrangesC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink7k2_resvC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink>went_In_boundsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC79OSSVerify5KrLib2CJ4Spec7Mh_00465KStep>round_up_pg_eqC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC69OSSVerify5KrLib2CJ3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00465KStepCround_up_pg_alignedC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init5Logic5proj2C46Stdlib4Bool4Bool:orb_true_rC79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv=lbrk_pages_okC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_le_gt_decC56Stdlib6ZArith6BinInt1Z2gtI47Corelib4Init6Specif7sumbool00K46Stdlib9micromega=RingMicromega3Op206C79OSSVerify5KrLib2CJ4Spec7Mh_00465KStep@mmap_len_alignedC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4ZdivAZ_div_mod_eq_fullC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05c79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink8k2_phaseC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc>brk0_answer_okC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv9brk_phase02C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink8k2_startC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z8eqb_reflK79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv9brk_phase01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv9brk_quietC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01c79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink?mmap_len_pos_pgC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink9k2_brkregC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink<wcov_rf_disjC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc>mmap_answer_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc6is_errC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv9brk_phase03C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv9set_metasC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink9vmwf_consC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink8ehi_pairC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink8elo_pairC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz05C46Stdlib7Sorting;PermutationBPermutation_middleK46Stdlib5Lists4List5NoDup02C46Stdlib7Sorting;PermutationAPermutation_NoDupc79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink9wcov_monoC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv:set_groupsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc=is_errno_formC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool>orb_true_introK79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv9brk_phase04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc2ev01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07C56Stdlib6ZArith6BinInt1Z7eqb_neqC79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv:set_brkregC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink8KL2_deadC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLinkAKL2_lbrk_pages_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv:event_postC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv9answer_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc=brk_answer_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_modC57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC46Stdlib6ZArith:ZArith_dec;Z_lt_le_decc79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink;k2_resv_topC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLinkAregion_free_aboveC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List>existsb_existsC57Corelib7BinNums6PosDef3Pos3mulC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z4landc79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLinkDiv_subtract_containsC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLinkFmaps_subtract_In_introC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296MallocDmmap_fixed_answer_okC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc2ev02C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<map_containsC79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc9PROT_NONEC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv5MAPFXC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv8g_removeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocC79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc@munmap_answer_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00465KStepCmmap_len_of_alignedC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink;k2_distinctC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink>g_remove_splitC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7map_appC46Stdlib5Lists4List>NoDup_remove_1C46Stdlib5Lists4List>NoDup_remove_2c79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink5k2_wfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink9pwdisj_InC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink<phase_quiet2C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv2wzC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00465KStep;unsigned_wzC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqc79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink;vmwf_removeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib5Lists4List@filter_length_leI47Corelib4Init5Peano2le00C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib7Mh_00948RefNodesHlive_bytes_map_remove_leC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:live_bytesK79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc2ev03C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7map_hasI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib5Lists4List6in_mapc79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink=nodup_map_injC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC47Corelib4Init5Logic8eq_transC79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv9bump_metaC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7map_extC79OSSVerify5KrLib2CJ4Spec7Mh_00296MallocBmprotect_answer_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mod_mulC46Stdlib5Lists4ListBNoDup_app_remove_lC56Stdlib6ZArith6BinInt1Z6eq_decc79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink=map_base_bumpC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc2ev04C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc7PROT_RWC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc5TWO64C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc6ENOSYSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ6Bridge7Mh_01085KLink6k2_ispC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizeC4ELinuxProcessSemantics?LinuxProcessSem5StateBstack_max_size_valC69OSSVerify5KrLib2CJ3Lib4RunPCalloc_ceiling_rangeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_lo".

Section CEIL_WRAP_1.
Context {RUNp : RunP}.

Lemma pwdisj_In : forall l e1 e2, pwdisj l -> In e1 l -> In e2 l -> e1 = e2 \/ edisj e1 e2.
Proof.
  induction l as [|e l IH]; intros e1 e2 Hp H1 H2; [destruct H1|].
  inversion Hp; subst. destruct H1 as [<-|H1], H2 as [<-|H2].
  - left; reflexivity.
  - right. apply H3. exact H2.
  - right. pose proof (H3 _ H1) as D. unfold edisj in *. lia.
  - apply IH; assumption.
Qed.

Lemma map_has_In : forall l (lo n : word), map_has l lo n = true -> In (lo, n) l.
Proof.
  intros l lo n H. unfold map_has in H. apply existsb_exists in H as (e & He & Heq).
  apply andb_prop in Heq as [H1 H2]. apply bv_eqb_eq in H1. apply bv_eqb_eq in H2.
  destruct e as [b s]. cbn [fst snd] in H1, H2. subst b. subst s. exact He.
Qed.

Lemma elo_pair : forall a n, elo (a, n) = bv_unsigned a. Proof. reflexivity. Qed.
Lemma ehi_pair : forall a n, ehi (a, n) = bv_unsigned a + bv_unsigned n. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma maps_subtract_vmwf : forall maps (aw nw : word),
  vmwf maps -> In (aw, nw) maps ->
  maps_subtract maps (bv_unsigned aw) (bv_unsigned aw + bv_unsigned nw) = map_remove maps aw.
Proof.
  intros maps aw nw Hwf Hin. pose proof (proj1 Hwf _ Hin) as Hw.
  rewrite elo_pair, ehi_pair in Hw.
  apply OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim.maps_subtract_exact.
  - lia.
  - intros b s He. pose proof (proj1 Hwf _ He) as H'. rewrite elo_pair, ehi_pair in H'. lia.
  - intros b s He Eb. subst b.
    destruct (pwdisj_In _ _ _ (proj2 Hwf) He Hin) as [E|D].
    + exact (f_equal snd E).
    + exfalso. pose proof (proj1 Hwf _ He) as H'. unfold edisj in D.
      rewrite !elo_pair, !ehi_pair in D. rewrite elo_pair, ehi_pair in H'. lia.
  - intros b s He Hne.
    destruct (pwdisj_In _ _ _ (proj2 Hwf) He Hin) as [E|D].
    + exfalso. apply Hne. exact (f_equal fst E).
    + unfold edisj in D. rewrite !elo_pair, !ehi_pair in D. lia.
Qed.

Lemma maps_subtract_has : forall maps (aw nw : word),
  vmwf maps -> map_has maps aw nw = true ->
  maps_subtract maps (bv_unsigned aw) (bv_unsigned aw + bv_unsigned nw) = map_remove maps aw.
Proof.
  intros maps aw nw Hwf H. apply maps_subtract_vmwf; [exact Hwf | apply map_has_In; exact H].
Qed.

Lemma region_free_app_r : forall l1 l2 a n, region_free (l1 ++ l2) a n = true -> region_free l2 a n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_KLink ()) ["CEIL_WRAP_1"] "p'0h01ah11Hh22l2h31nh42l1h52IHh62_Hh71eh81lh92szi001bi011pp;1p;2p;3p;4p;5p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?p4p710p9P0p1001fp4p710p9p1002^p4p710R0p1003;p4p710R1p8P0p1003Wp4p710R0p8p10045p4p7210R2P1p8P2P0p8p1004Rp4p73110P0p8g004nj12Tg005Sj1ATg0061j1<Tg006TR0j29Tg0074j1@Tg00Pmj31Tg008mj1;Tg009Mj36Tg00QJj4:Tg00Qjj44Tg00Rcj15Tg00SAj37Tg00T;j3?Tg00T^R2j2>Tg00H;j5=Tg009mj38Tg00OOR1f2R3f1R4f0R537g00OoR638p=0A8156p=3g00Kd#2#2#2#2#2#2#A#<R6/96R1#@R7P1f3R8=113?045A0834R9[^36^06^27R:X47%;1=113?045P5W1X36X06X27P0P6P6f5R0f4R;561=113?045P9[^36^06^27\:^87P5P6P6f6R9P0C:=61;=113?045P3P4f7R<P9C4#5R=A1108?734R>;?5%3=%3>'>P2P8P3f8R2P<C4#5#3A119;?083A00;8P5P0P;f:f9R;C4#5#3A11;<?090P;P2P<P9P5O4W1W6P4P5O2n2001000000120000000b1W1X36X06X27X5:X47X96X76P4P5O2n2001101010121100100X01P5D=W4o"). Qed.

Lemma region_free_app_l : forall l1 l2 a n, region_free (l1 ++ l2) a n = true -> region_free l1 a n = true.
Proof.
  induction l1 as [|[e sz] l1 IH]; intros l2 a n H; [reflexivity|]. cbn [region_free app] in H |- *.
  apply andb_prop in H as [H1 H]. rewrite H1. apply (IH l2). exact H.
Qed.

Lemma region_free_disj : forall maps a n e, region_free maps a n = true -> In e maps ->
  bv_unsigned a + bv_unsigned n <= elo e \/ ehi e <= bv_unsigned a.
Proof.
ltac2:(KReplay.run1 (kr_t_KLink ()) ["CEIL_WRAP_1"] "p'0h01Hh13Hinh21ah31eh42e0h54mapsh61nh72szi001bi011pp;1p;2p;3p;4p;7p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?p4p710p9P0p1001fp4p710p9p1002^p4p710R0p1003;p4p710R1p8P0p1003Wp4p710R0p8p10045p4p7210R2P1p8P2P0p8p1004Rp4p73110P0p8g004nj10Tg005Sj1ATg0061j1<Tg006TR0j2;Tg0074j1@Tg00SAj39Tg009mj38Tg008Vj36Tg00U9j21Tg00Ucj24Tg00FAj15Tg00EKj22Tg00G>j17Tg00Egj23Tg00QJj4:Tg00V@j7?Tg00WAj3=Tg00W^j3>Tg00Kd#0#0#0#0#0#0#AR2#<R1/;1R3#@P0P1P1g00OOR0f4R4f3R5f2R639g00OoR738f1R8f5R95631129R:1124'4%56'2%76/2:'3[[f0R:f7R4f6;99=807P1P1P6P8C:f8R7563f9P7P4P5P6P8P:F?1127R71124'4R4P1P1P5P6C:R69=11,12R5'2A>116,12,45/27'3e%56,24%76/27'3eW1W0X71X31P8P:O2n2001101000121100100X43X61X21W5o"). Qed.

Lemma vmwf_cons : forall maps a n, vmwf maps ->
  bv_unsigned a < bv_unsigned a + bv_unsigned n <= 2^64 ->
  region_free maps a n = true ->
  vmwf ((a, n) :: maps).
Proof.
  intros maps a n [Hb Hp] Hn Hrf. split.
  - intros e [<-|Hin]; [unfold elo, ehi; cbn; lia| apply Hb; exact Hin].
  - constructor; [|exact Hp]. intros e' Hin. pose proof (region_free_disj _ _ _ _ Hrf Hin). unfold edisj, elo, ehi in *. cbn. lia.
Qed.

Lemma pwdisj_filter : forall (f : word * word -> bool) l, pwdisj l -> pwdisj (List.filter f l).
Proof.
  induction l as [|e l IH]; intros Hp; [constructor|]. inversion Hp; subst. cbn. destruct (f e).
  - constructor; [|apply IH; assumption]. intros e' Hin. apply List.filter_In in Hin as [Hin _]. auto.
  - apply IH; assumption.
Qed.

Lemma vmwf_remove : forall maps a, vmwf maps -> vmwf (map_remove maps a).
Proof.
  intros maps a [Hb Hp]. unfold map_remove. split.
  - intros e Hin. apply List.filter_In in Hin as [Hin _]. auto.
  - apply pwdisj_filter. exact Hp.
Qed.

Lemma iv_subtract_sub : forall a sz lo hi e, 0 < bv_unsigned sz -> bv_unsigned a + bv_unsigned sz <= 2^64 ->
  In e (iv_subtract a sz lo hi) -> bv_unsigned a <= elo e /\ ehi e <= bv_unsigned a + bv_unsigned sz /\ elo e < ehi e.
Proof.
  intros a sz lo hi e Hsz Hwf Hin. unfold iv_subtract in Hin.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz).
  unfold bv_modulus in *.
  apply in_app_or in Hin as [Hin|Hin].
  - destruct (Z.ltb_spec (bv_unsigned a) (lo)); [|destruct Hin].
    destruct Hin as [<-|[]]. unfold elo, ehi. cbn. rewrite unsigned_lit by lia. lia.
  - destruct (Z.ltb_spec (hi) (bv_unsigned a + bv_unsigned sz)); [|destruct Hin].
    destruct Hin as [<-|[]]. unfold elo, ehi. cbn. rewrite !unsigned_lit by lia. lia.
Qed.

Lemma maps_subtract_In : forall maps lo hi e, In e (maps_subtract maps lo hi) ->
  exists e0, In e0 maps /\ In e (iv_subtract (fst e0) (snd e0) lo hi).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi e Hin; [destruct Hin|].
  cbn in Hin. apply in_app_or in Hin as [Hin|Hin].
  - exists (a, sz). split; [left; reflexivity| exact Hin].
  - destruct (IH _ _ _ Hin) as (e0 & H0 & H1). exists e0. split; [right; exact H0| exact H1].
Qed.

Lemma iv_subtract_disjoint : forall a sz lo hi,
  bv_unsigned a < bv_unsigned a + bv_unsigned sz <= 2^64 -> lo < hi ->
  (bv_unsigned a + bv_unsigned sz <= lo \/ hi <= bv_unsigned a) ->
  iv_subtract a sz lo hi = [(a, sz)].
Proof.
  intros a sz lo hi Hwf Hlh Hd. unfold iv_subtract.
  pose proof (bv_unsigned_in_range 64 a). unfold bv_modulus in *.
  destruct Hd as [Hd|Hd].
  - replace (bv_unsigned a <? lo) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (hi <? bv_unsigned a + bv_unsigned sz) with false by (symmetry; apply Z.ltb_ge; lia).
    cbn. rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - replace (bv_unsigned a <? lo) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (hi <? bv_unsigned a + bv_unsigned sz) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn. rewrite Z.max_l by lia. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma maps_subtract_keep : forall maps lo hi e, vmwf maps -> lo < hi ->
  In e maps -> (ehi e <= lo \/ hi <= elo e) -> In e (maps_subtract maps lo hi).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi e Hwf Hlh Hin Hd; [destruct Hin|].
  destruct Hwf as [Hb Hp]. cbn. apply in_or_app. destruct Hin as [<-|Hin].
  - left. rewrite iv_subtract_disjoint; [left; reflexivity| | exact Hlh|].
    + specialize (Hb (a, sz) (or_introl eq_refl)). unfold elo, ehi in Hb. cbn in Hb. lia.
    + unfold elo, ehi in Hd. cbn in Hd. lia.
  - right. apply IH; auto. split; [intros e' H'; apply Hb; right; exact H'| inversion Hp; assumption].
Qed.

Lemma iv_subtract_contains : forall a sz lo hi x y,
  lo < hi -> 0 <= lo -> bv_unsigned a + bv_unsigned sz <= 2^64 ->
  bv_unsigned a <= x -> x < y -> y <= bv_unsigned a + bv_unsigned sz ->
  (y <= lo \/ hi <= x) ->
  exists e, In e (iv_subtract a sz lo hi) /\ elo e <= x /\ y <= ehi e.
Proof.
  intros a sz lo hi x y Hlh Hlo Hwf Hax Hxy Hy Hd. unfold iv_subtract.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  destruct Hd as [Hd|Hd].
  - replace (bv_unsigned a <? lo) with true by (symmetry; apply Z.ltb_lt; lia).
    eexists. split; [apply in_or_app; left; left; reflexivity|]. unfold elo, ehi; cbn. rewrite unsigned_lit by lia. lia.
  - replace (hi <? bv_unsigned a + bv_unsigned sz) with true by (symmetry; apply Z.ltb_lt; lia).
    eexists. split; [apply in_or_app; right; left; reflexivity|]. unfold elo, ehi; cbn. rewrite !unsigned_lit by lia. lia.
Qed.

Lemma maps_subtract_In_intro : forall maps lo hi e e', In e maps -> In e' (iv_subtract (fst e) (snd e) lo hi) ->
  In e' (maps_subtract maps lo hi).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi e e' Hin H'; [destruct Hin|].
  cbn. apply in_or_app. destruct Hin as [<-|Hin]; [left; exact H'| right; eapply IH; eauto].
Qed.

Lemma pwdisj_app : forall P R, pwdisj P -> pwdisj R -> (forall p r, In p P -> In r R -> edisj p r) -> pwdisj (P ++ R).
Proof.
  induction P as [|p P IH]; intros R HP HR Hx; [exact HR|]. inversion HP; subst. cbn. constructor.
  - intros e' He'. apply in_app_or in He' as [He'|He']; [auto|]. apply Hx; [left; reflexivity| exact He'].
  - apply IH; auto. intros p' r Hp' Hr. apply Hx; [right; exact Hp'| exact Hr].
Qed.

Lemma iv_subtract_pwdisj : forall a sz lo hi, lo < hi -> 0 <= lo -> bv_unsigned a + bv_unsigned sz <= 2^64 -> pwdisj (iv_subtract a sz lo hi).
Proof.
  intros a sz lo hi Hlh Hlo Hwf. unfold iv_subtract.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  destruct (Z.ltb_spec (bv_unsigned a) (lo)); destruct (Z.ltb_spec (hi) (bv_unsigned a + bv_unsigned sz)); cbn [app].
  - constructor; [|constructor; [intros e' []| constructor]]. intros e' [<-|[]].
    unfold edisj, elo, ehi; cbn. rewrite !unsigned_lit by lia. left. lia.
  - constructor; [intros e' []| constructor].
  - constructor; [intros e' []| constructor].
  - constructor.
Qed.

Lemma vmwf_subtract : forall maps lo hi, lo < hi -> 0 <= lo -> vmwf maps -> vmwf (maps_subtract maps lo hi).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi Hlh Hlo [Hb Hp]; [split; [intros e []| constructor]|].
  inversion Hp; subst. assert (Hwf' : vmwf maps) by (split; [intros e He; apply Hb; right; exact He| assumption]).
  specialize (IH lo hi Hlh Hlo Hwf'). destruct IH as [IHb IHp].
  assert (Ha : elo (a, sz) < ehi (a, sz) <= 2^64) by (apply Hb; left; reflexivity). unfold elo, ehi in Ha; cbn in Ha.
  cbn. split.
  - intros e Hin. apply in_app_or in Hin as [Hin|Hin]; [|apply IHb; exact Hin].
    pose proof (iv_subtract_sub a sz lo hi e ltac:(lia) ltac:(lia) Hin). lia.
  - apply pwdisj_app; [apply iv_subtract_pwdisj; [exact Hlh| exact Hlo| lia]| exact IHp|].
    intros e e' He He'. pose proof (iv_subtract_sub a sz lo hi e ltac:(lia) ltac:(lia) He) as S1.
    destruct (maps_subtract_In _ _ _ _ He') as (e0 & H0 & H0').
    assert (W0 : elo e0 < ehi e0 <= 2^64) by (apply Hb; right; exact H0). destruct e0 as [a0 s0]. unfold elo, ehi in W0; cbn in W0.
    pose proof (iv_subtract_sub a0 s0 lo hi e' ltac:(lia) ltac:(lia) H0') as S2.
    pose proof (H1 _ H0) as D. unfold edisj, elo, ehi in *. cbn in *. lia.
Qed.

Lemma wcov_mono : forall maps maps' lo hi, (forall e, In e maps -> In e maps') -> wcov maps lo hi -> wcov maps' lo hi.
Proof.
ltac2:(KReplay.run1 (kr_t_KLink ()) ["CEIL_WRAP_1"] "p'0h01eh11Hh22Hch32Heh42Hrh52Hsh62Hxh72hih82loh94mapsh:5maps'h;1xi001xp;1p;2p;3p;4p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?p4p710p9P0p1001fp4p710p9p1002^p4p710R0p1003;p4p710R1p8P0p1003Wp4p710R0p8p10045p4p7210R2P1p8P2P0p8p1004Rp4p73110P0p8g004nj13Tg005Sj1?Tg0061j19Tg006Tj28Tg0074j1>Tg008Vj30Tg01IBj37Tg00FAj15Tg00G>j14Tg00T^R0j22Tg01=hR2j26Tg00`Yj4:Tg01>Bj4=Tg00EKj2<Tg00Z\j2;Tf3R1f2R3'<f1R4f0R5';'2p=1g00Kd#3#3#3#3#3#3#?#9R6/86R6#>R7g00M^R8f4R99065A0649[^06A7934P9P5P5P1C1P3P4P5O2f8R:9065%55R;P3P3%45R<C1'2X06,66P2P6f9R29065R=P;P1P1P<C1'2X06P;P9P9P<C1,2=X06,66P5f;R=9065P;f5R>P>P<C1'2P0f<R09064%54f6R?P?%44C1f=9065P;P:P:P<C1'2X06,66P5f>9061%59P2P2%49C1P6f@9065P;P=P=P<C1'2X06P>f?906>%5>f:R<P<%4>C1P0P>P4O2P5C:C=W4W3P4P5O2n2001000000120000000W1X06P4P5O2n2001000000121100000b0W6X;8A7913eW2W5X78W8X:7W9o"). Qed.

Section KL2DEF.
Variable resv_img : list (word * word).
Variable img_hi : Z.

Record KL2 (L : mled) (pbrk : Z) (h : VmMaps) : Prop := mkKL2 {
  k2_wf : vmwf (vm_maps h);
  k2_nabnd : forall e, In e (vm_noaccess h) -> elo e < ehi e <= 2^64;
  (* [comment removed for export] *)
  k2_resv : ld_resv L = map wwZ resv_img;
  k2_resv_img : exists rx, vm_reserved h = resv_img ++ rx;
  k2_resv_top : forall e, In e (vm_reserved h) ->
      ehi e <= bv_unsigned (vm_start_brk h) \/ bv_unsigned (vm_start_brk h) + 4 * PGSZ <= elo e;
  k2_start : 0 < bv_unsigned (vm_start_brk h)
      /\ bv_unsigned (vm_start_brk h) mod PGSZ = 0
      /\ bv_unsigned (vm_start_brk h) <= bv_unsigned (vm_brk h)
      /\ bv_unsigned (vm_start_brk h) + 4 * PGSZ <= alloc_ceiling
      /\ img_hi <= bv_unsigned (vm_start_brk h);
  k2_groups : forall b l, In (b, l) (ld_groups L) ->
      0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= alloc_ceiling
      /\ In (went b (mmap_len l)) (vm_maps h) /\ brk_disj L b (mmap_len l);
  k2_metas : forall b l k, In (b, l, k) (ld_metas L) ->
      0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= alloc_ceiling
      /\ 0 <= k /\ (1 + k) * PGSZ <= mmap_len l
      /\ In (went b (mmap_len l)) (vm_maps h) /\ brk_disj L b (mmap_len l)
      /\ (forall q, 1 + k <= q -> (q + 1) * PGSZ <= mmap_len l ->
            exists e, In e (vm_noaccess h) /\ elo e <= b + q * PGSZ /\ b + q * PGSZ + PGSZ <= ehi e);
  k2_distinct : List.NoDup (map fst (ld_groups L) ++ map (fun m => fst (fst m)) (ld_metas L));
  k2_brkreg : forall b l, ld_brkreg L = Some (b, l) ->
      0 < b /\ b mod PGSZ = 0 /\ 2 * PGSZ <= l /\ l mod PGSZ = 0 /\ b + l <= alloc_ceiling
      /\ wcov (vm_maps h) (b + PGSZ) (b + l);
  k2_phase : match ld_brk L with
      | BPUntried => vm_brk h = vm_start_brk h /\ ld_brkreg L = None
      | BPQueried cur => cur = bv_unsigned (vm_start_brk h)
          /\ bv_unsigned (vm_brk h) = cur /\ pbrk = cur /\ ld_brkreg L = None
      | BPGuard cur => cur = bv_unsigned (vm_start_brk h)
          /\ bv_unsigned (vm_brk h) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
          /\ ld_brkreg L = None /\ cur + 2 * PGSZ <= alloc_ceiling
          /\ (exists e, In e (vm_maps h) /\ elo e <= cur /\ cur + 2 * PGSZ <= ehi e)
          /\ (forall b l, In (b, l) (ld_groups L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
          /\ (forall b l k, In (b, l, k) (ld_metas L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
      | BPLive => exists b l, ld_brkreg L = Some (b, l) /\ bv_unsigned (vm_brk h) = b + l /\ pbrk = b + l
      | BPDead => True
      end;

  k2_isp : bv_unsigned (vm_init_sp h) = alloc_ceiling + 2 ^ 23;
  (* [comment removed for export] *)
  k2_mres : forall e, In e (vm_maps h) -> region_free (vm_reserved h) (fst e) (snd e) = true }.

Ltac k2_open HK := destruct HK as [Kwf Kna Kresv Kimg Krt Kstart Kgr Kme Kdis Kreg Kph Kisp Kmres].

Lemma k2_img_in : forall L pbrk h e, KL2 L pbrk h -> In e resv_img -> In e (vm_reserved h).
Proof.
  intros L pbrk h e HK He. destruct (k2_resv_img _ _ _ HK) as [rx E]. rewrite E. apply in_or_app. left. exact He.
Qed.

Definition phase_inv2 (ph : brk_phase) (L : mled) (pbrk : Z) (h : VmMaps) : Prop :=
  match ph with
  | BPUntried => vm_brk h = vm_start_brk h /\ ld_brkreg L = None
  | BPQueried cur => cur = bv_unsigned (vm_start_brk h)
      /\ bv_unsigned (vm_brk h) = cur /\ pbrk = cur /\ ld_brkreg L = None
  | BPGuard cur => cur = bv_unsigned (vm_start_brk h)
      /\ bv_unsigned (vm_brk h) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
      /\ ld_brkreg L = None /\ cur + 2 * PGSZ <= alloc_ceiling
      /\ (exists e, In e (vm_maps h) /\ elo e <= cur /\ cur + 2 * PGSZ <= ehi e)
      /\ (forall b l, In (b, l) (ld_groups L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
      /\ (forall b l k, In (b, l, k) (ld_metas L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
  | BPLive => exists b l, ld_brkreg L = Some (b, l) /\ bv_unsigned (vm_brk h) = b + l /\ pbrk = b + l
  | BPDead => True
  end.

Lemma KL2_rephase : forall L ph pbrk pbrk' h,
  KL2 L pbrk h -> phase_inv2 ph L pbrk' h -> KL2 (set_brkph ph L) pbrk' h.
Proof. intros L ph pbrk pbrk' h K Hph. k2_open K; constructor; cbn; auto. Qed.

Lemma KL2_dead : forall L pbrk pbrk' h, KL2 L pbrk h -> KL2 (set_brkph BPDead L) pbrk' h.
Proof. intros. eapply KL2_rephase; [eassumption| exact I]. Qed.

Lemma KL2_set_live : forall L v pbrk h, KL2 L pbrk h -> KL2 (set_live v L) pbrk h.
Proof. intros L v pbrk h K. k2_open K; constructor; cbn; auto. Qed.

Lemma went_In_bounds : forall L pbrk h b l, KL2 L pbrk h ->
  (In (b, l) (ld_groups L) \/ exists k, In (b, l, k) (ld_metas L)) ->
  0 < b /\ 0 < mmap_len l /\ b + mmap_len l <= alloc_ceiling /\ In (went b (mmap_len l)) (vm_maps h)
  /\ elo (went b (mmap_len l)) = b /\ ehi (went b (mmap_len l)) = b + mmap_len l.
Proof.
  intros L pbrk h b l K Hin. pose proof alloc_ceiling_lt.
  assert (0 < l < LEN_MAX /\ 0 < b /\ b + mmap_len l <= alloc_ceiling /\ In (went b (mmap_len l)) (vm_maps h)) as (Hl & Hb & Hc & Hm).
  { destruct Hin as [Hin|[k Hin]]; [pose proof (k2_groups _ _ _ K _ _ Hin)| pose proof (k2_metas _ _ _ K _ _ _ Hin)]; tauto. }
  pose proof (mmap_len_ge l ltac:(lia)). splits; auto; try lia.
  - apply elo_went. lia.
  - apply ehi_went; lia.
Qed.

Lemma In_lranges : forall L x, In x (lranges L) ->
  In x (ld_resv L)
  \/ (exists b l, In (b, l) (ld_groups L) /\ x = (b, round_up_pg l))
  \/ (exists b l k, In (b, l, k) (ld_metas L) /\ x = (b, round_up_pg l))
  \/ (exists b l, ld_brkreg L = Some (b, l) /\ x = (b + PGSZ, round_up_pg l - PGSZ)).
Proof.
  intros L x Hin. unfold lranges in Hin. rewrite !in_app_iff in Hin. destruct Hin as [H|[H|[H|H]]].
  - left; exact H.
  - right; left. apply in_map_iff in H as ([b l] & <- & H). exists b, l. auto.
  - right; right; left. apply in_map_iff in H as ([[b l] k] & <- & H). exists b, l, k. auto.
  - right; right; right. destruct (ld_brkreg L) as [[b l]|]; [|destruct H]. destruct H as [<-|[]]. exists b, l. auto.
Qed.

Lemma KL2_lbrk_pages_ok : forall L pbrk h lo len,
  KL2 L pbrk h ->
  0 < lo -> 0 < len -> lo + len <= alloc_ceiling ->
  region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 lo) (Z_to_bv 64 len) = true ->
  (forall b l, ld_brkreg L = Some (b, l) -> l mod PGSZ = 0 /\ (b + l <= lo \/ lo + len <= b + PGSZ)) ->
  lbrk_pages_ok L lo len = true.
Proof.
  intros L pbrk h lo len HK Hlo Hlen Hceil Hrf Hbrk. pose proof alloc_ceiling_lt as Hcl.
  assert (Ulo : bv_unsigned (Z_to_bv 64 lo) = lo) by (apply unsigned_lit; lia).
  assert (Ulen : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
  unfold lbrk_pages_ok. rewrite (proj2 (Z.ltb_lt 0 lo)) by lia. rewrite (proj2 (Z.leb_le _ _) Hceil). cbn [andb].
  unfold ranges_free. apply forallb_forall. intros [b0 m0] Hin. cbn [fst snd]. unfold iv_disjoint.
  enough (lo + len <= b0 \/ b0 + m0 <= lo) as D.
  { destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r]. }
  apply In_lranges in Hin as [H|[(b1 & l1 & H & E)|[(b1 & l1 & k & H & E)|(b1 & l1 & H & E)]]].
  - rewrite (k2_resv _ _ _ HK) in H. apply in_map_iff in H as ([e sz] & E & H). unfold wwZ in E. cbn [fst snd] in E. injection E as <- <-.
    pose proof (region_free_In _ _ _ _ _ Hrf (in_or_app _ _ _ (or_introl (k2_img_in _ _ _ _ HK H)))) as D. rewrite Ulo, Ulen in D. exact D.
  - injection E as -> ->. pose proof (went_In_bounds _ _ _ b1 l1 HK (or_introl H)) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ulo, Ulen in D. rewrite round_up_pg_eq. fold (mmap_len l1). exact D.
  - injection E as -> ->. pose proof (went_In_bounds _ _ _ b1 l1 HK (or_intror (ex_intro _ k H))) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ulo, Ulen in D. rewrite round_up_pg_eq. fold (mmap_len l1). exact D.
  - injection E as -> ->. destruct (Hbrk b1 l1 H) as [Al D]. rewrite round_up_pg_aligned by (unfold PGSZ in Al; exact Al). lia.
Qed.

Lemma wcov_rf_disj : forall maps lo hi aw nw,
  wcov maps lo hi -> region_free maps aw nw = true -> 0 < bv_unsigned nw -> lo < hi ->
  bv_unsigned aw + bv_unsigned nw <= lo \/ hi <= bv_unsigned aw.
Proof.
  intros maps lo hi aw nw Hc Hrf Hn Hlh.
  destruct (Z_le_gt_dec (bv_unsigned aw + bv_unsigned nw) lo) as [|H1]; [left; assumption|].
  destruct (Z_le_gt_dec hi (bv_unsigned aw)) as [|H2]; [right; assumption|]. exfalso.
  destruct (Hc (Z.max (bv_unsigned aw) lo) ltac:(lia)) as (e & He & Hr).
  pose proof (region_free_disj _ _ _ _ Hrf He). lia.
Qed.

Lemma mmap_len_pos_pg : forall l, 0 < l -> PGSZ <= mmap_len l.
Proof.
  intros l Hl. pose proof (mmap_len_ge l Hl). pose proof (mmap_len_aligned l).
  pose proof (Z_div_mod_eq_full (mmap_len l) 4096). unfold PGSZ. nia.
Qed.

Lemma KL2_brk0 : forall L pbrk h, KL2 L pbrk h -> ld_brk L = BPUntried ->
  let r := bv_unsigned (vm_brk h) in
  brk0_answer_ok r = true /\ KL2 (set_brkph (BPQueried r) L) r h.
Proof.
  intros L pbrk h HK Hph r.
  pose proof (k2_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as [Ebrk Ereg].
  pose proof (k2_start _ _ _ HK) as (S1 & S2 & S3 & S4 & S5).
  pose proof (bv_unsigned_in_range 64 (vm_brk h)) as R. unfold bv_modulus in R.
  subst r. rewrite Ebrk in *. split.
  - unfold brk0_answer_ok, TWO64. rewrite (proj2 (Z.ltb_lt 0 _)) by lia. rewrite S2, Z.eqb_refl.
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
  - eapply KL2_rephase; [exact HK|]. cbn [phase_inv2]. rewrite Ebrk. splits; auto.
Qed.

Lemma KL2_mmap_new : forall L pbrk h (a : word) len (isnone : bool),
  KL2 L pbrk h -> brk_quiet L -> 0 < len < LEN_MAX ->
  let n := mmap_len len in
  bv_unsigned a mod PGSZ = 0 -> 0 < bv_unsigned a -> bv_unsigned a + n <= alloc_ceiling ->
  region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 n) = true ->
  let h' := mkVmMapsFull (vm_reserved h) ((a, Z_to_bv 64 n) :: vm_maps h)
                 (if isnone then (a, Z_to_bv 64 n) :: vm_noaccess h else vm_noaccess h)
                 (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) in
  KL2 (if isnone then set_metas ((bv_unsigned a, len, 0) :: ld_metas L) L else set_groups ((bv_unsigned a, len) :: ld_groups L) L) pbrk h'
  /\ mmap_answer_ok (lranges L) len (bv_unsigned a) = true /\ is_err (bv_unsigned a) = false.
Proof.
  intros L pbrk h aw len isnone HK Hq Hlen n A1 A2 A3 Hrf h'. pose proof alloc_ceiling_lt as Hcl.
  set (a := bv_unsigned aw) in *.
  pose proof (mmap_len_ge len ltac:(lia)) as Hn1. pose proof (mmap_len_pos_pg len ltac:(lia)) as Hn2. fold n in Hn1, Hn2.
  assert (Ua : aw = Z_to_bv 64 a) by (subst a; symmetry; apply Z_to_bv_bv_unsigned).
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
  pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
  assert (Hround : round_up_pg len = n) by (subst n; apply round_up_pg_eq).
  assert (Dgm : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k, In (b0, l0, k) (ld_metas L)) ->
                 a + n <= b0 \/ b0 + mmap_len l0 <= a).
  { intros b0 l0 H. pose proof (WB b0 l0 H) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Un in D. exact D. }
  assert (Dbrk : forall b0 l0, ld_brkreg L = Some (b0, l0) -> a + n <= b0 + PGSZ \/ b0 + l0 <= a).
  { intros b0 l0 E. pose proof (k2_brkreg _ _ _ HK b0 l0 E) as (R1 & R2 & R3 & R4 & R5 & Rcov).
    pose proof (wcov_rf_disj _ _ _ _ _ Rcov Hrfm ltac:(rewrite Un; lia) ltac:(clear -R3; unfold PGSZ in *; lia)) as D. rewrite Un in D. exact D. }
  split; [|split].
  2:{ unfold mmap_answer_ok. apply orb_true_intro. right. rewrite Hround.
      rewrite (proj2 (Z.ltb_lt 0 a)) by lia. unfold PGSZ at 1. unfold PGSZ in A1. rewrite A1, Z.eqb_refl. rewrite (proj2 (Z.leb_le _ _) A3). cbn [andb].
      unfold ranges_free. apply forallb_forall. intros [lo m] Hin. cbn [fst snd]. unfold iv_disjoint.
      enough (a + n <= lo \/ lo + m <= a) as D.
      { destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r]. }
      apply In_lranges in Hin as [H|[(b0 & l0 & H & E)|[(b0 & l0 & k & H & E)|(b0 & l0 & H & E)]]].
      - rewrite (k2_resv _ _ _ HK) in H. apply in_map_iff in H as ([e sz] & E & H). unfold wwZ in E. cbn [fst snd] in E. injection E as <- <-.
        pose proof (region_free_In _ _ _ _ _ Hrf (in_or_app _ _ _ (or_introl (k2_img_in _ _ _ _ HK H)))) as D. rewrite Un in D. exact D.
      - injection E as -> ->. rewrite round_up_pg_eq. fold (mmap_len l0). apply Dgm. left; exact H.
      - injection E as -> ->. rewrite round_up_pg_eq. fold (mmap_len l0). apply Dgm. right; exists k; exact H.
      - injection E as -> ->. pose proof (k2_brkreg _ _ _ HK b0 l0 H) as (R1 & R2 & R3 & R4 & R5 & _).
        rewrite round_up_pg_aligned by (unfold PGSZ in R4; exact R4). pose proof (Dbrk b0 l0 H). lia. }
  2:{ unfold is_err, TWO64. apply Z.ltb_ge. lia. }
  assert (Hnotin : ~ In a (map fst (ld_groups L) ++ map (fun m => fst (fst m)) (ld_metas L))).
  { intros Hin. apply in_app_or in Hin as [Hin|Hin].
    - apply in_map_iff in Hin as ([b0 l0] & E & Hin). cbn in E. subst b0.
      pose proof (WB a l0 (or_introl Hin)) as (B1 & B2 & _). pose proof (Dgm a l0 (or_introl Hin)). lia.
    - apply in_map_iff in Hin as ([[b0 l0] k] & E & Hin). cbn in E. subst b0.
      pose proof (WB a l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & _). pose proof (Dgm a l0 (or_intror (ex_intro _ k Hin))). lia. }
  k2_open HK.
  assert (Kmres' : forall e, In e ((aw, Z_to_bv 64 n) :: vm_maps h) -> region_free (vm_reserved h) (fst e) (snd e) = true).
  { intros e [<-|He]; [exact (region_free_app_l _ _ _ _ Hrf)| exact (Kmres e He)]. }
  assert (Hph' : forall L', ld_brk L' = ld_brk L -> ld_brkreg L' = ld_brkreg L ->
            phase_inv2 (ld_brk L') L' pbrk h').
  { intros L' E1 E2. unfold phase_inv2. rewrite E1, E2. subst h'. cbn [vm_brk vm_start_brk]. unfold brk_quiet in Hq.
    destruct (ld_brk L); try contradiction; auto. }
  destruct isnone; constructor;
    first [ exact Kmres'
          | apply (Hph' (set_metas _ L)); reflexivity
          | apply (Hph' (set_groups _ L)); reflexivity
          | subst h'; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp set_metas set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto ].
  - apply vmwf_cons; [exact Kwf| rewrite Un; lia| exact Hrfm].
  - intros e [<-|He]; [rewrite elo_pair, ehi_pair, Un; subst a; lia| apply Kna; exact He].
  - intros b0 l0 Hin. specialize (Kgr b0 l0 Hin). unfold brk_disj in *; cbn. intuition auto with datatypes.
  - intros b0 l0 k [E|Hin].
    + injection E as <- <- <-. unfold brk_disj; cbn. splits; try lia.
      * left; unfold went, OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0046.KInv.wz; rewrite <- Ua; reflexivity.
      * exact Dbrk.
      * intros q Hq1 Hq2. exists (aw, Z_to_bv 64 n). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Un. fold n in Hq2. subst a.
        unfold PGSZ in Hq2 |- *. lia.
    + specialize (Kme b0 l0 k Hin). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). unfold brk_disj in *; cbn. splits; try assumption; try (right; assumption).
      intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hr). exists e. split; [right; exact He| exact Hr].
  - cbn [map fst app]. eapply Permutation_NoDup; [apply Permutation_middle|]. constructor; [exact Hnotin| exact Kdis].
  - intros b0 l0 E. specialize (Kreg b0 l0 E). destruct Kreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto. eapply wcov_mono; [|exact Rcov]. intros e He; right; exact He.
  - apply vmwf_cons; [exact Kwf| rewrite Un; lia| exact Hrfm].
  - intros b0 l0 [E|Hin].
    + injection E as <- <-. unfold brk_disj; cbn. splits; try lia.
      * left; unfold went, OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0046.KInv.wz; rewrite <- Ua; reflexivity.
      * exact Dbrk.
    + specialize (Kgr b0 l0 Hin). unfold brk_disj in *; cbn. intuition auto with datatypes.
  - intros b0 l0 k Hin. specialize (Kme b0 l0 k Hin). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). unfold brk_disj in *; cbn. splits; try assumption; try (right; assumption).
  - cbn [map fst app]. constructor; [exact Hnotin| exact Kdis].
  - intros b0 l0 E. specialize (Kreg b0 l0 E). destruct Kreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto. eapply wcov_mono; [|exact Rcov]. intros e He; right; exact He.
Qed.

Lemma KL2_brk_grow1 : forall L pbrk h cur, KL2 L pbrk h -> ld_brk L = BPQueried cur ->
  let b := vm_brk h in
  let req := round_up_pg cur + 2 * PGSZ in

  cur = bv_unsigned b /\ pbrk = cur /\ req = bv_unsigned b + 2 * PGSZ /\ bv_unsigned b mod PGSZ = 0 /\ 0 < bv_unsigned b
  /\ bv_unsigned b + 2 * PGSZ < 2 ^ 64 /\ bv_unsigned (vm_start_brk h) <= bv_unsigned b + 2 * PGSZ /\ req <> 0

  /\ (answer_ok L (EBrk req) cur = true /\ KL2 (event_post L (EBrk req) cur) cur h)

  /\ (region_free (vm_reserved h ++ vm_maps h) b (Z_to_bv 64 (2 * PGSZ)) = true -> bv_unsigned b + 2 * PGSZ <= alloc_ceiling ->
      answer_ok L (EBrk req) req = true
      /\ KL2 (event_post L (EBrk req) req) req
             (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 (2 * PGSZ)) :: vm_maps h) (vm_noaccess h) (vm_start_brk h)
                           (Z_to_bv 64 (bv_unsigned b + 2 * PGSZ)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h))).
Proof.
  intros L pbrk h cur HK Hph b req. pose proof alloc_ceiling_lt as Hcl.
  pose proof (k2_phase _ _ _ HK) as Kph0. rewrite Hph in Kph0. destruct Kph0 as (Ecur & Ebrk & Epbrk & Ereg).
  pose proof (k2_start _ _ _ HK) as (S1 & S2 & S3 & S4 & S5).
  pose proof (bv_unsigned_in_range 64 b) as Rb. unfold bv_modulus in Rb.
  assert (Hcb : cur = bv_unsigned b) by (subst b; lia).
  assert (Hreq : req = cur + 2 * PGSZ). { subst req. rewrite round_up_pg_aligned; [reflexivity|]. rewrite Ecur. exact S2. }
  assert (Hne : req <> 0) by (unfold PGSZ in *; lia).
  assert (Hb2 : bv_unsigned b + 2 * PGSZ < 2 ^ 64) by (rewrite <- Hcb, Ecur; unfold PGSZ in *; lia).
  assert (Hsb : bv_unsigned (vm_start_brk h) <= bv_unsigned b + 2 * PGSZ) by (rewrite <- Hcb, Ecur; unfold PGSZ; lia).
  splits; try lia.
  - rewrite <- Hcb, Ecur. exact S2.
  -
    unfold answer_ok, event_post. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). rewrite Hph.
    replace (cur =? req) with false by (symmetry; apply Z.eqb_neq; lia).
    unfold brk_answer_ok. rewrite Z.eqb_refl, orb_true_r. reflexivity.
  - unfold event_post. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). rewrite Hph.
    replace (cur =? req) with false by (symmetry; apply Z.eqb_neq; lia).
    apply KL2_dead with (pbrk := pbrk). exact HK.
  -
    intros Hrf Hceil.
    assert (Hn : bv_unsigned (Z_to_bv 64 (2 * PGSZ)) = 2 * PGSZ) by (apply unsigned_lit; unfold PGSZ; lia).
    assert (HPG : lbrk_pages_ok L (round_up_pg cur) (2 * PGSZ) = true).
    { rewrite round_up_pg_aligned by (rewrite Ecur; unfold PGSZ in S2; exact S2).
      apply (KL2_lbrk_pages_ok L pbrk h cur (2 * PGSZ) HK); [lia| unfold PGSZ; lia| lia| | intros b1 l1 Hb; rewrite Ereg in Hb; discriminate].
      rewrite Hcb, Z_to_bv_bv_unsigned. exact Hrf. }
    split.
    + unfold answer_ok. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). rewrite Hph.
      unfold brk_answer_ok. rewrite Z.eqb_refl, HPG. reflexivity.
    + unfold event_post. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). rewrite Z.eqb_refl, Hph.
      pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
      assert (Kmres' : forall e, In e ((b, Z_to_bv 64 (2 * PGSZ)) :: vm_maps h) -> region_free (vm_reserved h) (fst e) (snd e) = true).
      { pose proof (k2_mres _ _ _ HK) as Kmres. intros e [<-|He]; [exact (region_free_app_l _ _ _ _ Hrf)| exact (Kmres e He)]. }
      k2_open HK. constructor; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp set_brkph ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; first [exact Kmres' | auto].
      * apply vmwf_cons; [exact Kwf| rewrite Hn; unfold PGSZ in *; lia| eapply region_free_app_r; exact Hrf].
      * rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; try lia; auto.
      * intros b0 l0 Hin. specialize (Kgr b0 l0 Hin). unfold brk_disj in *. cbn. intuition auto with datatypes.
      * intros b0 l0 k Hin. specialize (Kme b0 l0 k Hin). unfold brk_disj in *. cbn. intuition auto with datatypes.
      * intros b0 l0 Hb. rewrite Ereg in Hb. discriminate.
      * rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; auto; try lia.
        -- exists (b, Z_to_bv 64 (2 * PGSZ)). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Hn. lia.
        -- intros b0 l0 Hin. pose proof (WB b0 l0 (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6).
           pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D. lia.
        -- intros b0 l0 k Hin. pose proof (WB b0 l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6).
           pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D. lia.
Qed.

Lemma KL2_brk_grow2 : forall L pbrk h b l, KL2 L pbrk h -> ld_brk L = BPLive -> ld_brkreg L = Some (b, l) ->
  let br := vm_brk h in
  let req := b + l + PGSZ in
  pbrk = b + l /\ bv_unsigned br = b + l /\ req = bv_unsigned br + PGSZ /\ bv_unsigned br mod PGSZ = 0 /\ 0 < bv_unsigned br
  /\ bv_unsigned br + PGSZ < 2 ^ 64 /\ bv_unsigned (vm_start_brk h) <= bv_unsigned br + PGSZ /\ req <> 0
  /\ (answer_ok L (EBrk req) (b + l) = true /\ KL2 (event_post L (EBrk req) (b + l)) (b + l) h)
  /\ (region_free (vm_reserved h ++ vm_maps h) br (Z_to_bv 64 PGSZ) = true -> bv_unsigned br + PGSZ <= alloc_ceiling ->
      answer_ok L (EBrk req) req = true
      /\ KL2 (event_post L (EBrk req) req) req
             (mkVmMapsFull (vm_reserved h) ((br, Z_to_bv 64 PGSZ) :: vm_maps h) (vm_noaccess h) (vm_start_brk h)
                           (Z_to_bv 64 (bv_unsigned br + PGSZ)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h))).
Proof.
  intros L pbrk h b l HK Hph Ereg br req. pose proof alloc_ceiling_lt as Hcl.
  pose proof (k2_phase _ _ _ HK) as Kph0. rewrite Hph in Kph0. destruct Kph0 as (b' & l' & Ereg' & Ebrk & Epbrk).
  rewrite Ereg in Ereg'. injection Ereg' as <- <-.
  pose proof (k2_brkreg _ _ _ HK b l Ereg) as (R1 & R2 & R3 & R4 & R5 & Rcov).
  pose proof (k2_start _ _ _ HK) as (S1 & S2 & S3 & S4 & S5).
  pose proof (bv_unsigned_in_range 64 br) as Rb. unfold bv_modulus in Rb.
  assert (Hne : req <> 0) by (unfold req, PGSZ in *; lia).
  assert (Hal : bv_unsigned br mod PGSZ = 0).
  { subst br. rewrite Ebrk. unfold PGSZ in *. rewrite Z.add_mod, R2, R4 by lia. reflexivity. }
  splits; try (subst br req; unfold PGSZ in *; lia).
  - unfold answer_ok. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). rewrite Hph, Ereg.
    replace (b + l =? req) with false by (symmetry; apply Z.eqb_neq; unfold req, PGSZ; lia).
    unfold brk_answer_ok. rewrite Z.eqb_refl, orb_true_r. reflexivity.
  - unfold event_post. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). rewrite Hph, Ereg.
    replace (b + l =? req) with false by (symmetry; apply Z.eqb_neq; unfold req, PGSZ; lia).
    apply KL2_dead with (pbrk := pbrk). exact HK.
  - intros Hrf Hceil. subst br. cbv zeta in *.
    assert (Hn : bv_unsigned (Z_to_bv 64 PGSZ) = PGSZ) by (apply unsigned_lit; unfold PGSZ; lia).
    assert (HPG : lbrk_pages_ok L (b + l) PGSZ = true).
    { apply (KL2_lbrk_pages_ok L pbrk h (b + l) PGSZ HK); [lia| unfold PGSZ; lia| lia| |].
      - rewrite <- Ebrk, Z_to_bv_bv_unsigned. exact Hrf.
      - intros b1 l1 E. rewrite Ereg in E. injection E as <- <-. split; [exact R4| left; lia]. }
    split.
    + unfold answer_ok. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). rewrite Hph, Ereg.
      unfold brk_answer_ok. rewrite Z.eqb_refl, HPG. reflexivity.
    + unfold event_post. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). rewrite Z.eqb_refl, Hph, Ereg.
      pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
      assert (Kmres' : forall e, In e ((vm_brk h, Z_to_bv 64 PGSZ) :: vm_maps h) -> region_free (vm_reserved h) (fst e) (snd e) = true).
      { pose proof (k2_mres _ _ _ HK) as Kmres. intros e [<-|He]; [exact (region_free_app_l _ _ _ _ Hrf)| exact (Kmres e He)]. }
      k2_open HK. constructor; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp set_brkreg ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; first [exact Kmres' | auto].
      * apply vmwf_cons; [exact Kwf| rewrite Hn; unfold PGSZ in *; lia| eapply region_free_app_r; exact Hrf].
      * rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; try lia; auto.
      * intros b0 l0 Hin. pose proof (WB b0 l0 (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6).
        pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D.
        specialize (Kgr b0 l0 Hin). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption; try (right; assumption).
        unfold brk_disj in *. cbn. intros b1 l1 E. injection E as <- <-. specialize (G6 b l Ereg). clear -G6 D Ebrk B2. lia.
      * intros b0 l0 k Hin. pose proof (WB b0 l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6).
        pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D.
        specialize (Kme b0 l0 k Hin). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption; try (right; assumption).
        unfold brk_disj in *. cbn. intros b1 l1 E. injection E as <- <-. specialize (G8 b l Ereg). clear -G8 D Ebrk B2. lia.
      * intros b1 l1 E. injection E as <- <-. splits; auto.
        -- clear -R3. unfold PGSZ in *; lia.
        -- unfold PGSZ in *. rewrite Z.add_mod, R4 by lia. reflexivity.
        -- clear -Hceil Ebrk. lia.
        -- intros x Hx. destruct (Z_lt_le_dec x (b + l)) as [Hlt|Hge].
           ++ destruct (Rcov x ltac:(lia)) as (e & He & Hr'). exists e. split; [right; exact He| exact Hr'].
           ++ exists (vm_brk h, Z_to_bv 64 PGSZ). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Hn. lia.
      * rewrite Hph. exists b, (l + PGSZ). rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; auto; lia.
Qed.

Lemma region_free_out : forall maps aw nw,
  (forall e, In e maps -> ehi e <= bv_unsigned aw \/ bv_unsigned aw + bv_unsigned nw <= elo e) ->
  region_free maps aw nw = true.
Proof.
  induction maps as [|[e sz] maps IH]; intros aw nw H; [reflexivity|]. cbn [region_free].
  rewrite IH by (intros e' He'; apply H; right; exact He'). unfold iv_overlap.
  specialize (H (e, sz) (or_introl eq_refl)). unfold ehi, elo in H; cbn [fst snd] in H. destruct H as [H|H].
  - replace (bv_unsigned aw <? bv_unsigned e + bv_unsigned sz) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  - replace (bv_unsigned e <? bv_unsigned aw + bv_unsigned nw) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite andb_false_r. reflexivity.
Qed.

Lemma KL2_mmap_fixed : forall L pbrk h cur, KL2 L pbrk h -> ld_brk L = BPGuard cur ->
  let a := round_up_pg cur in
  let aw := Z_to_bv 64 a in let nw := Z_to_bv 64 PGSZ in
  a = cur /\ cur mod PGSZ = 0 /\ 0 < cur /\ cur + PGSZ <= alloc_ceiling
  /\ region_free (vm_reserved h) aw nw = true
  /\ map_contains (vm_maps h) aw nw = true
  /\ mmap_fixed_answer_ok a a = true
  /\ KL2 (event_post L (EMmap a PGSZ PROT_NONE MAPFX) a) pbrk
         (mkVmMapsFull (vm_reserved h) (vm_maps h) ((aw, nw) :: maps_subtract (vm_noaccess h) a (a + PGSZ))
                       (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
Proof.
  intros L pbrk h cur HK Hph a aw nw. pose proof alloc_ceiling_lt as Hcl.
  pose proof (k2_phase _ _ _ HK) as Kph0. rewrite Hph in Kph0. destruct Kph0 as (Ecur & Ebrk & Epbrk & Ereg & Hceil & (e0 & He0 & He0l & He0h) & Dg & Dm).
  pose proof (k2_start _ _ _ HK) as (S1 & S2 & S3 & S4 & S5).
  assert (Ha : a = cur). { subst a. apply round_up_pg_aligned. rewrite Ecur. exact S2. }
  assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia).
  assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia).
  assert (Hrf : region_free (vm_reserved h) aw nw = true).
  { apply region_free_out. intros e He. rewrite Ua, Un, Ha, Ecur.
    destruct (k2_resv_top _ _ _ HK e He) as [H|H]; [left; exact H| right; unfold PGSZ in *; lia]. }
  assert (Hmc : map_contains (vm_maps h) aw nw = true).
  { unfold map_contains. apply existsb_exists. exists e0. split; [exact He0|]. rewrite Ua, Un. unfold elo, ehi in *.
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by (unfold PGSZ in *; lia). reflexivity. }
  splits.
  - exact Ha.
  - rewrite Ecur. exact S2.
  - lia.
  - unfold PGSZ in *; lia.
  - exact Hrf.
  - exact Hmc.
  - unfold mmap_fixed_answer_ok. rewrite Z.eqb_refl. apply orb_true_r.
  - unfold event_post. change (Z.land MAPFX MAP_FIXED =? 0) with false. cbv iota.
    pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
    assert (Dgm : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k, In (b0, l0, k) (ld_metas L)) ->
                   b0 + mmap_len l0 <= a \/ a + 2 * PGSZ <= b0).
    { intros b0 l0 [H|[k H]]; rewrite Ha; [apply (Dg _ _ H)| apply (Dm _ _ _ H)]. }
    assert (Hlohi : a < a + PGSZ) by (unfold PGSZ; lia).
    k2_open HK. constructor; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp set_brkph set_brkreg ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto.
    + intros e [<-|He]; [rewrite elo_pair, ehi_pair, Ua, Un; unfold PGSZ in *; lia|].
      destruct (maps_subtract_In _ _ _ _ He) as ([a1 s1] & H1 & H1'). pose proof (Kna _ H1) as W1. unfold elo, ehi in W1; cbn in W1.
      pose proof (iv_subtract_sub a1 s1 a (a + PGSZ) e ltac:(lia) ltac:(lia) H1'). lia.
    + intros b0 l0 Hin. pose proof (WB b0 l0 (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6). pose proof (Dgm b0 l0 (or_introl Hin)) as D.
      specialize (Kgr b0 l0 Hin). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption.
      unfold brk_disj; cbn. intros b1 l1 E. injection E as <- <-. clear -D. unfold PGSZ in *. lia.
    + intros b0 l0 k Hin. pose proof (WB b0 l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6). pose proof (Dgm b0 l0 (or_intror (ex_intro _ k Hin))) as D.
      specialize (Kme b0 l0 k Hin). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption.
      * unfold brk_disj; cbn. intros b1 l1 E. injection E as <- <-. clear -D. unfold PGSZ in *. lia.
      * intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
        pose proof (Kna _ He) as We.
        destruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) Hlohi ltac:(lia)
                   ltac:(destruct e; unfold elo, ehi in We; cbn in We |- *; lia)
                   ltac:(destruct e; exact Hel) ltac:(unfold PGSZ; lia) ltac:(destruct e; exact Heh)
                   ltac:(clear -D Hq1 Hq2 G5; unfold PGSZ in *; nia)) as (e' & He' & Hr).
        exists e'. split; [right; eapply maps_subtract_In_intro; [exact He| destruct e; exact He']| exact Hr].
    + intros b1 l1 E. injection E as <- <-. splits.
      * lia.
      * rewrite Ha, Ecur. exact S2.
      * lia.
      * reflexivity.
      * lia.
      * intros z Hz. exists e0. split; [exact He0|]. lia.
    + exists a, (2 * PGSZ). splits; [reflexivity| lia| lia].
Qed.

Lemma g_remove_split : forall a l0 (l : list (Z * Z)) (M : list Z), In (a, l0) l -> List.NoDup (map fst l ++ M) ->
  exists l1 l2, l = l1 ++ (a, l0) :: l2 /\ g_remove a l = l1 ++ l2.
Proof.
  intros a l0 l M. induction l as [|[x1 x2] l IH]; intros Hin Hnd; [destruct Hin|]. cbn [g_remove fst snd].
  cbn [map fst app] in Hnd. inversion Hnd as [|? ? Hni Hnd']; subst.
  destruct (Z.eqb_spec x1 a) as [->|Hne].
  - destruct Hin as [E|Hin]; [injection E as ->; exists [], l; split; reflexivity|].
    exfalso. apply Hni. apply in_or_app. left. apply in_map_iff. exists (a, l0). split; [reflexivity| exact Hin].
  - destruct Hin as [E|Hin]; [injection E; intros; subst; contradiction|]. destruct (IH Hin Hnd') as (l1 & l2 & -> & E).
    exists ((x1, x2) :: l1), l2. rewrite E. split; reflexivity.
Qed.

Lemma phase_quiet2 : forall L L' pbrk h h',
  KL2 L pbrk h -> brk_quiet L -> ld_brk L' = ld_brk L -> ld_brkreg L' = ld_brkreg L ->
  vm_start_brk h' = vm_start_brk h -> vm_brk h' = vm_brk h ->
  phase_inv2 (ld_brk L') L' pbrk h'.
Proof.
  intros L L' pbrk h h' HK Hq E1 E2 E3 E4. pose proof (k2_phase _ _ _ HK) as Kph. unfold brk_quiet in Hq. unfold phase_inv2.
  rewrite E1, E2, E3, E4. destruct (ld_brk L); try contradiction; auto.
Qed.

Lemma KL2_munmap : forall L pbrk h a l0 len, KL2 L pbrk h -> brk_quiet L -> In (a, l0) (ld_groups L) ->
  (len = l0 \/ len = round_up_pg l0) ->
  let n := mmap_len l0 in
  let aw := Z_to_bv 64 a in let nw := Z_to_bv 64 n in
  0 < len < 2^64 /\ mmap_len len = n /\ a mod PGSZ = 0 /\ 0 < a /\ 0 < n /\ a + n <= alloc_ceiling
  /\ map_has (vm_maps h) aw nw = true
  /\ munmap_answer_ok 0 = true
  /\ KL2 (event_post L (EMunmap a len) 0) pbrk
         (mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) aw) (maps_subtract (vm_noaccess h) a (a + n))
                       (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h))
  /\ Z.of_nat (length (map_remove (vm_maps h) aw)) < Z.of_nat (length (vm_maps h))
  /\ live_bytes (map_remove (vm_maps h) aw) <= live_bytes (vm_maps h).
Proof.
  intros L pbrk h a l0 len HK Hq Hin Hlen n aw nw. pose proof alloc_ceiling_lt as Hcl.
  rewrite round_up_pg_eq in Hlen. fold (mmap_len l0) in Hlen.
  pose proof (k2_groups _ _ _ HK a l0 Hin) as (A1 & A2 & A3 & A4 & A5 & A6).
  pose proof (went_In_bounds _ _ _ a l0 HK (or_introl Hin)) as (_ & B2 & _ & _ & B5 & B6).
  fold n in A4, A5, A6, B2, B5, B6.
  assert (Hnn : mmap_len n = n) by (subst n; apply mmap_len_of_aligned; [lia| apply mmap_len_aligned]).
  assert (Hlen3 : 0 < len < 2^64 /\ mmap_len len = n).
  { destruct Hlen as [-> | ->]; [unfold LEN_MAX in A1; split; [lia| reflexivity]| split; [lia| exact Hnn]]. }
  destruct Hlen3 as [Hlen1 Hlen2].
  assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; lia).
  assert (Un : bv_unsigned nw = n) by (subst nw; apply unsigned_lit; lia).
  assert (Hhas : map_has (vm_maps h) aw nw = true).
  { unfold map_has. apply existsb_exists. exists (went a n). split; [exact A5|]. unfold went, wz. fold aw nw. cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity. }
  splits; try assumption; try lia.
  - reflexivity.
  -
    unfold event_post. set (L' := set_groups (g_remove a (ld_groups L)) L).
    pose proof (k2_distinct _ _ _ HK) as Kd.
    destruct (g_remove_split a l0 (ld_groups L) _ Hin Kd) as (g1 & g2 & Eg & Ezz).
    rewrite Eg, map_app in Kd. cbn [map fst] in Kd. rewrite <- app_assoc in Kd. cbn [app] in Kd.
    pose proof (List.NoDup_remove_1 _ _ _ Kd) as Kd1. pose proof (List.NoDup_remove_2 _ _ _ Kd) as Kd2.
    assert (Hg' : forall b l, In (b, l) (g_remove a (ld_groups L)) -> In (b, l) (ld_groups L) /\ b <> a).
    { intros b l H. rewrite Ezz in H. rewrite Eg. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]|].
      intros ->. apply Kd2. rewrite app_assoc, <- map_app. apply in_or_app. left. apply in_map_iff. exists (a, l). split; [reflexivity| exact H]. }
    assert (Hm' : forall b l k, In (b, l, k) (ld_metas L) -> b <> a).
    { intros b l k H ->. apply Kd2. apply in_or_app. right. apply in_or_app. right. apply in_map_iff. exists (a, l, k). split; [reflexivity| exact H]. }
    assert (Dother : forall b l, (In (b, l) (ld_groups L) \/ exists k, In (b, l, k) (ld_metas L)) -> b <> a ->
                     b + mmap_len l <= a \/ a + n <= b).
    { intros b l H Hne. pose proof (went_In_bounds _ _ _ b l HK H) as (C1 & C2 & C3 & C4 & C5 & C6).
      destruct (pwdisj_In _ _ _ (proj2 (k2_wf _ _ _ HK)) C4 A5) as [E|D].
      - exfalso. apply Hne. apply (f_equal elo) in E. rewrite C5, B5 in E. exact E.
      - unfold edisj in D. rewrite C5, C6, B5, B6 in D. lia. }
    assert (Hlohi : a < a + n) by lia.
    assert (Hph' : phase_inv2 (ld_brk L') L' pbrk
              (mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) aw) (maps_subtract (vm_noaccess h) a (a + n))
                            (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h))).
    { eapply phase_quiet2; [exact HK| exact Hq| reflexivity| reflexivity| reflexivity| reflexivity]. }
    assert (Kfst : forall b l, b <> a -> 0 < b < 2^64 -> fst (went b (mmap_len l)) <> aw).
    { intros b l Hne Hb E. apply Hne. apply (f_equal bv_unsigned) in E. cbn [fst went] in E. rewrite unsigned_wz, Ua in E by lia. exact E. }
    assert (Hkeep : forall e, In e (vm_maps h) -> fst e <> aw -> In e (map_remove (vm_maps h) aw)).
    { intros e He Hne. unfold map_remove. apply filter_In. split; [exact He|]. destruct (bv_eqb (fst e) aw) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. contradiction. }
    assert (Kmres' : forall e, In e (map_remove (vm_maps h) aw) -> region_free (vm_reserved h) (fst e) (snd e) = true).
    { intros e He. unfold map_remove in He. apply filter_In in He as [He _]. exact (k2_mres _ _ _ HK e He). }
    subst L'. k2_open HK. constructor; try exact Hph'; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; first [exact Kmres' | auto].
    + apply vmwf_remove. exact Kwf.
    + intros e He. destruct (maps_subtract_In _ _ _ _ He) as ([a1 s1] & H1 & H1'). pose proof (Kna _ H1) as W1. unfold elo, ehi in W1; cbn in W1.
      pose proof (iv_subtract_sub a1 s1 a (a + n) e ltac:(lia) ltac:(lia) H1'). lia.
    + intros b0 l1 Hin0. destruct (Hg' b0 l1 Hin0) as [Hin1 Hne]. specialize (Kgr b0 l1 Hin1). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption.
      apply Hkeep; [exact G5|]. apply Kfst; auto. pose proof (mmap_len_ge l1 G0). lia.
    + intros b0 l1 k Hin0. pose proof (Hm' b0 l1 k Hin0) as Hne. specialize (Kme b0 l1 k Hin0). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption.
      * apply Hkeep; [exact G7|]. apply Kfst; auto. pose proof (mmap_len_ge l1 G0). lia.
      * intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
        pose proof (Dother b0 l1 (or_intror (ex_intro _ k Hin0)) Hne) as D. pose proof (Kna _ He) as We.
        destruct (iv_subtract_contains (fst e) (snd e) a (a + n) (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) Hlohi ltac:(lia)
                   ltac:(destruct e; unfold elo, ehi in We; cbn in We |- *; lia)
                   ltac:(destruct e; exact Hel) ltac:(unfold PGSZ; lia) ltac:(destruct e; exact Heh)
                   ltac:(clear -D Hq1 Hq2 G5; unfold PGSZ in *; nia)) as (e' & He' & Hr).
        exists e'. split; [eapply maps_subtract_In_intro; [exact He| destruct e; exact He']| exact Hr].
    + rewrite Ezz, map_app, <- app_assoc. exact Kd1.
    + intros b0 l1 E. specialize (Kreg b0 l1 E). destruct Kreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto.
      intros z Hz. destruct (Rcov z Hz) as (e & He & Hr). exists e. split; [|exact Hr]. apply Hkeep; [exact He|].
      intros Efst. unfold brk_disj in A6. specialize (A6 b0 l1 E).
      destruct (pwdisj_In _ _ _ (proj2 Kwf) He A5) as [->|D].
      * rewrite B5, B6 in Hr. clear -Hr A6 Hz R3. unfold PGSZ in *. lia.
      * pose proof (proj1 Kwf e He) as W. unfold edisj, elo, ehi in D, W. rewrite Efst in D, W. cbn [fst snd went] in D. unfold wz in D. fold aw nw in D. rewrite Un in D. lia.
  -
    clear -A5. unfold map_remove. induction (vm_maps h) as [|e es IH]; [destruct A5|]. cbn [List.filter length].
    destruct A5 as [->|Hin'].
    + cbn [fst went]. unfold wz. fold aw. rewrite bv_eqb_refl. cbn [negb]. pose proof (List.filter_length_le (fun p : word * word => negb (bv_eqb (fst p) aw)) es). lia.
    + specialize (IH Hin'). destruct (negb (bv_eqb (fst e) aw)); cbn [length]; lia.
  - apply OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.live_bytes_map_remove_le.
Qed.

Lemma nodup_map_inj : forall {A B} (f : A -> B) l x y, List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [|z l IH]; intros x y Hnd Hx Hy E; [destruct Hx|]. cbn in Hnd. inversion Hnd; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | | apply IH; auto].
  - exfalso. apply H1. rewrite E. apply in_map. exact Hy.
  - exfalso. apply H1. rewrite <- E. apply in_map. exact Hx.
Qed.

Lemma map_base_bump : forall a ms, map (fun m : Z * Z * Z => fst (fst m)) (map (bump_meta a) ms) = map (fun m => fst (fst m)) ms.
Proof.
  intros a ms. rewrite map_map. apply map_ext. intros [[b l] k]. unfold bump_meta. destruct (_ =? _); reflexivity.
Qed.

Lemma KL2_mprotect : forall L pbrk h b l k, KL2 L pbrk h -> brk_quiet L -> In (b, l, k) (ld_metas L) ->
  (2 + k) * PGSZ <= round_up_pg l ->
  let a := b + (1 + k) * PGSZ in
  let aw := Z_to_bv 64 a in let nw := Z_to_bv 64 PGSZ in
  a mod PGSZ = 0 /\ 0 < a /\ a + PGSZ <= alloc_ceiling
  /\ map_contains (vm_noaccess h) aw nw = true
  /\ map_contains (vm_maps h) aw nw = true
  /\ mprotect_answer_ok 0 = true
  /\ KL2 (event_post L (EMprotect a PGSZ PROT_RW) 0) pbrk
         (mkVmMapsFull (vm_reserved h) (vm_maps h) (maps_subtract (vm_noaccess h) a (a + PGSZ))
                       (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
Proof.
  intros L pbrk h b l k HK Hq Hin Hk2 a aw nw. pose proof alloc_ceiling_lt as Hcl.
  rewrite round_up_pg_eq in Hk2. fold (mmap_len l) in Hk2.
  pose proof (k2_metas _ _ _ HK b l k Hin) as (A1 & A2 & A3 & A4 & Ak & Ak1 & A5 & A6 & Ana).
  pose proof (went_In_bounds _ _ _ b l HK (or_intror (ex_intro _ k Hin))) as (_ & B2 & _ & _ & B5 & B6).
  set (nb := mmap_len l) in *.
  assert (Hab : b + PGSZ <= a /\ a + PGSZ <= b + nb) by (subst a; unfold PGSZ in *; nia).
  assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia).
  assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia).
  assert (Hamod : a mod PGSZ = 0). { subst a. unfold PGSZ in *. rewrite Z.add_mod, A3, Z.mod_mul by lia. reflexivity. }
  assert (Hcn : map_contains (vm_noaccess h) aw nw = true).
  { destruct (Ana (1 + k) ltac:(lia) ltac:(lia)) as (e & He & Hel & Heh). unfold map_contains. apply existsb_exists. exists e. split; [exact He|].
    rewrite Ua, Un. unfold elo, ehi in Hel, Heh. subst a. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
  assert (Hcm : map_contains (vm_maps h) aw nw = true).
  { unfold map_contains. apply existsb_exists. exists (went b nb). split; [exact A5|]. rewrite Ua, Un. unfold elo, ehi in B5, B6. rewrite B5.
    replace (bv_unsigned (fst (went b nb)) + bv_unsigned (snd (went b nb))) with (b + nb) by (symmetry; exact B6).
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
  splits.
  - exact Hamod.
  - lia.
  - lia.
  - exact Hcn.
  - exact Hcm.
  - reflexivity.
  - unfold event_post. cbn [Z.eqb orb]. set (L' := set_metas (map (bump_meta a) (ld_metas L)) L).
    pose proof (k2_distinct _ _ _ HK) as Kd. pose proof (List.NoDup_app_remove_l _ _ Kd) as Kdm.
    assert (Dother : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k0, In (b0, l0, k0) (ld_metas L)) -> b0 <> b ->
                     b0 + mmap_len l0 <= b \/ b + nb <= b0).
    { intros b0 l0 H Hne. pose proof (went_In_bounds _ _ _ b0 l0 HK H) as (C1 & C2 & C3 & C4 & C5 & C6).
      destruct (pwdisj_In _ _ _ (proj2 (k2_wf _ _ _ HK)) C4 A5) as [E|D].
      - exfalso. apply Hne. apply (f_equal elo) in E. rewrite C5, B5 in E. exact E.
      - unfold edisj in D. rewrite C5, C6, B5, B6 in D. lia. }
    assert (Hlohi : a < a + PGSZ) by (unfold PGSZ; lia).
    assert (Hph' : phase_inv2 (ld_brk L') L' pbrk
              (mkVmMapsFull (vm_reserved h) (vm_maps h) (maps_subtract (vm_noaccess h) a (a + PGSZ))
                            (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h))).
    { eapply phase_quiet2; [exact HK| exact Hq| reflexivity| reflexivity| reflexivity| reflexivity]. }
    subst L'. k2_open HK. constructor; try exact Hph'; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp set_metas ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto.
    + intros e He. destruct (maps_subtract_In _ _ _ _ He) as ([a1 s1] & H1 & H1'). pose proof (Kna _ H1) as W1. unfold elo, ehi in W1; cbn in W1.
      pose proof (iv_subtract_sub a1 s1 a (a + PGSZ) e ltac:(lia) ltac:(lia) H1'). lia.
    + intros b0 l0 k0' Hin0. apply in_map_iff in Hin0 as ([[b1 l1] k0] & Eb & Hin1).
      specialize (Kme b1 l1 k0 Hin1). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
      unfold bump_meta in Eb. destruct (Z.eqb_spec (b1 + (1 + k0) * PGSZ) a) as [Ea|Na]; injection Eb as -> -> <-.
      * assert (Eb0 : b0 = b).
        { destruct (Z.eq_dec b0 b) as [E|Hne]; [exact E|]. exfalso.
          pose proof (Dother b0 l0 (or_intror (ex_intro _ k0 Hin1)) Hne) as D. pose proof (mmap_len_ge l0 G0). clear -D Ea Hab G5 G6 H. unfold PGSZ in *. nia. }
        subst b0. pose proof (nodup_map_inj _ _ _ _ Kdm Hin1 Hin (eq_refl b)) as E. injection E as -> ->.
        splits; try assumption; try lia.
        intros q Hq1 Hq2. destruct (G9 q ltac:(lia) Hq2) as (e & He & Hel & Heh). pose proof (Kna _ He) as We.
        destruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) (b + q * PGSZ) (b + q * PGSZ + PGSZ) Hlohi ltac:(lia)
                   ltac:(destruct e; unfold elo, ehi in We; cbn in We |- *; lia)
                   ltac:(destruct e; exact Hel) ltac:(unfold PGSZ; lia) ltac:(destruct e; exact Heh)
                   ltac:(right; subst a; clear -Hq1; unfold PGSZ in *; nia)) as (e' & He' & Hr).
        exists e'. split; [eapply maps_subtract_In_intro; [exact He| destruct e; exact He']| exact Hr].
      * splits; try assumption.
        intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh). pose proof (Kna _ He) as We.
        assert (D : (b0 + q * PGSZ + PGSZ <= a \/ a + PGSZ <= b0 + q * PGSZ)).
        { destruct (Z.eq_dec b0 b) as [->|Hne].
          { pose proof (nodup_map_inj _ _ _ _ Kdm Hin1 Hin (eq_refl b)) as E. injection E as -> ->. exfalso. apply Na. reflexivity. }
          pose proof (Dother b0 l0 (or_intror (ex_intro _ k0 Hin1)) Hne) as D. clear -D Hab Hq1 Hq2 G5. unfold PGSZ in *. nia. }
        destruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) Hlohi ltac:(lia)
                   ltac:(destruct e; unfold elo, ehi in We; cbn in We |- *; lia)
                   ltac:(destruct e; exact Hel) ltac:(unfold PGSZ; lia) ltac:(destruct e; exact Heh) D) as (e' & He' & Hr).
        exists e'. split; [eapply maps_subtract_In_intro; [exact He| destruct e; exact He']| exact Hr].
    + rewrite map_base_bump. exact Kd.
Qed.

(* [comment removed for export] *)
Lemma KL2_meta_page_free : forall L pbrk h b l k (V : list (word * word)), KL2 L pbrk h ->
  In (b, l, k) (ld_metas L) -> (2 + k) * PGSZ <= round_up_pg l -> incl V (vm_reserved h) ->
  region_free V (Z_to_bv 64 (b + (1 + k) * PGSZ)) (Z_to_bv 64 PGSZ) = true.
Proof.
  intros L pbrk h b l k V HK Hin Hk2 Hincl. pose proof alloc_ceiling_lt as Hcl.
  rewrite round_up_pg_eq in Hk2. fold (mmap_len l) in Hk2.
  pose proof (k2_metas _ _ _ HK b l k Hin) as (A1 & A2 & A3 & A4 & Ak & Ak1 & A5 & A6 & Ana).
  pose proof (went_In_bounds _ _ _ b l HK (or_intror (ex_intro _ k Hin))) as (_ & B2 & _ & _ & B5 & B6).
  pose proof (k2_mres _ _ _ HK _ A5) as Hrf.
  set (nb := mmap_len l) in *.
  assert (Hab : b + PGSZ <= b + (1 + k) * PGSZ /\ b + (1 + k) * PGSZ + PGSZ <= b + nb) by (unfold PGSZ in *; nia).
  assert (Ua : bv_unsigned (Z_to_bv 64 (b + (1 + k) * PGSZ)) = b + (1 + k) * PGSZ)
    by (apply unsigned_lit; unfold PGSZ in *; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 PGSZ) = PGSZ) by (apply unsigned_lit; unfold PGSZ; lia).
  apply region_free_out. intros e He. apply Hincl in He.
  pose proof (region_free_disj _ _ _ _ Hrf He) as D. unfold elo, ehi in B5, B6, D |- *. rewrite Ua, Un. lia.
Qed.

Lemma KL2_alloc_top : forall L pbrk h, KL2 L pbrk h -> alloc_top h = alloc_ceiling.
Proof.
ltac2:(KReplay.run1 (kr_t_KLink ()) ["CEIL_WRAP_1"; "KL2DEF"] "h02Hah16__sat1h24__x1h31zh42HKh51Lh67__arithh74__ffh86__sat0h98__varmaph:5__with;1hh<4pbrkp;3p;1p;2p;4p;7p;6p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?p4p710p9P0p1001fp4p710p9p1002^p4p710R0p1003;p4p710R1p8P0g003WR0p4p710R2p8p103f[R3p6071001R4p103gep4p710R5p8P4p101Q7R6p4p710p8P4P1p8P4p100H;p4p710p8P4p10045R4p4p710p8P3p60721000R3P5p8P3P6p4p7210p8P3P1p8P3p103h<p4p710p8P3p100;ep4p7210p8P3P2p8P3P4p4p7210R4p8P3p101Z>p4p710p8P4P1p8P4P2p8p1004Rp4p73110P2p8g01J@j3UTg01T@j1TTg004nj10Tg00Y9j15Tg00@3j16Tg00YWj2OTg00Ucj29Tg00k\j23Tg009mj31Tg00Z4j2@Tg00Z\j2;Tg00EKj24Tg00[8j3STg00[\j2RTg00<Bj2<Tg008mj1NTg0074j1MTg00=Pj2KTg00>jj1FTg00?Hj1ETg00@Xj2DTg00\`j28Tg005Sj17Tg00]Cj3CTg00\=j3BTg014Cj3GTg00A;j4HTg00H]j7ATg00Blj2ITg00CNj2JTg00D:j3?Tg00DYj4LTP0j6:Tg01]aj1>Tg00U9j2PTg042?j4QTg043Bj1=Tf0R0#0#0#0#0p=2g01_\g00M^R2g01aaf2R4f1R1;U0P2p,4RUNp#TR3g00KdR6#0R5#5R7%65#6#6R8#5R9'OR:'9R;g044:R<,30=123X32P2%05#2R5#0#2#2#2#2#5R=13;0=123X321@79g00POR;/;7R>14;91;;:[R?[14;7R@g00LfRAAS791UW014;:\A^0@P1g00a41R;7'<P>eO1P?g00N<R?#N%M?1K21%F2%E2R?g00Ieg00JDR>P>g00JdR>P21D26R61827%785C25B2182=5G2g01;BP6CHg00KDFA1I?>P0P4g00OOR>g00OoR?'<1J04=1>?dA?2;1CLb7b9b:X22190:/3==120^22P0P3O1b6b1b8b1P<g0457E:%75%>1'Pf3P4P1P0CQE:%=1=123eW4W;W<W5o"). Qed.

Lemma KL2_init_sp_window : forall L pbrk h, KL2 L pbrk h -> sp_window_lo <= bv_unsigned (vm_init_sp h).
Proof.
ltac2:(KReplay.run1 (kr_t_KLink ()) ["CEIL_WRAP_1"; "KL2DEF"] "h02Hah14__p1h26__sat1h34__x1h4<CEIL_RANGE__h52HKh61Lh77__arithh84__ffh96__sat0h:8__varmaph;5__with<1hh=4pbrkh>1zp;3p;1p;2p;4p;6p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?p4p710p9P0p1001fp4p710p9p1002^p4p710R0p1003;p4p710R1p8P0g003WR0p4p710R2p8p103f[R3p6071001R4p103gep4p710R5p8P4p101Q7R6p4p710p8P4P1p8P4p100H;p4p710p8P4p10045R4p4p710p8P3p60721000R3P5p8P3P6p4p7210p8P3P1p8P3p103h<p4p710p8P3p100;ep4p7210p8P3P2p8P3P4p4p7210R4p8P3p101Z>p4p710p8P4P1p8P4P2p8p1004Rp4p73110P2p8g01J@j3]Tg01T@j1\Tg004nj10Tg00Y9j15Tg00@3j12Tg00YWj2NTg00Ucj2;Tg00EKj21Tg0468j1ETg00T^j2@Tg00Z4j2UTg00Z\j2=Tg00[8j3RTg00[\j2QTg00<Bj2<Tg008mj1MTg0074j1LTg00=Pj2ITg00>jj1HTg00?Hj1GTg00\`j28Tg00@Xj2FTg00A;j4?Tg019Tj6JTg00]fj7KTg00Afj1DTg005Sj19Tg00]Cj3CTg00\=j3BTg00BHj8OTg00Blj2PTg00CNj2ATg009mj3STg00D:j3TTg00DYj4[Tg01]aj1ZTg00U9j2YTg042?j4VTP0j6WTg00H]j7XTf0R0#2#2p=>%20#2#2#2p=3%00#0p=7%00#0#0#0p=6%00#0#0#0#0#0#0#0p=4f1R2g00IeR4g00JDR1P1g00JdR3P0g00KDFXp=:g01_\g00M^R6g01aaf2R5?]20P6p,4RUNpR7#\R8g00KdR9#0R:#5R;%2:#>R<#5R='NR>';R?g047<R@/10X>6%E7%>9#3#3#3R7#0#3#3#0#7#6#4#4#5RA/18%27R7#3#3#0#7#6#4#4#5,18RB'@1U;=g00PORC/=;RD11C=1=C>[RE[11C;RFg00LfRGAR;=2UW011C>\G^0FP2g00a41QC;'<PDeO1PEp-0REg00N<RD#M%LD1I62%H6%G6RDP4P1P1P3PDP4P1P1P3P6186Ag00NhRF1F69R9C?,:DPDP4P1P1P3f3R4EJFK%D1P6%07#7#6#4#4#4#5R7,86PF186;%9<5C69B69C?,:DGO1PD3P0P5g00OORDg00OoR3'<1A05=SD3dAT6C2C[b8b:b;X36W111A0/@21;2>,17[^36^1EP0PBP8f4O3b7b2b9b211@?eb4%0:#6#9%Z2'YP4P5P2P0CVEWW5W<W=W6o"). Qed.

End KL2DEF.
End CEIL_WRAP_1.
End KLink.
