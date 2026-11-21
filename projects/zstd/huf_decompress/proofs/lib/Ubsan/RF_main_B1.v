(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (10 recorded proofs replaced by written proofs (stderr_file0_wfile0, stderr_wfile0_agree, stderr_wfile0_heap_pres and 7 more); fprintf_exit restated for the revision's model; the zero-mapped stack depth; fprintf_exit and fwrite_exit are zstd/simple_decompress's proofs, with this binary's addresses; fprintf_exit and fwrite_exit use this unit's RSTAT, which takes no atexit flag). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree Startup_kit STRW_tac F_fmt_fp_lib Printf_fmts.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg F_syscalls StdioFiles Startup Exit F_printf_iface Stdio_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_iface RDriver_facts RDriver_kit RDriver_ctx RF_main_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require RMalloc_ifaceP.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_main_B1 () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib4Init5Logic2eq01C59OSSVerify5KrLib6Common8DrvAgree6zbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Image:ro_bytes_bC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib5Ubsan4UImg5usegsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RF_main_B15S_OOMC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RF_main_B15s_oomC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RF_main_B17S_SHORTC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RF_main_B17s_shortC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RF_main_B16S_OVERC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RF_main_B16s_overC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib6Common8DrvAgree=zbytes_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Image@ro_bytes_b_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem;ro_bytes_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Driver7IOStyle00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver>read_loop_bodyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver6s_diagC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7SysStep=impl_from_evtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Driver9rd_result00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps4bptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=Harness_iface<stderr_file0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:StdioFiles:file_cellsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z4landI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatK47Corelib4Init5Logic2or01K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib5Ubsan;Stdio_iface@fwrite_diag_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_iface@emit_printf_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8DrvAgree6magreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RDriver_ctx;stderr_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;Stdio_iface=stderr_wfile0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC59OSSVerify5KrLib6Common8DrvAgree?rw_cells_magreeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib5Ubsan=RMalloc_iface:rheap_presC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RMalloc_iface<rclient_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RMalloc_iface=ralloc_staticC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib6Malloc<Malloc_iface8in_blockC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07K47Corelib4Init5Logic2or02c59OSSVerify5KrLib5Ubsan:RF_main_B1Cstderr_wfile0_agreeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib6Malloc<MallocBlocks5blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree3memC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8DrvAgree?magree_of_munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~C46Stdlib7Strings6StringDlist_ascii_of_stringC46Stdlib7Strings5Ascii:N_of_asciiC56Stdlib6ZArith6BinInt1Z4of_NI47Corelib5Lists7ListDef6Forall00K47Corelib5Lists7ListDef6Forall01C46Stdlib7Strings5Ascii?N_ascii_boundedC56Stdlib6NArith6BinNat1N2ltC56Stdlib6ZArith4Znat3N2Z9is_nonnegK47Corelib5Lists7ListDef6Forall02K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes8list_indC59OSSVerify5KrLib4Spec5Stdio3strC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapI46Stdlib7Strings5Ascii5ascii00I47Corelib7Numbers7BinNums1N00C56Stdlib6ZArith4Znat3N2Z6inj_ltI46Stdlib7Strings6String6string00C59OSSVerify5KrLib4Spec5Monad5implMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib3Lib5ITree5ebindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5epostC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4implC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mgetC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Driver5rd_st00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3sum00c59OSSVerify5KrLib5Ubsan:RF_main_B1<rd_grow_partC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver6rd_capC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver:rd_contentC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3ltbK59OSSVerify5KrLib3Lib5Nodes4node04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode8dec_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4msysC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver7io_diagC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver9rd_result01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3sum02C56Stdlib5Arith8PeanoNat3Nat3eqbC59OSSVerify5KrLib4Spec6Driver6rd_bufC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver9rd_result02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver<u8s_of_bytesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appK59OSSVerify5KrLib4Spec6Driver5rd_st01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3sum01I59OSSVerify5KrLib3Lib6Decode8read_ans00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg;UREAD_STAGEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog2ioC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad:implM_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad9implM_evtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_iface9diag_argsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9RF_main_A4BASEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RMalloc_iface5RHEAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState5ps_soC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib2FP4frm0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RDriver_iface8pat_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RDriver_ctx8sp_factsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RDriver_ctx2LOC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C59OSSVerify5KrLib5Ubsan;RDriver_ctx5RSTATC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RMallocTree8rauxv_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAbuild_stack_bytesC59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RDriver_iface;trun_cells0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr03K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC59OSSVerify5KrLib3Lib6MState;lift_resultC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib3Lib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib3Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC59OSSVerify5KrLib3Lib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC59OSSVerify5KrLib3Lib6MState8step_genC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst3CANC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_ifaceAfprintf_diag_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan9RF_main_ABstderr_file0_wfileC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr04C47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RDriver_kit9RHEAP_sspC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7reg_getC59OSSVerify5KrLib5Ubsan>F_printf_iface<stderr_wfileC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:StdioFiles9ssp_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula01C59OSSVerify5KrLib5Ubsan;RDriver_ctx:rstat_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RDriver_ctx;RSTAT_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RMalloc_iface@rclient_write_okC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib6Malloc<MallocBlocks8blk_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks8blk_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>RMalloc_ifacePARHEAP_frame_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:StdioFiles;stdout_fileC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RDriver_ctx;stdout_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RDriver_ctxAstdout_file_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>F_printf_ifaceAstderr_wfile_fileC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RDriver_ctx:exit2_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec8evt_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C59OSSVerify5KrLib4Spec5Stdio;stdout_initC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Driver8diag_msg00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg7u_phdrsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep4RATPC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic4True00C59OSSVerify5KrLib5Ubsan>F_printf_iface=FPRINTF_DEPTHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:StdioFiles;GLOBALS_TOPC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib5Ubsan:RMallocRep5RLIBCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep4RCTXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep:RSSP_GUARDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep8RGOT_SSPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio=stderr_fwriteC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RF_main_B1Cstderr_file0_wfile0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<F_fmt_fp_lib2zbC1?~~~~~~~~~~~~~~~K46Stdlib7Strings5Ascii5ascii01c59OSSVerify5KrLib5Ubsan:RF_main_B1<rodata_bytesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:Forall_appc59OSSVerify5KrLib5Ubsan:RF_main_B19str_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;Stdio_ifaceBstderr_wfile0_fileC1?~~~~~~~~~~~~~~~K46Stdlib7Strings6String6string02K59OSSVerify5KrLib4Spec6Driver8diag_msg04C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan:RF_main_B18s_oom_roC1?~~~~~~~~~~~~~~~K46Stdlib7Strings6String6string01I46Stdlib5Lists4List6Exists00C59OSSVerify5KrLib5Ubsan;Stdio_iface<FWRITE_DEPTHC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac ua := idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       end).
Ltac zst := zstep; fix_lit_store.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {lx : launchT}.
Definition S_OOM : Z := 0x102ec.    Definition s_oom : list Z := (str "cli: out of memory"%string ++ [10])%list.
Definition S_SHORT : Z := 0x103fc.  Definition s_short : list Z := (str "cli: input shorter than header"%string ++ [10])%list.
Definition S_OVER : Z := 0x1031e.   Definition s_over : list Z := (str "cli: config_len overruns input"%string ++ [10])%list.
Lemma s_oom_ro : ro_bytes_b usegs S_OOM (zbytes s_oom) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_main_B1 ()) ["CANSEC1"] "p;2p;1p;3p10000p4p7210p1000\p4p710p8g001:j23Tg001Tj12Tg002Oj30Tg003Hj31Tg003bR0g004BR1'3g004bg005Wg006R#230=101do"). Qed.
Lemma s_short_ro : ro_bytes_b usegs S_SHORT (zbytes s_short) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_main_B1 ()) ["CANSEC1"] "p;2p;1p;3g001:j23Tg001Tj12Tg002Oj30Tg003Hj31Tg003bR0g004BR1'3g004bg007Mg008J#230=101do"). Qed.
Lemma s_over_ro : ro_bytes_b usegs S_OVER (zbytes s_over) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_main_B1 ()) ["CANSEC1"] "p;2p;1p;3g001:j23Tg001Tj12Tg002Oj30Tg003Hj31Tg003bR0g004BR1'3g004bg009Gg00:C#230=101do"). Qed.

Lemma rodata_bytes : forall m A (s : list Z),
  mem_inv usegs m -> ro_bytes_b usegs A (zbytes s) = true -> 0x10000 <= A -> A + zlength s <= 0x5d000 ->
  bytes_at usegs m A (zbytes s).
Proof.
ltac2:(KReplay.run1 (kr_t_RF_main_B1 ()) ["CANSEC1"] "h04__x1h17__arithh24__ffh38__varmaph45__with54__x2h61Ah72HIh82LOh92MIh:2ROh;4cstrh<1mh=1nh>1sp;1p;2p;3p;4p;6p;8p;7g00;?j10Tg00;dj1@Tg00<Bj1<Tg00<ej1]Tg00=Gj1CTg00=gj2OTg001Tj1?Tg002Oj3LTg003Hj3=Tg00>[j15Tg00?9j21Tg00?Uj2\Tg00@Mj28Tg00@jj16Tg00AOj1UTg00Aoj2BTg00BMj1TTg00Bkj1NTg00CVj23Tg00D9j2ATg00D\j1MTg00E>j2KTg001:j2HTg00E`j2GTg00FLj3ITg00Fkj4JTg00G]j2:Tg00H=j19Tg00H]j2FTg00I:j1ETg00I_j1PTg00J=j4QTg00J[j3DTg00K>j3RTg00Kaj1STg000\j6[Tg00Lcj4ZTg00Mbj8YTg00NZj4VTg00OEj7WTg00Oij8XTf0R0#0#0p=;%00#0#0#0p=2g00PMR1f1R2g00PkP0CVp=4P2g00QRR3g00R1R4P4g00RQR5P0g00S1FWp=7f3R6P3P4P4P5f2R3P2P0GXp=>g00SQR7#0R8#;R9#0#;R:#@R;#<%@9#<R9#][%C1g004bR</O3g003bR=%?29L<3g004BR>3=%;:#2#2#5R?/16f4R@1\16'8%07#6#6#6#0#6#2#2#2#5RA'1P<f6RBf5RC%?@RDP6g00T6R6#URE%C6R61B12%T1RF%N1RG131?1A17R7'4,7G%M4R4g00TbRH,31/47,7GC>1KG5R5P0P31H=>1G03===>dAI1H2CJR>b2b3b4X0111?011H2[^01P0PBP3O2b1g00U@R?1:1@R=%90,8B%58RI%5:'FR:'1X=?%E=%9=,1HPEP6P11B13P2%P1CQPFPG1A189D17R7131A'4,7GP4131I=R1;,47,7GC>P5P>b2b3b4X01X511802/1A1823/1:[^01^51P01:1B#9f7P3O3b1b;1:9D%S@E[P<PDPCP3CZGYW7W8W:W9W>X61W<o"). Qed.
(* [comment removed for export] *)
Lemma stderr_file0_wfile0 : forall m, stderr_file0 m -> stderr_wfile0 m.
Proof.
  intros m H. exists (Z_to_bv 64 5), (wz 0), 0, 0, (repeat (Z_to_bv 8 0) 80). split; [exact H|].
  split; [vm_compute; reflexivity|]. split; [left; reflexivity| lia].
Qed.

(* [comment removed for export] *)
Lemma stderr_wfile0_agree : forall (P : Z -> Prop) m m',
  magree usegs P m m' -> (forall a, stderr_addr a -> P a) -> stderr_wfile0 m -> stderr_wfile0 m'.
Proof.
  intros P m m' AG HP (flags & mode & e & wend & tail & F1 & F2 & F3 & F4).
  exists flags, mode, e, wend, tail. split; [| split; [exact F2| split; [exact F3| exact F4]]].
  eapply rw_cells_magree; [exact AG| exact F1|]. intros a Ha. apply HP. unfold stderr_addr. cbn in Ha. lia.
Qed.
Lemma stderr_wfile0_heap_pres : forall LB SP m m', rheap_pres LB SP m m' -> stderr_wfile0 m -> stderr_wfile0 m'.
Proof.
  intros LB SP m m' HP. apply (stderr_wfile0_agree _ _ _ HP). intros a Ha. right; left.
  unfold stderr_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
Qed.
Lemma stderr_wfile0_munch : forall W m m', munch W m m' -> wmono usegs m m' -> (forall a, stderr_addr a -> outside W a) -> stderr_wfile0 m -> stderr_wfile0 m'.
Proof. intros W m m' MU WM HW. apply (stderr_wfile0_agree _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.

Lemma str_range : forall s, Forall (fun c => 0 <= c < 256) (str s).
Proof.
  intros s. unfold str. induction (list_ascii_of_string s) as [|a l IH]; cbn; constructor; [| exact IH].
  pose proof (Ascii.N_ascii_bounded a). lia.
Qed.

Lemma implM_get_bind : forall {A} (f : PState -> M PState A) s Q ms,
  implM usegs (f s) s Q ms -> implM usegs (mbind mget f) s Q ms.
Proof. intros A f s Q ms H. unfold implM, mbind, mget in *. cbn. exact H. Qed.
Lemma implM_mret_bind : forall {A B} (a : A) (f : A -> M PState B) s Q ms,
  implM usegs (f a) s Q ms -> implM usegs (mbind (mret a) f) s Q ms.
Proof. intros A B a f s Q ms H. unfold implM, mbind, mret in *. cbn. exact H. Qed.

Section B.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (arg0 arg1 : list byte) (TID : Z)
            (J8 : list byte) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : dvalid_sp sp0 argv envp.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis EARGV : argv = [arg0; arg1].
  Hypothesis HT : 0 < TID < 4194304.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis FPR : @fprintf_diag_stmt PState.
  Hypothesis FWX : fwritex_stderr_stmt.
  Hypothesis SWF : stdio_write_flush_stmt.
  Hypothesis FWR : @fwrite_diag_stmt PState.
  Hypothesis TOW : towrite_stmt.

  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).
  Notation IMGB := (build_stack_bytes L_LA pph (Z_to_bv 64 (Z.of_N u_init_pc)) sp0 L_TOP argv envp L_EXECFN uid L_GID hw draw).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE sp0 argv envp uid hw draw TID).
  Notation FRAME' mm := (MFRAME sp0 argv mm J8 S7 S6 S5 S4).
  Ltac hyps := first [exact VSP | exact VARGV | exact VENVP | exact EARGV | exact HT | exact MALLOC | exact FREE | exact FPR | exact FWX | exact SWF | exact FWR | exact TOW].

  (* [comment removed for export] *)
  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition BUF (mm : mem) (s : PState) (bufp : bptr) (A cap : Z) (DATA junk : list byte) : Prop :=
    RHEAP s [(bufp, A, cap)] mm /\ ps_fa s = tt /\ ps_so s = stdout_init /\ True
    /\ rw_cells usegs mm A [CB (length DATA) DATA; CB (Z.to_nat (cap - Z.of_nat (length DATA))) junk]
    /\ (65536 <= cap <= MAX_INPUT /\ exists k, 0 <= k /\ cap = 2 ^ k) /\ Z.of_nat (length DATA) <= cap /\ rblock_range A cap.

  (* [comment removed for export] *)
  Definition STAGE (mm : mem) (sj : list byte) : Prop := rw_cells usegs mm UREAD_STAGE [CB PSTAGE_LEN sj].

  (* [comment removed for export] *)
  Notation RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 P1v len fd cap x23 t3 t4 t5 t6 F fc mm :=
    (GST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 len) (Z_to_bv 64 fd) (Z_to_bv 64 cap) (Z_to_bv 64 UREAD_STAGE) x23 t3 t4 t5 t6 F fc mm).

  (* [comment removed for export] *)
  Definition RDINV (fd P1v : Z) (st : rd_st) (s : PState) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem)
           (A : Z) (DATA junk : list byte) (errv : word) (sj : list byte) (pc : Z),
      ms = RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 P1v (zlength (rd_content st)) fd (rd_cap st) (Z_to_bv 64 A) t3 t4 t5 t6 F fc mm
      /\ ((pc = 0x12e28 /\ x9 = Z_to_bv 64 A) \/ (pc = 0x12e08 /\ rd_content st = []))
      /\ rd_content st = map bv_unsigned DATA
      /\ BUF mm s (rd_buf st) A (rd_cap st) DATA junk /\ STAGE mm sj
      /\ FRAME' mm /\ BASE' mm /\ rw_cells usegs mm RERRNO [C4 errv] /\ frm0 fc.

  (* [comment removed for export] *)
  Definition RDBRK (fd P1v : Z) (bufp : bptr) (content : list Z) (s : PState) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x23 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem)
           (A cap : Z) (DATA junk : list byte) (errv : word),
      ms = RST 0x12e94 x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 P1v (zlength content) fd cap x23 t3 t4 t5 t6 F fc mm
      /\ content = map bv_unsigned DATA
      /\ BUF mm s bufp A cap DATA junk
      /\ FRAME' mm /\ BASE' mm /\ rw_cells usegs mm RERRNO [C4 errv] /\ frm0 fc.

  Definition POSTBODY (fd P1v : Z) (r : rd_st + rd_result) (s : PState) (ms : machine_state) : Prop :=
    match r with
    | inl st' => RDINV fd P1v st' s ms
    | inr RdExit => pat_exit 2 s ms
    | inr (RdDone b c) => RDBRK fd P1v b c s ms
    end.

  (* [comment removed for export] *)
  Notation ioS := Prog.io.
  Definition rd_read_part (fd : Z) (path : list Z) (st1 : rd_st (ptr:=bptr)) : M PState (rd_st + rd_result (ptr:=bptr)) :=
    let len := zlength (rd_content st1) in
    let want0 := rd_cap st1 - len in
    let cnt := if 65536 <? want0 then 65536 else want0 in
    a <- msys (NRead fd UREAD_STAGE cnt) (dec_read UREAD_STAGE cnt) ;;
    match a with
    | RdErr _ => io_diag ioS (DReadError path) ;;; mret (inr RdExit)
    | RdData bs =>
        if (length bs =? 0)%nat then mret (inr (RdDone (rd_buf st1) (rd_content st1)))
        else mret (inl (mkRd (rd_buf st1) (rd_cap st1) (rd_content st1 ++ u8s_of_bytes bs)))
    end.

  Definition rd_grow_part (st : rd_st) : M PState (option rd_st) :=
    if zlength (rd_content st) =? rd_cap st then
      if MAX_INPUT <=? rd_cap st then io_diag ioS DTooBig ;;; mret None
      else
        nb <- raw_malloc (rd_cap st * 2) ;;
        match nb with
        | None => io_diag ioS DOom ;;; mret None
        | Some nb' => raw_free (rd_buf st) ;;; mret (Some (mkRd nb' (rd_cap st * 2) (rd_content st)))
        end
    else mret (Some st).

  Lemma read_loop_body_eq : forall fd path st,
    read_loop_body ioS raw_malloc raw_free UREAD_STAGE fd path st
    = (g <- rd_grow_part st ;; match g with None => mret (inr RdExit) | Some st1 =>
         let want0 := rd_cap st1 - zlength (rd_content st) in
         let cnt := if 65536 <? want0 then 65536 else want0 in
         a <- msys (NRead fd UREAD_STAGE cnt) (dec_read UREAD_STAGE cnt) ;;
         match a with
         | RdErr _ => io_diag ioS (DReadError path) ;;; mret (inr RdExit)
         | RdData bs =>
             if (length bs =? 0)%nat then mret (inr (RdDone (rd_buf st1) (rd_content st1)))
             else mret (inl (mkRd (rd_buf st1) (rd_cap st1) (rd_content st1 ++ u8s_of_bytes bs)))
         end end).
  Proof. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma fprintf_exit : forall (d : diag_msg) {R} (K : M PState R) (Q : R -> PState -> machine_state -> Prop) (s : PState) (LB : list block)
      x1 t0 t1 t2 x9 (a1v a2v : word) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem),
    diag_args d mm a1v a2v (usp0 - 6144513) (usp0 - 128) ->
    BASE' mm -> RHEAP s LB mm -> ps_so s = stdout_init -> frm0 fc ->
    (forall ms', pat_exit 2 s ms' -> implM usegs K s Q ms') ->
    implM usegs (s_diag d ;;; K) s Q
      (GST 0x13000 x1 t0 t1 t2 x9 (Z_to_bv 64 0x2b568) a1v a2v x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until mm. intros DA BA HP SO FRM HK.
    pose proof (sp_facts sp0 argv envp VSP) as SF. unfold LO in SF.
    pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & TR). unfold LO in ST.
    unfold implM. iprefix. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s Q msx) end.
    eapply implM_bind.
    { eapply (FPR d) with (lo := usp0 - 6144513) (canary := CAN);
        [exact FWX| exact SWF| apply stderr_file0_wfile; exact SE| reflexivity| rewrite unsigned_lit by lia; replace (usp0 + -128) with (usp0 - 128) by lia; exact DA
        | rewrite unsigned_lit by lia; exact ST
        | rewrite unsigned_lit by lia; unfold FPRINTF_DEPTH; lia| unfold GLOBALS_TOP; lia| rewrite unsigned_lit by lia; lia
        | apply (RHEAP_ssp _ _ _ HP)| exact MI| exact FRM]. }
    cbv beta. intros [] st' ms' PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc' & m2 & -> & MUc & WMc & MI2 & FRM2 & FEQ & ST2 & SEW & SSP2 & ->).
    ua. rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x13004)) with (Z_to_bv 64 0x13004) by (symmetry; rpc).
    pose proof (magree_of_munch usegs _ _ _ MUc WMc) as AG.
    assert (OUT2 : forall a, (0x10000 <= a < 0x5d000 /\ ~ (0x2b568 <= a < 0x2b568 + 232)) -> (fun a0 : Z => outside [(usp0 - 6144513, usp0 + -128); (0x2b568, 0x2b568 + 232)] a0) a).
    { intros a Ha. cbn. lia. }
    eapply implM_evt; [| intros ms'' H; apply HK; exact H].
    zstep.
    eapply (exit2_tail sp0 argv envp TID VSP HT s LB).
    - unfold LO. replace (usp0 - 6144513) with (usp0 + -6144513) in ST2 by lia. first [exact ST2 | replace (usp0 + -6144513) with (usp0 - 6144513) in ST2 by lia; exact ST2].
    - eapply (RSTAT_agree TID _ _ _ AG); [intros a Ha; apply OUT2; unfold rstat_addr in Ha; lia| exact RS].
    - eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP| exact MUc| exact WMc|].
      constructor; [left; cbn [fst snd]; atop_facts; lia|]. constructor; [| constructor].
      right; left. cbn [fst snd]. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. lia.
    - rewrite SO. eapply (stdout_file_agree _ _ _ _ AG); [intros a Ha; apply OUT2; unfold stdout_addr in Ha; lia| exact SOF].
    - apply stderr_wfile_file. exact SEW.
    - exact MI2.
  Qed.

  (* [comment removed for export] *)
  Lemma fwrite_exit : forall {R} (K : M PState R) (Q : R -> PState -> machine_state -> Prop) (s : PState) (LB : list block)
      x1 t0 t1 t2 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem),
    BASE' mm -> RHEAP s LB mm -> ps_so s = stdout_init ->
    (forall ms', pat_exit 2 s ms' -> implM usegs K s Q ms') ->
    implM usegs (s_diag DOom ;;; K) s Q
      (GST 0x13024 x1 t0 t1 t2 x9 (Z_to_bv 64 S_OOM) (Z_to_bv 64 19) (Z_to_bv 64 1) (Z_to_bv 64 0x2b568) x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until mm. intros BA HP SO HK.
    pose proof (sp_facts sp0 argv envp VSP) as SF. unfold LO in SF.
    pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & TR). unfold LO in ST.
    unfold implM. iprefix. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s Q msx) end.
    cbn [s_diag]. change (concat pieces_oom) with s_oom.
    eapply implM_bind.
    { eapply (FWR) with (lo := usp0 - 6144513) (canary := CAN) (s := s_oom);
        [exact TOW| apply stderr_file0_wfile0; exact SE| rewrite unsigned_lit by (unfold S_OOM; lia); apply rodata_bytes; [exact MI| apply s_oom_ro| unfold S_OOM; lia| unfold S_OOM, s_oom, zlength; cbn; lia]
        | apply str_range || (unfold s_oom; apply Forall_app; split; [apply str_range| constructor; [lia| constructor]])
        | unfold s_oom, zlength; cbn; lia| reflexivity| reflexivity| reflexivity
        | rewrite unsigned_lit by lia; exact ST
        | rewrite unsigned_lit by lia; unfold FWRITE_DEPTH; lia| unfold GLOBALS_TOP; lia
        | rewrite unsigned_lit by lia; lia
        | rewrite !unsigned_lit by (unfold S_OOM; lia); unfold S_OOM, s_oom, zlength; cbn; lia
        | rewrite !unsigned_lit by (unfold S_OOM; lia); unfold S_OOM, s_oom, zlength; cbn; lia
        | rewrite !unsigned_lit by (unfold S_OOM; lia); unfold S_OOM, s_oom, zlength; cbn; lia
        | apply (RHEAP_ssp _ _ _ HP)| exact MI]. }
    cbv beta. intros [] st' ms' PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MUc & WMc & MI2 & ST2 & SEW & SSP2 & ->).
    ua. rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x13028)) with (Z_to_bv 64 0x13028) by (symmetry; rpc).
    pose proof (magree_of_munch usegs _ _ _ MUc WMc) as AG.
    assert (OUT2 : forall a, (0x10000 <= a < 0x5d000 /\ ~ (0x2b568 <= a < 0x2b568 + 232)) -> (fun a0 : Z => outside [(usp0 - 6144513, usp0 + -128); (0x2b568, 0x2b568 + 232)] a0) a).
    { intros a Ha. cbn. lia. }
    eapply implM_evt; [| intros ms'' H; apply HK; exact H].
    eapply (exit2_tail sp0 argv envp TID VSP HT s LB).
    - unfold LO. replace (usp0 - 6144513) with (usp0 + -6144513) in ST2 by lia. first [exact ST2 | replace (usp0 + -6144513) with (usp0 - 6144513) in ST2 by lia; exact ST2].
    - eapply (RSTAT_agree TID _ _ _ AG); [intros a Ha; apply OUT2; unfold rstat_addr in Ha; lia| exact RS].
    - eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP| exact MUc| exact WMc|].
      constructor; [left; cbn [fst snd]; atop_facts; lia|]. constructor; [| constructor].
      right; left. cbn [fst snd]. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. lia.
    - rewrite SO. eapply (stdout_file_agree _ _ _ _ AG); [intros a Ha; apply OUT2; unfold stdout_addr in Ha; lia| exact SOF].
    - apply stderr_wfile0_file. exact SEW.
    - exact MI2.
  Qed.
End B.
End CANSEC1.
