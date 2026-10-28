(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp FseReadSound HufPure_FseReadBridge HufPure_FseDecompRT.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells AProto AMalloc_iface AFake0k_iface AF_fse_rd_iface
     AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm AF_huf_fdw_seg AF_huf_tbl_iface AF_huf_tbl_iface2 Stdio_kit AHarness_iface
     AF_huf_fdw_kit AF_huf_bdt_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require ABytes.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require RF_huf_fdw_tk RF_huf_bdt_model RF_huf_fdw_sm RF_huf_tbl_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_tbl_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_fdw_top1 () := "C46Stdlib5Lists4List2hdC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rI46Stdlib5Lists4List5NoDup00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_seg4SPAfK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface5AHEAPC5ARocqVerifyHarness?AgentSubmission5BothW=AFake0k_iface9fake0_lekC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_addrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_sizeC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_topC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC56Stdlib6ZArith6BinInt1Z3powc5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top19fdw_frameK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C56Stdlib6ZArith6BinInt1Z6shiftrC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_layoutC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_botC56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7al_fakec5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top1:spaf_propsC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:AI_aci_imgI47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface3aciC46Stdlib5Lists4List2InC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_aci_loC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:AI_rtcellsC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8artcellsK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell04C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_relroC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm<rd_got_cellsC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_seg4FRBfI47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8rng_sub'C5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_seg7fdw_proC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface=aclient_rangeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_ifaceAaclient_app_rangeK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind02K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface<aclient_addrC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree?magree_of_munchC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm@stack_not_clientK47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree;magree_monoC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree6magreeC5ARocqVerifyHarness?AgentSubmission5BothW=AFake0k_iface9sm0k_postC5ARocqVerifyHarness?AgentSubmission5BothW=AFake0k_ifaceDstack_malloc_0k_stmtC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:aheap_presC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_evenC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8ablk_linC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface?AI_blocks_nodupC47Corelib4Init5Logic9False_indK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_ifaceBAI_blocks_disjointC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_ifaceCaheap_pres_rw_cellsC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface>aheap_pres_stkC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm9aca_monoAC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree<magree_transC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib7InitMem:rw_bytes_bC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm;relro_wordAC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsK46Stdlib9micromega=RingMicromega5Psatz07C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C47Corelib5Lists7ListDef6firstnC47Corelib5Lists7ListDef5skipnC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_seg5FDHDRI47Corelib4Init5Logic2or00K47Corelib4Init5Logic2ex01C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8shad_divC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm>app_not_clientC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asmAshadow_not_clientC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asmAmagree_munch_stepK46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waK47Corelib4Init9Datatypes6option01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=stk_transportC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_seg7fdw_hdrC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF8evtF_cutC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4al_UC47Corelib4Init9Datatypes6lengthI47Corelib4Init5Peano2le00C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;a_space_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<al_space_begC47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega=RingMicromega5Psatz05I5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_seg;AGOT_SUAR_RC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_seg9AGOT_RDPCI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_seg4FDSHI47Corelib4Init5Logic4True00I5ARocqVerifyHarness?AgentSubmission5BothW5ABase7alayout00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintI5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6astate00c5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top1>FDW_OPEN_STACKC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3ATPC5ARocqVerifyHarness?AgentSubmission5BothW5ABase5AUMAXC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow4KENDK47Corelib4Init5Logic4True01C5ARocqVerifyHarness?AgentSubmission5BothW=AFake0k_iface:SM0K_STACKC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9ARELRO_LOC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9ARELRO_HIC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_seg:AGOT_FDWPCc5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top14PAGfC47Corelib5Lists7ListDef6repeatC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecompCfse_decompress_wkspc5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top15dresAC5ARocqVerifyHarness?AgentSubmission5BothWAAF_huf_tbl_iface2@fse_decomp_postAC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_fdw_seg7fdw_epiC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm;byte_of_c1AC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm>mem_eq_singleAC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm9aheap_eqAI5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01C47Corelib4Init9Datatypes3appK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind01C47Corelib4Init3Nat3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List:length_mapC46Stdlib5Lists4List:length_appC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2C5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_asm7res_sepC5ARocqVerifyHarness?AgentSubmission3Lib3Arr?u8arr_transportK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res02K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res03K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res04C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_doneC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9in_rangesC46Stdlib9micromega;ZifyClasses7rew_iffC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith6BinInt1Z3minC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow7gran_okC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow4svalC56Stdlib6ZArith6BinInt1Z8min_specC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow8sval_litC5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_mem@rd_rw_cells_appAI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00c5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top1:fdsh_splitC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedc5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top1;unp_of_c1_4C5ARocqVerifyHarness?AgentSubmission4SpecCHufPure_FseDecompRT9dtable_okC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp;dt_tableLogC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp8dt_cellsC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp;dt_fastModeC5ARocqVerifyHarness?AgentSubmission4SpecCHufPure_FseDecompRT7cell_okC5ARocqVerifyHarness?AgentSubmission5Plain=RF_huf_fdw_sm8cells_okC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp9dc_symbolC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp9dc_nbBitsC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp;dc_newStateC46Stdlib5Lists4List;Forall_implI47Corelib5Lists7ListDef6Forall00I5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp5dcell00I5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp6dtable00C56Stdlib6ZArith6BinInt1Z6eqb_eqc5ARocqVerifyHarness?AgentSubmission5BothW?AF_huf_fdw_top1:wksp_machAC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecompHFSE_DECOMPRESS_WKSP_SIZEC56Stdlib6ZArith6BinInt1Z3eqbC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit8all_fromC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit;brute_range".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= bdtA_acc_hint.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

Lemma spaf_props : forall SP, SP mod 16 = 0 -> SP - 272 <= SPAf SP <= SP - 256 /\ SPAf SP mod 32 = 0.
Proof.
intros SP H. unfold SPAf. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Definition FDW_OPEN_STACK : Z := 272 + 4096.

Section Asm.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis FFLAG : fake_flag_law AI fflag.
Hypothesis FREL : fake_release_law AI fflag.
Variable kk : nat.
Hypothesis SM0K : stack_malloc_0k_stmt AI fflag rng_fs kk.
Notation FB0 F := (mkABlock (ABFake 0) F 64).

(* [comment removed for export] *)
Definition fdw_frame (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock) (m m3 : amem)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (SPV lo FF : Z) (junk : list byte) : Prop :=
  FF mod 64 = 0 /\ ablk FF (FF + 64) /\ FF + 64 <= ATOP /\ rng RNG FF 64 /\ rng RNG (shad FF) 8
  /\ (forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF)
  /\ AHEAP AI L RNG st (FB0 FF :: LB) m3
  /\ magree bsegs (aclient_addr CI LB SPV) m m3 /\ mem_inv bsegs m3
  /\ rw_cells bsegs m3 (SPV + -104) (FRBf ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
  /\ rw_cells bsegs m3 FF (FDHDR FF (fflag L 0 FF) (firstn 24 junk) (skipn 28 junk))
  /\ rw_cells bsegs m3 (shad FF) FDSH
  /\ stk bsegs m3 lo (SPAf SPV) /\ stk bsegs m3 (SPAf SPV + 152) (SPV + -104).

(* [comment removed for export] *)
Lemma fdw_open : forall (L : alayout) (RNG : footprint)
    (ra gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock)
    (SPV DST dcap S size maxLog W wks lo : Z) (Q : machine_state -> Prop),
  AHEAP AI L RNG st LB m -> fake0_lek kk LB ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  stk bsegs m lo SPV -> ATOP + 4096 <= lo -> lo <= SPV - FDW_OPEN_STACK ->
  SPV + 16 < al_top L -> SPV mod 16 = 0 ->
  mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_fs L RNG ->
  0 <= wks < 2^64 -> 0 < W < 2^47 -> W mod 8 = 0 ->
  (forall (FF : Z) (m3 : amem) (junk j8 j64 j80 : list byte) (y5 y6 y7 y11 y12 y13 y14 y15 y17 y28 y29 y30 y31 : word),
     wks < 512 ->
     fdw_frame L RNG st LB m m3 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV lo FF junk ->
     rw_cells bsegs m3 (SPAf SPV) [CB 48 j8; C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 2147450880); CB 8 j64; C8 (Z_to_bv 64 FF); CB 72 j80] ->
     evtF bsegs RNG Q
       (MS (mkR (Z_to_bv 64 0x981e8) (Z_to_bv 64 (SPAf SPV)) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPAf SPV))
                (Z_to_bv 64 (-1)) y11 y12 y13 y14 y15 (Z_to_bv 64 FF) y17
                (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) (Z_to_bv 64 (W + 512)) (Z_to_bv 64 dcap)
                (Z_to_bv 64 size) (Z_to_bv 64 W) (Z_to_bv 64 wks) (Z_to_bv 64 S) (Z_to_bv 64 maxLog) s11
                y28 y29 y30 y31)
           FR (Z_to_bv 64 0x98320) fc None m3 (seg_rom bsegs))) ->
  (forall (FF : Z) (m3 : amem) (junk j0' j64 j80 : list byte) (y5 y6 y7 y17 y28 y29 y30 y31 : word),
     512 <= wks ->
     fdw_frame L RNG st LB m m3 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV lo FF junk ->
     rw_cells bsegs m3 (SPAf SPV) [CB 32 j0'; C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DST);
                                   C8 (Z_to_bv 64 2147450880); CB 8 j64; C8 (Z_to_bv 64 FF); CB 72 j80] ->
     evtF bsegs RNG Q
       (MS (mkR (Z_to_bv 64 0x98300) (Z_to_bv 64 (SPAf SPV)) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPAf SPV))
                (Z_to_bv 64 W) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 S) (Z_to_bv 64 size)
                (Z_to_bv 64 0) (Z_to_bv 64 FF) y17
                (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 (W + 512)) (Z_to_bv 64 dcap)
                (Z_to_bv 64 size) (Z_to_bv 64 W) (Z_to_bv 64 wks) (Z_to_bv 64 S) (Z_to_bv 64 maxLog) (Z_to_bv 64 (FF + 48))
                y28 y29 y30 y31)
           FR (Z_to_bv 64 0x969fc) fc None m3 (seg_rom bsegs))) ->
  evtF bsegs RNG Q
    (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 S) (Z_to_bv 64 size)
             (Z_to_bv 64 maxLog) (Z_to_bv 64 W) (Z_to_bv 64 wks) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 0x98160) fc None m (seg_rom bsegs)).
Proof.
intros L RNG ra gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB SPV DST dcap S size maxLog W wks lo Q
  AH LE1 LBH ST BOT LO SPT SP16 MI TP RSTK RI RFS WKS W47 W8 K1 K2.
pose proof atop_range as ATR.
pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
unfold FDW_OPEN_STACK in LO.
pose proof (spaf_props SPV SP16) as (SPAB & SPA32).
pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
pose proof (AI_rtcells AI _ _ _ _ _ AH) as RTC. unfold artcells in RTC.
destruct RTC as (C0 & GOT & RIC & REAL & SHB & SUA & INI & LAY & _).
destruct (rd_got_cells m (AI_relro AI _ _ _ _ _ AH)) as [GSU _].
eapply evtF_cut.
{ eapply (fdw_pro ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV lo);
  first [exact ST| exact MI| exact GOT| exact SHB| exact GSU| exact SUA| exact SP16| eapply rng_sub'; [exact RSTK| lia]
  | exact RI| unfold KEND; lia| lia]. }
cbv beta. intros ms' (m1 & k0 & k56 & -> & MU1 & WM1 & MI1 & FRB1 & FRA1 & STL1 & STG1).
clear C0 GOT RIC REAL SHB SUA INI LAY GSU.
assert (AH1 : AHEAP AI L RNG st LB m1).
{ eapply (AI_frame AI); [exact AH| exact MU1| exact WM1|]. constructor; [| constructor]. left; left. cbn. lia. }
assert (MG1 : magree bsegs (aclient_addr CI LB SPV) m m1).
{ eapply magree_mono; [eapply magree_of_munch; [exact MU1| exact WM1]|]. intros a Ha. cbn. split; [| exact I].
  intros Hr. exact (stack_not_client CI LB SPV (SPV - 272) a HCI HCI0 LBH ltac:(lia) Hr Ha). }
clear MU1 WM1.
eapply evtF_cut.
{ pose proof SM0K as SMC. unfold stack_malloc_0k_stmt in SMC. eapply SMC with (lo := lo); clear SMC;
  rewrite ?(unsigned_lit (SPAf SPV)) by lia;
  first [exact AH1| exact LE1| exact MI1| exact STL1| exact TP| reflexivity| exact RSTK| exact RI| exact RFS| lia| unfold SM0K_STACK; lia]. }
cbv beta. intros ms' PO.
destruct PO as (FF & z5 & z6 & z7 & e11 & e12 & e13 & e14 & e15 & e16 & e17 & z28 & z29 & z30 & z31 & m2 & j0 & j1 & j2 & junk
  & -> & MI2 & ST2 & HPR2 & AH2 & F64 & FH & FC & FFC2 & SHF2 & RFF & RSFF).
rewrite ?(unsigned_lit (SPAf SPV)) in ST2, HPR2 by lia.
rd_retlit.
pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
assert (NFB : ~ In (FB0 FF) LB).
{ pose proof (AI_blocks_nodup AI _ _ _ _ _ AH2) as NDx. inversion NDx as [|x l NI0 N3]. exact NI0. }
assert (FFD : forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF).
{ intros b Hb. assert (NE : FB0 FF <> b) by (intros E; apply NFB; rewrite E; exact Hb).
  pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH2 ltac:(left; reflexivity) ltac:(right; exact Hb) NE) as D. cbn in D. lia. }
pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRB1 ltac:(left; left; cbn; lia)) as FRB2.
pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRA1 ltac:(left; left; cbn; lia)) as FRA2.
pose proof (aheap_pres_stk _ _ _ _ _ _ _ HPR2 STG1 ltac:(lia) ltac:(lia)) as STG2.
assert (MG2 : magree bsegs (aclient_addr CI LB SPV) m m2).
{ eapply magree_trans; [exact MG1|]. eapply magree_mono; [exact HPR2|]. intros a Ha. eapply aca_monoA; [exact Ha| intros b Hb; exact Hb| lia]. }
clear MG1 HPR2 FRB1 FRA1 STG1 STL1 MI1 AH1.
assert (GPC2 : rw_cells bsegs m2 AGOT_FDWPC [C8 (Z_to_bv 64 0x98160)]).
{ unfold AGOT_FDWPC. apply relro_wordA; [exact (AI_relro AI _ _ _ _ _ AH2)| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]. }
assert (ESH : shad FF = Z.shiftr FF 3 + 2147450880) by (unfold shad, ASHOFF; lia).
assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
  by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
assert (FRM : forall m3, munch [(SPAf SPV, SPAf SPV + 152); (FF, FF + 64); (shad FF, shad FF + 8)] m2 m3 -> wmono bsegs m2 m3 ->
    mem_inv bsegs m3 -> rw_cells bsegs m3 FF (FDHDR FF (fflag L 0 FF) (firstn 24 junk) (skipn 28 junk)) ->
    rw_cells bsegs m3 (shad FF) FDSH ->
    fdw_frame L RNG st LB m m3 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV lo FF junk).
{ intros m3 MU3 WM3 MI3 FFC3 SHF3.
  assert (AH3 : AHEAP AI L RNG st (FB0 FF :: LB) m3).
  { eapply (AI_frame AI); [exact AH2| exact MU3| exact WM3|].
    constructor; [cbn; left; left; lia|].
    constructor; [cbn; right; left; exists (FB0 FF); split; [left; reflexivity| cbn; lia]|].
    constructor; [cbn; right; right; right; right; exists 0, FF, 64; split; [left; reflexivity| try unfold shad;
      rewrite ?Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; unfold ASHOFF; Z.div_mod_to_equations; lia]| constructor]. }
  assert (MG3 : magree bsegs (aclient_addr CI LB SPV) m m3).
  { eapply magree_munch_step; [exact MG2| exact MU3| exact WM3|]. intros a Ha. cbn.
    split; [intros Hr; exact (stack_not_client CI LB SPV (SPAf SPV) a HCI HCI0 LBH ltac:(lia) ltac:(lia) Ha)|].
    split; [intros Hr; exact (app_not_client CI LB SPV FF 64 a HCI HCI0 FH ltac:(lia) LBH FFD ltac:(lia) Ha)|].
    split; [intros Hr; exact (shadow_not_client CI LB SPV FF a HCI HCI0 FH F64 ltac:(lia) LBH FFD ltac:(lia) Ha)| exact I]. }
  pose proof (rw_cells_transport _ _ _ _ _ _ FRB2 MU3 WM3 ltac:(cbn; lia)) as FRB3.
  assert (STL3 : stk bsegs m3 lo (SPAf SPV))
    by (eapply stk_transport; [exact ST2| exact MU3| exact WM3| intros x Hx; left; cbn; lia]).
  assert (STG3 : stk bsegs m3 (SPAf SPV + 152) (SPV + -104))
    by (eapply stk_transport; [exact STG2| exact MU3| exact WM3| intros x Hx; left; cbn; lia]).
  unfold fdw_frame. repeat match goal with |- _ /\ _ => split end; first [exact F64| exact FH| exact FC| exact RFF| exact RSFF| exact FFD| exact AH3| exact MG3
    | exact MI3| exact FRB3| exact FFC3| exact SHF3| exact STL3| exact STG3]. }
eapply (fdw_hdr gp tp s2 s3 s11 FR fc SPV lo); first [exact FRA2| exact FFC2| exact SHF2| exact GPC2| exact MI2| exact FH| exact FC
  | exact F64| exact RFF| exact RSFF| exact SP16| exact RI| exact WKS| exact W8| eapply rng_sub'; [exact RSTK| lia]| lia| idtac].
- intros m3 j8 j64 j80 y11 y12 y13 y14 WK MU3 WM3 MI3 FRA3 FFC3 SHF3.
  exact (K1 FF m3 junk j8 j64 j80 z5 z6 z7 y11 y12 y13 y14 e15 e17 z28 z29 z30 z31 WK (FRM m3 MU3 WM3 MI3 FFC3 SHF3) FRA3).
- intros m3 j0' j64 j80 WK MU3 WM3 MI3 FRA3 FFC3 SHF3.
  exact (K2 FF m3 junk j0' j64 j80 z5 z6 z7 e17 z28 z29 z30 z31 WK (FRM m3 MU3 WM3 MI3 FFC3 SHF3) FRA3).
Qed.

(* [comment removed for export] *)
Definition PAGf (LB : list ablock) (SPV DST dcap W wks : Z) (a : Z) : Prop :=
  aclient_addr CI LB SPV a /\ ~ (DST <= a < DST + dcap) /\ ~ (W <= a < W + wks).

(* [comment removed for export] *)
Definition dresA (DST dcap : Z) (R : res (list Z)) (m2 : amem) (rv : Z) : Prop :=
  match R with
  | Ok l => rv = zlen l /\ exists junk, u8arr bsegs m2 DST (map (Z_to_bv 8) l ++ junk) /\ zlen junk = dcap - zlen l
  | Err e => rv = 2^64 - e /\ 0 < e < 120
  | Ub | NoFuel => False
  end.

(* [comment removed for export] *)
Lemma fdw_close : forall (L : alayout) (RNG : footprint)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m m4 : amem) (st : astate) (LB : list ablock) (SPV DST dcap W wks maxLog lo FF rv : Z) (src : list Z)
    (j0 : word) (csA : list cell)
    (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  AHEAP AI L RNG st (FB0 FF :: LB) m4 ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  FF mod 64 = 0 -> ablk FF (FF + 64) -> FF + 64 <= ATOP -> rng RNG FF 64 -> rng RNG (shad FF) 8 ->
  (forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF) ->
  magree bsegs (PAGf LB SPV DST dcap W wks) m m4 -> mem_inv bsegs m4 ->
  rw_cells bsegs m4 (Z.shiftr FF 3 + 2147450880) FDSH ->
  rw_cells bsegs m4 FF [C8 j0] -> rw_cells bsegs m4 (FF + 56) [C8 (Z_to_bv 64 (fflag L 0 FF))] ->
  rw_cells bsegs m4 (SPV + -104) (FRBf ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  rw_cells bsegs m4 (SPAf SPV) csA -> cells_size csA = 152%nat ->
  stk bsegs m4 lo (SPAf SPV) -> stk bsegs m4 (SPAf SPV + 152) (SPV + -104) ->
  ATOP + 4096 <= lo -> lo <= SPV - FDW_OPEN_STACK -> SPV + 16 < al_top L -> SPV mod 16 = 0 -> rng RNG lo (al_top L - lo) ->
  (exists p A N, In (HB p A N) LB /\ A <= DST /\ DST + dcap <= A + N) -> 0 <= dcap ->
  dresA DST dcap (fse_decompress_wksp (repeat 0 256) dcap src maxLog wks) m4 rv -> 0 <= rv < 2^64 ->
  evtF bsegs RNG (fse_decomp_postA AI L RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB SPV DST dcap W wks maxLog src lo m)
    (MS (mkR x1 (Z_to_bv 64 (SPAf SPV)) gp tp x5 x6 x7 (Z_to_bv 64 SPV) x9 (Z_to_bv 64 rv) x11 x12 x13 x14 x15 (Z_to_bv 64 FF) x17
             (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 FF) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        FR (Z_to_bv 64 0x98320) fc None m4 (seg_rom bsegs)).
Proof.
intros L RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m4 st LB SPV DST dcap W wks maxLog lo FF rv src j0 csA
  x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
  AH4 LBH F64 FH FC RFF RSFF FFD MG4 MI4 SHF4 FF04 FF564 FRB4 FRA4 CS4 STL4 STG4 BOT LO SPT SP16 RSTK HDST DC0 DR RV.
pose proof atop_range as ATR. unfold FDW_OPEN_STACK in LO.
pose proof (spaf_props SPV SP16) as (SPAB & SPA32).
pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
destruct (FFLAG _ _ _ _ _ _ _ _ AH4 ltac:(left; reflexivity)) as (FLC & RG & GH & GC & GBL & GCI).
pose proof (GBL _ ltac:(left; reflexivity)) as GF. cbn [ab_addr ab_size] in GF.
pose proof (ablk_lin _ _ GH) as (GHa & GHb & GHc & GHd). unfold AIMG_HI in GHa.
assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
  by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
eapply evtF_cut.
{ eapply (fdw_epi ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV lo);
  first [exact SHF4| exact FF04| exact FF564| exact FLC| exact FRB4| exact FRA4| exact CS4| exact STL4| exact STG4| exact MI4
  | exact FH| exact FC| exact F64| exact GH| exact GC| exact GF| exact RFF| exact RSFF| exact RG| exact SP16
  | eapply rng_sub'; [exact RSTK| lia]| lia]. }
cbv beta. intros ms' (mp & m5 & -> & MU1 & WM1 & MIp & MU2 & WM2 & MI5 & ST5 & FLC5).
assert (AHp : AHEAP AI L RNG st (FB0 FF :: LB) mp).
{ eapply (AI_frame AI); [exact AH4| exact MU1| exact WM1|].
  constructor; [| constructor; [| constructor]]; cbn.
  - right; right. right; right. exists 0, FF, 64. split; [left; reflexivity|].
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold ASHOFF. Z.div_mod_to_equations. lia.
  - right; left. exists (FB0 FF). split; [left; reflexivity| cbn; lia]. }
pose proof (FREL _ _ _ _ _ _ _ _ AHp) as AHr.
assert (AH5 : AHEAP AI L RNG st LB m5).
{ eapply aheap_eqA; [exact AHr|].
  apply (mem_eq_singleA mp m5 (fflag L 0 FF) (Z_to_bv 8 0)); [lia| lia| exact MU2| apply byte_of_c1A; [exact FLC5| lia]]. }
destruct HDST as (p & A & N & HbD & AD1 & AD2).
pose proof (LBH _ HbD) as HbDk. cbn [ab_addr ab_size] in HbDk.
destruct (res_sep FF (fflag L 0 FF) DST dcap A N AD1 AD2 HbDk DC0 (FFD _ HbD) (GBL _ (or_intror HbD)) (proj1 BSF) (proj2 BSF))
  as [DD1 DD2].
apply evtF_done. unfold fse_decomp_postA. do 14 eexists. exists rv, m5. split; [reflexivity|].
split; [exact MI5|]. split; [exact ST5|].
split.
{ change (magree bsegs (PAGf LB SPV DST dcap W wks) m m5).
  assert (MGp : magree bsegs (PAGf LB SPV DST dcap W wks) m mp).
  { eapply magree_munch_step; [exact MG4| exact MU1| exact WM1|].
    intros a (Ha & _ & _). cbn.
    split; [intros Hr; refine (shadow_not_client CI LB SPV FF a HCI HCI0 FH F64 ltac:(lia) LBH FFD _ Ha); unfold shad, ASHOFF; lia|].
    split; [intros Hr; exact (app_not_client CI LB SPV FF 64 a HCI HCI0 FH ltac:(lia) LBH FFD ltac:(lia) Ha)| exact I]. }
  eapply magree_munch_step; [exact MGp| exact MU2| exact WM2|].
  intros a (Ha & _ & _). cbn. split; [| exact I].
  intros Hr. refine (app_not_client CI LB SPV (fflag L 0 FF) 1 a HCI HCI0 GH ltac:(lia) LBH _ ltac:(lia) Ha).
  intros b Hb. exact (GBL b (or_intror Hb)). }
split; [exact AH5|]. split; [exact RV|].
unfold dresA in DR. destruct (fse_decompress_wksp (repeat 0 256) dcap src maxLog wks) as [l|e| |]; try contradiction.
- destruct DR as (-> & junk & U & ZJ). split; [reflexivity|]. exists junk. split; [|exact ZJ].
  assert (LEN : Z.of_nat (length (map (Z_to_bv 8) l ++ junk)) = dcap)
    by (clear - ZJ; rewrite length_app, length_map; change (zlen junk) with (Z.of_nat (length junk)) in ZJ;
        change (zlen l) with (Z.of_nat (length l)) in ZJ; lia).
  eapply u8arr_transport; [eapply u8arr_transport; [exact U| exact MU1| exact WM1| rewrite LEN; exact DD1]| exact MU2| exact WM2|
    rewrite LEN; exact DD2].
- exact DR.
Qed.

(* [comment removed for export] *)
Lemma unp_of_c1_4 : forall m A, rw_cells bsegs m (shad A) [C1 (Z_to_bv 8 4)] -> A mod 8 = 0 -> 0 <= A -> A + 8 <= 2^47 ->
  unpoisoned m A (A + 4).
Proof.
intros m A H A8 A0 AH.
split; [lia|]. split; [lia|]. intros G H0 H1 H2.
assert (EG : G = A / 8) by (Z.div_mod_to_equations; lia). subst G.
exists (Z_to_bv 8 4). split.
- rewrite shad_div in H. apply (byte_of_c1A m _ _ H). unfold ASHOFF. Z.div_mod_to_equations; lia.
- assert (SV : sval (Z_to_bv 8 4) = 4) by (vm_compute; reflexivity).
  right. rewrite SV, Z.min_r by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia.
Qed.

Lemma fdsh_split : forall m FF, rw_cells bsegs m (shad FF) FDSH ->
  rw_cells bsegs m (shad FF + 4) [C1 (Z_to_bv 8 4)] /\ rw_cells bsegs m (shad FF + 6) [C1 (Z_to_bv 8 4)].
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_fdw_top1 ()) ["CANSEC1"; "Asm"] "h01Hh12H0h22_Hh31mh41Ah54__x1h63cs1h73cs2h84segsh92FFh:2H4h;2H6h<7__arithh=4__ffh>8__varmaph?5__with@1zp;1p;4p;3p;2p;5p;7p;6g004;j15Tg00X:j1JTg00XXj1HTg00Y;j1NTg01Mej11Tg01_0j43Tg00Afj1GTg02[Wj3?Tg01VRj1=Tg01WKj17Tg008Tj20Tg00:PR0j2@Tg02oGj5KTg005^j12Tg004`j1>Tg00_oj2CTg013Mj1BTg00@fj1ITg00BFj2WTg00CBj1VTg00C`j1UTg00EPj2TTg00DKj2ETg00FVj3ATg00LVj4MTg00MAj7OTg00G\j2LTg00H>j2PTg00HXj2QTg00IDj3FTg00I^j3RTg00J=j4STg00=]j1DTg001>j6[Tg01Fdj4ZTg00AFj3XTf0R1#2#2p=Y%21#2#2#2#2#2#2#2p=<g02<9R2f1R3;X1p=:g02;DR4f6R5f5R6f4R7C3P4f3R8f2R9/03P1C3'@p=8P4P9P3P1C3p=9P4P81093P1C3p=4%13/01p=;1093/01p=6g00TAR:#5#5R;#5R<#5#5#5#J#H%J<R<#H#N[R=g00OQR>P4P3%11g02AmC3g030P#GR?%G2R@P0P7P8P9A?231C3P6P7P8P9C3P6P7%=9#7,08P3C3'@[RAP7P8P9P3C3P7P8%=3#7,09P1C3'@P6P7P8A?293C3RB[P5P6P7P8C3P5P6%=8#7,07P9C3'@\BP7P8P9P3P1DKP3n2001000000120000000X7@W6X4>X3=W8RBPA^7@^6@^4>^3=^8?R?P1P4P8%19R=%2:R@#Y#<#<#<#<#<#<#<#5#5RA#5#2#>,C<#BRC%I2RD,:C,:C,:C':RC%>;R;,C<#B/:DRE%2ARA#5#>,C<#B/:DRF%2A#>,C<#B/:DRD9?2ER<5?2RA5?2R2P3O6P8P=PCP8P=%=C#7R=P2F8P0%18R8=97CP7P8P=P2C4P6%17R7/0;PEP6P7%5@#>R@PEF8P1%16=95Cf7%15P=P2C4PBP?P1P4f9R2f8/;=R5PEPAP3O6P2P5PEP2P5%=E#7R5PAF8P0f:RC1;2=R2;9EPCP2P5PAC4f;R2%1CRC/0;PEP2PCP@PEF8P1f<RC%12P=PEC4f=R21;C=P5PAC4PBP?P1P4f?RAf>#1?6=5RCPFP<P3O6PAPCPFPAPC%=F#7RCP<F8P0f@R6%1A?6=5RA;9FP6PAPCP<C4fARA%16R6/0;PEPAP6P@PEF8P1fBR61;A=P5PFC4fC%16?6=5PCP<C4PBP?P1P4fER4fD/;=?65CR?PEPDP3O6P4P?PEP4P?P5PDF8P0fFR01;4=?65CR4;9EP0P4P5PDC4fGR4%10R0/0;PEP4P0P@PEF8P1fHR0%14?6=5PCPEC4fIR41;0=?65CP5PDC4fJRD%14R4P;PEC4104@R5=9DEP2g00TfR2#I%G21W>3%V>%U>R2g00Q4g00QSRCPCg00R3RCP>1T>:R01E>;5A>%>:R:,E>R=5A>=A>=g00PM1E>@9A>0CMg00RSFO1L2CP1P9g00V]RCg00W=R2'P1Q19=FC2dg00Oo=R>3CSb=b>b?X5>101;?6::101@5F>^5>P1%1DRDO1b<g00UR#DR:#D#D#D#7R;,04%7:R:;6:=F>5P>10D;?6::fL?91EX@>P910D@P1E[b0CZW2W;P3P1O2n2111000000121000000b0b1W0W2P3P1O2n2111000000121000000b0b1W0W:P3P1O2n2111000000121000000b0b1W0W2P3P1O2n2111000000121000000b0b1W0W9W3o"). Qed.

Lemma fdsh_unp : forall m FF, rw_cells bsegs m (shad FF) FDSH -> FF mod 64 = 0 -> 0 <= FF -> FF + 64 <= 2^47 ->
  unpoisoned m (FF + 32) (FF + 32 + 4) /\ unpoisoned m (FF + 48) (FF + 48 + 4).
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_fdw_top1 ()) ["CANSEC1"; "Asm"] "h04__x1h17__arithh24__ffh37__sat65h47__sat66h58__varmaph65__with74__x2h84__x3h94__x4h:4__x5h;2H0h<7__sat67h=1zh>2H1h?3H10h@2H2hA2H3hB2H5hC2H7hD2H8hE2H9hF4__p1hG4__x6hH4__x7hI4__x8hJ1HhK2H4hL2H6hM3H11hN3H12hO3H13hP3H14hQ3H15hR3H16hS2HahT7__sat68hU1qhV2q0hW2q1hX1rhY2r0hZ2r1h[2F0h\3F64h]2FFh^2FHh_1ah`1mp%0p&0p;1p;4p;2p;3p;6p;7p;8g004;j1<Tg00X:j1iTg00XXj1mTg00Y;k100Tg01Mej1:Tg01_0j4sTg004`j1CTg005>j21Tg008Tj20Tg005^j1STg00aHj2xTg00:4j2QTg031Ok30FTg00_ok20DTg013Mk10CTg00@fj1rTg00AFj3^Tg00:PR0j29Tg032Tj3]Tg007Zj22Tg006`j2OTg007Aj1lTg0091j2FTg009Xj25Tg00:kj2ETg00;Rj2MTg00<8j2PTg017`j2zTg018Hj3yTg00<^j1wTg00=<j2vTg00=]j1?Tg00><j3YTg01_fk20ETg00>ej2uTg029bj3tTg00?Nj2hTg00@:j2aTg00Afk10BTg019]k10ATg00CBk10?Tg00C`k10>Tg00DKj2qTg00Dnk10=Tg00F3j3XTg00EPj2oTg00G\k20<Tg00H>k20;Tg00HXk20:Tg00IDj3RTg00I^k309Tg00J=k408Tg0087j2dTg01dYj1eTg002Uj6ZTg001>j6kTg018lk304j2jTg01UVj2cTg028Zk603Tg01:;k306Tg033Oj6nTg01Fdk401Tg00Kmj3gTg00BFj2~Tg00Bdj4}Tg00LVj4WTg00MAj7_Tg00Mej6|Tg00FVk30@Tg00NIj8`Tg00Nmj7{Tg00OQR1f0R2g00OoR33Rp=61Q32p=3g02;DR4f2R5f1R6P2Csp=L1056=R12p=;f3R71d56/025R1p=>1Q351562'9p=@1Q23p=HAR162p==1u12p=AAg162p=VAg1629g15p=B1~12p=UP1P5P6P2C}p=G1q12p=IP5g00Q4R8g00QSR9P9g00R3R:P1P6g00PMR;P2CWg00RSR<F_p=NP6P8P9P9P:P2E|p=p1o12p=KB0@162p=4P1P6P;P2CWp=Jf4R;P8P9P9P:P7P5P6P8P9P9P:P2P<F_G`p=8P1P6g00S3P2CWp=\P6P8P9P9P:P2P<F_p=bP5P8P9P9P:P1P6g00SZR=P2CWP<F_p=DP5P8P9P9P:P6P2F{p=fP7P8P9P9P:P5P6P2G`p=Tf6R<P8P9P9P:f5R>P;P7P8P9P9P:P5P6P2G`G`p=71d56/02p>0710629R15p>051562,95p>02P1P6P=P2CWp=[g00TAR=#<R?#<R@#<RA#<#<RB#<RC#i#m%iARD#m$00[P4P6%:2g02AmCs%CCRC,16#6%35107C%C?R4%S?RE#S#S#SS00#CRF'xRG'QB0F>;7%:;RH%C@RI'0g02<9RJ20DDI$0C%rJ3^RJ5L>%S=RD#<RK#CRL,0H=L>J'9P0%:>R0/0I=L<J100L=L<Jf7R0%CBRB,0<RH10HI3]%<K#<#<#CRH,0<RM10MI5]0'9P2f8RM%:0/0I;LJf9RN%:M/0L;LJf:RO10NBRP10PI3]10NHRQ10QI5]OPOPPP1g02A3RR%CARS,2N'0S0110OB#:S029;2IX=1P112PS,0R12OSRT,0RS03?;I2X=11ONSS04%6SRU#lRVPOPSPT11OSC>[S051FOSS06153SRTf;RW/1SRX?@XS[S071EWSS0815S3RXf<RY/1SRZ,5S%HZ'9[S091MYSS0:f=RZ/2S#6\US0;1PZSS0<f>R[/1S/=[\US0=12[SS0>P1f?R\/1SS0?P1f@S0@/0BR]/OSfAS0A/0BR^PS12^SS0B11^SC>\V1F^SfBS0C/0BR_/1SR`?@`S\T1E_SfCS0D/0BRa/1SRb,5S%Hb'9\X1MaSfDRa/0BRb/2S#6\U1PbSfERb/0BRc/1S/=c\U12cSP1fFRc/0B/1SP1fGRd/OCS0E%6CRe#lS0FfHRfPC12fC11fCS0GC>[S0H1FfCS0I153CS0JfIRg/1CRh?@hC[S0K1EgCS0L15C3S0MfJRh/1CS0N,5CQ0N#H'9[S0O1MhCS0PfKRi/2C#6\eS0Q1PiCS0RfLRi/1C/=i\eS0S12iCS0TP1fM/1CS0UP11z4FRi1534%3F153G[[Rj%34Rkg02BkRlAy4F6UWSRF%3G\l^SkRkg00TfRl%w=,v1Rmg00URRn#?Ro#?Rp#?Rq#?S0V#?Rr#?Rs#?S0W#?Rt#ARu5Y1Rv%AqRq%ApRp%AoRo9Y1mRw'V3B20E1SRx1u1nS0X5t1Rn%?t#ARt%AsRs9Y1mS0YAt1xo,VpRx5Bu3Bg00V1Ru'h'a%ArRr/Vw9BvsAY1mq=Brx9Bnt/hu'a%rlRt5^l3^S0Z&0BlRn%UM&0A1Rx7G;%U<7G5%U>S0[%U07G77G6S0\&0?1Rq&0>1RsPs%ICRv1q13Ry5Ns,psS0]&0=9RzPs%KERE%KA9X1v%K@R@'4'JD8S0^PzPsPs%ISRA,\y,bsS0_Pz%SD#KR{9Dsy1\{A,bs5fsCTS0`PzPsPsANsAy,psR|PzPs%IBR},4E%KDRD9X1A/4{S0a'JD8PzPsPsQ0_Pz%KKRK9Dsy1\KA,bs5fsCTS0bPzPsPsP|PzPs%K?R?9X1A/4K,JED8S0cPzPsANs@yS0dPz1o1=R=/4?S0e%II'414=DS0f5NsF7F7F720<s:RKP2P5g00V]R{g00W=R~+0;20:25=R{~dB09136H08R3b2b5b6X01X71X81X91X:1XG1XH1XI1g00W]R~\eS0gP>PCPMP;C>[S0hA@MMS\TS0iP~\UR~B07S>NS0j9;0B[A@NNS\TS0k1dS<S0l>05NO\~S0m%6MS0n10<0S0o10<MS0p7;I[[[[[[^01^71^81^91^:1^G1^H1^I1P2P;POQ0AfQP7PWQ0CPRPNP\Q0@PcPdfOO>S0qb1b3b4bZbWbRbQbPbObNbYbVbMb?bEbDbCbXbUbBbAb@b>b;%:PR{%ePEZ%:NRP%eNS0rEZA;PI{P1%:OS0s/0IALY2JX=1S0tP5Q02P2Ekb;PiPjPFPkB04WCMRM%3C11YC#3[RJ10YBRI/jS%3I%3SRI10[BR{/1SS02#3[[10ZB/OSP{PS12{SQ02C>\V1F{S10\BS02/1SR{?@{S\TQ02/ES11]SR{,5S%H{'9\X1M]SQ0B#6\U1P^S1=`_\Ug02I]R`1c_SR_eP_Q0D/OCS0BQ0FPaPC12aC11aCC>[S0F1FaCS02Q0J11bCR_?@_C[S0J1EbCS0uQ0M11cCR_,5C%H_'9[S0M1McCS0v12dC#6\eS0w1PdCS0xQ0G/=f\eS0GP`1cfCReeS0yPep-0R_Q0YQ0V#A/Vw7BrQ0W#AAY1mr1Vpo3BQ0X,Vo/hu'a'a=^ltS0XPn%U;?G5xQ0[?G7x7G6S0[PqPsPsQ0]PzPsAX1vE/4?,JDD8RxPzPsPsQ0_PzPsP8P9P9P:P0J031\=A,bs5fsCTR:PzPsPsP|PzPs14D}R9AX1A@/4=R@'JD8PzPsPsADsy9PzPsADsyAPzADsy=R9CTR8CTPzPsADsyDPzPsANs?yPzANs=yF7R?F7F7PKP3b2b5b6X01X71X81X91X:1WFQ0gP7PCP>P5C>[R;B0205S\TR510>BRlQ0l/07R7'=\~%3l%3>\IRl[%3<%6<RuPu[[Ru[[[[^01^71^81^91^:1^F_P210hBRo/1SRp#312hCRr12oSPhQ0NPpP<PWPYPZPdPfO<b110gB/1S#6eb?bEbDbCbLbBbKbAb@b>b;bJb3b4b<bTPiPjPFPkPMPJPtPn%U6RpPqPsP9PzPs14=}R},[yD8PKP3b2b5b6X01%32Ro106BRB#3[^01P2PZPOO2Rmb1b3b4b<PiPjPFPkPMPJPtPnPpPqPs14=v%I4Q00#i6061R45DsRvPzPs14}A/[4D8PKP3b2b5b6X01102C/QGRC10BS/QG[^01P2PZPNO2RNb1b3b4b<EnPOPQP1Q0110OH#:RO9;2LX=1P112QS,0RQ03?;L2X=1Q04Q05Q06Q07Q08Q09Q0:Q0;Q0<Q0=Q0>P1Q0?P1Q0@/0HRR/OSQ0A/0HRBPS12BSR}11BSC>\V1FBSQ0C/0HRw/1SR^?@^S\T1EwSQ0D/0HR]/1SR{,5S%H{'9\X1M]S10aHRa/2S#6\U1PaS10bHRb/1S/=b\U12bSP110cH/1SP1Q0EQ0HQ0IQ0KQ0LQ0OQ0PQ0QQ0RQ0SQ0TP1Q0UP1PiPjPFPkQ0ZPnQ0\PqPsQ0^PzPsQ0`PzPsPsP|PzPs%IHRc,4EQ0a'JD8PzPsQ0bPzPsQ0cPzPsQ0dPzQ0e%IL'4Q0f5NsF7F7F7PKP3b2b5b6X01X71X81X91X:1XG1XH1XI1Q0hQ0iQ0j9;0H\~Q0kQ0mQ0nQ0oQ0p7;L[[[[[[^01^71^81^91^:1^G1^H1^I1Q0qb1b3b4bZbWbRbQbPbObNbYbVbMb?bEbDbCbXbUbBbAb@b>b;%:QR0%eQEZPPQ0rEZA;PL0P1Q0s/0LQ0tP6POP2Ekb;PiPjPFPkPMPJ10YHRO/jS%3O10[HR[/1SRO#3\I[10ZH/OSP[PS12[SPOC>\V1F[S10\HR\/1SR[?@[S\T1E\S11RSR\,5S%H\'9\X1MRS%6}\U1PBS1=^w\UP`1cwSRwePwQ0BQ0FQ02Q0JQ0uQ0MQ0vQ0wQ0xQ0GQ0yPeQ0XPnQ0[PqPsPxPzPsP:PzPsPsP|PzPs14DcRD/J@D8PzPsPsADsyDPzP8CTPzP?F7F7PKP3b2b5b6X01X71X81X91X:1XF_10>HR>/=7\~%3>Pl[Pu[[\5\;^01^71^81^91^:1^F_P210hHR_/1SR;#3Pr12_SPhQ0NP;P<PWPYPZPdPfO<b110gH/1S#6eb?bEbDbCbLbBbKbAb@b>b;bJb3b4b<bTPiPjPFPkPMPJPtPnPpPqPsP9PzPs14=cRc,[yD8PKP3b2b5b6X01106HRH#3\o^01Pmb1b3b4b<PiPjPFPkPMPJPtPnPpPqPsPvPzPs14cA/[4D8PKP3b2b5b6X0110HS/QG\C^01PNb1b3b4b<EnH01WLWKP6P2O2n2001000000121000000b_W^W[W\WJX]1W`o"). Qed.


Lemma fdhdr_split : forall m FF FLG j24 j52, rw_cells bsegs m FF (FDHDR FF FLG j24 j52) ->
  rw_cells bsegs m FF [C8 (Z_to_bv 64 0x41b58ab3)] /\ rw_cells bsegs m (FF + 24) [CB 24 j24]
  /\ rw_cells bsegs m (FF + 48) [C4 (Z_to_bv 64 255)] /\ rw_cells bsegs m (FF + 56) [C8 (Z_to_bv 64 FLG)].
Proof.
intros m FF FLG j24 j52 H. unfold FDHDR in H.
assert (RA : forall A A' cs, rw_cells bsegs m A cs -> A = A' -> rw_cells bsegs m A' cs) by (intros; subst; assumption).
apply (proj1 (rw_cells_app _ _ _ [_] _)) in H as [H1 H].
apply (proj1 (rw_cells_app _ _ _ [_; _] _)) in H as [_ H].
apply (proj1 (rw_cells_app _ _ _ [_] _)) in H as [H3 H].
apply (proj1 (rw_cells_app _ _ _ [_] _)) in H as [H4 H].
apply (proj1 (rw_cells_app _ _ _ [_] _)) in H as [_ H5].
split; [exact H1|]. split; [apply (RA _ _ _ H3); cbn; lia|].
split; [apply (RA _ _ _ H4); cbn; lia| apply (RA _ _ _ H5); cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma mg_after_call : forall LB SPV DST dcap W wks m m3 m4 (P : Z -> Prop),
  magree bsegs (aclient_addr CI LB SPV) m m3 -> magree bsegs P m3 m4 ->
  (forall a, PAGf LB SPV DST dcap W wks a -> P a) ->
  magree bsegs (PAGf LB SPV DST dcap W wks) m m4.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_fdw_top1 ()) ["CANSEC1"; "Asm"] "h01ah13DSTh21Hh32HPh42Hah52LBh62M3h72M4h81Ph93SPVh:1Wh;2_Hh<4dcaph=1mh>2m3h?2m4h@3wksp;1p;2p;4p;7p;6p;5g00Afj1ATg004;j11Tg00X:j18Tg00XXj17Tg00Y;j1@Tg00nGj2?Tg01CRj4;j56Tg01H?j4:Tg02N4j79j6=Tg00:4j22Tg008Tj24Tg009Xj25Tg00:PR0j20Tg007Aj13Tg01G?j7<Tg01[@j7>Tg02:K#Ag00OQR1g00TA#1#1#1R2#1#1#1#8#7%82#7#@[R2p-0\1g02;DR3p,2rcR4p,2AI,?4R5f9R6f8R7C;f3R8f2R9C:P3f1R:P8P9C:f<R;f;R<f:R=P6P7f7R>f0R?F9f4R@P:O1[^01P3P;P<P=P6P7P>E=R>f6RAf5RBP@P3P4P5P;P<C;P>PAPBP9f=RAP;P<P=P6P7P?F9P0P4P5f>R0PAP:D612;:14;<,5:'0#312=:14=6,5:'0#3'0P4P5f?R=P0P9D6P?P4P5f@P=P8D612=@14=0,5@'0#312A@14A;,5@'0#3'0P:W;W4P:P?O2n2001000000120000000W2X01F<P3P8P>PBP@P:P?F<F>W3W7W6W8X?2X>2W=X@1X:1X<1X11W9W5o"). Qed.

Lemma pag_rd : forall LB FF SPV SPA DST dcap W wks nW a,
  (forall iv, In iv CI -> snd iv <= AIMG_HI) -> (forall iv, In iv CI -> 0 <= fst iv) ->
  ablk FF (FF + 64) -> ATOP <= SPV -> SPA <= SPV -> nW <= wks ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  (forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF) ->
  PAGf LB SPV DST dcap W wks a ->
  aclient_addr CI (FB0 FF :: LB) SPA a /\ ~ (W <= a < W + nW) /\ ~ (FF + 48 <= a < FF + 48 + 4) /\ ~ (FF + 32 <= a < FF + 32 + 4).
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_fdw_top1 ()) ["CANSEC1"; "Asm"] "h04__x1h14__x2h21Hh37__arithh44__ffh58__varmaph65__with71bh82Hrh94__x3h:4__x4h;2ivh<3DSTh=2FFh>3FFDh?2FHh@3HCIhA4HCI0hB2HDhC3HSAhD3HSPhE2HWhF2HahG2HbhH3HnWhI2LBhJ3LBHhK3SPAhL3SPVhM1WhN1ahO4dcaphP2nWhQ3wksp;1p;2p;3p;7p;5p;4p;:p;?p;8p;6g00Afj1WTg00mgj2tTg00nGj2aTg00oCj3<Tg025Xj3sTg00:4j24Tg0265j3dTg004;j10Tg004`j1:Tg008Tj22Tg00]Mj3OTg00^Bj1ZTg00[]j1rTg00\Uj1pTg01c4j2kTg02N4j7gTg01CRj5;Tg00:PR0j23Tg01>gj1cTg01?`j3CTg00AFj3ATg005^j17Tg007Aj1ITg00IDj3QTg01T1j3^Tg00gPj1]Tg00@fj1\Tg00BFj2PTg019]j1[Tg00Bdj4LTg00CBj1YTg00C`j1XTg00EPj2ETg00Dnj1qTg00G\j2oTg00H>j2nTg00HXj2jTg00I^j3iTg00J=j4hTg01Z>l:fTg00=]j1MTg00>ej2NTg00Kmj3TTg00?Nj2eTg00DKj2DTg01eRl?UTg01Fdj4GTg009Xj2HTg00LVj4VTg00MAj7bTg00NIj8lTg00FVj3mTg00Nmj7`Tg00Mej6_Tf0R1#0#0p=Jf4R2f3R3'4f2R4f1R5/21'H'3#Ip=1%01#0#0#0p=K1251,H4p==1445/31p=9%71#7#7#7p=8%01#0#0#0#0#0#0#0p=Bg00OQR6P5g00SZP1CVp=FP5g00Q4R7g00QSR8P8g00R3R9P1g00RSFbp=5P3P7P8P8P9P4P5P1Glp=?Am651p=6P6P5g00S3P1CVp=>P4P7P8P8P9P5P1F`p=@P5P7P8P8P9P1E_p=S1H51,34p=Rg02:KR7#W1t66R:p,2rcR;p,2AI'aR<9<:1R=As665g02<n'4[];g00OoR>Ad665'4\=^;:f:R:g00TAR=#0R?#0R@#0#JRA#0#:RB,2:5O;%Z;RC/4:f;RD,4:f6REf7'4f@RF9<71%r5RG%p5,2GRH5O;[^77fARI9<7112IB/4G14HI'k[^77PIf?RHf=RGf<RJPDP:f8FgP0P;P<fBRKPFf9RLD;f>RMPLPLPMPGD1PJPLPLPJPDD1'3P;P<%c>RL?CKBfCRN5A7PFP:D;PGP:P:PGPDD1%7=RO#K#:RP,2KRQP:P:PQ%:@R@D1%:ARA,2KRQP:P:PQP@D1'3'3'3P1P;P<fDRQPKPDD;PIPJPJPIPFD1PHPJPJPHPMD1'3P0PKPGPGPKPID1PFPGPGPFPHD1P;P<fFR0=CLBfGRJ5A7PQPMD;PIPMPMPIPHD1120PRRPMPMPRP@D1120ARRPMPMPRP@D1'3'3'3P1PQPHPHPQPND1PNPFPFPNPKD1P;P<fIRR=CLBfJRS5A7RTPJPID;PQPIPIPQPKD1RU12RPRVA=IV@79IRV#IRW12RARXA=IX@79IRX#IRY'3RZ'3P;P<PSPTfHPJPIf5fKRJ9<71ACLJB=Q75fLRL9<75;^1WGX77%];R7%7ORT#8#8#8R[#0#8#8#0#J#K#B#B#:%7[#8#8#0#J#K#B#B#:,4C79CRCg00TfR[#\R\%W[R]P61P64R^P5%[6R_CLR`%Y6Ra%X6Rb1E6=R=1E6?R?'F,5bRc%q8R8PcC?1ob9R9P1P4g00V]Rdg00W=Re'n1j14=QdedAi6>5ChR>b4b5b6X06X161415Re1454Rd[^06^16P1PSPRPMO3b3b2M:fPUPZP7PCg00URRZ#M#MRU#M,N61N6U1N6Z5T65T6g00V1'e=A[\P]P6P^P5P6P_P31P62CLCLPaPb1E6TRT,6=,>?,5b9@bc,SbP8Pb1E6ORO/FT,5bP816=O,>?,5b9@bc,SbC?C?P9P>b4b5b6X06X16X96X:612139Re5g00W]Re[1432A=3429943Pe[[[^06^16^96^:6P1fEPQPNP0P4PGO6b3b2PWPYP;P<PJPRPSPBPKPIPFPHPMPDP:P7PCP\P]P`PaPb1D6P,6=RG/F?,5b1D6@R0,6G,>?,5b5@bP81D6B,6=,>?,5b9@bcRcC?P9P>b4b5b6X06X16121PRPA=5P@795125B9Rd4Rd[^06^16P1PQPLP4O3R4b3b2PEM?UX8VPWeP;P<PJPRPSPBPKPIPFPHPMPDP:P7PCP\P]P`PaPb1D6A,6=R=/F?,5b16=0,>?,5b5@bP8PcC?P9P>b4b5b6X06X16121ARAA=5A@795Pd[^06^16P4b3b2PEM?UX8XPYeCGCGCGWEWBP5P1O2n2001000000121000000W2WFP5P1O2n2001000000121000000W2W>WJWHWCWDW?WAW@XN6XP6XQ6XM6XO6X<6XK6XL6X=6WIo"). Qed.

(* [comment removed for export] *)
Definition DEC_STACK : Z := 2240.

(* [comment removed for export] *)
Definition dres_ok (r : res (list Z)) : Prop := match r with Ok _ | Err _ => True | Ub | NoFuel => False end.

Definition dec_stmtA (PC fm : Z) (fast : bool) : Prop :=
  forall (RNG : footprint) (Q : machine_state -> Prop) (m0 : amem) (SPV FF DST dcap S0 DT lo RLO RHI : Z) (bs : list Z)
         (d : dtable) (gp tp : word) (FR : bvmap 5 word) (fc : bv 32)
         (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 : word) (j48 jd : list byte),
    (* [comment removed for export] *)
    rw_cells bsegs m0 (SPAf SPV + 32) [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 2147450880)] ->
    rw_cells bsegs m0 (SPAf SPV + 80) [CB 72 j48] -> stk bsegs m0 lo (SPAf SPV) -> ATOP + 4096 <= lo ->
    lo <= SPAf SPV - DEC_STACK -> SPV mod 16 = 0 -> SPV + 16 <= 2^47 ->
    zshadow m0 (SPAf SPV + 80) 72 -> shclean m0 (SPAf SPV + 112) (SPAf SPV + 152) RLO RHI ->
    rng RNG (shad RLO) (shad RHI - shad RLO) -> rng RNG (SPAf SPV + 80) 72 -> rng RNG (shad (SPAf SPV + 80)) 9 ->
    rng RNG (SPAf SPV + 32) 32 ->
    (* [comment removed for export] *)
    5 <= dt_tableLog d <= 12 -> zlen (dt_cells d) = 2^(dt_tableLog d) -> RF_huf_fdw_sm.cells_ok (dt_tableLog d) (dt_cells d) ->
    dt_fastMode d = fm ->
    rw_cells bsegs m0 DT [C2 (Z_to_bv 64 (dt_tableLog d)); C2 (Z_to_bv 64 fm)] ->
    bytes_at bsegs m0 (DT + 4) (concat (map fse_cell_bytes (dt_cells d))) ->
    ablk DT (DT + 4 + 4 * 2^(dt_tableLog d)) -> DT mod 4 = 0 -> zshadow m0 DT (4 + 4 * 2^(dt_tableLog d)) ->
    rng RNG DT (4 + 4 * 2^(dt_tableLog d)) -> rng RNG (shad DT) (nshad (4 + 4 * 2^(dt_tableLog d) + DT mod 8)) ->
    (* [comment removed for export] *)
    bytes_at bsegs m0 S0 (map (Z_to_bv 8) bs) -> Forall (fun c => 0 <= c < 256) bs -> zlen bs <= 65536 ->
    ablk S0 (S0 + zlen bs) -> S0 + 8 <= 2^47 -> 16 <= S0 -> unpoisoned m0 S0 (S0 + zlen bs) ->
    rng RNG S0 (zlen bs) -> rng RNG (shad S0) (nshad (zlen bs + S0 mod 8)) ->
    dres_ok (decompress_usingDTable bs d dcap fast) ->
    (* [comment removed for export] *)
    u8arr bsegs m0 DST jd -> zlen jd = dcap -> 0 <= dcap <= 255 -> ablk DST (DST + dcap) -> 3 <= DST ->
    zshadow m0 DST dcap -> rng RNG DST dcap -> rng RNG (shad DST) (nshad (dcap + DST mod 8)) ->
    (DST + dcap <= S0 \/ S0 + zlen bs <= DST) -> (DST + dcap <= DT \/ DT + 4 + 4 * 2^(dt_tableLog d) <= DST) ->
    (S0 + zlen bs <= DT \/ DT + 4 + 4 * 2^(dt_tableLog d) <= S0) ->
    (* [comment removed for export] *)
    mem_inv bsegs m0 -> artcells m0 -> zshadow m0 ABIT_MASK 128 ->
    rng RNG lo (SPAf SPV - lo) -> rng_aimg RNG -> rng_aimg_sh RNG ->
    (* [comment removed for export] *)
    (forall m1 rv (j48' : list byte) (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
       munch [(lo, SPAf SPV); (SPAf SPV + 80, SPAf SPV + 152); (DST, DST + dcap)] m0 m1 -> wmono bsegs m0 m1 ->
       mem_inv bsegs m1 -> stk bsegs m1 lo (SPAf SPV) -> rw_cells bsegs m1 (SPAf SPV + 80) [CB 72 j48'] ->
       rw_cells bsegs m1 (SPAf SPV + 32) [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 2147450880)] ->
       dresA DST dcap (decompress_usingDTable bs d dcap fast) m1 rv -> 0 <= rv < 2^64 ->
       evtF bsegs RNG Q
         (MS (mkR y1 (Z_to_bv 64 (SPAf SPV)) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPAf SPV)) (Z_to_bv 64 rv)
                  y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) y19
                  y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
             FR (Z_to_bv 64 0x98318) fc None m1 (seg_rom bsegs))) ->
    evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SPAf SPV)) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPAf SPV)) x10
               x11 (Z_to_bv 64 (zlen bs)) x13 x14 x15 x16 x17 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880))
               (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 DT) (Z_to_bv 64 (DST + dcap)) x22 x23 x24 x25
               (Z_to_bv 64 S0) (Z_to_bv 64 2147450880) x28 x29 x30 x31)
          FR (Z_to_bv 64 PC) fc None m0 (seg_rom bsegs)).

(* [comment removed for export] *)
Lemma dtok_cellsA : forall msv tl d, dtable_ok msv tl d -> msv <= 255 ->
  RF_huf_fdw_sm.cells_ok tl (dt_cells d) /\ zlen (dt_cells d) = 2^tl /\ dt_tableLog d = tl /\ (dt_fastMode d = 0 \/ dt_fastMode d = 1).
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_fdw_top1 ()) ["CANSEC1"; "Asm"] "h01Hh12Hah24__x1h34__x2h44__x3h54__x4h64__x5h74__x6h84__x7h91ch:2C1h;2C2h<2C3h=2C4h>2FCh?2FMh@2HmhA2LnhB1ThC2_HhD7__arithhE4__ffhF6__sat5hG6__sat6hH6__sat7hI6__sat8hJ8__varmaphK5__withL4cstrhM1dhN3msvhO2tlp;3p;1p;2p;4p;6p;7p;8g034Uj3vTg035\j1NTg036cj18Tg037gj2RTg004;j1=Tg004`j1OTg00aHj24Tg038bj17Tg039ij3Cj4eTg005^j1<Tg00:4j20Tg03:nj2PTg022cj2JTg01WKj1MTg00:PR0j21Tg03;oj1@Tg009Xj2:Tg03=4j12Tg03>9j13Tg02Snj1dTg017`j2ZTg018Hj3YTg00=]j1XTg00>ej2STg00Kmj3WTg00?Nj2cTg00@fj1bTg00AFj3aTg00Afj1`Tg00BFj2VTg00Bdj4QTg019]j1uTg00CBj1tTg00C`j1sTg00FVj3rTg00Dnj1qTg00DKj2UTg00EPj2_Tg00LVj4^Tg00G\j2pTg00H>j2oTg00HXj2nTg00IDj3LTg00I^j3lTg00J=j4kTg03?@j6jTg01Fdj4TTg01c4j2iTg03?`j3mTg008Tj2[Tg00MAj7hTg00Nmj7gTg00NIj8fTg00OQR1f1R2f0R33Lp=5f2R4g00OoR55L1AL123'ip=;g03@AR6?m23p=E1123,14p=If4R7f3R8/44'[1423'0p=610571084'11052/13'1p=?1054/12/13p=G1052/13p=F%72=L13p=>1053p=91_13p=DP1P2g00SZP3C^p=BP2g00Q4R9g00QSR:P:g00R3R;P3g00RSFhp=AP4P9P:P:P;P2P3Fgp=HP8P9P:P:P;P4P2P3Gfp=K1[42/03p=\1023,14p=]g03ADAv423P0%N2/54%82R9,R6g00TAR<#=R=#OR>/44'5%72R?%O<R@7;?AC84?/E93I%<<R9#<#<#<#<#<#<#OR?,07%88RA,P71J6A#M14>7'5%N8/57RA%78RB?;B@'13I[P3%87RB,R6f5RC,4>'5%77RD?;D@f6RE?CCD/EB3IP0%8CRB,R614>E'5%7CRD?;D@f7RF?CED/EB'1f8RB/0?%8FRD,PB1J6D#M14>BRG'5%NF/5B%7FRH?;H@'13I[P31R6D/5G%7BRG?;G@f:RDf9RH;CG%8B'E'1P0%7HRG?;G@f;RI?CDG%8H'Ef<RG/0?%8IRJ,PG1J6J#M14>G'5%NI/5G%7IRJ?;J@RJ'13I[P3f>RKf=RL%7G3C%8G'Ef?RM/0?%8KRN,PMRO1J6N#M14>M'5RP%NK/5MRQ%7KRR?;R@RS'1RT'1P6f@RU?CMR%@3RR%==RV#=#=#=#=#=#=#ORW,:R%23RRPRPU%33RXPXP>PRP>PUD6D?3GX96fARRPU%7MP3CeP0%@2RXfBRY,0X'F%22RXPXPR%32RZPZP>PXP>PRD61>U@%24RU,0@['1D?%@4RX1:XWPUPUPY%34RXPXP>PUP>PYD6D?3GP3%@8RYfDRU,0Y'F%27RYPYPU%37RXPXP>PYP>PUD6fCRY/>@%2CRX,0@['1D?P0fERZ,0X,FX%3CR[P[P>PXP>PZD61>U@%2ERX,0@['1'F%@ER[1:[WPXPXfFR[%3ER\P\P>PXP>P[D6D?3GP3%2FRXfGR\,0X'F%3BRXPXP>%2BP>fHRXD61>\@%2HR],0@['1'FP0%3HR^#9P^P>P]P>fID61>X@%2DR],0@['1%@DR^1:^WP]P]fJR^%3DR_P_P>P]P>P^D6D?3GP3%3I#9%3GP>%2GP>fLRGD6fK/>@%2LR^,0@['1P0%3LP>P^P>fMD61>G@%2KRG,0@[%@KR^1:^WPGPGfNR^%3KRKPKP>PGP>P^D6D?3GP3%3MP>%2MP>fOR^D61>^@%2R,0@[fP#8,J6R@#d%M@#9fR,Z>1:5>R@fS#9fT,4>,:5[[%9>RRg02BkR^fURG=Y>2UW114>G#9\^^1R%2U,Z>%2Z#9%2[,4>,:5[\@%2\R@=Y>2V^X1R14>@R[#9\^^1Rg00TfRRg00URR^#XRZ#X,S11S1Z1S1^5W15W1g00V1'c%bR3a%`RP1P11V17P41V1ECQP2P1P11V1FPC%u1RRCQP8PRCQCQ%t1%s1RR%DVR^%<=#D5r1%=9#D'B,ARRZ%q:R:PR1U15RU/B^,ARR^P:PR%D=R=,BU,AR%D9,B=,AR5HRR=P:PR1_1<R<,BU,ARRU%<V#DRV,B<,AR5HRP:PR1U1?,BV,ARP:P1P<g00S31U1WC^,AR9HRUAHR^Z9HR=5HRCKCKCKCKCK1pR;P3P4g00V]RRg00W=R;'o1n34=LR;dAl152CkbEbJbKX21X31X41X51X61X71X81A\87C%97%98R5?]87A]58H10D?1:CWPEPEPFPBA\BHDD?5GC[[[[[^21^31^41^51^61^71^81P3fXfWRC,4>P[%3\PCP@%@\PFPIPMPYPXO<bDbFbGbHbIbLWCW=P2P3O2n2001000000121000000W0W<P2P3O2n2001000000121000000W0W;P2P3O2n2001000000121000000W0W:P2P3O2n2001000000121000000W0X96PNP2EjPOePPPTPEPQPSPDP4CTCTCTW@W>X?JP2P3O2n2001000000121000000W0WAP2P3O2n2001000000121000000W0XBAP2P3O2n2001000000121000000W0WMXO1XN1o"). Qed.

(* [comment removed for export] *)
Definition wksp_machA (tl msv : Z) : Z :=
  Z.land (Z.land (Z.land (bv_swrap 32 (1 ≪ (tl mod 32))) 18446744073709551615 ≪ 2 + 1 ≪ Z.land tl 63 +
                  Z.land ((msv + 1) ≪ 32) 18446744073709551615 ≫ 31 + 19) 18446744073709551615) 18446744073709551612 + 516.

Lemma wksp_machA_ok : forall tl msv, 5 <= tl <= 12 -> 0 <= msv <= 255 ->
  wksp_machA tl msv = FSE_DECOMPRESS_WKSP_SIZE tl msv.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_fdw_top1 ()) ["CANSEC1"; "Asm"] "h02Hth11Hh27__arithh32tlh41vh54__x1h64__ffh78__varmaph85__with91mh:1nh;1Ch<2Hmh=3msvp;1p;2p;3p;4p;7p;8p;6g004;j13Tg005^j15Tg004`j14Tg00:4j2@Tg00@fj1^Tg00Afj1[Tg00BFj2WTg00CBj1UTg00C`j1QTg00EPj2OTg00Dnj1bTg00G\j2]Tg00H>j2\Tg00HXj2ZTg00I^j3XTg00J=j4VTg03BHj2TTg03Bhj2ETg03Cmj2DTg00jGj1RTg00DKj2JTg00FVj3STg00LVj4ITg008Tj2gTg009Xj2fTg00:PR0j2BTg00MAj7NTg00Nmj7eTg029>j7dTg00NIj8aTg00IDj37Tg01c4R1j2FTg03EAj2GTg03E^j3`Tg03F[j6cTg002Uj7_Tf3R2f2R3'@f1R4f0R5'@'Bp=81@45,B3p=Mg00OQR6/J5p=6P6P4g00SZP5CIp=CP4g00Q4R7g00QSR8P8g00R3R9P5g00RSR:FNp=AP3P7P8P8P9P4P5Fep=HP3P7P8P8P9P6P4g00PMP5CIP:FNp=9P3P7P8P8P9P4P5Fdp=?P2P7P8P8P9P3P4P5Gap=Lg00V]R7g00W=R:775p=YA7623A7645'Fp=>f4R;=762A7634/F5'Fp=11G45=77:p=KA7645p=01E231D45'G=77:p=21@34/B5p=P1E231D45'Gp=<g00OoR<=`45=77:p=:P;P<P2P3P4P5Ecp==P6f5R=P;P2P3P4P5F_p=;g00TAR>#3R?#5R@#4RAP4P4%5>RB#3RC#3#4RDC81@<4RE%5BRB#5#5#5#5#5#4RF7M4g00TfRG#^RH%[GRG1W64RI%U6RJ%Q6RK%6ARL1O6>R>'C,AK%6DRM,C>,AK5HK%b8R8A9K>L%4CRC#699K>%4BRB#699K>%3?R?#3RL#4RN#699K>%5?#4R?#699K>%3@#4RO#699K>%5@#4R@#699K>A9K>M5?K5?K5?K5?K5?K5?K5?KCL1]K9R9P5P31\7:R:1Z53#YdAX6<4CVR7b6b7b8X56PAP5P5PDC8RMP4PAP4PCP4PBP4PNP4P?P4POP4P@P4PDC>D1D1D1[^56P5P;P3O2b2P2PAP2PCP2PBP2PNP2P?P2POP2P@P2PDC>D1D1D1P01K451034[R010451K34RP[1023\P1T45P4n2001000000120000000X96X:6P0^96^:6P51E=;1D=;P110=AP=PCP=PBP=PNP=P?P=POP=P@10=DD1D1D1f6R;P=P;P=C2P410;APAP4f8R0P4P0C2^0MX361@ADRP9PAAPAP5PAP5C<X46R3%3L#3#3#3#3#4RLP:%RLR2,:3df7R3PHPGPIPJPK1J6<RJ/C>,AKRI%6F,C>,AK5HKP8P6P>g00S3%6L9S6JCI,AK9HKICLP9P7b6b7b8X56R7P<P5P5PFC81g<L,f4,BE[^56REP5P0P;O2b2D=W0P3P5P=E;W1P5O1P;PCP;PBP;PNP;P?P;POP;P@10;DD1D1D1P1103CP3PBP3PNP3P?P3POP3P@P3PDC>D1D1P0P3P0P3C2P5100CPCP4f:R;P4P;C2^0MX36PAPCPCPDC8PCP5PCP5C<X46RCPLP:1:C2df9RCP7PEP5P;P0O2b2D=W0PCP5P3E;W1P5O1P0PBP0PNP0P?P0POP0P@P0PDC>D1D1P110CBPCPNPCP?PCPOPCP@10CDD1D1P;PCP;PCC2P510;BPBP4f<R0P4P0C2^0MX36PAPBPBPDC8PBP5PBP5C<X46RBPLP:1:B2df;RBP7PEP5P0P;O2b2D=W0PBP5PCE;W1P5O1P;PNP;P?P;POP;P@10;DD1D1P110BNPBP?PBPOPBP@PBPDC>D1P0PBP0PBC2P5100NPNP4f>R;P4P;C2^0MX36PAPNPNPDC8PNP5PNP5C<X46RNPLP:1:N2df=RNP7PEP5P;P0O2b2D=W0PNP5PBE;W1P5O1P0P?P0POP0P@P0PDC>D1P110N?PNPOPNP@10NDD1P;PNP;PNC2P510;?P?P4f@R0P4P0C2^0MX36PAP?P?PDC8P?P5P?P5C<X46R?PLP:1:?2df?R?P7PEP5P0P;O2b2D=W0P?P5PNE;W1P5O1P;POP;P@10;DD1P110?OP?P@P?PDC>P0P?P0P?C2P5100OPOP4fBR;P4P;C2^0MX36PAPOPOPDC8POP5POP5C<X46ROPLP:1:O2dfAROP7PEP5P;P0O2b2D=W0POP5P?E;W1P5O1P0P@P0PDC>P110O@10ODP;POP;POC2P510;@P@P4fDR1P4P1C2^0MX36RMPAP@P@PDC8P@P5P@P5C<X46R@PLP:1:@2dfCR@P7PEP5P1P;O2b2R1D=W0P@P5POE;W1P5O110;DPDPMAMPDDPDP5PDP5C<X46RDPLP:1:D2dP@P1D=W0P@P5POE;W1P5O1n200100000021100011000W1P5O1n200100000021100011000W1P5O1n200100000021100011000W1P5O1n200100000021100011000W1P5O1n200100000021100011000W1P5O1n200100000021100011000W1P5O1n200100000021100011000O3b1b;W<W0X=6X36o"). Qed.

End Asm.
End CANSEC1.
