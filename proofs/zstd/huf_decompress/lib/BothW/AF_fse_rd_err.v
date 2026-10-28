(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas FseAbs FseReaderRT FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_cnt1
     AF_fse_rd_count AF_fse_rd_zero AF_fse_rd_loop.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_fse_rd_err () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission4Spec9FseLemmas9all_bytesK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init9Datatypes4prod00I5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCountAread_ncount_body8C56Stdlib6ZArith6BinInt1Z8leb_specC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3lebI47Corelib4Init9Datatypes8BoolSpec00K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res03C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount8readLE32K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3ltbK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res02C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount5shr32C47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z6to_natK47Corelib4Init9Datatypes3nat02C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount;zero_prefixC56Stdlib6ZArith6BinInt1Z3powC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount;r_remainingC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount9r_charnumC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount:r_bitCountC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4r_ncC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4r_ipC56Stdlib6ZArith6BinInt1Z6shiftrI47Corelib4Init5Logic2eq00C5ARocqVerifyHarness?AgentSubmission6Common9FseRdKit25rd_s0C47Corelib4Init5Logic3notC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit=readLE32_le32C47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC5ARocqVerifyHarness?AgentSubmission4Spec9FseLemmas7land_15C56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init5Logic2or00C47Corelib4Init5Logic7f_equalK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or01C56Stdlib6ZArith6BinInt1Z3divC5ARocqVerifyHarness?AgentSubmission4Spec9FseLemmas8shr32_okC46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init5Logic6eq_symK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega=RingMicromega7Formula01C5ARocqVerifyHarness?AgentSubmission6Common9FseRdKit29rd_s0_invC5ARocqVerifyHarness?AgentSubmission4Spec<FseReadSound3CTLC5ARocqVerifyHarness?AgentSubmission4Spec<FseReadSound3POSC56Stdlib6ZArith6BinInt1Z4succK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib6ZArith4Znat5Nat2Z8inj_succC5ARocqVerifyHarness?AgentSubmission4Spec<FseReadSound;rloop_totalC5ARocqVerifyHarness?AgentSubmission4Spec<FseReadSound3BRKC5ARocqVerifyHarness?AgentSubmission4Spec<FseReadSound3pwsC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00K47Corelib4Init5Logic2or02C47Corelib4Init5Logic9False_indK47Corelib4Init5Logic2ex01C47Corelib4Init9Datatypes6lengthC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount6rstate01K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount5rloopC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4bindC5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit4le32I47Corelib4Init5Logic2ex00K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega6VarMap1t03I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes4bool02I5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount6rstate00I47Corelib4Init9Datatypes4unit00C46Stdlib9micromega5Tauto5eKindK46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCountLZSTD_error_tableLog_tooLargeC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCountRZSTD_error_maxSymbolValue_tooSmallC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCountNZSTD_error_corruption_detectedK47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCountIFSE_TABLELOG_ABSOLUTE_MAXC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount@FSE_MIN_TABLELOGI46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base7rd_invAC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base4a_NCC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit4u16sC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base5a_rt0C5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base5a_BUFC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base5a_bufC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base6a_MSVPC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base5a_SPAC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base3a_mc5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_err:rd_errinvAC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base8FRA_mainC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base5rd_WAC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base4a_loC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base5a_TLPI47Corelib4Init9Datatypes3nat00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base6rdctxA00C5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base:rd_brk_okAC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base6a_msv0C5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base8rd_exitAc5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_err=errinv_of_invC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base7okA_linC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base4a_SPC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC56Stdlib6ZArith6BinInt1Z3mulC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base4a_FFC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base4a_gpC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base4a_tpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base3a_FC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base4a_fcC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSc5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_err@rd_mainA_errpostK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr08C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inK47Corelib5Lists7ListDef6Forall01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK4ELinuxProcessSemantics5Riscv5Instr5instr05C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z3oppC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_doneC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC56Stdlib6ZArith6BinInt1Z6ltb_geC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsK46Stdlib9micromega7EnvRing5PExpr06C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit:signed_litK4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics5Riscv3Sem5alu64C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK4ELinuxProcessSemantics5Riscv5Instr5aluop01I4ELinuxProcessSemantics5Riscv5Instr5instr00C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow4KENDC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base:RDA_CALLEEC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03I47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base8rd_headAK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res04I5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4flow00C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount<rcount_blockC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base>buf_all_bytesAC5ARocqVerifyHarness?AgentSubmission4Spec<FseReadSound<rcount_totalC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base7rd_cntAC5ARocqVerifyHarness?AgentSubmission5BothW?AF_fse_rd_count:count_runAC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount;r_previous0C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount;rzero_blockC5ARocqVerifyHarness?AgentSubmission4Spec<FseReadSound;rzero_totalC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount;r_bitStreamC45stdpp9bitvector;definitions8bv_swrapC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount;r_thresholdC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount8r_nbBitsC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_base7rd_lstAC5ARocqVerifyHarness?AgentSubmission5BothW>AF_fse_rd_zero9zero_runAC47Corelib4Init9Datatypes7nat_indK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4flow02K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4flow01c5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_err7buf_h8Ec5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_err8msv1_okEc5ARocqVerifyHarness?AgentSubmission5BothW=AF_fse_rd_err9loop_runQ".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.
Local Ltac acc_hint ::= rdA_acc_hint.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma read_body8_err_inv : forall buf msv1 nc0 e, all_bytes buf -> 8 <= zlen buf -> 1 <= msv1 <= zlen nc0 ->
  read_ncount_body8 buf msv1 nc0 = Err e ->
  (10 < Z.land (le32 buf 0) 15 /\ e = 44)
  \/ (Z.land (le32 buf 0) 15 <= 10 /\ exists sF, rloop buf msv1 (S (Z.to_nat msv1)) (rd_s0 buf msv1 nc0) = Ok sF /\
        ((r_remaining sF <> 1 /\ e = 20) \/ (r_remaining sF = 1 /\ msv1 < r_charnum sF /\ e = 48)
         \/ (r_remaining sF = 1 /\ r_charnum sF <= msv1 /\ 32 < r_bitCount sF /\ e = 20))).
Proof.
ltac2:(KReplay.run1 (kr_t_AF_fse_rd_err ()) [] "p'0h04__x1h11Eh21Hh37__arithh44__ffh58__varmaph65__with74cstrh85cstr0h95heq_xh:4__p1h;2sFh<1sh=4__x2h>1bi001bh?:bitStream1h@1ei011ehA2e0hB1ri021rhC2b0hD1mhE1ni031nhF1zi041zhG1BhH2B2hI2B3hJ1LhK4__p2hL2b1hM2b2hN9bitStreamhO2s'hP2E1hQ3ES0hR2H8hS2HBhT3HB0hU3HC0hV3HP0hW2HmhX2N1hY2RLhZ2X0h[2_Hh\3_H0h]1ah^3bufh_4msv1h`3nc0ha1xi051xi061pp%0p&0p;1p;2p;3p;4p;6p;7p;>p;5p;9p;8p10000p4p7210g000\R0p4p710p8g001:k10MTg001Zk10}Tg002Wj1?Tg003<j1;Tg003Zj1OTg004:j22Tg004Vk20>Tg0056S00j1wTg005ok30ZTg0074k20|Tg007Vj23Tg0082j2UTg008OS01j3~Tg0093j2TTg009lk10iTg00:ek20hTg00;aj1eTg00<Fj2QTg00<dj20Tg00=Aj26Tg00=^j2CTg00>Wk20=Tg00?Pj2bTg00?nj1JTg00@Nj1FTg00@mj2dTg00Alj2ATg00BIj1zTg00CHk206Tg00Cej1tTg00DCj17Tg00E@j19Tg00F>j1ITg00G6j2\Tg00GSj1hTg00HKj2mTg00Hkj35Tg00IEj38Tg00J@j1WTg00JYj1GTg00K>k10gTg00K^k10fTg00L<k10eTg00LZk10dTg00MEk20FTg00Mhk20cTg00NJk20?Tg00Ndk20bTg00OPk30aTg00Ook40`Tg00Pak20ETg00Q?j2lTg00Qbk10_Tg00RDj3xTg00Rgk40^Tg00Sij6[Tg00TEk20]Tg00TeS02j21Tg00U@k30\Tg00Ugk10[TP0j6iTg00Vbk20<Tg00WDj2DTg00W^j6vTg00X;j4LTg00XVk308Tg00Y0k207Tg00YMk30YTg00ZIk20XTg00Zjk20WTg00[Jk20VTg00[jk40UTg00\Fk10TTg00\dk20STg00]Ek203Tg00]nk30QTg00^Wk30BTg00_@k20PTg00_lk30OTg00`Lk401Tg00a7k70RTg00b6k402Tg00c0j2nTg00cjk10LTg00dHk30{Tg00dkk20zTg00eIk10yTg00emm>0xTg00foj5`Tg00gij2sTg00hck20uTg00iES03k20tTg00ihj3{Tg00jBk20qTg00jak40pTg00k;k20oTg00k[k20mTg00lVm90nTg00mRj4qTg00n2j4jTg00nkj4yTg00ock20HTg010\S04k20lTg0116k70@Tg011Zk80kTg012>k70jTg012bk60vTg013Fk40wTg013dR0f0R1+0op=:f2R2f1R3'2/11p=@f3R41C31752p=N20m01p=cf5R5g014BR6f4R7P4P6P2P3P1g014`S05N90np=_P2P0P3P1Cqp=rP4P0P21031Cqp>00P2P0P3P1Cq,T4p=Eg015@R8P5P7P4P2P3CjP1Cyp=Sg016<R9P2P3P1Cyp=MP0P2P3P1Cyp=Y20H16p=fA5031p=412421131'1,17p=Kf7R:f6R;'11374A5023'1,15/D1'Dp=ZP5P7%J4#FP2Cj=5;3/11p=V20l81p=R1123/D1p>0G%O1,26p=HP2g016\R<P9P9g017;R=P0P3g017[P1H01g018BR>K0@p=Bg018bR?g019BS06751p==20F01p=PP4P<P9P9P=P2P3P1L0kp=>20H36/Q1p=]1261p=kP2P<P9P9P=P0P3g019bP1H01P>K0@p=X1342A5031'1p>0DP5P7P4A8231Cjp>0C1342/13,17/D1p>0;A55741123/D1'1p>0:g01:IR@=501p>0920?01p=^P2P<P9P9P=P3P1K0jp=aP3P<P9P9P=P1J0vp>05%J1#Fp>04P0P2P3P1H0wp=gP3P<P9P9P=P1P>K0@p>0N1131,12p=uP7P4P2P3Cj=551p>0K%z3=501p=<P4P2%J3#FP1Cjp>0JP8P2P3P1Cyp>0I1323/11p=o1223/11,14p=}P7P0P4P0P2P3CqP1Cqp=|A5031,12p>0s11741131,12'Dp>0rg01;YS07=501p>0Ag01<oS08=501p=p&0M0R<&0}4g01>ARA#?RB#?S09#?RC#;RD%:7#O'2%;ARE%:4#O,277@720><0RF00>0RG00>0RH#wRIB0Z;57PHP4CN%c5RJ-0|;12;J13J;1U;J3~%c;,U:P?Q01f8RJ%c:RK'213KJP?%w9RKP31T9>R>&0i9S0:n0110000020000f<RL00h6RMP?PIg01>f%eARN#eS0;#eRO#;RP,Q1g01@3RQ'0'6RR1CH@RSQ09#;RT-0=1RUP?PK1Q3P/0QRV,U6%eO#;RO,6V'bP>Q0:n0110000020000RVPHf?RWf>RX%JXRY#Ff=RZ,dYP3PT%;BRY1Q2P/0QR['AR\/0ER]P\10[ER[E_P?PI%z1R^006E#tR_Q08,CHR`P?PI%71Ra,6WQ07,CHRbP?PI%?CRC#?#;Rc%91Rd'6S0<P`PHPGPF%I11\aE5r<Re1Q4PPQH00%h1Q0;#;RQ,0d%;NRf'm'0S0=CEn0100000020000Rgn0100000020000n0100000020000X<8ESV95MHX?05YHn0100000020001XN0Rh5YHV9S0>5MH1CHJS0?55I%eBS0@#?Ri#;Rj%fLRk/QPRl'3f9RmQ0@#e#?#?#;Rn'4%w8RoPZPLPLf;Rp98ZL1T81Rq14^ER^#WS0Af:Rr%?i#;Ri'4RsP^PLPaPr%?NS0B#?#?#?#;RNP^PaPL13cdS0CPsDKGZFVX;8#R9@lj40G]1P3%cJS0D,2mQ0>9MH>Q0?55I%w0RlPMPIP?PIPRPSPHf@S0EPW%JWRR#FS0F1dRXP3PTP]P\P[E_P?PIP_P`P?PIQ0E/6aPbPgn0100000020000n0100000020000X<8ESV99MHVX?09YHUn0100000020001XN09YH1PHPrCNXBlP11T0kRkPLP6%:rRU#G%HUg01A7S0G$0gRUQ0G$0MRV&0f0Rg&0e0R[&0d0R\20F06R];B]20c\=R=P1P2Q06-0??20b12#=dB0a063H0`RRb4b5b61266P1b3b7%:LRM#GS0H%HMS0I%:pRM#GS0J%HMS0KPUPV20E03RMP[P\%PD1l0ARs5B\S0L&0_9Rd%PTS0M9x0]=B\sC>P=PRb4b5b6X0012D1S0N106T/23[^00P1%:W#OPrO2b3b8b7H0^E[PIAYHkhPHPmCN1]ZPP0P0%fXRk%;CRC+0]%k1S0O131CS0P'1RhXF0Q0HQ0IPUPVPgP[%PCS0Q9X\]P=PRb4b5b6136CP1b3b7:0\kC1QkP&0[kEiPhQ0@#;Rh,03Rk-0<P13Pk12kP16Pk3~102hS0R,6PP?Q01104hRt,3P12tPP?PIP3PSfCRt#f00=TP?PK10;hRu,U616uO'bP>Q0:n0110000020000PHfERufDRv%JvRw#FRx1dwtP3PT10:hRw,AYRy/0EPy10wEE_P?PIP_P`P?PI16uaPbP?PIQ0<P`PHPG10JhRy9rFeQ0=CEn0100000020000n0100000020000n0100000020000X<8ESV95MHX?05YHS0Sn0100000020001Q0E,CHRz55IPjP;fAR{PnH0DS0T12;jS0UPoPuPvPxPuPvPtJ0CPqQ0AfBRx/4iR|P^PvPa14xNP^PaPvQ0CP|DKI0;J0:X;8#RS0V'1S0W'D]1P3107hR|,3PA5ISzQ0TQ0WPIP0Q00PHP0P1PnP1PnPnn101102000410106101040000XAIPS1CH{S0XP1Ev&09{&09xP0P@PjPmP1PnH0DX@013jJ&09nfFR@/]PRS#^14JSRSePSfGRS#:R}#GS0Y%H}S0ZPUPVPMP[P\%PPS0[%PhS0\9x0sR}5X\Pd%PjS0]=X\sC>P=PRb4b5b6X00101hR~,3P13j3[^00P1PpP;O2b3b7b9%^nCLPtP1E[W2P1O1b2408W1WGP1O112|PQ0S=5IzQ0TQ0WQ0UQ0V%fvRz/QPR|#^14;|S0VeS0UQ0V%:uR|#GS0S%H|S0^%:vR|#GS0_%H|S0`PUPVPMP[P\Q0[9B\}S0aPdQ0]9B\sS0]C>P=PRb4b5b6X0012~PS0b123j[^00P1PrP5O2b3b8b7b9Pl20=zTPIP?PK1U6yS0c16yOS0d'bS0eP>Q0:n0110000020000PHPSP@%J@R~#FS0f1d~uS0gP3PT10mhR~,AYS0h/0ES0iQ0h10~ES0jE_P?PIP_P`P?PI16SaPbP?PIQ0<P`PHPG10rhR|9rFeQ0=CEn0100000020000n0100000020000n0100000020000X<8S0kESV95MHX?09YH1PHPxCNXBlP11AYTRl-07z,T0S0lQ0UQ0VQ0SQ0^Q0_Q0`PUPVPgP[Q0M9B\]Q0M%Pc5X\5a\P=PRb4b5b6%kT13Tc'1P1b3b8b7b9:0YzTE[Q0lP?PK1U6w16wO'bRwP>Q0:n0110000020000PHP@Pu%JuRz#F1dzvP3PT1AYyRz/0EPz10yEE_P?PIP_P`P?PI16@aPbP?PIQ0<P`PHPGArFe~Q0=CEn0100000020000n0100000020000n0100000020000X<8ESV95MHX?05YHQ0X55IP?PwQ06Q021b31#=%=2%=3Ry'1Rz[%=1,1y1b23#=[Ry1b42#=\z20X31P1n2001000000120000000XM?XL?Py^M?^L?P1Q0cQ0dQ0c#=Q0d#=Q021U31#=1223Ry[12311U23#=[Rz1U42#=\y20W31P1n2001000000120000000XD0XE0Pz^D0^E0P1P6P~%fSS0d/QPRz#^14mzS0ceS0XQ0cfHRz#:Ry#GS0l%HyS0MQ0YQ0Zp-0RyPUPVPMP[P\AB\]sS0`205\4S0_5a\S0^PdAB\]}C>P=PRb4b5b6X00W:Q0O/13%kk[^00^:yP113ZCPZPLO3b3b8b7b9O3b2Q021631#=1323S0O[1331S0S1623#=[S0VQ0O1642#=[20V31P1n2001000000120000000XD0XE0Q0V^D0^E0P1P~POQ0XQ0cQ0lQ0MQ0YQ0ZPUPVPMP[P\Q0_Q0Q9X\s5a\Pd%PO9X\}C>P=PRb4b5b6X00X:yQ0P,1313kO[^00^:yP1%kZPZPLO3b3b8b7b9O3b2CLO3b2H0UQ06=5?wP?Q0ePIP?PKP1P>Q0:n0110000020000PHPzPS%JSRK#FRw1dK@%fz007lPT1AY|RK/0EPK10|EE_R|P?PIP_P`P?PI16zaPbP?PIQ0<P`PHPGPFPePpPhH00Q0=CEn0100000020000n0100000020000n0100000020000X<8RKESV95MHPHPvCNX>?P3Q06P1EiPIPHPSP@Q0fQ0gQ0d007lPTQ0iQ0hQ0jE_RTQ0kESV99MH>PHPtCN20?8TA8S@u=58TP8P|PIPHfIR|Pz&04zP1P?PIP_P`P?PI16|aPbP?PIQ0<P`PHPGPFPePLPhH00Q0=CEn0100000020000n0100000020000n0100000020000X<8ESPHP@CNXB8P3A8zS@RTP1EiPIPHPzPSPwPTPKESPHPuCNP|PzPSPuPvPt1]|PRK#^14pKRTePTfJRT#:Rw#G%Hw%:|Rw#G%HwQ0G&0TA-0S0g01AcRA#FRw#F-03060Q02030w2030A60B060B0g01BB+0P<0OUPV20E02S0G9gg2?g3gP[P\P0Q0B,l0RAg01BnPsH01-0N\PdP\Q0\9x0AQ0[5B\PdQ0]C>C>P=PRb4b5b6X00X=01431Q0R/2PS0]122j[[^00^=0P1PWfMRA/]PP4PrO4b3b8b7b9K0RPzPS10KhA8|zSRKH021n|K%9K/3c3uQ02P|Pz1]TP/0hA8T|zRKH021nTK%9K/3c'1PofLRKfKRwPwA8KwTR>PqQ0A14|iR9P^PwPaP|PNP^PaPwQ0CP9DKGZFVX;8#RP1PwPT1]KP/0hP>H02A8AKwR>,nA%9>/3c'1Q02fNS0[Q0[?8AKR>'n%9>/3cPofPR>fOR9P9Q0[98>9RlPqQ0A14AiRkP^P9PaPAPNP^PaP9Q0CPkDKGZFVX;8#RP11n>lfQRl?8>9#9/3cfRRkQ0[1]kPRO#^14vOS0BeS0kQ0BfSRO#:R~#GS0j%H~S0h%:kR~#GS0i%H~S0dPUPVPMP[P\Q0LPdQ0LC>P=PRb4b5b6X00Q0N12D3[^00P1fVR~#:#OPlO2b3b8b7b9%ck,2DePlP>Q0kQ0BQ0jQ0hQ0iQ0dPUPVQ0G?g3gP[P\%PES0N=B\sS0L1l0B9B\s5a\RBPdPBC>P=PRb4b5b6X00X=012E1S0g1213'11232S0f9@E3[^00^=0P1fTRB#:#OS0efURDP>O3b3b8b7b9%c>,2l9@Ele10vhQ0kQ0BQ0jQ0hQ0iQ0dPUPVPMP[P\Q0aPdP\Q0^PdQ0\=B\}Q0a5a\C>C>P=PRb4b5b6X00X:yQ0b%k3S0a/12Q0RQ0]5@h[[^00^:yP113zCPzPtPSO4b3b8b7b9%JlRC#FS0bA8kl>S0]P5P3P1P0%OCS0R$0L1\k6R}/31XF0P0Pl&0L1,3}XF0Q0kQ0BQ0jQ0hQ0iQ0dPUPVPMP[B0{0s]Q0N9x0s5X\P=PRb4b5b6X001\16101E'3^00P1PDO1b3b8b7b9Q0RQ0kQ0BQ0jQ0hQ0iQ0dPUPVPMP[P\Q0LQ0_5a\PdQ0`C>P=PRb4b5b6X00X:yQ0g/13Q0a[^00^:yP1Q0e,2DPDP>O3b3b8b7b9-0zlEiQ0b#OR>&0yCEiQ0]#7,\l/3>eN>0xPoPOPkPkA8OklPqPOPkPl10uhP1D`%73R>10@hRCQ0;#?#;R6'2%I2%72Rs'sR]10ShR},AY'4[7@O\^'1FVXO8#RQ04P8PoPBPOPOA8BOkPqPBPOPkPCP1D`12}610zhR},AY,4][9@>B\^'1FVXO8PoPDPBPBA8DBOPqQ0A14kiRCP^PBPaPkPNP^PaPBQ0CPCDKGZFVX;8#RP1PoP~PDPDA8~DBPqP~PDPBP}P1D`10|hR}/2610ThRB,AY,4][9@>~\^'1FVQ02PofWR>P~&04~A8>~D1T83J0KP>P~PDP}P3D`1<3E12B6%I4%74's10wh,AY'4[9@s>['1PofYRsfXRBPBA8sB>H0JR>PqQ0A14~iR}P^PBPa14~NP^PaPBQ0CP}DKI0;J0:X;8#RP11T8495o>fZR>PsPB10KhP7D`1<7E%7510AhRA/26%I;%7;RB'sQ0[/0hR},AY'4[7@>['1Q02f[RDP>PsPAP5D`1<5E12}6%I:%7:'s109hR9,AY'4[9@BD[Pof]RBf\R}P}A8B}DPqQ0A14>iRAP^P}PaP>PNP^PaP}Q0CPADKGZFVX;8#RP1PBP}PDP9P:D`1<JE%7mf^R:10lh/26%Ir%7rR6's10khRk,AY'4[3@[Pof_RYP:P:A8Y:BH0JPIP?PIP_P`P?PIf`Rl/6aPbP?PIQ0<P`PHPGPFPePOPhH00Q0=CEn0100000020000n0100000020000n0100000020000X<8:0IH1PHPBCNXBoP@1T8mROP5E[PIP?PIP_P`P?PI16YaPbP?PIQ0<P`PHPGArFekQ0=CEn0100000020000n0100000020000n0100000020000X<8:0IHOPHP}CNP8PofaR}PlPlA8}lYPqQ0A14:iROP^PlPaP:PNP^PaPlQ0CPODKGZFVX;8PrPoPlPY&04YA8lY:1T8rJ0K%zrR:/4ERO#W14BiRkPOPYP6PBPNPOP6PY%9r=ockC}GZP;20u:E206:E-0tO%zp006EP?Q031<LEP?PI%t3P`P?PIfcRp%7XRO'6PbP?PI%9XR:,6cP`PHPGPFP<%IX1\OE10~hD|%hX10:Q/mf'0CEn0100000020000n0100000020000R:n01000000200001CH}R~55I1<WERO#WfbR;/4iRk'1RrPOfdRY%7WR6'3RB@0s;NPO126YRO%9W=ockI0rRk'D]1P31<ZEReP?PIQ06#tP`P:n0100000020000=5I~20<Y616Y69~BOfeQ0E#7'6P?Q01ffRO%7{RB'312BOP?PIP3PbP?PI%9tRB,6cP`PHPGPFP<%It%7t/\E10DhD|%ht10BQ/mf'0CEn0100000020000RBn01000000200001CHORO55I1<vERt#WfgRD/4iR6'1R_fiR9%7vRA'314DN5utR>PtPAP9%9vRv,3cRAP6DKR6'DRt'D]1P3%7xRs,3DA5IbOPIP0Q00PHP0P1PNP1PNPNn101102000410106101040000XAIPb1CHDP1Ev&0ADfh$0AP0Q071<SEflRb%7S'3141N3uX@01<@EfkR]%7@'3S07&0ANRC'1PJQ07PCP4%^NCLCLP9P1E[W2P1O1b2:08>69{_tW1WHP1O112sDA5IBO20<cv12vc16cv5~A%9u,6cP?Q01%9@R@,3c12@cP?PIP3P`PHPGPFP<%Iz%7z/\E10lhD|%hz%9z/0Q/mf'0CERzn01000000200001CH]R]55I1<|ERl#W14biR@'1RufnRA%7|Rv'314bN5ulROPlPvPA%9|Rl=oc@C}R@'DRB'D]1P3%9SRS,3cA5I`]PIP0Q00PHP0P1PiP1PiPin101102000410106101040000XAIRsP`1CHbRDP1Ev%pbfmRb#pP0Q081<KE%7Kfq%9K141iRK5ocC}X@01<wE%7wfp'2Rt%9w,3cRw%piR_'1R6'1PZPtP6PJPwP_P4%^iRwCLCLCLPAP1E[W2P1O1b29{O@9{uBW1WIP1O112ScA5Iz]PIPHPGPFP<%I|1\vE10}hD|%h|10lQ/mf'0CEQ00PHPyP1g01CUg01D1RfPfPfn101102000410000100000000XAIg01DNPDP1E[Pf1<TERf#W14biRDPffoRl%7TRQPbPNPfPQPl%9T=ocDC}GZ00q1b2W1WIP1O1n200210000000021100011000P2O1bCb>W1WHP1O1n200210000001021100011000P2O1bCb>W1WPP1O1%WeP?PIQ05#tP`P:n0100000020000=5I~PIP0PsP`1CH;P1Ev%p;%ppP0Q081<xE#W/1KX@01<{E#WP_P4PwCLPYP1E[W2P1O1b2:08rkW1WXP1O1n10210010201021110111103P2O1b>bBCLH0pb1W\W[P3P1O2n2001000000121000000W2WYP3P1O2n2001000000121000000W2X;8P3P1O2n2001000000121105000bAWTWVP3P1O2n2001000000121000000W2WUP3P1O2n2001000000121000000b]b1bQb1b2b1CL3{W1WGP1O1n200210000001021100011000P7O1bCb>bZbab1W1WJP1O1Q0D/3mQ0:Q0>5MHQ0?55IQ0HQ0IQ0JQ0KPUPVAgM2gQ0G?g2g7g2P[P\Q0@,l0R[Q09,l0Rg5X\PdP\205\7AB\g[5a\Pd205\5C>C>P=PRb4b5b6X00X=0X:yXKyQ0SQ0f,14P5[[^00^=0^:y^KyP11]WPRP,3j14LnPoQ0EPWQ0FQ0EPWPXJ0CPqQ0A14ZiRiP^PWPa14ZNP^PaPWQ0CPiDKI0;J0:X;8#R9@Pj40G12EX%:Z#OPXP7PmO6b3b8b7W1WJP1O1n200210000001021100011000P2O1bCb>W1WWWRWSX@0X`<X_0W^o"). Qed.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rd_errinvA (C : rdctxA) (m1 : amem) : Prop :=
  (exists nc, u8arr bsegs m1 (a_NC C) (u16s (map (Z_to_bv 64) nc)) /\ length nc = length (a_rt0 C))
  /\ (exists msvw, rw_cells bsegs m1 (a_MSVP C) [C4 msvw])
  /\ (exists tlw, rw_cells bsegs m1 (a_TLP C) [C4 tlw])
  /\ (exists k0 k32, rw_cells bsegs m1 (a_SPA C) [CB 24 k0; C8 (Z_to_bv 64 (a_FF C)); CB 56 k32])
  /\ stk bsegs m1 (a_lo C) (a_SPA C)
  /\ munch (rd_WA C) (a_m C) m1 /\ wmono bsegs (a_m C) m1 /\ mem_inv bsegs m1.

(* [comment removed for export] *)
Definition rd_mainA_errpost (C : rdctxA) (e : Z) : machine_state -> Prop :=
  fun ms' => exists m' (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x27 x28 x29 x30 x31 : word),
    ms' = MS (mkR x1 (Z_to_bv 64 (a_SPA C)) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 (a_SPA C)) x10
                  x11 (Z_to_bv 64 (- e)) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (a_FF C))
                  (Z_to_bv 64 (Z.shiftr (a_FF C) 3 + 2147450880)) x27 x28 x29 x30 x31)
             (a_F C) (Z_to_bv 64 0x971f0) (a_fc C) None m' (seg_rom bsegs)
    /\ rd_errinvA C m'.

Lemma errinv_of_inv : forall C m1 nc msvw tlw, rd_invA C m1 nc msvw tlw -> rd_errinvA C m1.
Proof.
intros C m1 nc msvw tlw (ARR & LNC & _ & HMSV & HTL & (j0 & j64 & FR) & ST & MU & WM & MI).
split; [exists nc; split; assumption|].
split; [exists msvw; exact HMSV|]. split; [exists tlw; exact HTL|].
split; [| exact (conj ST (conj MU (conj WM MI)))].
unfold FRA_main in FR.
lazymatch type of FR with rw_cells ?sg ?mm ?AA [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9] =>
  change (rw_cells sg mm AA ([c0; c1; c2; c3] ++ [c4; c5; c6; c7; c8; c9] ++ [])) in FR;
  apply rw_cells_merge in FR;
  change (rw_cells sg mm AA ([] ++ [c0; c1; c2] ++ (c3 :: [CB (cells_size [c4; c5; c6; c7; c8; c9])
    (cells_bytes [c4; c5; c6; c7; c8; c9])]))) in FR;
  apply rw_cells_merge in FR; cbn [app cells_size csize Nat.add] in FR
end.
do 2 eexists. exact FR.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Loop.
  Variable C : rdctxA.
  Variable RNG : footprint.
  Hypothesis OK : rd_okA C.
  Hypothesis SH : rd_shA C.
  Hypothesis RNGS : rd_rngA C RNG.
  Variable tl : Z.
  Hypothesis Htl : 5 <= tl <= 15.

  Notation buf := (a_buf C).
  Notation msv1 := (a_msv0 C + 1).
  Notation BUF := (a_BUF C).
  Notation NC := (a_NC C).
  Notation MSVP := (a_MSVP C).
  Ltac cbnR := cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0] in *.

  (* [comment removed for export] *)
  Lemma exit_run_errA : forall s m1 msvw (x1 x6 x7 x12 x18 x20 x22 x29 : word) e,
    rd_invA C m1 (r_nc s) msvw (Z_to_bv 64 tl) -> rd_brk_okA C s ->
    ((r_remaining s <> 1 /\ e = 20) \/ (r_remaining s = 1 /\ msv1 < r_charnum s /\ e = 48)
     \/ (r_remaining s = 1 /\ r_charnum s <= msv1 /\ 32 < r_bitCount s /\ e = 20)) ->
    evtF bsegs RNG (rd_mainA_errpost C e) (rd_exitA C s m1 x1 x6 x7 x12 x18 x20 x22 x29).
Proof.
intros s m1 msvw x1 x6 x7 x12 x18 x20 x22 x29 e INV (B1 & B2 & B3 & B4 & B5) HE.
pose proof RNGS as RNGS'. destruct RNGS' as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
pose proof (okA_lin C OK) as (HH & HM0 & HM1 & HRT & SP16 & SPK & LO & LOA & SPA12 & SPA3 & NC0 & NC1 & N8 & MS0 & MS1 & M4
& TL0 & TL1 & T4 & BF0 & BF1 & B8 & FF0 & FF1 & F64).
pose proof atop_range as ATR. unfold RDA_CALLEE, KHIGH, AIMG_HI, KEND in *.
pose proof (errinv_of_inv C m1 (r_nc s) msvw (Z_to_bv 64 tl) INV) as EI.
unfold rd_exitA, rd_lstA.
destruct s as [nc ip bs bc cn rem thr nb p0]. cbnR.
destruct INV as (_ & _ & _ & HMSV & _ & (j0 & j64 & FR) & _). unfold FRA_main, ASHB in FR.
change (2^31) with 2147483648 in *.
destruct HE as [(HR & ->) | [(HR & HC & ->) | (HR & HC & HB & ->)]].
- zstep. zstep. zstep. zstep. if_cases K1; zify_cond K1; try (exfalso; lia).
  apply evtF_done. unfold rd_mainA_errpost. exists m1. do 23 eexists. split; [reflexivity| exact EI].
- subst rem. zstep. zstep. zstep. zstep. if_false.
  zstep. if_cases K2; zify_cond K2; try (exfalso; lia).
  zstep. zstep.
  apply evtF_done. unfold rd_mainA_errpost. exists m1. do 23 eexists. split; [reflexivity| exact EI].
- subst rem. zstep. zstep. zstep. zstep. if_false.
  zstep. if_cases K2; zify_cond K2; [| exfalso; lia].
  zstep. zstep. if_cases K3; zify_cond K3; rewrite ?signed_lit in K3 by lia; try (exfalso; lia).
  apply evtF_done. unfold rd_mainA_errpost. exists m1. do 23 eexists. split; [reflexivity| exact EI].
Qed.

  Lemma buf_h8E : 8 <= FseNCount.Zlength buf.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_fse_rd_err ()) ["CANSEC1"; "Loop"] "h04__p1h14__x1h22HHh32_Hh47__arithh54__ffh68__varmaph75__with81ch94cstrh:1rp;1p;2p;3p;4p;7p;6p;8g002Wj16Tg003<j12Tg01L]j1JTg00k;j2=Tg003Zj1?Tg004:j20Tg00TeR0j21Tg007Vj2<Tg02gjj3DTg01`kj1CTg00;aj14Tg00<dj23Tg01J_j1cTg01e4j1^Tg00TEj2:Tg01Ymj1VTg01N\j1UTg00G6j2RTg01f2j1QTg01GNj1NTg01fhj2ITg02hKj38Tg01M\j1HTg01[]j1ETg01K^j1FTg01gEj1GTg00WDj27Tg00JYj1BTg00K>j1LTg001:j1MTg00Paj2ATg00L<j1OTg00LZj1PTg00MEj2@Tg00Q?j2STg00`Lj4TTg0116j7bTg012bj6aTg012>j7`Tg00Qbj1]Tg011Zj8\Tg00Mhj2[Tg00NJj2YTg00Ndj2ZTg00Hkj3>Tg00OPj3XTg00Ooj4WTg00k[j2_Tf0R1#6#6p=5g013dR2g014BR37>1p=;f2R4f1R5/11'1p=Kf4f3R61151,14'1'1p=9p,2OKg01>AR7#6R8#6R9#6R:#2R;p,1CR<#JR=,=2R>#?R?'0R@%6:R:#5RA#5RB#5#5#5#5#2RC,0?RD'1RE1031%2B,<1'1X82=D2=%C<RB,03%47#4#4#4#4#4#4#2,0B'1%27,3B%c<,=2#?RB'010BC%^<RC%2:R:':#;13C:g02a^'<%V<R:%U<g02bS'R'0p,2rcRC#Q/0:%N<R:%28/IB,3:RB58C1::;#;%H<R8%29R9,38RF58C1:89#;%E<RG13G9RH58C1:G9#;%F<R9139?RI58C%G<R<%2ARA,3<58C1:<A#;10B810F:'710BG10H:'710B910I:'710FG10H8'710F910I8'710H910IG'71039'13KD9D9D9D9D9R9'1P0PEP9P@P1%B>103?p-0R>g01A7R@#L%M@1A25%O2%P2R@g016\R0g016<RIPIg017;RGP@P0PIPIPGP@P0PIPIPGP21@2;g017[1S27CTg018BFbR7P@P0PIPIPGP6EaF`%]IP7G\1[@GP1P4g018bRGg019BR@'Y1Z14=>G@dAX235CWb5b6b7X12W010;1/1510;5[^12^0>P1PDP?P6O3b4b9X39X2EP5P1O2n2011000000121000000b:1_2=,0;eo"). Qed.
  Lemma msv1_okE : 1 <= msv1 <= FseNCount.Zlength (a_rt0 C).
Proof.
ltac2:(KReplay.run1 (kr_t_AF_fse_rd_err ()) ["CANSEC1"; "Loop"] "h01Hh14__p1h24__x1h34__x2h43HM0h53HM1h62_Hh73_H0h83_H1h97__arithh:4__ffh;8__varmaph<5__with=1ch>4cstrh?1rp;1p;2p;3p;4p;6p;7p;8g002Wj19Tg003<j13Tg01L]j1VTg00k;j2?Tg003Zj1ETg004:j20Tg007Vj2@Tg02gjj3KTg01`kj1JTg00;aj16Tg00<dj22Tg01J_j1jTg01e4j1hTg00TEj2<Tg01Ymj1\Tg01N\j1[Tg00G6j2ZTg01f2j1XTg01GNj1WTg01fhj2UTg02hKj3;Tg01M\j1TTg01[]j1RTg01K^j1QTg01gEj1NTg00WDj27Tg00TeR0j21Tg00JYj1ITg00K>j1LTg001:j1MTg00Paj2HTg00K^j1OTg013Fj4PTg00L<j1GTg00LZj1STg00Q?j2ATg00MEj2FTg00RDj3iTg00Qbj1gTg012bj6fTg00Mhj2_Tg00NJj2^Tg00Ndj2]Tg00Hkj3DTg00OPj3`Tg00Ooj4aTg00k[j2bTg00`Lj4cTg0116j7dTg012>j7eTg011Zj8YTf0R1#9#9p=8f2R2f1R3'0/11p=5g013dR4g014BR57D1p=:1131,12p=4P4P3g017[P1Ccp=>P3g016\R6g016<R7P7g017;R8P1g018BFdp==P2P6P7P7P8P3P1Fep=Cf3R9P6P7P7P8P2P3P1GYp=Bp,2OKg01>AR:#9R;#9R<#9R=#3R>p,1CR?#VR@,?4#ERA%9=R=#8RB#8RC#8#8#8#8#3RD,0A35RE%3C,@19551X=4=K4@R@%J?RC%6:#6#6#6#6#6#6#3,0CRF555RG%3:RH,2CRI%j?RJ,?4RK#ERL'0RM%h?RN%3=R='<#:12N=g02a^'@%\?R=%[?g02bS'Zp,2rcRN#X%W?RO%3;/UL,2ORP5;N1<O>#:%T?R>%3<R<,2>RQ5;N1<><#:%R?RR12R<RS5;N1<R<#:%Q?R<12<ARA5;N%N?R?%3BRB,2?5;N1<?B#:10P>10QO'710PR10SO'710P<10AO'710QR10S>'710Q<10A>'710S<10AR'7105<'13434343434343475=353495LDRD'1R='1R<'1RA'1P0PEPA10HIRR/1MRSP1P0P@P<PSP1P0PGP=PSP1P0PMPDPSP1%IK105Lp-0RKg01A7RS#L%MSP41H42P3%O4CP%G4%S4RS1A4:R:1F4HR05i4R>1A4;'>,=SR;%g7RQPS1F45/>:,=SPSP6P7P7P8f4Ef5CSPQ1>0>,=S=CS;CBCB1_S8P1P2g018bRSg019BR8'^1]12=DS8dA`453Cab:b;b<X24X34W1121H/03A5539122HR2102955H[[^24^34^1KP1PFPLPCP9f7O5b9b>X8DX5MP3P1O2n2011000000121000000X0=X4GP3P1O2n2011000000121000000X0<X7@P3P1O2n2011000000121000000X0AX6EP3P1O2n2011000000121000000b?1b4J,0I,1Reo"). Qed.

  (* [comment removed for export] *)
  Lemma loop_runQ : forall (Q : machine_state -> Prop) f s sF m1 msvw (x7 x12 x20 x22 x29 : word),
    rloop buf msv1 f s = Ok sF ->
    rd_invA C m1 (r_nc s) msvw (Z_to_bv 64 tl) -> CTL msv1 (a_rt0 C) tl s -> POS buf s -> r_bitCount s < 32 ->
    (forall m3 (z1 z6 z7 z12 z18 z20 z22 z29 : word), rd_invA C m3 (r_nc sF) msvw (Z_to_bv 64 tl) -> rd_brk_okA C sF ->
       evtF bsegs RNG Q (rd_exitA C sF m3 z1 z6 z7 z12 z18 z20 z22 z29)) ->
    evtF bsegs RNG Q (rd_headA C s m1 x7 x12 x20 x22 x29).
Proof.
induction f as [|f IH]; intros s sF m1 msvw x7 x12 x20 x22 x29 RL INV HC HP HB32 KX.
{ cbn in RL. discriminate RL. }
cbn [rloop] in RL.
assert (CNT : forall s1 m2 (y7 y10 y22 : word),
rd_invA C m2 (r_nc s1) msvw (Z_to_bv 64 tl) -> CTL msv1 (a_rt0 C) tl s1 -> POS buf s1 -> r_bitCount s1 < 32 ->
(let! fl := rcount_block buf msv1 s1 in match fl with Brk s' => Ok s' | Cont s' => rloop buf msv1 f s' end) = Ok sF ->
evtF bsegs RNG Q (rd_cntA C s1 m2 y7 y10 y22)).
{ intros s1 m2 y7 y10 y22 INV1 HC1 HP1 HB1 RL1.
destruct (rcount_total buf (buf_all_bytesA C OK) (buf_h8A C OK) msv1 (a_rt0 C) (msv1_okA C OK) tl Htl s1 HC1 HP1 HB1)
as (fl & EF & HF).
rewrite EF in RL1. cbn [bind] in RL1.
eapply (count_runA C RNG OK SH RNGS tl Htl Q s1 m2 msvw (Z_to_bv 64 tl) fl); try eassumption.
- intros s' m3 z1 z6 z7 z12 z18 z20 z22 z29 -> INV3 BK. inversion RL1; subst. apply KX; assumption.
- intros s' m3 z7 z12 z20 z22 z29 -> INV3. destruct HF as (HC3 & HP3 & HB3 & _).
eapply IH; eassumption. }
unfold rbody in RL.
destruct (r_previous0 s) eqn:EP.
-
destruct (rzero_total buf (buf_all_bytesA C OK) (buf_h8A C OK) msv1 (a_rt0 C) (msv1_okA C OK) tl Htl s HC HP HB32)
as (flz & EZ & HZ).
rewrite EZ in RL. cbn [bind] in RL.
unfold rd_headA. rewrite EP.
eapply (zero_runA C RNG OK SH RNGS Q tl s m1 msvw (Z_to_bv 64 tl) flz); try eassumption.
+ intros s' z1 z6 z7 z12 z18 z20 z22 z29 -> EN BK. cbn [bind] in RL. inversion RL; subst.
apply KX; [rewrite EN; exact INV| exact BK].
+ intros s' z7 z10 z22 -> EN. destruct HZ as (HC1 & HP1 & HB1 & _).
apply CNT; try assumption. rewrite EN. exact INV.
-
cbn [bind] in RL.
unfold rd_headA. rewrite EP.
eapply (cnt_entryA C RNG tl Htl Q s m1); try eassumption.
intros y7 y10 y22. apply CNT; assumption.
Qed.
  Corollary loop_runQ' : forall (Q : machine_state -> Prop) f s sF m1 msvw pc (x1 x6 x7 x10 x11 x12 x13 x16 x18 x20 x22 x29 : word),
    rloop buf msv1 f s = Ok sF ->
    rd_invA C m1 (r_nc s) msvw (Z_to_bv 64 tl) -> CTL msv1 (a_rt0 C) tl s -> POS buf s -> r_bitCount s < 32 ->
    (forall m3 (z1 z6 z7 z12 z18 z20 z22 z29 : word), rd_invA C m3 (r_nc sF) msvw (Z_to_bv 64 tl) -> rd_brk_okA C sF ->
       evtF bsegs RNG Q (rd_exitA C sF m3 z1 z6 z7 z12 z18 z20 z22 z29)) ->
    pc = (if r_previous0 s then 0x96cf8 else 0x96cdc) ->
    x1 = Z_to_bv 64 (r_nbBits s) -> x6 = Z_to_bv 64 (bv_swrap 32 (r_bitStream s)) -> x10 = Z_to_bv 64 (BUF + r_ip s) ->
    x11 = Z_to_bv 64 (r_remaining s) -> x13 = Z_to_bv 64 (r_charnum s) -> x16 = Z_to_bv 64 (r_bitCount s) ->
    x18 = Z_to_bv 64 (r_threshold s) ->
    evtF bsegs RNG Q (rd_lstA C pc m1 x1 x6 x7 x10 x11 x12 x13 x16 x18 x20 x22 x29).
Proof.
intros Q f s sF m1 msvw pc x1 x6 x7 x10 x11 x12 x13 x16 x18 x20 x22 x29 RL INV HC HP HB KX -> -> -> -> -> -> -> ->.
exact (loop_runQ Q f s sF m1 msvw x7 x12 x20 x22 x29 RL INV HC HP HB KX).
Qed.
End Loop.
End CANSEC1.
