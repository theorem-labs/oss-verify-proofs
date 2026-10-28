(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1 HufPure_HufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import STRW_tac FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_fa_iface RF_huf_y4s_iface RF_huf_y4body_kit RF_huf_y4body RF_huf_y4fastb.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_y4fast () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib6ZArith4ZdivAZ_div_mod_eq_fullK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2leC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr04C47Corelib4Init5Logic8eq_ind_rK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or01I46Stdlib;setoid_ring<Ring_polynom5PExpr00I47Corelib4Init9Datatypes4prod00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr07C56Stdlib6ZArith6BinInt1Z4to_NK46Stdlib;setoid_ring<Ring_polynom5PExpr09K46Stdlib;setoid_ring<Ring_polynom5PExpr06K46Stdlib;setoid_ring<Ring_polynom5PExpr05I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C56Stdlib6ZArith6BinInt1Z:div_uniqueC47Corelib4Init5Logic6eq_symK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_divC56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substK47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterK47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib;setoid_ring<Ring_polynom3Mon00I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_y4fast=y4_div5_magicC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z8mul_commC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC56Stdlib6ZArith6BinInt1Z7div_addc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_y4fast=y4_div7_magicC4ELinuxProcessSemantics5Riscv7Prelude5bvmapI45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit39x2_bytes'C47Corelib5Lists7ListDef6firstnC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_y4body=y4_x2tab_factC5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_y4fast3Y4MI47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<huf_dec_postC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic2ex00K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_y4fast:y4_tabfactK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission6Common5KXTac9ztab_factC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC5ARocqVerifyHarness?AgentSubmission3Lib3Arr@u64arr_transportC5ARocqVerifyHarness?AgentSubmission3Lib5FrameFstk_transport_disjointC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame<munch_weakenC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_transC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_transC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKitAbytes_of_unsignedK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr05K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC56Stdlib6ZArith6BinInt1Z3ltbC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC56Stdlib6ZArith6BinInt1Z6ltb_ltC46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith6BinInt1Z6ltb_geI4ELinuxProcessSemantics5Riscv7Prelude4tree00K4ELinuxProcessSemantics5Riscv5Instr5instr03C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_y4body=y4_body_proofC47Corelib4Init9Datatypes7nat_indC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Arr6u64arrK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invK46Stdlib9micromega5Tauto8GFormula06K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_leI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00c5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_y4fast3SPSC56Stdlib6ZArith4Znat5Nat2Z8inj_succI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05I4ELinuxProcessSemantics5Riscv5Instr5instr00C56Stdlib6ZArith6BinInt1Z:mul_div_leC46Stdlib5Lists4List9nth_errorC47Corelib4Init5Logic9False_indC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8c5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_y4fast5y4_q7c5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_y4fast6y4_q10K4ELinuxProcessSemantics5Riscv5Instr5instr02C56Stdlib6ZArith6BinInt1Z6shiftlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_auipcC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7b_auipcK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z7eqb_neqK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC4ELinuxProcessSemantics5Riscv7Prelude4zextC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC56Stdlib6ZArith6BinInt1Z8max_specc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_y4fast8y4_innerC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subK4ELinuxProcessSemantics5Riscv5Instr5instr0BC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC56Stdlib6ZArith6BinInt1Z7add_0_rc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_y4fast:y4_mulhu10C47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C46Stdlib4Bool4Bool>negb_false_iffc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_y4fast9y4_mulhu7C5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u64arr_readC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC56Stdlib6ZArith6BinInt1Z3maxK4ELinuxProcessSemantics5Riscv5Instr5instr06C45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_mulhuC4ELinuxProcessSemantics5Riscv3Sem7mul_divC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7m_mulhuC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_divC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapK4ELinuxProcessSemantics5Riscv5Instr5aluop01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK4ELinuxProcessSemantics5Riscv5Instr5msize04K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5mulop04K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK4ELinuxProcessSemantics5Riscv5Instr5aluop03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr;branch_cond06".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation Y4_M10 := 14757395258967641293 (only parsing).
Notation Y4_M7 := 2635249153387078803 (only parsing).

(* [comment removed for export] *)
Lemma y4_div5_magic : forall x, 0 <= x < 2^64 -> (x * 14757395258967641293 / 2^64) / 4 = x / 5.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_y4fast ()) [] "h07__arithh14__ffh28__varmaph35__with42H0h52Hah64__p1h76__sat0h86__sat1h96__sat2h:6__sat3h;4__x1h<4__x2h=4__x3h>4__x4h?1ah@2zhhA5heq_qhB5heq_rhC1xhD1HhE2H1hF2H2hG2H3hH2H4hI4__p2hJ6__sat4hK6__sat5hL4__x5hM2HqhN2HrhO2HxhP7fv_listhQ8hyp_listhR3lmphS1qhT1rhU1zp%0p&0p;1p;2p;3p;4p;6p;7p;5p;8p;:p;<g0000j10Tg000Uj1;Tg0013j2iTg001Pj22Tg001lj27Tg002Gj19Tg002lR0j25Tg003Ij26Tg003fj28Tg004Fk20ETg004mj2?Tg005Gj1UTg005gj1MTg006Gk10<Tg006ek10;Tg007Ck103Tg007nj2GTg008Qj2yTg0093j2xTg009_j3JTg00:9j3uTg00:Xj4tTg00;Jj3rk20JTg00<1R1j2CTg00<Nj2VTg00<jj2lTg00=[j2kTg00>Lj2[Tg00?4j3ZTg00?Xj2jTg00@9k10KTg00@Rk20ITg00A9k20HTg00A_k20GTg00BEk20DTg00CAj2hTg00Cbj1@Tg00DAj1gTg00D_j2fTg00E@j3dTg00Eij2cTg00FRj2bTg00G>k20ATg00Gjj3LTg00HJj2TTg00Hhj4HTg00IFj2FTg00Iik10:Tg00JKj3RTg00Jnk302Tg00KQj1`Tg00Koj3_Tg00LRk301Tg00M5j6QTg00MSj2^Tg00N<j3PTg00Nej4zTg00O@j3|Tg00OZj1}Tg00PDj2OTg00Pdj2\Tg00QNj2]Tg00R8j3NTg00Rbj1wTg00S@j3vTg00Sjk304Tg00TTk305Tg00U>k107Tg00Ufk408Tg00VLk709Tg00W;j6qTg00W_k40=Tg00X;k60>Tg00X_k50?Tg00Y@R2k20@Tg00Y]j4XTg00ZHj7oTg00Zlk30BTg00[Uk60CTg00\9j7nTg00\]j8WTg00]Al:mTg00^2m<0FTg00^_R3f0R4'Vp=1%04#0p=e%04#0#9#9p={%04#0#9#9#0#0#9#9p=>%04#9p=sg00_=R5f1R6;J4p=4f2R7/5600@4p=<P5P6g00_[P4CXp=DP6g00`BR8g00`aR9P9g00aAR:P4g00aaFop=3%94#0p=pAJ543p=Y1c54p=AB0B564p=:P5P6g00bAP4CXp=EP6P8P9P9P:P4J0Cp=SP7P8P9P9P:P6P4Fnp=If6R;P8P9P9P:f5R<f4R=f3R>P8P9P9P:P7P6P4GWGWp=BP5P6g00bhP4CXp=KP>P8P9P9P:P7P6P4GWp>00%04#0#0#0p=~%04#0#0#0#0#0#0#0p==P5P3P6P2P0P1g00cOR?g00clR@g00dIRAP4M:mp>06P5P3P7P2P0P1P?P@PAg00djS00P6P4N<0Fp=a%14g00eYRA#0R?#;R1%0?R0#eR2#eRB#;RC'iRD,24'7P5%9ARE#{#>#>#>#>#>#>#>#sRF#;RG,56RH%;0RI,5D'6%9?RJ#;RK,67,44XU5166KP5187KP520E>KA<K64,4>RLePL18=KRL,?5146LRLePL16<KRL,?514>LRLePLg00f>RL#URM%MLRN&0<5RO&0;5RP&035RQ1G53RR1G5KRS'D'31yQ:RTP4P7g00fjRUg00gJRV'?S011x47=JUVdAu536CtRWb1b2b3123KRXP4b0bAbB9r=K%16126K'7RYePYP5P>15<GRY%p2R2#;RZ,i1R['6PYP[P>15>[,CYR\%1\R]12\[R^'712[\1V\3'7P]P^P5A<K>7S02154G15=[R^'CR]#1XC518<KR_,?5147_R_eS03P_16;KR`,?514=`R`eS04P`f7Ra/lKS05%1aRb%1KRcf9Rd/8K#1[[S06f8Re/kKS07%1ef:Rf/6K#1\c[S081[1CS091231Rg%1C123D[Rh[S0:%11Rig00gjRjAZ1C6UW5S0;%1DRC\j^5iS0<1[1ZS0=%1Z123[[Rk\gS0>AZ1Z6VjX5iS0?%1[Rl\j^5iS0@f=/jKS0A%YKRm$0Kf>Rn16nK18nK5<K'4[S0B20JnKS0Cf?Ro/8KRp#112pK'7\XS0D20IoKS0E12K3f@Rp/8KRq,2K1Vq3'7[S0F20HpKS0GfARq/6K#Y\mS0H20GqKS0IfBRr/8K/4r\mS0Jg00hFS0K20DrKRmeS0LPmP=g00hbRs1h3K'?PXeO1S0MfC/8KRX#112XK'7RXP6PjPdP4P6O2X?iRdPl^?iRlPf1h31,?sPgeRgO1RsPkP=PjPnP4P6O2X?iRnPC^?iRiPoPgO1RgPhp-0Rog00iHRC#@Rt#@Ru#@Rv#@Rw#ARx%gA,f5%Av5d5Rv%gF,f5%Au5d51c5CRC':':':%@wRw#@#A,:Cg00igRu'b+0A=LLMPNP5P51T5=P7POCHRFP6P51T5<P>POCHCHPPPQ1F50R0,ER,3Q1SQa5IQ&0:9RyPQPQ1F5ERE,ER,3QRzPyPQ1ERS,3QPy1F5JRJ,ER,3QFBPyPQ1F5AR{/KJ,3QPyPQ1F5?RJ/K0,3QR|PyPQ1SQe9IQzPyAR5S{>025JRJ1G5G5R51G51Re%`25_5R29R5{6015R{,ER,3QH00FBFBPTPWb1b2b3X;5X<5X=5X>5XL5X6oWI%1>R}/7<Pb\c\}147;14=;%1;/7fA<K<;/5G15<['C#1[[[[[^;5^<5^=5^>5^L5^6o^IoP4fKRf/2D18fKR}/2K16fKP}PffHRcfIRbPaPrfDfERrfJR~O<b0b:b9b@b8b7b@b4A<Kqp/5G15q['CRq#1ebHbGbFbEb4bDb7b8b9b:bJbKbAbBP<P6EQP5Q0212][XC5Q03P_Q04P`Q05Q06Q07Q08Q09Q0:Q0;Q0<Q0=Q0>Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0FQ0GQ0HQ0IQ0JQ0LPmQ0MPXP6PjPdPlPsPkP=PjPnPiPgPh%~B#=#=#=#=#=#=#=#;,^5Rh%Aw5P5AP5hx%At1^5K=P5C':,:v':':/bu=LLMPNP5PFP61T5>CHPPPQ1SQ;1D0S,3Q5IQPyPQP|PyPQ1KEJ,3QPyPQ%`B9_5eRe,DE,3Q9IQzPy1D{2,3QFBFBPTPWb1b2b3X;5X<5X=5X>5X6o12>K,7=147=A<K7>,4=%1<12<D'7A<K=</5G/C^/2[[[[[^;5^<5^=5^>5^6oP4%1}P}PfPcPbPaPrfGP~O9b0b:b9b@b8b7b@b412q[ebHbGbFbEb4bDb7b8b9b:bJbKbAbBP<P6EQCz3|%}5R</O<R<#U%M<%U59L5=9L5;%M5Q00P4P61\5A1]5G5N5RG1]51%wZ5v5RZ1\5?R?5N5AN5?Z:045G6055R?Q0KQ01%;ARA0066g00jS,O5&075'O#MP5P@AaA4GAaA4?H08bR=JUVdK09bPbQA<[>\,4YeEqH0=bNbMbTbS16HD/6IPHPDPIPMPNPOPPPQP8P9P9P:1KeR,3QJ0>PTPWb1b2b3%YDg00k;[P4b0PMPNPOPP1G5I,DR,3QPTPWb1b2b3123IP4b0I0?EQWOXC5o"). Qed.

Lemma y4_mulhu10 : forall x, 0 <= x < 2^64 ->
  ((x * 14757395258967641293) ≫ 64 mod 18446744073709551616) ≫ 3 = x / 10.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_y4fast ()) [] "h07__arithh14__ffh28__varmaph35__with44__x1h51zh64__p1h71Bh82Hxh91xp;1p;2p;3p;6p;4p;5p;7p;8g0000j10Tg000Uj14Tg0013j2LTg001Pj28Tg001lj2<Tg002Gj13Tg002lj2:Tg00kXj2ETg003fj2BTg003Ij21Tg009_j35Tg00Eij2HTg00Cbj1JTg00Zlj3]Tg00FRj2\Tg00G>j2[Tg005Gj1ZTg00Gjj3YTg005gj1WTg00HJj2VTg006ej1UTg007Cj1TTg007nj2DTg00IFj2STg00[Uj6PTg00Iij1OTg00JKj3ITg008Qj2NTg004mj2MTg0093j2nTg00:9j3mTg00:Xj4lTg006Gj1kTg00KQj1gTg00Koj3fTg00l8j4eTg00lYj5bTg00Nej4aTg00Y]j4@Tg00X_j5KTg00M5j6=Tg00mEj2`Tg00nKj6cTg00ngj3dTg00oJj3FTg00<Nj2_Tg00ZHj7^Tg00\9j7hTg00\]j8iTg00X;j6jTg00^_R0f0R1'_p=6%01#0#0#0p=R%01#0#3#3p=X%01#0#3#3#0#0#3#3p=7%01#3p=Q%01#0p=o%01#0#0#0#0#0#0#0p=9g00_=R2f1R3g00bAP1C@p=>P3g00`BR4g00`aR5P5g00aAR6P1g00aaF^p=2f2R7P4P5P5P6P3P1Fhp=A1D21p=;f3R8P4P5P5P6P7P3P1Gip=CP2P3g00_[P1C@p=?P3P4P5P5P6P1Ejp=G%61R9g00eYR:#0R;#4R<%0;R=#RR>#4R?'LR@,81RA'<RBP2%3:RC#X#7#7#7#7#7#7#7#Q#4RD,:3RE/E?RF%o>#9#9#9#9#9#9#9#4RG'BRH%4CRC,L<RI'1%3;R;#0#4RJ,17RK9521X52P211E@RL1B1G/1I=52KX52%6LRM18L@RLPEP@p-0RNg00f>ROg00iHRP,H2RQ%JP#J,H29]2Qg00ig'\'[%ZORQ3YRP%WORO1V23RR%U2RS%T2RT1D20RU1S2:R:'>,2TRVPTP4P5P5P6P8EPR45AT%O5R5%;D9I2:RW,>U,2TCC1NT6R6P1P7g00fjRXg00gJRY'M1n17=5XYdAm203ClRYb1b2b3X42W61<93%6E[^42^6NP1187@P7P3O3b0PQPO%k2R9PS%;<RX%g>5f2R>,?U,2TP6PYb1b2b3180@P1b0RZCePEP@P@PZPPPOPRPSPT1?:>,2TR:9AT4P5AI2>>,?W,2TCCP6PYb1b2b3X42X6N1<3A1:@@,8E[^42^6NP1%67P7P3O3b0DbCa1<MLP21:7D/1@RL111I118JRJ552X52P2%4=R=,1LRI/1<A521JX52RMP2%4;R;,17RN111<=52JX52P21:;<,17PM1M2K11N<P7P;P<PQPOP9PSP2%;;g00bhRNPUC@,2T,GTP6PYb1b2b3A52;0g00k;R;[P1b0PQPOP9PS1?UX,2TP6PYb1b2b3180<P1b0RXDKE=PIPQPOPRPSPTAATV:R:P5P:CCP6PYb1b2b3X42R:%63183@'<\B^42RBP1P8P7O2b0,`7E=1:=<,1LPLP=P<PQPOP9PSP2%;=PNPUC@,2T,GTP6PYb1b2b3A52=0P;[P1b0PXDKEc1BLGP:PBP11:8D/1@P3O2b09dLGE=b7PFPQPOP9PS%;?,>U,2TP6PYb1b2b3%6?P1b09FE?E=1EHCPQPOP9PS%;C,>U,2TP6PYb1b2b3%6CP1b09FHCE=W8X92o"). Qed.

Lemma y4_div7_magic : forall x, 0 <= x < 2^64 ->
  ((x - x * 2635249153387078803 / 2^64) / 2 + x * 2635249153387078803 / 2^64) / 4 = x / 7.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_y4fast ()) [] "h05heq_th17__arithh24__ffh34__p1h48__varmaph55__with64__x1h71zh82H0h93H12h:3H18h;2H6h<4__p2h=4__p3h>6__sat4h?6__sat5h@4__x2hA4__x3hB4__x4hC4__x5hD4__x6hE1HhF5heq_qhG5heq_rhH2H1hI3H10hJ3H11hK3H13hL3H14hM3H15hN3H16hO3H17hP3H19hQ2H2hR3H20hS3H21hT3H22hU2H3hV2H4hW2H5hX2H7hY2H8hZ2H9h[2Hah\6__sat2h]6__sat3h^6__sat6h_6__sat7h`6__sat8ha6__sat9hb5__x10hc4__x7hd4__x8he4__x9hf1ahg7fv_listhh8hyp_listhi3lmphj2zhhk2E1hl2Hmhm2Hqhn2Hrho2Hthp2Hxhq2T0hr1qhs1rht1thu1xp%0p%1p&0p;1p;2p;6p;3p;4p;5p;7p;8p;:p;<g0000j10Tg000Uj1=Tg0013k20aTg002Gj1?Tg002lR0j22Tg003Ij21Tg003fj23Tg004Fk208Tg0103k20YTg00M5j6iTg005Gj1yTg005gj1eTg006Gk10STg006ek10PTg007Ck10OTg007nj2VTg00KQk10JTg00Kok30GTg008Qk20DTg004mj2YTg0093k20CTg00:9k30@Tg00:Xk40?Tg001Pj27Tg00;Jj3|j2lTg00<Nj2NTg00Eik20:Tg00Cbj18Tg00FRj2^Tg00G>j2XTg00IFk206Tg00Iik10XTg001lj2HTg00l8k40WTg010Uk50VTg00Nek404Tg00OZk10TTg00PDj2xTg00Gjj3]Tg00Pdj2wTg00Sjk303Tg00QNk202Tg00R8j3vTg00TTj3uTg00U>k10QTg00Ufk400Tg00VLj7~Tg00<1R1j29Tg00Y@R2j25Tg00X;k60NTg011Ak40MTg00nKk60ITg00<jj2}Tg00=[j2dTg00>Lk20FTg00?4k30ETg00?Xj2cTg00@9j1rTg00@Rj2bTg00A9j2jTg00A_j2kTg00BEj2_Tg00CAj2pTg00DAj1RTg00Jnj3aTg00LRk30HTg00O@k30>Tg00W;k60KTg00W_k40LTg00X_k50=Tg009_j3[Tg00Y]j4sTg00ZHk701Tg00Zlj3mTg00HJk20<Tg00[Uk60;Tg00\9k705Tg00JKk30UTg00\]j8nTg00]Am:0_Tg00^2m<0^Tg00D_k20]Tg00E@k30\Tg00MSk20[Tg00N<k309Tg00Hhk40ZTg00^_R3f0R4'Np=4%04#0p=of2R5f1R6/74'Hp={%04#?#0#0p=\%?4#0#0#?p=Z%04#0#?#0p=`g00_=R715647[5p>0`f3R81256/545[7p=>1Y74p=BA[764p=6P7P6g00_[P4Csp=PP6g00`BR9g00`aR:P:g00aAR;P4g00aaR<K01p=;g00fjR=g00gJR>7[4p=q1N351764'Hp=A20:74p=:Am764p>07g00f>R??]64p=W20<74p=MP5P9P:P:P;P7P6g00bAP4CsP<K01p=<P6P9P:P:P;P4J0;p=OP5P9P:P:P;P6P4K05p=hB0U764p=UP8P9P:P:P;P5P6P4Gnp=z1N36/H4p=gP7P3P6P2P0P1g00cOR<g00clR@g00dIRAP4N:0_p>0RP7P3P5P2P0P1P<P@PAg00djS00P6P4N<0^p=tP7P6g00bhP4Csp=QA[743p=J1N64,H5p=L20]74p=SB0\764p=G20[74p=FB09756=m74p=IAm7649m75p=E%04#?p>0BB09764p=f%04#0#0#0#0#0#0#0p>0A%04#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=KP7P5P6P4H0Zp=@20674p=Cf6RAP9P:P:P;f5R<f4R1P8P9P:P:P;P5P6P4GnGnp=DP<P9P:P:P;P1P9P:P:P;P8P5K05P6P4Gnp=T%44R0g00eYR2#0RB#=RC%0BRD#0RE#0#oRF#=RG+0aRH7{4%?DS01#0#\#Z#`#\#Z#`#\#Z#`#\#Z#`#\#ZRI#?#=RJ,26RK/1HP7P7125JRL/1HRM,2H128JRN13NHRO80`4X77208LH12MH20YMHEiPLP4PH13LHC>RLePL11NHRL#B166LRLePL%y?RL%e?R?&0S7RM&0P7RP&0O7RQ1V73RR1V7CRS&0JF60G7RT'P';20DQ;RUP4P51Y=>S0220C45#qdB0@736H0?R>b2b4b5173HR=P4b1RVb09|NHAAOOH121JRO/1HRN#41NN1POPH%BN165NRNeRWPNp-0RXg00iHRY-0:7RZ%8YS03#8RY#:S04-07Zg00igR['^'X/WLR\P?%M6R]PPPQ20672R^9<QRR_1OQ85hQR`&0X:Ra1V7J,U^Rb9<QRS05CzPUP>b2b4b5X67W31H06R0%4K[^67^3XP417AHS06PAP<O3Rcb1b0PWPNPVb0RVH0WPOPHP1PVPWPNP\P?P]PPPQP`Pa1UT^9<QbCzPUP>b2b4b5X67X3X12H6,NK\0^67^3XPcb1b0I0VH041N51,g5RcePc&0T7Rc/xcRc#yS07%ecS08%y79]71S099]7A%e7S0:Q00P4P61w72Rc1w7BR060372027C9v705u7RKAu7c0R0g00hFRcQ02%=2R`00R6S0;g00jS,x7&0Q7'x#eS0<P7P@At`4KAt`40S0=H00bi#qdF~bgbh19<8RK128C'515<8R]'6R\eP\P719A1R\121C'5RNf7RW/9</1C/5<RV114C'6X77P711\C/51RO16V4X77%BO11NCP\P1PC12AJ/1HR\#B161\S0>eS0?Q0>PLP?PMPPPQP9P:P:P;1QSR,;QJ0NS0@PUP>b2b4b5%JCR;g00k;[S0AP4b1b0S0BH0MEi15A1R:P4J0IbE11KC/5811]C'6P711:CS0C%=DR],14%?2RK#?R9#=R\,1WRN'6X77P712C],1:164NX7711A\P713W\P7f8RN008\PNP\P6P4C>RVePVf9RV13V\Rd#B166dRdePdf:Rd/1\Re#B168eReePef;Re/2JS0D/1HRf#B16VfRfePfPLP?PMPP1V7\Rf,PR,;QPUP>b2b4b5173\RgP4b1b0bFbG7|\AA66\RhePhP7P815dNRh%=ERi'1PhPiP8128i,9hRj%4jRk17jiRl'H17ij?Lj3PkPl13d\Rl#B165lS0EeS0FQ0E11e\Rl#B161lS0GeS0HQ0Gf<Rl/2J/1HRk#B16dkS0IeS0JQ0If=Rk/2JRm/}HS0K%4m%4HRmf?Rn/2J/3H#4[[S0Lf>Ro/2JRp/dHS0M%4pf@Rp/2J/1H#4\m[S0N1}n\S0O%4nS0P%4\RqfARr/3\#4[[S0Q1dp\S0R%4pfBRp/1\#4\q[S0S20FCGS0T173CRq%4GP=[S0U[S0V%4CRsg00gjRtB0ECG6UW[S0WPm\t^[sS0XfCRG/5rRr/dCS0Y%4rfERr/5G/1C#4\s[S0ZfDRu/9pRv/dCS0[%4vfFRv/9uRu/1CRw#4\s[S0\19rG/cCS0]%r;RGPuPCPw13uCC>[S0^1luCS0_fGRu/9rRr/3CRw?AwC\qS0`1brCS0a17C3RrfHRw/9vRv/3CRx,7C?Lx3[S0b1jvCS0cfIRv/9uRu/1C#J\;S0d1kuCS0efJRu/9wRx/3C/6x\;S0fPc1_xCS0geS0hQ0gfKRx/5v/cCS0ifLRy/5uRuPC11uC13uCC>\GS0j1luCS0kfMRu/5xRx/3CRG?AGC\qS0l1bxCS0mfNRx/5yRy/3CRG,7C?LG3\rS0n1jyCS0ofO/5uRu/1C#J\;S0p1kuCS0qfPRu/5xRx/3C/6x\;S0rPc1_xCS0seS0tQ0sfQS0u/c\S0v%J\Rx#rfRR;P\11;\13;\C>[S0w1l;\S0xfSR;/3\Ry?Ay\\gS0y1b;\S0z17\3fTR;/3\Ry,7\?Ly3[S0{1j;\S0|fUR;/1\#J\xS0}1k;\S0~fVR;/3\/6;\xS10Pc1_;\S11eS12Q11fW/2J/cHS13%JHRx#rfXS14/2JRyPH11yH13yHC>[S151lyHS16fYS17/2JRy/3HRr?ArH\=S181byHS1917H3fZS1:/2JRy/3HRr,7H?Lr3[S1;1jyHS1<f[Ry/2JRr/1H#J\xS1=1krHS1>f\S1?/2JRr/3H/6r\xS1@Pc1_rHS1AeS1BQ1AP1g00hbRr1p3H'YP=eO1S1Cf]R=/2J/3HRx?AxHS1DPe1p3\,YrPgeO1S1Ef^Rg/3\Rx?Ax\S1FPp1p3C,YrPqeRqO1S1Gf_/5=/3CRr?ArCS1HPvPqO1S1If`S1J/9g/3CRr?ArCS1KP1PtPuP4P6O2XfsS1LPm^fsS1MQ0uPqO1S1NQ0U%8YRY#8Rq#8Ru#8Rr#8Rp#8Rx#8RG#8Rz#8R{#8R|#:%R2#SR2%:{R{'G%Fi%:pRp;IZ3E207Z{%?BR{#=#FR}%8|#8#8R|#8#:R~%0I$0B#?RI#=#F%:|'f%R{#S%:GRG'G%RI#SRI%:xRx'G1GIp%:q%oF$0A#K#K#KRF#=#FQ04'f3E3E3E7IZ/^['X'XRq%FJ%RF#S/GG%:YRY,G25E~7IZ%:zRz%:rRr5EZ/^['X,XG%RB#S/Gx=EzY%:uRu9EZG/^['X/WL'W,Wq'WP?%MW%Md7@1%MV?@<M7@5%MN?@dM%MARq7@87@6PPPQPQ%CDRD9<QRRG1PDT,;QPaPQPQ%CERE9<QR1OQlPaPQPQ%0KRz#0#CR~9<QR1OQkPaPQPQQ0@Pa%CBRB9a7^R2%CzRz,US=a7~'Q,;QCzPaPQPQA<QR2PaPQA<QRSPaA<QRzFDPaPQPQQ05PaPQA<QRTPa%0{#CR{9<QRFDPaPQ1QB{,;QPaPQ%CKR{Q01#C'Q,;QPaPQ%C9Rz/QE,;QRSPaPQ1Uf{=a7z,Q^,;QRzPaPQA<QRBA<QB^R~5hQPaPQ1UBT=a7D,Qb,;QRbPaPQ1OQo9hQ_Pa1V7iRD,U{:0H72R29<QRFDFDFDFDFDETETETPUP>b2b4b5X67X@7XA7XB7XC7XD7Xc7Xd7Xe7Xb7X3XX<XX=X%48R{?{8H1gWe%4eRB/HkQ0A151<RIPCPNPkC>[%4I%4d\s[12<JRs#4Q0P\m[16Wo16Vo16koPVP\PePoC>ALBedQ0DPlPHPoC>1glw15ko12ni'9#4[[[[[[[[[[[[[^67^@7^A7^B7^C7^D7^c7^d7^e7^b7^3X^<X^=XP4feRn/7HfcRo,5nRk/3CRw/7C13n\RB/7\Pw12nJRJ/1H11n\PBP=11kC13JHRJPgPoPnPWPAP<PvQ0uP;Q14Q17Q1:Q1?Q1JfbRvfdRkOJb1b?b>bjb8b;b9b:15=y12;i'9R;#4ebTbSbRbPb:bObNbMbLbKb9bJbIbZbYbXb;bWbVbUbQbHb8bEb\b]b>b?b^b_b`bab0bFbGQ0FQ0EQ0HQ0GQ0JQ0IQ0KQ0LQ0MQ0NQ0OQ0QQ0RQ0SQ0TQ0VQ0WQ0XQ0YQ0ZQ0[Q0\Q0]Q0^Q0_Q0`Q0aQ0bQ0cQ0dQ0eQ0fQ0hQ0gQ0iQ0jQ0kQ0lQ0mQ0nQ0oQ0pQ0qQ0rQ0tQ0sQ0vQ0wQ0xQ0yQ0zQ0{Q0|Q0}Q0~Q10Q12Q11Q13Q15Q16Q18Q19Q1;Q1<Q1=Q1>Q1@Q1BQ1AQ1CQ1DQ1EQ1FQ1GQ1HQ1IQ1KP1PtQ1LQ1MQ1NQ0U%F\%0F#o#=#FRF%R9#S/GYQ03#:,f}%K9#K#K#K#=#F/fZ3E9IFu9IFr7Ip7Ix/^[/WLP?A@q1M?@5M%M<9@M87@6PPPQPQPG1OQNPaPQPQ1OQV1PEf,;QPaPQPSPaPQPzPaPQPQ1OQdP~PaPQPbPaPQ1P^T,;Q9hQ_Pa1P2D,;QFDETFDETETPUP>b2b4b5X67X@7XA7XB7XC7XD7X3XX<XX=X1H{AA{NA\16AWP8P\P<PWC>ALl<1PsPAPHPNC>Q06,gA15WN12Vi'9/7i[[[[[[[^67^@7^A7^B7^C7^D7^3X^<X^=XP4%4o%4B17JHPBP=PJPgPoPnPWPAQ1:Q1?Q1JPvPkO@b1b?b>bjb8b;b9b:17;iebTbSbRbPb:bObNbMbLbKb9bJbIbZbYbXb;bWbVbUbQbHb8bEb\b]b>b?b^b_b`bab0bFbGH0440>Q07Q08Q099]7V9]7eQ0:Q00P4P6P02027iR61w7KRK5v7Av7K6:03705u7R0PcQ02Q0;Q0<P7P@Q0=At`40H00bi#qdF~bgbhPhPiP8PjC>eJ0KH0LbnbmbsbrQ0C/1]P:PCP]Q0BQ0?Q0>PLP?PMPP1V7],PR,;QPUP>b2b4b5173]P4b1b0I0=EiPOP4EibkbqblbobtWpXu7o"). Qed.

Lemma y4_mulhu7 : forall x, 0 <= x < 2^64 ->
  ((((x - (x * 2635249153387078803) ≫ 64 mod 18446744073709551616) mod 18446744073709551616) ≫ 1
     + (x * 2635249153387078803) ≫ 64) mod 18446744073709551616) ≫ 2 = x / 7.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_y4fast ()) [] "h04__x1h14__p1h27__arithh34__ffh48__varmaph55__with64__x2h75heq_th81zh94__x3h:1Hh;2Hah<4__p2h=6__sat3h>4__x4h?2Hxh@2T0hA6__sat1hB6__sat2hC6__sat4hD1thE1xp;1p;2p;3p;4p;5p;7p;6p;8g0000j10Tg000Uj1>Tg0013j2ZTg001Pj26Tg001lj24Tg002Gj1;Tg002lj2:Tg00kXj2STg003fj25Tg00<1j27Tg00Y@j2=Tg003Ij21Tg00<Nj29Tg004mj2HTg00Eij2ATg00Cbj1LTg00FRj2PTg00G>j2[Tg005Gj1gTg00Gjj3ITg005gj1fTg00HJj2OTg006ej1dTg007Cj1cTg007nj2DTg00IFj2MTg00Iij1bTg00JKj3TTg008Qj2~Tg0093j2|Tg009_j3aTg00:9j3{Tg00:Xj4zTg006Gj1yTg00KQj1xTg00Koj3vTg00l8j4uj2sTg010Uj5`Tg00Nej4_Tg011bj2tTg00=[j2^Tg00>Lj2rTg00?4j3qTg00CAj2pTg00DAj1oTg00D_j2nTg00E@j3mTg00Hhj4QTg00LRj3]Tg00Y]j4VTg00Jnj3jTg00ngj3UTg00oJj3WTg00Zlj3iTg00ZHj7XTg00[Uj6wTg00\9j7\Tg00\]j8RTg00M5j6hTg00^_R0f0R1'9p=2%01#0#0#0p=e%;1#0p=l%01#;#0#0p=K%;1#0#0#;p=G%01#0#;#0p=N%01#0p=}%01#0#0#0#0#0#0#0p=@g00_=R2f1R3;a1p=8Ai231p=?f2R4g00`BR5g00`aR6P6g00aAR7P2P3g00bAP1CVg00aaR8FXp=3P3P5P6P6P7P1Ewp=FP4P5P6P6P7P3P1F\p=Bf3R9P5P6P6P7P4P3P1GRp=YP4P5P6P6P7P2P3g00_[P1CVP8FXp=<f6R:P5P6P6P7f5R;f4R<P9P5P6P6P7P4P3P1GRGRp=JP3P5P6P6P7P1P8FXp=kP;P5P6P6P7P<P5P6P6P7P9P4F\P3P1GRp=CP2P<P9P4P3P1Ehp=E%21R5g00eYR8#0R=#>R>%0=R?#eR@#>RA'ZRB,61'4RC%l?#K#G#N#K#G#N#K#G#N#K#G#N#K#G#;#>RD,:3RE/SARF%}@#@#@#@#@#@#@#@#>RG'5,73/5GRH%>8RI'SRJ/=F/5GRK1Z>>RL'1%;8RM#;#>RN,14RO,81X821Z>IRP,1H1:4DRQ/SA,=1/5G/1L/8OX8211EBRR151G,74/5G/1P/=1/5G/1L/8OX82PRP211QBRR#219R4PQPB1H2R181RRReROPRp-0RSg00f>RTg00iHRU,A2RV%LURU#LRW,A2RX,?Vg00igRY'PRZ'[%gTR[3IR\%fTR]1O23R^%d2R_%c2R`1D20Ra1M28Rb53`Rc1F`95B`Rd%b6R61D2DRe9T2bRf93`aCY1~`7R7P1P4g00fjRgg00gJRh'H1|14=aghdA{203CzRhb3b4b5X02W11453Rg%2E[^02^1SP116<BP<P9O3Rib2b7POPRP[P]%y2RjP_1D2>Rk%x@5v2R@9<`aP7Phb3b4b5160BRlP1b2b7RmCuPQPBP4PmPOPRP\P]P^P_P`PdP6AT2@b93`fCYP7Phb3b4b5X02X1S1:B3,9E\g^02^1SPib2b7D`C_1914,45RiePiP317<1/5G/1P/=4/5G/1L11<NRi'8X821793Rg111P/=4/5G/1L/8iX8211g>RL/=3RP%>?Rf,11/8iX821:9DRi/1BRd,H2183dRdeR\PdP[P]P^P_P`A<`b@R^9B`cRRP6PRCYP7Phb3b4b5X02%23RR163BRO'4\C^02P1P;P<O2b2b7,t911Pf119N'8e15PG%2P16PG1sg>%2g160>RN17;9/1>#2[[1:<D/1BRf,H2184fRfeRCPf1:;DRm/^B%2m%2BRmf7RQ/:D/1B#2[[1r>A%2ARnPl[Rl\N%2>Rog00gjRpAq>A3UW;Pm\p^;of8Rp/7:Rq/^>%2qf:Rq/7p/1>#2\o[P4g00hb1p0>'HPNeO1Pl%LWRW#LRl#L,A21A2lRl%o8,n21A2WRW5m2/?V'?'?/PY1[lZ=IT[5ITP]P2P21O2<P4PjCQP31O29RlCQP_P`P`1M2MRM1M2=R=5]2RZ93`aP6P`A3`akR8P6PcFJP6P`P`AT2Me93`aP6P`A3`a@P61M2?R?93`aFJP6P`P2P=g00bhP?CV,k`P6P`1F`:A3`=M5B`P6P`P`A3`aM1F`QP6Aj2b=R?93`aECFJFJP7Phb3b4b5X02X62X92X>2X1SX<S1743Re#2%24R0\o[%2i%2:Ri\m[189;19<;,4Qf9RQ,4i1=;:#2[[[[[^02^62^92^>2^1S^<SP1f;Rm/6B%2Q1:mD/1BPmPQ17mQ/1>P4P;P:PpPqO;b2b=bAbBb=bCb7b:PgP>PgP\PdP[P]PjP_A<`akP7Phb3b4b5PNP1b2b7P\PdP[P]P21O24RNP3PjCQRqP_P`P`1F`<RpA3`=bRmP6A]2b=RQAT2kQ53`ECP7Phb3b4b5X02X62X1S1931Rk,441734RD1:>D'9[^02^62^1SP1%29P9P;P4O4b2b7D`19LgPCPf1A2U/?VRV,?X/PY=IT[RXP]P2PNP3PlCQP_P`A3`bZP6P`1F`;A<`M@5B`P61D2GRM9<`?FJP7Phb3b4b5X02X62X92X1S191e169B,4<1=49/6G[[^02^62^92^1SP1PiP:P<17:</1>P4P;O6b2b7b:C_9UPGDE15gGP\Pd1?WV/PY=IT[P]PqP_P`P`A3`a=PmP6P`P`PpP^P6A3`aQA<`QM5B`ECECP7Phb3b4b5X02X62X1S14Rk149O1749RO#216OG'4[[^02^62^1SP1%2;ROP9P;P4P<O5b2b79UgGDE153GP\PdPXP]PqP_P`P`PcA3`b=P6P`P`PpA<`=@P6A<`bM9B`cECECP7Phb3b4b5X02X62X1S1913,45164B,49164G,40[[^02^62^1SP1POP;P9P4P<O5b2b79U3GDEb@bDPFP[P]PjP_1D2A93`aP7Phb3b4b5PnP1b29WEADEPJP[P]PjP_1D2I93`aP7Phb3b4b5%2IP1b29WHIDE1SK>P[P]PjP_P8P7Phb3b4b5PoP1b29WK>DEW?XE2o"). Qed.

Section CANSEC1. Context {rc : runConstT}.
Section Y4FAST.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (DST dcap SS DT lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Notation seg := ((dcap + 3) / 4).
  Hypothesis TOK : x2_table_ok cells 11.
  Hypothesis ECB : cbs = firstn (Z.to_nat (4 * 2^11)) (x2_bytes' cells).
  Hypothesis LCB : zlen cbs = 8192.
  Hypothesis D8 : 8 <= DST.
  Hypothesis DC : 0 < dcap < 2^32.
  Hypothesis SG : 3 * seg < dcap.
  Hypothesis DL : DST + dcap <= lo.
  Hypothesis S0 : 16 <= SS.
  Hypothesis SL : SS + n <= lo.
  Hypothesis NSM : n < 2^26.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis DT0 : 0 < DT.
  Hypothesis CBL : DT + 4 + 8192 <= lo.
  Hypothesis DJ1 : DT + 4 + 8192 <= DST \/ DST + dcap <= DT.
  Hypothesis DJ3 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis LOS : lo <= SP - 4096.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SP47 : SP <= 2^47.
  Hypothesis DTA : DT mod 4 = 0.

  Notation DW := [(SP - 4096, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Notation Y4M := (RF_huf_y4s_iface.Y4M ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT lo src cbs).
  Notation SPS4 := (RF_huf_y4s_iface.SPS4 DST dcap SS DT src).
  Notation SPSL w0 w8 := (SPS4 w0 w8 Y4_M10 Y4_M7 (DST + dcap) SS (DST + 3 * seg) (DST + 2 * seg) (DST + seg)).
  Notation W4 a b c d := [Z_to_bv 64 a; Z_to_bv 64 b; Z_to_bv 64 c; Z_to_bv 64 d].

  Notation HO mm b0 IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3 x5 x7 x8 x10 x12 x20 x21 x24 x26 x27 x28 x29 x31 :=
    (MS (mkR (Z_to_bv 64 (-25)) (Z_to_bv 64 (SP + -512)) gp tp x5 (Z_to_bv 64 OP3) x7 x8 (Z_to_bv 64 IP2) x10
             (Z_to_bv 64 IP3) x12 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 IP0) (Z_to_bv 64 OP1) (Z_to_bv 64 OP2)
             (Z_to_bv 64 (SP + -168)) (Z_to_bv 64 OP0) (Z_to_bv 64 IP1) x20 x21 b0 (Z_to_bv 64 (SP + -136)) x24
             (Z_to_bv 64 (-16)) x26 x27 x28 x29 (Z_to_bv 64 (- (DT + 4) - 1)) x31)
        F (Z_to_bv 64 0x15cbc) fc None mm (seg_rom usegs)).

  Notation HI mm b0 b1 b2 b3 IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3 OL x9 x11 x14 x19 x21 x24 x28 :=
    (MS (mkR (Z_to_bv 64 (-25)) (Z_to_bv 64 (SP + -512)) gp tp (Z_to_bv 64 Y4_FT0) (Z_to_bv 64 OP3) (Z_to_bv 64 IP0) b1 x9
             (Z_to_bv 64 OL) x11 (Z_to_bv 64 Y4_FA2) (Z_to_bv 64 (DT + 4)) x14 (Z_to_bv 64 OP1) (Z_to_bv 64 OP2)
             (Z_to_bv 64 (SP + -168)) (Z_to_bv 64 OP0) x19 (Z_to_bv 64 IP1) x21 b0 (Z_to_bv 64 (SP + -136)) x24
             (Z_to_bv 64 (-16)) b3 (Z_to_bv 64 IP2) x28 b2 (Z_to_bv 64 (- (DT + 4) - 1)) (Z_to_bv 64 IP3))
        F (Z_to_bv 64 Y4_IH) fc None mm (seg_rom usegs)).

  Hypothesis WB : forall mm ws (w0 w8 w64 w72 w80 w88 w96 w104 w112 : Z) (b0 b1 b2 b3 : word)
                         IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3 IE0 IE1 IE2 IE3
                         (x1 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    Y4M mm (SPS4 w0 w8 w64 w72 w80 w88 w96 w104 w112) ws (W4 OP0 OP1 OP2 OP3) (W4 IP0 IP1 IP2 IP3) [b0; b1; b2; b3] ->
    nth_error ws 13 = Some (Z_to_bv 64 SS) ->
    nth_error ws 15 = Some (Z_to_bv 64 IE0) -> nth_error ws 16 = Some (Z_to_bv 64 IE1) ->
    nth_error ws 17 = Some (Z_to_bv 64 IE2) -> nth_error ws 18 = Some (Z_to_bv 64 IE3) ->
    SS <= IE0 <= SS + n -> SS <= IE1 <= SS + n -> SS <= IE2 <= SS + n -> SS <= IE3 <= SS + n ->
    SS <= IP0 -> IP0 + 8 <= SS + n -> SS <= IP1 -> IP1 + 8 <= SS + n ->
    SS <= IP2 -> IP2 + 8 <= SS + n -> SS <= IP3 -> IP3 + 8 <= SS + n ->
    DST <= OP0 <= DST + seg -> DST <= OP1 <= DST + 2 * seg -> DST <= OP2 <= DST + 3 * seg -> DST <= OP3 <= DST + dcap ->
    bv_unsigned b0 <> 0 -> bv_unsigned b1 <> 0 -> bv_unsigned b2 <> 0 -> bv_unsigned b3 <> 0 ->
    evt usegs POST (MS (mkR x1 (Z_to_bv 64 (SP + -512)) gp tp (Z_to_bv 64 Y4_FT0) x6 x7 x8 x9 x10 x11 (Z_to_bv 64 Y4_FA2)
                           x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x1667c) fc None mm (seg_rom usegs)).

  Ltac y4f_zl := repeat match goal with |- context [Z.of_nat (length ?l)] => change (Z.of_nat (length l)) with (zlen l) end.
  Ltac y4f_ucond C := unfold bv_ltu, bv_leu, bv_eqb in C; rewrite ?Z.shiftl_mul_pow2 in C by lia;
    rewrite ?unsigned_lit in C by lia; zify_bool C.
  Tactic Notation "y4f_if" ident(C) :=
    lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
      destruct (Bool.bool_dec c true) as [C|C];
      [ replace (if c then a else b) with a by (rewrite C; reflexivity)
      | apply Bool.not_true_is_false in C; replace (if c then a else b) with b by (rewrite C; reflexivity) ]
    end.
  Ltac y4f_c8 A := lazymatch goal with |- rw_cells _ _ ?a _ =>
    lazymatch type of A with u64arr _ _ ?b _ =>
      replace a with b by lia; apply RF_huf_x4body_kit.x4k_u64arr_c8; exact A end end.
  Ltac y4f_sp := try replace (Z_to_bv 64 (SP + -512 + 344)) with (Z_to_bv 64 (SP + -168)) by (f_equal; lia);
    try replace (Z_to_bv 64 (SP + -512 + 376)) with (Z_to_bv 64 (SP + -136)) by (f_equal; lia).

  Lemma y4m_body : forall mm mm' sps ws ops ips bts ops' ips' bts',
    Y4M mm sps ws ops ips bts ->
    munch [(DST, DST + dcap); (SP + -200, SP + -104)] mm mm' -> wmono usegs mm mm' -> mem_inv usegs mm' ->
    (exists buf', u8arr usegs mm' DST (map (Z_to_bv 8) buf') /\ zlen buf' = dcap) ->
    u64arr usegs mm' (SP + -200) ops' -> length ops' = 4%nat ->
    u64arr usegs mm' (SP + -168) ips' -> length ips' = 4%nat ->
    u64arr usegs mm' (SP + -136) bts' -> length bts' = 4%nat ->
    Y4M mm' sps ws ops' ips' bts'.
  Proof using All.
    intros mm mm' sps ws ops ips bts ops' ips' bts' X MU' WM' MI' OB O' LO' I' LI' B' LB'.
    destruct X as (BUF & SRCB & CBSB & STK & SPSA & LSPS & WSA & LWS & [jo J0] & OPA & LOP & IPA & LIP & BTA & LBT & FR & MI & MU & WM).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (LCB' : Z.of_nat (length cbs) = 8192) by exact LCB.
    unfold RF_huf_y4s_iface.Y4M.
    split; [exact OB|].
    split; [eapply bytes_at_transport; [exact SRCB| exact MU'| rewrite length_map; y4f_zl; cbn [disjoint_from]; lia]|].
    split; [eapply bytes_at_transport; [exact CBSB| exact MU'| cbn [disjoint_from]; lia]|].
    split; [eapply stk_transport_disjoint; [exact STK| exact MU'| exact WM'| cbn [disjoint_from]; lia]|].
    split; [eapply u64arr_transport; [exact SPSA| exact MU'| exact WM'| rewrite LSPS; cbn [disjoint_from]; lia]|].
    split; [exact LSPS|].
    split; [eapply u64arr_transport; [exact WSA| exact MU'| exact WM'| rewrite LWS; cbn [disjoint_from]; lia]|].
    split; [exact LWS|].
    split; [exists jo; eapply rw_cells_transport; [exact J0| exact MU'| exact WM'| cbn; lia]|].
    split; [exact O'|]. split; [exact LO'|]. split; [exact I'|]. split; [exact LI'|].
    split; [exact B'|]. split; [exact LB'|].
    split; [eapply rw_cells_transport; [exact FR| exact MU'| exact WM'| cbn; lia]|].
    split; [exact MI'|].
    split; [eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU']; unfold sub_fp; intros ?x; cbn; intuition lia]|].
    eapply wmono_trans; [exact WM| exact WM'].
  Qed.

  Lemma y4_inner : forall (r : nat) mm ws (w0 w8 : Z) (b0 b1 b2 b3 : word) IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3 OL
                          (ops ips bts : list word) (x9 x11 x14 x19 x21 x24 x28 : word),
    Y4M mm (SPSL w0 w8) ws ops ips bts ->
    (1 <= r)%nat -> OL <= OP3 + 5 * Z.of_nat r -> OP3 < OL ->
    OP0 + 10 * Z.of_nat r <= DST + seg -> OP1 + 10 * Z.of_nat r <= DST + 2 * seg ->
    OP2 + 10 * Z.of_nat r <= DST + 3 * seg -> OP3 + 10 * Z.of_nat r <= DST + dcap ->
    DST <= OP0 -> DST <= OP1 -> DST <= OP2 -> DST <= OP3 ->
    SS + 7 * Z.of_nat r <= IP0 -> IP0 + 8 <= SS + n -> SS + 7 * Z.of_nat r <= IP1 -> IP1 + 8 <= SS + n ->
    SS + 7 * Z.of_nat r <= IP2 -> IP2 + 8 <= SS + n -> SS + 7 * Z.of_nat r <= IP3 -> IP3 + 8 <= SS + n ->
    bv_unsigned b0 mod 512 <> 0 -> bv_unsigned b1 mod 512 <> 0 -> bv_unsigned b2 mod 512 <> 0 -> bv_unsigned b3 mod 512 <> 0 ->
    (forall mm' (b0' b1' b2' b3' : word) IP0' IP1' IP2' IP3' OP0' OP1' OP2' OP3'
            (x5 x7 x8 x10 x12 x20 x21 x24 x26 x27 x28 x29 x31 : word),
       Y4M mm' (SPSL w0 w8) ws (W4 OP0' OP1' OP2' OP3') (W4 IP0' IP1' IP2' IP3') [b0'; b1'; b2'; b3'] ->
       SS <= IP0' -> IP0' + 8 <= SS + n -> SS <= IP1' -> IP1' + 8 <= SS + n ->
       SS <= IP2' -> IP2' + 8 <= SS + n -> SS <= IP3' -> IP3' + 8 <= SS + n ->
       DST <= OP0' <= DST + seg -> DST <= OP1' <= DST + 2 * seg -> DST <= OP2' <= DST + 3 * seg ->
       OL <= OP3' <= DST + dcap ->
       bv_unsigned b0' mod 512 <> 0 -> bv_unsigned b1' mod 512 <> 0 ->
       bv_unsigned b2' mod 512 <> 0 -> bv_unsigned b3' mod 512 <> 0 ->
       evt usegs POST (HO mm' b0' IP0' IP1' IP2' IP3' OP0' OP1' OP2' OP3' x5 x7 x8 x10 x12 x20 x21 x24 x26 x27 x28 x29 x31)) ->
    evt usegs POST (HI mm b0 b1 b2 b3 IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3 OL x9 x11 x14 x19 x21 x24 x28).
Proof using All.
    induction r as [|r IH];
      intros mm ws w0 w8 b0 b1 b2 b3 IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3 OL ops ips bts x9 x11 x14 x19 x21 x24 x28
        X R1 OLr OLo Q0 Q1 Q2 Q3 P0 P1 P2 P3 I0 I0' I1 I1' I2 I2' I3 I3' M0 M1 M2 M3 K; [lia|].
    pose proof X as X0.
    destruct X as ([buf [BUFA LBUF]] & SRCB & CBSB & STK & SPSA & LSPS & WSA & LWS & J0 & OPA & LOP & IPA & LIP & BTA & LBT & FR & MI & MU & WM).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (LCB' : Z.of_nat (length cbs) = 8192) by exact LCB.
    assert (SGL : 0 <= seg <= dcap) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
    replace (Z_to_bv 64 (SP + -168)) with (Z_to_bv 64 (SP + -512 + 344)) by (f_equal; lia).
    replace (Z_to_bv 64 (SP + -136)) with (Z_to_bv 64 (SP + -512 + 376)) by (f_equal; lia).
    apply (y4_body_proof POST mm F fc gp tp (Z_to_bv 64 OL) b0 b1 b2 b3 x9 x11 x14 x19 x21 x24 x28
             (SP + -512) (DT + 4) DST dcap SS IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3 cells buf src ops ips bts);
      [ exact MI | exact TOK | rewrite <- ECB; exact CBSB | exact BUFA | exact LBUF | exact SRCB
      | y4f_c8 OPA | exact LOP | y4f_c8 IPA | exact LIP | y4f_c8 BTA | exact LBT
      | first [assumption | y4f_zl; lia] .. | ].
    intros mm' b0' b1' b2' b3' j21' j24' j28' nb0 nb1 nb2 nb3 d0 d1 d2 d3
      MU' WM' MI' OB' NB0 NB1 NB2 NB3 D0 D1 D2 D3 M0' M1' M2' M3' CO' CI' CB'.
    assert (X' : Y4M mm' (SPSL w0 w8) ws (W4 (OP0 + d0) (OP1 + d1) (OP2 + d2) (OP3 + d3))
                   (W4 (IP0 - nb0) (IP1 - nb1) (IP2 - nb2) (IP3 - nb3)) [b0'; b1'; b2'; b3']).
    { eapply y4m_body; [exact X0 | | exact WM' | exact MI' | exact OB' | | reflexivity | | reflexivity | | reflexivity].
      - replace (SP + -200) with (SP + -512 + 312) by lia. replace (SP + -104) with (SP + -512 + 408) by lia. exact MU'.
      - apply RF_huf_x4body_kit.x4k_c8_u64arr. replace (SP + -200) with (SP + -512 + 312) by lia. exact CO'.
      - apply RF_huf_x4body_kit.x4k_c8_u64arr. replace (SP + -168) with (SP + -512 + 344) by lia. exact CI'.
      - apply RF_huf_x4body_kit.x4k_c8_u64arr. replace (SP + -136) with (SP + -512 + 376) by lia. exact CB'. }
    clear MU' WM' MI' OB' CO' CI' CB'.
    y4f_sp.
    zstep.
    y4f_if C; y4f_ucond C.
    - eapply (IH mm' ws w0 w8 b0' b1' b2' b3' (IP0 - nb0) (IP1 - nb1) (IP2 - nb2) (IP3 - nb3)
                 (OP0 + d0) (OP1 + d1) (OP2 + d2) (OP3 + d3) OL);
        [exact X' | first [assumption | lia] .. | exact K].
    - zstep.
      eapply (K mm' b0' b1' b2' b3' (IP0 - nb0) (IP1 - nb1) (IP2 - nb2) (IP3 - nb3)
                (OP0 + d0) (OP1 + d1) (OP2 + d2) (OP3 + d3));
        [exact X' | first [assumption | lia] .. ].
Qed.

  Lemma y4_q10 : forall x, 0 <= x < 2^64 -> 0 <= x / 10 /\ 10 * (x / 10) <= x /\ x / 10 < 2^64.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_y4fast ()) ["CANSEC1"; "Y4FAST"] "h02Hah17__sat50h27__sat52h37__sat54h47__sat56h57__sat58h64__p1h74__x1h87__arithh94__ffh:7__sat48h;7__sat49h<7__sat51h=7__sat53h>7__sat55h?7__sat57h@7__sat59hA8__varmaphB5__withC4cstrhD5cstr0hE2HxhF1xp;1p;2p;3p;4p;6p;5p;7p;8g0000j12Tg000Uj11Tg0013j25Tg001Pj28Tg001lj2:Tg002Gj14Tg003Ij2BTg002lj2@Tg00<Nj2?Tg01@jj2>Tg01@Ej1=Tg01:_j1CTg00KQj1HTg013Tj1bTg01<Ej2YTg00<jj2XTg003fj2VTg00>Lj26Tg00?4j37Tg00Y@j2UTg00=[j2STg00CAj2RTg004mj2DTg005Gj1PTg005gj1OTg00HJj2NTg006ej1MTg007Cj1LTg007nj2;Tg00IFj2KTg00Y]j4ETg00[Uj6JTg00Iij1QTg008Qj2ITg0093j2TTg009_j3eTg00:9j3dTg00:Xj4cTg006Gj1aTg00l8j4]Tg02DMj3ZTg00Koj3[Tg00JKj3\Tg00lYj5WTg00Nej4GTg00ZHj7^Tg00\9j7_Tg00\]j8`Tg00^_R0f0R1'?p=01801p=3f1R2g00`BR3g00`aR4P4g00aAR5P1g00aaF^p=9f2R6P3P4P4P5P2P1F_p=Af3R7P3P4P4P5P6P2P1G`p=Fg00_=R8P2g00_[P1CEp=<%01R9g00eYR:#2R;#1R<%2;R=#2R>#2R?#2R@#2RA#1RB'5RC,81RD':%4;R;#2#1RE,B2RF#01@EF/?2RG18FCRF':P2PEp,3src,>8RH#=RI%CH#0RH%H>#bp,3cbs'>R>#=RJ%C>#0R>%HARAp,2sp'YRK%1?R?'XRL%0K%0?1VK?#0[[R?%4;R;#4#4#1RK,6<RM%3<RN%0K15<KRO#3[RP[RQ%0<RRg00gjRSA7<K2UW0RK%0O\S^0RRO%1@R@,6<RT%0@15<@RU#3[RV\NRWA7<@2VSX0RR@%0U\S^0RRU%1;R;,6<RX%0;15<;RY#3[RZ\NR[A7<;2VSX0RR;%0Y\S^0RRY16<BR\%0B%3C[R]\NR^A7<B2VSX0RRB%0C\S^0RR_%4:R`#2#4#2#1Ra,6<Rb%0a15<aRc#3[Rd\NReA7<a2VSX0RRa%0c\S^0RRRp,4dcap%1`'UR`%1=R='SRS%0`%0=1B`=#0[[R=P6g00hb1R0<'DPNeRNO1R`Pdf5PNO1RcP]f8PNO1RfPZf;PNO1RgPVf>PNO1RNPPp-0Rhg00f>Ri#PRj%OiRi1N82Rk%M8Rl%L8RmP81;80Rng00bA1K8:R:CE,9mRoPmP3P4P4P5P7EJR75Am%Q4R4PoCF1Im5R5P1P6g00fjRog00gJR3'D1T16=eo3dAd802CcR0b9bAbBX78W61:92%02[^78^6hP1fER9/8CP9fDR3O3b8b5b4b3b2b1b:b;b1b<b2b=b3b>b4b?b5b@bDbCPIPHPJP>PLP?PMPQPKPOPTPWP@PUPXP[P;PYP\P^PBP_PbPePaPRPSP=P`PdPcP]PfPZPgPVPNPPPjPi%a8Pl1;8ERo,<n,9mP5P0b9bAbB%3EP1b8b5b4b3b2b1b:b;b1b<b2b=b3b>b4b?b5b@bDbCRnC]PGPFAZ2EnP2PEPCPnPIPHPJP>PLP?PMPQPKPOPTPWP@PUPXP[P;PYP\P^PBP_PbPePaPRPSP=P`PdPcP]PfPZPgPVPNPPPjPiPkPlPm1;8<=[8ARA,<:,9m9Am7P4A\8oA,<:,9mCFP5P0b9bAbBX78X6h1:2D1@EC,82[^78^6hP1%09P9P3O3b8b5b4b3b2b1b:b;b1b<b2b=b3b>b4b?b5b@bDbCDWCGCGWEXF8o"). Qed.
  Lemma y4_q7 : forall x, 0 <= x < 2^64 -> 0 <= x / 7 /\ 7 * (x / 7) <= x /\ x / 7 < 2^64.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_y4fast ()) ["CANSEC1"; "Y4FAST"] "h02Hah17__sat50h27__sat52h37__sat54h47__sat56h57__sat58h64__p1h74__x1h87__arithh94__ffh:7__sat48h;7__sat49h<7__sat51h=7__sat53h>7__sat55h?7__sat57h@7__sat59hA8__varmaphB5__withC4cstrhD5cstr0hE2HxhF1xp;1p;2p;3p;4p;6p;5p;7p;8g0000j12Tg000Uj11Tg0013j25Tg001Pj28Tg001lj2:Tg002Gj14Tg003Ij2BTg002lj2@Tg00<Nj2?Tg01@jj2>Tg01@Ej1=Tg01:_j1CTg00KQj1HTg013Tj1bTg01<Ej2YTg00<jj2XTg003fj2VTg00>Lj26Tg00?4j37Tg00Y@j2UTg00=[j2STg00CAj2RTg004mj2DTg005Gj1PTg005gj1OTg00HJj2NTg006ej1MTg007Cj1LTg007nj2;Tg00IFj2KTg00Y]j4ETg00[Uj6JTg00Iij1QTg008Qj2ITg0093j2TTg009_j3eTg00:9j3dTg00:Xj4cTg006Gj1aTg00l8j4]Tg02DMj3ZTg00Koj3[Tg00JKj3\Tg00lYj5WTg00Nej4GTg00ZHj7^Tg00\9j7_Tg00\]j8`Tg00^_R0f0R1'?p=01801p=3f1R2g00`BR3g00`aR4P4g00aAR5P1g00aaF^p=9f2R6P3P4P4P5P2P1F_p=Af3R7P3P4P4P5P6P2P1G`p=Fg00_=R8P2g00_[P1CEp=<%01R9g00eYR:#2R;#1R<%2;R=#2R>#2R?#2R@#2RA#1RB'5RC,81RD':%4:RE#4#1RF,B2RG#01@FG/?2RH18GCRG':P2PFp,3src,>8RI#=RJ%CI#0RI%H>#bp,3cbs'>R>#=RK%C>#0R>%HARAp,2sp'YRL%1?R?'XRM%0L%0?1VL?#0[[R?%4;#4R;#4#4#1RL,6<RN%3<RO%0L15<LRP#3[RQ[RR%0<RSg00gjRTA7<L2UW0RL%0P\T^0SRP%1@R@,6<RU%0@15<@RV#3[RW\ORXA7<@2VTX0SR@%0V\T^0SRV%1;R;,6<RY%0;15<;RZ#3[R[\OR\A7<;2VTX0SR;%0Z\T^0SRZ16<BR]%0B%3C[R^\OR_A7<B2VTX0SRB%0C\T^0SR`%2E#4#2#1Ra,6<Rb%0a15<aRc#3[Rd\OReA7<a2VTX0SRa%0c\T^0SRSp,4dcap%1E'URE%1=R='SRT%0E%0=1BE=#0[[R=P6g00hb1R0<'DPOeROO1REPdf5POO1RcP^f8POO1RfP[f;POO1RgPWf>POO1ROPQp-0Rhg00f>Ri#PRj%OiRi1N82Rk%M8Rl%L8RmP81;80Rng00bA1K8:R:CE,9mRoPmP3P4P4P5P7EJR75Am%Q4R4PoCF1Im5R5P1P6g00fjRog00gJR3'D1T16=eo3dAd802CcR0b9bAbBX78W61:92%02[^78^6hP1fER9/8CP9fDR3O3b8b5b4b3b2b1b:b;b1b<b2b=b3b>b4b?b5b@bDbCPJPIPKP>PMP?PNPRPLPPPUPXP@PVPYP\P;PZP]P_PBP`PbPePaPSPTP=PEPdPcP^PfP[PgPWPOPQPjPi%a8Pl1;8FRo,<n,9mP5P0b9bAbB%3FP1b8b5b4b3b2b1b:b;b1b<b2b=b3b>b4b?b5b@bDbCRnC]PHPGAZ2FnP2PFPCPnPJPIPKP>PMP?PNPRPLPPPUPXP@PVPYP\P;PZP]P_PBP`PbPePaPSPTP=PEPdPcP^PfP[PgPWPOPQPjPiPkPlPm1;8<=[8ARA,<:,9m9Am7P4A\8oA,<:,9mCFP5P0b9bAbBX78X6h1:2D1@FC,82[^78^6hP1%09P9P3O3b8b5b4b3b2b1b:b;b1b<b2b=b3b>b4b?b5b@bDbCDWCGCGWEXF8o"). Qed.

  Lemma y4_outer : forall (fuel : nat) mm ws (w0 w8 : Z) (b0 b1 b2 b3 : word) IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3
                          IE0 IE1 IE2 IE3 (x5 x7 x8 x10 x12 x20 x21 x24 x26 x27 x28 x29 x31 : word),
    Y4M mm (SPSL w0 w8) ws (W4 OP0 OP1 OP2 OP3) (W4 IP0 IP1 IP2 IP3) [b0; b1; b2; b3] ->
    nth_error ws 13 = Some (Z_to_bv 64 SS) ->
    nth_error ws 15 = Some (Z_to_bv 64 IE0) -> nth_error ws 16 = Some (Z_to_bv 64 IE1) ->
    nth_error ws 17 = Some (Z_to_bv 64 IE2) -> nth_error ws 18 = Some (Z_to_bv 64 IE3) ->
    SS <= IE0 <= SS + n -> SS <= IE1 <= SS + n -> SS <= IE2 <= SS + n -> SS <= IE3 <= SS + n ->
    DST + dcap - OP3 < 5 * Z.of_nat fuel ->
    SS <= IP0 -> IP0 + 8 <= SS + n -> SS <= IP1 -> IP1 + 8 <= SS + n ->
    SS <= IP2 -> IP2 + 8 <= SS + n -> SS <= IP3 -> IP3 + 8 <= SS + n ->
    DST <= OP0 <= DST + seg -> DST <= OP1 <= DST + 2 * seg -> DST <= OP2 <= DST + 3 * seg -> DST <= OP3 <= DST + dcap ->
    bv_unsigned b0 mod 512 <> 0 -> bv_unsigned b1 mod 512 <> 0 -> bv_unsigned b2 mod 512 <> 0 -> bv_unsigned b3 mod 512 <> 0 ->
    evt usegs POST (HO mm b0 IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3 x5 x7 x8 x10 x12 x20 x21 x24 x26 x27 x28 x29 x31).
Proof using All.
    exact (RF_huf_y4fastb.y4_outer_b ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT lo src cells cbs
             TOK ECB LCB D8 DC SG DL S0 SL NSM BYS DT0 CBL DJ1 DJ3 LOS SP16 SP47 DTA WB y4_mulhu10 y4_mulhu7 y4_inner).
Qed.

End Y4FAST.
End CANSEC1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
