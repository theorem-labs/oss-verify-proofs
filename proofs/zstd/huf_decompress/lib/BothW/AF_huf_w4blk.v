(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.

From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_w4m.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_w4blk () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib6ZArith4ZdivAZ_div_mod_eq_fullK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2leC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr04C47Corelib4Init5Logic8eq_ind_rK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or01I46Stdlib;setoid_ring<Ring_polynom5PExpr00I47Corelib4Init9Datatypes4prod00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr07C56Stdlib6ZArith6BinInt1Z4to_NK46Stdlib;setoid_ring<Ring_polynom5PExpr09K46Stdlib;setoid_ring<Ring_polynom5PExpr06K46Stdlib;setoid_ring<Ring_polynom5PExpr05I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C56Stdlib6ZArith6BinInt1Z:div_uniqueC47Corelib4Init5Logic6eq_symK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_divC56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substK47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterK47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib;setoid_ring<Ring_polynom3Mon00I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundc5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_w4blk=w4_div5_magicC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z8mul_commC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC56Stdlib6ZArith6BinInt1Z7div_addC47Corelib4Init5Logic6eq_indc5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_w4blk=w4_div7_magicC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z:mul_div_leC4ELinuxProcessSemantics5Riscv7Prelude5bvmapI45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02K4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subK4ELinuxProcessSemantics5Riscv5Instr5instr0BC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_mulhuC4ELinuxProcessSemantics5Riscv3Sem7mul_divC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7m_mulhuK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addc5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_w4blk9w4_mulhu7c5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_w4blk9w4_mulhu5c5ARocqVerifyHarness?AgentSubmission5BothW<AF_huf_w4blk;w4_land_modC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeAunsigned_lit_landC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics5Riscv5Instr5instr06K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI47Corelib4Init9Datatypes3nat00K4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_w4m6AW4_M5C5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_w4m6AW4_M7C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5mulop04K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:munch_reflC5ARocqVerifyHarness?AgentSubmission3Lib5Frame:wmono_reflK4ELinuxProcessSemantics5Riscv5Instr5instr02C56Stdlib6ZArith6BinInt1Z6shiftlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_auipcC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7b_auipcC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib4StepDrw_cells_store_ok_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_boundC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC5ARocqVerifyHarness?AgentSubmission3Lib4StepArw_cells_store_okC5ARocqVerifyHarness?AgentSubmission3Lib4StepDmem_inv_store_cbytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cell_updC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC47Corelib4Init9Datatypes6lengthC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8I47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst7Inj_Z_ZC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK4ELinuxProcessSemantics5Riscv5Instr5aluop03".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).


Lemma w4_div5_magic : forall x, 0 <= x < 2^64 -> (x * 14757395258967641293 / 2^64) / 4 = x / 5.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_w4blk ()) [] "h07__arithh14__ffh28__varmaph35__with42H0h52Hah64__p1h76__sat0h86__sat1h96__sat2h:6__sat3h;4__x1h<4__x2h=4__x3h>4__x4h?1ah@2zhhA5heq_qhB5heq_rhC1xhD1HhE2H1hF2H2hG2H3hH2H4hI4__p2hJ6__sat4hK6__sat5hL4__x5hM2HqhN2HrhO2HxhP7fv_listhQ8hyp_listhR3lmphS1qhT1rhU1zp%0p&0p;1p;2p;3p;4p;6p;7p;5p;8p;:p;<g0000j10Tg000Uj1;Tg0013j2iTg001Pj22Tg001lj27Tg002Gj19Tg002lR0j25Tg003Ij26Tg003fj28Tg004Fk20ETg004mj2?Tg005Gj1UTg005gj1MTg006Gk10<Tg006ek10;Tg007Ck103Tg007nj2GTg008Qj2yTg0093j2xTg009_j3JTg00:9j3uTg00:Xj4tTg00;Jj3rk20JTg00<1R1j2CTg00<Nj2VTg00<jj2lTg00=[j2kTg00>Lj2[Tg00?4j3ZTg00?Xj2jTg00@9k10KTg00@Rk20ITg00A9k20HTg00A_k20GTg00BEk20DTg00CAj2hTg00Cbj1@Tg00DAj1gTg00D_j2fTg00E@j3dTg00Eij2cTg00FRj2bTg00G>k20ATg00Gjj3LTg00HJj2TTg00Hhj4HTg00IFj2FTg00Iik10:Tg00JKj3RTg00Jnk302Tg00KQj1`Tg00Koj3_Tg00LRk301Tg00M5j6QTg00MSj2^Tg00N<j3PTg00Nej4zTg00O@j3|Tg00OZj1}Tg00PDj2OTg00Pdj2\Tg00QNj2]Tg00R8j3NTg00Rbj1wTg00S@j3vTg00Sjk304Tg00TTk305Tg00U>k107Tg00Ufk408Tg00VLk709Tg00W;j6qTg00W_k40=Tg00X;k60>Tg00X_k50?Tg00Y@R2k20@Tg00Y]j4XTg00ZHj7oTg00Zlk30BTg00[Uk60CTg00\9j7nTg00\]j8WTg00]Al:mTg00^2m<0FTg00^_R3f0R4'Vp=1%04#0p=e%04#0#9#9p={%04#0#9#9#0#0#9#9p=>%04#9p=sg00_=R5f1R6;J4p=4f2R7/5600@4p=<P5P6g00_[P4CXp=DP6g00`BR8g00`aR9P9g00aAR:P4g00aaFop=3%94#0p=pAJ543p=Y1c54p=AB0B564p=:P5P6g00bAP4CXp=EP6P8P9P9P:P4J0Cp=SP7P8P9P9P:P6P4Fnp=If6R;P8P9P9P:f5R<f4R=f3R>P8P9P9P:P7P6P4GWGWp=BP5P6g00bhP4CXp=KP>P8P9P9P:P7P6P4GWp>00%04#0#0#0p=~%04#0#0#0#0#0#0#0p==P5P3P6P2P0P1g00cOR?g00clR@g00dIRAP4M:mp>06P5P3P7P2P0P1P?P@PAg00djS00P6P4N<0Fp=a%14g00eYRA#0R?#;R1%0?R0#eR2#eRB#;RC'iRD,24'7P5%9ARE#{#>#>#>#>#>#>#>#sRF#;RG,56RH%;0RI,5D'6%9?RJ#;RK,67,44XU5166KP5187KP520E>KA<K64,4>RLePL18=KRL,?5146LRLePL16<KRL,?514>LRLePLg00f>RL#URM%MLRN&0<5RO&0;5RP&035RQ1G53RR1G5KRS'D'31yQ:RTP4P7g00fjRUg00gJRV'?S011x47=JUVdAu536CtRWb1b2b3123KRXP4b0bAbB9r=K%16126K'7RYePYP5P>15<GRY%p2R2#;RZ,i1R['6PYP[P>15>[,CYR\%1\R]12\[R^'712[\1V\3'7P]P^P5A<K>7S02154G15=[R^'CR]#1XC518<KR_,?5147_R_eS03P_16;KR`,?514=`R`eS04P`f7Ra/lKS05%1aRb%1KRcf9Rd/8K#1[[S06f8Re/kKS07%1ef:Rf/6K#1\c[S081[1CS091231Rg%1C123D[Rh[S0:%11Rig00gjRjAZ1C6UW5S0;%1DRC\j^5iS0<1[1ZS0=%1Z123[[Rk\gS0>AZ1Z6VjX5iS0?%1[Rl\j^5iS0@f=/jKS0A%YKRm$0Kf>Rn16nK18nK5<K'4[S0B20JnKS0Cf?Ro/8KRp#112pK'7\XS0D20IoKS0E12K3f@Rp/8KRq,2K1Vq3'7[S0F20HpKS0GfARq/6K#Y\mS0H20GqKS0IfBRr/8K/4r\mS0Jg00hFS0K20DrKRmeS0LPmP=g00hbRs1h3K'?PXeO1S0MfC/8KRX#112XK'7RXP6PjPdP4P6O2X?iRdPl^?iRlPf1h31,?sPgeRgO1RsPkP=PjPnP4P6O2X?iRnPC^?iRiPoPgO1RgPhp-0Rog00iHRC#@Rt#@Ru#@Rv#@Rw#ARx%gA,f5%Av5d5Rv%gF,f5%Au5d51c5CRC':':':%@wRw#@#A,:Cg00igRu'b+0A=LLMPNP5P51T5=P7POCHRFP6P51T5<P>POCHCHPPPQ1F50R0,ER,3Q1SQa5IQ&0:9RyPQPQ1F5ERE,ER,3QRzPyPQ1ERS,3QPy1F5JRJ,ER,3QFBPyPQ1F5AR{/KJ,3QPyPQ1F5?RJ/K0,3QR|PyPQ1SQe9IQzPyAR5S{>025JRJ1G5G5R51G51Re%`25_5R29R5{6015R{,ER,3QH00FBFBPTPWb1b2b3X;5X<5X=5X>5XL5X6oWI%1>R}/7<Pb\c\}147;14=;%1;/7fA<K<;/5G15<['C#1[[[[[^;5^<5^=5^>5^L5^6o^IoP4fKRf/2D18fKR}/2K16fKP}PffHRcfIRbPaPrfDfERrfJR~O<b0b:b9b@b8b7b@b4A<Kqp/5G15q['CRq#1ebHbGbFbEb4bDb7b8b9b:bJbKbAbBP<P6EQP5Q0212][XC5Q03P_Q04P`Q05Q06Q07Q08Q09Q0:Q0;Q0<Q0=Q0>Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0FQ0GQ0HQ0IQ0JQ0LPmQ0MPXP6PjPdPlPsPkP=PjPnPiPgPh%~B#=#=#=#=#=#=#=#;,^5Rh%Aw5P5AP5hx%At1^5K=P5C':,:v':':/bu=LLMPNP5PFP61T5>CHPPPQ1SQ;1D0S,3Q5IQPyPQP|PyPQ1KEJ,3QPyPQ%`B9_5eRe,DE,3Q9IQzPy1D{2,3QFBFBPTPWb1b2b3X;5X<5X=5X>5X6o12>K,7=147=A<K7>,4=%1<12<D'7A<K=</5G/C^/2[[[[[^;5^<5^=5^>5^6oP4%1}P}PfPcPbPaPrfGP~O9b0b:b9b@b8b7b@b412q[ebHbGbFbEb4bDb7b8b9b:bJbKbAbBP<P6EQCz3|%}5R</O<R<#U%M<%U59L5=9L5;%M5Q00P4P61\5A1]5G5N5RG1]51%wZ5v5RZ1\5?R?5N5AN5?Z:045G6055R?Q0KQ01%;ARA0066g00jS,O5&075'O#MP5P@AaA4GAaA4?H08bR=JUVdK09bPbQA<[>\,4YeEqH0=bNbMbTbS16HD/6IPHPDPIPMPNPOPPPQP8P9P9P:1KeR,3QJ0>PTPWb1b2b3%YDg00k;[P4b0PMPNPOPP1G5I,DR,3QPTPWb1b2b3123IP4b0I0?EQWOXC5o"). Qed.

Lemma w4_mulhu5 : forall x, 0 <= x < 2^64 ->
  ((x * 14757395258967641293) ≫ 64 mod 18446744073709551616) ≫ 2 = x / 5.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_w4blk ()) [] "h07__arithh14__ffh28__varmaph35__with44__x1h54__p1h61zh71Bh82Hxh91xp;1p;2p;3p;6p;4p;5p;7p;8g0000j10Tg000Uj18Tg0013j2ITg001Pj27Tg001lj29Tg002Gj11Tg002lj2=Tg00kXj2DTg003fj2?Tg003Ij22Tg009_j3<Tg00Eij2HTg00Cbj1FTg00Zlj3ZTg00FRj2YTg00G>j2XTg005Gj1WTg00Gjj3VTg005gj1TTg00HJj2RTg006ej1QTg007Cj1PTg007nj2;Tg00IFj2OTg00[Uj6NTg00Iij1KTg00JKj3CTg008Qj2JTg004mj2STg0093j2iTg00:9j3hTg00:Xj4gTg006Gj1fTg00KQj1eTg00Koj3cTg00l8j4bTg00lYj5aTg00Nej4_Tg00mEj2^Tg00nJj3`Tg00M5j6ATg00nmj3GTg00<Nj2]Tg00Y]j4ETg00ZHj7\Tg00\9j7dTg00\]j8[Tg00^_R0f0R1']p=4%01#0#0#0p=M%01#0#1#1p=U%01#0#1#1#0#0#1#1p=5%01#1p=L%01#0p=j%01#0#0#0#0#0#0#0p=6g00_=R2f1R3g00bAP1CEp=:P3g00`BR4g00`aR5P5g00aAR6P1g00aaF\p=3f2R7P4P5P5P6P3P1Fdp=>f3R8P4P5P5P6P7P3P1G[p=BP2P3g00_[P1CEp=@%41R9g00eYR:#0R;#8R<%0;#MR=#8R>'IR?,71R@'9RAP2%1:#U#5#5#5#5#5#5#5#L#8RB,=3RC/D>RD%j=#6#6#6#6#6#6#6#8RE'?RF1I<<RG'2%1;#8R;,27RH9<21X62P212C?RI1?1E/2G=<2HX62%4IRH17I?RIPCP?p-0RJg00f>RKg00iHRL,H2RM%FL#F,H29Z2Mg00ig'Y'X%WKRM3VRL%TKRK1R23RN%Q2RO%P2RP1;20RQ1O2:R:':,3PRRPPP4P5P5P6P8ENR45>P%K5R51;2B9C2:RS,:Q,3PCB1JP6R6P1P7g00fjRTg00gJRU'S1i17=<TUdAh203CgRUb1b2b3X42W51993%4C[^42^5JP1177?P7P3O3b0PMPK%f2R9PO1;2<RT%e=5c2R=,@Q,3PP6PUb1b2b3170?P1b0R0CbPCP?P?P0PLPKPNPOPP1@:=,3PR:9>P4P5AC2==,@S,3PCBP6PUb1b2b3X42X5J193@1=??,7C[^42^5JP1%47P7P3O3b0DaC_19HIP21=7B/2?RI121G128;5<2X621^731?IEPMPKPNPOPPA>PR:R:P5P:CBP6PUb1b2b3X42%43173?'9\A^42P11=8B/2?P3O2b09`IEEAb7PDPMPKP9PO1;2>,:Q,3PP6PUb1b2b3%4>P1b09GC>EA1DF<PMPKP9PO1:QT,3PP6PUb1b2b3%4<P1b09GF<EAW8X92o"). Qed.

Lemma w4_div7_magic : forall x, 0 <= x < 2^64 ->
  ((x - x * 2635249153387078803 / 2^64) / 2 + x * 2635249153387078803 / 2^64) / 4 = x / 7.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_w4blk ()) [] "h05heq_th17__arithh24__ffh34__p1h48__varmaph55__with64__x1h71zh82H0h93H12h:3H18h;2H6h<4__p2h=4__p3h>6__sat4h?6__sat5h@4__x2hA4__x3hB4__x4hC4__x5hD4__x6hE1HhF5heq_qhG5heq_rhH2H1hI3H10hJ3H11hK3H13hL3H14hM3H15hN3H16hO3H17hP3H19hQ2H2hR3H20hS3H21hT3H22hU2H3hV2H4hW2H5hX2H7hY2H8hZ2H9h[2Hah\6__sat2h]6__sat3h^6__sat6h_6__sat7h`6__sat8ha6__sat9hb5__x10hc4__x7hd4__x8he4__x9hf1ahg7fv_listhh8hyp_listhi3lmphj2zhhk2E1hl2Hmhm2Hqhn2Hrho2Hthp2Hxhq2T0hr1qhs1rht1thu1xp%0p%1p&0p;1p;2p;6p;3p;4p;5p;7p;8p;:p;<g0000j10Tg000Uj1=Tg0013k20aTg002Gj1?Tg002lR0j22Tg003Ij21Tg003fj23Tg004Fk208Tg00oVk20YTg00M5j6iTg005Gj1yTg005gj1eTg006Gk10STg006ek10PTg007Ck10OTg007nj2VTg00KQk10JTg00Kok30GTg008Qk20DTg004mj2YTg0093k20CTg00:9k30@Tg00:Xk40?Tg001Pj27Tg00;Jj3|j2lTg00<Nj2NTg00Eik20:Tg00Cbj18Tg00FRj2^Tg00G>j2XTg00IFk206Tg00Iik10XTg001lj2HTg00l8k40WTg0108k50VTg00Nek404Tg00OZk10TTg00PDj2xTg00Gjj3]Tg00Pdj2wTg00Sjk303Tg00QNk202Tg00R8j3vTg00TTj3uTg00U>k10QTg00Ufk400Tg00VLj7~Tg00<1R1j29Tg00Y@R2j25Tg00X;k60NTg010dk40MTg011Ek60ITg00<jj2}Tg00=[j2dTg00>Lk20FTg00?4k30ETg00?Xj2cTg00@9j1rTg00@Rj2bTg00A9j2jTg00A_j2kTg00BEj2_Tg00CAj2pTg00DAj1RTg00Jnj3aTg00LRk30HTg00O@k30>Tg00W;k60KTg00W_k40LTg00X_k50=Tg009_j3[Tg00Y]j4sTg00ZHk701Tg00Zlj3mTg00HJk20<Tg00[Uk60;Tg00\9k705Tg00JKk30UTg00\]j8nTg00]Am:0_Tg00^2m<0^Tg00D_k20]Tg00E@k30\Tg00MSk20[Tg00N<k309Tg00Hhk40ZTg00^_R3f0R4'Np=4%04#0p=of2R5f1R6/74'Hp={%04#?#0#0p=\%?4#0#0#?p=Z%04#0#?#0p=`g00_=R715647[5p>0`f3R81256/545[7p=>1Y74p=BA[764p=6P7P6g00_[P4Csp=PP6g00`BR9g00`aR:P:g00aAR;P4g00aaR<K01p=;g00fjR=g00gJR>7[4p=q1N351764'Hp=A20:74p=:Am764p>07g00f>R??]64p=W20<74p=MP5P9P:P:P;P7P6g00bAP4CsP<K01p=<P6P9P:P:P;P4J0;p=OP5P9P:P:P;P6P4K05p=hB0U764p=UP8P9P:P:P;P5P6P4Gnp=z1N36/H4p=gP7P3P6P2P0P1g00cOR<g00clR@g00dIRAP4N:0_p>0RP7P3P5P2P0P1P<P@PAg00djS00P6P4N<0^p=tP7P6g00bhP4Csp=QA[743p=J1N64,H5p=L20]74p=SB0\764p=G20[74p=FB09756=m74p=IAm7649m75p=E%04#?p>0BB09764p=f%04#0#0#0#0#0#0#0p>0A%04#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=KP7P5P6P4H0Zp=@20674p=Cf6RAP9P:P:P;f5R<f4R1P8P9P:P:P;P5P6P4GnGnp=DP<P9P:P:P;P1P9P:P:P;P8P5K05P6P4Gnp=T%44R0g00eYR2#0RB#=RC%0BRD#0RE#0#oRF#=RG+0aRH7{4%?DS01#0#\#Z#`#\#Z#`#\#Z#`#\#Z#`#\#ZRI#?#=RJ,26RK/1HP7P7125JRL/1HRM,2H128JRN13NHRO80`4X77208LH12MH20YMHEiPLP4PH13LHC>RLePL11NHRL#B166LRLePL%y?RL%e?R?&0S7RM&0P7RP&0O7RQ1V73RR1V7CRS&0JF60G7RT'P';20DQ;RUP4P51Y=>S0220C45#qdB0@736H0?R>b2b4b5173HR=P4b1RVb09|NHAAOOH121JRO/1HRN#41NN1POPH%BN165NRNeRWPNp-0RXg00iHRY-0:7RZ%8YS03#8RY#:S04-07Zg00igR['^'X/WLR\P?%M6R]PPPQ20672R^9<QRR_1OQ85hQR`&0X:Ra1V7J,U^Rb9<QRS05CzPUP>b2b4b5X67W31H06R0%4K[^67^3XP417AHS06PAP<O3Rcb1b0PWPNPVb0RVH0WPOPHP1PVPWPNP\P?P]PPPQP`Pa1UT^9<QbCzPUP>b2b4b5X67X3X12H6,NK\0^67^3XPcb1b0I0VH041N51,g5RcePc&0T7Rc/xcRc#yS07%ecS08%y79]71S099]7A%e7S0:Q00P4P61w72Rc1w7BR060372027C9v705u7RKAu7c0R0g00hFRcQ02%=2R`00R6S0;g00jS,x7&0Q7'x#eS0<P7P@At`4KAt`40S0=H00bi#qdF~bgbh19<8RK128C'515<8R]'6R\eP\P719A1R\121C'5RNf7RW/9</1C/5<RV114C'6X77P711\C/51RO16V4X77%BO11NCP\P1PC12AJ/1HR\#B161\S0>eS0?Q0>PLP?PMPPPQP9P:P:P;1QSR,;QJ0NS0@PUP>b2b4b5%JCR;g00k;[S0AP4b1b0S0BH0MEi15A1R:P4J0IbE11KC/5811]C'6P711:CS0C%=DR],14%?2RK#?R9#=R\,1WRN'6X77P712C],1:164NX7711A\P713W\P7f8RN008\PNP\P6P4C>RVePVf9RV13V\Rd#B166dRdePdf:Rd/1\Re#B168eReePef;Re/2JS0D/1HRf#B16VfRfePfPLP?PMPP1V7\Rf,PR,;QPUP>b2b4b5173\RgP4b1b0bFbG7|\AA66\RhePhP7P815dNRh%=ERi'1PhPiP8128i,9hRj%4jRk17jiRl'H17ij?Lj3PkPl13d\Rl#B165lS0EeS0FQ0E11e\Rl#B161lS0GeS0HQ0Gf<Rl/2J/1HRk#B16dkS0IeS0JQ0If=Rk/2JRm/}HS0K%4m%4HRmf?Rn/2J/3H#4[[S0Lf>Ro/2JRp/dHS0M%4pf@Rp/2J/1H#4\m[S0N1}n\S0O%4nS0P%4\RqfARr/3\#4[[S0Q1dp\S0R%4pfBRp/1\#4\q[S0S20FCGS0T173CRq%4GP=[S0U[S0V%4CRsg00gjRtB0ECG6UW[S0WPm\t^[sS0XfCRG/5rRr/dCS0Y%4rfERr/5G/1C#4\s[S0ZfDRu/9pRv/dCS0[%4vfFRv/9uRu/1CRw#4\s[S0\19rG/cCS0]%r;RGPuPCPw13uCC>[S0^1luCS0_fGRu/9rRr/3CRw?AwC\qS0`1brCS0a17C3RrfHRw/9vRv/3CRx,7C?Lx3[S0b1jvCS0cfIRv/9uRu/1C#J\;S0d1kuCS0efJRu/9wRx/3C/6x\;S0fPc1_xCS0geS0hQ0gfKRx/5v/cCS0ifLRy/5uRuPC11uC13uCC>\GS0j1luCS0kfMRu/5xRx/3CRG?AGC\qS0l1bxCS0mfNRx/5yRy/3CRG,7C?LG3\rS0n1jyCS0ofO/5uRu/1C#J\;S0p1kuCS0qfPRu/5xRx/3C/6x\;S0rPc1_xCS0seS0tQ0sfQS0u/c\S0v%J\Rx#rfRR;P\11;\13;\C>[S0w1l;\S0xfSR;/3\Ry?Ay\\gS0y1b;\S0z17\3fTR;/3\Ry,7\?Ly3[S0{1j;\S0|fUR;/1\#J\xS0}1k;\S0~fVR;/3\/6;\xS10Pc1_;\S11eS12Q11fW/2J/cHS13%JHRx#rfXS14/2JRyPH11yH13yHC>[S151lyHS16fYS17/2JRy/3HRr?ArH\=S181byHS1917H3fZS1:/2JRy/3HRr,7H?Lr3[S1;1jyHS1<f[Ry/2JRr/1H#J\xS1=1krHS1>f\S1?/2JRr/3H/6r\xS1@Pc1_rHS1AeS1BQ1AP1g00hbRr1p3H'YP=eO1S1Cf]R=/2J/3HRx?AxHS1DPe1p3\,YrPgeO1S1Ef^Rg/3\Rx?Ax\S1FPp1p3C,YrPqeRqO1S1Gf_/5=/3CRr?ArCS1HPvPqO1S1If`S1J/9g/3CRr?ArCS1KP1PtPuP4P6O2XfsS1LPm^fsS1MQ0uPqO1S1NQ0U%8YRY#8Rq#8Ru#8Rr#8Rp#8Rx#8RG#8Rz#8R{#8R|#:%R2#SR2%:{R{'G%Fi%:pRp;IZ3E207Z{%?BR{#=#FR}%8|#8#8R|#8#:R~%0I$0B#?RI#=#F%:|'f%R{#S%:GRG'G%RI#SRI%:xRx'G1GIp%:q%oF$0A#K#K#KRF#=#FQ04'f3E3E3E7IZ/^['X'XRq%FJ%RF#S/GG%:YRY,G25E~7IZ%:zRz%:rRr5EZ/^['X,XG%RB#S/Gx=EzY%:uRu9EZG/^['X/WL'W,Wq'WP?%MW%Md7@1%MV?@<M7@5%MN?@dM%MARq7@87@6PPPQPQ%CDRD9<QRRG1PDT,;QPaPQPQ%CERE9<QR1OQlPaPQPQ%0KRz#0#CR~9<QR1OQkPaPQPQQ0@Pa%CBRB9a7^R2%CzRz,US=a7~'Q,;QCzPaPQPQA<QR2PaPQA<QRSPaA<QRzFDPaPQPQQ05PaPQA<QRTPa%0{#CR{9<QRFDPaPQ1QB{,;QPaPQ%CKR{Q01#C'Q,;QPaPQ%C9Rz/QE,;QRSPaPQ1Uf{=a7z,Q^,;QRzPaPQA<QRBA<QB^R~5hQPaPQ1UBT=a7D,Qb,;QRbPaPQ1OQo9hQ_Pa1V7iRD,U{:0H72R29<QRFDFDFDFDFDETETETPUP>b2b4b5X67X@7XA7XB7XC7XD7Xc7Xd7Xe7Xb7X3XX<XX=X%48R{?{8H1gWe%4eRB/HkQ0A151<RIPCPNPkC>[%4I%4d\s[12<JRs#4Q0P\m[16Wo16Vo16koPVP\PePoC>ALBedQ0DPlPHPoC>1glw15ko12ni'9#4[[[[[[[[[[[[[^67^@7^A7^B7^C7^D7^c7^d7^e7^b7^3X^<X^=XP4feRn/7HfcRo,5nRk/3CRw/7C13n\RB/7\Pw12nJRJ/1H11n\PBP=11kC13JHRJPgPoPnPWPAP<PvQ0uP;Q14Q17Q1:Q1?Q1JfbRvfdRkOJb1b?b>bjb8b;b9b:15=y12;i'9R;#4ebTbSbRbPb:bObNbMbLbKb9bJbIbZbYbXb;bWbVbUbQbHb8bEb\b]b>b?b^b_b`bab0bFbGQ0FQ0EQ0HQ0GQ0JQ0IQ0KQ0LQ0MQ0NQ0OQ0QQ0RQ0SQ0TQ0VQ0WQ0XQ0YQ0ZQ0[Q0\Q0]Q0^Q0_Q0`Q0aQ0bQ0cQ0dQ0eQ0fQ0hQ0gQ0iQ0jQ0kQ0lQ0mQ0nQ0oQ0pQ0qQ0rQ0tQ0sQ0vQ0wQ0xQ0yQ0zQ0{Q0|Q0}Q0~Q10Q12Q11Q13Q15Q16Q18Q19Q1;Q1<Q1=Q1>Q1@Q1BQ1AQ1CQ1DQ1EQ1FQ1GQ1HQ1IQ1KP1PtQ1LQ1MQ1NQ0U%F\%0F#o#=#FRF%R9#S/GYQ03#:,f}%K9#K#K#K#=#F/fZ3E9IFu9IFr7Ip7Ix/^[/WLP?A@q1M?@5M%M<9@M87@6PPPQPQPG1OQNPaPQPQ1OQV1PEf,;QPaPQPSPaPQPzPaPQPQ1OQdP~PaPQPbPaPQ1P^T,;Q9hQ_Pa1P2D,;QFDETFDETETPUP>b2b4b5X67X@7XA7XB7XC7XD7X3XX<XX=X1H{AA{NA\16AWP8P\P<PWC>ALl<1PsPAPHPNC>Q06,gA15WN12Vi'9/7i[[[[[[[^67^@7^A7^B7^C7^D7^3X^<X^=XP4%4o%4B17JHPBP=PJPgPoPnPWPAQ1:Q1?Q1JPvPkO@b1b?b>bjb8b;b9b:17;iebTbSbRbPb:bObNbMbLbKb9bJbIbZbYbXb;bWbVbUbQbHb8bEb\b]b>b?b^b_b`bab0bFbGH0440>Q07Q08Q099]7V9]7eQ0:Q00P4P6P02027iR61w7KRK5v7Av7K6:03705u7R0PcQ02Q0;Q0<P7P@Q0=At`40H00bi#qdF~bgbhPhPiP8PjC>eJ0KH0LbnbmbsbrQ0C/1]P:PCP]Q0BQ0?Q0>PLP?PMPP1V7],PR,;QPUP>b2b4b5173]P4b1b0I0=EiPOP4EibkbqblbobtWpXu7o"). Qed.

Lemma w4_mulhu7 : forall x, 0 <= x < 2^64 ->
  ((((x - (x * 2635249153387078803) ≫ 64 mod 18446744073709551616) mod 18446744073709551616) ≫ 1
     + (x * 2635249153387078803) ≫ 64) mod 18446744073709551616) ≫ 2 = x / 7.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_w4blk ()) [] "h04__x1h14__p1h27__arithh34__ffh48__varmaph55__with64__x2h75heq_th81zh94__x3h:1Hh;2Hah<4__p2h=6__sat3h>4__x4h?2Hxh@2T0hA6__sat1hB6__sat2hC6__sat4hD1thE1xp;1p;2p;3p;4p;5p;7p;6p;8g0000j10Tg000Uj1>Tg0013j2ZTg001Pj26Tg001lj24Tg002Gj1;Tg002lj2:Tg00kXj2STg003fj25Tg00<1j27Tg00Y@j2=Tg003Ij21Tg00<Nj29Tg004mj2HTg00Eij2ATg00Cbj1LTg00FRj2PTg00G>j2[Tg005Gj1gTg00Gjj3ITg005gj1fTg00HJj2OTg006ej1dTg007Cj1cTg007nj2DTg00IFj2MTg00Iij1bTg00JKj3TTg008Qj2~Tg0093j2|Tg009_j3aTg00:9j3{Tg00:Xj4zTg006Gj1yTg00KQj1xTg00Koj3vTg00l8j4uj2sTg0108j5`Tg00Nej4_Tg011aj2tTg00=[j2^Tg00>Lj2rTg00?4j3qTg00CAj2pTg00DAj1oTg00D_j2nTg00E@j3mTg00Hhj4QTg00LRj3]Tg00Y]j4VTg00Jnj3jTg00nJj3UTg00nmj3WTg00Zlj3iTg00ZHj7XTg00[Uj6wTg00\9j7\Tg00\]j8RTg00M5j6hTg00^_R0f0R1'9p=2%01#0#0#0p=e%;1#0p=l%01#;#0#0p=K%;1#0#0#;p=G%01#0#;#0p=N%01#0p=}%01#0#0#0#0#0#0#0p=@g00_=R2f1R3;a1p=8Ai231p=?f2R4g00`BR5g00`aR6P6g00aAR7P2P3g00bAP1CVg00aaR8FXp=3P3P5P6P6P7P1Ewp=FP4P5P6P6P7P3P1F\p=Bf3R9P5P6P6P7P4P3P1GRp=YP4P5P6P6P7P2P3g00_[P1CVP8FXp=<f6R:P5P6P6P7f5R;f4R<P9P5P6P6P7P4P3P1GRGRp=JP3P5P6P6P7P1P8FXp=kP;P5P6P6P7P<P5P6P6P7P9P4F\P3P1GRp=CP2P<P9P4P3P1Ehp=E%21R5g00eYR8#0R=#>R>%0=R?#eR@#>RA'ZRB,61'4RC%l?#K#G#N#K#G#N#K#G#N#K#G#N#K#G#;#>RD,:3RE/SARF%}@#@#@#@#@#@#@#@#>RG'5,73/5GRH%>8RI'SRJ/=F/5GRK1Z>>RL'1%;8RM#;#>RN,14RO,81X821Z>IRP,1H1:4DRQ/SA,=1/5G/1L/8OX8211EBRR151G,74/5G/1P/=1/5G/1L/8OX82PRP211QBRR#219R4PQPB1H2R181RRReROPRp-0RSg00f>RTg00iHRU,A2RV%LURU#LRW,A2RX,?Vg00igRY'PRZ'[%gTR[3IR\%fTR]1O23R^%d2R_%c2R`1D20Ra1M28Rb53`Rc1F`95B`Rd%b6R61D2DRe9T2bRf93`aCY1~`7R7P1P4g00fjRgg00gJRh'H1|14=aghdA{203CzRhb3b4b5X02W11453Rg%2E[^02^1SP116<BP<P9O3Rib2b7POPRP[P]%y2RjP_1D2>Rk%x@5v2R@9<`aP7Phb3b4b5160BRlP1b2b7RmCuPQPBP4PmPOPRP\P]P^P_P`PdP6AT2@b93`fCYP7Phb3b4b5X02X1S1:B3,9E\g^02^1SPib2b7D`C_1914,45RiePiP317<1/5G/1P/=4/5G/1L11<NRi'8X821793Rg111P/=4/5G/1L/8iX8211g>RL/=3RP%>?Rf,11/8iX821:9DRi/1BRd,H2183dRdeR\PdP[P]P^P_P`A<`b@R^9B`cRRP6PRCYP7Phb3b4b5X02%23RR163BRO'4\C^02P1P;P<O2b2b7,t911Pf119N'8e15PG%2P16PG1sg>%2g160>RN17;9/1>#2[[1:<D/1BRf,H2184fRfeRCPf1:;DRm/^B%2m%2BRmf7RQ/:D/1B#2[[1r>A%2ARnPl[Rl\N%2>Rog00gjRpAq>A3UW;Pm\p^;of8Rp/7:Rq/^>%2qf:Rq/7p/1>#2\o[P4g00hb1p0>'HPNeO1Pl%LWRW#LRl#L,A21A2lRl%o8,n21A2WRW5m2/?V'?'?/PY1[lZ=IT[5ITP]P2P21O2<P4PjCQP31O29RlCQP_P`P`1M2MRM1M2=R=5]2RZ93`aP6P`A3`akR8P6PcFJP6P`P`AT2Me93`aP6P`A3`a@P61M2?R?93`aFJP6P`P2P=g00bhP?CV,k`P6P`1F`:A3`=M5B`P6P`P`A3`aM1F`QP6Aj2b=R?93`aECFJFJP7Phb3b4b5X02X62X92X>2X1SX<S1743Re#2%24R0\o[%2i%2:Ri\m[189;19<;,4Qf9RQ,4i1=;:#2[[[[[^02^62^92^>2^1S^<SP1f;Rm/6B%2Q1:mD/1BPmPQ17mQ/1>P4P;P:PpPqO;b2b=bAbBb=bCb7b:PgP>PgP\PdP[P]PjP_A<`akP7Phb3b4b5PNP1b2b7P\PdP[P]P21O24RNP3PjCQRqP_P`P`1F`<RpA3`=bRmP6A]2b=RQAT2kQ53`ECP7Phb3b4b5X02X62X1S1931Rk,441734RD1:>D'9[^02^62^1SP1%29P9P;P4O4b2b7D`19LgPCPf1A2U/?VRV,?X/PY=IT[RXP]P2PNP3PlCQP_P`A3`bZP6P`1F`;A<`M@5B`P61D2GRM9<`?FJP7Phb3b4b5X02X62X92X1S191e169B,4<1=49/6G[[^02^62^92^1SP1PiP:P<17:</1>P4P;O6b2b7b:C_9UPGDE15gGP\Pd1?WV/PY=IT[P]PqP_P`P`A3`a=PmP6P`P`PpP^P6A3`aQA<`QM5B`ECECP7Phb3b4b5X02X62X1S14Rk149O1749RO#216OG'4[[^02^62^1SP1%2;ROP9P;P4P<O5b2b79UgGDE153GP\PdPXP]PqP_P`P`PcA3`b=P6P`P`PpA<`=@P6A<`bM9B`cECECP7Phb3b4b5X02X62X1S1913,45164B,49164G,40[[^02^62^1SP1POP;P9P4P<O5b2b79U3GDEb@bDPFP[P]PjP_1D2A93`aP7Phb3b4b5PnP1b29WEADEPJP[P]PjP_1D2I93`aP7Phb3b4b5%2IP1b29WHIDE1SK>P[P]PjP_P8P7Phb3b4b5PoP1b29WK>DEW?XE2o"). Qed.

Lemma w4_land64 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_w4blk ()) [] "h02Hxh17__arithh24__ffh38__varmaph45__with51xh61zp;2p;1p;3p;4p;7p;6g00<Nj24Tg0000j10Tg000Uj11Tg0013j25Tg001Pj2ITg001lj2CTg003fj2=Tg009_j33Tg00nJj3:Tg012fj16Tg013Dj27Tg005Gj18Tg005gj19Tg006Gj1HTg006ej1GTg007Cj1FTg007nj22Tg00Y]j4BTg00ZHj7>Tg008Qj2?Tg004mj2@Tg0093j2ATg00:9j3<Tg00:Xj4;Tg013bj3DTg00M5j6ETg00_=R0g00^_R1f0R2'4g00eY#0R3#1%03#0#0#0#0#1R3'5R4,I2'CP0f1R5/=4f2R69302X60A:542%63,75g00f>R4#8%94%H0%G0%F0R4g00`Bg00`aR7P7g00aAR7P01201g00bA1203CBg00aaF>1?47P2P6g00fjR7g00gJR4'@1A26=374dA<015C;b2b3b41413P2b19D53EEW0W5o"). Qed.

Lemma w4_land_mod : forall x, Z.land x 18446744073709551615 = x mod 18446744073709551616.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_w4blk ()) [] "h07__arithh14__ffh28__varmaph35__with41xh51zp;1p;2p;3p;4p;7p;6g0000j10Tg000Uj12Tg0013j27Tg003fj23Tg009_j34Tg004mj26Tg012fj1;Tg013Dj28Tg005Gj19Tg005gj1:Tg006Gj1ITg006ej1HTg007Cj1GTg007nj25Tg00Y]j4ETg00ZHj7BTg008Qj2?Tg0093j2@Tg00:9j3ATg00:Xj4=Tg00<Nj2CTg013bj3DTg00M5j6<Tf0R0#0#0#0#0p=>%00#0p=F%00#0#0#0#0#0#0#0p=1g00_=R1P1g00eY#0R2#2%02#>R2#2R3'7,30f1R4%F2#1#1#1#1#1#1#1#2R2'39410X511302,61%;3,80g00f>R2#9%:2%I1%H1%G1R2g00`Bg00`aR5P5g00aAR5P1g00^_R6,51g00bA1513CEg00aaFB1?25P0f2R5g00fjR2g00gJR7'61@05=427dAA164C=b1b2b31C63P0b09D03E<W4o"). Qed.

Lemma w4_q5 : forall x, 0 <= x < 2^64 -> 0 <= x / 5 /\ 5 * (x / 5) <= x /\ x / 5 < 2^64.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_w4blk ()) [] "h04__p1h14__x1h27__arithh34__ffh48__varmaph55__with62Hxh71xp;2p;1p;4p;6p;3p;5p;7p;8g00<Nj22Tg0000j10Tg000Uj15Tg0013j2@Tg001Pj21Tg001lj23Tg002Gj1QTg003Ij2DTg002lj28Tg005Gj1ATg005gj1?Tg00HJj2>Tg006ej1=Tg007Cj1WTg007nj27Tg00IFj2VTg00Y]j4<Tg00[Uj6UTg00Iij1PTg008Qj2CTg004mj2ETg0093j2FTg009_j3BTg00:9j3GTg00:Xj4HTg006Gj1ITg00l8j4JTg014Ej3KTg00KQj1LTg00Koj3MTg00JKj3NTg00lYj5OTg00Nej4;Tg00ZHj7RTg00\9j7STg00\]j8TTf1R0g00`BR1g00`aR2P2g00aAR3f0R4g00aaFRp=4f2R5P1P2P2P3P0P4FSp=:f3R6P1P2P2P3P5P0P4GTp=9g00_=R7P0g00_[P4C<p=6g00^_R8/24R9g00eYR:#0R;#5R<%0;#0#0#0#0R=#5'@R>,14R?'3%Q;#5R;,D0R@,2818;@/20RA11@>R@'3P0P;p-0RBg00f>RC#ARD%?CRC1>70RE%=7RF%W7RGP71778RHg00bA1V7:R:C<,4GRIPGP1P2P2P3P6EUR65:G%P2R2PIC91CG3R3P4P5g00fjRIg00gJR1'E1F45=BI1dAG780CHR1b3b4b5X17W013901280[^17^0BP4115>P5P0O3b2PDPC%I7PF177;R9,6H,4GP3P1b3b4b5118;P4b2RHCJPAP@AK0;HP0P;P>PHPDPCPEPFPG177<%L=5M7R=,6:,4G9:G6P2AN79=,6:,4GC9P3P1b3b4b5X17X0B130?18;>,10[^17^0BP41285P5P0O3b2DOC;C;W6X77o"). Qed.
Lemma w4_q7 : forall x, 0 <= x < 2^64 -> 0 <= x / 7 /\ 7 * (x / 7) <= x /\ x / 7 < 2^64.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_w4blk ()) [] "h04__p1h14__x1h27__arithh34__ffh48__varmaph55__with62Hxh71xp;2p;1p;4p;6p;3p;5p;7p;8g00<Nj22Tg0000j10Tg000Uj15Tg0013j2ATg001Pj21Tg001lj24Tg002Gj19Tg003Ij2GTg002lj28Tg005Gj1BTg005gj1@Tg00HJj2?Tg006ej1>Tg007Cj1WTg007nj27Tg00IFj2VTg00Y]j4=Tg00[Uj6UTg00Iij1QTg008Qj2FTg004mj2ETg0093j2DTg009_j3CTg00:9j3HTg00:Xj4ITg006Gj1JTg00l8j4KTg014Ej3LTg00KQj1MTg00Koj3NTg00JKj3OTg00lYj5PTg00Nej4<Tg00ZHj7RTg00\9j7STg00\]j8TTf1R0g00`BR1g00`aR2P2g00aAR3f0R4g00aaFRp=3f2R5P1P2P2P3P0P4FSp=;f3R6P1P2P2P3P5P0P4GTp=:g00_=R7P0g00_[P4C=p=6g00^_R8/24R9g00eYR:#0R;#5R<%0;#0#0#0#0R;#5'AR=,14R>'4%9:#9#5R?,G0R@,2818?@/20RA11@=R@'4P0P?p-0RBg00f>RC#BRD%@CRC1?70RE%>7RF%W7RGP71778RHg00bA1V7:R:C=,3GRIPGP1P2P2P3P6EUR65;G%Q2R2PIC:1FG3R3P4P5g00fjRIg00gJR1'E1D45=CI1dAH780CIR1b3b4b5X17W014901280[^17^0BP4115=P5P0O3b2PDPC%J7PF177?R9,6H,3GP3P1b3b4b5118?P4b2RHCKPAP@AL0?HP0P?P=PHPDPCPEPFPG177<%M;5N7R;,6:,3G9;G6P2AO79;,6:,3GC:P3P1b3b4b5X17X0B140>18?=,10[^17^0BP41285P5P0O3b2DPC<C<W6X77o"). Qed.


Notation W4C mm P w88 w96 w104 w112 w120 w128 w224 w232 :=
  (rw_cells bsegs mm (P + 88) [C8 w88; C8 w96; C8 w104; C8 w112] /\
   rw_cells bsegs mm (P + 120) [C8 w120; C8 w128; C8 (Z_to_bv 64 2147450880)] /\
   rw_cells bsegs mm (P + 224) [C8 w224; C8 w232]) (only parsing).

Section CANSEC1. Context {rc : runConstT}.











End CANSEC1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXTac KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_z4m AF_huf_w4m.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell KXCell2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_w4s3b Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_fa_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require I_asan_memcpy.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AFrameD.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

Module W4FSB.
Import KXS.

Lemma w4f_shd_ap : forall E X B O k w H,
  bv_unsigned (edenot E X) < H -> 0 <= O -> O + H / 8 + 1 <= 2^64 -> 0 < w < 2^64 ->
  0 <= bv_unsigned (edenot E B) + k -> bv_unsigned (edenot E B) + k + w <= 2^64 ->
  bv_unsigned (edenot E B) + k + w <= O \/ O + H / 8 + 1 <= bv_unsigned (edenot E B) + k ->
  flat E (SA (EAlu ALU_SRL X (ELit 3)) O) (elenZ E (ELit 1)) /\ flat E (SA B k) (elenZ E (ELit w)) /\
  (estart E (SA (EAlu ALU_SRL X (ELit 3)) O) + elenZ E (ELit 1) <= estart E (SA B k) \/
   estart E (SA B k) + elenZ E (ELit w) <= estart E (SA (EAlu ALU_SRL X (ELit 3)) O)).
Proof.
  intros E X B O k w H HX HO1 HO2 HW HB1 HB2 HAP.
  pose proof (bv_unsigned_in_range _ (edenot E X)) as [RX0 _].
  unfold flat, estart, elenZ. cbn [a_base a_off edenot].
  rewrite u_srl64.
  change (bv_unsigned (Z_to_bv 64 3)) with 3. change (bv_unsigned (Z_to_bv 64 1)) with 1.
  change (2 ^ (3 mod 64)) with 8.
  rewrite (Z_to_bv_unsigned 64 w). unfold bv_wrap, bv_modulus. rewrite (Z.mod_small w) by lia.
  assert (HD : bv_unsigned (edenot E X) / 8 <= H / 8) by (apply Z.div_le_mono; lia).
  assert (HD0 : 0 <= bv_unsigned (edenot E X) / 8) by (apply Z.div_pos; lia).
  repeat split; lia.
Qed.

Ltac w4f_zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.

Ltac w4fxb :=
  lazymatch goal with
  | |- bv_unsigned (edenot ?E ?X) < _ =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        rewrite (ez_ok zv E (kE_atoms zv xs) X);
        let na := eval vm_compute in (length zv) in
        cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb];
        repeat match goal with
        | |- context [?c mod 64] => w4f_zlit c; let v := eval vm_compute in (c mod 64) in change (c mod 64) with v
        end;
        rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64;
        first [lia | Z.div_mod_to_equations; lia]
      end
  end.

Lemma w4f_shd_ap2 : forall E X B O k w H,
  bv_unsigned (edenot E X) < H ->
  0 <= O /\ O + H / 8 + 1 <= 2^64 /\ 0 < w < 2^64 ->
  0 <= bv_unsigned (edenot E B) + k /\ bv_unsigned (edenot E B) + k + w <= 2^64 /\
  (bv_unsigned (edenot E B) + k + w <= O \/ O + H / 8 + 1 <= bv_unsigned (edenot E B) + k) ->
  flat E (SA (EAlu ALU_SRL X (ELit 3)) O) (elenZ E (ELit 1)) /\ flat E (SA B k) (elenZ E (ELit w)) /\
  (estart E (SA (EAlu ALU_SRL X (ELit 3)) O) + elenZ E (ELit 1) <= estart E (SA B k) \/
   estart E (SA B k) + elenZ E (ELit w) <= estart E (SA (EAlu ALU_SRL X (ELit 3)) O)).
Proof.
  intros E X B O k w H HX (HO1 & HO2 & HW) (HB1 & HB2 & HAP).
  apply (w4f_shd_ap E X B O k w H); assumption.
Qed.

Ltac w4f_aplia :=
  first [ match goal with H : KXGoM.apart ?a _ _ _ |- context [?a] =>
            let H' := fresh "AP" in pose proof H as H'; unfold KXGoM.apart in H'; lia end
        | match goal with H : KXGoM.apart _ _ _ _ |- _ =>
            let H' := fresh "AP" in pose proof H as H'; unfold KXGoM.apart in H'; lia end ].

Ltac w4fshd H :=
  lazymatch goal with
  | |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ ?E (ELit ?w)) /\ _ =>
      apply (w4f_shd_ap2 E X B O k w H);
      [ w4fxb
      | lia
      | w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia;
        split; [lia | split; [lia | w4f_aplia]] ]
  end.
Lemma w4f_rd_nb : forall m A z,
  ztab_fact bsegs m A 4096 2 [(0, 0, 11)] -> A <= z < A + 4096 -> (z - A) mod 2 = 0 ->
  bv_unsigned (rdval bsegs m (Z_to_bv 64 z) 2 false) mod 64 <= 11.
Proof.
  intros m A z ZT HZ HM.
  assert (FF : find_field ((z - A) mod 2) [(0, 0, 11)] = Some (0, 11)) by (rewrite HM; reflexivity).
  destruct (ZT z HZ 0 11 FF) as (b & RB & HB).
  unfold rdval. cbn [rdn] in RB |- *.
  revert RB.
  lazymatch goal with |- (match ?x with Some _ => _ | None => _ end) = _ -> _ => destruct x as [b0|] eqn:L0 end;
    [| discriminate].
  intros RB. injection RB as Eb. subst b0.
  cbn beta iota.
  match goal with |- context [m ?X] =>
    destruct (m X) as [b1|] eqn:L1; [| destruct (seg_rom bsegs X) as [b1|] eqn:L2] end;
  cbn beta iota; unfold extz;
  rewrite ?bytes_le_to_Z_le_val; cbn [map le_val];
  rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64;
  try (pose proof (bv_unsigned_in_range _ b1) as R1; unfold bv_modulus in R1; change (Z.of_N 8) with 8 in R1);
  Z.div_mod_to_equations; lia.
Qed.

Lemma w4f_mod_div : forall a n m, 0 < n -> (n | m) -> 0 < m -> (a mod m) mod n = a mod n.
Proof.
  intros a n m Hn [c Hc] Hm. subst m.
  rewrite (Z.div_mod a (c * n)) at 2 by lia.
  rewrite Z.add_comm. replace (c * n * (a / (c * n))) with ((c * (a / (c * n))) * n) by ring.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma w4f_lb_shift : forall p s k x, 0 <= p -> 0 <= k <= s -> p + s <= 63 ->
  x mod 2^(p+1) <> 0 -> ((x * 2^k) mod 2^64) mod 2^(p + s + 1) <> 0.
Proof.
  intros p s k x Hp Hk Hps Hl.
  assert (P1 : 0 < 2^(p+s+1)) by (apply Z.pow_pos_nonneg; lia).
  assert (P2 : 0 < 2^k) by (apply Z.pow_pos_nonneg; lia).
  assert (P3 : 0 < 2^(p+s+1-k)) by (apply Z.pow_pos_nonneg; lia).
  assert (P4 : 0 < 2^(p+1)) by (apply Z.pow_pos_nonneg; lia).
  assert (D1 : (2^(p+s+1) | 2^64)).
  { exists (2^(63 - p - s)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (D2 : (2^(p+1) | 2^(p+s+1-k))).
  { exists (2^(s - k)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  rewrite (w4f_mod_div (x * 2^k) (2^(p+s+1)) (2^64) P1 D1 ltac:(lia)).
  replace (2^(p+s+1)) with (2^(p+s+1-k) * 2^k) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.mul_mod_distr_r by lia.
  intro HZ. apply Z.mul_eq_0 in HZ. destruct HZ as [HZ|HZ]; [|lia].
  apply Hl. rewrite <- (w4f_mod_div x (2^(p+1)) (2^(p+s+1-k)) P4 D2 P3), HZ. reflexivity.
Qed.

Lemma w4f_sll_lb : forall (B : Z) (e : word) p, 0 <= p -> p + 11 <= 63 -> 0 <= B < 2^64 ->
  B mod 2^(p+1) <> 0 -> bv_unsigned e mod 64 <= 11 ->
  0 <= bv_unsigned (alu64 ALU_SLL (Z_to_bv 64 B) e) < 2^64 /\
  bv_unsigned (alu64 ALU_SLL (Z_to_bv 64 B) e) mod 2^(p + 11 + 1) <> 0.
Proof.
  intros B e p Hp Hp2 HB HL HE.
  rewrite u_sll64. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64.
  rewrite (Z.mod_small B) by lia.
  pose proof (Z.mod_pos_bound (bv_unsigned e) 64 ltac:(lia)) as HK.
  split; [apply Z.mod_pos_bound; lia |].
  apply (w4f_lb_shift p 11 (bv_unsigned e mod 64) B); [lia | lia | lia | exact HL].
Qed.

Lemma w4f_rd_nb2 : forall m A (x : word) k,
  ztab_fact bsegs m A 4096 2 [(0, 0, 11)] -> A <= bv_unsigned x + k < A + 4096 -> (bv_unsigned x + k - A) mod 2 = 0 ->
  bv_unsigned (rdval bsegs m (v_addi x k) 2 false) mod 64 <= 11.
Proof.
  intros m A x k ZT H1 H2. unfold v_addi. exact (w4f_rd_nb m A (bv_unsigned x + k) ZT H1 H2).
Qed.

Ltac w4f_nb_read ZT TA :=
  lazymatch goal with
  | |- bv_unsigned (rdval _ ?m (adenot ?E ?a) 2 false) mod 64 <= 11 =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        cbv [adenot a_base a_off];
        apply (w4f_rd_nb2 m TA); [exact ZT | |];
        rewrite (ez_ok zv E (kE_atoms zv xs)); rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
        change (Z.of_N 64) with 64;
        let na := eval vm_compute in (length zv) in
        cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb];
        repeat match goal with
        | |- context [?c mod 64] => w4f_zlit c; let v := eval vm_compute in (c mod 64) in change (c mod 64) with v
        end;
        Z.div_mod_to_equations; lia
      end
  end.

Ltac w4f_bits A p ZT TA HB LBb e :=
  lazymatch goal with
  | H : rw_cells _ _ A [C8 (edenot ?E (EAlu ALU_SLL (EVar ?j) (EVar ?r)))] |- _ =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        let HR := fresh "HR" in kx_read_eq r HR;
        let NB := fresh "NB" in
        assert (NB : bv_unsigned (ev E r) mod 64 <= 11) by (rewrite HR; w4f_nb_read ZT TA);
        clear HR;
        cbn [edenot] in H;
        set (e := ev E r) in *;
        change E with (kE zv xs) in H;
        rewrite (kE_atoms zv xs j ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)) in H;
        cbn [nth] in H;
        lazymatch type of H with
        | rw_cells _ _ _ [C8 (alu64 ALU_SLL (Z_to_bv 64 ?B) e)] =>
            let BR := fresh "BR" in let BL := fresh "BL" in
            pose proof (w4f_sll_lb B e p ltac:(lia) ltac:(lia) HB LBb NB) as [BR BL]
        end
      end
  end.

Lemma w4f_srl58 : forall E X, 0 <= bv_unsigned (edenot E (EAlu ALU_SRL X (ELit 58))) < 64.
Proof.
  intros E X. pose proof (bv_unsigned_in_range _ (edenot E X)) as [R0 R1]. unfold bv_modulus in R1.
  change (Z.of_N 64) with 64 in R1.
  cbn [edenot]. rewrite u_srl64. change (bv_unsigned (Z_to_bv 64 58) mod 64) with 58.
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia | change (2^58 * 64) with (2^64); lia]].
Qed.

Lemma w4f_ctz_rd : forall m E X off,
  ztab_fact bsegs m off 64 1 [(0, 0, 63)] -> 0 <= off -> off + 64 <= 2^64 ->
  exists bs, rdn bsegs m (adenot E (SA (EAlu ALU_SRL X (ELit 58)) off)) 1 = Some bs.
Proof.
  intros m E X off ZT H0 H1. pose proof (w4f_srl58 E X) as HV.
  cbv [adenot a_base a_off]. unfold v_addi.
  set (u := bv_unsigned (edenot E (EAlu ALU_SRL X (ELit 58)))) in *.
  assert (FF : find_field ((u + off - off) mod 1) [(0, 0, 63)] = Some (0, 63)) by (rewrite Z.mod_1_r; reflexivity).
  destruct (ZT (u + off) ltac:(lia) 0 63 FF) as (b & RB & _). exists [b]. exact RB.
Qed.

Lemma w4f_ctz_acc : forall RNG E X off, rng RNG off 64 -> accP RNG E (SA (EAlu ALU_SRL X (ELit 58)) off, 1%nat).
Proof.
  intros RNG E X off (R0 & R1 & R2). pose proof (w4f_srl58 E X) as HV.
  unfold accP. cbn [fst snd].
  set (u := bv_unsigned (edenot E (EAlu ALU_SRL X (ELit 58)))) in *.
  change (RNG (bv_unsigned (Z_to_bv 64 (u + off))) 1%nat).
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64.
  rewrite Z.mod_small by lia. apply R2; cbn; lia.
Qed.

Lemma w4f_ctz_ap : forall E X B O k w,
  0 <= O -> O + 64 <= 2^64 -> 0 < w < 2^64 ->
  0 <= bv_unsigned (edenot E B) + k -> bv_unsigned (edenot E B) + k + w <= 2^64 ->
  bv_unsigned (edenot E B) + k + w <= O \/ O + 64 <= bv_unsigned (edenot E B) + k ->
  (flat E (SA (EAlu ALU_SRL X (ELit 58)) O) (elenZ E (ELit 1)) /\ flat E (SA B k) (elenZ E (ELit w)) /\
   (estart E (SA (EAlu ALU_SRL X (ELit 58)) O) + elenZ E (ELit 1) <= estart E (SA B k) \/
    estart E (SA B k) + elenZ E (ELit w) <= estart E (SA (EAlu ALU_SRL X (ELit 58)) O))) /\
  (flat E (SA B k) (elenZ E (ELit w)) /\ flat E (SA (EAlu ALU_SRL X (ELit 58)) O) (elenZ E (ELit 1)) /\
   (estart E (SA B k) + elenZ E (ELit w) <= estart E (SA (EAlu ALU_SRL X (ELit 58)) O) \/
    estart E (SA (EAlu ALU_SRL X (ELit 58)) O) + elenZ E (ELit 1) <= estart E (SA B k))).
Proof.
  intros E X B O k w HO1 HO2 HW HB1 HB2 HAP. pose proof (w4f_srl58 E X) as HV.
  unfold flat, estart, elenZ. cbn [a_base a_off].
  set (u := bv_unsigned (edenot E (EAlu ALU_SRL X (ELit 58)))) in *.
  change (edenot E (ELit 1)) with (Z_to_bv 64 1). change (edenot E (ELit w)) with (Z_to_bv 64 w).
  change (bv_unsigned (Z_to_bv 64 1)) with 1.
  rewrite (Z_to_bv_unsigned 64 w). unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64. rewrite (Z.mod_small w) by lia.
  repeat split; lia.
Qed.

Ltac w4f_rngs :=
  repeat match goal with
  | |- context [EVar ?j] =>
      lazymatch goal with
      | _ : _ <= bv_unsigned (ev _ j) <= _ |- _ => fail
      | _ => let H := fresh "HR" in kx_range (EVar j) H
      end
  end.

Ltac w4fctz :=
  lazymatch goal with
  | |- exists bs, rdn _ ?m (adenot ?E (SA (EAlu ALU_SRL ?X (ELit 58)) ?O)) 1 = Some bs =>
      eapply (w4f_ctz_rd m E X O); [eassumption | lia | lia]
  | |- accP ?R ?E (SA (EAlu ALU_SRL ?X (ELit 58)) ?O, 1%nat) => apply (w4f_ctz_acc R E X O); assumption
  | |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 58)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ ?E (ELit ?w)) /\ _ =>
      apply (proj1 (w4f_ctz_ap E X B O k w ltac:(lia) ltac:(lia) ltac:(lia) ltac:(w4uz) ltac:(w4uz) ltac:(w4uz)))
  | |- flat ?E (SA ?B ?k) (elenZ ?E (ELit ?w)) /\ flat ?E (SA (EAlu ALU_SRL ?X (ELit 58)) ?O) _ /\ _ =>
      apply (proj2 (w4f_ctz_ap E X B O k w ltac:(lia) ltac:(lia) ltac:(lia) ltac:(w4uz) ltac:(w4uz) ltac:(w4uz)))
  end.

Lemma w4f_br_nz : forall E P B,
  bv_unsigned (edenot E B) <= 64 -> 64 < bv_unsigned (edenot E P) ->
  branch_taken BC_NE
    (edenot E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU (EAlu ALU_XOR P (EAlu ALU_SRL B (ELit 3))) (ELit 1))))
    (edenot E (ELit 0)) = true.
Proof.
  intros E P B HB HP.
  pose proof (bv_unsigned_in_range _ (edenot E B)) as [RB _].
  cbn [edenot branch_taken].
  rewrite bv_eqb_Z, u_xor64, u_sltu64, u_xor64, u_srl64.
  change (bv_unsigned (Z_to_bv 64 3) mod 64) with 3. change (2 ^ 3) with 8.
  change (bv_unsigned (Z_to_bv 64 1)) with 1. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  assert (HL : 0 < Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8)).
  { assert (0 <= Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8)).
    { apply Z.lxor_nonneg; split; intros; Z.div_mod_to_equations; lia. }
    assert (Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8) <> 0).
    { assert (HB8 : bv_unsigned (edenot E B) / 8 <= 8) by (apply Z.div_le_upper_bound; lia).
      intros H0. pose proof (Z.lxor_eq _ _ H0). lia. }
    lia. }
  destruct (Z.ltb_spec (Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8)) 1); [lia|].
  reflexivity.
Qed.

Lemma w4f_lit_acc : forall RNG E off (n : nat) lo len, (1 <= n)%nat -> rng RNG lo len -> lo <= off -> off + Z.of_nat n <= lo + len ->
  accP RNG E (SA (ELit 0) off, n).
Proof.
  intros RNG E off n lo len HN (R0 & R1 & R2) H1 H2.
  unfold accP. cbn [fst snd].
  change (RNG (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 0) + off))) n).
  change (bv_unsigned (Z_to_bv 64 0)) with 0.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64.
  rewrite Z.mod_small by lia. apply R2; lia.
Qed.

Ltac w4fbr :=
  lazymatch goal with
  | |- branch_taken BC_NE (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU (EAlu ALU_XOR ?P (EAlu ALU_SRL ?B (ELit 3))) (ELit 1))))
         (edenot ?E (ELit 0)) = true => w4f_rngs; apply (w4f_br_nz E P B); w4uz
  end.

Ltac w4facc WIM :=
  lazymatch goal with
  | |- accP ?R ?E (SA (ELit 0) ?O, ?n) => eapply (w4f_lit_acc R E O n); [lia | exact WIM | lia | cbn; lia]
  end.

Lemma w4f_mod2_64 : forall x, (x mod 2^64) mod 2 = x mod 2.
Proof. intros x. apply (w4f_mod_div x 2 (2^64)); [lia | exists (2^63); reflexivity | lia]. Qed.

Lemma w4f_ev_add : forall E a b, bv_unsigned (edenot E a) mod 2 = 0 -> bv_unsigned (edenot E b) mod 2 = 0 ->
  bv_unsigned (edenot E (EAlu ALU_ADD a b)) mod 2 = 0.
Proof. intros E a b Ha Hb. cbn [edenot]. rewrite u_add64, w4f_mod2_64, Z.add_mod by lia. rewrite Ha, Hb. reflexivity. Qed.

Lemma w4f_ev_mul : forall E c b, c mod 2 = 0 -> bv_unsigned (edenot E (EMd M_MUL (ELit c) b)) mod 2 = 0.
Proof.
  intros E c b Hc. cbn [edenot]. rewrite u_mul64, w4f_mod2_64, Z.mul_mod by lia.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64. rewrite w4f_mod2_64, Hc. reflexivity.
Qed.

Lemma w4f_ev_and : forall E b m, m mod 2 = 0 -> bv_unsigned (edenot E (EAlu ALU_AND b (ELit m))) mod 2 = 0.
Proof.
  intros E b m Hm. cbn [edenot]. rewrite u_and64, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64.
  set (x := bv_unsigned (edenot E b)). set (y := m mod 2^64).
  assert (Hy : Z.land y (Z.ones 1) = 0) by (rewrite Z.land_ones by lia; change (2^1) with 2; unfold y; rewrite w4f_mod2_64; exact Hm).
  assert (H : Z.land x y mod 2 = Z.land (Z.land x y) (Z.ones 1)) by (rewrite Z.land_ones by lia; reflexivity).
  rewrite H, <- Z.land_assoc, Hy. apply Z.land_0_r.
Qed.

Ltac w4f_ev :=
  lazymatch goal with
  | |- bv_unsigned (edenot ?E (EAlu ALU_ADD ?a ?b)) mod 2 = 0 => apply (w4f_ev_add E a b); w4f_ev
  | |- bv_unsigned (edenot ?E (EMd M_MUL (ELit ?c) ?b)) mod 2 = 0 => apply (w4f_ev_mul E c b); reflexivity
  | |- bv_unsigned (edenot ?E (EAlu ALU_AND ?b (ELit ?m))) mod 2 = 0 => apply (w4f_ev_and E b m); reflexivity
  end.

Lemma w4f_rl_bits : forall E Y V, bv_unsigned (edenot E Y) mod 2 = 0 ->
  0 <= bv_unsigned (edenot E (EAlu ALU_SLL (EAlu ALU_ADD Y (ELit 1)) (EAlu ALU_AND V (ELit 7)))) < 2^64 /\
  bv_unsigned (edenot E (EAlu ALU_SLL (EAlu ALU_ADD Y (ELit 1)) (EAlu ALU_AND V (ELit 7)))) mod 2^8 <> 0.
Proof.
  intros E Y V HY.
  pose proof (bv_unsigned_in_range _ (edenot E Y)) as [Y0 Y1]. unfold bv_modulus in Y1. change (Z.of_N 64) with 64 in Y1.
  pose proof (bv_unsigned_in_range _ (edenot E V)) as [V0 _].
  cbn [edenot]. rewrite u_sll64, u_add64, u_and64.
  change (bv_unsigned (Z_to_bv 64 1)) with 1. change (bv_unsigned (Z_to_bv 64 7)) with 7.
  set (y := bv_unsigned (edenot E Y)) in *. set (v := bv_unsigned (edenot E V)) in *.
  assert (HY2 : y + 1 < 2^64) by (Z.div_mod_to_equations; lia).
  rewrite (Z.mod_small (y + 1)) by lia.
  assert (HO : (y + 1) mod 2^(0+1) <> 0) by (change (2^(0+1)) with 2; Z.div_mod_to_equations; lia).
  assert (HL : 0 <= Z.land v 7 <= 7).
  { assert (E7 : Z.land v 7 = v mod 2^3) by (rewrite <- Z.land_ones by lia; reflexivity). rewrite E7.
    pose proof (Z.mod_pos_bound v (2^3) ltac:(lia)). change (2^3) with 8 in *. lia. }
  rewrite (Z.mod_small (Z.land v 7) 64) by lia.
  split; [apply Z.mod_pos_bound; lia |].
  change (2^8) with (2^(0+7+1)).
  apply (w4f_lb_shift 0 7 (Z.land v 7) (y + 1)); [lia | lia | lia | exact HO].
Qed.

Ltac w4f_rlb A c :=
  lazymatch goal with
  | H : rw_cells _ _ A [C8 (edenot ?E (EAlu ALU_SLL (EAlu ALU_ADD ?Y (ELit 1)) (EAlu ALU_AND ?V (ELit 7))))] |- _ =>
      let BR := fresh "BR" in let BL := fresh "BL" in
      pose proof (w4f_rl_bits E Y V ltac:(w4f_ev)) as [BR BL];
      set (c := edenot E (EAlu ALU_SLL (EAlu ALU_ADD Y (ELit 1)) (EAlu ALU_AND V (ELit 7)))) in *; clearbody c
  end.

Lemma w4f_ctz_val : forall m E X off, ztab_fact bsegs m off 64 1 [(0, 0, 63)] -> 0 <= off -> off + 64 <= 2^64 ->
  bv_unsigned (rdval bsegs m (adenot E (SA (EAlu ALU_SRL X (ELit 58)) off)) 1 false) <= 63.
Proof.
  intros m E X off ZT H0 H1. pose proof (w4f_srl58 E X) as HV.
  set (u := bv_unsigned (edenot E (EAlu ALU_SRL X (ELit 58)))) in *.
  change (bv_unsigned (rdval bsegs m (Z_to_bv 64 (u + off)) 1 false) <= 63).
  assert (FF : find_field ((u + off - off) mod 1) [(0, 0, 63)] = Some (0, 63)) by (rewrite Z.mod_1_r; reflexivity).
  destruct (ZT (u + off) ltac:(lia) 0 63 FF) as (b & RB & HB).
  unfold rdval. rewrite RB. unfold extz. cbn beta iota.
  rewrite bytes_le_to_Z_le_val. cbn [map le_val].
  pose proof (bv_unsigned_in_range _ b) as [B0 B1]. unfold bv_modulus in B1. change (Z.of_N 8) with 8 in B1.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64.
  rewrite Z.mod_small by lia. lia.
Qed.

Ltac w4f_rlnb A nb :=
  lazymatch goal with
  | H : rw_cells _ _ A [C8 (Z_to_bv 64 (?S + (?i + -1 * (bv_unsigned ?Z mod ?M / ?D))))] |- _ =>
      lazymatch Z with
      | ?f ?j =>
          let HR := fresh "HR" in kx_read_eq j HR;
          let HV := fresh "HV" in
          lazymatch type of HR with
          | ?L = ?R =>
              assert (HV : 0 <= bv_unsigned L <= 63)
                by (rewrite HR; pose proof (bv_unsigned_in_range _ R) as [? _];
                    split; [lia | eapply w4f_ctz_val; [eassumption | lia | lia]]);
              change (0 <= bv_unsigned Z <= 63) in HV
          end;
          clear HR;
          let NB := fresh "NB" in
          assert (NB : 0 <= bv_unsigned Z mod M / D <= 7)
            by (change D with 8; change M with (2^64); rewrite Z.mod_small by lia;
                assert (bv_unsigned Z / 8 < 8) by (apply Z.div_lt_upper_bound; lia);
                assert (0 <= bv_unsigned Z / 8) by (apply Z.div_pos; lia); lia);
          set (nb := bv_unsigned Z mod M / D) in *; clearbody nb
      end
  end.

Lemma w4f_x5 : forall E a, bv_unsigned (edenot E (EAlu ALU_SRL (EMd M_MULHU a (ELit 14757395258967641293)) (ELit 2))) = bv_unsigned (edenot E a) / 5.
Proof.
  intros E a. pose proof (bv_unsigned_in_range _ (edenot E a)) as [A0 A1]. unfold bv_modulus in A1. change (Z.of_N 64) with 64 in A1.
  cbn [edenot]. rewrite u_srl64, u_mulhu64.
  change (bv_unsigned (Z_to_bv 64 2) mod 64) with 2. change (2 ^ 2) with 4.
  change (bv_unsigned (Z_to_bv 64 14757395258967641293)) with 14757395258967641293.
  apply w4_div5_magic; lia.
Qed.

Lemma w4f_x7 : forall E a,
  bv_unsigned (edenot E (EAlu ALU_SRL (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD a (EMd M_MUL (ELit (-1)) (EMd M_MULHU a (ELit 2635249153387078803))))
                                                    (ELit 1)) (EMd M_MULHU a (ELit 2635249153387078803))) (ELit 2)))
  = bv_unsigned (edenot E a) / 7.
Proof.
  intros E a. pose proof (bv_unsigned_in_range _ (edenot E a)) as [A0 A1]. unfold bv_modulus in A1. change (Z.of_N 64) with 64 in A1.
  cbn [edenot]. repeat first [rewrite u_srl64 | rewrite u_add64 | rewrite u_mul64 | rewrite u_mulhu64].
  change (bv_unsigned (Z_to_bv 64 2) mod 64) with 2. change (2 ^ 2) with 4.
  change (bv_unsigned (Z_to_bv 64 1) mod 64) with 1. change (2 ^ 1) with 2.
  change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1).
  change (bv_unsigned (Z_to_bv 64 2635249153387078803)) with 2635249153387078803.
  set (x := bv_unsigned (edenot E a)) in *.
  assert (Hh : 0 <= x * 2635249153387078803 / 2^64 <= x).
  { split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. }
  set (h := x * 2635249153387078803 / 2^64) in *.
  replace ((2^64 - 1) * h) with (- h + h * 2^64) by ring.
  rewrite Z_mod_plus_full, Z.add_mod_idemp_r by lia.
  rewrite (Z.mod_small (x + - h)) by lia.
  assert (H2 : 0 <= (x + - h) / 2 <= x - h) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  rewrite (Z.mod_small ((x + - h) / 2 + h)) by lia.
  replace (x + - h) with (x - h) by ring.
  unfold h. apply w4_div7_magic; lia.
Qed.

Lemma w4f_x5z : forall E a,
  bv_unsigned (edenot E (EMd M_MULHU a (ELit 14757395258967641293))) mod 2 ^ 64 / 2 ^ (2 mod 64) = bv_unsigned (edenot E a) / 5.
Proof.
  intros E a. rewrite <- (w4f_x5 E a). cbn [edenot]. rewrite u_srl64.
  pose proof (bv_unsigned_in_range _ (mul_div M_MULHU (edenot E a) (Z_to_bv 64 14757395258967641293))) as [H0 H1].
  unfold bv_modulus in H1. change (Z.of_N 64) with 64 in H1.
  rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma w4f_x7z : forall E a A, bv_unsigned (edenot E a) = A ->
  ((A + -1 * bv_unsigned (edenot E (EMd M_MULHU a (ELit 2635249153387078803)))) mod 2 ^ 64 / 2 ^ (1 mod 64)
     + bv_unsigned (edenot E (EMd M_MULHU a (ELit 2635249153387078803)))) mod 2 ^ 64 / 2 ^ (2 mod 64) = A / 7.
Proof.
  intros E a A HA. rewrite <- HA. rewrite <- (w4f_x7 E a). cbn [edenot].
  rewrite u_srl64, u_add64, u_srl64, u_add64, u_mul64.
  change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1).
  set (x := bv_unsigned (edenot E a)).
  set (h := bv_unsigned (mul_div M_MULHU (edenot E a) (Z_to_bv 64 2635249153387078803))).
  replace ((2^64 - 1) * h) with (- h + h * 2^64) by ring.
  rewrite Z_mod_plus_full, Z.add_mod_idemp_r by lia.
  replace (x + -1 * h) with (x + - h) by ring.
  reflexivity.
Qed.

Lemma w4f_negm : forall A h M D1 D2,
  ((A + -1 * h) mod M / D1 + h) mod M / D2 = ((A + - h) mod M / D1 + h) mod M / D2.
Proof. intros. replace (-1 * h) with (- h) by ring. reflexivity. Qed.

Ltac w4fhb :=
  lazymatch goal with
  | |- branch_taken _ _ _ = _ =>
      unfold branch_taken; try unfold bv_lts;
      rewrite ?bv_ltu_Z, ?bv_eqb_Z; rewrite ?w4f_x5, ?w4f_x7;
      w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64;
      rewrite ?Z.mod_small by lia;
      repeat match goal with |- context [(?x <? ?y)%Z] => destruct (Z.ltb_spec x y) end;
      repeat match goal with |- context [(?x =? ?y)%Z] => destruct (Z.eqb_spec x y) end;
      cbn [negb]; first [reflexivity | exfalso; Z.div_mod_to_equations; lia]
  end.

Ltac w4f_xeq :=
  lazymatch goal with
  | |- bv_unsigned (edenot ?E (EMd M_MULHU ?a _)) mod _ / _ = _ =>
      transitivity (bv_unsigned (edenot E a) / 5); [apply w4f_x5z |];
      w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64;
      rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia
  | |- ((?A + -1 * bv_unsigned (edenot ?E (EMd M_MULHU ?a _))) mod _ / _ + _) mod _ / _ = _ =>
      transitivity (A / 7);
      [apply (w4f_x7z E a A); w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64;
       rewrite ?Z.mod_small by lia; reflexivity |];
      Z.div_mod_to_equations; lia
  | |- ((?A + - bv_unsigned (edenot ?E (EMd M_MULHU ?a _))) mod _ / _ + _) mod _ / _ = _ =>
      rewrite <- w4f_negm; transitivity (A / 7);
      [apply (w4f_x7z E a A); w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64;
       rewrite ?Z.mod_small by lia; reflexivity |];
      Z.div_mod_to_equations; lia
  end.

Ltac w4f_cell_gen H W off :=
  lazymatch goal with
  | HLF : log_flat ?E ?log |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      lazymatch type of H with
      | rw_cells ?segs m ?A [?c0] =>
          let rec go pre l :=
            lazymatch l with
            | SE ?a W ?v :: ?rest =>
                tryif (lazymatch a with {| a_base := _; a_off := off |} => idtac end) then
                  first [ let Hn := fresh "HC" in
                          assert (Hn : rw_cells segs (mem_denot E m (pre ++ SE a W v :: rest)) A
                                         [ltac:(lazymatch W with 8%nat => exact (C8 (edenot E v)) | _ => exact (C4 (edenot E v)) end)])
                            by (first [ eapply (kx_cell_store8 segs E m pre a v rest A)
                                      | eapply (kx_cell_store4 segs E m pre a v rest A) ];
                                [ change (pre ++ SE a W v :: rest) with log; exact HLF
                                | exact H
                                | change E with (kE zv xs); kx_estart_z zv
                                | change E with (kE zv xs); apply log_apart_ez_ok; kx_log_z zv ]);
                          change (pre ++ SE a W v :: rest) with log in Hn;
                          rewrite (ez_ok zv E (kE_atoms zv xs) v) in Hn;
                          let EQ := fresh "HCe" in let pf := w4_ez_pf zv E v in pose proof pf as EQ; rewrite EQ in Hn; clear EQ;
                          rewrite ?Z_to_bv_bv_unsigned in Hn;
                          clear H; rename Hn into H
                        | let pre' := eval cbn [app] in (pre ++ [SE a W v]) in go pre' rest ]
                else (let pre' := eval cbn [app] in (pre ++ [SE a W v]) in go pre' rest)
            | ?e :: ?rest => let pre' := eval cbn [app] in (pre ++ [e]) in go pre' rest
            | [] => fail "w4f_cell: no store found for" A
            end in
          let l := eval hnf in log in
          go constr:(@nil sentry) l
      end
    end
  end.

Ltac w4f_cells_post :=
  repeat match goal with
  | HLF : log_flat ?E ?log, H : rw_cells ?segs ?m ?A [?c] |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
      let l := eval hnf in log in
      lazymatch A with
      | _ + ?off => tryif kx_log_has_off l off
                    then first [ w4f_cell_gen H 8%nat off | w4f_cell_gen H 4%nat off | w4_cell H | w4_cell4 H | kx_frame H ]
                    else kx_frame H
      | _ => first [ w4_cell H | w4_cell4 H | kx_frame H ]
      end
  end.

Ltac w4f_frame3 MU :=
  repeat match goal with
  | H : rw_cells ?segs ?m (?P + ?off) [?c] |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
      lazymatch type of MU with munch ?W m ?m' =>
        first [ constr_eq off 288 | constr_eq off 328 | constr_eq off 368 ];
        let H' := fresh "HF" in
        pose proof (AFrameD.cells_frameD W m m' (P + off) [c] H MU ltac:(cbn [disjoint_from cells_size csize]; lia)) as H';
        clear H; rename H' into H
      end
  end.

End W4FSB.
Import W4FSB.


Section CANSEC1. Context {rc : runConstT}.
Section W4F.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (pdt pb : aptr) (SBL SBH : Z) (rstk : region).
  Notation SP := (bv_unsigned sp).
  Notation SPF := (SP + -480).
  Notation n := (zlen src).
  Notation DTL := (DTABLE_BYTES mtl).
  Hypothesis AH : AHEAP AI L RNG st LB m0.
  Hypothesis HDT : In (HB pdt DT DTL) LB.
  Hypothesis HDB : In (HB pb DST dcap) LB.
  Hypothesis LOA : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= SP - HUF_DEC_STACK_A.
  Hypothesis SPT : SP + 16 < al_top L.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis LCB : zlen cbs = 4096.
  Hypothesis MTL : 10 <= mtl <= 12.
  Variable cells : list deltX1.
  Hypothesis TOK : x1_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (2 * 2^tl)) (x1_bytes cells).
  Hypothesis DC : 0 < dcap < 2^32.
  Hypothesis NSM : 10 <= n < 2^26.
  Hypothesis SBB : SBL <= SS /\ SS + n <= SBH.
  Hypothesis SBA : ablk SBL SBH /\ SBL mod 8 = 0.
  Hypothesis DJ1 : KXGoM.apart DST dcap DT DTL.
  Hypothesis DJ2 : KXGoM.apart DST dcap SS n.
  Hypothesis UDT : unpoisoned m0 DT (DT + DTL).
  Hypothesis UDB : unpoisoned m0 DST (DST + dcap).
  Hypothesis USB : unpoisoned m0 SBL SBH.
  Hypothesis WSK : rng RNG lo (al_top L - lo).
  Hypothesis WIM : rng_aimg RNG.
  Hypothesis WDT : rng RNG DT DTL.
  Hypothesis WDB : rng RNG DST dcap.
  Hypothesis WSB : rng RNG SBL (SBH - SBL).
  Hypothesis WDTS : rng RNG (shad DT) (shlen (DTL + 7)).
  Hypothesis WDBS : rng RNG (shad DST) (shlen (dcap + 7)).
  Hypothesis WSBS : rng RNG (shad SBL) (shlen (SBH - SBL + 7)).
  Hypothesis RCL : rclean m0 rstk.
  Hypothesis RLO : r_lo rstk <= lo.
  Hypothesis RHI : SP <= r_hi rstk.
  Hypothesis RRL : ATOP <= r_rlo rstk.
  Hypothesis RRS : rrng RNG rstk.

  Notation DW := [(lo, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).
  Hypothesis w4_blocks : AIMG_HI <= DT /\ DT + DTL <= ATOP /\ DT mod 16 = 0 /\ AIMG_HI <= DST /\ DST + dcap <= ATOP /\ DST mod 16 = 0
                    /\ ablk DST (DST + dcap) /\ AIMG_HI <= SBL /\ SBH <= ATOP.
  Hypothesis w4_unp : forall mm, munch DW m0 mm ->
    unpoisoned mm DT (DT + DTL) /\ unpoisoned mm DST (DST + dcap) /\ unpoisoned mm SBL SBH.
  Hypothesis w4_dtl : 4100 <= DTL.
  Notation W4FX := (W4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs).

  Definition w4_ist (P pc : Z) (x8 x9 x10 x12 x18 x19 x20 x22 x25 : word) (mm : amem) : machine_state :=
    MS (mkR (Z_to_bv 64 (P + 296)) (Z_to_bv 64 P) gp tp (Z_to_bv 64 (-24)) (Z_to_bv 64 2) (Z_to_bv 64 3)
            x8 x9 x10 (Z_to_bv 64 (-1 * DT + -5)) x12 (Z_to_bv 64 (P + 256)) (Z_to_bv 64 (P + 336))
            (Z_to_bv 64 (-17)) (Z_to_bv 64 (-16)) (Z_to_bv 64 (-25)) x18 x19 x20 (Z_to_bv 64 AW4_K21) x22
            (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 AW4_KSB) x25 (Z_to_bv 64 AW4_KTB) (Z_to_bv 64 (DT + 4))
            (Z_to_bv 64 4) (Z_to_bv 64 5) (Z_to_bv 64 6) (Z_to_bv 64 (-8)))
       FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs).

  Definition w4_lo (o0 o1 o2 o3 : Z) (po4 : word) : list cell :=
    [C8 (Z_to_bv 64 (DST + o0)); C8 (Z_to_bv 64 (DST + o1)); C8 (Z_to_bv 64 (DST + o2)); C8 (Z_to_bv 64 (DST + o3)); C8 po4].
  Definition w4_li (i0 i1 i2 i3 : Z) (pi4 : word) : list cell :=
    [C8 (Z_to_bv 64 (SS + i0)); C8 (Z_to_bv 64 (SS + i1)); C8 (Z_to_bv 64 (SS + i2)); C8 (Z_to_bv 64 (SS + i3)); C8 pi4].
  Definition w4_lb (b0 b1 b2 b3 : Z) (pb4 : word) : list cell :=
    [C8 (Z_to_bv 64 b0); C8 (Z_to_bv 64 b1); C8 (Z_to_bv 64 b2); C8 (Z_to_bv 64 b3); C8 pb4].

  Lemma w4_ablk_ap : forall a b, ablk a b -> a <= b -> KXGoM.apart a (b - a) ASHOFF (ATOP / 8 + 1).
  Proof.
    intros a b H HL. pose proof (@ATOP_lo rc). pose proof (@ATOP_hi rc).
    unfold KXGoM.apart, ablk, AIMG_HI, KLS, ASHOFF in *. lia.
  Qed.

  Lemma w4_stk_ap : forall a, ATOP + 4096 <= a -> KXGoM.apart a 480 ASHOFF (ATOP / 8 + 1).
  Proof.
    intros a H. pose proof (@ATOP_lo rc). pose proof (@ATOP_hi rc).
    unfold KXGoM.apart, ASHOFF in *. lia.
  Qed.

  Lemma w4_tab11 : forall mm, tl = 11 -> bytes_at bsegs mm (DT + 4) cbs -> ztab_fact bsegs mm (DT + 4) 4096 2 [(0, 0, 11)].
  Proof using All.
    intros mm T11 BA z HZ lo' hi' FF.
    pose proof TOK as (TL1 & TL2 & TC). rewrite T11 in TL2, TC, ECB.
    cbn [find_field] in FF. revert FF.
    destruct (Z.eqb_spec 0 ((z - (DT + 4)) mod 2)) as [E0|E0]; intro FF; [injection FF as <- <- | discriminate FF].
    set (v := (z - (DT + 4)) / 2).
    assert (HZv : z = DT + 4 + 2 * v) by (pose proof (Z.div_mod (z - (DT + 4)) 2 ltac:(lia)); unfold v; lia).
    assert (Hv : 0 <= v < 2^11) by (unfold v; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    rewrite ECB in BA. change (x1_bytes cells) with (x1_bytes' cells) in BA.
    unfold FseNCount.Zlength in TL2.
    destruct (x1_cell_rd bsegs mm (DT + 4) cells (Z.to_nat (2 * 2 ^ 11)) v BA ltac:(lia)
                ltac:(rewrite Z2Nat.id by lia; lia) ltac:(lia)) as [R0 _].
    destruct (TC v Hv) as [NB _].
    rewrite HZv. exists (Z_to_bv 8 (x1_nbBits (nth (Z.to_nat v) cells x1_default))).
    rewrite <- ov_rdn. split; [exact R0 |].
    rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 8) with 8.
    rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma w4_tr : forall (mm mm' : amem) (fr mid l256 l296 l336 l256' l296' l336' : list cell) (buf' : list Z),
    W4FX mm fr mid l256 l296 l336 ->
    munch [(SPF + 256, SPF + 376); (DST, DST + dcap)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
    u8arr bsegs mm' DST (map (Z_to_bv 8) buf') -> zlen buf' = dcap ->
    rw_cells bsegs mm' (SPF + 256) l256' -> cells_size l256' = 40%nat ->
    rw_cells bsegs mm' (SPF + 296) l296' -> cells_size l296' = 40%nat ->
    rw_cells bsegs mm' (SPF + 336) l336' -> cells_size l336' = 40%nat ->
    W4FX mm' fr mid l256' l296' l336'.
  Proof using All.
    intros mm mm' fr mid l256 l296 l336 l256' l296' l336' buf' HW MU' WM' MI' OUT' LOUT2 C256' L256' C296' L296' C336' L336'.
    destruct HW as ((buf & OUT & LOUT) & SRCB & TB & DTH & STK & FRC & FRL & MIDC & MIDL & C256 & L256L & C296 & L296L
                    & C336 & L336L & FRSC & MI & MU & WM).
    pose proof w4_blocks as (BK1 & BK2 & BK3 & BK4 & BK5 & BK6 & BK7 & BK8 & BK9).
    pose proof (w4_sp_bounds AI L RNG st LB sp m0 lo AH LOA LOS SPT) as (S1 & S2 & S3 & S4).
    pose proof w4_dtl as HDTL.
    pose proof DJ1 as DJ1u. pose proof DJ2 as DJ2u. unfold KXGoM.apart in DJ1u, DJ2u.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
              (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))))))))))).
    - exists buf'. split; assumption.
    - eapply bytes_at_transport; [exact SRCB | exact MU' | cbn [disjoint_from]; rewrite length_map; lia].
    - eapply bytes_at_transport; [exact TB | exact MU' | cbn [disjoint_from]; lia].
    - eapply bytes_at_transport; [exact DTH | exact MU' | cbn [disjoint_from length]; lia].
    - eapply stk_transport_disjoint; [exact STK | exact MU' | exact WM' | cbn [disjoint_from]; lia].
    - eapply rw_cells_transport; [exact FRC | exact MU' | exact WM' | cbn [disjoint_from]; rewrite FRL; lia].
    - exact FRL.
    - eapply rw_cells_transport; [exact MIDC | exact MU' | exact WM' | cbn [disjoint_from]; rewrite MIDL; lia].
    - exact MIDL.
    - exact C256'.
    - exact L256'.
    - exact C296'.
    - exact L296'.
    - exact C336'.
    - exact L336'.
    - eapply rw_cells_transport; [exact FRSC | exact MU' | exact WM' | cbn [disjoint_from cells_size csize]; lia].
    - exact MI'.
    - eapply munch_trans; [exact MU |].
      apply (munch_weaken [(SPF + 256, SPF + 376); (DST, DST + dcap)]); [| exact MU'].
      intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (Hx1 & Hx2 & _). repeat split; lia.
    - eapply wmono_trans; [exact WM | exact WM'].
  Qed.

  Definition w4_fr (w0 w8 w16 : word) : list cell :=
    [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 AW4_M5); C8 (Z_to_bv 64 AW4_M7); C8 (Z_to_bv 64 SS); C8 (Z_to_bv 64 DT);
     C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (DST + dcap)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + dcap));
     C8 (Z_to_bv 64 SS)].

  Lemma w4_d4 : forall (Q : machine_state -> Prop) (mm : amem) (fr mid : list cell) (o0 o1 o2 o3 i0 i1 i2 i3 B0 B1 B2 B3 : Z)
      (po4 pi4 pb4 x8 x9 x10 x12 x18 x19 x20 x22 x25 : word),
    tl = 11 ->
    W4FX mm fr mid (w4_lo o0 o1 o2 o3 po4) (w4_li i0 i1 i2 i3 pi4) (w4_lb B0 B1 B2 B3 pb4) ->
    0 <= o0 -> o0 + 5 <= dcap -> 0 <= o1 -> o1 + 5 <= dcap -> 0 <= o2 -> o2 + 5 <= dcap -> 0 <= o3 -> o3 + 5 <= dcap ->
    0 <= B0 < 2^64 -> 0 <= B1 < 2^64 -> 0 <= B2 < 2^64 -> 0 <= B3 < 2^64 ->
    B0 mod 2^53 <> 0 -> B1 mod 2^53 <> 0 -> B2 mod 2^53 <> 0 -> B3 mod 2^53 <> 0 ->
    (forall (mm' : amem) (C0 C1 C2 C3 : Z) (y9 y10 y12 y18 y19 y20 y22 y25 : word),
       W4FX mm' fr mid (w4_lo o0 o1 o2 o3 po4) (w4_li i0 i1 i2 i3 pi4) (w4_lb C0 C1 C2 C3 pb4) ->
       0 <= C0 < 2^64 -> 0 <= C1 < 2^64 -> 0 <= C2 < 2^64 -> 0 <= C3 < 2^64 ->
       C0 mod 2^64 <> 0 -> C1 mod 2^64 <> 0 -> C2 mod 2^64 <> 0 -> C3 mod 2^64 <> 0 ->
       evtF bsegs RNG Q (w4_ist SPF 0x889b8 x8 y9 y10 y12 y18 y19 y20 y22 y25 mm')) ->
    evtF bsegs RNG Q (w4_ist SPF 0x88818 x8 x9 x10 x12 x18 x19 x20 x22 x25 mm).
  Proof using All.
    intros Q mm fr mid o0 o1 o2 o3 i0 i1 i2 i3 B0 B1 B2 B3 po4 pi4 pb4 x8 x9 x10 x12 x18 x19 x20 x22 x25
      T11 HW HO0 HO0b HO1 HO1b HO2 HO2b HO3 HO3b HB0 HB1 HB2 HB3 LB0 LB1 LB2 LB3 K.
    pose proof (w4_tab11 mm T11) as ZT0.
    unfold w4_lo, w4_li, w4_lb in HW, K. pose proof HW as HW0.
    destruct HW as ((buf & OUT & LOUT) & SRCB & TB & DTH & STK & FRC & FRL & MIDC & MIDL & C256 & L256L & C296 & L296L
                    & C336 & L336L & FRSC & MI & MU & WM).
    pose proof (ZT0 TB) as ZT. clear ZT0.
    pose proof w4_blocks as (BK1 & BK2 & BK3 & BK4 & BK5 & BK6 & BK7 & BK8 & BK9).
    pose proof (w4_sp_bounds AI L RNG st LB sp m0 lo AH LOA LOS SPT) as (S1 & S2 & S3 & S4).
    pose proof w4_dtl as HDTL.
    pose proof (w4_unp mm MU) as (UDT' & UDB' & USB').
    pose proof (@ATOP_lo rc) as HAL. pose proof (@ATOP_hi rc) as HAH.
    pose proof (AI_block AI _ _ _ _ _ _ _ _ AH HDT) as (_ & (KDT & _) & _).
    assert (UT : unpoisoned mm DT (DT + 4100)) by (eapply unpoisoned_sub; [exact UDT' | lia | lia]).
    assert (RP : rng RNG SPF 480) by (eapply rng_sub; [exact WSK | lia | lia]).
    assert (RT : rng RNG (DT + 4) 4096) by (eapply rng_sub; [exact WDT | lia | lia]).
    assert (RTS : rng RNG (shad DT) (shlen (4100 + 7))).
    { eapply rng_sub; [exact WDTS | lia |].
      assert (shlen (4100 + 7) <= shlen (DTL + 7)) by (unfold shlen; rewrite !Z.shiftr_div_pow2 by lia; apply Z.div_le_mono; lia).
      lia. }
    assert (AS1 : KXGoM.apart DST dcap ASHOFF (ATOP / 8 + 1)).
    { pose proof (w4_ablk_ap DST (DST + dcap) BK7 ltac:(lia)) as H. replace (DST + dcap - DST) with dcap in H by lia. exact H. }
    assert (AS2 : KXGoM.apart DT 4100 ASHOFF (ATOP / 8 + 1)).
    { pose proof (w4_ablk_ap DT (DT + DTL) KDT ltac:(lia)) as H. unfold KXGoM.apart in H |- *. lia. }
    assert (AS3 : KXGoM.apart SPF 480 ASHOFF (ATOP / 8 + 1)) by (apply w4_stk_ap; lia).
    assert (DJ1' : KXGoM.apart DST dcap (DT + 4) 4096) by (unfold KXGoM.apart in *; lia).
    assert (DJ2' : KXGoM.apart DST dcap SPF 480) by (unfold KXGoM.apart in *; lia).
    assert (DJ3' : KXGoM.apart SPF 480 (DT + 4) 4096) by (unfold KXGoM.apart in *; lia).
    assert (HDT' : 2^20 <= DT <= 2^47 - 4100) by (unfold AIMG_HI in BK1; lia).
    assert (HDST : 2^20 <= DST <= 2^47 - 1) by (unfold AIMG_HI in BK4; lia).
    assert (HDE : DST + dcap <= 2^47) by lia.
    assert (HP : 2^20 <= SPF <= 2^47 - 480) by lia.
    assert (HAT1 : DT + 4100 <= ATOP) by lia.
    assert (HAT3 : ATOP + 4096 <= SPF) by lia.
    assert (DT16 : DT mod 16 = 0) by exact BK3.
    assert (LOUT' : zlen (map (Z_to_bv 8) buf) = dcap) by (rewrite length_map; exact LOUT).
    unfold ASHOFF in AS1, AS2, AS3.
    set (P := SPF) in *. assert (HPE : P = SPF) by reflexivity. clearbody P.
    assert (K' : forall (mm' : amem) (c0 c1 c2 c3 y9 y10 y12 y18 y19 y20 y22 y25 : word) (buf' : list Z),
              munch [(P + 336, P + 368); (DST, DST + dcap)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
              u8arr bsegs mm' DST (map (Z_to_bv 8) buf') -> zlen buf' = dcap ->
              rw_cells bsegs mm' (P + 336) [C8 c0; C8 c1; C8 c2; C8 c3; C8 pb4] ->
              bv_unsigned c0 mod 2^64 <> 0 -> bv_unsigned c1 mod 2^64 <> 0 ->
              bv_unsigned c2 mod 2^64 <> 0 -> bv_unsigned c3 mod 2^64 <> 0 ->
              evtF bsegs RNG Q (w4_ist P 0x889b8 x8 y9 y10 y12 y18 y19 y20 y22 y25 mm')).
    { intros mm' c0 c1 c2 c3 y9 y10 y12 y18 y19 y20 y22 y25 buf' MU' WM' MI' OUT' LOUT2 C336' LC0 LC1 LC2 LC3.
      pose proof (bv_unsigned_in_range _ c0) as R0. pose proof (bv_unsigned_in_range _ c1) as R1.
      pose proof (bv_unsigned_in_range _ c2) as R2. pose proof (bv_unsigned_in_range _ c3) as R3.
      unfold bv_modulus in R0, R1, R2, R3. change (Z.of_N 64) with 64 in R0, R1, R2, R3.
      apply (K mm' (bv_unsigned c0) (bv_unsigned c1) (bv_unsigned c2) (bv_unsigned c3) y9 y10 y12 y18 y19 y20 y22 y25);
        [| lia | lia | lia | lia | exact LC0 | exact LC1 | exact LC2 | exact LC3].
      subst P.
      apply (w4_tr mm mm' fr mid _ _ _ _ _ _ buf' HW0);
        [ apply (munch_weaken [(SPF + 336, SPF + 368); (DST, DST + dcap)]); [| exact MU'];
          intros x Hx; cbn [outside] in Hx |- *; destruct Hx as (Hx1 & Hx2 & _); repeat split; lia
        | exact WM' | exact MI' | exact OUT' | exact LOUT2
        | eapply rw_cells_transport; [exact C256 | exact MU' | exact WM' | cbn [disjoint_from]; rewrite L256L; lia]
        | exact L256L
        | eapply rw_cells_transport; [exact C296 | exact MU' | exact WM' | cbn [disjoint_from]; rewrite L296L; lia]
        | exact L296L
        | rewrite !Z_to_bv_bv_unsigned; exact C336'
        | reflexivity ]. }
    clear - ZT TB LCB OUT LOUT' MI C256 C336 UT UDB' RP RT WDB RTS WDBS HDT' HDST HDE HP DC DT16
      HO0 HO0b HO1 HO1b HO2 HO2b HO3 HO3b HB0 HB1 HB2 HB3 LB0 LB1 LB2 LB3 DJ1' DJ2' DJ3' AS1 AS2 AS3 HAT1 BK5 BK6 HAT3 HAH K'.
    unfold w4_ist in K' |- *.
    cbv [AW4_KSB AW4_K21 AW4_KTB] in K' |- *.
    (kx_prepFm [0x889b8; 0x88f9c; 0x88fac; 0x88fb8; 0x88fc8; 0x88fd4; 0x88fe4; 0x88ff0; 0x89000; 0x8cb6c] 400%nat
      [KZTab (DT + 4) 4096 2 [(0, 0, 11)]; KZAlign DT 16;
       KZRange DT (2^20) (2^47 - 4100); KZRange DST (2^20) (2^47 - 1); KZRange dcap 1 (2^32); KZRange P (2^20) (2^47 - 480);
       KZRange o0 0 (2^32); KZRange o1 0 (2^32); KZRange o2 0 (2^32); KZRange o3 0 (2^32);
       KZRange (DST + o0) (2^20) (2^47 - 1); KZRange (DST + o1) (2^20) (2^47 - 1);
       KZRange (DST + o2) (2^20) (2^47 - 1); KZRange (DST + o3) (2^20) (2^47 - 1);
       KZRange B0 0 (2^64 - 1); KZRange B1 0 (2^64 - 1); KZRange B2 0 (2^64 - 1); KZRange B3 0 (2^64 - 1);
       KZWord (P + 256) 8 (DST + o0); KZWord (P + 264) 8 (DST + o1); KZWord (P + 272) 8 (DST + o2); KZWord (P + 280) 8 (DST + o3);
       KZWord (P + 336) 8 B0; KZWord (P + 344) 8 B1; KZWord (P + 352) 8 B2; KZWord (P + 360) 8 B3;
       KZWr (P + 256) 40; KZWr (P + 336) 40;
       KZWr (DST + o0 + 4) 1; KZWr (DST + o1 + 4) 1; KZWr (DST + o2 + 4) 1; KZWr (DST + o3 + 4) 1;
       KZDisj (DST + o0 + 4) 1 (DT + 4) 4096; KZDisj (DST + o1 + 4) 1 (DT + 4) 4096;
       KZDisj (DST + o2 + 4) 1 (DT + 4) 4096; KZDisj (DST + o3 + 4) 1 (DT + 4) 4096;
       KZDisj (DST + o0 + 4) 1 P 480; KZDisj (DST + o1 + 4) 1 P 480; KZDisj (DST + o2 + 4) 1 P 480; KZDisj (DST + o3 + 4) 1 P 480;
       KZDisj P 480 (DT + 4) 4096]
      [(DT + 4, 4096)]
      [(P, 480); (DT + 4, 4096); (DST + o0 + 4, 1); (DST + o1 + 4, 1); (DST + o2 + 4, 1); (DST + o3 + 4, 1)]
      [(DT + 4, 4096); (DST + o0 + 4, 1); (DST + o1 + 4, 1); (DST + o2 + 4, 1); (DST + o3 + 4, 1)];
      let D := eval vm_compute in (repeat true 256) in kx_goFL D).
    all: try w4br.
    all: try (w4fshd ATOP).
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => unfold KXGoM.apart in *; lia end).
    lazymatch goal with |- evtF _ _ _ _ => idtac | _ => fail "w4_d0: side goal left" end.
    kx_post_regs_keep.
    pose proof (munch_refl [(P + 336, P + 368); (DST, DST + dcap)] mm) as MU0.
    pose proof (wmono_refl bsegs mm) as WM0.
    kx_munch_wins MU0 [(P + 336, 32); (DST + o0 + 4, 1); (DST + o1 + 4, 1); (DST + o2 + 4, 1); (DST + o3 + 4, 1)].
    kx_post_mem_free.
    kx_cells_split C336. w4f_frame3 MU0. w4f_cells_post.
    lazymatch goal with HLF : KXS.log_flat ?E ?lg |- context [KXS.mem_denot ?E mm ?lg] =>
      destruct (kx_u8arr_ex bsegs E mm lg DST buf OUT HLF) as (buf' & OUT' & LOUT2)
    end.
    w4f_bits (P + 336) 52 ZT (DT + 4) HB0 LB0 e0.
    w4f_bits (P + 344) 52 ZT (DT + 4) HB1 LB1 e1.
    w4f_bits (P + 352) 52 ZT (DT + 4) HB2 LB2 e2.
    w4f_bits (P + 360) 52 ZT (DT + 4) HB3 LB3 e3.
    lazymatch goal with |- context [KXS.mem_denot ?E mm ?lg] => set (mm' := KXS.mem_denot E mm lg) in * end.
    try change (Z_to_bv 64 (- DT + -5)) with (Z_to_bv 64 (-1 * DT + -5)).
    eapply (K' mm' (alu64 ALU_SLL (Z_to_bv 64 B0) e0) (alu64 ALU_SLL (Z_to_bv 64 B1) e1)
                   (alu64 ALU_SLL (Z_to_bv 64 B2) e2) (alu64 ALU_SLL (Z_to_bv 64 B3) e3)).
    all: try assumption.
    all: try (rewrite LOUT2; rewrite length_map in LOUT'; exact LOUT').
    all: try kx_cells_merge.
  Qed.
  Lemma w4_rl : forall (Q : machine_state -> Prop) (mm : amem) (fr mid : list cell) (o0 o1 o2 o3 i0 i1 i2 i3 B0 B1 B2 B3 OL : Z)
      (po4 pi4 pb4 x9 x10 x12 x18 x19 x20 x22 x25 : word),
    W4FX mm fr mid (w4_lo o0 o1 o2 o3 po4) (w4_li i0 i1 i2 i3 pi4) (w4_lb B0 B1 B2 B3 pb4) ->
    0 <= o0 -> o0 + 5 <= dcap -> 0 <= o1 -> o1 + 5 <= dcap -> 0 <= o2 -> o2 + 5 <= dcap -> 0 <= o3 -> o3 + 5 <= dcap ->
    7 <= i0 -> i0 + 8 <= n -> 7 <= i1 -> i1 + 8 <= n -> 7 <= i2 -> i2 + 8 <= n -> 7 <= i3 -> i3 + 8 <= n ->
    1 <= B0 < 2^64 -> 1 <= B1 < 2^64 -> 1 <= B2 < 2^64 -> 1 <= B3 < 2^64 ->
    DST <= OL <= DST + dcap ->
    (forall (mm' : amem) (C0 C1 C2 C3 nb0 nb1 nb2 nb3 : Z) (y9 y10 y12 y18 y19 y20 y22 y25 : word),
       W4FX mm' fr mid (w4_lo (o0 + 5) (o1 + 5) (o2 + 5) (o3 + 5) po4) (w4_li (i0 - nb0) (i1 - nb1) (i2 - nb2) (i3 - nb3) pi4)
         (w4_lb C0 C1 C2 C3 pb4) ->
       0 <= nb0 <= 7 -> 0 <= nb1 <= 7 -> 0 <= nb2 <= 7 -> 0 <= nb3 <= 7 ->
       0 <= C0 < 2^64 -> 0 <= C1 < 2^64 -> 0 <= C2 < 2^64 -> 0 <= C3 < 2^64 ->
       C0 mod 2^8 <> 0 -> C1 mod 2^8 <> 0 -> C2 mod 2^8 <> 0 -> C3 mod 2^8 <> 0 ->
       (DST + o3 + 5 < OL -> evtF bsegs RNG Q (w4_ist SPF 0x88170 (Z_to_bv 64 OL) y9 y10 y12 y18 y19 y20 y22 y25 mm')) /\
       (OL <= DST + o3 + 5 -> evtF bsegs RNG Q (w4_ist SPF 0x880d8 (Z_to_bv 64 OL) y9 y10 y12 y18 y19 y20 y22 y25 mm'))) ->
    evtF bsegs RNG Q (w4_ist SPF 0x889b8 (Z_to_bv 64 OL) x9 x10 x12 x18 x19 x20 x22 x25 mm).
  Proof using All.
    intros Q mm fr mid o0 o1 o2 o3 i0 i1 i2 i3 B0 B1 B2 B3 OL po4 pi4 pb4 x9 x10 x12 x18 x19 x20 x22 x25
      HW HO0 HO0b HO1 HO1b HO2 HO2b HO3 HO3b HI0 HI0b HI1 HI1b HI2 HI2b HI3 HI3b HB0 HB1 HB2 HB3 HOL K.
    unfold w4_lo, w4_li, w4_lb in HW. pose proof HW as HW0. unfold w4_lo, w4_li, w4_lb in HW0.
    destruct HW as ((buf & OUT & LOUT) & SRCB & TB & DTH & STK & FRC & FRL & MIDC & MIDL & C256 & L256L & C296 & L296L
                    & C336 & L336L & FRSC & MI & MU & WM).
    pose proof w4_blocks as (BK1 & BK2 & BK3 & BK4 & BK5 & BK6 & BK7 & BK8 & BK9).
    pose proof (w4_sp_bounds AI L RNG st LB sp m0 lo AH LOA LOS SPT) as (S1 & S2 & S3 & S4).
    pose proof (w4_unp mm MU) as (UDT' & UDB' & USB').
    pose proof (@ATOP_lo rc) as HATL. pose proof (@ATOP_hi rc) as HATH.
    pose proof SBA as (SB1 & SBL8). pose proof SBB as (SBL1 & SBH1).
    pose proof (ablk_img _ _ SB1) as HSB0. pose proof (ablk_top _ _ SB1) as HSB2.
    assert (HSB : 2^20 <= SBL) by (unfold AIMG_HI in HSB0; lia).
    assert (ZC : ztab_fact bsegs mm AW4_KTB 64 1 [(0, 0, 63)]) by (apply ztab_fact_img; [exact MI | lia | vm_compute; reflexivity]).
    assert (RKT : rng RNG AW4_KTB 64) by (eapply rng_sub; [exact WIM | unfold AW4_KTB; lia | unfold AW4_KTB; lia]).
    assert (RP : rng RNG SPF 480) by (eapply rng_sub; [exact WSK | lia | lia]).
    assert (LSB : zlen (map (Z_to_bv 8) src) = n) by (rewrite length_map; reflexivity).
    assert (AS1 : KXGoM.apart SBL (SBH - SBL) ASHOFF (ATOP / 8 + 1)) by (apply w4_ablk_ap; [exact SB1 | lia]).
    assert (AS2 : KXGoM.apart SPF 480 ASHOFF (ATOP / 8 + 1)) by (apply w4_stk_ap; lia).
    assert (DJS : KXGoM.apart SBL (SBH - SBL) SPF 480) by (unfold KXGoM.apart; lia).
    assert (HP1 : ATOP + 4096 <= SPF) by lia.
    assert (HP2 : SPF <= 2^47 - 480) by lia.
    assert (HN : 10 <= n < 2^26) by exact NSM.
    assert (HD1 : 2^20 <= DST) by (unfold AIMG_HI in BK4; lia).
    assert (HD2 : DST + dcap <= ATOP) by exact BK5.
    assert (HDC : 1 <= dcap < 2^32) by lia.
    assert (HOL2 : OL <= ATOP) by lia.
    set (P := SPF) in *. assert (HPE : P = SPF) by reflexivity. clearbody P.
    destruct (Z_lt_ge_dec (DST + o3 + 5) OL) as [HOL1 | HOL1].
    - 
      assert (K' : forall (mm' : amem) (c0 c1 c2 c3 y9 y10 y12 y18 y19 y20 y22 y25 : word) (nb0 nb1 nb2 nb3 : Z),
       munch [(P + 256, P + 376)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
       rw_cells bsegs mm' (P + 256) [C8 (Z_to_bv 64 (DST + o0 + 5)); C8 (Z_to_bv 64 (DST + o1 + 5));
                                     C8 (Z_to_bv 64 (DST + o2 + 5)); C8 (Z_to_bv 64 (DST + o3 + 5)); C8 po4] ->
       rw_cells bsegs mm' (P + 296) [C8 (Z_to_bv 64 (SS + (i0 + -1 * nb0))); C8 (Z_to_bv 64 (SS + (i1 + -1 * nb1)));
                                     C8 (Z_to_bv 64 (SS + (i2 + -1 * nb2))); C8 (Z_to_bv 64 (SS + (i3 + -1 * nb3))); C8 pi4] ->
       rw_cells bsegs mm' (P + 336) [C8 c0; C8 c1; C8 c2; C8 c3; C8 pb4] ->
       0 <= nb0 <= 7 -> 0 <= nb1 <= 7 -> 0 <= nb2 <= 7 -> 0 <= nb3 <= 7 ->
       bv_unsigned c0 mod 2^8 <> 0 -> bv_unsigned c1 mod 2^8 <> 0 -> bv_unsigned c2 mod 2^8 <> 0 -> bv_unsigned c3 mod 2^8 <> 0 ->
       evtF bsegs RNG Q (w4_ist P 0x88170 (Z_to_bv 64 OL) y9 y10 y12 y18 y19 y20 y22 y25 mm')).
    { intros mm' c0 c1 c2 c3 y9 y10 y12 y18 y19 y20 y22 y25 nb0 nb1 nb2 nb3 MU' WM' MI' C256' C296' C336'
        N0 N1 N2 N3 LC0 LC1 LC2 LC3.
      pose proof (bv_unsigned_in_range _ c0) as R0. pose proof (bv_unsigned_in_range _ c1) as R1.
      pose proof (bv_unsigned_in_range _ c2) as R2. pose proof (bv_unsigned_in_range _ c3) as R3.
      unfold bv_modulus in R0, R1, R2, R3. change (Z.of_N 64) with 64 in R0, R1, R2, R3.
      subst P.
      apply (proj1 (K mm' (bv_unsigned c0) (bv_unsigned c1) (bv_unsigned c2) (bv_unsigned c3) nb0 nb1 nb2 nb3
                       y9 y10 y12 y18 y19 y20 y22 y25
                       ltac:(apply (w4_tr mm mm' fr mid _ _ _ _ _ _ buf HW0);
                         [ apply (munch_weaken [(SPF + 256, SPF + 376)]); [| exact MU'];
                           intros x Hx; cbn [outside] in Hx |- *; destruct Hx as (Hx1 & _); repeat split; lia
                         | exact WM' | exact MI'
                         | eapply u8arr_transport; [exact OUT | exact MU' | exact WM' | cbn [disjoint_from]; rewrite length_map; split; [lia | exact I]]
                         | exact LOUT
                         | unfold w4_lo; replace (DST + (o0 + 5)) with (DST + o0 + 5) by lia;
                           replace (DST + (o1 + 5)) with (DST + o1 + 5) by lia;
                           replace (DST + (o2 + 5)) with (DST + o2 + 5) by lia;
                           replace (DST + (o3 + 5)) with (DST + o3 + 5) by lia; exact C256'
                         | reflexivity
                         | unfold w4_li; replace (i0 - nb0) with (i0 + -1 * nb0) by lia;
                           replace (i1 - nb1) with (i1 + -1 * nb1) by lia;
                           replace (i2 - nb2) with (i2 + -1 * nb2) by lia;
                           replace (i3 - nb3) with (i3 + -1 * nb3) by lia; exact C296'
                         | reflexivity
                         | unfold w4_lb; rewrite !Z_to_bv_bv_unsigned; exact C336'
                         | reflexivity ])
                       N0 N1 N2 N3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) LC0 LC1 LC2 LC3)).
      lia. }
      clear - MI C256 C296 C336 SRCB LSB ZC USB' WSB WSBS SBL8 SBL1 SBH1 RP WIM RKT HSB HSB2 HP1 HP2 HN DJS AS1 AS2
        HD1 HD2 HDC HO0 HO0b HO1 HO1b HO2 HO2b HO3 HO3b HI0 HI0b HI1 HI1b HI2 HI2b HI3 HI3b HB0 HB1 HB2 HB3 HOL HOL1 HOL2 HATH HATL K'.
      rename K' into K. unfold w4_ist in K |- *.
      pose proof (@ATOP_hi rc) as HATH'. unfold ASHOFF in AS1, AS2.
      cbv [AW4_KSB AW4_K21 AW4_KTB] in *.
      (kx_prepFm [0x88170; 0x880d8; 0x8cb6c; 0x8900c; 0x89018; 0x89024; 0x89030; 0x8903c; 0x89048; 0x89054; 0x89060] 800%nat
        [KZTab 134547 64 1 [(0, 0, 63)]; KZAlign SBL 8; KZImg (65620 + 860) (65620 + 868); KZImg 134547 (134547 + 64);
         KZRange P (2^20) (2^47 - 480); KZRange SS (2^20) (2^47); KZRange n 10 (2^26); KZRange DST (2^20) (2^47 - 1);
         KZRange dcap 1 (2^32); KZRange OL (2^20) (2^47); KZRange (OL - (DST + o3 + 5)) 1 (2^47);
         KZRange o0 0 (2^32); KZRange o1 0 (2^32); KZRange o2 0 (2^32); KZRange o3 0 (2^32);
         KZRange (dcap - o0) 5 (2^32); KZRange (dcap - o1) 5 (2^32); KZRange (dcap - o2) 5 (2^32); KZRange (dcap - o3) 5 (2^32);
         KZRange i0 7 (2^26); KZRange i1 7 (2^26); KZRange i2 7 (2^26); KZRange i3 7 (2^26);
         KZRange (n - i0) 8 (2^26); KZRange (n - i1) 8 (2^26); KZRange (n - i2) 8 (2^26); KZRange (n - i3) 8 (2^26);
         KZRange B0 1 (2^64 - 1); KZRange B1 1 (2^64 - 1); KZRange B2 1 (2^64 - 1); KZRange B3 1 (2^64 - 1);
         KZWord (P + 256) 8 (DST + o0); KZWord (P + 264) 8 (DST + o1); KZWord (P + 272) 8 (DST + o2); KZWord (P + 280) 8 (DST + o3);
         KZWord (P + 296) 8 (SS + i0); KZWord (P + 304) 8 (SS + i1); KZWord (P + 312) 8 (SS + i2); KZWord (P + 320) 8 (SS + i3);
         KZWord (P + 336) 8 B0; KZWord (P + 344) 8 B1; KZWord (P + 352) 8 B2; KZWord (P + 360) 8 B3;
         KZWr (P + 256) 40; KZWr (P + 296) 40; KZWr (P + 336) 40; KZDisj SS n P 480]
        [(SS, n)]
        [(P, 480); (SS, n)]
        [(SS, n)];
        let D := eval vm_compute in (repeat true 256) in kx_goFL D).
      all: try w4fctz.
      all: try w4fbr.
      all: try (w4facc WIM).
      all: try (lazymatch goal with |- branch_taken _ _ _ = _ => w4f_rngs; w4br end).
      all: try (lazymatch goal with |- KXS.flat _ _ _ /\ _ => w4f_rngs; (w4fshd ATOP) end).
      all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => unfold KXGoM.apart in *; cbn [cells_size csize]; lia end).
      lazymatch goal with |- evtF _ _ _ _ => idtac | _ => fail "side goal left" end.
      kx_post_regs_keep.
      pose proof (munch_refl [(P + 256, P + 376)] mm) as MU0.
      pose proof (munch_refl [(P + 256, P + 288); (P + 296, P + 328); (P + 336, P + 368)] mm) as MU1.
      pose proof (wmono_refl bsegs mm) as WM0.
      kx_munch_wins MU0 [(P + 256, 120)].
      kx_munch_wins MU1 [(P + 256, 32); (P + 296, 32); (P + 336, 32)].
      kx_post_mem_free.
      kx_cells_split C256. kx_cells_split C296. kx_cells_split C336.
      w4f_frame3 MU1.
      w4f_cells_post.
      w4f_rlnb (P + 296) nb0. w4f_rlnb (P + 304) nb1. w4f_rlnb (P + 312) nb2. w4f_rlnb (P + 320) nb3.
      w4f_rlb (P + 336) c0. w4f_rlb (P + 344) c1. w4f_rlb (P + 352) c2. w4f_rlb (P + 360) c3.
      lazymatch goal with |- context [KXS.mem_denot ?E mm ?lg] => set (mm' := KXS.mem_denot E mm lg) in * end.
      eapply (K mm' c0 c1 c2 c3 _ _ _ _ _ _ _ _ nb0 nb1 nb2 nb3).
      all: try eassumption.
      all: try kx_cells_merge.
    - 
      assert (K' : forall (mm' : amem) (c0 c1 c2 c3 y9 y10 y12 y18 y19 y20 y22 y25 : word) (nb0 nb1 nb2 nb3 : Z),
       munch [(P + 256, P + 376)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
       rw_cells bsegs mm' (P + 256) [C8 (Z_to_bv 64 (DST + o0 + 5)); C8 (Z_to_bv 64 (DST + o1 + 5));
                                     C8 (Z_to_bv 64 (DST + o2 + 5)); C8 (Z_to_bv 64 (DST + o3 + 5)); C8 po4] ->
       rw_cells bsegs mm' (P + 296) [C8 (Z_to_bv 64 (SS + (i0 + -1 * nb0))); C8 (Z_to_bv 64 (SS + (i1 + -1 * nb1)));
                                     C8 (Z_to_bv 64 (SS + (i2 + -1 * nb2))); C8 (Z_to_bv 64 (SS + (i3 + -1 * nb3))); C8 pi4] ->
       rw_cells bsegs mm' (P + 336) [C8 c0; C8 c1; C8 c2; C8 c3; C8 pb4] ->
       0 <= nb0 <= 7 -> 0 <= nb1 <= 7 -> 0 <= nb2 <= 7 -> 0 <= nb3 <= 7 ->
       bv_unsigned c0 mod 2^8 <> 0 -> bv_unsigned c1 mod 2^8 <> 0 -> bv_unsigned c2 mod 2^8 <> 0 -> bv_unsigned c3 mod 2^8 <> 0 ->
       evtF bsegs RNG Q (w4_ist P 0x880d8 (Z_to_bv 64 OL) y9 y10 y12 y18 y19 y20 y22 y25 mm')).
    { intros mm' c0 c1 c2 c3 y9 y10 y12 y18 y19 y20 y22 y25 nb0 nb1 nb2 nb3 MU' WM' MI' C256' C296' C336'
        N0 N1 N2 N3 LC0 LC1 LC2 LC3.
      pose proof (bv_unsigned_in_range _ c0) as R0. pose proof (bv_unsigned_in_range _ c1) as R1.
      pose proof (bv_unsigned_in_range _ c2) as R2. pose proof (bv_unsigned_in_range _ c3) as R3.
      unfold bv_modulus in R0, R1, R2, R3. change (Z.of_N 64) with 64 in R0, R1, R2, R3.
      subst P.
      apply (proj2 (K mm' (bv_unsigned c0) (bv_unsigned c1) (bv_unsigned c2) (bv_unsigned c3) nb0 nb1 nb2 nb3
                       y9 y10 y12 y18 y19 y20 y22 y25
                       ltac:(apply (w4_tr mm mm' fr mid _ _ _ _ _ _ buf HW0);
                         [ apply (munch_weaken [(SPF + 256, SPF + 376)]); [| exact MU'];
                           intros x Hx; cbn [outside] in Hx |- *; destruct Hx as (Hx1 & _); repeat split; lia
                         | exact WM' | exact MI'
                         | eapply u8arr_transport; [exact OUT | exact MU' | exact WM' | cbn [disjoint_from]; rewrite length_map; split; [lia | exact I]]
                         | exact LOUT
                         | unfold w4_lo; replace (DST + (o0 + 5)) with (DST + o0 + 5) by lia;
                           replace (DST + (o1 + 5)) with (DST + o1 + 5) by lia;
                           replace (DST + (o2 + 5)) with (DST + o2 + 5) by lia;
                           replace (DST + (o3 + 5)) with (DST + o3 + 5) by lia; exact C256'
                         | reflexivity
                         | unfold w4_li; replace (i0 - nb0) with (i0 + -1 * nb0) by lia;
                           replace (i1 - nb1) with (i1 + -1 * nb1) by lia;
                           replace (i2 - nb2) with (i2 + -1 * nb2) by lia;
                           replace (i3 - nb3) with (i3 + -1 * nb3) by lia; exact C296'
                         | reflexivity
                         | unfold w4_lb; rewrite !Z_to_bv_bv_unsigned; exact C336'
                         | reflexivity ])
                       N0 N1 N2 N3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) LC0 LC1 LC2 LC3)).
      lia. }
      clear - MI C256 C296 C336 SRCB LSB ZC USB' WSB WSBS SBL8 SBL1 SBH1 RP WIM RKT HSB HSB2 HP1 HP2 HN DJS AS1 AS2
        HD1 HD2 HDC HO0 HO0b HO1 HO1b HO2 HO2b HO3 HO3b HI0 HI0b HI1 HI1b HI2 HI2b HI3 HI3b HB0 HB1 HB2 HB3 HOL HOL1 HOL2 HATH HATL K'.
      rename K' into K. unfold w4_ist in K |- *.
      pose proof (@ATOP_hi rc) as HATH'. unfold ASHOFF in AS1, AS2.
      cbv [AW4_KSB AW4_K21 AW4_KTB] in *.
      (kx_prepFm [0x88170; 0x880d8; 0x8cb6c; 0x8900c; 0x89018; 0x89024; 0x89030; 0x8903c; 0x89048; 0x89054; 0x89060] 800%nat
        [KZTab 134547 64 1 [(0, 0, 63)]; KZAlign SBL 8; KZImg (65620 + 860) (65620 + 868); KZImg 134547 (134547 + 64);
         KZRange P (2^20) (2^47 - 480); KZRange SS (2^20) (2^47); KZRange n 10 (2^26); KZRange DST (2^20) (2^47 - 1);
         KZRange dcap 1 (2^32); KZRange OL (2^20) (2^47); KZRange (DST + o3 + 5 - OL) 0 (2^47);
         KZRange o0 0 (2^32); KZRange o1 0 (2^32); KZRange o2 0 (2^32); KZRange o3 0 (2^32);
         KZRange (dcap - o0) 5 (2^32); KZRange (dcap - o1) 5 (2^32); KZRange (dcap - o2) 5 (2^32); KZRange (dcap - o3) 5 (2^32);
         KZRange i0 7 (2^26); KZRange i1 7 (2^26); KZRange i2 7 (2^26); KZRange i3 7 (2^26);
         KZRange (n - i0) 8 (2^26); KZRange (n - i1) 8 (2^26); KZRange (n - i2) 8 (2^26); KZRange (n - i3) 8 (2^26);
         KZRange B0 1 (2^64 - 1); KZRange B1 1 (2^64 - 1); KZRange B2 1 (2^64 - 1); KZRange B3 1 (2^64 - 1);
         KZWord (P + 256) 8 (DST + o0); KZWord (P + 264) 8 (DST + o1); KZWord (P + 272) 8 (DST + o2); KZWord (P + 280) 8 (DST + o3);
         KZWord (P + 296) 8 (SS + i0); KZWord (P + 304) 8 (SS + i1); KZWord (P + 312) 8 (SS + i2); KZWord (P + 320) 8 (SS + i3);
         KZWord (P + 336) 8 B0; KZWord (P + 344) 8 B1; KZWord (P + 352) 8 B2; KZWord (P + 360) 8 B3;
         KZWr (P + 256) 40; KZWr (P + 296) 40; KZWr (P + 336) 40; KZDisj SS n P 480]
        [(SS, n)]
        [(P, 480); (SS, n)]
        [(SS, n)];
        let D := eval vm_compute in ([true; true; true; true; false] ++ repeat true 251) in kx_goFL D).
      all: try w4fctz.
      all: try w4fbr.
      all: try (w4facc WIM).
      all: try (lazymatch goal with |- branch_taken _ _ _ = _ => w4f_rngs; w4br end).
      all: try (lazymatch goal with |- KXS.flat _ _ _ /\ _ => w4f_rngs; (w4fshd ATOP) end).
      all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => unfold KXGoM.apart in *; cbn [cells_size csize]; lia end).
      lazymatch goal with |- evtF _ _ _ _ => idtac | _ => fail "side goal left" end.
      kx_post_regs_keep.
      pose proof (munch_refl [(P + 256, P + 376)] mm) as MU0.
      pose proof (munch_refl [(P + 256, P + 288); (P + 296, P + 328); (P + 336, P + 368)] mm) as MU1.
      pose proof (wmono_refl bsegs mm) as WM0.
      kx_munch_wins MU0 [(P + 256, 120)].
      kx_munch_wins MU1 [(P + 256, 32); (P + 296, 32); (P + 336, 32)].
      kx_post_mem_free.
      kx_cells_split C256. kx_cells_split C296. kx_cells_split C336.
      w4f_frame3 MU1.
      w4f_cells_post.
      w4f_rlnb (P + 296) nb0. w4f_rlnb (P + 304) nb1. w4f_rlnb (P + 312) nb2. w4f_rlnb (P + 320) nb3.
      w4f_rlb (P + 336) c0. w4f_rlb (P + 344) c1. w4f_rlb (P + 352) c2. w4f_rlb (P + 360) c3.
      lazymatch goal with |- context [KXS.mem_denot ?E mm ?lg] => set (mm' := KXS.mem_denot E mm lg) in * end.
      eapply (K mm' c0 c1 c2 c3 _ _ _ _ _ _ _ _ nb0 nb1 nb2 nb3).
      all: try eassumption.
      all: try kx_cells_merge.
  Qed.
  Lemma w4_hd : forall (Q : machine_state -> Prop) (mm : amem) (w0 w8 w16 : word) (mid : list cell)
      (o0 o1 o2 o3 i0 i1 i2 i3 B0 B1 B2 B3 : Z) (po4 pi4 pb4 x8 x9 x10 x12 x18 x19 x20 x22 x25 : word),
    W4FX mm (w4_fr w0 w8 w16) mid (w4_lo o0 o1 o2 o3 po4) (w4_li i0 i1 i2 i3 pi4) (w4_lb B0 B1 B2 B3 pb4) ->
    0 <= o0 <= dcap -> 0 <= o1 <= dcap -> 0 <= o2 <= dcap -> 0 <= o3 <= dcap ->
    0 <= i0 -> i0 + 8 <= n -> 0 <= i1 -> i1 + 8 <= n -> 0 <= i2 -> i2 + 8 <= n -> 0 <= i3 -> i3 + 8 <= n ->
    (Z.min ((dcap - o3) / 5) (i0 / 7) = 0 \/ i1 < i0 \/ i2 < i1 \/ i3 < i2 ->
       forall (y8 y9 y10 y12 y18 : word), evtF bsegs RNG Q (w4_ist SPF 0x892c4 y8 y9 y10 y12 y18 x19 x20 x22 x25 mm)) ->
    (1 <= Z.min ((dcap - o3) / 5) (i0 / 7) -> i0 <= i1 -> i1 <= i2 -> i2 <= i3 ->
       forall (y9 y10 y12 y18 : word),
       evtF bsegs RNG Q (w4_ist SPF 0x88170 (Z_to_bv 64 (DST + o3 + 5 * Z.min ((dcap - o3) / 5) (i0 / 7)))
                          y9 y10 y12 y18 x19 x20 x22 x25 mm)) ->
    evtF bsegs RNG Q (w4_ist SPF 0x880d8 x8 x9 x10 x12 x18 x19 x20 x22 x25 mm).
  Proof using All.
    intros Q mm w0 w8 w16 mid o0 o1 o2 o3 i0 i1 i2 i3 B0 B1 B2 B3 po4 pi4 pb4 x8 x9 x10 x12 x18 x19 x20 x22 x25
      HW HO0 HO1 HO2 HO3 HI0 HI0b HI1 HI1b HI2 HI2b HI3 HI3b KX KC.
    unfold w4_fr, w4_lo, w4_li, w4_lb in HW.
    destruct HW as ((buf & OUT & LOUT) & SRCB & TB & DTH & STK & FRC & FRL & MIDC & MIDL & C256 & L256L & C296 & L296L
                    & C336 & L336L & FRSC & MI & MU & WM).
    pose proof w4_blocks as (BK1 & BK2 & BK3 & BK4 & BK5 & BK6 & BK7 & BK8 & BK9).
    pose proof (w4_sp_bounds AI L RNG st LB sp m0 lo AH LOA LOS SPT) as (S1 & S2 & S3 & S4).
    pose proof SBB as (SBL1 & SBH1). pose proof SBA as (SB1 & _).
    pose proof (ablk_img _ _ SB1) as HSB0. pose proof (ablk_top _ _ SB1) as HSB2.
    pose proof (@ATOP_lo rc) as HATL. pose proof (@ATOP_hi rc) as HATH.
    assert (RP : rng RNG SPF 480) by (eapply rng_sub; [exact WSK | lia | lia]).
    assert (HP : 2^20 <= SPF <= 2^47 - 480) by lia.
    assert (HS : 2^20 <= SS) by (unfold AIMG_HI in HSB0; lia).
    assert (HSE : SS + n <= 2^47) by lia.
    assert (HN : 10 <= n < 2^26) by exact NSM.
    assert (HD : 2^20 <= DST) by (unfold AIMG_HI in BK4; lia).
    assert (HDE : DST + dcap <= 2^47) by lia.
    assert (HDC : 1 <= dcap < 2^32) by lia.
    set (P := SPF) in *. assert (HPE : P = SPF) by reflexivity. clearbody P.
    unfold w4_ist in KX, KC |- *.
    clear - MI FRC C256 C296 RP HP HS HSE HN HD HDE HDC HO0 HO1 HO2 HO3 HI0 HI0b HI1 HI1b HI2 HI2b HI3 HI3b KX KC.
    cbv [AW4_KSB AW4_K21 AW4_KTB AW4_M5 AW4_M7] in *.
    destruct (Z_lt_ge_dec ((dcap - o3) / 5) (i0 / 7)) as [CA | CA].
    + 
      assert (RM : Z.min ((dcap - o3) / 5) (i0 / 7) = (dcap - o3) / 5) by lia.
      rewrite RM in KX, KC.
      assert (R0 : 0 <= (dcap - o3) / 5) by (apply Z.div_pos; lia).
      destruct (Z_lt_ge_dec ((dcap - o3) / 5) 1) as [CB | CB].
      * (kx_prepFm [0x88170; 0x892c4; 0x8cb6c] 200%nat
        [KZRange P (2^20) (2^47 - 480); KZRange SS (2^20) (2^47); KZRange n 10 (2^26); KZRange DST (2^20) (2^47);
         KZRange dcap 1 (2^32); KZRange o0 0 (2^32); KZRange o1 0 (2^32); KZRange o2 0 (2^32); KZRange o3 0 (2^32);
         KZRange (dcap - o3) 0 (2^32);
         KZRange i0 0 (2^26); KZRange i1 0 (2^26); KZRange i2 0 (2^26); KZRange i3 0 (2^26);
         KZWord (P + 24) 8 14757395258967641293; KZWord (P + 32) 8 2635249153387078803; KZWord (P + 64) 8 (DST + dcap); KZWord (P + 96) 8 SS;
         KZWord (P + 256) 8 (DST + o0); KZWord (P + 264) 8 (DST + o1); KZWord (P + 272) 8 (DST + o2); KZWord (P + 280) 8 (DST + o3);
         KZWord (P + 296) 8 (SS + i0); KZWord (P + 304) 8 (SS + i1); KZWord (P + 312) 8 (SS + i2); KZWord (P + 320) 8 (SS + i3)]
        (@nil (Z * Z)) [(P, 480)] (@nil (Z * Z));
        let D := eval vm_compute in [true; false] in kx_goFL D).
      all: try w4fhb.
      lazymatch goal with |- evtF _ _ _ _ => idtac | _ => fail "w4_hd: side goal left" end.
      kx_post_regs_keep.
      eapply KX. left; lia.
      * destruct (Z_lt_ge_dec i1 i0) as [CC | CC].
        -- (kx_prepFm [0x88170; 0x892c4; 0x8cb6c] 200%nat
        [KZRange P (2^20) (2^47 - 480); KZRange SS (2^20) (2^47); KZRange n 10 (2^26); KZRange DST (2^20) (2^47);
         KZRange dcap 1 (2^32); KZRange o0 0 (2^32); KZRange o1 0 (2^32); KZRange o2 0 (2^32); KZRange o3 0 (2^32);
         KZRange (dcap - o3) 0 (2^32);
         KZRange i0 0 (2^26); KZRange i1 0 (2^26); KZRange i2 0 (2^26); KZRange i3 0 (2^26);
         KZWord (P + 24) 8 14757395258967641293; KZWord (P + 32) 8 2635249153387078803; KZWord (P + 64) 8 (DST + dcap); KZWord (P + 96) 8 SS;
         KZWord (P + 256) 8 (DST + o0); KZWord (P + 264) 8 (DST + o1); KZWord (P + 272) 8 (DST + o2); KZWord (P + 280) 8 (DST + o3);
         KZWord (P + 296) 8 (SS + i0); KZWord (P + 304) 8 (SS + i1); KZWord (P + 312) 8 (SS + i2); KZWord (P + 320) 8 (SS + i3)]
        (@nil (Z * Z)) [(P, 480)] (@nil (Z * Z));
        let D := eval vm_compute in [true; true; false] in kx_goFL D).
      all: try w4fhb.
      lazymatch goal with |- evtF _ _ _ _ => idtac | _ => fail "w4_hd: side goal left" end.
      kx_post_regs_keep.
      eapply KX. right; left; lia.
        -- destruct (Z_lt_ge_dec i2 i1) as [CD | CD].
           ++ (kx_prepFm [0x88170; 0x892c4; 0x8cb6c] 200%nat
        [KZRange P (2^20) (2^47 - 480); KZRange SS (2^20) (2^47); KZRange n 10 (2^26); KZRange DST (2^20) (2^47);
         KZRange dcap 1 (2^32); KZRange o0 0 (2^32); KZRange o1 0 (2^32); KZRange o2 0 (2^32); KZRange o3 0 (2^32);
         KZRange (dcap - o3) 0 (2^32);
         KZRange i0 0 (2^26); KZRange i1 0 (2^26); KZRange i2 0 (2^26); KZRange i3 0 (2^26);
         KZWord (P + 24) 8 14757395258967641293; KZWord (P + 32) 8 2635249153387078803; KZWord (P + 64) 8 (DST + dcap); KZWord (P + 96) 8 SS;
         KZWord (P + 256) 8 (DST + o0); KZWord (P + 264) 8 (DST + o1); KZWord (P + 272) 8 (DST + o2); KZWord (P + 280) 8 (DST + o3);
         KZWord (P + 296) 8 (SS + i0); KZWord (P + 304) 8 (SS + i1); KZWord (P + 312) 8 (SS + i2); KZWord (P + 320) 8 (SS + i3)]
        (@nil (Z * Z)) [(P, 480)] (@nil (Z * Z));
        let D := eval vm_compute in [true; true; true; false] in kx_goFL D).
      all: try w4fhb.
      lazymatch goal with |- evtF _ _ _ _ => idtac | _ => fail "w4_hd: side goal left" end.
      kx_post_regs_keep.
      eapply KX. right; right; left; lia.
           ++ destruct (Z_lt_ge_dec i3 i2) as [CE | CE].
              ** (kx_prepFm [0x88170; 0x892c4; 0x8cb6c] 200%nat
        [KZRange P (2^20) (2^47 - 480); KZRange SS (2^20) (2^47); KZRange n 10 (2^26); KZRange DST (2^20) (2^47);
         KZRange dcap 1 (2^32); KZRange o0 0 (2^32); KZRange o1 0 (2^32); KZRange o2 0 (2^32); KZRange o3 0 (2^32);
         KZRange (dcap - o3) 0 (2^32);
         KZRange i0 0 (2^26); KZRange i1 0 (2^26); KZRange i2 0 (2^26); KZRange i3 0 (2^26);
         KZWord (P + 24) 8 14757395258967641293; KZWord (P + 32) 8 2635249153387078803; KZWord (P + 64) 8 (DST + dcap); KZWord (P + 96) 8 SS;
         KZWord (P + 256) 8 (DST + o0); KZWord (P + 264) 8 (DST + o1); KZWord (P + 272) 8 (DST + o2); KZWord (P + 280) 8 (DST + o3);
         KZWord (P + 296) 8 (SS + i0); KZWord (P + 304) 8 (SS + i1); KZWord (P + 312) 8 (SS + i2); KZWord (P + 320) 8 (SS + i3)]
        (@nil (Z * Z)) [(P, 480)] (@nil (Z * Z));
        let D := eval vm_compute in [true; true; true; true; false] in kx_goFL D).
      all: try w4fhb.
      lazymatch goal with |- evtF _ _ _ _ => idtac | _ => fail "w4_hd: side goal left" end.
      kx_post_regs_keep.
      eapply KX. right; right; right; lia.
              ** (kx_prepFm [0x88170; 0x892c4; 0x8cb6c] 200%nat
        [KZRange P (2^20) (2^47 - 480); KZRange SS (2^20) (2^47); KZRange n 10 (2^26); KZRange DST (2^20) (2^47);
         KZRange dcap 1 (2^32); KZRange o0 0 (2^32); KZRange o1 0 (2^32); KZRange o2 0 (2^32); KZRange o3 0 (2^32);
         KZRange (dcap - o3) 0 (2^32);
         KZRange i0 0 (2^26); KZRange i1 0 (2^26); KZRange i2 0 (2^26); KZRange i3 0 (2^26);
         KZWord (P + 24) 8 14757395258967641293; KZWord (P + 32) 8 2635249153387078803; KZWord (P + 64) 8 (DST + dcap); KZWord (P + 96) 8 SS;
         KZWord (P + 256) 8 (DST + o0); KZWord (P + 264) 8 (DST + o1); KZWord (P + 272) 8 (DST + o2); KZWord (P + 280) 8 (DST + o3);
         KZWord (P + 296) 8 (SS + i0); KZWord (P + 304) 8 (SS + i1); KZWord (P + 312) 8 (SS + i2); KZWord (P + 320) 8 (SS + i3)]
        (@nil (Z * Z)) [(P, 480)] (@nil (Z * Z));
        let D := eval vm_compute in [true; true; true; true; true] in kx_goFL D).
      all: try w4fhb.
      lazymatch goal with |- evtF _ _ _ _ => idtac | _ => fail "w4_hd: side goal left" end.
      kx_post_regs_keep.
      lazymatch goal with |- context [Z_to_bv 64 (DST + (o3 + 5 * ?X))] =>
        let EX := fresh "EX" in assert (EX : X = (dcap - o3) / 5) by w4f_xeq;
        rewrite EX; replace (DST + (o3 + 5 * ((dcap - o3) / 5))) with (DST + o3 + 5 * ((dcap - o3) / 5)) by ring
      end.
      eapply KC; lia.
    + 
      assert (RM : Z.min ((dcap - o3) / 5) (i0 / 7) = i0 / 7) by lia.
      rewrite RM in KX, KC.
      assert (R0 : 0 <= i0 / 7) by (apply Z.div_pos; lia).
      destruct (Z_lt_ge_dec (i0 / 7) 1) as [CB | CB].
      * (kx_prepFm [0x88170; 0x892c4; 0x8cb6c] 200%nat
        [KZRange P (2^20) (2^47 - 480); KZRange SS (2^20) (2^47); KZRange n 10 (2^26); KZRange DST (2^20) (2^47);
         KZRange dcap 1 (2^32); KZRange o0 0 (2^32); KZRange o1 0 (2^32); KZRange o2 0 (2^32); KZRange o3 0 (2^32);
         KZRange (dcap - o3) 0 (2^32);
         KZRange i0 0 (2^26); KZRange i1 0 (2^26); KZRange i2 0 (2^26); KZRange i3 0 (2^26);
         KZWord (P + 24) 8 14757395258967641293; KZWord (P + 32) 8 2635249153387078803; KZWord (P + 64) 8 (DST + dcap); KZWord (P + 96) 8 SS;
         KZWord (P + 256) 8 (DST + o0); KZWord (P + 264) 8 (DST + o1); KZWord (P + 272) 8 (DST + o2); KZWord (P + 280) 8 (DST + o3);
         KZWord (P + 296) 8 (SS + i0); KZWord (P + 304) 8 (SS + i1); KZWord (P + 312) 8 (SS + i2); KZWord (P + 320) 8 (SS + i3)]
        (@nil (Z * Z)) [(P, 480)] (@nil (Z * Z));
        let D := eval vm_compute in [false; false] in kx_goFL D).
      all: try w4fhb.
      lazymatch goal with |- evtF _ _ _ _ => idtac | _ => fail "w4_hd: side goal left" end.
      kx_post_regs_keep.
      eapply KX. left; lia.
      * destruct (Z_lt_ge_dec i1 i0) as [CC | CC].
        -- (kx_prepFm [0x88170; 0x892c4; 0x8cb6c] 200%nat
        [KZRange P (2^20) (2^47 - 480); KZRange SS (2^20) (2^47); KZRange n 10 (2^26); KZRange DST (2^20) (2^47);
         KZRange dcap 1 (2^32); KZRange o0 0 (2^32); KZRange o1 0 (2^32); KZRange o2 0 (2^32); KZRange o3 0 (2^32);
         KZRange (dcap - o3) 0 (2^32);
         KZRange i0 0 (2^26); KZRange i1 0 (2^26); KZRange i2 0 (2^26); KZRange i3 0 (2^26);
         KZWord (P + 24) 8 14757395258967641293; KZWord (P + 32) 8 2635249153387078803; KZWord (P + 64) 8 (DST + dcap); KZWord (P + 96) 8 SS;
         KZWord (P + 256) 8 (DST + o0); KZWord (P + 264) 8 (DST + o1); KZWord (P + 272) 8 (DST + o2); KZWord (P + 280) 8 (DST + o3);
         KZWord (P + 296) 8 (SS + i0); KZWord (P + 304) 8 (SS + i1); KZWord (P + 312) 8 (SS + i2); KZWord (P + 320) 8 (SS + i3)]
        (@nil (Z * Z)) [(P, 480)] (@nil (Z * Z));
        let D := eval vm_compute in [false; true; false] in kx_goFL D).
      all: try w4fhb.
      lazymatch goal with |- evtF _ _ _ _ => idtac | _ => fail "w4_hd: side goal left" end.
      kx_post_regs_keep.
      eapply KX. right; left; lia.
        -- destruct (Z_lt_ge_dec i2 i1) as [CD | CD].
           ++ (kx_prepFm [0x88170; 0x892c4; 0x8cb6c] 200%nat
        [KZRange P (2^20) (2^47 - 480); KZRange SS (2^20) (2^47); KZRange n 10 (2^26); KZRange DST (2^20) (2^47);
         KZRange dcap 1 (2^32); KZRange o0 0 (2^32); KZRange o1 0 (2^32); KZRange o2 0 (2^32); KZRange o3 0 (2^32);
         KZRange (dcap - o3) 0 (2^32);
         KZRange i0 0 (2^26); KZRange i1 0 (2^26); KZRange i2 0 (2^26); KZRange i3 0 (2^26);
         KZWord (P + 24) 8 14757395258967641293; KZWord (P + 32) 8 2635249153387078803; KZWord (P + 64) 8 (DST + dcap); KZWord (P + 96) 8 SS;
         KZWord (P + 256) 8 (DST + o0); KZWord (P + 264) 8 (DST + o1); KZWord (P + 272) 8 (DST + o2); KZWord (P + 280) 8 (DST + o3);
         KZWord (P + 296) 8 (SS + i0); KZWord (P + 304) 8 (SS + i1); KZWord (P + 312) 8 (SS + i2); KZWord (P + 320) 8 (SS + i3)]
        (@nil (Z * Z)) [(P, 480)] (@nil (Z * Z));
        let D := eval vm_compute in [false; true; true; false] in kx_goFL D).
      all: try w4fhb.
      lazymatch goal with |- evtF _ _ _ _ => idtac | _ => fail "w4_hd: side goal left" end.
      kx_post_regs_keep.
      eapply KX. right; right; left; lia.
           ++ destruct (Z_lt_ge_dec i3 i2) as [CE | CE].
              ** (kx_prepFm [0x88170; 0x892c4; 0x8cb6c] 200%nat
        [KZRange P (2^20) (2^47 - 480); KZRange SS (2^20) (2^47); KZRange n 10 (2^26); KZRange DST (2^20) (2^47);
         KZRange dcap 1 (2^32); KZRange o0 0 (2^32); KZRange o1 0 (2^32); KZRange o2 0 (2^32); KZRange o3 0 (2^32);
         KZRange (dcap - o3) 0 (2^32);
         KZRange i0 0 (2^26); KZRange i1 0 (2^26); KZRange i2 0 (2^26); KZRange i3 0 (2^26);
         KZWord (P + 24) 8 14757395258967641293; KZWord (P + 32) 8 2635249153387078803; KZWord (P + 64) 8 (DST + dcap); KZWord (P + 96) 8 SS;
         KZWord (P + 256) 8 (DST + o0); KZWord (P + 264) 8 (DST + o1); KZWord (P + 272) 8 (DST + o2); KZWord (P + 280) 8 (DST + o3);
         KZWord (P + 296) 8 (SS + i0); KZWord (P + 304) 8 (SS + i1); KZWord (P + 312) 8 (SS + i2); KZWord (P + 320) 8 (SS + i3)]
        (@nil (Z * Z)) [(P, 480)] (@nil (Z * Z));
        let D := eval vm_compute in [false; true; true; true; false] in kx_goFL D).
      all: try w4fhb.
      lazymatch goal with |- evtF _ _ _ _ => idtac | _ => fail "w4_hd: side goal left" end.
      kx_post_regs_keep.
      eapply KX. right; right; right; lia.
              ** (kx_prepFm [0x88170; 0x892c4; 0x8cb6c] 200%nat
        [KZRange P (2^20) (2^47 - 480); KZRange SS (2^20) (2^47); KZRange n 10 (2^26); KZRange DST (2^20) (2^47);
         KZRange dcap 1 (2^32); KZRange o0 0 (2^32); KZRange o1 0 (2^32); KZRange o2 0 (2^32); KZRange o3 0 (2^32);
         KZRange (dcap - o3) 0 (2^32);
         KZRange i0 0 (2^26); KZRange i1 0 (2^26); KZRange i2 0 (2^26); KZRange i3 0 (2^26);
         KZWord (P + 24) 8 14757395258967641293; KZWord (P + 32) 8 2635249153387078803; KZWord (P + 64) 8 (DST + dcap); KZWord (P + 96) 8 SS;
         KZWord (P + 256) 8 (DST + o0); KZWord (P + 264) 8 (DST + o1); KZWord (P + 272) 8 (DST + o2); KZWord (P + 280) 8 (DST + o3);
         KZWord (P + 296) 8 (SS + i0); KZWord (P + 304) 8 (SS + i1); KZWord (P + 312) 8 (SS + i2); KZWord (P + 320) 8 (SS + i3)]
        (@nil (Z * Z)) [(P, 480)] (@nil (Z * Z));
        let D := eval vm_compute in [false; true; true; true; true] in kx_goFL D).
      all: try w4fhb.
      lazymatch goal with |- evtF _ _ _ _ => idtac | _ => fail "w4_hd: side goal left" end.
      kx_post_regs_keep.
      lazymatch goal with |- context [Z_to_bv 64 (DST + (o3 + 5 * ?X))] =>
        let EX := fresh "EX" in assert (EX : X = i0 / 7) by w4f_xeq;
        rewrite EX; replace (DST + (o3 + 5 * (i0 / 7))) with (DST + o3 + 5 * (i0 / 7)) by ring
      end.
      eapply KC; lia.
  Qed.


  Definition w4_c117 (Q : machine_state -> Prop) (b0 b1 b2 b3 : Z) : Prop :=
    forall (mm : amem) (w0 w8 w16 po4 pi4 pb4 x8 x9 x10 x12 x18 x19 x20 x22 x25 : word),
      W4FX mm (w4_fr w0 w8 w16) (fast_args_cells DST dcap SS DT src b0 b1 b2 b3)
           (w4_lo 0 ((dcap + 3) / 4) (2 * ((dcap + 3) / 4)) (3 * ((dcap + 3) / 4)) po4)
           (w4_li (jt_len src 0 - 2) (jt_len src 0 + jt_len src 2 - 2) (jt_len src 0 + jt_len src 2 + jt_len src 4 - 2)
                  (n - 8) pi4)
           (w4_lb b0 b1 b2 b3 pb4) ->
      evtF bsegs RNG Q (w4_ist SPF 0x880d8 x8 x9 x10 x12 x18 x19 x20 x22 x25 mm).


  Lemma w4p_lay : KHIGH <= lo /\ lo + 8192 <= SP /\ SP <= 2^47 /\ ATOP + 4096 <= lo /\ 2^20 <= SPF.
  Proof using All.
    pose proof (w4_sp_bounds AI L RNG st LB sp m0 lo AH LOA LOS SPT) as (S1 & S2 & S3 & S4).
    pose proof (@ATOP_lo rc) as HA. unfold ATOP_MIN, KHIGH in *. lia.
  Qed.

  Lemma w4p_aheap : forall mm, munch DW m0 mm -> wmono bsegs m0 mm -> AHEAP AI L RNG st LB mm.
  Proof using All.
    intros mm MU WM. pose proof (AI_layout AI L RNG st LB m0 AH) as HL. unfold HUF_DEC_STACK_A in LOS.
    eapply (AI_frame AI); [exact AH | exact MU | exact WM |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; unfold aclient_range, aclient_app_range.
    - left. left. lia.
    - right. left. exists (HB pb DST dcap). split; [exact HDB|]. cbn. lia.
  Qed.

  Lemma w4p_appW : appW DW.
  Proof using All.
    pose proof w4p_lay as LY.
    destruct (AI_block AI L RNG st LB m0 pb DST dcap AH HDB) as (_ & (AB & _) & _).
    pose proof (ablk_app_blk _ _ AB ltac:(lia)) as AP. unfold app_blk in AP.
    unfold appW. apply Forall_cons; [cbv beta; cbn [fst snd]; lia |].
    apply Forall_cons; [cbv beta; cbn [fst snd]; lia | apply Forall_nil].
  Qed.

  Lemma w4p_cb8 : forall m A bs, rw_cells bsegs m A [CB 8 bs] -> rw_cells bsegs m A [C8 (le_bytes_to_word bs)].
  Proof.
    intros m A bs [[WF BA] WR]. cbn [cells_wf cell_wf] in WF. destruct WF as [HL _].
    split; [split|].
    - cbn [cells_wf cell_wf]. split; exact I.
    - cbn [cells_bytes cbytes] in BA |- *. rewrite (le8_of_bytes bs HL). exact BA.
    - cbn [cells_size csize] in WR |- *. exact WR.
  Qed.

  Lemma w4p_of_cb : forall m A cs bs, rw_cells bsegs m A [CB (cells_size cs) bs] -> bs = cells_bytes cs -> cells_wf cs ->
    rw_cells bsegs m A cs.
  Proof.
    intros m A cs bs [[_ BA] WR] E WF. subst bs. split; [split|]; [exact WF | |].
    - cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA. exact BA.
    - cbn [cells_size csize] in WR. rewrite Nat.add_0_r in WR. exact WR.
  Qed.

  Lemma w4p_evtF_eq : forall (P : machine_state -> Prop) ms ms', evtF bsegs RNG P ms' -> ms' = ms -> evtF bsegs RNG P ms.
  Proof. intros P ms ms' H E. subst ms'. exact H. Qed.

  Lemma w4p_rw_mid : forall m A cs k, rw_cells bsegs m A cs ->
    rw_cells bsegs m (A + Z.of_nat (cells_size (firstn k cs))) (firstn 4 (skipn k cs)).
  Proof.
    intros m A cs k H. rewrite <- (firstn_skipn k cs) in H.
    apply (proj1 (kx_rw_cells_app bsegs m A _ _)) in H. destruct H as [_ H].
    rewrite <- (firstn_skipn 4 (skipn k cs)) in H.
    apply (proj1 (kx_rw_cells_app bsegs m _ _ _)) in H. exact (proj1 H).
  Qed.

  Lemma w4p_W4F_eq : forall (mm : amem) (fr mid a b c a' b' c' : list cell),
    W4FX mm fr mid a b c -> a = a' -> b = b' -> c = c' -> W4FX mm fr mid a' b' c'.
  Proof. intros mm fr mid a b c a' b' c' H -> -> ->. exact H. Qed.

  Ltac w4plist :=
    repeat (apply (f_equal2 (@cons cell));
            [first [reflexivity | (apply (f_equal C8); apply (f_equal (Z_to_bv 64)); lia)] |]);
    reflexivity.

  Lemma w4p_bveq2 : forall a b, a = b \/ a = b + 2^64 \/ a + 2^64 = b -> Z_to_bv 64 a = Z_to_bv 64 b.
  Proof.
    intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2^64).
    destruct H as [E | [E | E]]; subst; [reflexivity | | symmetry].
    - rewrite <- (Z.mod_add b 1 (2^64)) by lia. f_equal; lia.
    - rewrite <- (Z.mod_add a 1 (2^64)) by lia. f_equal; lia.
  Qed.

  Ltac w4pveq :=
    first [ reflexivity | f_equal; ring | f_equal; lia | apply w4p_bveq2; lia
          | apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity ].

  Ltac w4pmeq :=
    f_equal;
    try (lazymatch goal with |- mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ => f_equal end);
    try (lazymatch goal with
         | |- Z_to_bv 64 ?a = Z_to_bv 64 ?b => w4pveq
         | |- Z_to_bv 64 ?a = ?w => first [ reflexivity | apply Z_to_bv_bv_unsigned ]
         | |- _ => reflexivity
         end).

  Ltac w4pcell :=
    first [ eassumption
          | lazymatch goal with |- rw_cells ?s ?m ?A [C8 ?w] =>
              match goal with H : rw_cells s m A [C8 ?v] |- _ => replace w with v; [exact H | w4pveq] end end ].

  Ltac w4pmerge :=
    repeat (lazymatch goal with |- rw_cells ?segs ?m ?A (?c :: ?c' :: ?cs) =>
              apply (proj2 (kx_rwc_cons segs m A c (c' :: cs))); split; [w4pcell|]; cbn [csize];
              lazymatch goal with
              | |- rw_cells _ _ (?a + ?b + Z.of_nat ?k) _ =>
                  tryif is_Zlit b then
                    (let v := eval vm_compute in (b + Z.of_nat k) in replace (a + b + Z.of_nat k) with (a + v) by lia)
                  else (let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v)
              | |- rw_cells _ _ (?a + Z.of_nat ?k) _ =>
                  let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v
              end end);
    w4pcell.

  Lemma w4p_trfr : forall (mm mm' : amem) (fr fr' mid l256 l296 l336 : list cell),
    W4FX mm fr mid l256 l296 l336 ->
    munch [(SPF, SPF + 104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
    rw_cells bsegs mm' SPF fr' -> cells_size fr' = 104%nat ->
    W4FX mm' fr' mid l256 l296 l336.
  Proof using All.
    intros mm mm' fr fr' mid l256 l296 l336 HW MU' WM' MI' FR' FRL'.
    destruct HW as ((buf & OUT & LOUT) & SRCB & TB & DTH & STK & FRC & FRL & MIDC & MIDL & C256 & L256L & C296 & L296L
                    & C336 & L336L & FRSC & MI & MU & WM).
    pose proof w4_blocks as (BK1 & BK2 & BK3 & BK4 & BK5 & BK6 & BK7 & BK8 & BK9).
    pose proof w4p_lay as (LY1 & LY2 & LY3 & LY4 & LY5).
    pose proof w4_dtl as HDTL.
    pose proof SBB as (SB1 & SB2). pose proof SBA as (SBA1 & _).
    assert (HSB : SBH <= ATOP) by (pose proof (@ATOP_lo rc); unfold ablk, AIMG_HI, KLS, ATOP_MIN in *; lia).
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj FR' (conj FRL' (conj _ (conj MIDL (conj _ (conj L256L
      (conj _ (conj L296L (conj _ (conj L336L (conj _ (conj MI' (conj _ _)))))))))))))))))).
    - exists buf. split; [|exact LOUT]. eapply u8arr_transport; [exact OUT | exact MU' | exact WM' |].
      rewrite length_map. cbn [disjoint_from]. lia.
    - eapply bytes_at_transport; [exact SRCB | exact MU' | cbn [disjoint_from]; rewrite length_map; lia].
    - eapply bytes_at_transport; [exact TB | exact MU' | cbn [disjoint_from]; lia].
    - eapply bytes_at_transport; [exact DTH | exact MU' | cbn [disjoint_from length]; lia].
    - eapply stk_transport_disjoint; [exact STK | exact MU' | exact WM' | cbn [disjoint_from]; lia].
    - eapply rw_cells_transport; [exact MIDC | exact MU' | exact WM' | cbn [disjoint_from]; rewrite MIDL; lia].
    - eapply rw_cells_transport; [exact C256 | exact MU' | exact WM' | cbn [disjoint_from]; rewrite L256L; lia].
    - eapply rw_cells_transport; [exact C296 | exact MU' | exact WM' | cbn [disjoint_from]; rewrite L296L; lia].
    - eapply rw_cells_transport; [exact C336 | exact MU' | exact WM' | cbn [disjoint_from]; rewrite L336L; lia].
    - eapply rw_cells_transport; [exact FRSC | exact MU' | exact WM' | cbn [disjoint_from cells_size csize]; lia].
    - eapply munch_trans; [exact MU |]. eapply munch_weaken; [| exact MU'].
      intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (H1 & H2 & _).
      split; [|exact I]; intro Hc; apply H1; lia.
    - eapply wmono_trans; [exact WM | exact WM'].
  Qed.

  Lemma w4p_trl : forall (A : Z) (mm mm' : amem) (fr mid l256 l296 l336 l256' l296' l336' : list cell),
    W4FX mm fr mid l256 l296 l336 -> SPF + 256 <= A -> A + 32 <= SPF + 376 ->
    munch [(SPF - 2224, SPF); (A, A + 32)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' -> stk bsegs mm' lo SPF ->
    rw_cells bsegs mm' (SPF + 256) l256' -> cells_size l256' = 40%nat ->
    rw_cells bsegs mm' (SPF + 296) l296' -> cells_size l296' = 40%nat ->
    rw_cells bsegs mm' (SPF + 336) l336' -> cells_size l336' = 40%nat ->
    W4FX mm' fr mid l256' l296' l336'.
  Proof using All.
    intros A mm mm' fr mid l256 l296 l336 l256' l296' l336' HW HA1 HA2 MU' WM' MI' ST' C256' L256' C296' L296' C336' L336'.
    destruct HW as ((buf & OUT & LOUT) & SRCB & TB & DTH & STK & FRC & FRL & MIDC & MIDL & C256 & L256L & C296 & L296L
                    & C336 & L336L & FRSC & MI & MU & WM).
    pose proof w4_blocks as (BK1 & BK2 & BK3 & BK4 & BK5 & BK6 & BK7 & BK8 & BK9).
    pose proof w4p_lay as (LY1 & LY2 & LY3 & LY4 & LY5).
    pose proof w4_dtl as HDTL.
    pose proof SBB as (SB1 & SB2). pose proof SBA as (SBA1 & _).
    assert (HSB : SBH <= ATOP) by (pose proof (@ATOP_lo rc); unfold ablk, AIMG_HI, KLS, ATOP_MIN in *; lia).
    refine (conj _ (conj _ (conj _ (conj _ (conj ST' (conj _ (conj FRL (conj _ (conj MIDL (conj C256' (conj L256'
      (conj C296' (conj L296' (conj C336' (conj L336' (conj _ (conj MI' (conj _ _)))))))))))))))))).
    - exists buf. split; [|exact LOUT]. eapply u8arr_transport; [exact OUT | exact MU' | exact WM' |].
      rewrite length_map. cbn [disjoint_from]. lia.
    - eapply bytes_at_transport; [exact SRCB | exact MU' | cbn [disjoint_from]; rewrite length_map; lia].
    - eapply bytes_at_transport; [exact TB | exact MU' | cbn [disjoint_from]; lia].
    - eapply bytes_at_transport; [exact DTH | exact MU' | cbn [disjoint_from length]; lia].
    - eapply rw_cells_transport; [exact FRC | exact MU' | exact WM' | cbn [disjoint_from]; rewrite FRL; lia].
    - eapply rw_cells_transport; [exact MIDC | exact MU' | exact WM' | cbn [disjoint_from]; rewrite MIDL; lia].
    - eapply rw_cells_transport; [exact FRSC | exact MU' | exact WM' | cbn [disjoint_from cells_size csize]; lia].
    - eapply munch_trans; [exact MU |]. eapply munch_weaken; [| exact MU'].
      intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (H1 & H2 & _).
      split; [|split; [|exact I]]; intro Hc; apply H1; lia.
    - eapply wmono_trans; [exact WM | exact WM'].
  Qed.

  Definition w4sel (j k : nat) (x l : list cell) : list cell := if Nat.eqb j k then x else l.

  Lemma w4p_mcstep : forall (j : nat) (A S : Z) (mm : amem) (fr mid cs l256 l296 l336 : list cell) (jb : list byte)
      (xra t0 t1 t2 y8 y9 a3 a4 a5 a6 a7 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 t3 t4 t5 t6 : word),
    W4FX mm fr mid l256 l296 l336 -> (j <= 2)%nat -> A = SPF + 256 + 40 * Z.of_nat j ->
    rw_cells bsegs mm A [CB 40 jb] ->
    rw_cells bsegs mm S cs -> cells_size cs = 32%nat -> SPF + 104 <= S -> S + 32 <= SPF + 256 ->
    (forall (m' : amem) (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word),
       W4FX m' fr mid (w4sel j 0 (cs ++ [C8 (le_bytes_to_word (skipn 32 jb))]) l256)
                      (w4sel j 1 (cs ++ [C8 (le_bytes_to_word (skipn 32 jb))]) l296)
                      (w4sel j 2 (cs ++ [C8 (le_bytes_to_word (skipn 32 jb))]) l336) ->
       evtF bsegs RNG POST (MS (mkR xra (Z_to_bv 64 SPF) gp tp u0 u1 u2 y8 y9 (Z_to_bv 64 A) b1 b2 b3 b4 b5 b6 b7
                               y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 u3 u4 u5 u6) FR (ret_pc xra) fc None m' (seg_rom bsegs))) ->
    evtF bsegs RNG POST (MS (mkR xra (Z_to_bv 64 SPF) gp tp t0 t1 t2 y8 y9 (Z_to_bv 64 A) (Z_to_bv 64 S) (Z_to_bv 64 32)
                             a3 a4 a5 a6 a7 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 t3 t4 t5 t6)
                        FR (Z_to_bv 64 331992) fc None mm (seg_rom bsegs)).
  Proof using All.
    intros j A S mm fr mid cs l256 l296 l336 jb xra t0 t1 t2 y8 y9 a3 a4 a5 a6 a7 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
      t3 t4 t5 t6 HW HJ HA DJ SC HS HS1 HS2 K.
    pose proof w4p_lay as LY. pose proof (AI_layout AI L RNG st LB m0 AH) as HLY.
    pose proof (w4_sp_bounds AI L RNG st LB sp m0 lo AH LOA LOS SPT) as (S1 & S2 & S3 & S4).
    pose proof HW as HW'.
    destruct HW' as (_ & _ & _ & _ & ST & _ & _ & _ & _ & C256 & L256L & C296 & L296L & C336 & L336L & _ & MI & MUD & WMD).
    pose proof (w4p_aheap mm MUD WMD) as AHm.
    pose proof (AI_rtcells AI _ _ _ _ _ AHm) as (_ & R1 & R2 & R3 & R4 & _ & R6 & R7 & _).
    pose proof (rclean_transport DW m0 mm rstk RCL MUD WMD w4p_appW) as RC.
    pose proof (rclean_shclean _ _ RC) as SHC.
    pose proof (shclean_hull _ _ _ _ _ SHC) as HU.
    pose proof (shclean_wr _ _ _ _ _ SHC) as WRS. pose proof (shclean_app_blk _ _ _ _ _ SHC) as APB.
    pose proof RRS as RRS'. unfold rrng in RRS'.
    pose proof DJ as DJW. destruct DJW as [[DJWF _] _]. cbn [cells_wf cell_wf] in DJWF. destruct DJWF as [LJB _].
    apply (rw_cells_split_CB bsegs mm A [] 40 jb [] [32%nat; 8%nat]) in DJ; [| reflexivity].
    cbn [app mk_CB_cells] in DJ.
    apply (proj1 (kx_rw_cells_app bsegs mm A [CB 32 (firstn 32 jb)] [CB 8 (firstn 8 (skipn 32 jb))])) in DJ.
    destruct DJ as [CJ1 CJ2]. cbn [cells_size csize Nat.add] in CJ2.
    pose proof SC as SCW. destruct SCW as [[WFs BS] _].
    assert (ESP : bv_unsigned (Z_to_bv 64 SPF) = SPF) by (apply unsigned_lit; lia).
    assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
    assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
    assert (En : bv_unsigned (Z_to_bv 64 32) = 32) by (apply unsigned_lit; lia).
    pose proof (proj1 (shclean_sub _ _ _ _ _ S (S + 32) SHC ltac:(lia) ltac:(lia) ltac:(lia))) as UZS.
    pose proof (proj1 (shclean_sub _ _ _ _ _ A (A + 32) SHC ltac:(lia) ltac:(lia) ltac:(lia))) as UZA.
    eapply evtF_cut.
    { eapply (I_asan_memcpy.asan_memcpy_spec RNG xra (Z_to_bv 64 SPF) gp tp t0 t1 t2 y8 y9 (Z_to_bv 64 A) (Z_to_bv 64 S)
               (Z_to_bv 64 32) a3 a4 a5 a6 a7 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 t3 t4 t5 t6 FR fc mm lo (cells_bytes cs)
               (firstn 32 jb) (r_rlo rstk) (r_rhi rstk) (r_rlo rstk) (r_rhi rstk));
      rewrite ?EA, ?ES, ?En, ?ESP;
      first [ exact MI | exact ST | exact BS | exact CJ1 | exact WIM | exact RRS' | exact WRS | exact R1 | exact R2
            | exact R3 | exact R4 | exact R6 | exact R7 | reflexivity
            | (rewrite (cells_bytes_length cs WFs), HS; reflexivity)
            | (eapply app_blk_sub; [exact APB | lia | lia | lia])
            | exact UZS | exact UZA
            | (eapply rng_sub; [exact WSK | lia | lia])
            | (unfold KHIGH in *; lia) | lia ]. }
    intros ms' PO. unfold I_asan_memcpy.asan_memcpy_post in PO. rewrite EA, ES, En, ESP in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & EQ & MU1 & WM1 & MI1 & ST1
                    & RW1 & BS1).
    subst ms'. apply K.
    change (Z.to_nat 32) with 32%nat in RW1.
    assert (T : forall B l, rw_cells bsegs mm B l -> SPF <= B -> (B + Z.of_nat (cells_size l) <= A \/ A + 32 <= B) ->
                rw_cells bsegs m' B l).
    { intros B l HB HB1 HB2. eapply rw_cells_transport; [exact HB | exact MU1 | exact WM1 | cbn [disjoint_from]; lia]. }
    assert (NEW : rw_cells bsegs m' A (cs ++ [C8 (le_bytes_to_word (skipn 32 jb))])).
    { apply (proj2 (kx_rw_cells_app bsegs m' A cs _)). split.
      - eapply w4p_of_cb; [rewrite HS; exact RW1 | reflexivity | exact WFs].
      - rewrite HS. apply w4p_cb8.
        rewrite firstn_all2 in CJ2 by (rewrite length_skipn; lia).
        exact (T _ _ CJ2 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)). }
    assert (LN : cells_size (cs ++ [C8 (le_bytes_to_word (skipn 32 jb))]) = 40%nat)
      by (rewrite cells_size_app, HS; reflexivity).
    destruct j as [|[|[|j]]]; [| | | lia]; cbn [w4sel Nat.eqb]; cbn [Z.of_nat] in HA;
      (eapply (w4p_trl A mm m'); [exact HW | lia | lia | exact MU1 | exact WM1 | exact MI1 | exact ST1 | .. ]);
      first [ exact LN | exact L256L | exact L296L | exact L336L
            | (replace (SPF + 256) with A by lia; exact NEW)
            | (replace (SPF + 296) with A by lia; exact NEW)
            | (replace (SPF + 336) with A by lia; exact NEW)
            | (apply T; [exact C256 | lia | rewrite L256L; lia])
            | (apply T; [exact C296 | lia | rewrite L296L; lia])
            | (apply T; [exact C336 | lia | rewrite L336L; lia]) ].
  Qed.

  Lemma w4p_s4 : forall (Q : machine_state -> Prop) (mm : amem) (mid l256 l296 l336 : list cell) (w0 w8 w16 w24 w32 : word)
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word),
    W4FX mm [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 (Z_to_bv 64 SS); C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 n);
             C8 (Z_to_bv 64 (DST + dcap)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + dcap));
             C8 (Z_to_bv 64 SS)] mid l256 l296 l336 ->
    (forall (mm' : amem) (y8 y9 y10 y12 y18 y19 y20 y22 y25 : word),
       W4FX mm' (w4_fr w0 w8 w16) mid l256 l296 l336 ->
       evtF bsegs RNG Q (w4_ist SPF 557272 y8 y9 y10 y12 y18 y19 y20 y22 y25 mm')) ->
    evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 (SPF + 256)) x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 AW4_KSB) x25 x26 (Z_to_bv 64 (DT + 4))
               x28 x29 x30 x31)
          FR (Z_to_bv 64 557116) fc None mm (seg_rom bsegs)).
  Proof using All.
    intros Q mm mid l256 l296 l336 w0 w8 w16 w24 w32 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
      x25 x26 x28 x29 x30 x31 HW K.
    pose proof HW as HW0.
    destruct HW as (_ & _ & _ & _ & _ & FRC & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI & _ & _).
    pose proof (w4_sp_bounds AI L RNG st LB sp m0 lo AH LOA LOS SPT) as (S1 & S2 & S3 & S4).
    pose proof w4_blocks as (BK1 & BK2 & BK3 & BK4 & BK5 & BK6 & BK7 & BK8 & BK9).
    pose proof w4_dtl as HDTL.
    assert (RP : rng RNG SPF 480) by (eapply rng_sub; [exact WSK | lia | lia]).
    assert (HDT' : 2^20 <= DT <= 2^47 - 4100) by (unfold AIMG_HI in BK1; lia).
    assert (HP : 2^20 <= SPF <= 2^47 - 480) by lia.
    set (P := SPF) in *. assert (HPE : P = SPF) by reflexivity. clearbody P.
    assert (K' : forall (mm' : amem) (y8 y9 y10 y12 y18 y19 y20 y22 y25 : word),
              munch [(P, P + 104)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
              rw_cells bsegs mm' P (w4_fr w0 w8 w16) ->
              evtF bsegs RNG Q (w4_ist P 557272 y8 y9 y10 y12 y18 y19 y20 y22 y25 mm')).
    { intros mm' y8 y9 y10 y12 y18 y19 y20 y22 y25 MU' WM' MI' FR'. subst P. apply K.
      eapply w4p_trfr; [exact HW0 | exact MU' | exact WM' | exact MI' | exact FR' | reflexivity]. }
    clear - FRC MI RP WIM HDT' HP K'.
    unfold w4_ist, w4_fr in K'. cbv [AW4_KSB AW4_K21 AW4_KTB AW4_M5 AW4_M7] in K' |- *.
    kx_runFmd [557272] 100%nat (repeat true 64)
      [KZRange P (2^20) (2^47 - 480); KZRange DT (2^20) (2^47 - 4100); KZWr (P + 24) 8; KZWr (P + 32) 8;
       KZImg 66424 66432]
      (@nil (Z * Z)) [(P, 480)] (@nil (Z * Z)).
    all: try (w4facc WIM).
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => lia end).
    lazymatch goal with |- evtF _ _ _ _ => idtac | _ => fail "S4: side goal left" end.
    kx_post_regs_keep.
    pose proof (munch_refl [(P, P + 104)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
    kx_munch_wins MUW [(P + 24, 8); (P + 32, 8)].
    kx_post_mem_free.
    kx_cells_split FRC. kx_cells_post.
    lazymatch goal with |- context [KXS.mem_denot ?E mm ?l] => set (m1 := KXS.mem_denot E mm l) in *; clearbody m1 end.
    eapply w4p_evtF_eq; [eapply (K' m1); [exact MUW | exact WMr | assumption | w4pmerge] | w4pmeq].
  Qed.

  Lemma w4p_s23 : forall (mm : amem) (w0 w8 w16 w24 w32 pbq : word) (j256 j296 : list byte) (b0 b1 b2 b3 : Z)
      (u0 u1 u2 a1 a2 a3 a4 a5 a6 a7 u3 u4 u5 u6 : word),
    W4FX mm [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 (Z_to_bv 64 SS); C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 n);
             C8 (Z_to_bv 64 (DST + dcap)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + dcap));
             C8 (Z_to_bv 64 SS)]
         (fast_args_cells DST dcap SS DT src b0 b1 b2 b3) [CB 40 j256] [CB 40 j296]
         [C8 (Z_to_bv 64 b0); C8 (Z_to_bv 64 b1); C8 (Z_to_bv 64 b2); C8 (Z_to_bv 64 b3); C8 pbq] ->
    w4_c117 POST b0 b1 b2 b3 ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 557080) (Z_to_bv 64 SPF) gp tp u0 u1 u2 (Z_to_bv 64 dcap) (Z_to_bv 64 DST) (Z_to_bv 64 (SPF + 336))
               a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 DT) (Z_to_bv 64 SS) s4 s5 s6 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 AW4_KSB) s9 s10
               (Z_to_bv 64 (DT + 4)) u3 u4 u5 u6)
          FR (Z_to_bv 64 557080) fc None mm (seg_rom bsegs)).
  Proof using All.
    intros mm w0 w8 w16 w24 w32 pbq j256 j296 b0 b1 b2 b3 u0 u1 u2 a1 a2 a3 a4 a5 a6 a7 u3 u4 u5 u6 HW K.
    pose proof w4p_lay as (LY1 & LY2 & LY3 & LY4 & LY5).
    assert (K2 : evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 557096) (Z_to_bv 64 SPF) gp tp u0 u1 u2 (Z_to_bv 64 dcap) (Z_to_bv 64 DST) (Z_to_bv 64 (SPF + 296))
               (Z_to_bv 64 (SPF + 104)) (Z_to_bv 64 32) a3 a4 a5 a6 a7 (Z_to_bv 64 DT) (Z_to_bv 64 SS) s4 s5 s6
               (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 AW4_KSB) s9 s10 (Z_to_bv 64 (DT + 4)) u3 u4 u5 u6)
          FR (Z_to_bv 64 331992) fc None mm (seg_rom bsegs))).
    { pose proof HW as HW'. unfold fast_args_cells in HW'. cbv zeta in HW'.
      destruct HW' as (_ & _ & _ & _ & _ & _ & _ & MIDC & _ & _ & _ & C296 & _ & _ & _ & _ & _ & _ & _).
      pose proof (w4p_rw_mid _ _ _ 0 MIDC) as SRC. cbn [firstn skipn cells_size csize Nat.add] in SRC.
      replace (SPF + 104 + Z.of_nat 0) with (SPF + 104) in SRC by lia.
      eapply (w4p_mcstep 1 (SPF + 296) (SPF + 104) mm _ _ _ _ _ _ j296);
        [exact HW | lia | lia | exact C296 | exact SRC | reflexivity | lia | lia |].
      intros m3 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 HW3. cbn [w4sel Nat.eqb app] in HW3.
      rewrite ret_pc_even by (first [lia | reflexivity]).
      assert (K3 : evtF bsegs RNG POST
        (MS (mkR (Z_to_bv 64 557116) (Z_to_bv 64 SPF) gp tp v0 v1 v2 (Z_to_bv 64 (SPF + 256)) (Z_to_bv 64 DST)
                 (Z_to_bv 64 (SPF + 256)) (Z_to_bv 64 (SPF + 136)) (Z_to_bv 64 32) c3 c4 c5 c6 c7 (Z_to_bv 64 DT) (Z_to_bv 64 SS)
                 s4 s5 s6 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 AW4_KSB) s9 s10 (Z_to_bv 64 (DT + 4)) v3 v4 v5 v6)
            FR (Z_to_bv 64 331992) fc None m3 (seg_rom bsegs))).
      { pose proof HW3 as HW3'. unfold fast_args_cells in HW3'. cbv zeta in HW3'.
        destruct HW3' as (_ & _ & _ & _ & _ & _ & _ & MIDC3 & _ & C256 & _ & _ & _ & _ & _ & _ & _ & _ & _).
        pose proof (w4p_rw_mid _ _ _ 4 MIDC3) as SRC3. cbn [firstn skipn cells_size csize Nat.add] in SRC3.
        replace (SPF + 104 + Z.of_nat 32) with (SPF + 136) in SRC3 by lia.
        eapply (w4p_mcstep 0 (SPF + 256) (SPF + 136) m3 _ _ _ _ _ _ j256);
          [exact HW3 | lia | lia | exact C256 | exact SRC3 | reflexivity | lia | lia |].
        intros m4 e0 e1 e2 d1 d2 d3 d4 d5 d6 d7 e3 e4 e5 e6 HW4. cbn [w4sel Nat.eqb app] in HW4.
        rewrite ret_pc_even by (first [lia | reflexivity]).
        eapply (w4p_s4 POST m4 (fast_args_cells DST dcap SS DT src b0 b1 b2 b3)
                  (w4_lo 0 ((dcap + 3) / 4) (2 * ((dcap + 3) / 4)) (3 * ((dcap + 3) / 4)) (le_bytes_to_word (skipn 32 j256)))
                  (w4_li (jt_len src 0 - 2) (jt_len src 0 + jt_len src 2 - 2) (jt_len src 0 + jt_len src 2 + jt_len src 4 - 2)
                         (n - 8) (le_bytes_to_word (skipn 32 j296)))
                  (w4_lb b0 b1 b2 b3 pbq)).
        - eapply w4p_W4F_eq; [exact HW4 | unfold w4_lo; w4plist | unfold w4_li; w4plist | unfold w4_lb; w4plist].
        - intros mm' y8 y9 y10 y12 y18 y19 y20 y22 y25 HWf.
          exact (K mm' w0 w8 w16 _ _ _ y8 y9 y10 y12 y18 y19 y20 y22 y25 HWf). }
      kx_runFm [331992] 20%nat [KZRange SP (2^20 + 480) (2^47)] (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
      all: kx_post_regs_keep; try cbn [KXS.mem_denot].
      eapply w4p_evtF_eq; [exact K3 | w4pmeq]. }
    kx_runFm [331992] 20%nat [KZRange SP (2^20 + 480) (2^47)] (@nil (Z * Z)) (@nil (Z * Z)) (@nil (Z * Z)).
    all: kx_post_regs_keep; try cbn [KXS.mem_denot].
    eapply w4p_evtF_eq; [exact K2 | w4pmeq].
  Qed.

  Lemma w4_pre : forall (w0 w8 w16 w24 w32 w64 w96 : word) (j256 j296 j336 : list byte) (b0 b1 b2 b3 : Z) (mm : amem)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    W4FX mm [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 (Z_to_bv 64 SS); C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 n); C8 w64;
             C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + dcap)); C8 w96]
         (fast_args_cells DST dcap SS DT src b0 b1 b2 b3) [CB 40 j256] [CB 40 j296] [CB 40 j336] ->
    w4_c117 POST b0 b1 b2 b3 ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 dcap) (Z_to_bv 64 DST) (Z_to_bv 64 1)
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 DT) (Z_to_bv 64 SS) s4 s5 s6
               (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 AW4_KSB) s9 s10 s11 x28 x29 x30 x31)
          FR (Z_to_bv 64 AW4_FA) fc None mm (seg_rom bsegs)).
  Proof using All.
    intros w0 w8 w16 w24 w32 w64 w96 j256 j296 j336 b0 b1 b2 b3 mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
      HW K.
    pose proof HW as HW0.
    unfold fast_args_cells in HW. cbv zeta in HW.
    destruct HW as (_ & _ & _ & _ & _ & FRC & _ & MIDC & _ & _ & _ & _ & _ & _ & _ & _ & MI & _ & _).
    pose proof (w4_sp_bounds AI L RNG st LB sp m0 lo AH LOA LOS SPT) as (S1 & S2 & S3 & S4).
    pose proof w4_blocks as (BK1 & BK2 & BK3 & BK4 & BK5 & BK6 & BK7 & BK8 & BK9).
    pose proof w4_dtl as HDTL.
    pose proof w4p_lay as LY.
    pose proof SBB as (SB1 & SB2). pose proof SBA as (SBA1 & _).
    pose proof (@ATOP_lo rc) as HAL. pose proof (@ATOP_hi rc) as HAH.
    assert (RP : rng RNG SPF 480) by (eapply rng_sub; [exact WSK | lia | lia]).
    assert (HDT' : 2^20 <= DT <= 2^47 - 4100) by (unfold AIMG_HI in BK1; lia).
    assert (HDST : 2^20 <= DST <= 2^47 - 1) by (unfold AIMG_HI in BK4; lia).
    assert (HDE : DST + dcap <= 2^47) by lia.
    assert (HSS : 2^20 <= SS <= 2^47) by (unfold ablk, AIMG_HI, KLS, ATOP_MIN in *; lia).
    assert (HP : 2^20 <= SPF <= 2^47 - 480) by lia.
    set (P := SPF) in *. assert (HPE : P = SPF) by reflexivity. clearbody P.
    assert (K1 : forall mm1 : amem, munch [(P, P + 104)] mm mm1 -> wmono bsegs mm mm1 -> mem_inv bsegs mm1 ->
               rw_cells bsegs mm1 P [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 (Z_to_bv 64 SS); C8 (Z_to_bv 64 DT);
                                     C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (DST + dcap)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST);
                                     C8 (Z_to_bv 64 (DST + dcap)); C8 (Z_to_bv 64 SS)] ->
               evtF bsegs RNG POST
                 (MS (mkR (Z_to_bv 64 557080) (Z_to_bv 64 P) gp tp x5 x6 x7 (Z_to_bv 64 dcap) (Z_to_bv 64 DST)
                          (Z_to_bv 64 (P + 336)) (Z_to_bv 64 (P + 168)) (Z_to_bv 64 32) x13 x14 x15 x16 x17
                          (Z_to_bv 64 DT) (Z_to_bv 64 SS) s4 s5 s6 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 AW4_KSB) s9 s10
                          (Z_to_bv 64 (DT + 4)) x28 x29 x30 x31)
                     FR (Z_to_bv 64 331992) fc None mm1 (seg_rom bsegs))).
    { intros mm1 MU1 WM1 MI1 FR1. subst P.
      pose proof (w4p_trfr mm mm1 _ _ _ _ _ _ HW0 MU1 WM1 MI1 FR1 eq_refl) as HW1.
      pose proof HW1 as HW1'. unfold fast_args_cells in HW1'. cbv zeta in HW1'.
      destruct HW1' as (_ & _ & _ & _ & _ & _ & _ & MIDC1 & _ & _ & _ & _ & _ & C336 & _ & _ & _ & _ & _).
      pose proof (w4p_rw_mid _ _ _ 8 MIDC1) as SRC. cbn [firstn skipn cells_size csize Nat.add] in SRC.
      replace (SPF + 104 + Z.of_nat 64) with (SPF + 168) in SRC by lia.
      eapply (w4p_mcstep 2 (SPF + 336) (SPF + 168) mm1 _ _ _ _ _ _ j336);
        [exact HW1 | lia | lia | exact C336 | exact SRC | reflexivity | lia | lia |].
      intros m2 u0 u1 u2 a1 a2 a3 a4 a5 a6 a7 u3 u4 u5 u6 HW2. cbn [w4sel Nat.eqb app] in HW2.
      rewrite ret_pc_even by (first [lia | reflexivity]).
      exact (w4p_s23 m2 w0 w8 w16 w24 w32 _ j256 j296 b0 b1 b2 b3 u0 u1 u2 a1 a2 a3 a4 a5 a6 a7 u3 u4 u5 u6 HW2 K). }
    clear - FRC MIDC MI RP HDT' HDST HDE HSS HP DC K1.
    unfold AW4_FA. cbv [AW4_KSB] in K1 |- *.
    kx_runFmd [331992] 100%nat (repeat true 64)
      [KZRange P (2^20) (2^47 - 480); KZRange DT (2^20) (2^47 - 4100); KZRange DST (2^20) (2^47 - 1);
       KZRange dcap 1 (2^32); KZRange SS (2^20) (2^47);
       KZWord (P + 200) 8 (DT + 4); KZWord (P + 208) 8 SS; KZWord (P + 216) 8 (DST + dcap);
       KZWr (P + 64) 8; KZWr (P + 96) 8]
      (@nil (Z * Z)) [(P, 480)] (@nil (Z * Z)).
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => lia end).
    lazymatch goal with |- evtF _ _ _ _ => idtac | _ => fail "S1: side goal left" end.
    kx_post_regs_keep.
    pose proof (munch_refl [(P, P + 104)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
    kx_munch_wins MUW [(P + 64, 8); (P + 96, 8)].
    kx_post_mem_free.
    kx_cells_split FRC. kx_cells_post.
    lazymatch goal with |- context [KXS.mem_denot ?E mm ?l] => set (m1 := KXS.mem_denot E mm l) in *; clearbody m1 end.
    eapply w4p_evtF_eq; [eapply (K1 m1); [exact MUW | exact WMr | assumption | w4pmerge] | w4pmeq].
  Qed.
End W4F.
End CANSEC1.
