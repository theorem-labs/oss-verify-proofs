(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg AProto ABase ADepot_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AKit AKit2 AModelFacts F_apoison F_aalloc_s F_aalloc1 F_aalloc2 F_aalloc3.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_aalloc () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib5AsanW9F_apoison<poison_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00I47Corelib5Lists7ListDef6Forall00C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic3and01C47Corelib5Lists7ListDef:Forall_indK47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvK59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells7cell_wfC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z3powC47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC56Stdlib6ZArith6BinInt1Z2ltC47Corelib4Init5Logic3notK46Stdlib9micromega7EnvRing5PExpr01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4AImg5asegsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase7AIMG_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase7AIMG_LOC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z;log2_nonnegC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1Z<log2_le_monoC56Stdlib6ZArith6BinInt1Z9log2_pow2C47Corelib4Init5Logic6eq_indK46Stdlib9micromega5Tauto8GFormula03C47Corelib4Init5Logic9False_indK46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z;land_nonnegK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z9log2_landC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z8min_specC56Stdlib6ZArith6BinInt1Z8log2_lorc59OSSVerify5KrLib5AsanW8F_aalloc?lt_pow2_of_log2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9F_aalloc2:hdr_b1_midC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib5AsanW5ABase6al_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9F_aalloc1<allocA_cellsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase4sclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase4iclrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib3Lib3Arr6u32arrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6to_natK47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec8AsanCtrl7rz_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;needed_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3eqbK47Corelib7Numbers7BinNums1Z03K59OSSVerify5KrLib3Lib5Cells4cell03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase8al_nodesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase8al_storeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib5AsanW5ABase4al_UC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib5AsanW<ADepot_iface6ADEPOTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC59OSSVerify5KrLib5AsanW;AModelFacts;small_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:is_primaryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<rounded_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6rz_logC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW8F_aalloc=allocate_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusK59OSSVerify5KrLib5AsanW4AKit5boxed01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW4AKit5boxed00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9F_aalloc1;allocA_postC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9F_aalloc1;allocA_specC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K46Stdlib9micromega5Tauto8GFormula01C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib3Lib3Arr@u64arr_transportC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02c59OSSVerify5KrLib5AsanW8F_aallocDpoison_cells_frame_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<ADepot_iface9adi_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9F_aalloc2<allocBC_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF8rng_sub'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9F_aalloc2<allocBC_specC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses8or_morphC59OSSVerify5KrLib5AsanW;AModelFactsCrz_size_small_casesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW8F_aalloc@hdr_b1_mid_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9F_aalloc3;allocD_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9F_aalloc3;allocD_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame<munch_weakenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;munch_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6ExElim:ex_elim_16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9evtF_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6ExElim:ex_elim_19C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF8evtF_cutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6ExElim:ex_elim_15C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8class_idC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=size_of_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC59OSSVerify5KrLib4LibA5ExecF4evtFC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04C47Corelib4Init3Nat3addC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C47Corelib5Lists7ListDef6repeatK47Corelib4Init5Logic2ex01C59OSSVerify5KrLib5AsanW:F_aalloc_s7ARSSLIMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase5ATSDIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase5ATSDKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase5ATP88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase4ATSDC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init5Logic4True00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI59OSSVerify5KrLib5AsanW5ABase7alayout00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase3ATPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase9AINSTANCEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9F_aalloc1>allocate_entryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase7AINITEDC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_Z".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Lemma poison_cells_frame_b : forall m m' W,
  poison_cells m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) W -> poison_cells m'.
Proof.
ltac2:(KReplay.run1 (kr_t_F_aalloc ()) ["CANSEC1"] "p'0h01Hh12H0h22H1h31Wh41Ah51mh62m'h72csh84segsh91ih:2H2h;7__arithh<4__ffh=8__varmaph>5__with?4__x1h@4__x2hA4__x3hB4__x4hC4__x5hD4__x6hE1nhF1DhG2HAhH2HBhI2HWhJ2IHhK2MUhL2P1hM2P2hN2P3hO2P4hP2P5hQ2P6hR2P7hS2PChT2WMhU2hihV2ivhW1lhX2lohY1xi001pi011zp%0p&0p;1p;3p;2p;4p;7p;:p;8p10000p4p7210p1000\p4p710p8g001:j11Tg001_k102Tg002=k100Tg002`k10WTg003Bj1hTg003bk108Tg004ck306Tg005Wk304Tg006KR0k20FTg006kj22Tg007Gj2cTg007ak30;Tg008Bj3LTg009>j1zTg009^j3gTg00:>k40:Tg00:^j1kTg00;=j2eTg00;fj3jTg00<Ok205Tg00=;j2wTg00=Yj4vTg00>7k10ITg00>Uk10HTg00?3k10ETg00?^j2]Tg00@Aj10Tg00@fk101Tg00AHk20@Tg00Ajk20?Tg00BDk20=Tg00C0j3~Tg00CJk30VTg00Cik40UTg00D[j4:Tg00E6k70TTg00EYj1@Tg00F7j2yTg00F]k10OTg00GRR1j23Tg00Gmj1DTg00Hdj1?Tg00I^j1<Tg00JTj2BTg00K4k20GTg00KQj2KTg00Kij1uTg00LIj4RTg00M?j4tTg00N6j4sTg00Nhm:0DTg00Oij3rTg00Pfj2ATg00QCj4qTg00R8j3oTg00Rhk30BTg00SEk30ATg00Sbk30JTg00TEk40KTg00U0k70LTg00UTk70MTg00V8k80NTg00V\k109Tg00WQk10>Tg00XJk10PTg00Y9k30QTg00YWk20RTg00Z3k10STg00ZLk20<Tf0R2#1#1p=\g00ZoR3@0B32p=pB0A332p=}f2R4f1R5'A/22p==B0J352p=MP4g00[MR6g00[lR7P7g00\LR8P3P5g00\lP2H0Kg00]SK0Lp=5P4P6P7P7P8P5P2K0Mp>03f3R9P6P7P7P8P4P5P2L0Np=|%12#0#1#0p=n%02#0#0#1p=Z%12#1#0#0p={%12#1#1#@p=N%02#1p=X%12#0#1#1p=P%02#1#0#1p=i%12#@,y5$09p=O%12#0p=8%02#1#0#0p=m%02#0#1#1p=b%02#0#0#0p=l%12#1#0#1p=a1y52$09p=f%02#0p=`%12#1#1#1p=Fg00^3R6?g52p=9g00^hR:P4P5P2CRp=4%02#0#0#0#0#0#0#0p=_%12#@p>07P:f5R;f4R<P9CRP:P4P5P2CR'3p=^P:f6R=P;P<CRP:P9P4P5CR/32'3p=7P:P9P4P5CR/32p=xP:P4P5P2Ctp=V&0>2#up=>P:P4P5P2Csp=UP:P4P5P2Cqp=TP5P2g00_]R>P>C:p=YP4%D5P>P2C:p=Qg00`9R?/22p=C%u5,A4/22p=I1A52$0Pp=6Ao:52p=[B0Q4529~<9p=G20R52,34p=JA~452$0Sp=E20<32p=;f7R@13=;P<P9P4P5P2C:C:p=HAr:52p=SP=P;P<P9P4P5C:P2C:p=WP=P;P<P9P4P5P2C:C:p=dP<1394P5P2C:p>0Cg00`WRA#1RB#1RC#1S00#1S01#\RD$02RE$00Q00$02RF$00RG$0WRH[RIg00a<#hRJ&084B06594B04:<920F33RKg00anRL%p2'2%}2g00bfRM'2'cXVKRN<0;912M5ROA=45LRPPKPN%hKRQAL2<9W3P>%zK?L94eP0P3P3%p5,2L%}5/2M'cB0;KN5RNf8R0=L4@AgK<9f9R>;L0[[[^WQP2P3P3P4P5H0:RR#p,2L%}R/2M'cf;RRf:RS5L4f<RT?=R;12<T'cAL9TRg00c^RUg00dJRV#kRW#kRX#kRY,e31e3XRX1e3V5j35j3g00diRV+05%kY,e31e3W9j3X5j3005V%zURV5gU3g%hURUP3P31w3<P41w3=CvP5P31w3;P9&0I3RXCvCv&0H3RW&0E3RY1]3ARZ1]3B'MR[%0B,]3R\55Y&017R7PY%0AR]#1R^,]3R_=5YZP7PY1]3]R`95Y\1]3CRC=5Y_603YP7A5Y[`A5YCZ603YC|C|C|20@Y8R8P2P4g00eURCg00f5RZ+0?20=24=~CZdB0V3?5H0URZb<b=b>X?3X@3XA3XB3XC3XD3A=25<12=512=<12;@'cA=9<;12=9'c[[[^?3^@3^A3^B3^C3^D3P2PMPLP;P=PTf=S02PSPRP9O9b;P2C:P3P3P;P<H0:=gK9?LTReWJX:NW2X3QXU3XX3P5P2O2n2001100000121101101XYKP0P<K0TWHWGXE3X43AL094\P\O^E3^43P1%nA#Z#Z#{#NRO%1A#X#P#i#n#P,OERP%8A#X#i#\#m#b,OERK%8A#X#l#a#l#NRQ,fERN%8A#b#{#{#P,OERL%8A#`#F#b#Z#\,OERM%8A#`#F#b#b#NRC,fER`%z6R['9R7'9R_'9R\'9Ra'9Rb'9Rc54@RdP@%nA#`#m#i#8#NRe%8A#X#a#m#8#P,OES03/9[RfP@%8A#X#a#m#P#NRg%8A#P#n#a#b,OES04%8A#P#8#`#a#Z,OES05/9[S06'9RhP@PQ%`]#l#_R]#\#F#F#F,OES07/9[RiP@PC%0]#`#l#_#_#_R]#@,fES081fE?S09Q09/9[S0:'9S0;'9R?P@%8A#X#Z#\#Z#Z$07Rj%@AS0<,yF$0OS0=/9[RFP@%1A#X#8#a#i#P#NRk%0]#_#_#@,fES0>/9[REE^F7F7R]13d]P<A4>OcPSPePfPSPgPhPSPQPiPSPCP?PSPjPFPSPkPEE^F7F7P1A4RefR]PRPgPhPRPQPiPRPCP?PRPjPFA4RkEF7F7RdPRPOPc13]dCxP2Q02?4eff>RdPgPhPdPQPiPdPCP?PdPjPFA4dkEF7F7P1f?Rd?4ghR]PdPQPiPdPCP?PdPjPFPdPkPEE^F7RlPdPOPcPdPePf13]lF7P2fAS0??4ghfBRlPQPiPlPCP?PlPjPFPlPkPEE^F7P1fCRl?4QiR]PlPCP?PlPjPFA4lkEF7RmPlPOPcPlPePfPlPgPh13]mCxF7P2fES0@?4QifFRmPCP?PmPjPFA4mkEF7P1fGRm?4C?R]PmPjPFPmPkPEE^RnPmPOPcPmPePfPmPgPhPmPQPi13]nF7F7P2fIS0A?4C?fJRnPjPFPnPkPEE^P1fKR]?4jFRoA4]kERpP]POPcP]PePfP]PgPhP]PQPiP]PCP?13opCxF7F7P2fMRp?4jFfNRo?4kES0BA4oOcA4oefS0CA4oghS0DA4oQiS0EA4oC?S0FA4ojFS0GQ0B'3S0H'3S0I'3S0J'3S0KAVoOc%>cRq9UoO%Dc%?cRr9ToO%<P%<K%<N%<L%<M%<`%D[R['Y7Q77Q_7Q\7Qa7Qb%COS0L1BGrRb%@B%@D+0GRB5IORag00fUR\1K2bPHfPRb%u5R_,6O'[PGPrP5DG[]9Rrg00g4#hR7%h6R6P;P9P5P2CRR`B06;<9RMB04@;<RL%>99L@<RNP1P>P=P;P<CtRKP>P=P;%><RPCsRsPSP@P=%>;RtCsP>P0P@P=P;P<P9P4P5P2N:0DRuP2n2001000000120000000UUUUW7X43X6IX5IX3JW8RvPs\N\L\M\`^76^43^6I^5I^3J^87RwP1%C;S0MA=;PBS0N%C2RP?J2t16@59rR0&01GRx5EH[^93S0O'3S0P%C=PSP>P0P@P=P;P<P9P4P5P2O:RyP5n2001000000120000000VNVLVMV`X76X43X6IX5IX3JX87S0QQ0M\N\L\M\`^76^43^6I^5I^3J^87S0RP2P:fORzfQR{PbPOPcPmPpfLRmPnPOPqPVPUPXPW%1D#\#F#NRD#;R|%;OR}55YP8PZb<b=b>12DOR~P2b;P~eS0SPVPUPXPW%\^S0T$07R^#;,M}%0A#F#8#i#F#F#NRA#;R}55YP8PZb<b=b>A=O^AP2b;1AOqS0U/2AeS0VO4O:b1b0S0WPaPrP1PKPsPSP@P=P;CtPuP5n2001000000120000000VNVLVMV`X76X43X6IX5IX3JX87RuPK\N\L\M\`^76^43^6I^5I^3J^87RKP1%D<P>P=P;%?<RsCqRrPSP@P=%?;RSCqPyP2n2001000000120000000VNVLVMV`X76X43X6IX5IX3JX87RaPr\N\L\M\`^76^43^6I^5I^3J^87RrP1Q0M1BGs=I;BRs1BGSRS,K2PH16@_9oR0PG%?=R^P5DG[^9\S0X'3R~AI=SBRS1BG^,K2PH160_9oT>PG%?@P5DG[^9\S0Y'3PyP2n2001000000120000000VNVLVMV`X76X43X6IX5IX3JX87R^P~\N\L\M\`^76^43^6I^5I^3J^87R~P1PsQ0XPSPyP5n2001000000120000000VNVLVMV`X76X43X6IX5IX3JX87S0ZPs\N\L\M\`^76^43^6I^5I^3J^87S0[P2P:P{fSS0\fRRSPOPcQ0APzPoPmPOPqQ0SQ0VO4O:S0Ab:b2b1b0PuPKPaPrP^P~P1PsQ0XQ0YPyP2n2001000000120000000VNVLVMV`X76X43X6IX5IX3JX87S0YQ0X\N\L\M\`^76^43^6I^5I^3J^87S0XQ0Ab:b2b1b0GHQ0LQ0U/2BS0UAJP2q16O5,Sb=EHx[^93RsQ0WQ0UPsPvPwP1Q0MQ0PA==tBS0M%>=9JP216059rT>=EHx[^93S0U'3PyP2n2001000000120000000VNVLVMV`X76X43X6IX5IX3JX87RtQ0P\N\L\M\`^76^43^6I^5I^3J^87RsP1Q0NQ0OQ0MPyP5n2001000000120000000VNVLVMV`X76X43X6IX5IX3JX87S0MQ0N\N\L\M\`^76^43^6I^5I^3J^87S0PP2P:PbPSP{POPcfHPoPpP]POPqQ0SQ0VO4O:Rqb2b1b0PvPwPtPsP1Q0NQ0OQ0UPyP2n2001000000120000000VNVLVMV`X76X43X6IX5IX3JX87RyQ0O\N\L\M\`^76^43^6I^5I^3J^87R7Pqb2b1b0GHFWQ0CQ0KAVoef%>fRq9Uoe%Df%?fRJ9ToeQ03#</Y[%CeR61BGJR`=IeBRM1K2`PH16e_,[bPGPJP5DG[^9\RJ'3PvPwQ0QQ0RP2P:PzP{PbPePfPlPpPmPnPePqPVPUPXPW%;eRl95Y|P8PZb<b=b>12DeR`P2b;P`eR`PVPUPXPWQ00#@RL#;RN,Ml=5Y}P8PZb<b=b>A=eLAP2b;1AeqRl/2AeR1O4O:b1b0ROPMPJPuPKPaPrP^P~Q0ZQ0[P2P:P{Q0\PSPePfQ0@PzPoPmPePqP`P1O4O:RJb:b2b1b0PuPKPaPrP^P~Q0YQ0XPJb:b2b1b0C:FdP612lBRlAJP2q16e5,Sb=EHx[^93R6POPlP6PvPwPtPsQ0MQ0PP2P:PbPSP{PePffDPoPpP]PePqP`P1O4O:R1b2b1b0PvPwPtPsPyP7P1b2b1b0GHQ0DQ0JAVogh%>hR19Uog%Dh%?hR`9TogQ04#<Q06Q05#</Y[3Q%CgRq1BG`Re=IgBRf1K2ePH16g_,[bPGP`P5DG[^9\R`'3PvPwQ0QQ0RP2P:PzP{PbPgPhPdPpPmPnPgP1PVPUPXPW%;gRd95Y|P8PZb<b=b>12DgReP2b;PeeRePVPUPXPWQ01#@R6#;,Md=5Y}P8PZb<b=b>A=g6AP2b;1Ag1R6/2AeRdO4O:b1b0RlPfP`PuPKPaPrP^P~Q0ZQ0[P2P:P{Q0\PSPgPhQ0?PzPoPmPgP1PePdO4O:R`b:b2b1b0PuPKPaPrP^P~Q0YQ0XP`b:b2b1b0C:FdPq126BR6AJP2116g5,Sb=EHx[^93RqPlP6PqPvPwPtPsQ0MQ0PP2P:PbPSP{PgPhf@PoPpP]PgP1PePdO4O:Rdb2b1b0PvPwPtPsPyP7Pdb2b1b0GHQ0EQ0IAVoQi%>iRd9UoQ%Di%?iRe9ToQQ07#</Y[%CQR11BGeRg=IQBRh1K2gPH16Q_,[bPGPeP5DG[^9\Re'3PvPwQ0QQ0RP2P:PzP{PbPQPiPRPpPmPnPQPdPVPUPXPW%;QRR95Y|P8PZb<b=b>12DQRgP2b;PgeRgPVPUPXPW1MRN=5Y}P8PZb<b=b>A=QLAP2b;1AQdRR/2AeRqO4O:b1b0R6PhPePuPKPaPrP^P~Q0ZQ0[P2P:P{Q0\PSPQPiQ02PzPoPmPQPdPgPqO4O:Reb:b2b1b0PuPKPaPrP^P~Q0YQ0XPeb:b2b1b0C:FdP112RBRRAJP2d16Q5,Sb=EHx[^93R1P6PRP1PvPwPtPsQ0MQ0PP2P:PbPSP{PQPiPTPoPpP]PQPdPgPqO4O:Rqb2b1b0PvPwPtPsPyP7Pqb2b1b0GHQ0FQ0HAVoC?%>?Rq9UoC%D?%??Rg9ToCQ08#<Q0;Q09#<RdQ0:1Yd[3Q3Q%CCRd1BGgRQ=ICBRT1K2QPH16C_,[bPGPgP5DG[^9\Rg'3PvPwQ0QQ0RP2P:PzP{PbPCP?P@PpPmPnPCPqPVPUPXPW%;CR@95Y|P8PZb<b=b>12DCRQP2b;PQeRQPVPUPXPWQ0T#@Ri#;,M@=5Y}P8PZb<b=b>A=CiAP2b;1ACqRi/2AeR@O4O:b1b0R1PTPgPuPKPaPrP^P~Q0ZQ0[P2P:P{Q0\PSPCP?P>PzPoPmPCPqPQP@O4O:R>b:b2b1b0PuPKPaPrP^P~Q0YQ0XP>b:b2b1b0C:FdPd12iBRiAJP2q16C5,Sb=EHx[^93RdP1PiPdPvPwPtPsQ0MQ0PP2P:PbPSP{PCP?P0PoPpP]PCPqPQP@O4O:R@b2b1b0PvPwPtPsPyP7P@b2b1b0GHQ0GQ0BAVojF%>FR@9Uoj%DF%?FRQ9TojQ0=#</Y[%CjRq1BGQRC=IjBR01K2CPH16j_,[bPGPQP5DG[^9\RQ'3PvPwQ0QQ0RP2P:PzP{PbPjPFP9PpPmPnPjP@PVPUPXPW%;jRC95Y|P8PZb<b=b>12DjR?P2b;P?eR?PVPUPXPWQ0<#;,MC=5Y}P8PZb<b=b>Q0<==jAP2b;1Aj@RC/2AeRdO4O:b1b0RiP0PQPuPKPaPrP^P~Q0ZQ0[P2P:P{Q0\PSPjPFP;PzPoPmPjP@P?PdO4O:R;b:b2b1b0PuPKPaPrP^P~Q0YQ0XP;b:b2b1b0C:FdPq12CBRCAJP2@16j5,Sb=EHx[^93RqPiPCPqPvPwPtPsQ0MQ0PP2P:PbPSP{PjPFP<PoPpP]PjP@P?PdO4O:Rdb2b1b0PvPwPtPsPyP7Pdb2b1b0GHAVokE%>ERd9Uok%DE%?ER?9TokQ0>#</Y[%CkR[1BG?R@=IkBRj1K2@PH16k_,[bPGP?P5DG[^9\R\PvPwQ0QQ0RP2P:PzP{PbPkPEP4PpPmPnPkPdPVPUPXPW%;kRn95Y|P8PZb<b=b>12DkRDP2b;PDeRDPVPUPXPW1MnN=5Y}P8PZb<b=b>A=kLAP2b;1AkdRL/2AeRAO4O:b1b0RZPjP\PuPKPaPrP^P~Q0ZQ0[P2P:P{Q0\PSPkPEP<PzPoPmPkPdPDPAO4O:Rmb:b2b1b0PuPKPaPrP^P~Q0YQ0XPmb:b2b1b0GHP[12LBRLAJP2d16k5,Sb=EHx[^93R3PZPLP3PvPwPtPsQ0MQ0PP2P:PbPSP{PkPEP9PoPpP]PkPdPDPAO4O:RAb2b1b0PvPwPtPsPyP7PAb2b1b0GHFWFWFWFWFWFWI0CWRWQP5P2O2n2001000010121000000W0WPP5P2O2n2001000010121000000W0WOP5P2O2n2011000010121000000W0WNP5P2O2n2011000010121000000W0WMP5P2O2n2011000010121000000W0WLP5P2O2n2111000010121000000&08=ebFWIWTWKWSW3X6IW5o"). Qed.
Lemma lt_pow2_of_log2 : forall a k, 0 <= a -> Z.log2 a < k -> a < 2 ^ k.
Proof.
ltac2:(KReplay.run1 (kr_t_F_aalloc ()) ["CANSEC1"] "p'0h04__x1h17__arithh24__ffh38__varmaph45__with54__x2h62Hah72Hlh81Hh94__p1h:1ah;1kh<1Gh=1Kh>1Lh?1ei001eh@1ni011nhA1ohB1si021sp;2p;1p;3p;4p;8p;6p;7g006kj20Tg00h3j12Tg00YWj21Tg00hQj2FTg00Z3j1:Tg00i1R0j2UTg001:j1NTg00EYj1ITg00K4j25Tg009>j1ETg003Bj1DTg00>7j1CTg00>Uj1`Tg00?3j1[Tg00ZLj2BTg00AHj2VTg00Ajj2TTg00BDj2QTg00C0j3=Tg00CJj3MTg00Cij4LTg00=;j2>Tg00?^j29Tg00@fj1HTg00iQj4GTg000\j8JTg00j9j1KTg00:^j1@Tg00;=j28Tg00;fj3?Tg00<Oj2OTg009^j3PTg00=Yj4;Tg00@Aj1RTg00j^j2STg007GR1j2_Tg00kCj3^Tg00kij2]Tg00lLj6ZTg00lhj6YTg00mLj2XTg00TEj4ATg00U0j7WTg00V8j8\Tg00ZoR2f0R3g00`9R43=p=<P2f1R5g00mkP3CAp=7P5g00[MR6g00[lR7P7g00\LR8P3g00]SFWp=3P2P5g00\lP3CAp=6f3R9P6P7P7P8f2R:P5P3G\p=41045R;%2:/151F94%<9R<%:<'UP0f4R0#<R<%:<f5R<g00`WR=#NR>#IR?/50'1P3%<<R@P2P41043RA%25f7RB'1f8RC,5?RD,1:]7]6X:21044%24f6RE'1P?PBg00c^RF#ERG%DFRH%C2RI%`2RJ%[2RK1B24RL1B2?'7'31VK8RMP3P:g00eURNg00f5RO'T1Q3:==NOdAM245CLROb2b3b4114?P3b1PGPH1>25RNPJPK192=RP,7L,3K%H7RQ16LP,3KRRC4PMPOb2b3b4X021143P;[^02P3PCP5O2b1CGW7W6PEP3P0P9GJW?P3O1%:@%KE%2E,04g00dJR@#@R9#@,821829182@5?25?2g00di'O=PFGPHP2PIP51>2:RFC;PJPK%R=,92R=,6L,3KPQPK17=P,3KPQPRC4C4PMPOb2b3b4X02X5211:5104:[\;^02^52P3%2CPBP5P<O4b1b8104<15?ERE,SB11BE10EB'_P115?BRB,1C10BCf9RB/1DRCP3P3X>CP3O110DBf:RD15?BRC'1P2%2Cf;R1#2,03X;2PGPHP2PFP5PIC;PJPK192>R>,6P,3KRPPQPPC4PMPOb2b3b4X02X521035105:[^02^52P3P115?DP5O3b19^CDPBPGPHPNPJPKPRPQPRC4PMPOb2b3b4X02P;\A^02P3PDP0O2b1,]BEZ%2D,0Bp-0RDPGPHP2PNP:PFC;PJPK16=>,3KPQPK17>=,3KPQPKP6P7P7P8P0EYC4C4PMPOb2b3b4X02X52W91053115:P0[[^02^52^9DP3g00nRP1f<#2P5PBO5b1b8'XW<P3O1n200100000021000011000bAb=W@P3O1n200110200021010011101bBW7W6X;2X:2o"). Qed.
Lemma hdr_b1_mid_range : forall b1, 0 <= b1 -> 0 <= hdr_b1_mid b1 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_F_aalloc ()) ["CANSEC1"] "h07__arithh11Hh24__ffh38__varmaph45__with54__x1h65heq_xh71ah81bh91zh:2L1h;4__p1h<4__p2h=4__p3h>4__x2h?4__x3h@4__x4hA2A0hB2H2hC2H3hD2HbhE2X0hF2b1hG1xhH2z2hI2z3p;1p;2p;3p;4p;6p;7p;8g00@Aj11Tg001:j15Tg00EYj19Tg00noj22Tg00oMj28Tg00GRR0j2ATg00ojj2]Tg007Gj2<Tg010Nj2XTg009>j1VTg003Bj1qTg00=;j2MTg00>Uj1nTg00?3j1gTg00ZLj2RTg00?^j2LTg00@fj1bTg00AHj2`Tg00Ajj2>Tg00BDj2_Tg00C0j3NTg00CJj3^Tg00Cij4\Tg0113j3[Tg00>7j1ZTg00D[j4PTg011Mj3WTg00YWj26Tg00h3j13Tg011gj2FTg012Dj4pTg012gj2ETg006kj27Tg000\j6UTg013Dj2oTg013fj2mTg00:^j1KTg00;=j2CTg00;fj3GTg00<Oj2TTg009^j3STg00=Yj4JTg00TEj4HTg00lLj6fTg014Hj4eTg014jj4dTg015mj1hTg00U0j7cTg00V8j8iTg016lj7jTg00lhj6kTg00UTj7lTg00`9R1f0R2'7p=0%12#1p=a%12#1#1#1#1#1#1#1p=;g00ZoR3f1R4g00\lP2CHp=@P4g00[MR5g00[lR6P6g00\LR7P2g00]SFcp=4f3R8P5P6P6P7f2R9P4P2Gip=B1R32p==%12#1#1#1p=YAN342p=?P9P5P6P6P7P4P2Fjp=DAN342,A9p=:P3P4g017PP2CHp=IP4P5P6P6P7P2Ekp=OP9P5P6P6P7P4P2Flp=Q%02R5g00`WR:#1R;#1R<#1#a#;#;#;#;#;#;#;#5#5#9R=,24%9:R>'8P3P01842#0%09R?%04R@'ARA[1A@51894#0[RB1889#0\A1]42P2n2001000000120000000X83X73RAPB^83^73RBP2128=RCP>%0C%0>RCP01242#01<?@R0[1<@51294#0[RD1289#0\01X42P2n2001000000120000000X83X73R0PD^83^73RDP2f4REP=%0E%0=g00c^RF#VRG%qFRH1M34RI%n3RJ%g3RK1R31RL1L3:RM'@,4KRN%b6R6PNCB1`K7R7P2P9g00eUROg00f5RP'>1_29=NOPdA^314C\R1b2b3b4X53RPP@\5^53ROP2f5RQPEO2b03[O3b1PGPH%Z3RRPJ%=>,@L,4KP7P1b2b3b4PCP2b0CPO3b1P5P0PDP2P9%5:R:#5RD#5R0#Y#9RC%0CRS12E=/8>RT,>31?9TRTeRUPTPGPHPRPJ%=C,@L,4KP7P1b2b3b4PSP2b0b6RS5W?O3b1124C#0129CR?%50RV#9RW'8RX#0%5V#5#5#5#9RV,6XPAPBP2128CPW12Q=/8>RB,>31?8BRBePBPGPHPIPJPKPNP6%=W,@L,4KRL9DKNCBP7P1b2b3b4X53%0WRN,A@\5^53P212QCR5P8O2b0b6O3b1R@PX%90RIP@P3%3?R@%3WRB'F162IX93P9PCP4PSCp%39%3CRS'E,7@1>3S%9<R</?SP3PS%35%3Q/E2'7X93P4P<P2EU12ECRQ#3%3E/E<'71>3B%9DRD/?BP3PDf7R5/2C#3RS/F2/6IX93f8R@/2=/8>R>,>3f6R=/?>R>eP>1oSD16SD1FSDR>;:D17DS?:>S'<12@C#3/FDP3f9#3R>/m<16><1E><RS;:>17<>?:S<'<f:#3/E<P3p-0RSg00dJR>#KRA#KRY#KRZ,C31C3Y1C3A1C3>5G35G35G3R>g00diRA'T%KZ,C3=G3>/TA=SFG5SFPHP3P3P31M3EPEPRCJPE1M38CJP4P31M39PEPRCJCJPJPKP31L30R0g00mkRF%=<RACH,4K%5;,L3R;/I0,4K5DK1OK=1I;A,4K5DK5QKP6PK1OK5%=D,IM,4K5DK1OK@%1:,L3R:,IM,4K5DK5QKP6PK1@:;,4KP6P3PMPF%=ICH,4KCBCBCBP7P1b2b3b4X53X>3X?3X@3X;SX<SW=168<?:98A:E9<'<A:=4DA:549'<178E168I[[[^53^>3^?3^@3^;S^<S^=SP2f<RS/2C#3RC,7D16CD%3SRS,7<PSP4PCP8P9PEP5O:b0bIbCbHbBb6PBP2Efb1b:b1b:%3XP?PWPUPTPPPOP2PQP9O2b0b6PUPTPGPHPRPJPLP7P1b2b3b4PNP2b0b6CeEUCdCPbAbEbG%h4R4#0164V'AeWDXF3o"). Qed.

(* [comment removed for export] *)
End CANSEC1.
Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Section CANSEC2. Context {rc : runConstT}.
Section WithDepot.
Variable DI : ADepotIface.

(* [comment removed for export] *)
Notation allocate_W L sp t c AB UB PG pgw n :=
  ([(bv_unsigned sp - 1152, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2792);
    (t + 2800, t + 3168); (UB - 16, UB + n); (AB, AB + 16);
    (shad UB, shad UB + shlen (n - n mod 8)); (PG, PG + pgw);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Definition allocate_post (L : alayout) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n t c cnt AB UB PG pgw lo b1 : Z) (maxc csz : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (sj' : list word) (stj' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (allocate_W L sp t c AB UB PG pgw n) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ 0 < id < 2^31
    (* [comment removed for export] *)
    /\ rw_cells asegs m' (t + 208 + c * 80) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz]
    /\ rw_cells asegs m' (t + 2784) [C8 stj']
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
    (* [comment removed for export] *)
    /\ rw_cells asegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 (Z.lor (Z.land (hdr_b1_mid b1) 243) 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
    /\ rw_cells asegs m' UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat n))]
    /\ (16 < rz_size n -> rw_cells asegs m' AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))])
    /\ rw_cells asegs m' (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))]
    /\ (n mod 8 <> 0 -> rw_cells asegs m' PG [C1 (Z_to_bv 8 (n mod 8))])
    /\ ADEPOT DI L m'.

Lemma allocate_fast_spec : forall (L : alayout) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (n S t c cnt spacebeg AB UB PG pgw lo b0 b1 szh szl ctxj sz pc : Z) (maxc csz stj idxw j1 j2 : word) (pj : byte)
    (chunks sj : list word) (sjunk uj : list byte) (tb : list word) (tr : list Z),
  let ctx := al_ctx L in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 1152 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 S -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 1 ->
  1 <= n <= 448 ->
  (* [comment removed for export] *)
  allocA_cells m ctx t -> poison_cells m ->
  rw_cells asegs m 0xb51cd [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xb51a4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells asegs m 0xb0380 [C8 (Z_to_bv 64 0x10)] -> rw_cells asegs m 0x5ea920 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0x149440 [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0xb4338 [C8 (Z_to_bv 64 spacebeg)] ->
  (* [comment removed for export] *)
  rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] -> rw_cells asegs m t [C8 (Z_to_bv 64 ctx)] ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> sclr ctx 65536 ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> sclr t 4096 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  (* [comment removed for export] *)
  Z.shiftr (needed_size n + 31) 5 = c ->
  rw_cells asegs m (t + 208 + c * 80) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (t + 208 + c * 80 + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (t + 2784) [C8 stj] ->
  0 <= spacebeg < 2^47 ->
  (* [comment removed for export] *)
  AB = spacebeg + c * 2^32 + 16 * bv_unsigned idxw ->
  UB = AB + rz_size n -> 0x10007fff8000 <= AB -> UB + (size_of_class (class_id (needed_size n)) - rz_size n) <= ATOP -> AB mod 16 = 0 ->
  needed_size n <= size_of_class (class_id (needed_size n)) <= 65536 ->
  PG = shad UB + shlen (n - n mod 8) -> pgw = (if n mod 8 =? 0 then 0 else 1) ->
  0x2008fff7000 <= shad AB -> shad AB + 2 <= shad UB -> 0 <= shlen (n - n mod 8) <= 56 -> PG + 1 <= 0x10007fff8000 ->
  rw_cells asegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)] ->
  0 <= b1 < 256 ->
  rw_cells asegs m UB [CB (Z.to_nat n) uj] ->
  (16 < rz_size n -> rw_cells asegs m AB [C8 j1; C8 j2]) ->
  rw_cells asegs m (shad AB) [C1 (Z_to_bv 8 0xfa)] ->
  rw_cells asegs m (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) sjunk] ->
  (n mod 8 <> 0 -> rw_cells asegs m PG [C1 pj]) ->
  (* [comment removed for export] *)
  (t + 4096 <= AB \/ AB + 65536 <= t) -> (ctx + 4096 <= AB \/ AB + 65536 <= ctx) ->
  (al_nodes L + 1048576 <= AB \/ AB + 65536 <= al_nodes L) -> (al_store L + 8388608 <= AB \/ AB + 65536 <= al_store L) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m S [C8 (Z_to_bv 64 (S + 16)); C8 (Z_to_bv 64 sz)] ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr asegs m (S + 16) tb -> length tb = 255%nat -> map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = pc :: tr ->
  In (pc :: tr) (al_U L) -> bv_unsigned sp <= S -> S + 2056 <= 2^47 ->
  ADEPOT DI L m ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S 2056 -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 ->
  rng RNG (UB - 16) (n + 16) -> rng RNG AB 16 -> rng RNG (shad AB) 1 -> rng RNG (shad UB) (shlen (n - n mod 8)) -> (n mod 8 <> 0 -> rng RNG PG 1) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L ->      (* [comment removed for export] *)
  evtF asegs RNG (allocate_post L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 allocate_entry) fc None m (seg_rom asegs)).
Proof.
  intros until tr. cbv zeta.
  intros ST CEIL LO MI TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 N AC PC PP FLG LS1 LS2 HK SB CT8 TT0 STATS LSJ CX0 CX1 CXS T0 T1 TAL TS CT2
         HC CR CH LCH CNT NTH IXS STS SBR HAB HUB ABLO UBHI AB16 NSZ HPG HPW SB1 SB2 SB3 SB4 HDR B1 UJ LH SHA SHU SHP
         DJT DJC DJN DJS DTN DTS DCN DCS N0 N1 R0 R1 SS SZ SZB TB LTB TRF TRU SPS S47 DEP
         RIMG RSTK RS RCTX RT RNO RST RU RAB RSA RSU RSP NI SI. band_lin.
 assert (PW01 : 0 <= pgw <= 1) by (rewrite HPW; destruct (n mod 8 =? 0); lia).
  pose proof (small_facts n N) as (PRIM & NS & RZR & RZE & RSR & RSM & NSR).
  assert (C16 : 1 <= c <= 16) by (rewrite <- HC; rewrite Z.shiftr_div_pow2 by lia; clear -NSR; Z.div_mod_to_equations; lia).
  pose proof AC as AC'. destruct AC' as (INI & RSS & IMAX & TI & TK & T88 & TSD & CT).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM in *.
  word_range sp SPR.
  box DJT. box DJC. box DJN. box DJS. box DTN. box DTS. box DCN. box DCS. box CT2.
  eapply evtF_cut.
  { eapply (allocA_spec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m n S (al_ctx L) t c cnt spacebeg lo maxc csz stj chunks idxw);
      try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
    all: try (with_box CT2 lia). all: try solve_rng. }
  cbv beta. intros ms1 PA. unfold allocA_post in PA. destruct_exs PA.
  destruct PA as (-> & MUa & WMa & MIa & STa & [fr0 FRa] & CRa & [stja STSa]).
  rewrite <- HAB.
  xport HDR MUa WMa ltac:(with_box DJT lia). xport SHA MUa WMa ltac:(with_band TS lia). xport SHU MUa WMa ltac:(with_band TS lia).
  xport PP MUa WMa ltac:(lia). xport CT8 MUa WMa ltac:(with_box CT2 lia). xport TT0 MUa WMa ltac:(lia).
  xport SS MUa WMa ltac:(lia). xport TB MUa WMa ltac:(rewrite LTB; lia).
  xport STATS MUa WMa ltac:(rewrite LSJ; lia). xport CT MUa WMa ltac:(with_box CT2 lia).
  xport UJ MUa WMa ltac:(with_box DJT lia).
  xport FLG MUa WMa ltac:(lia). xport LS1 MUa WMa ltac:(lia). xport LS2 MUa WMa ltac:(lia). xport HK MUa WMa ltac:(lia).
  xport TI MUa WMa ltac:(lia). xport TK MUa WMa ltac:(lia). xport T88 MUa WMa ltac:(lia). xport TSD MUa WMa ltac:(lia).
  assert (PC1 : poison_cells x13).
  { eapply poison_cells_frame_b; [exact PC | exact MUa | exact WMa |]. unfold AIMG_HI, AIMG_LO.
    repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
  assert (SHP1 : n mod 8 <> 0 -> rw_cells asegs x13 PG [C1 pj]).
  { intros NE. specialize (SHP NE). xport SHP MUa WMa ltac:(with_band TS lia). exact SHP. }
  assert (LH1 : 16 < rz_size n -> rw_cells asegs x13 AB [C8 j1; C8 j2]).
  { intros RZ. specialize (LH RZ). xport LH MUa WMa ltac:(with_box DJT lia). exact LH. }
  assert (DEP1 : ADEPOT DI L x13).
  { eapply (adi_frame DI); [exact DEP | exact MUa | exact WMa |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; pose proof DTN as X1; unbox X1; pose proof DTS as X2; unbox X2; lia|]).
    apply Forall_nil. }
  clear SHP LH PC DEP.
  eapply evtF_cut.
  { eapply (allocBC_spec DI L RNG sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc x13 n S t AB UB PG pgw lo b0 b1 szh szl ctxj sz pc pj sjunk tb tr fr0 _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STa
         | |- mem_inv _ _ => exact MIa
         | |- poison_cells _ => exact PC1
         | |- ADEPOT _ _ _ => exact DEP1
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ _ _ => exact TB
         | |- _ \/ _ => first [unboxed DJT | unboxed DJC | unboxed DJN | unboxed DJS]
         | |- rng _ _ _ => solve_rng
         | |- ~ _ -> _ => exact SHP1
         | |- _ -> rw_cells _ _ _ _ => exact LH1
         end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMBC" G end. }
  cbv beta. intros ms2 PB. unfold allocBC_post in PB. destruct_exs PB.
  destruct PB as (-> & MUb & WMb & MIb & STb & IDR & HDRb & SHUb & SHPb & DEPb).
  xport FRa MUb WMb ltac:(lia).
  xport STATS MUb WMb ltac:(ub DJT; ub DTN; ub DTS; with_band TS lia).
  xport TI MUb WMb ltac:(lia). xport TK MUb WMb ltac:(lia). xport T88 MUb WMb ltac:(lia). xport TSD MUb WMb ltac:(lia).
  xport CT MUb WMb ltac:(ub DJC; ub DCN; ub DCS; with_band CXS lia).
  xport FLG MUb WMb ltac:(lia). xport LS1 MUb WMb ltac:(lia). xport LS2 MUb WMb ltac:(lia). xport HK MUb WMb ltac:(lia).
  destruct PC1 as (GOT & GOT80 & REAL & PC4 & PC5 & PC6 & PC7).
  xport GOT MUb WMb ltac:(lia). xport GOT80 MUb WMb ltac:(lia). xport REAL MUb WMb ltac:(lia).
  xport UJ MUb WMb ltac:(ub DJN; ub DJS; lia).
  xport CRa MUb WMb ltac:(ub DJT; ub DTN; ub DTS; with_band TS lia). xport STSa MUb WMb ltac:(ub DJT; ub DTN; ub DTS; with_band TS lia).
  assert (LH2 : 16 < rz_size n -> rw_cells asegs x32 AB [C8 j1; C8 j2]).
  { intros RZ. specialize (LH1 RZ). pose proof (rz_size_small_cases n N) as RZC.
    xport LH1 MUb WMb ltac:(ub DJN; ub DJS; lia). exact LH1. }
  clear LH1 SHP1.
  pose proof (hdr_b1_mid_range b1 ltac:(lia)) as B1M.
  eapply evtF_mono.
  { eapply (allocD_spec L RNG sp gp tp F fc x32 n t c AB UB lo b0 (hdr_b1_mid b1) x14 S sj uj j1 j2 fr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STb
         | |- mem_inv _ _ => exact MIb
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ \/ _ => first [unboxed DJT | unboxed DJC | unboxed DJN | unboxed DJS]
         | |- rng _ _ _ => solve_rng
         | |- _ -> rw_cells _ _ _ _ => exact LH2
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + -16) _ => exact HDRb
         end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMD" G end. }
  cbv beta. intros ms3 PD. unfold allocD_post in PD. destruct_exs PD.
  destruct PD as (-> & MUd & WMd & MId & STd & STATSd & LSJd & UFd & HDRd & LHd).
  xport CRa MUd WMd ltac:(ub DJT; lia). xport STSa MUd WMd ltac:(ub DJT; lia).
  xport SHUb MUd WMd ltac:(with_band TS lia).
  assert (SHPd : n mod 8 <> 0 -> rw_cells asegs x47 PG [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPb NE). xport SHPb MUd WMd ltac:(with_band TS lia). exact SHPb. }
  assert (DEPd : ADEPOT DI L x47).
  { eapply (adi_frame DI); [exact DEPb | exact MUd | exact WMd |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha SPR S47 CEIL LO T0 T1 TAL NI SI N0 N1 R0 R1 HUB ABLO UBHI AB16 NSZ NS RZR RSR NSR HPG PW01 SB1 SB2 SB3 SB4 C16 LSJ N DTN DTS DJN DJS; ub DTN; ub DTS; ub DJN; ub DJS; lia | ub DTN; ub DTS; ub DJN; ub DJS; lia]|]). apply Forall_nil. }
  assert (MU : munch (allocate_W L sp t c AB UB PG pgw n) m x47).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUd]].
    eapply munch_trans; [| eapply munch_weaken; [| exact MUb]].
    eapply munch_weaken; [| exact MUa].
    all: first [clear -N C16 PW01; unfold sub_fp; cbn [outside]; intros q Hq; lia | unfold sub_fp; cbn [outside]; intros q Hq; lia]. }
  assert (WM : wmono asegs m x47).
  { eapply wmono_trans; [| exact WMd]. eapply wmono_trans; [exact WMa | exact WMb]. }
  unfold allocate_post. do 18 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MId|]. split; [exact STd|]. split; [exact IDR|].
  split; [exact CRa|]. split; [exact STSa|]. split; [exact STATSd|]. split; [exact LSJd|].
  split; [exact HDRd|]. split; [exact UFd|]. split; [exact LHd|]. split; [exact SHUb|]. split; [exact SHPd|]. exact DEPd.
  Unshelve. all: try exact STb.
Qed.
End WithDepot.
End CANSEC2.
(* [comment removed for export] *)
