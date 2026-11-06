(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr FP FpBound FpReal FpSiteB FpSiteC ExpfModelB ExpfTablesB.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_deserkit Km_setelem Km_iface Km_kit KmF_kit Pm_gaps_iface Pm_iface Pm_iface2 Pm_iface4 Cf_iface Cf_kit CfX_kit RT_fk RT_fk_iface Bi_iface Bi_fktw Bi_fkkit Bi_fpkit Bi_pixakit Bi_addkit Bi_relkit Bi_restore Bi_lskit Bi_kmkit Bi_bgkit Bi_fpkit2 Bi_iface2 Bi_bcreate_defs Bi_bckit BiV_defs BiV_iface BiV_iface2 Bi_bcreate_ncloop Bi_bcreate_kfrloop LeptB_guard LeptB_guard2 LeptB_guard3 Bi_bcreate_rloop_defs D_iface D_defs.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_Bi_bcreate_sloop_defs () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z3mulC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC4ELinuxProcessSemantics5Riscv3Sem7nan_boxC4ELinuxProcessSemantics5Riscv3Sem7unbox_sC69OSSVerify5KrLib2K53Lib:ExpfModelB7bil_argC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega=RingMicromega5Psatz03K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv3Fpu9fp_of_intC4ELinuxProcessSemantics5Riscv3Fpu6fp_divC47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib2K53Lib7FpSiteCFfp_of_int_signed_smallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib2FP=unbox_nan_boxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib2FP8fcvt_s_wC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib2FP6fdiv_sC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC4ELinuxProcessSemantics5Riscv3Sem8sgnj_valK46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics5Riscv3Fpu:fmt_singleK4ELinuxProcessSemantics5Riscv3Fpu5rmode01K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics5Riscv3Fpu6fflags00K4ELinuxProcessSemantics5Riscv5Instr6fsgnop02K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib4Init9Datatypes4bool02C69OSSVerify5KrLib2K53Lib;ExpfTablesB;DEN_SPATIALC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00C69OSSVerify5KrLib2K53Lib:ExpfModelB2ESC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib2K53B02EBi_bcreate_rloop_defs8FS1_SPATC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma spat_arg : forall i, 0 <= i <= 10 ->
  fdiv_s RNE (nan_box (sgnj_val F_SGNJN (unbox_s (fcvt_s_w RNE (Z_to_bv 64 (i * i)))) (unbox_s (fcvt_s_w RNE (Z_to_bv 64 (i * i))))))
         (nan_box (Z_to_bv 32 DEN_SPATIAL))
  = nan_box (Z_to_bv 32 (bil_arg DEN_SPATIAL i)).
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_bcreate_sloop_defs ()) [] "h02Hah16__sat1h24__x1h31zh41bh57__arithh64__ffh76__sat0h88__varmaph95__with:1Eh;1Hh<2Hih=1ih>1pp&0p;1p;2p;3p;4p;5p;6p;7p;8g0000j10Tg000Uj11Tg001:j13Tg001Xj2\Tg0024j2GTg002Oj1STg002mj1bTg003Pj2LTg003mj2?Tg004Sj2<Tg005=j1DTg005gj1ITg006Qj2WTg007Oj2uTg0085j3@Tg008Oj2_Tg0097j2ATg009Sj2dTg00:0j3cTg00:Tj2kTg00;5j2KTg00;Oj1OTg00;nj2JTg00<Wj2NTg00=Cj2]Tg00=dj4gTg00>Ek208Tg00>nk106Tg00?Nj3MTg00?nk105Tg00@Nk204Tg00@lk102Tg00AJj1}Tg00B5j2YTg00BXj1|Tg00C:j5{Tg00C^j3aTg00DAj2zTg00Ddj3yTg00EGj4PTg00F2j2xTg00FTj2wTg00G@j3vTg00G_j4tTg00HQj1sTg00I:j3rTg00Ifj2qTg00JUj6=Tg00K3j2pTg00KSj5RTg00L?j4TTg00Lhj6oTg00MDj4nTg00NNj1XTg00OJj2mTg00PAj3lTg00Q6j3ZTg00QSj4fTg00R>j3~Tg00Rgk300Tg00SPk201Tg00T9j7jTg00T]j8iTg00UAk703Tg00UeR0f0R1'\p=5%01#0p=:g00VCR2g00W0R3g00WZR4f1R5P1DRp=Hg00X:R6g00XXR7;Z1,?5p=9f2R8g00YCR9P5P1Cfp=e1?51#Dp=Bf4R:f3R;P2P3P8P5CT9Z67'?#D;@1p=7P8P9P5P1Cf,<;p=6A~651p=2B00651p=>%01#0#0#0p=^%01#0#0#0#0#0#0#0p=h%01#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=420161p=F%11#1#1#1p>07%11#1p=[%11#1#1#1#1#1#1#1p=EP6P5g00Z0P1CPp=CP5g00ZWR9g00[6R<P<g00[VR=P1g00\6Fjp=8P;P9P<P<P=P8P5P1Gip=;P8P9P<P<P=P5P1K03p=VP2P3g00\VR>P5P1DRp=QAZ671p=UP2P3P1g00]6R?CTp=`%51g00^9R@#0RA#1#0RB#3RC,\1'G%0A#:RD#0RE#SRF#bRG%3ERH%0ERE#SRI1L55RJ,?IRK'<RL'H,9FRM#D#IRN=eFNRO%bIRPPF1<F1RQ1?F?RR#DRS#IRT,<FRU1W?8,BFRVD7X4GPGPMPPPFPFPFP1P1C6PUPVD7X4GPGPRPPPFPFPF1L88RU,?I,<IRW,HH,9FRXPXC6PQPVD7X4GP61uIJA@61UX36%3ARA%3ERG'_1A0ARQ%5G1dAGRX,A0[RY[%5ARZg00^^R[AcAG5UW0%5X\[RG^0ZP5g00_:1k0A'KPQeO1R\PYg00_`RYg00`LR]#OR^#OR_#O,J6R`1J6_R_/2_'21J6]R],2`R`'>g00`kRa'NRb%0B#^#h#4RB#0#4#4#3#FRcP6%3@,]6P@1]60Cg-0861J6^R^'2Rd'2&07@Re#1#[#E#ERf#1#E#E#E#E#:#1#[#3#F/2`%:E#^#4#4#4RE#:#4#4#4#4#3#F12_^R^'212_]R],2c'>'>'>/Na&06YRc5MY3M&05YR_20465Rg&026Rh%}6RiPi1Y60Rj1Y6ARk'C,8iRl%|<RmPiPiP9P<P<P=D{R<PmAa6kIR9,Cj,8iC;C;PmPi1z6@R@,Cj,8i1Y6C,C@,8i5ViRnPmAy6@@R@,Cj,8iRoP6P@g00aWRpP9CP,8i5ViC;C;1xi=R=P1P8g00b>R9/K41w18=@94dAv605CtR9b6b8b9X26PG\Z%551\5C'GRC%5URG1AUX'G[[^26P1f5RXP8P:O3b5b1b7b1%5J%sI,AJ'Ge9rIJPL1qIJE=A@6LJP6PUPPPFPFPF1HH1,9FRLPLC61<FRRL1W?;,BFRJD7X361p67R71QHURIPPPFPFPF19F1R4P4C6PLPJD7X>7P6PUPPPFPFPF1L;;,QH,9FR;P;C6R;PLg00b^R7P3PFPFP7P3P>PHP1DR,9FR>P>C6P?CT#U,BFD7X36%1D#:#1#:#1#0#:#4#3RD,K61?FD,<F9@6DdA@6?LRDePDP6P?PPPFPFPF1L::,QH,9FR:P:C6R:P1%`:#U,BFD7X36%`;#U,BF,KPPLP1Eob;PWP1E=PPPFPFPF19FIRIPIC6PLPVD7e1HHUP2P3PU%3eR2,_A%521dA2RH,A0[R0\QAcA25V[X0Z%5H\[R[^0ZP\P0%3B#FRB/2d%:f#1#[#3#F/2`%3E#F/2^12B]'>'>'>/Na=MYc9MYbP_PgPhPiPiPlPmPiP<Pm%Se9a6kRk,Cj,8iC;C;PmPiPnPmP6P@PpPkCP,8i9VioC;C;P=P9b6b8b9X26P[\Z1AUH,GG\C[^26P1f6P8PXO3b5b1b7b1CnE=PWP1E=b:PT%XRE=PN%XME=%DO#I%XOE=1m3K#IRK=eFK#D=l3S1W?5,BF5@PeW<X=6o"). Qed.
Lemma fs1_spat_box : nan_box (Z_to_bv 32 DEN_SPATIAL) = Z_to_bv 64 FS1_SPAT.
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_bcreate_sloop_defs ()) [] "p;1p;2p;3g0000j11Tg002Oj16Tg002mj17Tg000Uj10Tg001:j1;Tg00cWj2:Tg00dJj38Tg00;5j29Tg003mj25Tg005=j1>Tg0085j3=Tf0R0#1#1#1#1p=3%00#0p=<%00#0#0#0p=2%10#1p=4g00^9R0#1#3R1#1#6R2#7R3%00#<#2#2#2#2#2#2#2#1#0#3#0#4#0#4#0#1#4#3#3#3#3#;R01:20582'9%61g00]6'5#>g00dm,525=3do"). Qed.

Section SloopDefs.
Variable RT : rt_sig.
Definition bc_sloop_stmt : Prop :=
  forall (PMc : Model -> Prop) (QF : config -> Prop) (F : bvmap 5 word) (x2 : rts RT) (x4 m : mem) (usp lo spat : Z) (gp FS0V FS2V S9c S10c : word) (PL PF : Z -> Prop),
  fdfs_only PMc -> mat_stable PMc ->
  In (spat, 44) (rt_live RT x2) -> spat mod 16 = 0 ->
  (forall a, PF a -> a < spat \/ spat + 44 <= a) ->
  (spat + 44 <= 65536 \/ 6746112 <= spat) -> (spat + 44 <= 2147446784 \/ 17594333495296 <= spat) -> spat + 44 <= rt_sp0 RT x2 - 8388608 ->
  rt_sp0 RT x2 - 8388608 <= lo -> lo + LSTK 2 <= usp -> usp mod 32 = 0 -> usp + 16 <= USTACK_TOP -> usp <= rt_sp0 RT x2 -> 0 <= usp ->
  (forall a, PL a -> aclient (rt_live RT x2) (rt_frames RT x2) (usp - 352) a /\ outside [(spat, spat + 44)] a) ->
  (forall a, PF a -> aclient (rt_live RT x2) (rt_frames RT x2) usp a) ->
  forall (KONT : forall (Se : rts RT) (me : mem) (rae t0e t1e t2e a0e a1e a2e a3e a4e a5e a6e a7e t3e t4e t5e t6e : word) (Fe : bvmap 5 word) (fce : bv 32),
       fs_agree_but [8; 9; 18] F Fe -> reg_get Fe 8 = FS0V -> reg_get Fe 9 = Z_to_bv 64 FS1_SPAT -> reg_get Fe 18 = FS2V -> frm0 fce ->
       ART RT Se me -> mem_inv asegs me -> wmono asegs x4 me -> stk asegs me lo (usp + -352) -> LIBH me -> io_ssp me ->
       agree_on PL x4 me -> agree_on PF m me -> wr_at asegs me spat 44 -> u32arr asegs me spat (bil_words DEN_SPATIAL 11) ->
       rt_live RT Se = rt_live RT x2 -> rt_frames RT Se = rt_frames RT x2 -> rt_sp0 RT Se = rt_sp0 RT x2 -> rt_credit RT Se = rt_credit RT x2 ->
       cps asegs (ASTA RT Se PMc (eq (entry_st rae (Z_to_bv 64 (usp + -352)) gp (Z_to_bv 64 TP_A) t0e t1e t2e (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -352))
                    a0e a1e a2e a3e a4e a5e a6e a7e
                    (Z_to_bv 64 (spat + 44)) (Z_to_bv 64 2147450880) (Z_to_bv 64 11) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 (spat + 44))
                    S9c S10c (Z_to_bv 64 spat) t3e t4e t5e t6e Fe fce 0xcf4c4 me))) QF),
  forall k i, Z.to_nat (11 - i) = k -> 0 <= i < 11 ->
  forall (Si : rts RT) (mi : mem) (rai t0i t1i t2i a0i a1i a2i a3i a4i a5i a6i a7i t3i t4i t5i t6i : word) (Fi : bvmap 5 word) (fci : bv 32),
     fs_agree_but [8; 9; 18] F Fi -> reg_get Fi 8 = FS0V -> reg_get Fi 9 = Z_to_bv 64 FS1_SPAT -> reg_get Fi 18 = FS2V -> frm0 fci ->
     ART RT Si mi -> mem_inv asegs mi -> wmono asegs x4 mi -> stk asegs mi lo (usp + -352) -> LIBH mi -> io_ssp mi ->
     agree_on PL x4 mi -> agree_on PF m mi -> wr_at asegs mi spat 44 -> u32arr asegs mi spat (bil_words DEN_SPATIAL (Z.to_nat i)) ->
     rt_live RT Si = rt_live RT x2 -> rt_frames RT Si = rt_frames RT x2 -> rt_sp0 RT Si = rt_sp0 RT x2 -> rt_credit RT Si = rt_credit RT x2 ->
     cps asegs (ASTA RT Si PMc (eq (entry_st rai (Z_to_bv 64 (usp + -352)) gp (Z_to_bv 64 TP_A) t0i t1i t2i (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -352))
                  a0i a1i a2i a3i a4i a5i a6i a7i
                  (Z_to_bv 64 (spat + 4 * i)) (Z_to_bv 64 2147450880) (Z_to_bv 64 i) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 (11 - i)) (Z_to_bv 64 (spat + 4 * i))
                  S9c S10c (Z_to_bv 64 spat) t3i t4i t5i t6i Fi fci 0xcf454 mi))) QF.
End SloopDefs.
