(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import PropExec CatExec SeqExec StepTac.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ArgvEnv () := "C59OSSVerify5KrLib2AS7CatExec>valid_argv_lenC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib2AS7StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic4True00K46Stdlib9micromega=RingMicromega3Op205c59OSSVerify5KrLib2AS7ArgvEnv5argcNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7StepTac9bsb_boundC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAbuild_stack_bytesK47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z3addc59OSSVerify5KrLib2AS7ArgvEnv9sp_hi_numC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib2AS8PropExec6v_slliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec5v_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib2AS8PropExec8v_slli_3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec;v_add_smallC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedC47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib2AS7ArgvEnv7u_argcNC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7ArgvEnv9sp_lo_numC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00c59OSSVerify5KrLib2AS7ArgvEnv8envp_ptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExecDrdn_wrap_stack_aboveC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib2AS8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunAentry_stack_imageC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout<stack_to_memI47Corelib4Init9Datatypes3nat00c59OSSVerify5KrLib2AS7ArgvEnv4wmemC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase8word_le8K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib2AS8PropExec9read_argcC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses;rew_iff_revc59OSSVerify5KrLib2AS7ArgvEnv>rdn_wmem_stackC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2c59OSSVerify5KrLib2AS7ArgvEnv6bsb_nwC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC47Corelib4Init5Peano2ltC46Stdlib9micromega;ZifyClasses7rew_iffC59OSSVerify5KrLib2AS7SeqExec?argv_ptr_boundsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC59OSSVerify5KrLib2AS7SeqExecAargv_layout_slackC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3mulC47Corelib4Init3Nat3addC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib2AS7CatExec<cat_argv_ptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7CatExec?read_argv_ptr_kC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03C59OSSVerify5KrLib2AS7StepTac<word_add_natC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_add".
(* [comment removed for export] *)
Unset Lia Cache.

Import ListNotations.
Open Scope bv_scope.

Section Scaffold.

  (* [comment removed for export] *)
  Variable segs : list Segment.

  (* [comment removed for export] *)
  Variable ph : PhdrInfo.

  Variable sp : word.
  Variable av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.

  (* [comment removed for export] *)
  Variable rnd : EntryDraw.

  (* [comment removed for export] *)
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned sp)%Z.
  Hypothesis Hsp_hi : (bv_unsigned sp <= sp_window_hi)%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma sp_lo_num : (0x7fff80000000 <= bv_unsigned sp)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ArgvEnv ()) ["Scaffold"] "p,6Hsp_loo"). Qed.

  Lemma sp_hi_num : (bv_unsigned sp <= 0x800000000000)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ArgvEnv ()) ["Scaffold"] "p,6Hsp_hio"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition argcN : word := len_word av.

  Lemma u_argcN : bv_unsigned argcN = Z.of_nat (length av).
Proof.
ltac2:(KReplay.run1 (kr_t_ArgvEnv ()) ["Scaffold"] "h04__x1h12Hah27__arithh34__ffh48__varmaph55__with64cstrh71Hh86__sat0h96__sat1p;2p;1p;4p;3p;7p;8g0000j2STg000nj10Tg001Sj1:Tg0021j1?Tg002Tj1;Tg0034j2LTg003Tj1FTg0044j15Tg004Rj22Tg004nj1@Tg005Sj1=Tg0063j2<Tg006Qj1RTg006oj1QTg007Zj26Tg008=j2KTg008`j43Tg009Kj1ETg009mj2DTg00:Oj2CTg00:ij2BTg00;Uj39Tg00;oj3ATg00<Nj4GTg00=@j2HTg00=hj27Tg00>Dj2ITg00>aj3JTg00?Ej3>Tg00?hj3MTg00@^j2NTg00AHj7OTg00Alj8PTg00BPR0f0R1'2p=1f1R2g00BnR3g00CMR4P4g00CmR5P1g00DMFOp=4f3P3P4P4P5f2R3P2P1GPp=8p,2avR6p,3Hva'Sg00DmR7#0R8#0#0R9#:#?#;/L6R6#FR:%09#0#0R9#0#0#0#0#5R;'2%@6R6%1:R<g00ERR=g00F0R>#=R?%;>R>1<=2R@%R=RA%Q=RBP=16=0g00F\RC1K=7R7C3,4BRD%E4R4PDC81DB5R5P1P3g00GCRDg00GcRE'C1B13=9DEdAA=02CGREb3b4b5W0%11%12[^0=P1P:P2O2b2b6P6P<%58R8%59R<'H1708%1<1I8<R6,70[[%18R0g00HCRDAJ8<2UW1%16\D^10P?P>P@PAPBP=P7PC16=;C3,4BP4P=P7g00H_16=8%:9R95>=C3,4BC8P5PEb3b4b5X0=121;1726[^0=P1P:f4O2b2b8b9b65M:g00IF,N9=9=:eb7o"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma bsb_nw :
    (bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp av ev uid hw rnd)) < 2^64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ArgvEnv ()) ["Scaffold"] "h02Hah14__x1h24__x2h31Hh42H0h57__arithh64__ffh76__sat1h86__sat2h98__varmaph:5__with;4cstrp;9p;1p;7p;2p;3p;4p;8g00J;l9^Tg000nj10Tg001Sj1>Tg0021j1]Tg00K4j7PTg0034j2MTg003Tj1JTg00L:j13Tg0044j14Tg004Rj21Tg00@^j2@Tg004nj1\Tg00=@j2UTg00=hj2:Tg00>Dj2OTg00>aj3NTg00L_j1=Tg00M>j29Tg00Mgj3<Tg00NPj2LTg005Sj1ITg00O<j3HTg002Tj1ETg0063j2DTg00O\j1FTg00P:j4GTg006Qj1CTg006oj1KTg008=j2;Tg007Zj25Tg008`j46Tg009Kj1BTg00PXj3ATg00?Ej3QTg009mj2RTg00:Oj2STg00:ij2[Tg00;Uj3ZTg00;oj3YTg00<Nj4VTg00Q;j2WTg00AHj7XTg00Alj8TTf0R0#0#0p=7%00#0#0#0#0#0#0#0p=2f1R1g00BnR2g00CMR3P3g00CmR4P0g00DMFXp=8f3R5P2P3P3P4f2R2P1P0GTp=?p,2phR6p,2spR7p,2avR8p,2evR9p,3uidR:p,2hwR;p,3rndR<p,3Hvap,3HveM9^g00DmR=#0R>#7R?#>#]P6P7P8P9P:P;P<FP'MR<#JR;%3?#0#7#3#0#3#3#3#0#2#4R:'1g00QX%0?#7R?#>R9/@7R7%0?#2#2#2#2#2#4R8'1%\<g00BPR</1;%4>R6%4?R?'U1:<611<?1O6?R@,:<[[11<6RAg00HCRBAN6?1UW011<@\B^0Ag00ERRAg00F0RBg00RQR?#=RC#=,9A19AC19A?5<A5<Ag00S0'L%IB3H%EBPA1DA2P1%FACG%CA%KARBPA1;A=R=g00F\R?15A8C6,8B%B3R3PBPA1;A>R>P?15A:C6,8BP3PAAAA=>g00H_15A6=QA9C6,8BC?C?1RB4P0P2g00GCRBg00GcR4'S1[02=ZB4dAYA<1CVb6b9b:X1AW21108112:1W25/:@[[^1A^2AP0P;P7f4f5O4b5b7b8b;b4b3o"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition envp_ptr : word :=
    Z_to_bv 64 (bv_unsigned sp + 8 + 8 * Z.of_nat (length av) + 8).

  Lemma envp_ptr_eq :
    v_addi (v_add (Z_to_bv 64 (bv_unsigned sp + 8)) (v_slli argcN 3)) 8 = envp_ptr.
Proof.
ltac2:(KReplay.run1 (kr_t_ArgvEnv ()) ["Scaffold"] "h01zh14__x1h27__arithh34__ffh48__varmaph55__with64cstrh76__sat1h86__sat2h92Hah:4__x2h;2b1h<2b2h=1nh>1Hh?2H0h@2H1hA4Hlenp;1p;2p;3p;4p;6p;7p;8g000nj10Tg001Sj1OTg00@^j22Tg0044j18Tg004Rj23Tg00L:j1BTg0000j2[Tg0021j1<Tg002Tj1RTg0034j2sTg003Tj1pTg00;Uj3>Tg00S\j3lTg00Q;j21Tg00T@j2DTg00Tfj2bTg00U]j2aTg00VSj2`Tg00WJj2=Tg00X0j2?Tg00:Oj2NTg00>Dj2^Tg00=hj25Tg004nj1]Tg00=@j2\Tg00>aj3ZTg00XMj2YTg00L_j1LTg00M>j2ETg00Y6j3KTg00Mgj3HTg00NPj2JTg005Sj1XTg00O<j3STg0063j2WTg006Qj1rTg006oj1qTg008=j2UTg007Zj2;Tg009Kj1oTg00Y_j3TTg00?Ej3mTg009mj2kTg00:ij2jTg00;oj3gTg00<Nj4fTg00ZBj2eTg00PXj3PTg00?hj3dTg00O\j1cTg00P:j4hTg00[;j3iTg00\7j2QTg00\fj6VTg008`j4MTg00AHj7nTg00Alj8_Tf0R0#0#0p=G%00#0#0#0p=I%00#0#0#0#0#0#0#0p=:%B0#Bp=7g00ERR1f1R2;>0p=4P1f3R3f2R4P2P0g00]DEVp=CP1P2g00F\P0CMp=AP2g00BnR5g00CMR6P6g00CmR7P0g00DMFnp=6P1P2g00H_P0CMp=FP3P5P6P6P7P4P2P0G_p=@P1f4R5P3P4P2P0EVp=9g00QXg00DmR8#0R9#GR:#0#GR;#OR<p,2sp'2R=%I;R>#0#I#:#:#:#:#8R?'3g00^;%B8R@#7#7#7#7#7#7#7#0#G#I#:#:#:#8RA/3=p,2avRBp,3Hva'[%O:#<#R/sBRB#pRC%8>R>'3g00_4RD%<0RE%<2RFg00_R%<4?>2012341232'4RG[12421240'4%<3?>42[RH%<5?>34\GAl420P0n2001000000120000000W<W;W=PH^<F^;E^=DP0P<%8:R:,1=RD,D<REg00IFRF%8@'bR@'aRH/`:RGg00_mRI12<HRH/1:RJ,=<RK1?:C,1D/1:RL,D<,2<RM,40X011=<LRN14K0X0112<ERK12<@RO'1110:,=</4NX01PD110ORP/1:,=</4NX0112<FRQ,?:RR11D0RS/1:,=</4NX01PC1?:0RT,1DRU/1:,=</4NX011N1NPQCCPOPC%89RN%8;R;'^RV,5TX01%]BRBg00BPRT/3CRW1\N;RX15TN13T;15TV[[RY13TNRZg00HCR[AZN;2UW9R;13TV\[^9ZRZg00F0R[1Y1:R\g00RQR]#LR^,E1R_5K11E1]R]5H1g00S0R`'J%X[Ra3S%R[Rb1W12Rc%r1Rd%q1Re1U18R81;1>Rf'A,6e%o6R61;1:Rg=T181;1N=m1<RN'F,6eC@1ke7R7P0P4g00GCRhg00GcRi'N1j04=>hidAg1T2CfRib3b4b5X11130>1?:2/5V[^11P0PCf5RhO2b2b7b8b6PQCC,eFRFD9PKPBPWPaPbPcPdPe1;1A/A8,6eP61;1TAP18gRj'A,6eC@P7Pib3b4b5X1113A0112:RA,3T[^11P0P=P5O2b2b6PBPWPXPYP;PZPaPbPcPdPe1;1?,A8,6eR8P61FjN,6eC@P7Pib3b4b5X11130?15AV[^11P0P=f7RAO2b2b7b8b65dDRcD9PHPD15PVX01PR15SVX01PC15UVX01PBPWPXPYP;PZ%L^,E19K1\AH1_]5H1/J`=S[aPbP11W14P2%c1ChPdPe1U19R9/Af,6eP6PeP8P6AT1g99P1j/FN,6eC@C@P7Pib3b4b5X11X:1132>132?114:1?:3'1/5V[[^11^:1P0PCP=PhPAO4b2b7b8b6PQCCPOPFD9PKPcD99iE@D9PM1Q<LD91D<J,2<1Q<JD912<G12<I'4eO4b@bAb?b>o"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition wmem : word -> option byte := wrap_mem ph sp av ev uid hw rnd.

  (* [comment removed for export] *)
  Lemma rdn_wmem_stack : forall (a : word) n,
    (bv_unsigned sp <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
    rdn segs wmem a n
    = rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd)) a n.
Proof.
ltac2:(KReplay.run1 (kr_t_ArgvEnv ()) ["Scaffold"] "h02Hah12Hnh21ah31np;1p;2p;<p;4p;7p;3g000nj10Tg001Sj14Tg0021j12Tg00@^j21Tg004Rj26Tg003Tj1<Tg00Q;j2;Tg0044j13Tg00>Dj2:Tg00`el<9Tg002Tj17Tg00ajj18Tg00bLj45Tg00c@j7?Tg00d>j2>Tg00;Uj3=Tg00Dm#0R0#0#0R1#0#0#0R2#4R3#2g00e?p,2spR4,13f1R5,13'6f2R6,13%<5';%30%32':'6p,4segsR2p,2phR0P4p,2avR3p,2evR7f3R8P6p,3uidR9p,2hwR:p,3rndR;P5f0M<9%41#2#7#8P2g00e^P8P6C5P2P0P4P3P7P9P:P;F?,>4P8P6C53=eW1W0W3W2o"). Qed.

  (* [comment removed for export] *)
  Lemma read_argc_w :
    rdn segs wmem sp 8%nat = Some (word_le8 argcN).
Proof.
ltac2:(KReplay.run1 (kr_t_ArgvEnv ()) ["Scaffold"] "h04__x1h11xh22Hah37__arithh44__ffh58__varmaph65__with71Hh86__sat0h96__sat1h:1mh;1nh<1oh=1yp;1p;2p;7p;4p;3p;9p;<p;8p;6p;Bg000nj10Tg001Sj1;Tg00@^j2DTg0044j16Tg004RR0j21Tg0021j1HTg002Tj1:Tg00ajj1ETg00c@j7CTg00d>j2BTg00L_j12Tg00bLj4?Tg00fRj1bTg00gJj2YTg00;Uj3>Tg00gll9VTg005Sj1UTg0063j2TTg006Qj1STg006oj1QTg008=j2GTg009mj2FTg00:Oj23Tg00:ij2ITg00;oj3JTg00<Nj4KTg003TR1j1<Tg00Q;R2j25Tg00>Dj2LTg00hfj1MTg00iDj4NTg00igl<ATg00=@j2RTg00=hj2=Tg00>aj3dTg007Zj29Tg009Kj1cTg00PXj3aTg00?Ej3`Tg00Alj8]Tg00jLj4ZTg00k7j4[Tg00\fj6\Tg008`j4XTg00AHj7WTg00l5l<^Tg00lZlB_Tf0R3#0#0p=@%03#0#0#0#0#0#0#0p=4g00ERR4f1R5g00F\P3CXp=7P5g00BnR6g00CMR7P7g00CmR8P3g00DMFWp=8g00e?R9P4P4P4P1P1f5R1f4R:f3R;f2R<P5P3M<^p=OP4P4P4P4P4P4P2P3P5P<P2P;P:P1f6f7f8f9MB_p=Pg00QXg00DmR1#0R:#@R2#0#@R=#;R>p,2spR?'DR@%0=#4#4#4#4#4#6RA'1%;2#H#:RB#ERCp,4segsRDp,2phREP?p,2avRFp,2evRGp,3uidRHp,2hwRIp,3rndRJFC,B?P?g00RQ#2#2#2#2#2#2#2#2RKC?g00IF#b,YB9>C3X<CPEPDP?PFPGPHPIPJg00m@M9VPDg00e^P?PKC?P?PKg00F0R?#URD%:?R?1T45RJ%S4RI%Q4RH1G41R1/71'81FH8RGP3P<g00GCRFg00GcRE'31I3<=>FEdg00BPRE=J45CKRFb4b5b6X041133^04P3P@O1b3%<KR<,5@RC%6:R:%6=R='LRB'1%62R2,5@RL/1BP4P4P0P3X14RMP01153#MX=4X14PCPLPMPMPMP4P4g00n61553CN,34X:4X;4P@P@134@P<P2PMPM%<3,34X19PKP21342EOM:PPBPB134BM<A1R:=1=E:11E=1=EB[[11E:RKg00HCR9Ad:=5UW211EB\9^2KPDP?PJPIPHP6P7P7P8194A,71,8H%c719429a41194:=`4>'7,8HG]PGPFb4b5b6X04113A1552/1B[^04P3P@P;O2b3b8b9CZC[E\b7o"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma argv_ptr_bounds_at : forall k, (k < length av)%nat ->
    (bv_unsigned sp <= bv_unsigned (cat_argv_ptr sp av ev k))%Z /\
    (bv_unsigned (cat_argv_ptr sp av ev k)
       + Z.of_nat (length (nth k av [])) + 1 < 2^64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ArgvEnv ()) ["Scaffold"] "h02Hah14__x1h21Hh32Hkh43Hk0h57__arithh64__ffh76__sat1h86__sat2h98__varmaph:5__with;4cstrh<5cstr0h=1kp;1p;2p;4p;3p;8p;<p;7g000nj10Tg001Sj1;Tg0021j1DTg002Tj1@Tg0034j2UTg00nZR0j2<Tg00@^j2ITg0044j15Tg004Rj22Tg003TR1j18Tg00=hR2j23Tg00:Oj29Tg00o2j4VTg004nj1=Tg00=@j2TTg00>Dj2STg00>aj3OTg005Sj1NTg0063j2KTg006Qj1HTg006oj1GTg008=j2FTg007Zj27Tg008`j4:Tg009Kj1ETg00L:j11Tg00PXj3CTg00?Ej3LTg00Alj8MTg009mj2BTg00:ij2PTg00;Uj3QTg00;oj3ATg00<Nj4RTg00Q;j2>Tg00oYj8ZTg00igl<YTg00AHj7XTf0R3#0#0p=6%03#0#0#0#0#0#0#0p=4g00e?R4g00ERR5P0P1P2g010Xf5f4f3R2f2R1f1R0P3M<Yp=WP0g00BnR6g00CMR7P7g00CmR8P3g00DMFXp=?%03#0#0#0p=Jg00DmR9#0R:#6R;#;#D#@p,2avR<'UR=,<3p,2spR>P<p,2evP0p,3Hvap,3HveP3g00QX%6;R;#0R<#;R?/I>R>%0<#4#4#4#4#4#5R@'21<1=%81RA%8=RB'3RCP1PA195AP=PB195BEWP0CVPC%=2g00BPRC%82'2%==12CB%5:R:%5<R<'T13C:12C<1S:<RB,3C[[12C:R=g00HCR2AO:<0UW012CB\2^0=g00F0R=#N%@=1K50%H5%G5R=P6P7P7P8P51F59R9g00F\175@C:,?=%E7P5%1;#1#6#1#1#1#6#1#1#1#0#J#5R;,759C59g00H_175:=L5?C:,?=GM1B=8P3P1g00GCR=g00GcR8'91P31=Q=8dAA5C0CRb6b9b:X15123@1>0;/3B[^15P3P>f6O2b5b7b8b<b;b4g011:,>>/3Beb2GZW3X=4o"). Qed.

  (* [comment removed for export] *)
  Lemma read_argv_ptr_w : forall k, (k < length av)%nat ->
    rdn segs wmem (sp + nat_to_word (8 + 8 * k)) 8%nat
    = Some (word_le8 (cat_argv_ptr sp av ev k)).
Proof.
ltac2:(KReplay.run1 (kr_t_ArgvEnv ()) ["Scaffold"] "h04__x1h14__x2h23Hk0h37__arithh44__ffh58__varmaph65__with74__x3h84cstrh95cstr0h:1xh;2Hah<6__sat1h=6__sat2h>1bh?1yh@1zhA1HhB2H0hC3HalhD2HkhE1khF1mhG1nhH1op&0p;1p;2p;7p;3p;4p;;p;<p;6p;Bp;8g000nj11Tg001Sj1VTg0021j1STg002Tj1]Tg0034k204Tg00nZR0j2WTg00L:j1CTg0044j1=Tg00@^j2GTg004RR1j20Tg0000k207Tg003TR2j18Tg00ajk103Tg00c@j7}Tg00d>j2xTg00L_j16Tg012;j2sTg012Rj2oTg012ij1mTg013dj3jTg00bLj4XTg014Ij4hTg00fRj1fTg00gJj2eTg00;Uj3ZTg015El;bTg00Q;R3j22Tg00T@j2aTg00X0R4j2BTg00hfj1RTg00iDj4`Tg00=hR5j27Tg00o2k406Tg004nj1[Tg00M>j2ETg00Mgj3ATg00NPj2MTg016Dk202Tg005Sk101Tg00O<j3HTg0063j2YTg00O\j1|Tg00P:j4FTg006Qj1wTg006oj1vTg007Zj2>Tg008=j2KTg009Kj1rTg00Y_j3qTg00PXj3OTg009mj2nTg00:Oj2JTg00:ij2lTg00;oj3kTg00<Nj4pTg00jLj4@Tg00XMj2uTg00Y6j3TTg00>Dj2iTg00igl<DTg00=@j2gTg00>aj3yTg008`j4ITg00?Ej3zTg00?hj3{Tg00\fj6?Tg0170j2~Tg00k7k400Tg00lZlBLTg00l5l<dTg00AHj7cTg00Alk805Tf0R6#1#1p=N%C6#Cp=:%16#1#1#1p=P%16#1#1#1#1#1#1#1p=;g00ERR7/J6p=<g00e?R8P8P8P7P7P7g017lP2P2P2P4g018Lf5R4f4R9f3R:f2R;f1R<P6MBLp=_P8P8P8P7P7P7g018oP2P2P2P3g019OP4P9P:P;P<P6MBLp=^P8P7P7P7P2P2P4P9P:P;P<P6M<dp=QP7P7P7P7P7P7P3P6P<P;P3P:P9P4f6R3f7R=f8R>f9MBLp=UP7P7P1P=P1P3P4P9P:P;P<P6M<Dp=\P8P7P0P2P5g010XP4P9P:P;P<P6M<Dp>08g00BPR2/06p=3P7P<g00F\P6CIp=9P<g00BnR0g00CMR?P?g00CmR@P6g00DMFcp=5P:P0P?P?P@P;P<P6L05p=4P7P7P1P4P1P9P2P2P:P;P<P6M<Dp=tg00DmR1#1R0#NRA#V#S#]RBp,2avRC+04RD,W6g00^;%C1#:#:#:#:#:#:#:#1#N#P#;#;#;#=RE%1A#NRF#VRGp,2spRH'GRI'0g00QX%PFRJ#1#P#;#;#;#;#=RK,0Ip,3Hva-07C%8DRL%=JRJ'0&03BRMp,4segsRNp,2phROPHPCp,2evRPp,3uidRQp,2hwRRp,3rndRSF},xHg00RQRT#6RU#6RV#6RW#6#6#6#6#6RX1sX9RY'oRZ#m9jGHR[PXCXPHPCPPP4Ch#f,eB9ZM6XHMPOPNPHPCPPP9PQPRPSP:g00m@M;bPNg00e^P[PXCXP[PX%SGRN%8ZRS,2IRR,aGRQ1GG6RP,0IX>NP7PR10I6X@710IR%=ARA%89RC,BARO'2RM,2IRB,0IP6X:7R\10<6#RX?7X:7R]PIPI%<IR^PRPBP\P\P\P7P7g00n612<6C`#<XF7XG7R_PIPIP^PSPMP\P\%86#<X:8RSPZPMPXPA%<ARMPYPOPXPAPMP9PC%<CROE_E^EQM:URYG\1W9D17CLR^P9PCPOPDPL%<LJ08P:H06ROP^%[4RC%84#3R`%[DRD%3LRag00F0Rb1E7TRT1E7VRV9A7Tg00S0Rc'M+02&01bRd3H%]bReP71Y7;RfP<%|7RgCFRh%w7Ri%v7Rj1>72Rk1K70Rl'9,5jRm%r?R?1K71R11>7ARnAq7nl5O79O71Ro'9,5jC41nj@R@P6P;g00GCRpg00GcRq'J1l6;=ZpqdAk72<CpRqb4b5b6X07X17%3<Rp1BA;,2A,2<,0<[^07^17P6%8>R>PIP;O3b3b9b8b2C@1GGQRr%3R%3BP\P]1J72PRPBPYEtPOP^PCP`PDPa1u7ARs=T7V1E7U=A7T5A7RT/Mc=HbdPePhPiPjPmP?Pj1>7E/91,5jP?19ko,5jC4C4P@Pqb4b5b6X07X1710E<1BA:,2A,2;#3[\p^07^17P6P>PIP;P3O4b3b9b8b2C@%=0R>%=FRF'iRp,7R17BpP7P7P5P\P517<6#RX?7X:7PRPBPYPpPp%<pR5M<DPOP^PCP`PDPa1g>FRE172>%3F172p[[R2%3>Rkg00HCRmAy>F<UW;RF%3p\m^;kRk1E7W9T7s=A7T/Mc=HbdRdPeP7PfP<P71Y7:P:PgCFCFRgPiPjP7Plg00H_Rl%C0,K7R0CI,5jRfP?Pj1>7J,90,5jR0P?Pj1>7K,91,5jR1P?P7PoPl1>7>=z7GRGCI,5jC4C4C4P@Pqb4b5b6X07X17X7717<;R<10:JRJ10;KRK1BA9,2A,2:R:/7p[[[^07^17^77P6PLf:#8PIP4P3P=O6R=b3b<b=b9b8b2C@5{RR3E?P[1~HZRZE?PNPQ%8XRQ,2P/0pX>NP7PR126Q/0pX@712RQR6/0p12BARN/0pP\P]P6PNP\P\P\P_PRPBPYPQPAP\P\PSPXPAPMEQM:UPpPpP5G\POP^PCP`PDPaPEP2PFPkPdPePgPiPjPfP?PjP0P?PjP1P?AO7on/9G,5jC4C4C4P@Pqb4b5b6X07X17X7712:A/0p\K\J\<^07^17^77P=b3b<b=b9b8b2C@PrP3E?P[PZE?H00E?bCbBbAWDXE8o"). Qed.

End Scaffold.
