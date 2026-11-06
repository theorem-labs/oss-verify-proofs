(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require NArith ZArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module ArgvEnv.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_ArgvEnv () := "C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List7existsbC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List:firstn_nilC59OSSVerify5KrLib7Mh_00387CatExec>valid_argv_lenC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib7Mh_00387StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic4True00K46Stdlib9micromega=RingMicromega3Op205c59OSSVerify5KrLib7Mh_00417ArgvEnv5argcNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StepTac9bsb_boundC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAbuild_stack_bytesK47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z3addc59OSSVerify5KrLib7Mh_00417ArgvEnv9sp_hi_numC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib8PropExec6v_slliC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C49OSSVerify5KrLib8PropExec8v_slli_3C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;v_add_smallC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedc59OSSVerify5KrLib7Mh_00417ArgvEnv7u_argcNC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00417ArgvEnv9sp_lo_numC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00c59OSSVerify5KrLib7Mh_00417ArgvEnv8envp_ptrC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecDrdn_wrap_stack_aboveC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunAentry_stack_imageC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout<stack_to_memI47Corelib4Init9Datatypes3nat00c59OSSVerify5KrLib7Mh_00417ArgvEnv4wmemC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase8word_le8K47Corelib4Init9Datatypes6option01C49OSSVerify5KrLib8PropExec9read_argcC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses;rew_iff_revc59OSSVerify5KrLib7Mh_00417ArgvEnv>rdn_wmem_stackC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2c59OSSVerify5KrLib7Mh_00417ArgvEnv6bsb_nwC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC47Corelib4Init5Peano2ltC46Stdlib9micromega;ZifyClasses7rew_iffC59OSSVerify5KrLib7Mh_00387SeqExec?argv_ptr_boundsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC59OSSVerify5KrLib7Mh_00387SeqExecAargv_layout_slackC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3mulC47Corelib4Init3Nat3addC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib7Mh_00387CatExec<cat_argv_ptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec?read_argv_ptr_kC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03C59OSSVerify5KrLib7Mh_00387StepTac<word_add_natC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_add".

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section Scaffold.

  (* [comment removed for export] *)
  Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)

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
ltac2:(KReplay.run1 (kr_t_ArgvEnv ()) ["Scaffold"] "h04__x1h12Hah27__arithh34__ffh48__varmaph55__with64cstrh71Hh86__sat0h96__sat1p;2p;1p;4p;3p;7p;8p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000dR1p4p710p8P0P1p4p7210p8P0p1001Ap4p710p8p1001]p4p710R0p1002:p4p710p8P0p1002Vp4p710R0p8p10034p4p710P0p8g003Sj2STg004Vj10Tg005;j1:Tg005Yj1?Tg006<j1;Tg006\j2LTg007<j1FTg007\j15Tg008:j22Tg008Vj1@Tg009;j1=Tg009[j2<Tg00:9j1RTg00:Wj1QTg00;Bj26Tg00;ej2KTg00<Hj43Tg00=3j1ETg00=Uj2DTg00>7j2CTg00>Qj2BTg00?=j39Tg00?Wj3ATg00@6j4GTg00@hj2HTg00APj27Tg00Alj2ITg00BIj3JTg00Bmj3>Tg00CPj3MTg00DKj2NTg00E5j7OTg00EYj8PTg00F=R0f0R1'2p=1f1R2g00F[R3g00G:R4P4g00GZR5P1g00H:FOp=4f3P3P4P4P5f2R3P2P1GPp=8p,2avR6p,3Hva'Sg00HZR7#0R8#0#0R9#:#?#;/L6R6#FR:%09#0#0R9#0#0#0#0#5R;'2%@6R6%1:R<g00I?R=g00I]R>#=R?%;>R>1<=2R@%R=RA%Q=RBP=16=0g00JIRC1K=7R7C3,4BRD%E4R4PDC81DB5R5P1P3g00K0RDg00KPRE'C1B13=9DEdAA=02CGREb3b4b5W0%11%12[^0=P1P:P2O2b2b6P6P<%58R8%59R<'H1708%1<1I8<R6,70[[%18R0g00L0RDAJ8<2UW1%16\D^10P?P>P@PAPBP=P7PC16=;C3,4BP4P=P7g00LL16=8%:9R95>=C3,4BC8P5PEb3b4b5X0=121;1726[^0=P1P:f4O2b2b8b9b65M:g00M3,N9=9=:eb7o"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma bsb_nw :
    (bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp av ev uid hw rnd)) < 2^64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_ArgvEnv ()) ["Scaffold"] "h02Hah14__x1h24__x2h31Hh42H0h57__arithh64__ffh76__sat1h86__sat2h98__varmaph:5__with;4cstrp;9p;1p;7p;2p;3p;4p;8p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000dR1p4p710p8P0P1p4p7210p8P0p1001Ap4p710p8p1001]p4p710R0p1002:p4p710p8P0p1002Vp4p710R0p8p10034p4p710P0p8g00Mml9^Tg004Vj10Tg005;j1>Tg005Yj1]Tg00Nkj7PTg006\j2MTg007<j1JTg00P1j13Tg007\j14Tg008:j21Tg00DKj2@Tg008Vj1\Tg00@hj2UTg00APj2:Tg00Alj2OTg00BIj3NTg00PVj1=Tg00Q5j29Tg00Q^j3<Tg00RGj2LTg009;j1ITg00S3j3HTg006<j1ETg009[j2DTg00SSj1FTg00T1j4GTg00:9j1CTg00:Wj1KTg00;ej2;Tg00;Bj25Tg00<Hj46Tg00=3j1BTg00TOj3ATg00Bmj3QTg00=Uj2RTg00>7j2STg00>Qj2[Tg00?=j3ZTg00?Wj3YTg00@6j4VTg00U2j2WTg00E5j7XTg00EYj8TTf0R0#0#0p=7%00#0#0#0#0#0#0#0p=2f1R1g00F[R2g00G:R3P3g00GZR4P0g00H:FXp=8f3R5P2P3P3P4f2R2P1P0GTp=?p,2phR6p,2spR7p,2avR8p,2evR9p,3uidR:p,2hwR;p,3rndR<p,3Hvap,3HveM9^g00HZR=#0R>#7R?#>#]P6P7P8P9P:P;P<FP'MR<#JR;%3?#0#7#3#0#3#3#3#0#2#4R:'1g00UO%0?#7R?#>R9/@7R7%0?#2#2#2#2#2#4R8'1%\<g00F=R</1;%4>R6%4?R?'U1:<611<?1O6?R@,:<[[11<6RAg00L0RBAN6?1UW011<@\B^0Ag00I?RAg00I]RBg00VMR?#=RC#=,9A19AC19A?5<A5<Ag00Vl'L%IB3H%EBPA1DA2P1%FACG%CA%KARBPA1;A=R=g00JIR?15A8C6,8B%B3R3PBPA1;A>R>P?15A:C6,8BP3PAAAA=>g00LL15A6=QA9C6,8BC?C?1RB4P0P2g00K0RBg00KPR4'S1[02=ZB4dAYA<1CVb6b9b:X1AW21108112:1W25/:@[[^1A^2AP0P;P7f4f5O4b5b7b8b;b4b3o"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition envp_ptr : word :=
    Z_to_bv 64 (bv_unsigned sp + 8 + 8 * Z.of_nat (length av) + 8).

  Lemma envp_ptr_eq :
    v_addi (v_add (Z_to_bv 64 (bv_unsigned sp + 8)) (v_slli argcN 3)) 8 = envp_ptr.
Proof.
ltac2:(KReplay.run1 (kr_t_ArgvEnv ()) ["Scaffold"] "h01zh14__x1h27__arithh34__ffh48__varmaph55__with64cstrh76__sat1h86__sat2h92Hah:4__x2h;2b1h<2b2h=1nh>1Hh?2H0h@2H1hA4Hlenp;1p;2p;3p;4p;6p;7p;8p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000dR1p4p710p8P0P1p4p7210p8P0p1001Ap4p710p8p1001]p4p710R0p1002:p4p710p8P0g002VR0p4p710R1p8p10034p4p710P1p8g004Vj10Tg005;j1OTg00DKj22Tg007\j18Tg008:j23Tg00P1j1BTg003Sj2[Tg005Yj1<Tg006<j1RTg006\j2sTg007<j1pTg00?=j3>Tg00WXj3lTg00U2j21Tg00X<j2DTg00Xbj2bTg00YVj2aTg00ZIj2`Tg00[=j2=Tg00[cj2?Tg00>7j2NTg00Alj2^Tg00APj25Tg008Vj1]Tg00@hj2\Tg00BIj3ZTg00\@j2YTg00PVj1LTg00Q5j2ETg00\ij3KTg00Q^j3HTg00RGj2JTg009;j1XTg00S3j3STg009[j2WTg00:9j1rTg00:Wj1qTg00;ej2UTg00;Bj2;Tg00=3j1oTg00]Rj3TTg00Bmj3mTg00=Uj2kTg00>Qj2jTg00?Wj3gTg00@6j4fTg00^5j2eTg00TOj3PTg00CPj3dTg00SSj1cTg00T1j4hTg00^kj3iTg00_dj2QTP0j6VTg00<Hj4MTg00E5j7nTg00EYj8_Tf0R0#0#0p=G%00#0#0#0p=I%00#0#0#0#0#0#0#0p=:%B0#Bp=7g00I?R1f1R2;>0p=4P1f3R3f2R4P2P0g00`SEVp=CP1P2g00JIP0CMp=AP2g00F[R5g00G:R6P6g00GZR7P0g00H:Fnp=6P1P2g00LLP0CMp=FP3P5P6P6P7P4P2P0G_p=@P1f4R5P3P4P2P0EVp=9g00UOg00HZR8#0R9#GR:#0#GR;#OR<p,2sp'2R=%I;R>#0#I#:#:#:#:#8R?'3g00aO%B8R@#7#7#7#7#7#7#7#0#G#I#:#:#:#8RA/3=p,2avRBp,3Hva'[%O:#<#R/sBRB#pRC%8>R>'3g00bMRD%<0RE%<2RFg00bk%<4?>2012341232'4RG[12421240'4%<3?>42[RH%<5?>34\GAl420P0n2001000000120000000W<W;W=PH^<F^;E^=DP0P<%8:R:,1=RD,D<REg00M3RF%8@'bR@'aRH/`:RGg00cFRI12<HRH/1:RJ,=<RK1?:C,1D/1:RL,D<,2<RM,40X011=<LRN14K0X0112<ERK12<@RO'1110:,=</4NX01PD110ORP/1:,=</4NX0112<FRQ,?:RR11D0RS/1:,=</4NX01PC1?:0RT,1DRU/1:,=</4NX011N1NPQCCPOPC%89RN%8;R;'^RV,5TX01%]BRBg00F=RT/3CRW1\N;RX15TN13T;15TV[[RY13TNRZg00L0R[AZN;2UW9R;13TV\[^9ZRZg00I]R[1Y1:R\g00VMR]#LR^,E1R_5K11E1]R]5H1g00VlR`'J%X[Ra3S%R[Rb1W12Rc%r1Rd%q1Re1U18R81;1>Rf'A,6e%o6R61;1:Rg=T181;1N=m1<RN'F,6eC@1ke7R7P0P4g00K0Rhg00KPRi'N1j04=>hidAg1T2CfRib3b4b5X11130>1?:2/5V[^11P0PCf5RhO2b2b7b8b6PQCC,eFRFD9PKPBPWPaPbPcPdPe1;1A/A8,6eP61;1TAP18gRj'A,6eC@P7Pib3b4b5X1113A0112:RA,3T[^11P0P=P5O2b2b6PBPWPXPYP;PZPaPbPcPdPe1;1?,A8,6eR8P61FjN,6eC@P7Pib3b4b5X11130?15AV[^11P0P=f7RAO2b2b7b8b65dDRcD9PHPD15PVX01PR15SVX01PC15UVX01PBPWPXPYP;PZ%L^,E19K1\AH1_]5H1/J`=S[aPbP11W14P2%c1ChPdPe1U19R9/Af,6eP6PeP8P6AT1g99P1j/FN,6eC@C@P7Pib3b4b5X11X:1132>132?114:1?:3'1/5V[[^11^:1P0PCP=PhPAO4b2b7b8b6PQCCPOPFD9PKPcD99iE@D9PM1Q<LD91D<J,2<1Q<JD912<G12<I'4eO4b@bAb?b>o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_ArgvEnv ()) ["Scaffold"] "h02Hah12Hnh21ah31np;1p;2p;<p;4p;7p;3p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000dR1p4p710p8P0P1p4p7210p8P0p1001Ap4p710p8p1001]p4p710R0p1002:p4p710p8P0p1002Vp4p710R0p8p10034p4p710P0p8g004Vj10Tg005;j14Tg005Yj12Tg00DKj21Tg008:j26Tg007<j1<Tg00U2j2;Tg007\j13Tg00Alj2:Tg00dCl<9Tg006<j17Tg00eEj18Tg00egj45Tg00fXj7?Tg00gVj2>Tg00?=j3=Tg00HZ#0R0#0#0R1#0#0#0R2#4R3#2g00hWp,2spR4,13f1R5,13'6f2R6,13%<5';%30%32':'6p,4segsR2p,2phR0P4p,2avR3p,2evR7f3R8P6p,3uidR9p,2hwR:p,3rndR;P5f0M<9%41#2#7#8P2g00i6P8P6C5P2P0P4P3P7P9P:P;F?,>4P8P6C53=eW1W0W3W2o"). Qed.

  (* [comment removed for export] *)
  Lemma read_argc_w :
    rdn segs wmem sp 8%nat = Some (word_le8 argcN).
Proof.
ltac2:(KReplay.run1 (kr_t_ArgvEnv ()) ["Scaffold"] "h04__x1h11xh22Hah37__arithh44__ffh58__varmaph65__with71Hh86__sat0h96__sat1h:1mh;1nh<1oh=1yp;1p;2p;7p;4p;3p;9p;<p;8p;6p;Bp-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000dR1p4p710p8P0P1p4p7210p8P0p1001Ap4p710p8p1001]p4p710R0p1002:p4p710p8P0g002VR0p4p710R1p8p10034p4p710P1p8g004Vj10Tg005;j1;Tg00DKj2DTg007\j16Tg008:R1j21Tg005Yj1HTg006<j1:Tg00eEj1ETg00fXj7CTg00gVj2BTg00PVj12Tg00egj4?Tg00ioj1bTg00jgj2YTg00?=j3>Tg00kIl9VTg009;j1UTg009[j2TTg00:9j1STg00:Wj1QTg00;ej2GTg00=Uj2FTg00>7j23Tg00>Qj2ITg00?Wj3JTg00@6j4KTg007<R2j1<Tg00U2R3j25Tg00Alj2LTg00l@j1MTg00l^j4NTg00mAl<ATg00@hj2RTg00APj2=Tg00BIj3dTg00;Bj29Tg00=3j1cTg00TOj3aTg00Bmj3`Tg00EYj8]Tg00mfj4ZTg00nQj4[TP0j6\Tg00<Hj4XTg00E5j7WTg00oTl<^Tg0109lB_Tf0R0#0#0p=@%00#0#0#0#0#0#0#0p=4g00I?R4f1R5g00JIP0CXp=7P5g00F[R6g00G:R7P7g00GZR8P0g00H:FWp=8g00hWR9P4P4P4P2P2f5R2f4R:f3R;f2R<P5P0M<^p=OP4P4P4P4P4P4P3P0P5P<P3P;P:P2f6f7f8f9MB_p=Pg00UOg00HZR2#0R:#@R3#0#@R=#;R>p,2spR?'DR@%0=#4#4#4#4#4#6RA'1%;3#H#:RB#ERCp,4segsRDp,2phREP?p,2avRFp,2evRGp,3uidRHp,2hwRIp,3rndRJFC,B?P?g00VM#2#2#2#2#2#2#2#2RKC?g00M3#b,YB9>C0X<CPEPDP?PFPGPHPIPJg010_M9VPDg00i6P?PKC?P?PKg00I]R?#URD%:?R?1T45RJ%S4RI%Q4RH1G42R2/72'81FH8RGP0P<g00K0RFg00KPRE'31I0<=>FEdg00F=RE=J45CKRFb4b5b6X041100^04P0P@O1b3%<KR<,5@RC%6:R:%6=R='LRB'1%63R3,5@RL/1BP4P4P1P0X14RMP11150#MX=4X14PCPLPMPMPMP4P4g011Z1550CN,34X:4X;4P@P@134@P<P3PMPM%<0,34X19PKP31343EOM:PPBPB134BM<A1R:=1=E:11E=1=EB[[11E:RKg00L0R9Ad:=5UW211EB\9^2KPDP?PJPIPHP6P7P7P8194A,72,8H%c719439a42194:=`4>'7,8HG]PGPFb4b5b6X04110A1553/1B[^04P0P@P;O2b3b8b9CZC[E\b7o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_ArgvEnv ()) ["Scaffold"] "h02Hah14__x1h21Hh32Hkh43Hk0h57__arithh64__ffh76__sat1h86__sat2h98__varmaph:5__with;4cstrh<5cstr0h=1kp;1p;2p;4p;3p;8p;<p;7p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000dR1p4p710p8P0P1p4p7210p8P0p1001Ap4p710p8p1001]p4p710R0p1002:p4p710p8P0p1002Vp4p710R0p8p10034p4p710P0p8g004Vj10Tg005;j1;Tg005Yj1DTg006<j1@Tg006\j2UTg012>R0j2<Tg00DKj2ITg007\j15Tg008:j22Tg007<R1j18Tg00APR2j23Tg00>7j29Tg012Vj4VTg008Vj1=Tg00@hj2TTg00Alj2STg00BIj3OTg009;j1NTg009[j2KTg00:9j1HTg00:Wj1GTg00;ej2FTg00;Bj27Tg00<Hj4:Tg00=3j1ETg00P1j11Tg00TOj3CTg00Bmj3LTg00EYj8MTg00=Uj2BTg00>Qj2PTg00?=j3QTg00?Wj3ATg00@6j4RTg00U2j2>Tg013=j8ZTg00mAl<YTg00E5j7XTf0R3#0#0p=6%03#0#0#0#0#0#0#0p=4g00hWR4g00I?R5P0P1P2g014Af5f4f3R2f2R1f1R0P3M<Yp=WP0g00F[R6g00G:R7P7g00GZR8P3g00H:FXp=?%03#0#0#0p=Jg00HZR9#0R:#6R;#;#D#@p,2avR<'UR=,<3p,2spR>P<p,2evP0p,3Hvap,3HveP3g00UO%6;R;#0R<#;R?/I>R>%0<#4#4#4#4#4#5R@'21<1=%81RA%8=RB'3RCP1PA195AP=PB195BEWP0CVPC%=2g00F=RC%82'2%==12CB%5:R:%5<R<'T13C:12C<1S:<RB,3C[[12C:R=g00L0R2AO:<0UW012CB\2^0=g00I]R=#N%@=1K50%H5%G5R=P6P7P7P8P51F59R9g00JI175@C:,?=%E7P5%1;#1#6#1#1#1#6#1#1#1#0#J#5R;,759C59g00LL175:=L5?C:,?=GM1B=8P3P1g00K0R=g00KPR8'91P31=Q=8dAA5C0CRb6b9b:X15123@1>0;/3B[^15P3P>f6O2b5b7b8b<b;b4g014c,>>/3Beb2GZW3X=4o"). Qed.

  (* [comment removed for export] *)
  Lemma read_argv_ptr_w : forall k, (k < length av)%nat ->
    rdn segs wmem (sp + nat_to_word (8 + 8 * k)) 8%nat
    = Some (word_le8 (cat_argv_ptr sp av ev k)).
Proof.
ltac2:(KReplay.run1 (kr_t_ArgvEnv ()) ["Scaffold"] "h04__x1h14__x2h23Hk0h37__arithh44__ffh58__varmaph65__with74__x3h84cstrh95cstr0h:1xh;2Hah<6__sat1h=6__sat2h>1bh?1yh@1zhA1HhB2H0hC3HalhD2HkhE1khF1mhG1nhH1op&0p;1p;2p;7p;3p;4p;;p;<p;6p;Bp;8p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000dR1p4p710p8P0P1p4p7210p8P0p1001Ap4p710p8p1001]p4p710R0p1002:p4p710p8P0g002VR0p4p710R1p8p10034p4p710P1p8g004Vj11Tg005;j1VTg005Yj1STg006<j1]Tg006\k204Tg012>R1j2WTg00P1j1CTg007\j1=Tg00DKj2GTg008:R2j20Tg003Sk207Tg007<R3j18Tg00eEk103Tg00fXj7}Tg00gVj2xTg00PVj16Tg015ij2sTg016@j2oTg016Wj1mTg017Rj3jTg00egj4XTg0187j4hTg00ioj1fTg00jgj2eTg00?=j3ZTg0198l;bTg00U2R4j22Tg00X<j2aTg00[cR5j2BTg00l@j1RTg00l^j4`Tg00APR6j27Tg012Vk406Tg008Vj1[Tg00Q5j2ETg00Q^j3ATg00RGj2MTg01:<k202Tg009;k101Tg00S3j3HTg009[j2YTg00SSj1|Tg00T1j4FTg00:9j1wTg00:Wj1vTg00;Bj2>Tg00;ej2KTg00=3j1rTg00]Rj3qTg00TOj3OTg00=Uj2nTg00>7j2JTg00>Qj2lTg00?Wj3kTg00@6j4pTg00mfj4@Tg00\@j2uTg00\ij3TTg00Alj2iTg00mAl<DTg00@hj2gTg00BIj3yTg00<Hj4ITg00Bmj3zTg00CPj3{TP0j6?Tg01:hj2~Tg00nQk400Tg0109lBLTg00oTl<dTg00E5j7cTg00EYk805Tf0R0#1#1p=N%C0#Cp=:%10#1#1#1p=P%10#1#1#1#1#1#1#1p=;g00I?R7/J0p=<g00hWR8P8P8P7P7P7g01;iP3P3P3P5g01<If5R5f4R9f3R:f2R;f1R<P0MBLp=_P8P8P8P7P7P7g01<lP3P3P3P4g01=LP5P9P:P;P<P0MBLp=^P8P7P7P7P3P3P5P9P:P;P<P0M<dp=QP7P7P7P7P7P7P4P0P<P;P4P:P9P5f6R4f7R=f8R>f9MBLp=UP7P7P2P=P2P4P5P9P:P;P<P0M<Dp=\P8P7P1P3P6g014AP5P9P:P;P<P0M<Dp>08g00F=R3/00p=3P7P<g00JIP0CIp=9P<g00F[R1g00G:R?P?g00GZR@P0g00H:Fcp=5P:P1P?P?P@P;P<P0L05p=4P7P7P2P5P2P9P3P3P:P;P<P0M<Dp=tg00HZR2#1R1#NRA#V#S#]RBp,2avRC+04RD,W0g00aO%C2#:#:#:#:#:#:#:#1#N#P#;#;#;#=RE%1A#NRF#VRGp,2spRH'GRI'0g00UO%PFRJ#1#P#;#;#;#;#=RK,0Ip,3Hva-07C%8DRL%=JRJ'0&03BRMp,4segsRNp,2phROPHPCp,2evRPp,3uidRQp,2hwRRp,3rndRSF},xHg00VMRT#6RU#6RV#6RW#6#6#6#6#6RX1sX9RY'oRZ#m9jGHR[PXCXPHPCPPP5Ch#f,eB9ZM0XHMPOPNPHPCPPP9PQPRPSP:g010_M;bPNg00i6P[PXCXP[PX%SGRN%8ZRS,2IRR,aGRQ1GG0RP,0IX>NP7PR10I0X@710IR%=ARA%89RC,BARO'2RM,2IRB,0IP0X:7R\10<0#RX?7X:7R]PIPI%<IR^PRPBP\P\P\P7P7g011Z12<0C`#<XF7XG7R_PIPIP^PSPMP\P\%80#<X:8RSPZPMPXPA%<ARMPYPOPXPAPMP9PC%<CROE_E^EQM:URYG\1W9D17CLR^P9PCPOPDPL%<LJ08P:H06ROP^%[5RC%85#3R`%[DRD%3LRag00I]Rb1E7TRT1E7VRV9A7Tg00VlRc'M+02&01bRd3H%]bReP71Y7;RfP<%|7RgCFRh%w7Ri%v7Rj1>73Rk1K71Rl'9,5jRm%r?R?1K72R21>7ARnAq7nl5O79O72Ro'9,5jC41nj@R@P0P;g00K0Rpg00KPRq'J1l0;=ZpqdAk73<CpRqb4b5b6X07X17%3<Rp1BA;,2A,2<,0<[^07^17P0%8>R>PIP;O3b3b9b8b2C@1GGQRr%3R%3BP\P]1J73PRPBPYEtPOP^PCP`PDPa1u7ARs=T7V1E7U=A7T5A7RT/Mc=HbdPePhPiPjPmP?Pj1>7E/92,5jP?19ko,5jC4C4P@Pqb4b5b6X07X1710E<1BA:,2A,2;#3[\p^07^17P0P>PIP;P4O4b3b9b8b2C@%=1R>%=FRF'iRp,7R17BpP7P7P6P\P617<0#RX?7X:7PRPBPYPpPp%<pR6M<DPOP^PCP`PDPa1g>FRE173>%3F173p[[R3%3>Rkg00L0RmAy>F<UW;RF%3p\m^;kRk1E7W9T7s=A7T/Mc=HbdRdPeP7PfP<P71Y7:P:PgCFCFRgPiPjP7Plg00LLRl%C1,K7R1CI,5jRfP?Pj1>7J,91,5jR1P?Pj1>7K,92,5jR2P?P7PoPl1>7>=z7GRGCI,5jC4C4C4P@Pqb4b5b6X07X17X7717<;R<10:JRJ10;KRK1BA9,2A,2:R:/7p[[[^07^17^77P0PLf:#8PIP5P4P=O6R=b3b<b=b9b8b2C@5{RR4E?P[1~HZRZE?PNPQ%8XRQ,2P/0pX>NP7PR120Q/0pX@712RQR0/0p12BARN/0pP\P]P0PNP\P\P\P_PRPBPYPQPAP\P\PSPXPAPMEQM:UPpPpP6G\POP^PCP`PDPaPEP3PFPkPdPePgPiPjPfP?PjP1P?PjP2P?AO7on/9G,5jC4C4C4P@Pqb4b5b6X07X17X7712:A/0p\K\J\<^07^17^77P=b3b<b=b9b8b2C@PrP4E?P[PZE?H00E?bCbBbAWDXE8o"). Qed.

End Scaffold.

End ArgvEnv.
From Stdlib Require ZArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.
Module StartupAux.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.WalkTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.MemSplit.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_StartupAux () := "C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List7existsbC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyC4ELinuxProcessSemantics5Riscv3Sem7reg_getI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C4ELinuxProcessSemantics5Riscv7Prelude6bv_keyK4ELinuxProcessSemantics5Riscv7Prelude4tree01C4ELinuxProcessSemantics5Riscv7Prelude4tgetC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4bool00I47Corelib7Numbers7BinNums8positive00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics5Riscv3Sem2w0I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4lnotC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z4predC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z:ones_equivK47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z=ones_mod_pow2C56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith8Zbitwise1Z?sub_land_same_lC56Stdlib6ZArith6BinInt1Z5ldiffC56Stdlib6ZArith6BinInt1Z:ldiff_landC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z6shiftlK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z<ldiff_ones_rC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z:land_assocK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula07K47Corelib4Init9Datatypes4list02K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C45stdpp9bitvector;definitions7bv_wrapC49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=bv_wrap_smallC56Stdlib6ZArith6BinInt1Z<eq_decidableI47Corelib4Init5Logic2or00K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula06c59OSSVerify5KrLib7Mh_0041:StartupAux?land_align_maskC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedC49OSSVerify5KrLib8PropExec6v_andiC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst7Inj_Z_Zc59OSSVerify5KrLib7Mh_0041:StartupAux=land_low_zeroC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z=testbit_neg_rC56Stdlib6ZArith6BinInt1Z=mul_pow2_bitsC46Stdlib4Bool4Bool<andb_false_rC56Stdlib6ZArith6BinInt1Z=pow2_bits_eqbC56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib7Mh_0041:StartupAux?land_4_aligned8C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9pow_add_rK47Corelib4Init5Logic2ex01C56Stdlib6ZArith4Zdiv1Z>mod_mod_divideC45stdpp9bitvector;definitions8bv_swrapC45stdpp9bitvector;definitions?bv_half_modulusC46Stdlib6ZArith4ZdivBZminus_mod_idemp_rc59OSSVerify5KrLib7Mh_0041:StartupAux=mod4_mod_pow2C1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4ZdivBZminus_mod_idemp_lC49OSSVerify5KrLib8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_subwC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC47Corelib4Init9Datatypes7nat_indI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_lec59OSSVerify5KrLib7Mh_0041:StartupAuxDfirstn_Z_to_le_bytesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01c59OSSVerify5KrLib7Mh_0041:StartupAuxGfirstn_word_to_le_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec:rdn_firstnC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC49OSSVerify5KrLib8PropExec:bytes_le_NC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega7EnvRing5PExpr06C45stdpp9bitvector;definitions>bv_swrap_smallC49OSSVerify5KrLib8PropExec4v_lwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega5Tauto8GFormula01C49OSSVerify5KrLib8PropExec6v_slliC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz05C46Stdlib5Lists4List2InC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic9False_indC46Stdlib4Bool4Bool=andb_true_iffC47Corelib4Init9Datatypes3orbC46Stdlib4Bool4Bool<orb_true_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib4Init5Logic6eq_symK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib4Init9Datatypes8list_indC45stdpp9bitvector;definitionsDbv_unsigned_in_rangec59OSSVerify5KrLib7Mh_0041:StartupAux<Z_to_bv_u_eqC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma getr_empty : forall r : reg, getr bvmap_empty r = Z_to_bv 64 0.
Proof.
ltac2:(KReplay.run1 (kr_t_StartupAux ()) ["FPX_1"] "p'0h01pi001ph12b1h22b2h31nh41Hh51bi011bh61ri021vi031xp;1p;3p;2p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000dR1p4p710p8P0P1p4p7210p8P0p1001Ap4p710p8p1001]p4p710R0p1002:p4p710p8P0p1002Vp4p710R0p8p10034p4p710P0p8g003Sj12Tg0048j18Tg004]j17Tg005;j11Tg005^j3@Tg006Aj3>Tg006nj2<Tg007Tj2;Tg008Fj26Tg0090j30Tg009Jj25Tg009dj29Tg00:Qj1:Tg00;>j34Tg00;ij23Tg00<Sj3?Tg00=7j2=Tg00=iR0#2R1#8#7R2#1f0R3g00>NR4g00>l5@25>2g00?HR5P5%21#2#2#2#2#7R1#1R6P5P6P31<14R41;26R5f2R7'6n0100000020000;04P31564f1R8,92g00?hR2P2g00@MR9P6P6%:6R:9463P3g00@oR;n10110300021010200=064P3g00ATR<%13R=%18R>g00B2%17?083g00BMR?f3R@/3713@830RA[1378137350?%1@?078[RBf4#1?0@7\AA?783P3n2001000000120000000W2W1W3PB^2>^1=^3<P3P1P;P41314,5?O4b4R?P9P6P6%83=46:P3P;n10110300021010200=064eX02P3O1P?P9P6P6%23=46:P3P;n10110300021010200=064eX02P3O1P?P9P6P6A460:P3P;n10110300021010200=064en011000003101001010000b01658=064en0110100020001b51=53=064eW6o"). Qed.
End FPX_1.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Open Scope Z_scope.
Section FPX_2. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


Lemma land_align_mask : forall a k, 0 <= a < 2^64 -> 0 <= k <= 64 -> a mod 2^k = 0 ->
  Z.land a (2^64 - 2^k) = a.
Proof.
ltac2:(KReplay.run1 (kr_t_StartupAux ()) ["FPX_2"] "h06__sat0h14__x1h21Hh32Hah42H0h52H1h62H2h72H3h82H4h92H5h:7__arithh;6__sat1h<6__sat2h=6__sat3h>6__sat4h?1qh@1rhA1zhB4__ffhC8__varmaphD5__withE4__p1hF4__x2hG4__p2hH6__sat5hI4__x3hJ4__x4hK4__x5hL2H6hM2HkhN4HmodhO1ahP1kp%0p&0p;1p;2p;3p;4p;6p;7p;8p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000dR1p4p710p8P0P1p4p7210p8P0p1001Ap4p710p8p1001]p4p710R0g002:R1p4p710p8P0g002VR0p4p710R2p8p10034p4p710P2p8g003Sj1ETg00Bkj1YTg00CIj22Tg00Cfj23Tg00B2R2j26Tg00DBj2;Tg00D^j27Tg00E>j1RTg00E\j1STg00F:j2=Tg00FXj28Tg00G5j1kTg00GSj2PTg00H;j3QTg00H_j2]Tg00IPj2Uj3zTg00J1j1JTg00JJj2>Tg00Jgj2<Tg00KDj2BTg00Kaj2TTg00LHj2ZTg00Loj2^Tg00MUj2XTg00N;j1sTg00N[j1qTg00O;j2OTg00OYj1oTg00P7j1nTg00Pbj2KTg004]j1mTg00QEj3lTg00Qhj3ITg00RKj2FTg00Rnk20<Tg009Jk20;Tg00SPk20:Tg0090j3cTg00T<k309Tg00T[k408Tg00UMj1jTg00V1k103Tg00VSk302Tg00W:j3iTg00W]k201TP1j6`Tg00XHj2[Tg00Xgj2\Tg00YKj2|Tg00Ykj2aTg00ZKj1{Tg00Zij4NTg0048j1hTg00[Gj2yTg00\8j1xTg00\Vj2wTg00]7j1WTg00]Vj2VTg00^?j3eTg00^hj3LTg00_Qj2fTg00`=j3dTg00``j3vTg00aCj3uTg00alj3}Tg00bUj3~Tg00c;j3tTg00c^k300Tg00dBj4_Tg00dmj7rTP0k604Tg00eQk705Tg00f5j8bTg00fYk606Tg00g=k607Tg00gaj3pTg00>NR0f0R1';p=0g00BMR3?c10p=5f1R4=c31p=11301p=:P3P4g00hAP1C_p=AP4g00hhR5g00iGR6P6g00igR7P1g00jGFrp=4P3f4R8f3R9f2R:P4P1J04p=9P3P4g00jgP1C_p=GP:P5P6P6P7P4P1K05p=CP9P5P6P6P7P:P4P1Gbp=DP4P5P6P6P7P1J06p=MP3P4g00kNP1C_p=Hf6R;P5P6P6P7f5R<P8P9P5P6P6P7P:P4P1GbGbp=?P4P5P6P6P7P1J07p=gg00l5R5?p41p=@%04R=g00=iR>#ER?#YR@%E?S00#E#E#E#ERA#YRB'2RC,34'61;4B,6=S0112@:,79#5%RBRD%R9RE#S'=S0212@8RF,8CRG,11XA3RHP31=DES03,8DPH12@9RH,7DRI18D1/1GXA3RJPEPJ%kCRJ%R8RK,81/1GXA3%kH18J1/1GXA31P@BRJ%:@RL%0BS04%:C[[RM%0@RNg00laROAQ@B4UW3RP%0C\O^3NRQ1P@<S05%0;S06f7RR,2@RS#:[\LS07f8RT=Q@4VOX3NS0812@TRU#0RV\O^3NS091]TSS0:%0TS0;f:RWf9RX,2@RY'7RZ#0\V[S0<1UXUS0=%5U#J1>WY,<Y/BZ,1W[S0>1TWYS0?%:Yf;RZ12@WRV'7R[#0S0@13[V'6[S0A1ZZVS0B13V012@ZR\f<R]/7\R^'31;^0'6[R_1^]\R`%5\S0Cf=Ra12@]Rb'>S0D#5[Rc1XabRd%5bS0Ef>Re12@aRf'7Rg/1e[Rh1>efRiP3f?Rj12@eRk'7RlP3P2f@Rm#0Rn13mCRo%Y>Rp,8CRq12@mRr/8p'818Cr'1PefBRs#0RtfCRu/3CRvPZP4O1Rw12@uS0F#0%0<S0G[Rx%s5Ry%q5R51O34S0H%o3Rz%n3R{1K3@S0I%mA5l3RA1K3pR|5I31F3>R}=I3|5I3AI3A}'A'420<{7R7P1P:g00?HR|g00m=R~+0;20:1:=c|~dB09304H08R~bBbCbDX13181p,8q18C1'1^13P1fERq,2@O1b:b0W9W8P4P1O2n2001000000120000000b@b?b7b6b5b4b2b0b;b<b=b>PE%j9D9PD%jBD9PIPJPMPPPQQ05Q07Q08Q09Q0:Q0<Q0=Q0>Q0?Q0AQ0BP_P`PcPdPhPiP3PlP3P2PnPo1;mB,6nPePwPxPyP5Q0HPzP{1K30RI/G},4{Rp1K3BS0J,G},4{5C{R|&036R6P|CDP7P~bBbCbDX13%01R|1;1B'6Q01[^13P1PqPuO2b:b0X9vX8tP4P1O2n2001000000121000000b@b?b7b6b5b4b2b0b;b<b=b>:02B9D9Q03PJPMPPPQQ05Q07Q08Q09Q0:Q0<Q0=Q0>Q0?Q0AQ0BP_P`PcPdPhPiP3PlP3P2PnPoPnPePwPxp-0RxPyP5Q0HPzP{1M{99C{pP6PpCDP7P~bBbCbDX13WES0B16|4P=[^13^ExS0AP11;qBPqPuO3b:b0X9vX8tP4P1O2n2001000000120000000b@b?b7b6b5b4b2b0b;b<b=b>9iD9D9Q02201DEE`1[DER|1\DED918CH,1|P31[DKS021=;1/1;XA3R|%SKRH,=DS0?P|1=<DS0>/=H111;XA3R|17<CS0=%R<#S,=1/1;XA3REP<PEP31[<KS0<P|1|<8S0:/a8P|1><FRE1a1</1;XA31<EFP|PJPMPPPQ1P@;S09%0RS08%:U[\LS07AQ@X4VOX3NS05%0YR|\O^3NS031]XUS01%0XS0KQ0@\|[S0@1UWYS0L%5Y#J1>ZV,<V/B[,1Z[S0M1TZVS0N%:VS0O%0^13^\'6[S0P1Z]\S0Q13\017abR^,3b1;^0'6[S0R1^abS0SQ0E%5i[S0E1XefS0T%5f11lj[S0U1>jkS0VP312@jRi,7mS0WP3P2fAR[#0RY13[CR|12@[S0X#5#JPj%0uRufDRU/3CRnPw12@U#0Q0G[RoPyP5P3%{3RhP41O3:CNPzP{P{Q0I,HI,4{S0IP6P{%h>,F3Rd,GI,4{RcP61HI},4{F?P6P{1M{89C{cP61A}I,4{S0Y,g{F?P7P~bBbCbDX13XF3XEx%0:Rc%::[\L16c9%5:R`g00m]S0Z[[[^13^F3^ExP1fFR_/;BS0[P_12@_S0\PjPUO5b:b0W9W8P4P1O2n2001000000121000000b@b?b7b6b5b4b2b0b;b<b=b>9z<F1<FE17<F'B,1<12@<,y;Q0612@;#01>TS#0[[PJPMPPPQ1P@TQ0KQ0O[\LAQ@Z4VOX3N%0\RS\O^3N1]ZV%0Z%0^\S[1U]\Q0C#JQ0D,<b/B^,1a[1Tab%:b%0g13gf'6[1Zef13f013kl1;l0'6[1^jk%5k1>mi#5[1Xmi%5i17[r/1[[1>[rP3Q0X,7sP3P2PuPvQ0F,<:/1UP[%0q13_CPwQ0\#0Q0G[P[P:O1fGR[,2@#0Q08[%x>,w3R>g00n:Rq#W#WRv#W,V3Rr5e31V3vRv9e3>1V3qRq5L35L3g00nYR>'fRiAL3vq9L3r/f>R>1@>y,@i,@>,@i,@>,@i'@'@P5P3P31O38P:PhCNP4P31O3<P9PhCNCNPzP{P{1F3?Ri/AI,4{R>P6%h?,F3R?/Ad,4{CDP6P{P{P>P6Q0YCDP6P{P{1HIi,4{RrP61M{R1H?i,4{5C{CDP6P{P{1g{>P6Ad3i}=v3?,Ad,4{R>CDP6P{P{Q0IP6P{Q00,F3,GI,4{RqP6PrF?P6P{P>P6P{1A?I,4{P6P{1M{T9C{qP6Ad3}i/Ad,4{F?F?F?F?P7P~bBbCbDX13XF3XI3XJ3XK3XExXGx%5411<9[P`\`%:913R8,6T[%58Q0Z[1<<8/BT,1;[Q0;%:R[\L1<;</BX,1R%5W%0W/6a1<TX/1W[[[[[[[[^13^F3^I3^J3^K3^Ex^GxP1fIRx/;BQ08PRPxfJ12@xPTPXPWP]PaPmPUP_P[O?b:bHb0WLW9P4P1O2n2001000000121000000b@b?b8b7b6b5b4b0b;b<b=b>bHb21aE8PJPMPPPQQ09Q07Q05Q03Q01Q0@Q0LQ0MQ0NQ0PQ0QQ0RQ0SQ0EQ0TQ0UQ0VP3Q0WP3P2PYP|PYPjPwPoQ0BQ0AP1Q0[P_PUO3b:b0X9nX8uP4P1O2n2001000000120000000b@b?b7b6b5b4b2b0b;b<b=b>RU9uE8D9Q0:A}<8UD9Q0<A~<8UD91=<H1\<KE`Q0=PJPMPPPQQ09Q07Q05Q03Q01Q0@Q0LQ0MQ0NQ0PQ0QQ0RQ0SQ0EQ0TQ0UQ0VP3Q0WP3P2PYP|13sC,6tPjPwPoPyP5Q0HPzP{1H}A,4{R}P6P{PpP6AC{p}F?P7P~bBbCbDX13131C13:C,6c\=[^13P1P[P:P9O3b:b0X9nX8uP4P1O2n2001000000121000000b@b?b7b6b5b4b2b0b;b<b=b>9t<CD9Q0>PJPMPPPQQ09Q07Q05Q03Q01Q0@Q0LQ0MQ0NQ0PQ0QQ0RQ0SQ0EQ0TQ0UQ0VP3Q0WP3P2PYP|Q04PjPwPoPyP5PhPzQ0J,GI,4{P7P~bBbCbDQ04P1b:b0X9nX8uP4P1O2n2001000000120000000b@b?b7b6b5b4b2b0b;b<b=b>9i<BD9Q0?,=<B00<DHD9Q021\DKD9PGP1E`b2WNWMW3XP3XO3o"). Qed.

(* [comment removed for export] *)
Lemma v_andi_m16_aligned : forall x : word,
  bv_unsigned x mod 16 = 0 -> v_andi x (-16) = x.
Proof.
ltac2:(KReplay.run1 (kr_t_StartupAux ()) ["FPX_2"] "h01Hh16__sat2h22Hah34__x1h41xh52H0h62H1h72H2h82H3h92H4h:2H5h;7__arithh<4__ffh=6__sat0h>6__sat1h?8__varmaph@5__withA1nhB1qhC1rhD6__sat4hE6__sat5hF4__x2hG4__x3hH4__x4hI4__x5hJ2b1hK2b2hL1zhM3H10hN3H11hO2H6hP2H7hQ2H8hR2H9hS2HmhT6__sat3hU1mhV2q0hW2r0hX1yp%0p&0p;1p;2p;3p;4p;<p;6p;7p;5p;Bp;8p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000dR1p4p710p8P0P1p4p7210p8P0p1001Ap4p710p8p1001]p4p710R0p1002:p4p710p8P0g002VR0p4p710R1p8p10034p4p710P1p8g003Sj1BTg004]j1hTg005;j1@Tg00;ij20Tg00Bkj1JTg00D^j23Tg0090j3=Tg00<Sj3mTg00\8j1\Tg00oEj2LTg00F:j2ZTg006nk20?Tg00okk10=Tg00CIR1j2ITg010bR2j1aTg00CfR3j22Tg00B2R4j2:Tg009Jj2<Tg011@j3tTg011fj1rTg012Dj4qTg012gl<nTg013Lj6lTg00H_j2gTg00GSj2fTg00H;j3[Tg00IPj2NTg00J1j1MTg00JJj27Tg00Jgj2DTg00KDj2ETg00Kaj2KTg00LHj2RTg00DBj2GTg00Loj2YTg00MUj2WTg00N;k10>Tg00N[k10<Tg00O;j2VTg00OYk10;Tg00P7k108Tg00RKj2CTg00Pbj2FTg00QEj3cTg00V1k106Tg00Rnk205Tg00SPk204Tg00T<j3~Tg00T[j4}Tg0145j4|Tg014`j1zTg015Ij3yTg00FXj2xTg00ZKj1wTg0165j2vTg016[j2]Tg00\Vj2sTg00]7j1?Tg00^?j3XTg00]Vj2_Tg00_Qj2uTg0175j2`Tg00gaj3OTg00Zij4PTg0048j1^Tg017aj7{Tg00`=j3bTg00``j3dTg018Ek500TP0j6eTg019Lk201Tg01:;k202Tg01:om<03Tg01;TlBkTg00dBj4UTg00dmk707Tg00eQj7jTg00f5k809Tg00^hk30:Tg00g=j6iTg00BMR0f0R5g00>NR63=p=8f1R7==05p=41G65p=1f2R81275':p=9g00ATR9P0P0P0P2P2f5R2f4R:f3R;P8P7P5N<03p=pP0P0P0P0P0P0P1P5P7P8P1P;P:P2f6R1f7R<f8R=f9R>MBkp=oP0P7g00kNP5CUp=TP7g00hhR?g00iGR@P@g00igRAP5g00jGK07p=5P0P7g00jgP5CUp=HP8P?P@P@PAP7P5Fjp=SP;P?P@P@PAP8P7P5L09p=61_05p=AB0:075p=>P0P7g00hAP5CUp=;P7P?P@P@PAP5Eip=Qg00=iRB#BRC#BRD#B#BRE#B#BRF#hRG#@RH10G5%JERI'3#8%@5RJ%@7RKP4%@8?=7510;810;7'4RL[10871085'4%@;?=87[RM%@:?=;8\LAm875P5n2001000000120000000WKWJXA9PM^KK^JJ^A9P5PG10G8RJ%\ERE,LG'ZRK-0?GRMP8P01LGK10G;RL,45XL0&0=8%1J%JCRN%JFRF'IRO79JP0PL1LG510G:RJ'4XL0%1LRP%aGRQ,INRR,2LRS':12LORT,:PPPPSPPPTp-0/<P9tPPP0P0P3P5X40RTP31275#rXX0X40PLPL1<0LPRPOPTPTPTP0P0g01<:1I75Cq,<0XU0XA0PNPN1<0NPQPFPTPT%a5,<0X49PGPF1<0FEpM:oM<nEl1gLIR9%1IRT10G2/3I#1[\PRQ1fNFRR126NR3%1F126O[[RS%1NRUg00laRVA[NF7UW2RW%1O\V^2URX10G1RY/NIS00%8IRZ#MR[10G<R\17\I,DI13\I'E'4[S011K\IS02126IR\10G=R]/3IR^#1?9^I[S031R]IS0412I6R]10G>R^/3IR_,2I1G_6':[S051Y^IS06f:R_,0GR`/7I#8\ZS071W`IS08f;,0GRa/3I/4a\ZS0917aIS0:P0f<Rb,0GRc/3IRdP0P4f=Re,0GRf#1Rg12fORhf>Ri,0GRj#1?9jOP_f?S0;,0GRk#1Rlf@S0<,0GRm/2ORnPeP7O1Re%12S0=\TRog00l5Rp$0>Rq&0<pRr1V07&0;0Rs&080Rt1C0BRu1F0NRv=c0G'T,5tRw&06@RxPt1F06Ry/Hu,5tRzPxAStzwC6C6205tARwP5P8g00?HR{g00m=R|'<20458=={|dA~067C}R|b<b?b@X30125O%17%18?98O[[^30P5fC,0GR{P8P;O3b;b1W:W0P7P5O2n2001000000121000000bCbBb9b8b7b6b5b=b>b1R}C|%zG99PLe9yGL%JDRP,INR~,xO,ZLPLPPP}P9PQPRPSPWPXQ00Q01Q02Q03Q04Q05Q06Q07Q08Q09Q0:P0PdP0P4PgPh%1PRh1GPF':RgP_PePoPqPr%w0RoPs1F0PRe,Hy,5t1F0F,He,5t5StPwP|b<b?b@PgP5b;b1X:nX0lP7P5O2n2001000000120000000bCbBb9b8b7b6b5b=b>b1P9PQ1gJ~%1J%1~RJ13Y~#1[[1fNP126~RY\h\3A[NP7VVX2UPJ\V^2UPRPSPWPX1N^~%8~R^#M17`~,D~13`~'E,4`[1K`~13a~R`#1?9`~\Y1Ra~12~613c~Ra,2~1Ga6':[1Yc~17f~#8\^1Wf~13j~/4j\^17j~P013k~P01NmIfA,0GRm17mI,DI13mI'E'4\[1KmIfB,0GRm/3IR[#1?9[I\\1RmI13{IRm,2I1Gm6':\]1Y{IfDR{,0GR]/7I#8\Z1W]IfER],0GRm/3I/4m\Z17mIP0fFRm,0G/3IP0P4fG,0GR4#1124O%8=P{fI,0G#1fJ,0G/2OPmP7O1%1b\JfHP8O1%11\T1vi<14i<RT%MT']RTePT%\B,s0RTg00n:Rb#?Rm#?RO#?R4#?R6#?#?R\#A5X0%A6R6%A4%AmRm9X0T'>'>'>%?\#AAX0T6%AO/>m'>'>1_0b,>mg00nY'u'`'`RmAOpmq9Opm5OpPrP0P01V0:P8PoCPP7P01V02P;PoCPCPPsPtPtP?P@P@PA1C0DRA%^C,C0R@';,5tR?1Qt?F{PxPtPt1F0IR?/;y,5t,QtPx%^B,C0RBAb0?@1C0CRC5d0';,5tC6PxPtPt%hD9c0vRv,Ty,5tPx1Tuv,5t9StzC6PxPtPt1;vy,5t,QtPxAb0vA=d0u,;B,5tC6PxPtPt1Hyv,5tPxPzC6PxPt1;Cy,5tPx1;uy,5tC6C6C6C6C6C6PwP|b<b?b@X30XF0XG0XH0XI014;:R|g00m]Rw\|']Pw\Z1DI1/E;,4:[%1;?9;~\YPw\^1D~</E:,41[Q0=\J%81R1P1[[[[[[^30^F0^G0^H0^I0P5P>Q0<fO,0GP=Q0;P7PiP{P]P;fNO;b;bNbEbDWMW0P7P5O2n2001000000121000000bWbVbRbQbPbOb:bCbBb9b8b7b6b5b=b>b1bTbDbEI00Eeb010GM201GKEeO4b02027E==H7eWSW4o"). Qed.

(* [comment removed for export] *)
Lemma v_andi_m8_aligned : forall x : word,
  bv_unsigned x mod 8 = 0 -> v_andi x (-8) = x.
Proof.
ltac2:(KReplay.run1 (kr_t_StartupAux ()) ["FPX_2"] "h06__sat0h11Hh22Hah36__sat1h44__x1h51xh62H0h72H1h82H2h92H3h:2H4h;2H5h<7__arithh=4__ffh>6__sat2h?8__varmaph@5__withA1nhB1qhC1rhD4__x2hE4__x3hF4__x4hG4__x5hH2b1hI2b2hJ1zhK3H10hL3H11hM2H6hN2H7hO2H8hP2H9hQ2HmhR6__sat3hS6__sat4hT6__sat5hU1mhV2q0hW2r0hX1yp%0p&0p;1p;2p;3p;4p;<p;6p;7p;5p;Bp;8p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000dR1p4p710p8P0P1p4p7210p8P0p1001Ap4p710p8p1001]p4p710R0p1002:p4p710p8P0g002VR0p4p710R1p8p10034p4p710P1p8g003Sj1ATg004]j1hTg005;j1@Tg00;ij20Tg00Bkj1JTg00D^j22Tg0090j3?Tg00<Sj3mTg00\8j1\Tg00oEj2LTg00F:j2[Tg006nk20?Tg00okk10=Tg00CIR1j2ITg010bR2j1aTg00CfR3j23Tg00B2R4j2:Tg009Jj2<Tg011@j3tTg011fj1rTg012Dj4qTg012gl<nTg013Lj6lTg00GSj2gTg00H;j3fTg00H_j2NTg00IPj2MTg00J1j1OTg00JJj27Tg00Jgj2FTg00KDj2DTg00Kaj2KTg00LHj2RTg00DBj2ETg00Loj2ZTg00MUj2YTg00N;k10>Tg00N[k10<Tg00O;j2XTg00OYk10;Tg00P7k108Tg00RKj2CTg00Pbj2GTg00QEj3cTg00V1k106Tg00Rnk205Tg00SPk204Tg00T<j3~Tg00T[j4}Tg0145j4|Tg014`j1zTg015Ij3yTg0048j1`Tg00FXj2xTg00ZKj1wTg0165j2vTg016[j2^Tg00\Vj2sTg00]7j1=Tg00^?j3PTg00]Vj2]Tg00_Qj2uTg0175j2_Tg00gaj3QTg00Zij4STg017aj7{Tg00`=j3bTg00``j3dTg018Ek500TP0j6eTg019Lk201Tg01:;k202Tg01:om<03Tg01;TlBkTg00dBj4WTg00dmk707Tg00eQj7jTg00f5k809Tg00^hk30:Tg00g=j6iTg00BMR0f0R5g00>NR63?p=8f1R7=?05p=41E65p=1f2R81375':p=9g00ATR9P0P0P0P2P2f5R2f4R:f3R;P8P7P5N<03p=pP0P0P0P0P0P0P1P5P7P8P1P;P:P2f6R1f7R<f8R=f9R>MBkp=oP0P7g00kNP5CWp=VP7g00hhR?g00iGR@P@g00igRAP5g00jGK07p=5P0P7g00jgP5CWp=HP8P?P@P@PAP7P5Fjp=UP;P?P@P@PAP8P7P5L09p=61]05p=BB0:075p=>P0P7g00hAP5CWp=;P7P?P@P@PAP5Eip=Tg00=iRB#ARC#ARD#ARE#A#A#ARF#hRG#@RH10G5%JERI'2#8%@5RJ%@7RKP4%@8??7510;810;7'4RL[10871085'4%@;??87[RM%@:??;8\LAm875P5n2001000000120000000WIWHXA9PM^IK^HJ^A9P5PG10G8RJ%\ERE,LG'[RK-0?GRMP8P01LGK10G;RL,45XJ0&0=8%1J%JCRN%JFRF'IRO79JP0PL1LG510G:'4XJ0%1LRJ%aGRP,INRQ,3LRR':13LORS,:JPJPRPJPSp-0/<J9tJJP0P0P3P5X50RSP31375#rXX0X50PLPL1<0LPQPOPSPSPSP0P0g01<:1I75Cq,<0XU0XA0PNPN1<0NPPPFPSPS%a5,<0X59PGPF1<0FEpM:oM<nEl1gNFR9136NRS%1F136O[[RP%1NRQg00laR3AfNF7UW2RR%1O\3^2QRT10G2RU/NIS00%1U%1IRU10G<RV/2IRW#1[[S0110G1/MIS02%8IRX#ORY17VI,FI/DW,4V[S031KVIS04136IRW10G=RZ/2IR[#1?9[I[S051RZIS0613I6R[10G>R\/2IR],3I1E]6':[S071Z\IS08f:R],0GR^/7I#8\XS091Y^IS0:f;R_,0GR`/2I/4`\XS0;17`IRaP0f<,0GRb/2IRcP0P4f=Rd,0GRe#1Rf13eORgf>Rh,0GRi#1?9iOP]f?S0<,0GRj#1Rkf@S0=,0GRl/3ORmP_P7O1R_%12S0>\URng00l5Ro$0>Rp&0<oRq1X07&0;0Rr&080Rs1C0BRt1G0NRu=c0G'V,5sRv&06@RwPs1G06Rx/Ht,5sRyPwAUsyvC6C6205sARvP5P8g00?HRzg00m=R{'<20458=?z{dA~067C}R{b=b?b@X40135O%17%18?98O[[^40P5fC,0GRzP8P;O3b<b0W;W1P7P5O2n2001000000121000000bCbBb:b9b8b7b6b0b3b>R|C|%zG99JLe9yGL%`BRJ#JR},INR~,xO,[LPLP}P|P9PPPRPTQ00Q01Q02Q03Q04Q05Q06Q07Q08Q09Q0:Q0;PaP0PcP0P4PfPg%1}Rg1E}F':RfP]P_PnPpPq%w0R_Pr1G0}R],Hx,5s1G0F,H],5s5UsPvP{b=b?b@PfP5b<b0X;mX1kP7P5O2n2001000000120000000bCbBb:b9b8b7b6b0b3b>1gN}136~Rk\g\SAfN}7V3X2Q%1~R}\3^2QP9PPPRPT1NV~%1V12\~#1\}[1NZI%1Z12^I#1\U[1M\~%8~R\#O17^~,F~12^~'D,4^[1K^~12`~R^#1?9^~\k1R`~13~612b~R`,3~1E`6':[1Zb~17e~#8\\1Ye~12i~/4i\\17i~P012j~P01MlIfA,0GRl17lI,FI12lI'D'4\Y1KlIfBRl,0GRY/2IRj#1?9jI\W1RYI12zIRY,3I1EY6':\[1ZzIfDRz,0GR[/7I#8\X1Y[IfER[,0GRY/2I/4Y\X17YIP0fF,0G/2IP0P4fG,0GR4#1134O%8=PzfI,0G#1fJ,0G/3OPlP7O1PnPzP8O1%1d\}1vh<14h<Rd%Od'^RdePd%\B,s0RBg00n:Rd#=Rn#=Rl#=RO#=R4#=#=RY#B5P0%B4R4%BO%BnRn9P0B'>'>'>%=Y#BAP0B4%Bl/>n'>'>1]0d,>ng00nY'u'_'_RnAQonp9Qon5QoPqP0P01X0:P8P_CSP7P01X02P;P_CSCSPrPsPsP?P@P@PA1C0DRD%`C,C0RA';,5sR@1Ts@F{PwPsPs1G0IR@/;x,5s,TsPw1C0JR?Ab0@A1C0CRC5d0';,5sC6PwPsPs%hJ9c0uRu,Vx,5sPw1Vtu,5s9UsyC6PwPsPs1;ux,5s,TsPwAb0uD=d0t,;?,5sC6PwPsPs1Hxu,5sPwPyC6PwPs1;Cx,5sPw1;tx,5sC6C6C6C6C6C6PvP{b=b?b@X40XD0XE0XF0XG014;:R{g00m]Rv\{'^Pv\X1FI1/D;,4:[%1;?9;~\kPv\\1F~</D:,41[Q0>\}%81R1P1[[[[[[^40^D0^E0^F0^G0P5P>Q0=fO,0GP=Q0<P7PhPzP[P8fNO;b<bLb3b0WKW1P7P5O2n2001000000121000000bWbVbPbObNbMb;bCbBb:b9b8b7b6b0b3b>bRbSbTI00Eeb110GM201GKEeO4b12027E=?H7eWQW5o"). Qed.

(* [comment removed for export] *)
Lemma land_low_zero : forall a k, 0 <= a -> 0 <= k -> a mod 2^k = 0 -> Z.land a (Z.ones k) = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_StartupAux ()) ["FPX_2"] "h02Hah11ah26__sat2h34__x1h41Hh52H0h62H1h72H2h82H3h92Hkh:2Hmh;7__arithh<4__ffh=6__sat0h>6__sat1h?8__varmaph@5__withA1khB1qhC1rhD1zp;1p;2p;3p;4p;7p;8p;6p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000dR1p4p710p8P0P1p4p7210p8P0p1001Ap4p710p8p1001]p4p710R0p1002:p4p710p8P0g002VR0p4p710R1p8p10034p4p710P1p8g003Sj1YTg00Bkj1@Tg00CIj20Tg00D^j21Tg00E>j1BTg00F:j2?Tg00GSj2>Tg00Cfj23Tg00H;j3<Tg00H_j3:Tg00IPj29Tg00J1j1XTg00JJj26Tg00Jgj2UTg00KDj2LTg0090j35Tg00Kaj2KTg00B2j27Tg00LHj2ATg00DBj28Tg00Loj2CTg00MUj2DTg00N;j1ETg00N[j1FTg00O;j2GTg00OYj1HTg00P7j1=Tg00Pbj2ITg00RKj2JTg00dBj4;Tg00dmj7MTg00V1j1NTg00f5j8OTg00Rnj2PTg009Jj2QTg00SPj2RTg00T<j3STg00T[j4TTg00W:j3WTP0j6VTg00>NR0f0R1'8p=2g00BMR2?510p=4f1R3#2R4f3R5g00=iR6#Y#@R7f2R8'0'1#4P2f4R91075'1%41XD2P1%B5,?91>751307R:%29f5,07R;,30[[%27R<g00laR=f6R>=<73UW0107>R?#2\=^0<A:>;9%2;f7R;/1?#2[19;?%4?#Xf8R?107;R;16?;'U11?;'L552[1K?;130;f9R;107?R?'1R>#213>?'7[1A;?13?0107;R;f:R?/1;R>'318>0'7[1C?;%4;f;R;107?R>'6#4[1D;>%4>f<R>107;R;'1=52>[16>;P2f=R;107>'1P2P?P1P>O2X1:f>,07,30^1:g00l5R:#E%F:1G23%H2%=2R:g00hhR7g00iGR>P>g00igR?P:P7P>P>P?P21I20g00jg1J26C;g00jGFMR6%N>P6GO1P:?P1P8g00?HR?g00m=R:'Q1R18=5?:dAS203CTb<b?b@X32%21P4[^32P1f?P;O2b;b2bCbBb8b7b6b5b4b=b>b29W95EVW:X94W0XA2X12o"). Qed.

Lemma v_andi_3_aligned : forall x : word,
  bv_unsigned x mod 4 = 0 -> v_andi x 3 = Z_to_bv 64 0.
Proof.
ltac2:(KReplay.run1 (kr_t_StartupAux ()) ["FPX_2"] "h01xh11Hh22H0h32H1h42H2h52H3h62Hmh77__arithh84__ffh96__sat0h:8__varmaph;5__with<1qh=1rp;1p;2p;3p;4p;7p;5p;8p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000dR1p4p710p8P0P1p4p7210p8P0p1001Ap4p710p8p1001]p4p710R0p1002:p4p710p8P0p1002Vp4p710R0p8p10034p4p710P0p8g003Sj12Tg004]j1\Tg005;j1DTg00;ij20Tg00Bkj16Tg00D^j23Tg006nj1Cj2WTg0048j1BTg00oEj2ATg00F:j2@Tg009Jj2<Tg00CIj2[Tg00Cfj24Tg00okj1UTg00H_j2RTg00IPj2QTg00J1j1OTg00JJj27Tg00Jgj2LTg00KDj2KTg0090j35Tg00Kaj2ETg00B2R0j29Tg00LHj2FTg00DBj2:Tg00Loj2GTg00MUj2HTg00N;j1ITg00N[j1JTg00ZKj1?Tg00OYj1MTg00P7j1NTg00Pbj2;Tg00dBj4>Tg00dmj7PTg00Rnj2=Tg00SPj2STg00T<j3TTg00T[j4ZTg01<^j5YTg01=cj8XTg01:;j2VTg00BMR1f0R2g00>NR335p=81:32p=1g00=iR4#2R5#2R6#2#2#2#2R7#\R8#DR91082R:%66R6'3#8P1P9%C8R;P;f1R<,08R=%B4#6R4,A8'@P3P9\1/<;P=%65R5P0%1:R0%67,[5,4:%1=R:%U2P<n2001000000120000000X09P0^09P2f2R0O1b11R=6%16f3,08R=/36R7#1[\:1080/Q6%86R:#O17=6,L6/K7951=[1E=61436f4,08R=/36R7#11476'9[1F=61463f5,08R=/36R7,461:73'9[1G=6f6,08R=/76#8\:1H=6f7,08R=/36=51=\:17=6P1f8,08/36P1g00l5R6#I%J6%?1%M1%N1R6g00hhg00iGR=P=g00igR=P11;13g00jg1;15C>g00jGFP1=6=P2P0g00?HR=g00m=R6'<1S20=5=6dAT13<CZb8b:b;%15P2b7b=b<b5b4b3b2b1b9P2DYGX1V<41W83559eW6W0o"). Qed.

Lemma land_4_aligned8 : forall a, 0 <= a -> a mod 8 = 0 -> Z.land a 4 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_StartupAux ()) ["FPX_2"] "p'0h06__sat0h11Hh21bi001bh31ri011rh42H0h52H1h62H2h72H3h87__arithh94__ffh:8__varmaph;5__with<1ah=1qh>2Hih?6__sat1h@6__sat3hA4__x1hB4__x2hC4__x3hD1ihE2HahF2HmhG6__sat2hH1ei021ehI1ni031np;1p;2p;3p;4p;6p;7p;8p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000dR1p4p710p8P0P1p4p7210p8P0p1001Ap4p710p8p1001]p4p710R0g002:R1p4p710p8P0g002VR0p4p710R2p8p10034p4p710P2p8g003Sj1NTg00Bkj1CTg00D^j20Tg00F:j2UTg01>@j21Tg01>aj28Tg0090j3:Tg01??j2RTg01?\j2]Tg01@>R2j2|Tg0048j1zTg00GSj2rTg00Cfj24Tg00CIj2WTg00H;j3nTg00H_j3MTg00[Gj3eTg00JJj25Tg00IPj2ITg00J1j1VTg00Jgj26Tg00KDj2@Tg00Kaj2HTg00B2j29Tg00LHj2GTg00DBj2ATg00Loj2KTg00MUj2FTg00]7j1QTg00]Vj2ETg00^hj3?Tg00_Qj2PTg00\8j1\Tg00\Vj2[Tg00^?j3OTg00N;j1ZTg00gaj3YTg00N[j1{Tg00O;j2XTg00Zij4yTg00OYj1xTg00P7j1wTg00Pbj2=Tg00g=j6qTg00V1j1pTg00RKj2JTg00`=j3STg00``j3oTg004]j1mTg00QEj3lTg00Rnj2kTg009Jj2TTg00SPj2gTg00T<j3fTg00T[j4hTg00FXj2iTg00ZKj1jTg00dBj4BTg01@aj3dTP0j6>Tg01AHj4cTP1j6bj7aTg01Aoj1`Tg01BOj3sTg01C6j1tTg01CVj3_Tg01D9j3uTg00dmj7vTg00f5j8^Tg00>NR1f0R0'Ap=2g00BMR3?:01p=;g00?HR4g01D\R57:0p=<f1R6=:30p=3P3P6g00hAP0CBp=DP6g00hhR7g00iGR8P8g00igR9P0g00jGFvp=7f3R:P7P8P8P9f2R;P6P0G^p=L%20R<g00=iR=#NR>#NR?#N#CR@,06#;%C?R?,U;P4f4RA/1611?6'8111;9:40X24P4P5f5RB/1;RC11?;'8=:40X24P4%C>RD/R6RE18C0#<X241]D613D6/|E1RD;P4P213D:f8R2/1BRE/86#<P613DARCP3PDf:RF/16g00m=RG'8#<^><XD3%2DRH%z=RI#CRJ,rD141DRK%2JRL1WDJRM,41RN[[AnDJ6%2Mf;RO?M@F%2@RPf<RQ/0@RR#2[AeQ@Of=RS/5@#2\P1IS@%;@RT#VRUf>RV15V@,6@10V@RW'@'3[1HV@141@RXf?RY/0@RZ#214Z@'9[1GY@14@1RZf@R[/0@R\,4@1A\1'9[1K[@fAR]/5@#;\T1F]@fBR^/0@/3^\T15^@P3fC/0@P3f7R^f9R_O1R`%26RaP_PFO1PaPSP0PQO2X<KPN^<Kg00l5RKg00n:RN#QRa#Q,E3Rb1E3aRa1E3NRN5?35?3g00nYRc'P%\=Rd,[3Re=O3bAO3ea=?3N5?3/Pc%ZKRc5YK3Y%{KRKP31X3;P61X3:Cy%x3RN%w3RePePeP7P8P8P91=3@R71=31Ra'D,7eEq%p8R81J3>R>1J3=R=9S371J3IR75o3'D,7eCLP8Pe1D7a,7eP81=3DR8%mI5l39S3=/D>,7eCLCL1ke9R9P0P;1T4G1g0;=:4GdAf316ChR>b9b:b;XA3XB3XC3g00m]\T16@6/@:,3;[%;:16;M/3:[[^A3^B3^C3P0PAfHPBPFfFO5b8b@b?b0b3b=b7b6b5b4b1b0b?bGb@15_@R;/6M/3_P315F@R=/6MRM110D/8G#<X<3P41iDJ,1=180G#<X24RGP4P5PG1T4511=dAMF@_R510O@R4#2\PRG1IO@RO15Q@,6@/@R,3Q\URR1HQ@RQ10S@RI#214I@'9\XRI1GS@RS14@W1AW1'9\ZRW1KV@RV15Y@#;\TR71FY@RY13\[\TR\15[@R[P310]@R]P3P`P<PcPK%j3RbPNP31=3dg00kNPaCB,7eP9P>b9b:b;14d1P0b8b0b3b=b7b6b5b4b1b09d=dE>11MDP=PJPDP5PGPOPRPQPIPSPWPVP7PYP\P[P3P]P3P`P<PcPKPbPNP3Pag00jgR`1=3JCB,7eP9P>b9b:b;PLP0b8b0b3b=b7b6b5b4b1b0CcE>PFP0Ebb1W>PBP0PAFaWHP0O1%VC%`EWIP0O1n10210010100021110210103b2b31WDD/16AMA@:10B@#2\P1IB@f6RB15B@,6@10B@'@'3\U1HB@10^@RB#214B@'9\X1G^@102@R^,4@1A^1'9\Z1K2@%;;\T1F_@10F@/3F\TP=P3P4P3PcPKPbPNP3PaP`P8CB,7eP9P>b9b:b;PHP0b8b3b=b7b6b5b4b1b09sD6E>1116%t6E>1UA?/16A_A?6E>X><XD37u1WFWEX<3o"). Qed.

Lemma v_andi_4_aligned8 : forall x : word,
  bv_unsigned x mod 8 = 0 -> v_andi x 4 = Z_to_bv 64 0.
Proof.
ltac2:(KReplay.run1 (kr_t_StartupAux ()) ["FPX_2"] "h01xh11Hh22Hmp;1p;2p;3p;8p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000dR1p4p710p8P0P1p4p7210p8P0p1001Ap4p710p8p1001]p4p710R0p1002:p4p710p8P0p1002Vp4p710R0p8p10034p4p710P0p8g003Sj10Tg004]j1BTg005;j19Tg00;ij23Tg00Bkj11Tg00D^j2;Tg0090j34Tg006nj18j2>Tg00oEj27Tg00F:j26Tg009Jj25Tg00DBj22Tg00CIj2:Tg00Cfj2ATg00okj1@Tg01E<j3?Tg01=cj8<Tg01:;j2=Tg00=i#0R0#0R1#0R2#0#0#0R3#BR4#9R5g00BMR6f0R7,34R8%12';g00>NR234P6P5%84R9P9f1R:,34R;%11R1,74'6P2P5\6/59g00B21228R9%10%13':,A8122;%@7P:n2001000000120000000X05P9^05P7f2O1b1=?;7G<1=:11>42545eW2W0o"). Qed.

Lemma v_andi_1_of01 : forall z, (z = 0 \/ z = 1) ->
  v_andi (Z_to_bv 64 z) 1 = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_StartupAux ()) ["FPX_2"] "h01Hh12b1h22b2h31nh41zp;1p;3p;2p;6p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000dR1p4p710p8P0P1p4p7210p8P0p1001Ap4p710p8p1001]p4p710R0p1002:p4p710p8P0g002VR0p4p710R1p8p10034p4p710P1p8g00Bkj1<Tg0090j30Tg016[R1j2:Tg003Sj13Tg004]j1;Tg005;j12Tg006nj25Tg01:;j24Tg00;ij21Tg00<Sj39Tg009Jj27TP0j68Tg00BMR0f0R2g00>NR330p=6%62g00=iR4#<R59002':P1f1R1#6A0015%34#3#3#3#3#3#;R4#2R6f2R7,54R8/45;08P2%67P0P31542R8/45=068X40R8g00ATR6%22R9%21R:g00B2%27?012f3R;/1711;1500R<[11711172500%2;?071[R=f4#2?0;7\<A9712P2n2001000000120000000W2W1W3R1P=^2:^19^36R6P2P41543R3/45P31143,70O4b0P;P2E8W0P2O1A0075P0P5P8P1P6P2P41545R6/45P61146,70O4b0P;P2E8W0P2O1n200100000021000010000W0X40o"). Qed.

Lemma mod4_mod_pow2 : forall t k, 2 <= k -> (t mod 2^k) mod 4 = t mod 4.
Proof.
ltac2:(KReplay.run1 (kr_t_StartupAux ()) ["FPX_2"] "h04__x1h17__arithh24__ffh38__varmaph45__with51zh62Hkh71kh81tp;1p;2p;3p;4p;8p;5p;6p;7p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000dR1p4p710p8P0P1p4p7210p8P0p1001Ap4p710p8p1001]p4p710R0g002:R1p4p710p8P0p1002Vp4p710R0p8p10034p4p710P0p8g003Sj15Tg00Bkj1;Tg00DBj23Tg00CIj20j1BTg00Jgj2<Tg0090j31Tg00FXj27Tg00KDj29Tg009Jj26Tg00N;j1@Tg00N[j1>Tg00O;j2=Tg00OYj1RTg00P7j1QTg00RKj2PTg00Pbj2:Tg00Qhj3LTg00``j3KTg00dBj48Tg00Rnj2GTg00SPj2DTg00T<j3CTg00T[j4ETg01=cj8FTg00V1j1HTg00f5j8ATg00ZKj1ITg01FCj5JTP1j6?Tg01Ffj4MTg01G@j4NTg00dmj7OTf1R1g00hhR0g00iGR2P2g00igR3f0R4g00jGFOp=2g00BMR5P1g00jgP4C8p=4g00=iR6#5R7#;R8/34R9f2R:1081%57#;R7P5108:R;1<47515X551718R7,08R<P51978R=,08A15;4X55P5P5%B8R;P;P1P=P5\5/6;g00l5R;#@R=%>;R;1=51R>%R5R?%Q5R@P51P56R6g00hA1:58RA9L56RB=K5AC8'21G@3RCP4P:g00?HRDg00m=RE'61D4:=1DEdg00>NRE=C51CERDb2b3b4X051748/989154^05P4P:O1b1GF1088,<<P8P7P8P=P;P>P?P@P0P2P2P314A6,2@%H21:5ER2/4B,2@GAPCPDb2b3b4X0513E7\9^05P4P:P1O2b1P=P;%I5P?142A,2@PCPDb2b3b413E8P4b1DJE?CMCNW6X75X85o"). Qed.

(* [comment removed for export] *)
Lemma negw_and3_aligned : forall x : word,
  bv_unsigned x mod 4 = 0 -> v_andi (v_subw (Z_to_bv 64 0) x) 3 = Z_to_bv 64 0.
Proof.
ltac2:(KReplay.run1 (kr_t_StartupAux ()) ["FPX_2"] "h01Hh11zh22H0h32H1h42H2h52H3h67__arithh74__ffh86__sat0h98__varmaph:5__with;1qh<1rh=2Hah>4__x1h?2Hmh@6__sat1hA6__sat2hB1xp;1p;2p;3p;4p;6p;8p;7p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000dR1p4p710p8P0P1p4p7210p8P0p1001Ap4p710p8p1001]p4p710R0g002:R1p4p710p8P0g002VR0p4p710R2p8p10034p4p710P2p8g003Sj19Tg004]j1HTg005;j1]Tg00;ij22Tg00Bkj1;Tg00D^j20Tg006nj1\j2OTg00FXj21Tg01Gfj2JTg0048j1@Tg00oEj2<Tg00F:j2TTg009Jj2BTg00CIj2FTg01HMj1gTg00KDj27Tg00H_j2bTg00GSj2_Tg00Cfj24Tg00H;j3[Tg00IPj2PTg00J1j1ZTg00JJj2:Tg00Jgj2NTg00Kaj2LTg00B2j2ATg00LHj2KTg00DBj2=Tg00Loj2ITg00MUj2MTg00N;j1YTg00N[j1XTg00O;j2WTg00OYj1VTg00P7j1UTg00Pbj2?Tg00QEj3rTg00RKj2qTg00Qhj3STg00``j3pTg00dBj4RTg00Rnj2oTg00SPj2nTg0090j3>Tg00T<j3fTg00T[j4eTP0j68Tg01I;j3dTP1j6ETg00ZKj1cTg01Icj3QTg01Jhj3aTg01KPj1`Tg019Lj2hTg00E>j1iTg00W:j3jTg01=cj8kTg01LKj2^Tg01:;j2lTg00dmj7mTg00BMR1f0R0g00>NR23>p=31=20p=5f1R3=>10p=6P3g00hhg00iGR4P4g00igR4P0g00jGFmp=CA>120p=DP1P3g00jgP0CRp=Gg00=iR5#9R6#9R7#9#9#9R8#9R9#HR:#]R;12:0%;7R7'0#3P1P;%\:R<P<%H8R=1O:2R>,2:12:3R?'1'JR@,O:,2:RA%@5RB#;RC,<:'TP2P;\1/B<P1%;6R6/F6R<,0A%30X11RDP11<:@100<#3X11REP1112?RF%g=RG'7,<=/1GRG%;9R9,F6RH'0PEP1%@B#@#@RB#;RE,F6RI,7FRJ%;8R8,F6'0RK/1IRL/07RMPDP110K7RN/1I/07PDP110J7RD110I/07#3X11RO1b?7RP%5?%57f3,2:RQ/07RR#5[[RS1_6E1426%5E142I[[%56RTg00laRUA[6E3UW=%5I\U^=Tf4,2:RU/P7%37RE#ZRVf5,2:RW1:W7,N710W7RX'7'6[1LW71427RYf6,2:RZ/07R[#514[7'A[1KZ71472R[f7,2:R\/07R],471=]2'A[1I\7f8,2:R^/:7#3\E1M^7f9,2:R_/07/6_\E1:_7P1f:,2:/07P1g00l5R_#YR`%X_R_1W13%V1Ra%U1RbP11?16Rc%HB5r1RB1q15R55S1g00hA1?12Rd=S15=p1BCR'C1ob4R4P0f2RBg00?HR5g00m=Re'B1n0B=>5edAf123CeReb7b9b:X>111I0R51120/7I'6^>1P0f<,2:O1b6b<b;b5b4b3b2b0b8b@bA11I?/6JP112:BRB,1IR?1007#DX11P110B7Rf,1I/07%D0X11P1P21057#DX1111I2/07,B1PfP3E810?7AdIB7EE112B/7IR?P0EEb0%DDP1P2PO1B1210?7P0EEb0PNPPPS1PB7RB1:Q7,N7/7R,6Q\VRV1LQ7RQ10U7RR#514R7'A\YRY1KU7RU147X1=X2'A\[R[1IW7RW1:Z7#3\ERX1MZ7RZ16]\\ERE1:\7R\P110^7R^P1P`P_%c1R]Pa1?18,Gc,CbP4Peb7b9b:1=68P0b6b<b;b5b4b3b2b0b89QJ8E8PMAaKI7EE10LH/07PPPSPBPVPQPYPUP[PWPXPZPEP\P1P^P1P`P_P]Pa1?19,Gc,CbP4Peb7b9b:1=69P0b6b<b;b5b4b3b2b0b89QL9E81<=J/1I/0H/0<#3e1<:G%`GE81J=F,<:/0<#3ePA1h:@E8%i6,TAPPPSPBPVPQPYPUP[PWPXPZPEP\P1P^P1P`P_P]Pa1Gdc,CbP4Peb7b9b:PTP0b6b<b;b5b4b3b2b0b89jA6E8Gk1^>3/lC=>;>eW?WBo"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma firstn_Z_to_le_bytes : forall k n z, (k <= n)%nat ->
  firstn k (Z_to_le_bytes n z) = Z_to_le_bytes k z.
Proof.
ltac2:(KReplay.run1 (kr_t_StartupAux ()) ["FPX_2"] "p'0h02Hkh14__x1h21ni001nh31kh41zh53Hk0h67__arithh74__ffh84__p1h98__varmaph:5__with;4__x2h<4cstrh=2IHh>5cstr0h?1lh@1xp;2p;1p;3p;4p;6p;<p;7p;8p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000dR1p4p710p8P0P1p4p7210p8P0p1001Ap4p710p8p1001]p4p710R0p1002:p4p710p8P0g002VR0p4p710R1p8p10034p4p710P1p8g01M?R1j22Tg003Sj1?Tg004]j1STg005;j1MTg00N[j1JTg01MYj20Tg01NVj38Tg0090j36Tg009Jj25Tg00]7R2j13Tg01O5R3j14Tg00Bkj1@Tg00KDj27Tg00DBR4j21Tg01OUj4GTg01P<j1<Tg00N;j1WTg00O;j2FTg00OYj1VTg00P7j1UTg00Pbj2ETg00RKj2DTg00V1j1RTg00``j3CTg00fYj6QTg00Rnj2PTg00SPj2LTg00T<j3NTg00T[j4OTg00YKj2ATg006nj2BTg00gaj3>Tg00ZKj1KTg00Zij4TTg0145j4_TP0j6^Tg01Paj4]Tg01:ol<\Tg012gl<ITg00dBj4[Tg00dmj7YTg00f5j8ZTg01QBR0P0g00BMR5P5P2P3P3f3R2g01Qaf2R6f1R7f0R8M<\p==P0P5P1P3P4g01RER9P2P6P7g00n:R:g00>NR;P8M<Ip=XP5P7g00jgP8C[p=:P7g00hhR<g00iGR=P=g00igR>P8g00jGFYp=9P2P<P=P=P>P6P7P8GZp=;P0P5P1P3P4P9f5R9f4R4P2P6P7P8M<Ip=H1267g00=iR3#?R1#?#?R?#SR@#MRA#JRB106798A2102736[^45^20RCX3012:710:7,5BW0X45X20%32/27P0%39RD/28f6RE#3RF107258A10F256B]0P6%34/2:12D:%49RG%@3RH'7/1;RIPD178HRDX@5RJPGO1PJP9PG155GC=155;CXP8CGPI%<E%4E,1;p-0RIg00l5RK#WRL%JKRK1F57%V5RM%U5RN1E5;RO1D53R3':,9N%R=RPPN1E5HRQ9C53RR/:O,9NPPPNP<P=P=P>P2EQC;C;1PN>R>P8P6g00?HR=g00m=R<'51L86=6=<dAN5;7COR<b7b9b:X15W811;8177HR=/1;P2[[^15^8IP8f8RI#3RO10:958A10O956B%4IROP7P6O4b6b<b5W0%38,2FPBf7RF%@?R?,A4R:'0RS1B@9RT=>A81A9?,0I9>AT56BX?B1B@4=>AS,5B107:98AFPEP7P:12F7%4FR:%47RE'1PFP:155:RSP7PE155ER@EH%3FRT%37R?'217:H17EH'1RHPTPJP:O1PJPFP:PSC=P?PJPEO1PJP7PEP@C=EHP8CGPH%<I11;O%<2%42,1;PLPKP51F56P7%K5CTPMPN1D51R1=C5Q,:R,9NPP1:31,9NC;P>P<b7b9b:X15X;511D=1176[^15^;5P8PGf;#4P2O3b6b>b<b5C_O3E^10?498AT10T456BeW0X20P8O1n0110000020111100P8O1W0X45X20X=CX30P8C]X30o"). Qed.

Lemma firstn_word_to_le_bytes : forall k n (v : word), (k <= n)%nat ->
  firstn k (word_to_le_bytes n v) = word_to_le_bytes k v.
Proof.
ltac2:(KReplay.run1 (kr_t_StartupAux ()) ["FPX_2"] "h01kh11nh21vp;1p;2p;4p;3p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000dR1p4p710p8P0P1p4p7210p8P0p1001Ap4p710p8p1001]p4p710R0p1002:p4p710p8P0p1002Vp4p710R0p8p10034p4p710P0p8g003Sj10Tg004]j13Tg005;j11Tg01M?j24Tg00;ij29Tg01Rgj48Tg00N[j17Tg01T3j22Tg01NVj35Tg0090j36Tg01QBR0g00=i#0#0#0R1#0#0#0#3R2#1f2R3f1R4'4f3R5P31924f0C8%31#1R1#712349515125436eUW2X10W0o"). Qed.

(* [comment removed for export] *)
Lemma rdn_low_bytes : forall segs m (a v : word) k, (k <= 8)%nat ->
  rdn segs m a 8 = Some (word_to_le_bytes 8 v) ->
  rdn segs m a k = Some (word_to_le_bytes k v).
Proof.
ltac2:(KReplay.run1 (kr_t_StartupAux ()) ["FPX_2"] "h01Hh12Hkh21ah31kh41mh51oh64segsh71vp;1p;2p;4p;3p;8p;6p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000dR1p4p710p8P0P1p4p7210p8P0p1001Ap4p710p8p1001]p4p710R0p1002:p4p710p8P0g002VR0p4p710R1p8p10034p4p710P1p8g00N[j18Tg003Sj11Tg004]j16Tg005;j17Tg00@Mj19Tg00]7j10Tg01M?j2<Tg01U;j45Tg01T3j22Tg01Ulj23j1:Tg0090j34Tg01NVj3;Tg009Jj2ATg01VNj4@Tg01=cj8?Tg01W]j8=TP0j6>Tg01X\#8g00=i#1#1#1R0#1#1#1#6#7R1%60#7R0#9[g01QBf0R2g00n:#0#0#0#0#0#0#0#0R3'<%80R4#9R5f5R6f4R7f3R8P3C5f2R9,23,3434P51238R:9;09R0,341287,349452X55P4P5%:4R;P;P01298P5\4/A;P9P3P8f1R8C@G?f6R;P6P7P9C5P;P6P3P7P:P9P2P8G=E>W0W1W3X71X21W4W6o"). Qed.

Lemma bytes_le_to_Z_4_small : forall v : word, bv_unsigned v < 2^32 ->
  bytes_le_to_Z (word_to_le_bytes 4 v) = bv_unsigned v.
Proof.
ltac2:(KReplay.run1 (kr_t_StartupAux ()) ["FPX_2"] "h02Hah11Hh24__x1h32H0h42Hvh57__arithh64__ffh76__sat0h86__sat1h96__sat2h:6__sat3h;8__varmaph<5__with=1vh>1zp;1p;2p;3p;4p;7p;6p;8p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000dR1p4p710p8P0P1p4p7210p8P0p1001Ap4p710p8p1001]p4p710R0p1002:p4p710p8P0g002VR0p4p710R1p8p10034p4p710P1p8g003Sj13Tg004]j1?Tg005;j1GTg00;ij22Tg00Bkj15Tg00CIj26Tg00Cfj21Tg00]7j14Tg01O5j1ETg00Jgj2DTg00D^j2CTg0090j3;Tg00okj1@Tg00B2R1j27Tg00GSj2>Tg00H;j3<Tg00N;j1WTg00N[j1VTg00O;j2UTg00OYj1TTg00P7j1NTg00Pbj2:Tg00RKj2FTg00dBj49Tg00V1j1HTg00QEj3ITg00eQj7JTg00Rnj2KTg009Jj2BTg00SPj2LTg00T<j3MTg00T[j4ATg00c;j3OTg01T3j2PTg01Y[j1QTg01ZXj2RTP0j6STg00DBj2ZTg00dmj7YTg00f5j8XTg00>NR0f0R2'Zp=0f1R3g00hhR4g00iGR5P5g00igR6P2g00jGFYp==f3P4P5P5P6f2R7P3P2GXp=8g00=iR8#3R9#3#3R:#3#3R;#3R<#?R=#G12=2%59R9%5;R>'6R?'1g00BMR@12=3RA%5:g00n:#4#4#4#4R:#E'D,69'C12=79;@2X>@%@3%0A%5<R<,69RB,1A'71>9>1109RC%0>110?[[%09RDg00laREA<9>3UW0%0?\E^0D1>9<%0<110B[\CA<9<3VEX0D%0B\E^0DP1f6,2=R1#0111Bf7,2=R1#0111?'7f4f8,2=#0f9,2=/1Bg00l5RB#W%VB1U@3%T@%N@RBP@1:@0g00jg1F@8R8C9,=BR1%H5RDPBP@P8g00kN1:@9%?;5I@C9,=BR;PDPBP4P5P5P6P1P;FJC8C81KB6P2P7g00?HRBg00m=R6'B1L27=;B6dAM@03CAb6b;b<X2@%02113?%07117?'7[[^2@P2f;,2=P7f:O3b5W3W1P3P2O2n2001000000121000000b7b8b9b:b19OA?1P:3#Q1R:3ESW4W=o"). Qed.

Lemma v_lw_small : forall v : word, bv_unsigned v < 2^31 -> v_lw v = v.
Proof.
ltac2:(KReplay.run1 (kr_t_StartupAux ()) ["FPX_2"] "h01Hh12Hah24__x1h31nh41xh52H0h67__arithh74__ffh86__sat0h96__sat1h:6__sat2h;6__sat3h<8__varmaph=5__with>2b1h?2b2h@1zhA2HvhB1mhC1vhD1yp;1p;2p;3p;4p;<p;6p;Bp;7p;8p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000dR1p4p710p8P0P1p4p7210p8P0p1001Ap4p710p8p1001]p4p710R0p1002:p4p710p8P0g002VR0p4p710R1p8p10034p4p710P1p8g003Sj16Tg004]j1=Tg005;j17Tg00;ij21Tg00Bkj1?Tg0048j1;Tg00CIR1j29Tg00CfR2j20Tg0090j33Tg00<Sj3OTg01Gfj2DTg006nj2ITg00oEj2ATg00okj1jTg00B2R3j24Tg010bR4j1GTg009Jj25Tg011@j3YTg011fj1XTg012Dj4VTg012gl<STg013Lj6RTg00GSj2CTg00H;j3@Tg00N;j1PTg00N[j1NTg00O;j2MTg00OYj1LTg00P7j1KTg00Pbj2BTg00RKj2JTg00dBj4:Tg00V1j1QTg00QEj3ETg00Rnj2iTg00SPj2hTg00T<j3gTg00T[j4fTg0145j4eTg014`j1_Tg015Ij3^Tg01[Pj1]Tg00DBj2>Tg01[mj2\Tg01\Pj3[TP0j6HTg019Lj2ZTg01]=j1`Tg01:ol<aTg01;TlBbTg00dmj7cTg00eQj7dTg00f5j8WTg00>NR0f0R5'>p=2g00ATR6g00BMR7P7P7P4P4f5R4f4R8f3R9f2R:f1R;P5M<ap=UP7P7P7P7P7P7P1P5P;P:P1P9P8P4f6f7R4f8R1f9R<MBbp=TP;g00hhR=g00iGR>P>g00igR?P5g00jGFcp=<P:P=P>P>P?P;P5Fdp=FP9P=P>P>P?P:P;P5GWp=8g00=iR=#6R@#6#6#6#6RA#6RB#=RC#7RD11C5%?@R@%;=#;#;#;RE#?RF'9RG'0%75RH%7;RIP3%7:?3;5119:119;537RJ[11:;11:5537%79?3:;[RK%78?39:\JAO:;5P5n2001000000120000000W?W>X36PK^?I^>H^36P5PC%=ARA11C:RH'DRI,ICRKP:P71ACI11C9R99375X@7%j:%2H%?BRB,9@RJ,0H'4P7P91AC511C8537X@7%29RH%GCRL,9@RM,09RN'4109JRO,4HPHPNPHPOp-0/5H9YHHP7P7P2P5X47ROP210;5#XXD7X47P9P91579PMPJPOPOPOP7P7g01<:19;5CV,57XB7X37P@P@157@PLPBPOPO%G5,57X46PCPB157BEUM:TM<SER1C@BR6100@RO%2B100J[[RL%2@RMg00laR2A@@B;UW1RB%2J\2^1MRN1C@FRP%2F100G[\OROA@@F;V2X1MRF%2G\2^1MRMP311C4R4#2R2104JR411C1R1#2101J'4P811C<#2R<f:,1C/0JRQg00l5RR#PRS%NRRR1M7;RT%L7RU%K7RVP71B70g00jgRW1J7=R=C:,<VRX%Q>R>PVP7P=g00kNRY1B7@R@%=E5E7REC:,<VRZP>P7P=PYAE7@CC:,<V9FVXC8C81iV?R?P5P:g00?HR@g00m=RY'51h5:=3@YdAg70;CfR0b7b<b=X27%25RY10;GR@%2:10:J'4[[^27P5f<,1CP:f;O3RJb6W5W0P;P5O2n2001000000121000000b8b9b:b;Ce%_C,09,4He9^C91DA9PPPOPFPMP6PLPBPNP3P2P4%]GR4/>1101G'4P8PSPRPTPUPVPXP>PVPZP>P71\7EPWP=C:,<V=FVZC8C8P?P0b7b<b=X271>4:10:G'4\@\Y^27PJb6X5QX0<P;P5O2n2001000000121000000b8b9b:b;9[A9EHb011CK1ZCIEHO4b0%`;=3D;eWAWCo"). Qed.

(* [comment removed for export] *)
Lemma v_add_lit_r : forall (x : word) (k : Z), 0 <= k < 2^64 ->
  v_add x (Z_to_bv 64 k) = Z_to_bv 64 (bv_unsigned x + k).
Proof.
ltac2:(KReplay.run1 (kr_t_StartupAux ()) ["FPX_2"] "h04__x1h11Hh22H0h32Hah47__arithh54__ffh66__sat0h76__sat1h88__varmaph95__with:2Hkh;1kh<1xh=1zp;1p;2p;3p;4p;6p;7p;8p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000dR1p4p710p8P0P1p4p7210p8P0p1001Ap4p710p8p1001]p4p710R0p1002:p4p710p8P0g002VR0p4p710R1p8p10034p4p710P1p8g003Sj12Tg004]j1TTg005;j1CTg00Bkj1<Tg00CIj2MTg00Cfj21Tg00B2R1j2BTg00;ij25Tg00KDj24Tg006nj23Tg0090j36Tg009Jj27Tg00GSj2STg00H;j3RTg00N;j1QTg00N[j1LTg00O;j2KTg00OYj1HTg00P7j1FTg00Pbj29Tg00RKj2ETg00dBj48Tg00V1j1DTg00Rnj2ATg00SPj2GTg00T<j3@Tg00T[j4ITg00QEj3JTg01]oj3?TP0j6>Tg01^jj2NTg00DBj2=Tg00dmj7OTg00f5j8PTg00>NR0f0R2'=p=0f1R3g00hhR4g00iGR5P5g00igR6P2g00jGFOp=;f3R7P4P5P5P6f2R4P3P2GPp=:g00=iR8#2R9#2#2#2#2#2R:#TR;#CR<g00BMR=%02R>%<9R9%<:R:'MR?,12R@'BP=P315;7RA/42,3;14A4,3;56<X==15;4/43,3;RA,7<13;3RB,5;1S9:RC1109%0:110?[[RD%09REg00laRFAR9:3UW3R:%0?\F^3EREP1%07RF117?R7f4RG#0P4f5#0RHf6/1?RIg00l5RJ#QRK%LJRJ1K=3RL%H=RM%F=RNP=19=0g00jg1E=8R8C8,;NRO%D5R5POC:1AN6R6P2P4g00?HROg00m=RP'71G24=6OPdA@=03CIR0b5b8b9X0=%03\>^0=P2f8R>P4O2b4W2W1P3P2O2n2001000000120000000b6b7PCPDP:PEP1PFP711G?P4PKPJPLPMPNP=P8g00kN19=9=J=;C8,;NRNP5PNC:P6P0b5b8b9X0=113?\@^0=P2P>P3O2b4X2IX1HP3P2O2n2001000000120000000b6b75?3E>1N4B=6<AeW:W;W<o"). Qed.

Lemma v_add_lit_l : forall (x : word) (k : Z), 0 <= k < 2^64 ->
  v_add (Z_to_bv 64 k) x = Z_to_bv 64 (bv_unsigned x + k).
Proof.
ltac2:(KReplay.run1 (kr_t_StartupAux ()) ["FPX_2"] "h04__x1h11Hh22H0h37__arithh44__ffh56__sat0h66__sat1h78__varmaph85__with92Hah:4__x2h;2Hkh<1kh=1xh>1zp;1p;2p;3p;4p;8p;6p;7p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000dR1p4p710p8P0P1p4p7210p8P0p1001Ap4p710p8p1001]p4p710R0p1002:p4p710p8P0g002VR0p4p710R1p8p10034p4p710P1p8g003Sj13Tg004]j1YTg005;j1HTg00Bkj1>Tg00CIj2PTg00Cfj22Tg00B2R1j2GTg00;ij24Tg00KDj20Tg006nj26j1@Tg0090j35Tg009Jj2?Tg00GSj2VTg00H;j3UTg00N;j1OTg00N[j1NTg00O;j29Tg00ZKj1MTg00Zij4LTg00OYj1KTg00P7j1FTg00RKj2;Tg00``j3:Tg00dBj47Tg00Rnj2ETg00SPj2DTg00T<j3ITg00T[j4JTg01=cj8CTg00Pbj2=Tg00V1j1BTg00QEj3ATg01]oj3QTP0j6RTg01^jj2STg00DBj2TTg00dmj7XTg00f5j8WTg00>NR0f0R2'Tp=1f1R3g00hhR4g00iGR5P5g00igR6P2g00jGFXp=8f3R7P4P5P5P6f2R4P3P2GWp=<g00=iR8#3R9#3#3#3#3#3R:#YR;#HR<g00BMR=%12R>%>9R?%>:R:'PR@,22RA'GP=P314;7RB,02,6;10B4,6;55<X>=P=P<%@;RBPB14;4RC,0310C3RCP<\=/?B1V?:RB120?%1:120@[[RD%1?REg00laRFAU?:3UW9R:%1@\F^9EREP1%17RF127@R7f4RGf5RH,4;RI'010IG55=P4%1HRHf6/2@RIg00l5RJ#ORK%NJRJP=19=4P3%M=CL%K=RL%F=RMP=1;=8R81;=9R95:=g00hAA:=98C7'81EM6R6P2P4g00?HR9g00m=RN'?1D24=59NdAI=03CJRNb4b7b8X0=X:=1023103255=^0=^:=P2f9,4;f8R9O2b3W2W1P3P2O2n2001000000120000000b5b6GC16;3RO,4;PBPDP:PEP1PFP7%1GP4PKPJ19=3RPPLPMP=1==0g00jgP8C7,8MR0%B5R5P0C<P6PNb4b7b8X0=%13\>^0=P2P9P4O2b3X2IX1HP3P2O2n2001000000120000000b5b6PBPDP:PEP1PFP712G@P4PKPJPPPLPMP=P8g00kN1==?=A=;C7,8MRMP5PMC<P6PNb4b7b8X0=123@\A^0=P2P9P3O2b3X2IX1HP3P2O2n2001000000120000000b5b65Q3ER1SO416;C55<eW;W<W=o"). Qed.

(* [comment removed for export] *)
Lemma v_slli_lit : forall z sh, 0 <= z -> 0 <= sh -> z * 2^sh < 2^64 ->
  v_slli (Z_to_bv 64 z) sh = Z_to_bv 64 (z * 2^sh).
Proof.
ltac2:(KReplay.run1 (kr_t_StartupAux ()) ["FPX_2"] "h06__sat3h12Hah24__x1h37__arithh46__sat0h56__sat1h66__sat2h71zh84__ffh98__varmaph:5__with;4__x2h<1ah=2Hbh>3Hshh?2Hzh@2shp;1p;2p;3p;4p;5p;6p;8p;7p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000dR1p4p710p8P0P1p4p7210p8P0p1001Ap4p710p8p1001]p4p710R0p1002:p4p710p8P0g002VR0p4p710R1p8p10034p4p710P1p8g003Sj10Tg00Bkj1:Tg00CIj22Tg00Jgj28Tg00Cfj21Tg004]j1WTg005;j1VTg006nj1Tj2ATg00;ij2LTg00Ykj2KTg009Jj2?Tg0090j3=Tg00GSj2HTg00H;j3GTg00N;j1]Tg00N[j1\Tg00O;j2ETg00OYj1YTg00P7j1XTg00Pbj2CTg00RKj2BTg00V1j1UTg00Rnj2STg00SPj2QTg00T<j3PTg00T[j4NTg00\Vj2DTg01_]j4MTg01`>j2OTg00]Vj2;Tg00]7j1>Tg01`gj2JTg00^hj39Tg00_Qj2lTg00gaj3kTg00ZKj1jTg00Zij4iTg01aPj5gTg00QEj3fTg0048j1`Tg00`=j3_Tg01]oj3^TP0j6ITg00aCj3bTg01=cj8cTg01b4j2dTg00DBj2eTg00dBj4FTg00dmj7[Tg00f5j8ZTg01bhj3hTg00>NR0f0R1'ep=5%01#0#0#0p=ag00BMR2f1R3g00jgP1CFp=@P3g00hhR4g00iGR5P5g00igR6P1g00jGF[p=7f3R7P4P5P5P6f2R8P3P1GZp=4Ah231p=3%01#0p=R%01#0#0#0#0#0#0#0p=6P2P3g00kNP1CFp=<%53R9g00=iR:#0R;#:R</28,87%0;#aR;#:R=,2<R>'1P2%W;R?#VR@%T?RAPAf4RB,A?RC,L?RD/K7RE12<7RF,8BRGP@\2/?AP218DFf5RF12<BRA'8RH9=21X72P2PB181A==2HX721?2GPD1H<7RH110<RA%5B12<F,10[[RF%5<RIg00laRJf6RK=G<3UW1RL12<K#5\J^1IRM1H<=RN%5=110>[\AROAG<=3VJX1IR=%5>\JRJ^1IRPPBP1PKO2X<ARQf8RR,2<,10^<ARSg00l5RT#]RU%\TRV1E23%Y2RW%X2RX1C20RY1B2:RZ'@,7XR[%U5R\P[C41SX6R[P1P8g00?HR]g00m=R^'?1Q18==]^dAP203CNR^b8b9b:X22R]%51P9[^22R_P1f:R`PRO2b3b0b4b5b6b0PHPFPLPMPNPOP=PPPQPSP2%::,D2P:1D20CM,O2RRg00n:Ra,;2Rb%>aRa#>Rc,;2Rd'3%R;#6#6#6#6#6#6#6#:,J2/3d=92b592'31;2a,3R1J2<%>c,;2/3b'313bb592592592g00nY'l=kTUPVP2%j2P31E28CiPWPXPX1C2<RW,@Y,7XP\PXPXP4P5P5P6DgP\Af2W?R6,@Y,7XC4C4P\PXPX1<YW,7XP\%`:,B2R:,<Y,7XC4P\PXA_2Z:/<6,7XP\1<Z6,7XC4C4C4P[P^b8b9b:X22X;2PJ\I1107\A1887/1>117>[[[^22^;2P1f9R>,2<P`P8P3PKO5b3b0b4b5b6b05^BEIPEPHPFPLPMPNPOP=PPPQPSP]P_P1P>f7O2b3b0b4b5b6b09bD7EIGc1dC71A?G5=@eW=X>9W?X@2X72o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_sub_bv : forall (l1 l2 : list reg) (r : reg),
  forallb (fun x => existsb (fun y => bv_eqb x y) l2) l1 = true -> In r l1 -> In r l2.
Proof.
ltac2:(KReplay.run1 (kr_t_StartupAux ()) ["FPX_2"] "p'0h01yh11Hh22Hxh32b1h42b2h52l2h61xh71nh81rh93Hinh:2l1h;3Hxyh<1mh=2H0h>3Hl1h?2IHh@3IH2hA1ei001bp;1p;3p;2p;6p;4p;5p-1R0g01cQR1p4p710p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000dR2p4p710p8P0P2p4p7210p8P0g01chR0p4p710p8p1001]p4p710R2g002:R3p4p710p8P2p1002Vp4p710R2p8p10034p4p710P2p8g003Sj1OTg0048j1NTg004]j1GTg005;j19Tg00N[j1MTg006Aj31Tg001Aj34TP0j36TP1j32Tg00N;j1CTg01dDj2=Tg00gaj3:Tg01>aj2ATg00B2R1j2<Tg01dcj2LTg0090j33TP3j6?Tg01eDj2>Tg016[R3j2;Tg01eaj2ITg00;ij28Tg00<Sj3FTg01??j2@Tg01fAj2ETg01faj4HTg01g=j3DTg01gWj3JTg01h1j6Kj5BTg00?HR0f0R2g00m=R433p=0f2R5f1R6;42=304p=5g00BMR7?362p=7g00=i#O#N#GR8#9R9#MR:P9A1862X09R;=495X69R<=695#0f3R=9296A295=R>[[^89^5:R?X::%C9R@969<#0A296@1=>2W9W1X89X5:f4R>=:9=969<#0f5R<=:9>9296P11A62#0%05RA%06RB'<[RC%02RD,<B1A56#0RE[%0=RF/<A\E1L62P6n2001000000120000000X40X30PC^40^30P2f8RC=182X09=49>REA49;<X69f6RG569RHP5O3%0E%0H'<P1f9RH=182X09=59<A49;GX69f7RE569#0A29<GP2f;RI=182X09=59EA49;HX69f:R;569#0P3f<RJ=39CA29CIA29H;PGf==39HP9f>A292JX89P9f@RK=182X09RL=592A29K6]2X5:f?=182X09=59@P0A49L@P0p-0P2g00m]RLg00lan0110000020000XA0g00>lP4P2E?PLA29K@/=2b1W2fARK=182X09=592A29K6]2fB=182X09A:956559P11>62#01;AB[RK1;BD1>56#0RD[1;FA\D1I62P6n2001000000120000000X40X30PK^40^30P2fC=18>R0fDRK=182X09=49=RDP6O3%00%0D';P3A18K<#0fERK=182X09=59>A:9G<929KP2A18KG#0fFRK939ER3A29KGRGP9PKPEg00ATRE%92RD%96R0P1%95?36218=518=6'7RF[18561852'7%9=?356[RA%9>?3=5\FAF562P2n2001000000120000000W4W3W7PA^40^3D^7EP2P8fGPCP11@62#01756[R117621@56#0RC[17=5\C1E62P6n2001000000120000000X<7X77P1^<7^77P2fH,88R7188HR1P5O31771P2b;b1O4b1CH3DW;P2O1A18K2X09=59<P<P2O19J3GW2P2O1n200100000021000010000b2b1W2W@X5:X09PIP=EKP;P2E?W1P2O1A29HJPJPIP;P5P2O4W9P2O1n200100000021100010000W>W2P6P2O2n2001000000121000000b1b=W9W1X89X5:X??X::X69P2DBW:o"). Qed.

Lemma Z_to_bv_u_eq : forall (a : word) (z : Z), z = bv_unsigned a -> Z_to_bv 64 z = a.
Proof.
ltac2:(KReplay.run1 (kr_t_StartupAux ()) ["FPX_2"] "h01zh11Hh22b1h32b2h41nh51ap;1p;2p;3p;6p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000dR1p4p710p8P0P1p4p7210p8P0p1001Ap4p710p8p1001]p4p710R0p1002:p4p710p8P0g002VR0p4p710R1p8p10034p4p710P1p8g003Sj13Tg004]j1;Tg005;j12Tg00;ij20Tg0090j31Tg006nj25Tg00<Sj3:Tg00oEj29Tg01hSj28Tg015Ij37Tg019Lj26TP0j64Tg00=i#3#3#3#3#3#3#;R0#2R1g00BMR2f0R3f1R4,00512P2f2R5,001503f3R6511X02g00ATR1%23R7%24R8g00B2%25?14310651064512R9[10541053512%26?154[R:f4R;#2?165\9A:543P3n2001000000120000000W3W2W4P:^38^27^41P3P01006R1,50R7P6P21901100;9123X021806970110071601E4O4b1P4P3E4W1W0W5o"). Qed.

Lemma Z_to_bv_u_eq_sym : forall (a : word) (z : Z), z = bv_unsigned a -> a = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_StartupAux ()) ["FPX_2"] "h01Hh11ah21zp;1p;2p;3p;4p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000dR1p4p710p8P0P1p4p7210p8P0p1001Ap4p710p8p1001]p4p710R0p1002:p4p710p8P0p1002Vp4p710R0p8p10034p4p710P0p8g003Sj10Tg004]j17Tg005;j12Tg00;ij21Tg0090j36Tg006nj25Tg01iFj33Tg01faj44Tg00=i#0#0#0#0#0#0#7R0#2R1g00BMR2f0R3f1R4,10562P11504f2R0A3043C4W0W2W1o"). Qed.

End FPX_2.

End StartupAux.
From Stdlib Require FunctionalExtensionality. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
Module ZStores.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.MemSplit.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


Definition zeros (n : nat) : list byte := repeat (Z_to_bv 8 0) n.

Fixpoint zstores (m : word -> option byte) (d : word) (ws : list (Z * nat)) : word -> option byte :=
  match ws with
  | [] => m
  | (o, n) :: ws' => zstores (wbytes m (Z_to_bv 64 (bv_unsigned d + o)) (zeros n)) d ws'
  end.

Definition covers_off (i : Z) (on : Z * nat) : bool :=
  (fst on <=? i) && (i <? fst on + Z.of_nat (snd on)).

Definition ws_inb (ws : list (Z * nat)) (N : Z) : bool :=
  forallb (fun on => (0 <=? fst on) && (fst on + Z.of_nat (snd on) <=? N)) ws.

Fixpoint iota_Z (i : Z) (k : nat) : list Z :=
  match k with O => [] | S k' => i :: iota_Z (i + 1) k' end.

Definition ws_cover (ws : list (Z * nat)) (N : nat) : bool :=
  forallb (fun i => existsb (covers_off i) ws) (iota_Z 0 N).

Lemma forallb_In : forall {A} (f : A -> bool) l x, forallb f l = true -> In x l -> f x = true.
Proof.
  induction l as [|y l IH]; intros x H Hin; [contradiction|].
  cbn in H. apply andb_true_iff in H as [Hy Hl].
  destruct Hin as [<-|Hin]; [exact Hy | apply IH; assumption].
Qed.

Lemma iota_Z_In : forall k i z, i <= z < i + Z.of_nat k -> In z (iota_Z i k).
Proof.
  induction k as [|k IH]; intros i z Hz; [lia|].
  cbn. destruct (Z.eq_dec i z); [left; assumption | right]. apply IH. lia.
Qed.

Lemma existsb_false_forall : forall {A} (f : A -> bool) l,
  existsb f l = false -> forall x, In x l -> f x = false.
Proof.
  induction l as [|y l IH]; intros H x Hin; [contradiction|].
  cbn in H. apply orb_false_iff in H as [Hy Hl].
  destruct Hin as [<-|Hin]; [exact Hy | apply IH; assumption].
Qed.

Lemma existsb_true_exists : forall {A} (f : A -> bool) l,
  existsb f l = true -> exists x, In x l /\ f x = true.
Proof.
  induction l as [|y l IH]; intros H; [discriminate|].
  cbn in H. apply orb_true_iff in H as [Hy|Hl].
  - exists y. split; [left; reflexivity | exact Hy].
  - destruct (IH Hl) as [x [Hin Hx]]. exists x. split; [right; exact Hin | exact Hx].
Qed.

Lemma length_zeros : forall n, length (zeros n) = n.
Proof. intro n. apply repeat_length. Qed.

Lemma nth_zeros : forall n k, nth k (zeros n) (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof. intros n k. unfold zeros. apply nth_repeat. Qed.

Lemma rdn_wbytes_zeros_in : forall segs m (d a : word) (N n : nat),
  bv_unsigned d + Z.of_nat N < 2^64 ->
  bv_unsigned d <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= bv_unsigned d + Z.of_nat N ->
  rdn segs (wbytes m d (zeros N)) a n = Some (zeros n).
Proof.
  intros segs m d a N n Hnw Hlo Hhi. unfold zeros at 2. apply rdn_const; [lia|].
  intros x Hx. rewrite wbytes_inside by (rewrite length_zeros; lia).
  f_equal. apply nth_zeros.
Qed.

Lemma bytes_le_to_Z_zeros : forall n, bytes_le_to_Z (zeros n) = 0.
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [zeros repeat bytes_le_to_Z].
  fold (zeros n). rewrite IH. reflexivity.
Qed.

Section Cover.
  Variable d : word.
  Variable N : Z.
  Hypothesis Hnw : bv_unsigned d + N < 2^64.

  Lemma zstores_miss : forall ws m (x : word),
    ws_inb ws N = true ->
    (forall on, In on ws -> covers_off (bv_unsigned x - bv_unsigned d) on = false) ->
    zstores m d ws x = m x.
  Proof.
    induction ws as [|[o n] ws IH]; intros m x Hinb Hno; [reflexivity|].
    cbn [zstores]. cbn [ws_inb forallb fst snd] in Hinb.
    apply andb_true_iff in Hinb as [Hon Hinb]. apply andb_true_iff in Hon as [Ho Hn].
    apply Z.leb_le in Ho. apply Z.leb_le in Hn.
    rewrite IH; [| exact Hinb | intros on Hin; apply Hno; right; exact Hin].
    pose proof (Hno (o, n) (or_introl eq_refl)) as Hc. cbn [covers_off fst snd] in Hc.
    pose proof (u64_range x). pose proof (u64_range d).
    apply wbytes_outside.
    - rewrite length_zeros. rewrite u_Z2bv by lia. lia.
    - rewrite length_zeros. rewrite u_Z2bv by lia.
      apply andb_false_iff in Hc as [Hc|Hc]; [apply Z.leb_gt in Hc | apply Z.ltb_ge in Hc];
        cbn [fst snd] in Hc; lia.
  Qed.

  Lemma zstores_hit : forall ws m (x : word),
    ws_inb ws N = true ->
    (exists on, In on ws /\ covers_off (bv_unsigned x - bv_unsigned d) on = true) ->
    zstores m d ws x = Some (Z_to_bv 8 0).
  Proof.
    induction ws as [|[o n] ws IH]; intros m x Hinb Hex.
    { destruct Hex as [on [[] _]]. }
    cbn [zstores]. cbn [ws_inb forallb fst snd] in Hinb.
    apply andb_true_iff in Hinb as [Hon Hinb]. apply andb_true_iff in Hon as [Ho Hn].
    apply Z.leb_le in Ho. apply Z.leb_le in Hn.
    destruct (existsb (covers_off (bv_unsigned x - bv_unsigned d)) ws) eqn:E.
    - apply IH; [exact Hinb|]. apply existsb_true_exists. exact E.
    - rewrite zstores_miss; [| exact Hinb | apply existsb_false_forall; exact E].
      destruct Hex as [on [[<-|Hin] Hc]].
      2:{ rewrite (existsb_false_forall _ _ E on Hin) in Hc. discriminate. }
      cbn [covers_off fst snd] in Hc. apply andb_true_iff in Hc as [Hc1 Hc2].
      apply Z.leb_le in Hc1. apply Z.ltb_lt in Hc2. cbn [fst snd] in Hc1, Hc2.
      pose proof (u64_range x). pose proof (u64_range d).
      rewrite wbytes_inside by (rewrite length_zeros, u_Z2bv by lia; lia).
      f_equal. apply nth_zeros.
  Qed.

  Lemma zstores_cover : forall ws m (n : nat),
    Z.of_nat n = N ->
    ws_inb ws N = true ->
    ws_cover ws n = true ->
    zstores m d ws = wbytes m d (zeros n).
  Proof.
    intros ws m n HnN Hinb Hcov. apply functional_extensionality. intro x.
    pose proof (u64_range x). pose proof (u64_range d).
    destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned d)) as [Hlt|Hge].
    { rewrite wbytes_outside by (rewrite length_zeros; lia).
      apply zstores_miss; [exact Hinb|]. intros [o k] Hin.
      pose proof (forallb_In _ _ _ Hinb Hin) as Hb. cbn [fst snd] in Hb.
      apply andb_true_iff in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1.
      cbn [covers_off fst snd]. apply andb_false_iff. left. apply Z.leb_gt. cbn [fst snd]. lia. }
    destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned d + N)) as [Hin|Hout].
    - rewrite wbytes_inside by (rewrite length_zeros; lia). rewrite nth_zeros.
      apply zstores_hit; [exact Hinb|].
      pose proof (forallb_In _ _ _ Hcov (iota_Z_In n 0 (bv_unsigned x - bv_unsigned d) ltac:(lia))) as He.
      apply existsb_true_exists in He. exact He.
    - rewrite wbytes_outside by (rewrite length_zeros; lia).
      apply zstores_miss; [exact Hinb|]. intros [o k] Hin'.
      pose proof (forallb_In _ _ _ Hinb Hin') as Hb. cbn [fst snd] in Hb.
      apply andb_true_iff in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb2.
      cbn [covers_off fst snd]. apply andb_false_iff. right. apply Z.ltb_ge. cbn [fst snd]. lia.
  Qed.
End Cover.

End FPX_1.

End ZStores.
Module StartupTac.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Export OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.WalkTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.MemSplit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.StartupAux OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.ZStores.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_StartupTac () := "C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List7existsbC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib7Mh_00417ZStores:forallb_InC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indc59OSSVerify5KrLib7Mh_00417ZStoresDexistsb_false_forallC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00417ZStoresCexistsb_true_existsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilI47Corelib4Init9Datatypes4list00I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim<msteps_transC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0041:StartupTac3bwdC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac pin :=
  repeat match goal with
         | H : getr ?rs ?r = _ |- context [getr ?rs ?r] => rewrite !H
         end.

(* [comment removed for export] *)
Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with
             | context [Z_to_bv 64 _] => fail
             | _ => rewrite (u_Z2bv z) by lia
             end
         end.

(* [comment removed for export] *)
Ltac zlit :=
  repeat match goal with
         | |- context [Z_to_bv 64 ?z] =>
             lazymatch z with
             | Z0 => fail | Zpos _ => fail | Zneg _ => fail
             | _ => check_closed_term z; let z' := eval vm_compute in z in change z with z'
             end
         end.

(* [comment removed for export] *)
Ltac region_side :=
  unfold win_lo; rewrite ?stack_max_size_val, ?length_N_to_le_bytes, ?length_zeros, ?repeat_length;
  cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul]; imm_norm; unorm; lia.

(* [comment removed for export] *)
Ltac addr_norm :=
  gres; pin; imm_norm; rewrite ?v_addi_0; unfold v_addi, v_add; unorm; zlit.

(* [comment removed for export] *)
Ltac vclose_fin :=
  first [ reflexivity | f_equal; lia | apply at_self | symmetry; apply at_self
        | apply Z_to_bv_u_eq; lia | apply Z_to_bv_u_eq_sym; lia | bveq ].
Ltac vclose :=
  gres; pin; imm_norm;
  first [ reflexivity
        | unfold v_addi, v_add; unorm; zlit; vclose_fin
        | rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l; first [ reflexivity | vclose_fin ]
        | rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l; unfold v_addi, v_add; unorm; zlit; vclose_fin ].

(* [comment removed for export] *)
Ltac sn F D := stepn F D; pin.
Ltac sv F D v := stepiv F D v vclose.

(* [comment removed for export] *)
Ltac blit :=
  repeat match goal with
         | |- context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] =>
             lazymatch z with
             | Z0 => change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 0)
             | Zpos _ => let z' := eval vm_compute in (z mod 256)%Z in
                         change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 z')
             end
         end.

(* [comment removed for export] *)
Ltac push_store :=
  blit;
  first [ rewrite wbytes_cmem_win by region_side
        | rewrite wbytes_cmem_data by region_side
        | idtac ].

(* [comment removed for export] *)
Ltac stw F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Store SZ8 _ _ _, _) =>
        eapply step_sd_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | vclose | vclose | oktac ]
    | decode_any _ = Some (Store SZ4 _ _ _, _) =>
        eapply step_sw_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | vclose | vclose | oktac ]
    | decode_any _ = Some (Store SZ2 _ _ _, _) =>
        eapply step_sh_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | vclose | vclose | oktac ]
    | decode_any _ = Some (Store SZ1 _ _ _, _) =>
        eapply MmapSim.step_sb_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | vclose | vclose | reflexivity | oktac ]
    end
  | step_simpl; push_store ].

(* [comment removed for export] *)
Ltac ok_sub Hok :=
  store_ok_peel; eapply store_ok_sub; [ | exact Hok | | ];
  rewrite ?length_N_to_le_bytes, ?length_zeros; unorm; lia.

(* [comment removed for export] *)
Ltac ok_win HJ :=
  apply store_ok_cmem_win; [ repeat apply wfJ_wbytes; exact HJ | region_side | region_side ].

(* [comment removed for export] *)
Ltac ok_data :=
  apply store_ok_cmem_data;
  lazymatch goal with |- ?g => check_closed_term g; vm_compute; reflexivity end.

(* [comment removed for export] *)
Ltac ld_step F D bsv vv rdtac valtac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Load SZ8 _ _ _ _, _) => eapply step_ld with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ4 true _ _ _, _) => eapply step_lw with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ4 false _ _ _, _) => eapply step_lwu with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ2 true _ _ _, _) => eapply step_lh with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ2 false _ _ _, _) => eapply step_lhu with (bs := bsv) (v := vv)
    end;
    [ exact F | reflexivity | exact D | addr_norm; rdtac | valtac ]
  | step_simpl ]; vnorm; pin.

(* [comment removed for export] *)
Ltac lb_step F D bb rdtac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Load SZ1 false _ _ _, _) => eapply step_lbu with (b := bb)
    | decode_any _ = Some (Load SZ1 true _ _ _, _) => eapply step_lb with (b := bb)
    end;
    [ exact F | reflexivity | exact D | addr_norm; rdtac ]
  | step_simpl ]; vnorm; pin.

(* [comment removed for export] *)
Ltac peel := repeat (rewrite rdn_wbytes_out by region_side).

(* [comment removed for export] *)
Ltac rd_img L := addr_norm; rewrite rdn_cmem_data by region_side; peel; exact L.

(* [comment removed for export] *)
Ltac rd_hit8 :=
  addr_norm; peel;
  lazymatch goal with |- rdn _ (wbytes _ ?a' _) ?a _ = _ =>
    first [ constr_eq a a' | replace a with a' by (first [f_equal; lia | bveq]) ] end;
  apply rdn_wbytes_hit8; unorm; lia.

(* [comment removed for export] *)
Ltac in_list := cbn [In]; repeat first [ left; reflexivity | right ].
Ltac solve_regs_agree :=
  repeat (apply regs_agree_upd; [ in_list | ]); apply regs_agree_refl.

(* [comment removed for export] *)
Ltac incl_list :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [In] in Hr;
  repeat (destruct Hr as [<-|Hr]; [in_list|]); destruct Hr.
Ltac regs_agree_weaken Hag :=
  eapply regs_agree_mono; [| exact Hag]; incl_list.

Ltac notin_list :=
  cbn [In]; intros HH; repeat (destruct HH as [HH|HH]; [apply bv_eq in HH; cbv in HH; discriminate HH|]); exact HH.

(* [comment removed for export] *)
Ltac carry Hag H r T :=
  pose proof (Hag r ltac:(notin_list)) as T;
  repeat first [ rewrite getr_same in T by reg_neq_tac | rewrite getr_other in T by reg_neq_tac ];
  rewrite ?H in T.

(* [comment removed for export] *)
Ltac ra_chain :=
  first [ apply regs_agree_refl
        | apply regs_agree_upd; [ in_list | ]; ra_chain
        | match goal with
          | Hag : regs_agree _ _ ?r |- regs_agree _ _ ?r =>
              eapply regs_agree_trans; [ | regs_agree_weaken Hag ]; ra_chain
          end ].
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition bwd (segs : list Segment) (G : machine_state -> Prop) : Prop :=
  forall st st', msteps segs st st' -> G st' -> G st.

Lemma bwd_msteps : forall segs tgt, bwd segs (fun st => msteps segs st tgt).
Proof.
ltac2:(KReplay.run1 (kr_t_StartupTac ()) ["FPX_1"] "h02sth12H1h22H2h34segsh43st'h53tgtp;1p;3p;6p;2p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000dR2p4p710p8P0P2p4p7210p8P0p1001Ap4p710R0p8p1001]p4p710R2p1002:p4p710R3p8P2p1002Vp4p710R2p8p10034p6051000R4P1p8P4P3p8P4p10043p4p710R5p8P4P0p8p1004Up6051000R4P1p8P4P3p8P4P5p8P4P0p8p1005^p6051000R4P1p8P4P5p8P4P0p8p1006fp4p710P2p8g007Ej13Tg007ej30Tg008aj62Tg009aj21Tg00:\#3g00;[R2f3R0f1R4f0R530f4R1?040f5P0f2R0P1P4P5E2W2W1X42X02A0054X02,14eW5W3o"). Qed.
End FPX_1.


(* [comment removed for export] *)
Ltac gsteps HG := eapply HG.

End StartupTac.
Module RefLayout.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.ArgvEnv.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_RefLayout () := "C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List7existsbC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib7Mh_00417ZStores:forallb_InC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indc59OSSVerify5KrLib7Mh_00417ZStoresDexistsb_false_forallC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00417ZStoresCexistsb_true_existsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01C47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C47Corelib4Init5Logic7f_equalC47Corelib5Lists7ListDef6firstnC45stdpp9bitvector;definitions6bv_addC49OSSVerify5KrLib8PropExec:word_add_0C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec:rdn_firstnC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecEnat_to_word_add_mergeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C47Corelib4Init5Logic9False_indC47Corelib4Init9Datatypes7nat_indC47Corelib5Lists7ListDef5skipnC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappK47Corelib4Init9Datatypes3nat01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C56Stdlib6ZArith4Znat5Nat2Z8inj_succI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init5Logic4True01C49OSSVerify5KrLib8PropExec9word1_natC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00C46Stdlib5Lists4List9app_nil_rC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:firstn_allC47Corelib4Init3Nat3subC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagC46Stdlib5Lists4List:firstn_appc59OSSVerify5KrLib7Mh_00419RefLayout@firstn_app_exactC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9skipn_allC46Stdlib5Lists4List9skipn_appc59OSSVerify5KrLib7Mh_00419RefLayout?skipn_app_exactC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatC56Stdlib5Arith8PeanoNat3Nat7sub_0_rc59OSSVerify5KrLib7Mh_00419RefLayout=skipn_repeat'C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03c59OSSVerify5KrLib7Mh_00419RefLayout>firstn_repeat'C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula05C56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC46Stdlib5Lists4List9app_assocc59OSSVerify5KrLib7Mh_00419RefLayoutCrepeat_firstn_skipnC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout:build_auxvC47Corelib4Init9Datatypes3sndC4ELinuxProcessSemantics?LinuxProcessSem6BvBase8word_le8K47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout<auxv_entriesc59OSSVerify5KrLib7Mh_00419RefLayout@build_auxv_wordsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout:auxv_bytesc59OSSVerify5KrLib7Mh_00419RefLayout:auxv_wordsC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00c59OSSVerify5KrLib7Mh_00417ArgvEnv6bsb_nwC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC4ELinuxProcessSemantics?LinuxProcessSem3Run?total_arg_bytesI47Corelib5Lists7ListDef6Forall00C45stdpp9bitvector;definitions7Z_to_bvC47Corelib4Init5Logic3notC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei>path_has_slashC4ELinuxProcessSemantics?LinuxProcessSem2Fs8path_eqbC46Stdlib5Lists4List2tlC46Stdlib9micromega;ZifyClasses9and_morphC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathK47Corelib4Init9Datatypes4bool02C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei;dotdot_pathC47Corelib4Init3Nat3mulC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout=at_random_ptrC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout<string_addrsC49OSSVerify5KrLib8PropExecCtotal_arg_bytes_natC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout?flatten_stringsC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z6to_natC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9ed_randomC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout?at_random_bytesI47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01C49OSSVerify5KrLib8PropExecAstring_addrs_pairC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec?cat_string_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec<cat_env_baseC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9auxv_sizeC46Stdlib5Lists4List:length_appC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr05C49OSSVerify5KrLib8PropExecGlength_string_addrs_fstC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecClength_flat_map_le8C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec@length_n_to_le_8C1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC49OSSVerify5KrLib8PropExecDread_at_offset_imageC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunAentry_stack_imageC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout<stack_to_memc59OSSVerify5KrLib7Mh_00419RefLayout:bsb_decompC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00419RefLayout:lay_bsb_nwC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00419RefLayout=len_argc_argvC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List@firstn_length_leC47Corelib4Init5Peano2ltc59OSSVerify5KrLib7Mh_00419RefLayout8envp_offC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00419RefLayout<cat_envp_ptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExecCflat_map_le8_decompC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAbuild_stack_bytesC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3powC47Corelib5Lists7ListDef3nthC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op205c59OSSVerify5KrLib7Mh_00419RefLayout=len_envp_ptrsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00419RefLayout8auxv_offC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAlength_auxv_bytesc59OSSVerify5KrLib7Mh_00419RefLayoutAlength_auxv_wordsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00419RefLayout@auxv_bytes_wordsC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpK46Stdlib9micromega:ZMicromega;ZArithProof03c59OSSVerify5KrLib7Mh_00419RefLayout9rdn_skipnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00419RefLayout=read_auxv_allC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC46Stdlib6ZArith4ZdivAZplus_mod_idemp_rC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC56Stdlib6ZArith4Znat5Z2Nat2idK47Corelib4Init5Logic3and01C49OSSVerify5KrLib8PropExecFlength_flatten_stringsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=repeat_lengthC46Stdlib5Lists4List<firstn_skipnC4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutFlength_at_random_bytesC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses:impl_morphC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib5Lists4List<length_skipnc59OSSVerify5KrLib7Mh_00419RefLayout@bsb_random_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StepTac9bsb_boundC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega8ZifyInst7Inj_Z_ZC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC59OSSVerify5KrLib7Mh_00387CatExec?cat_struct_sizeC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat9add_assocC59OSSVerify5KrLib7Mh_00387CatExec@nth_string_addrsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecAtotal_arg_bytes_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExecItotal_arg_bytes_firstn_leC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflc59OSSVerify5KrLib7Mh_00419RefLayoutEtotal_firstn_ev_boundC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib7Mh_00387StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StepTac<word_add_natC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00419RefLayout?cat_envp_ptr_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00419RefLayout?struct_av_boundC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9not_morphc59OSSVerify5KrLib7Mh_00419RefLayout>u_cat_envp_ptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec<cat_argv_ptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExecCcat_argv_ptr_offsetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExecBvalid_argv_str_lenC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7ph_addrC56Stdlib6ZArith6BinInt1Z4of_NC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType6ph_entC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType6ph_numC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout7AT_PHDRC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout8AT_PHENTC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout8AT_PHNUMC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout8AT_HWCAPC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9AT_PAGESZC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout6AT_UIDC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout7AT_EUIDC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9AT_SECUREC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9AT_RANDOMC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout7AT_NULLC56Stdlib6ZArith4Zdiv1Z>mod_mod_divideC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z7add_modc59OSSVerify5KrLib7Mh_00419RefLayout=at_random_offC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00419RefLayout;lay_bsb_lenC1?~~~~~~~~~~~~~~~".

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_skipn : forall segs mem n (a : word) bs off k,
  rdn segs mem a n = Some bs -> (off + k <= n)%nat ->
  rdn segs mem (a + nat_to_word off) k = Some (firstn k (skipn off bs)).
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) [] "p'0h01Hh12Hkh24__x1h34__x2h41bi001bh52H0h62bsh73offh82Ebh92Erh:1kh;1oi011oh<3Hk0h=7__arithh>4__ffh?8__varmaph@5__withA1ahB4cstrhC5cstr0hD1ehE1ni021nhF2H1hG4__x3hH1xi031xhI2IHhJ5cstr1hK3memhL4resti044resthM4segshN1yi051lp&0p;1p;2p;3p;4p;6p;7p;8p;<p;Bp-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000dR2p4p710p8P0P2p4p7210p8P0p1001Ap4p710R0p8p1001]p4p710R2g002:R3p4p710R4p8P2g002VR2p4p710R5p8p10034p4p710R6P1p8P6P4p8P6p10043p4p710R7p8P6P0p8p1004Up4p710R6P1p8P6P4p8P6P7p8P6P0p8p1005^p4p710R6P1p8P6P7p8P6P0p8p1006fp4p710P5p8g007Ej1WTg007ej1ITg008Jj1dTg008hj1_Tg009KR5j1lTg009mj21Tg00:Oj24Tg00:fR0j2=Tg00;@j19Tg00<;j30j1jTg00<UR6j13Tg00=5j2~Tg00=Xj3zTg00>5j2<Tg00>OR7j25Tg00>lR1j2;Tg00?Hj4PTg00?oj1JTg00@TR4j18Tg00A3j2STg00A\j3NTg00BEj2aTg00C1j1`Tg00CQj36Tg00D1j2^Tg00DOj1pTg00Dmj4]Tg00EKj1oTg00Eij1nTg00FTj2mTg00G7j2[Tg00GZj1ZTg00H<j3KTg00H_j4XTg00IJk204Tg00Ilk203Tg00JXk302Tg00K7k401Tg00Kij4VTg00LTj1}Tg00M2j2{Tg00MSj3yTg00N<j6gTg00NYj3UTP3j6MTg00O8j32Tg00O]j1fTP2j6Cj7\Tg00PUj2DTg00QJj1xTg00Qhj3wTg00RKj4OTg00S<j8vTg00T;j3uTg00U>j1tTg00Ucj2bTg00VBj4sTg00Vcj3iTg00WAl<YTg00WflBrTg00XLj7|Tg00Y0j8qTg00YTm<00Tf5R2f4R3f3R8f2R9f1R:COf0R;30p=:Ai9:;9U38,12p=>f7R<f6R=P2A2389P:CO;0;p=7g00Z9R>,=;p=Bg00ZXR?g00[6R@70;p=R1<?;p=Eg00[TRAP?P=P6P2P3P8P9P:P>P@P;M<Yp=ePAPAPAP?P?P?g00\3P6P6P6P7g00\SP2P3P8P9P:P;MBrp=QPAP?P0P6P1g00]6R7P8P9P:P>P@P;M<Yp=h1;@;p=@P?P:g00]XP;CXp=HP:g00^?RBg00^^RCPCg00_>RDP;g00_^F|p=?P8PBPCPCPDP9P:P;Gqp=AAi:>;p=GAU9:;,18p=F11:;9089p=LP2P3A289:P;COp=TPAP?P0P6P1P7P2P3P8P9P:P;M<Yp=cPAPAP?P?P4P6P6P8g00`>P9P:P;N<00p=kg00`b#Wg00aaR6#IR4#I#IR7#I#I#I#dR1#_R0%d7#_R7#lRB[%W7RE%lERFP<P=P8P311E9RGE:149:RH/=2PFf9RIf8RJP1P2%98P9PEP7P9P7P8P3E>G7[[^:A^7A]6^A0RKXEAPFP=P2P8P>PGE:%BHA0A8>RL%38RM#RRN%jARO%j?RP%3:%3;50?A0A:;1~:;3zXNAXHARQP8PM%EMRR1<?@RSFeRT1489RU#B%39RV,5MRW/;@RXPUPWP8PMPRP9PV%EVRREQPSChP;CPPX%J8%@M%J2RM%32RX#@RWg00bFRU%8>RY#8,S?RZ1S?YR[1S?>R\5N?5N?g00c2R]'a%`UR^36%WUR_P?1^?9R`P:%p?C]Ra%o?Rb%n?Rc1m?@Rd1[?6Re'H,?cRf%ZCRCPc1[?4R4,Hd,?cPCPcAK?e4Rg/Hd,?cPCP?Peg00c^RhPdCX,?cRiCACACA204cDRDP;P9g00dERjg00deRk'<203;9=0jkdB02?@:H01Rkb>b?b@X2?X3?%@;Rj%@91598/;@%R8Rl[[[^2?^3?P;%3=%3<RmP:P9P8O5b=bCbBb<CVPLPLPNPTA0A3>%33RT#RRNPOPPPQP3PT%ETRQPSFeP;CPPN1423RN#B15XTRP/;@ROPNPPP2PX%EXP3PTPQEQPSChP9CPPOPMPW%J<%@m%}6,{?=y?[=N?\9N?Z/a]=6U^P_PaPbPcPfPCPcAK?4e/Hd,?cPCPcP?P4PhPdCX,?cPCPiCACACAPDPkb>b?b@X2?X3?159:/;@Pl\l[\j^2?^3?P;%3I%3JP9P8P3O5b=bCbBb<bFCVPLPAP>14;2#BPFf<RLf;RjP1PI%9:RlP=PEP7P=P7P:PJE>G7]1X7A14>3#BPAP>14>;#BPFf=R@PLP1f:Ri%9>RdP:PEP7P:1G7IRhCFG7]1X:A14>>#BP0PIPFP@PLP;P>PEP7P>PhCFE:X40PFPEP5PEPEP;P;%`7Rhn10110100021010500XDF11EhRf11EJRaP2EgA0EhJA0EhIPEPhPFPfPE1G7;9U7>CLX6EPEP7P>1G7hCF,<FPiP;EMW0P;O1b5PFPLPjPIP>PEP7P>1G7JCFE:eA21Id%fIECW1P2P:P;F\W1P2P:P9F\bFb5W1W0X:AX7AX6EXA0PFPJP<P8%82PGE:%8=,=HP5P7PBPIP2O1117;RH1Di2n10110300021010000PB1<B;P5P7PBPiP=O1PH1Dj=n10110300021010000=0B;P5P7P5P7PBPLPJO1PH1D@Jn10110300021010000=0B;P5P7PFP:P5PEPFf?RGf>RhP1Pi%x6Rfg00eERU5w1R]PLETRZA67:;,1ER\%ZER[n10110300021010400P[n10110300021010000=0FaPFPGPhP1Pi%9JP<PEP7P<P7PJPIE>G7RO]0]8P:P5P7PBP@PIO1PH1DhIn10110300021010000=0BHPFP5PEPFPZA679;,1EP[n10110300021010400PEPICLf@RZPGP1PjP]P@ETPF1<F;PFfARSPZP1PLP]PhP;G7P5PEPFfCRQfBRTP1PhP]PZP;G7P5PEPFP:A67<;,1EP[n1011030002101040011EhRX50FPFfERPfDRNP1PZ%9hP@PEP7P@P7PhPGE>G7Rn]0]9P:PFPNPQP1PGP]PS11E;G7PFA67<:,1EPEPGCLPFPEP5PEPEP;P;A67I8Ron10110100021010500XDFA67J9Rp,1E11EZP;EgA0EpZA0EoSPEA67i3PFfIRofHRpP1PN%9TPSPEP7PSP7PTP;E>G7X6EPA14;SfFRq#8Rr'=PFfJRsPoP1PPPlPTPEP7PTP7P:A67L=R=E>G7]1PS14>Z%8P'=P0PNPFPsPoP;PTPEP7PT1G7=CFE:X40PoPpPrPNA67j2RZPSPB117jP5P7PFP;P5PEPFfKR>PsA21q]RtPpCOP\P[n10110300021010400P[n1011030002101000011E=R=50FX;BPF11E2P5PEPFP;A67@;,1EP[n10110300021010400=0F=X;F11EZR=,<FPoPpP1PNP]PqETP3ECP5P7PBPpPNO1PH1DoNn10110300021010000PiECPFPoPpPNPrP=E:eP;GvPFPoPpPNPSPEP7PS1G7ZCFE:eA21Nd%fNECW1%8;/4TfGRd#8'=P0%9YRZA21d;%99R=521%89Rr#9921dRi500X40P014Y:#9921qA00;iX40%8:R2#9921qR\,<0A21qZ=21lAuqY:ECP]g00eaECA21tl=00\P0A21d]Rd=21=PFfMfLP;PPPEP7PPP7P8PIE>E:X40PpPdPJP9PNP<149NRJ/=o%3NRd,5VRp%3oRI';PJPpP9PVPRPNPd%EdRpEQPoPI%EIRJEc14rNR=%8oRt'=15Vf/5d15If';RlP=15;fR=XH?RqPVO1RY/5dPrPYPqP9PVPRCkPNPdPpEQPtPqPIO1PqPoPIPJCkEcP:CPPl%JP%3P#@%J>%3>#@PMPWP^P_P?P`P:1^?8C]PbPc1m?fRb9K?e=K?4%t6,[?R6=K?b'H,?cPC1Hg6,?cCAPDPkb>b?b@X2?X3?XG?15=:159f';15:9/;8[^2?^3?^G?P;fN#3PIPmP3O4b=bJbCbBb<CVO6PiP;EMb0PFP>PsP\PQPEP7PQP7P2A67@<E>E:eW1X7AP;O1n0110200020111102PhO1PTP;EMW0P;O1b5W0W9XLEP;O1PFPTPSP1P@P]PGP[G7PFP[PEP@CLPFP[P5PEp-0P;g00fXR@g00g5n10110100021000000XDFRGPUPXP;EMP@1bn;b5W0W9n10110100021110501P;P9O2b9b;W0W8X47P;O1P5P7PBPjP<O1PH1DL<n10110300021010000%Z750BPFP[PEP<CLPFP[PGPUPaP;EMP@1bO;b5W0W8n10110101021110000P;P8O2b8b;W1W0X:AX7AX6EXA0XIKXEAP;CsXEAWKWMo"). Qed.

Lemma firstn_app_exact : forall {A} (l1 l2 : list A) n,
  length l1 = n -> firstn n (l1 ++ l2) = l1.
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) [] "h01nh11lh21Ah31Hh42l1h52l2p;1p;2p;3p;6p;4p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000dR2p4p710p8P0P2p4p7210p8P0p1001Ap4p710R0p8g00gQR2p4p710R3g002:R4p4p710R5p8P3g002VR6p4p710R7p8p10034p4p710R8P1p8P8P5p8P8p10043p4p710R9p8P8P0p8p1004Up4p710R8P1p8P8P5p8P8P9p8P8P0p8p1005^p4p710R8P1p8P8P9p8P8P0p8p200R0P3p8P0g00NYR3p4p710p8P0g00goR8p4p710p8P0g00hOR9p4p710p8P0g00hlR1p4p710R5p8P5P7p8g007Ej13TP8j25Tg00<;j32TP9j31TP3j30Tg00iKj26TP2j2<Tg00ibj2;Tg00jBj1:TP6j64TP1j27Tg00jgj48TP4j69Tf0R4#3f1R1#3g00[TR6f3R2f2R3'5=264P6f4R9/52R8f5R7#3R5A17929074;29X06%39R:A0982R;1688=093519A2549X1:P:P21579R</6<=0729174=259X1:P6g00Z9R<A07429179=259X061<92A09<39192=2:2e1;88%:8E4P;1792E4A19239098P9P8P2P3C8E4P1P4E9W3W0W5W4X20o"). Qed.

Lemma skipn_app_exact : forall {A} (l1 l2 : list A) n,
  length l1 = n -> skipn n (l1 ++ l2) = l2.
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) [] "h01nh11lh21Ah31Hh42l1h52l2p;1p;2p;3p;6p;4p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000dR2p4p710p8P0P2p4p7210p8P0p1001Ap4p710R0p8p1001]p4p710R2g002:R3p4p710R4p8P2g002VR5p4p710R6p8p10034p4p710R7P1p8P7P4p8P7p10043p4p710R8p8P7P0p8p1004Up4p710R7P1p8P7P4p8P7P8p8P7P0p8p1005^p4p710R7P1p8P7P8p8P7P0p8p100kFp4p710R0P2p8P0g00VcR2p4p710R7p8P0g00goR8p4p710R1p8P0g00hOR4p4p710R9p8P0g00lMR0p4p710R:p8p200R;P7p8P;P6p8P;P1p8P;P9p8P;P:p8P:P6p8g007Ej13TP8j25Tg00<;j32TP4j31TP2j30Tg00iKj27Tg00C1j16Tg00>5j2<Tg00ibj2;Tg00jBj1:TP5j64TP0j28Tg00lkj49TP3j6=Tf0R3#3f1R0#3g00[TR5f3R2f2R4'5=253P5f4R8/52R6f5R:#3R9A1:8290:3;22X05%38R1A0862R71766=084518A2932X11P1%6815:8R</7<=0:291:3=292X11P5g00Z9%6:A0:3251:=292X051<141;66%:6E4P71882E4A18249086P8P6P2P4C9E4P0P3E=W3W0W5W4X2;o"). Qed.

Lemma skipn_repeat' : forall {A} (x : A) off n,
  skipn off (repeat x n) = repeat x (n - off).
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) [] "p'0h01ni001nh13offh21Ah32IHh41lh51xp;1p;3p;2p;6p;4p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000dR2p4p710p8P0P2p4p7210p8P0p1001Ap4p710R0p8p1001]p4p710R2p1002:p4p710R3p8P2g002VR4p4p710R5p8p10034p4p710R6P1p8P6P3p8P6p10043p4p710R7p8P6P0p8p1004Up4p710R6P1p8P6P3p8P6P7p8P6P0p8p1005^p4p710R6P1p8P6P7p8P6P0p8p100kFp4p710R0P2p8P0g00VcR2p4p710R6p8P0p100gop4p710R7p8P0p100hOp4p710R1p8P0p1006fp4p710R0p8p100mIp4p710R3P6p8P3P5p8P3P7p8P3P1p8P3P0p8p200R3g00nOR1p4p710p8P3P6p8P3P5p8P0P5p8g007Ej14TP1j30TP2j33Tg00iKj21Tg00<;j35Tg00>5j26Tg00ibj2:Tg00nnj19TP4j67Tg00@Tj12Tg00VBj48Tf0R4g00[TR2f4R1#4R5f1R0f3R6=014R75311140901635^02R8X12P2P4g00Z9R9A0160531=557X02%46R7f2R5=064R:'61:49%94E7A369:11499065557eX02P2f6R7#4%26R:f5R;=074537114:907;35P4%4;%25,1990;1'6f7R9#4R511419097f8R:#4%20%2;'190:9754X45%24R:%21R;'19097R0,65A09749391P6P4O1E7A097:939;=550eX02P4O1n0110000020010100X02X38X12P4C8W1W5X23o"). Qed.

Lemma firstn_repeat' : forall {A} (x : A) k n, (k <= n)%nat ->
  firstn k (repeat x n) = repeat x k.
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) [] "p'0h01Hh14__x1h21ni001nh31kh42H0h57__arithh64__ffh74__p1h88__varmaph95__with:4__x2h;4cstrh<1xh=1Ah>2IHh?5cstr0h@1lp;2p;1p;3p;4p;6p;<p;7p;8p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000dR2p4p710p8P0P2p4p7210p8P0p1001Ap4p710R0p8p1001]p4p710R2p1002:p4p710R3p8P2g002VR4p4p710R5p8p10034p4p710R6P1p8P6P3p8P6p10043p4p710R7p8P6P0p8p1004Up4p710R6P1p8P6P3p8P6P7p8P6P0p8p1005^p4p710R6P1p8P6P7p8P6P0p8p100kFp4p710R0P2p8P0g00NYR2p4p710R6p8P0p100gop4p710R7p8P0p100hOp4p710R1p8P0p1006fp4p710R0p8p100mIp4p710R3P6p8P3P5p8P3P7p8P3P1p8P3P0p8p100oRp4p710R3g00nOR1p4p710R7p8P3P6p8P3P5p8p200R3P7p8P3P6p8P3P5p8P0P5p8g00:fR5j22Tg007Ej17TP1j30TP2j39Tg00<;j36Tg00>5j24Tg00@TR2j13Tg00<UR1j15Tg00QJj1OTg00>Oj28Tg00>lR0j21Tg00?Hj4ETg00?oj1>Tg00C1j1XTg00D1j2DTg00EKj1WTg00Eij1VTg00FTj2CTg00G7j2BTg00GZj1PTg00H<j3ATg010Vj6NTg00IJj2MTg00Ilj2LTg00JXj3KTg00K7j4JTg00CQj3<Tg00DOj1ITg00Dmj4HTg007ej1QTg00Kij4RTP4j6STg00VBj4TTg00YTl<UTg00WAl<FTg00H_j4[Tg00XLj7ZTg00Y0j8YTg00[TR4P4g00ZXR6P6P2P1P1f3R2g00`>f2R7f1R8f0R9M<Up=?P4P6P5P1P0g00]6R:P2P7P8g00Z9R;g00[6R<P9M<Fp=GP6P8g00]XP9C[p=;P8g00^?R=g00^^R>P>g00_>R?P9g00_^FZp=:P2P=P>P>P?P7P8P9GYp==P4P6P5P1P0P:f5R:f4R0P2P7P8P9M<Fp=@1289%7:A0:0899:7A0:0736[^24R1X3412;9%70A002;'4W0X24%37/29P4%30R5/29f8R@#7%3:RAf7RB=0@859@A0@BA36]0P8%32/2;125;%50RCg00aaRD#ORE'8/1<RFP5189ER5X<6RGPCO1PGP0PC146CC?146<CGP9CEPF%>:%5:RF,1<p-0RCg00bFR0#XRH%70R01D68%W6RI%V6RJ1C6<RK1B6DRL';,:J%P>RMPJ1C6ERN9A6LRO/;K,:JPMPJP=P>P>P?P2ENC=C=1MJ?R?P9P7g00dER>g00deR='41L97=6>=dAK6<8CJR=b6b8b9X16W711<9188ER>/1<P2[[^16^7CP9f:RC#7RK%3BRPf9RQ=0C;59CA0CQP36%5BRPP8P7O4b5b;b4W0%39,2A%7QRAf6R;90Q@RRA<CQ9A0CQB9<CQ56KX@AA<Q@R,4AA0Q@899Q;P:P812;8%5;R:%58RR'1P;P:146:RKP8PR146RRSE@%3;RT%38RU'218:E18RE'1REPTPGP:O1PGP;P:PKC?PUPGPRO1PGP8PRPSC?E@P9CEPE%>B11<P%>2%52,1<PHP0P61D67P8%I6CHPIPJ%QD,B6RD=A6N,;O,:JPM1;LD,:JC=P?P=b6b8b9X16X:6115>1187[^16^:6P9PF%5CP2O3b5b?b;b4CRO2ESA0Q@U99QTA0Q@T56AeW0X24P9O1n0110000020011100P9O1W0X24X>1X34P9CTX34X<9X=3o"). Qed.

Lemma repeat_firstn_skipn : forall {A} (x : A) n off k,
  (off + k <= n)%nat -> firstn k (skipn off (repeat x n)) = repeat x k.
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) [] "h04__p1h14__x1h24__x2h34__x3h44__x4h51lh61nh71Ah81Hh92H0h:2H2h;7__arithh<4__ffh=8__varmaph>5__with?4cstrh@5cstr0hA5cstr1hB1khC1mhD3offhE1xhF2z2p;2p;1p;3p;4p;6p;7p;5p;Bp;<p;8p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000dR2p4p710p8P0P2p4p7210p8P0p1001Ap4p710R0p8p1001]p4p710R2p1002:p4p710R3p8P2g002VR4p4p710R5p8p10034p4p710R6P1p8P6P3p8P6p10043p4p710R7p8P6P0p8p1004Up4p710R6P1p8P6P3p8P6P7p8P6P0p8p1005^p4p710R6P1p8P6P7p8P6P0p8p100kFp4p710R0P2p8P0g00NYR2p4p710R6p8P0p100gop4p710R7p8P0p100hOp4p710R1p8P0p1006fp4p710R0p8p100mIp4p710R3P6p8P3P5p8P3P7p8P3P1p8P3P0p8g00oRR3p4p710R1g00nOR7p4p710R8p8P1P6p8P1P5p8g011:R9p4p710R:P8p8P:P6p8P:P5p8p200R;P8p8P;P6p8P;P1p8P;P:p8P0P5p8g00:Oj2MTg00:fR5j2=Tg007Ej1>Tg00iKj2WTP7j3:TP2j3HTg00<;j32Tg00>5j24Tg00<UR2j10Tg012?j23Tg012\j27Tg00>lR7j21Tg00>OR0j2ETg00?Hj4gTg00?oj1KTg0139j2_Tg013[j2OTg0147j28Tg014Rj2GTg00@Tj1<Tg00A3j29Tg00LTj1[Tg00M2j2ZTg00MSj3YTg00A\j3?Tg00BEj2DTg00C1j1XTg00CQj3JTg00D1j2CTg00DOj1VTg00Dmj4BTg00EKj1UTg00Eij1TTg010Vj6RTg007ej1ATg00G7j26Tg00U>j1STg014lj3oTg00H_j4@Tg00FTj2nTg015Oj7lTg00GZj1kTg00H<j3hTg00IJj2fTg00Ilj2eTg00JXj3`Tg00K7j4aTg00Kij4bTP9j5cTP4j6ITg00Vcj3dTP3j4^Tg00WflBFTg00WAl<]Tg00XLj7\Tg0163j7iTg00Y0j8jTg00[TR3P3P3g00ZXR4P4P4g00ibP2P2P2f6R9g016Wf5R:f4R1f3R6f2R8f1R<f0R=MBFp=QP3P4P5P2P7g00]6P:P1P6P8P<P=M<]p=PP3P3P3P4P4P4g00\3P2P2P2P0g00\SP:P1P6P8P<P=MBFp=mP<g00^?R0g00^^R2P2g00_>R7P=g00_^F\p=5P8P0P2P2P7P<P=Fip=NP4P<g00]XP=C@p=;P6P0P2P2P7P8P<P=Gjp=L1M<=/=8%>:R51W68R>9::1R?%>9R@AH98=A:9:8RA32X55P5A::1<RBA2@=AX55145BAH:<?P:P1P<P>1=<>%0<R?g00[6RB%06R5%08RA'3'7R@'1P<P?144?RCP>P@13<=,7BXC4X64P6P51445R@P8PA144AR>FQEP1M8<RD/=61EA?RE/15RFPDPEP8PAP>P<P?PCEmP6P5P@EPP=CgPF%K811BA%K:RA%0:,1BRFPAPFf7#0RF%09'3RA,_B1OBA17BAR@=24A'811ABA24@B'8'Gf8#0R@/3F,7BP4p-0RFg00bFRAg00Z9R5#<RC#<R?#<,94g00aaR>#[,Z4194?5Y4194C19455?45?4R55?4g00c2RC'D1D5C%XA5JA3J%>AP4P41C41P8%V4CBP<1C46CB%U4%T4RAPAP0P2P2P7PAP0P2P2P7P9ERP4%A>R0,64RCg00c^R5%A0,64R0%S>,64R?5o4REC@,5A5NA1n4BRD,;E,5AP4PCP5PDC@,5A5NAFl%k2R2PA164>R>9h4?/;0,5AP21;>C,5ACLCL1fA7P=P8g00dERAg00deR7'41e=8=2A7dA`4B<Cab<b=b>X14X24X34X44W01368R7924<,81117BA24<B'8'G1E6</111186[[^14^24^34^44^0FP=f:#0RFf9#0R4'3,OBPFP4P<P@P8P9O7b;bFb:bAb@b?b9CbDcEIA::169d:8P:P1P8P6C^EIW8XB3XD3X63XE=X7;o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cat_envp_ptr (sp : word) (av ev : list (list byte)) (k : nat) : word :=
  nth k (fst (string_addrs (cat_env_base sp av ev) ev)) (Z_to_bv 64 0).

(* [comment removed for export] *)
Definition envp_off (av : list (list byte)) : nat := (8 + 8 * (length av + 1))%nat.
Definition auxv_off (av ev : list (list byte)) : nat :=
  (8 + 8 * (length av + 1) + 8 * (length ev + 1))%nat.

(* [comment removed for export] *)
Definition auxv_words (ph : PhdrInfo) (rnd uid hw : word) : list word :=
  flat_map (fun e => [fst e; snd e]) (auxv_entries ph rnd uid hw).

Lemma build_auxv_words : forall entries,
  build_auxv entries = flat_map word_le8 (flat_map (fun e => [fst e; snd e]) entries).
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) [] "p'0h01lh11eh27entriesh32IHh41ah52esh61th71vi001bi011pp;1p;2p;3p;4p;6p;5p-1R0p10000p4p710R1p8P0g000GR2p4p710p8P0P2p4p7210p8P0g000dR3p4p710p8P0P3p4p7210p8P0p1001Ap4p710R0p8g017>R4p4p710R5g002:R6p4p710R7p8P5g002VR8p4p710R9p8p10034p4p710R:P1p8P:P7p8P:g0043R;p4p710R<p8P:P0p8p1004Up4p710R:P1p8P:P7p8P:P<p8P:P0p8p1005^p4p710R:P1p8P:P<p8P:P0p8p100kFp4p710R0P5p8P0p100NYp4p710R5p8P0p100gop4p710R:p8P0g00hOR<p4p710R1p8P0p1006fp4p710R0p8p100mIp4p710R7P5p8P7P9p8P7P:p8P7P1p8P7P0p8p100oRp4p710R7p100nOp4p710R1p8P7P5p8P7P9p8p1011:p4p710R:P1p8P:P5p8P:P9p8p1017\p4p710R=P1p8P=P5p8P=P7p8P=P:p8P0P9p8g007ej12Tg008Jj1:Tg008hj19Tg018fR9j2=Tg007Ej1<Tg019Fj17TP2j3?Tg01:Ej3>Tg00C1j18Tg00CQj36TP3j41Tg00<;j34Tg00>5j2;Tg01:bR3j15TP<j30TP4j4DTP6j6CTP8j6BTg01;Zj4@TP;j5ATf2R;f1R8P3f0R3C1p=3g00aa#2#2#2R6#2#2#2#:#9R4/=4R<#<R2P<%:6#9R6#<R0%73P<P4A?443R:A>443R=%84564564X1<R7P3C1934634R5X22P<P4P7%8<C19346,;0P9P4P4A6<;8R9#7P<P4P7P9C19346540\5^02P3P0P<P4P7P8C19346R9f4#5R1f3R>#5R?506=063P<P4P7P;C19346906?9061R1540X00P0%5;R@=069906?RAA4031X001;0AA06?@=069P6P?P@P9CDECP<P6%5:%5=506X1<P8C1P3EBP4P4P>P;C@=6<8R;#7P<P4P7P;C19346540eX35X52X74X64P8P3O2n2001101010121100100X4<P3DAW2o"). Qed.

Lemma auxv_bytes_words : forall ph rnd uid hw,
  auxv_bytes ph rnd uid hw = flat_map word_le8 (auxv_words ph rnd uid hw).
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) [] "h02hwh12phh23rndh33uidp;1p;4p;3p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0g000dR2p4p710p8P0P2p4p7210p8P0p1001Ap4p710R0p8p1001]p4p710R3p1002:p4p710R4p8P3p1002Vp4p710R5p8p10034p4p710R6P1p8P6P4p8P6p10043p4p710R7p8P6P0p8p1004Up4p710R6P1p8P6P4p8P6P7p8P6P0p8p1005^p4p710R6P1p8P6P7p8P6P0p8p100kFp4p710R0P3p8P0p100NYp4p710R3p8P0p100gop4p710R6p8P0p100hOp4p710R7p8P0p1006fp4p710R0p8p100mIp4p710R1P3p8P1P5p8P1P6p8P1P7p8P1P0p8p100oRp4p710R1p100nOp4p710R7p8P1P3p8P1P5p8p1011:p4p710R6P7p8P6P3p8P6P5p8p1017\p4p710R4P7p8P4P3p8P4P1p8P4P6p8P0P5p8g007ej10Tg008Jj12Tg008hj11Tg01<:j43Tg01=;j19Tg007Ej18Tg01>Bj47Tg01?Aj44TP2j45Tg00<;j36Tg01@Bg00aa#0#0#0R2#0#0#0#2#1R5f3R0f2R6f1R4f0R1C3#9%22#1R2#8P0P6P4P1C7P5P2g01:bP0P6P4P1C4C536eX05X35W2W1o"). Qed.

Lemma length_auxv_words : forall ph rnd uid hw, length (auxv_words ph rnd uid hw) = 20%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) [] "h02hwh12phh23rndh33uidp;1p;2p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000dR2p4p710p8P0P2p4p7210p8P0p1001Ap4p710R0p8p1001]p4p710R2p1002:p4p710R3p8P2p1002Vp4p710R4p8p10034p4p710R5P1p8P5P3p8P5p10043p4p710R6p8P5P0p8p1004Up4p710R5P1p8P5P3p8P5P6p8P5P0p8p1005^p4p710R5P1p8P5P6p8P5P0p8p100kFp4p710R0P2p8P0p100NYp4p710R2p8P0p100gop4p710R5p8P0p100hOp4p710R6p8P0p1006fp4p710R0p8p100mIp4p710R1P2p8P1P4p8P1P5p8P1P6p8P1P0p8p100oRp4p710R1p100nOp4p710R6p8P1P2p8P1P4p8p1011:p4p710R5P6p8P5P2p8P5P4p8p1017\p4p710R3P6p8P3P2p8P3P1p8P3P5p8P0P4p8g007ej10Tg008Jj15Tg008hj13Tg00>5j24Tg00@Tj12Tf0#2#2#2#2p=1g01@Bg00aa#0#0#0#0#0#0#5#3R4g00[Tg00Z9#1#1#1#1#1'4X04X34W2W1o"). Qed.

Section Layout.

  Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
  Variable ph : PhdrInfo.
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.       (* [comment removed for export] *)

  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned sp)%Z.
  Hypothesis Hsp_hi : (bv_unsigned sp <= sp_window_hi)%Z.

  Let bsb := build_stack_bytes ph sp av ev uid hw rdraw.
  (* [comment removed for export] *)
  Let stk := stack_to_mem sp (entry_stack_image ph sp av ev uid hw rdraw).

  Lemma lay_bsb_nw : (bv_unsigned sp + Z.of_nat (length bsb) < 2^64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) ["Layout"] "p;:p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000dR2p4p710p8P0P2p4p7210p8P0p1001Ap4p710R0p8p1001]p4p710R2p1002:p4p710R3p8P2p1002Vp4p710R4p8p10034p6051000R5P1p8P5P3p8P5p10043p4p710R6p8P5P0p8p1004Up6051000R5P1p8P5P3p8P5P6p8P5P0p8p1005^p6051000R5P1p8P5P6p8P5P0p8p100kFp6051000R0P2p8P0p100NYp4p710R2p8P0p100gop4p710R5p8P0p100hOp4p710R6p8P0p1006fp4p710R0p8p100mIp6051000R1P2p8P1P4p8P1P5p8P1P6p8P1P0p8p100oRp6051000R1p100nOp4p710R6p8P1P2p8P1P4p8p1011:p6051000R5P6p8P5P2p8P5P4p8p1017\p6051000R3P6p8P3P2p8P3P1p8P3P5p8P0P4p8g01ABl:0Tp,2php,2spp,2avp,2evp,3uidp,2hwp,5rdrawp,3Hvap,3Hvep,6Hsp_hiM:0o"). Qed.

  Lemma lay_len_av : (1 <= length av <= 1024)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) ["Layout"] "h01ah14__x1h21Hh32H1h42H2h52_Hh67__arithh74__ffh88__varmaph95__with:4cstrh;3stkh<1vp;1p;2p;3p;6p;4p;7p;<p;8p-1R0g01B=R1p4p710R2p8P0p1000GR3p4p710p8P0P3p4p7210p8P0p1000dR3p4p710p8P0P3p4p7210p8P0p1001Ap4p710R0p8p1001]p4p710R3p1002:p4p710R4p8P3p1002Vp4p710R5p8p10034p6051000R6P2p8P6P4p8P6p10043p4p710R7p8P6P0p8p1004Up6051000R6P2p8P6P4p8P6P7p8P6P0p8p1005^p6051000R6P2p8P6P7p8P6P0p8p100kFp6051000R0P3p8P0p100NYp4p710R3p8P0g00goR6p4p710R7p8P0p100hOp4p710R2p8P0p1006fp4p710R0p8p100mIp6051000R4P3p8P4P5p8P4P7p8P4P2p8P4P0p8p100oRp6051000R4p100nOp4p710R2p8P4P3p8P4P5p8p1011:p6051000R7P2p8P7P3p8P7P5p8p1017\p6051000R8P2p8P8P3p8P8P4p8P8P7p8P0P5p8g00QJj18Tg007ej16Tg008Jj1GTg008hj1cTg007Ej1BTP6j2>Tg00<UR6j1=Tg00>lR5j23Tg0147R0j24Tg01BTj1FTg01CPj3:Tg01D1j2bTP1j3]Tg01DWj1WTg01E0j1VTg00<;j39Tg01F4j2TTg01Fhj2STg00@Tj10Tg00:fR1j2ATg00>5j27Tg01G?j6HTg00?oj1JTg009Kj1KTg00C1j1LTg00D1j2MTg00EKj1ETg00Eij1QTg00G7j2RTg00FTj2;Tg00H_j4?Tg00GZj1aTg0163j7`Tg00IJj2\Tg00Ilj2[Tg00JXj3XTg00K7j4YTg00Kij4ZTg00U>j1CTg00WAl<UTg00XLj7^Tg00Y0j8_Tf0R7#6#6p=2%C7#Cp=5%07#0p=P%07#0#0#0p=O%07#0#0#0#0#0#0#0p=N%07#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=I%07#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00[Tg00ZXR8P1P6P5g00]6f5R5f4R6f3R1f2R4f1R3P7M<Up=<P3g00^?R2g00^^R9P9g00_>R:P7g00_^F^p=@P1P2P9P9P:P4P3P7G_p=Dp,3Hvag00aaR1#8R;%61#2R<#GR=#cR>#BR?p,2avR@'>RA#=RB'3RC%6<#2#2#2R<#8RD,3BRE'4RF%F@%6<#2#2#2#2#2#8'31>>7#=%51#5#5#5#5#5#5#5#8'3X0?=:?@g00[6R<,b==]>7#WX0?=:?@g01GhR=g00dERG%V7g01HXRH39g01I8,T7=9GH'4X0=1S?@3:'4'4'4R@'4P0PFP@g00Z9#0R?/AAR=%0?#P#O#N#I#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1RH,AARI'4RJP7P0PCPEPJ\@P7PJPFP=PIPCPEP?P;178;PAPB178BR?E<PAPBP?PHPD178DE<EH%JA13<Bp,3stkp,2hwO1%K>g00bFR>#L%B>1M83%E8%Q8R>P81R81R1g00]XRA1;8DC?,@>RH%a9R?P>P81;8;PAP1C?,@>R1P?P>P2P9P9P:P1PHF`CDCD1\>:P7P4g00deR>,7G1[74=9G>dAX8<3CYb7b8b9X18137D13;313;4134D'4[[^18P7PBP6P5O3b6b;b:CZX5@X4EX3CP3P7O2n2001000010121000000X2FP3P7O2n2001000010121000000b<o"). Qed.

  Lemma lay_len_ev : (length ev <= 256)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) ["Layout"] "h04__x1h11eh22H1h32_Hh47__arithh54__ffh68__varmaph75__with84cstrh93stkh:1vp;1p;2p;3p;4p;7p;8p;<p-1R0g01B=R1p4p710R2p8P0p1000GR3p4p710p8P0P3p4p7210p8P0p1000dR3p4p710p8P0P3p4p7210p8P0p1001Ap4p710R0p8p1001]p4p710R3p1002:p4p710R4p8P3p1002Vp4p710R5p8p10034p6051000R6P2p8P6P4p8P6p10043p4p710R7p8P6P0p8p1004Up6051000R6P2p8P6P4p8P6P7p8P6P0p8p1005^p6051000R6P2p8P6P7p8P6P0p8p100kFp6051000R0P3p8P0p100NYp4p710R3p8P0g00goR6p4p710R7p8P0p100hOp4p710R2p8P0p1006fp4p710R0p8p100mIp6051000R4P3p8P4P5p8P4P7p8P4P2p8P4P0p8p100oRp6051000R4p100nOp4p710R2p8P4P3p8P4P5p8p1011:p6051000R7P2p8P7P3p8P7P5p8p1017\p6051000R8P2p8P8P3p8P8P4p8P8P7p8P0P5p8g007ej15Tg008Jj1GTg008hj1ATg007Ej1=TP6j2<Tg00<UR6j1;Tg00QJj17Tg00>lR5j24Tg01BTj1BTg01CPj3:Tg01D1j2>TP1j3XTg01DWj1VTg0147R1j28Tg00:fR0j2UTg00>5j26Tg00?oj1STg009Kj1RTg00C1j1FTg00D1j2ETg00EKj1DTg00Eij1CTg00G7j2HTg00FTj2ITg00H_j4JTg00XLj7KTg00GZj1LTg00Y0j8@Tg00IJj2MTg00Ilj2NTg00<;j3?Tg00JXj3OTg00K7j4PTg00Kij4QTg00U>j19Tg00@Tj10Tg00WAl<WTf0R7#5#5p=3%97#9p=1%07#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=2g00[Tg00ZXR8P0P6P5g00]6f5f4R5f3f2R6f1R0P7M<Wp=Tp,3Hveg00aaR4#5#3R3#GR2#AR9#=R:p,2evR;'<R<#;R=%53#3#3R3#7R>'4R?%B;%53#3#3#3#3#7'41<97#;%14#1#1#1#1#1#1#1#7'4X1:=::;g00[6R3,>2=X97#VX1:=::;'8'8R;'8P1P?P;g00Z9#2#2#2#2#2#2#2#2R1,U<R:P7P:P?P<P=168=P1P>168>ET%S<143=p,3stkp,2hwO1%R9g00bFR9#F%=91E80%D8%C8R9g00^?R<g00^^R1P1g00_>R:P9P<P1P1P:P81H84g00]X1I8>CJg00_^FKR4%L1P4G@1M9:P7P6g00dER:g00deR9'61N76=?:9dAO830CPb5b6b7X08147>140>[^08P7P=P5O2b4b9b8CQX3;X2?P0P7O2n2001000010121000000b:o"). Qed.

  (* [comment removed for export] *)
  Lemma bsb_decomp : exists strs_tail,
    bsb = (word_le8 (len_word av)
           ++ flat_map word_le8 (fst (string_addrs (cat_string_base sp av ev) av)))
          ++ word_le8 (Z_to_bv 64 0)
          ++ flat_map word_le8 (fst (string_addrs (cat_env_base sp av ev) ev))
          ++ word_le8 (Z_to_bv 64 0)
          ++ auxv_bytes ph (at_random_ptr sp av ev) uid hw
          ++ strs_tail.
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) ["Layout"] "p'0h01lh19strs_tailh21pi009argv_ptrsi011bi02<env_str_basei039envp_ptrsi041xp;1p;2p;3p;4p;6p-1R0p10000p4p710R1p8P0g000GR2p4p710p8P0P2p4p7210p8P0g000dR3p4p710p8P0P3p4p7210p8P0p1001Ap4p710R0p8g017>R4p4p710R5g002:R6p4p710R7p8P5g002VR8p4p710R9p8p10034p6051000R:P1p8P:P7p8P:p10043p4p710R;p8P:P0p8p1004Up6051000R:P1p8P:P7p8P:P;p8P:P0p8p1005^p6051000R:P1p8P:P;p8P:P0p8p100kFp6051000R0P5p8P0p100NYp4p710R5p8P0g00goR:p4p710R;p8P0g00hOR1p4p710R7p8P0p1006fp4p710R0p8p100mIp6051000R<P5p8P<P9p8P<P;p8P<P7p8P<P0p8p100oRp6051000R<g00nOR7p4p710R;p8P<P5p8P<P9p8p1011:p6051000R=P;p8P=P5p8P=P9p8p1017\p6051000R>P;p8P>P5p8P>P<p8P>P=p8P0P9p8g007ej1<Tg008Jj1NTg008hj1GTg007Ej1DTg018fR9j2ZTg00@Tj16TP:j2:Tg00:Oj29Tg01J9j2FTg01JPj3TTg01>Bj4RTg00;@j1?Tg00O8j3>Tg01KRj27TP2j3;Tg01LSj1MTg01;Zj4KTg01MTj2VTg01:bR2j1JTg01D1j2ITg01NLj1HTP1j30Tg00QJj1UTg00<Uj1ATg01OPj28Tg012?j2@Tg01P0j1BTP7j3CTg01PPj1STg01QNj1QTg00<;j32Tg01RRj2=Tg00>5j2PTP4j45TP6j63Tg01Rlj4OTg01SFj2ETP8j6LTg01TEj3YTg01UIj3XTP3j4WTf2R3f1R8P2f0R2CWp=4f4f3R6A038230p=1g00aa#<#<#<R3#<#<#<#NR4#GR7#DR1/Z7R:P1P7p,2spR0g00Z9#6R=#6#6#6#6#6#6#6R>%N3R<#GR5#DR;p,2avR?':/9=/F>'9p,2evR@,:;/9=/F>'9R>p,2phAT0?@p,3uidp,2hwCRR=,:5'9#?5>4RA/7?RB9;17RC%M?#?RD9>4ARECKP9P1P7P;P8P9P1P7P;172@P5P51V;?#JRFP5A4756P5g00[6R6,I4#JRGP5A4758%H?RH%H@RI505RJ905=RK905GRLD1RMD1RNP51I<6R6%U3R31:5N#A/83'@/83#B5C5p,5rdraw#S#QRND1n2001104000121103101n2001104000121100102P5g01VJ,9>#?9>40R>/7?9;179475R<905FROP5PGA>4>D/7@9;179475R>P5PGP5P=P2D1RD505D1RP52;X1;,=;X2:P:P1P717E@RQ9;17RR%M@#?9>4ECKP9P1P7P;P8P5P5PFP5A475CRCPMD1RMP51:5M#A/83,@3/83#B9C56PND1RMn2001104000121103101=2;PX1;,=;X2:P;A475RRR=05LR:905GR8905CR4905FRS1:5S#A/83,@3/83#B9C56=05NRN505R6=2;PX1;R3P5PHP5PIPND1RSP;A054NRT905FP5PGP5P>P5PGP5P=PSD1R>D1RU905ORO92;2X0;P;A058NRV905CA05F2=2;OX0;P;A05:NRW905GP5PFP5PCP2D1=2;OX0;P;A05LNRX905RP5PFP5PCA05G2RYD1=2;OX0;P;A05KNRZ905GP5PFP5PCP5PGP5PRP2D1D1=2;OX0;P;A05JNR[905=P5PFP5PCP5PGP5PRPYD1D1=2;OX0;P;PSP5PFP5PCP5PGP5PRPDD1D1=2;OX0;P;P5PFP5P<PUD1RSP5PFP5PCP5PGP5PRP>D1D1=2;2X0;1P;SPOP5PFP<PUC5E3P[P5PHPIPNC5E3PZP5P=PJPNC5E3PXP5PGPKPNC5E3PWP5PRPLPNC5E3PVP5PGP:PNC5E3PTP5PCP8PNC5E3P6P5PFP4PNC5E3CO1=;3ePQ1E@EELP9P1P7P;PQPMn2001104000121103101=2;PX1;,=;ePB1E?AELp,3bsbP5AY0?@/7?9;179475905FP5PGAX0?@/7@9;179475=05DD152;X1;,=;eo"). Qed.

  Lemma len_argc_argv :
    length (word_le8 (len_word av)
            ++ flat_map word_le8 (fst (string_addrs (cat_string_base sp av ev) av)))
    = (8 + 8 * length av)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) ["Layout"] "h01nh14__x1h27__arithh34__ffh48__varmaph55__with64cstrh73stkh81xh91yp;1p;2p;3p;4p;<p;7p;6p;Bp-1R0p10000p4p710R1p8P0g000GR2p4p710p8P0P2p4p7210p8P0g000dR3p4p710p8P0P3p4p7210p8P0p1001Ap4p710R0p8g01WHR4p4p710R5p1002:p4p710R6p8P5g002VR7p4p710R8p8p10034p6051000R9P1p8P9P6p8P9p10043p4p710R:p8P9P0p8p1004Up6051000R9P1p8P9P6p8P9P:p8P9P0p8p1005^p6051000R9P1p8P9P:p8P9P0p8p100kFp6051000R0P5p8P0p100NYp4p710R5p8P0g00goR9p4p710R:p8P0g00hOR1p4p710R6p8P0p1006fp4p710R0p8p100mIp6051000R;P5p8P;P8p8P;P:p8P;P6p8P;P0p8p100oRp6051000R;p100nOp4p710R6p8P;P5p8P;P8p8p1011:p6051000R:P6p8P:P5p8P:P8p8p1017\p6051000R<P6p8P<P5p8P<P;p8P<P:p8P0P8p8g007ej11Tg008Jj1@Tg008hj1<Tg007Ej19Tg01MTj2cTg01:bR8j1XTP9j23Tg01TEj3STg01KRj2LTP2j3ETP3j4DTg00:Oj24Tg00@Tj10Tg01J9j27Tg00QJj1YTg00<UR3j1:Tg01WgR2j2>Tg00>OR9j2;Tg00<;j35j1=Tg00=5j2VTg00=Xj3RTg00>5j28Tg00WAl<FTg00?oj1GTg00>lj2HTg009Kj1ITg00C1j1JTg00D1j2CTg00EKj1MTg00Eij1NTg00FTj2BTg00G7j2OTg01XDj3PTg00H<j3ATg00H_j4TTg00XLj7UTg00IJj2bTg00Ilj2aTg00JXj3`Tg00K7j4_Tg00Kij4^Tg01Xgj2\TP7j66Tg01Ylj1ZTg01Zmj1[TP1j3WTP4j3]Tg00WflB?Tg00[TR4f1R1f0R735p=2P4P4P4g00ZXR0P0P0g01[kP3P3P3P2g01\Kf5R2f4R:f3R<f2R;P1P7MB?p=QP4P4P4P0P0P0g00\3P3P3P3P9g00\SP2P:P<P;P1P7MB?p=KP4g00aaR<#1#1#1R:#@#<R2%92R9p,2avR5'cR6#XR='3R>%1:#1#1#@#<R?P2P8%9?p,2spp,2ev7S5R8/L57E?R@CDRA,32RB'4g00Z9#0#0#0#0#0#0#0#0RC1395R9,7CRD'4RE,27X04P4PC147B/2EX04P413?@R?,7C14C7/2EX04P4P917C7,4C/2EX0412EE%Y:R:%:9RF,>:RG';RH=50HP4P0%=4P3%=0%:1%:755012171V173RX94X84PEPHPCP:180:R4PDPGPCP:P4P9PF180FEQEKR4PEPHP4M<F%G9g00[6R9/HFp,3stkp,2hwO1%I2g00bFR4#J%941C01%M0%N0R4g00^?g00^^RHPHg00_>RHP01B0:RE1O0<9P0E5A0REg00c^PECTg00_^FU1b4HP7P;g00dERHg00deR4'81a7;=5H4dA`091C_b3b4b5X101>:7,;:R:=50:^10P7PFO1b2b7b6C^P?1\58E6PB%Z@E6P>%[6E6AW2=A,32A]2=AE6o"). Qed.

  Lemma len_envp_ptrs :
    length (flat_map word_le8 (fst (string_addrs (cat_env_base sp av ev) ev))) = (8 * length ev)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) ["Layout"] "h04__x1h11nh27__arithh34__ffh48__varmaph55__with64cstrh73stkh81xh91yp;1p;3p;2p;<p;4p;7p;6p;Bp-1R0p10000p4p710R1p8P0g000GR2p4p710p8P0P2p4p7210p8P0g000dR3p4p710p8P0P3p4p7210p8P0p1001Ap4p710R0p8p1001]p4p710R4p1002:p4p710R5p8P4g002VR6p4p710R7p8p10034p6051000R8P1p8P8P5p8P8p10043p4p710R9p8P8P0p8p1004Up6051000R8P1p8P8P5p8P8P9p8P8P0p8p1005^p6051000R8P1p8P8P9p8P8P0p8p100kFp6051000R0P4p8P0p100NYp4p710R4p8P0g00goR8p4p710R9p8P0p100hOp4p710R1p8P0p1006fp4p710R0p8p100mIp6051000R5P4p8P5P7p8P5P9p8P5P1p8P5P0p8p100oRp6051000R5p100nOp4p710R1p8P5P4p8P5P7p8p1011:p6051000R9P1p8P9P4p8P9P7p8p1017\p6051000R:P1p8P:P4p8P:P5p8P:P9p8P0P7p8g00@Tj10Tg007ej12Tg008Jj18Tg008hj19Tg007Ej17Tg01UIj3VTg01KRj2RTP2j3DTP8j23Tg01J9j24Tg00<;j31j1;Tg00QJj1>Tg00<UR8j15Tg01WgR2j2<Tg00=5j2WTg00=Xj3UTg00>5j26Tg00WAl<QTg00?oj1LTg00>lj2KTg009Kj1CTg00C1j1ETg00D1j2FTg00EKj1BTg00Eij1GTg00FTj2HTg00G7j2ATg01XDj3ITg00H_j4JTg00XLj7@Tg00IJj2?Tg00Ilj2MTg00JXj3NTg00K7j4OTg00Kij4PTg01Xgj2=TP6j6:TP3j4STg01Ylj1YTg00WflBXTg00[TR3P3P3g00ZXR6P6P6g01[kP8P8P8P2g01\Kf5f4f3f2R2f1R7f0R0MBXp=TP3g00Z9#0#0#0#0#0#0#0#0R9g00aaR:#2#2#2R5#2#2#2#8#9R4%74p,2spp,2avp,2evR13VR;/R17D4R<'3R='4%85#9R>#7/31R?,49R@9130X13P3P?1490=13@X13A13@@%>5R5%5?RA'<RB=16BP3P6%;3P8%;6%57%50516A13701W703UX93X83P@PBP9P51665P?PA166AETR9P@PBP9M<Q%L?g00[6R?/KAp,3stkp,2hwO1%C>g00bFR9#E%791F67%B6%G6R9g00^?g00^^RBPBg00_>RBP61H651A6:5I6R:g00c^P:CJg00_^F@1?9BP0P2g00dERBg00deR9'61M02=1B9dAN6?7COb3b4b5X061<50R5=165^06P0PAO1b2b7b6CPP=1=1;E:P4P>g01:bP<CS,3>%Y<E:o"). Qed.

  (* [comment removed for export] *)
  Lemma read_argv_null :
    rdn segs stk (sp + nat_to_word (8 + 8 * length av)) 8%nat = Some (word_le8 (Z_to_bv 64 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) ["Layout"] "p'0h01Hh11Eh21eh31nh49strs_tailh52tli001xp;1p;2p;3p;4p;?p;7p;6p-1R0p10000p4p710R1p8P0g000GR2p4p710p8P0P2p4p7210p8P0g000dR3p4p710p8P0P3p4p7210p8P0p1001Ap4p710R0p8p1001]p4p710R4g002:R5p4p710R6p8P4p1002Vp4p710R7p8p10034p6051000R8P1p8P8P6p8P8p10043p4p710R9p8P8P0p8p1004Up6051000R8P1p8P8P6p8P8P9p8P8P0p8p1005^p6051000R8P1p8P8P9p8P8P0p8p100kFp6051000R0P4p8P0p100NYp4p710R4p8P0g00goR8p4p710R9p8P0g00hOR1p4p710R6p8P0p1006fp4p710R0p8p100mIp6051000R:P4p8P:P7p8P:P9p8P:P6p8P:P0p8p100oRp6051000R:p100nOp4p710R6p8P:P4p8P:P7p8p1011:p6051000R9P6p8P9P4p8P9P7p8p1017\p6051000R;P6p8P;P4p8P;P:p8P;P9p8P0P7p8g007ej12Tg008Jj1>Tg008hj1:Tg007Ej17Tg01MTj2NTg01:bR7j1<Tg01TEj3FTg01KRj28TP2j39TP3j4=TP1j30Tg01D1j2@Tg01UIj3?Tg01JPj3MTg01>Bj4LTg00<;j33Tg01RRR1j2ITg009Kj1HTg00@Tj11TP8j2;Tg01J9j2ETg00:Oj2DTg00;@j15Tg00O8j36Tg00RKj44Tg009mj2CTg01Zmj1BTg01\nl?GTg01^0j7ATg01^nj2JTP5j6KTg01_og00aa#2#2#2R5#>#:R8#7R3p,3bsbp,2avR2,N3#<%25#2#2#>R5#:R0P8P7%70R9p,2spR;p,2evR:7F2/82790C=508R4g00[6,@5R6#<R<P0P8P7A?;2:/8:9990C=R9p,2phR0AM;2:p,3uidR7p,2hwR=CLR>f0R?508908<508508508533R@X43RA'IP1P3PA%H3RAp,4segsR1p,3stkg00Z9#1#1#1#1#1#1#1#1RB1;32,EB'DRC#5965;RDPBC41C3<RE33P?P1P0P;P2P:P7P=p,5rdrawRFP4P<f1RG908>908<9089PBP?%B6g01a0M?GP1P0P;P2P:P7P=PFFA,J;RF1;84R4#5965;PBC4=3AEg00[TR8P4P1PF%5?965;PBC4=3AEX38P?PCg01b1EKP1PFPDPBC4=3AEP?b0b0X1@X53PGP?O2n2011000000121100000b2o"). Qed.

  (* [comment removed for export] *)
  Lemma read_envp_ptr_k : forall k, (k < length ev)%nat ->
    rdn segs stk (sp + nat_to_word (envp_off av + 8 * k)) 8%nat
    = Some (word_le8 (cat_envp_ptr sp av ev k)).
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) ["Layout"] "p'0h01Hh11nh21lh31Eh44__x1h54__x2h64Hk'0h73Hk0h87__arithh94__ffh:8__varmaph;5__with<4cstrh=5cstr0h>5cstr1h?3stkh@2H0hA2HkhB3Hk'hC5cstr2hD1ehE1khF9strs_tailhG2tlhH1xi001xhI1yp&0p;1p;2p;3p;4p;6p;<p;7p;8p;Bp-1R0p10000p4p710R1p8P0g000GR2p4p710p8P0P2p4p7210p8P0g000dR3p4p710p8P0P3p4p7210p8P0p1001Ap4p710R0p8g017>R4p4p710R5g002:R6p4p710R7p8P5g002VR8p4p710R9p8p10034p6051000R:P1p8P:P7p8P:p10043p4p710R;p8P:P0p8p1004Up6051000R:P1p8P:P7p8P:P;p8P:P0p8p1005^p6051000R:P1p8P:P;p8P:P0p8p100kFp6051000R0P5p8P0g00NYR5p4p710R:p8P0g00goR;p4p710R1p8P0g00hOR7p4p710R<p8P0g01c5R0p4p710R=p8p100mIp6051000R>P:p8P>P9p8P>P1p8P>P<p8P>P=p8p100oRp6051000R>p100nOp4p710R<p8P>P:p8P>P9p8p1011:p6051000R1P<p8P1P:p8P1P9p8p1017\p6051000R?P<p8P?P:p8P?P>p8P?P1p8P=P9p8g007ej1ITg008Jj1uTg008hj1kTg007Ej1^TP;j21Tg01cZR;j2ETg01MTk20?Tg01:bR9j1HTg01TEk304Tg01KRj2eTP2j3sTP7j32Tg01D1k20ITg01UIk30FTg01JPk30ETg01>Bk40BTg01RRR7k20>Tg009Kj1nTg01d2k10=Tg00@Tj15Tg01J9j29Tg00:Oj24Tg01e1j4hTg01Xgj2jTP8j6ATg01f4j3zTP6j6tTg00<;j3;j1iTP4j4LTg01\nl<vTg01g<k70HTg01hBk20GTg00<UR4j16Tg00>OR6j28Tg00QJj1TTg01hlk20DTg013[R8j2KTg01^0k70CTg01^nk20ATg009mj2NTP5j3BTg01iIj4\Tg01Zmj1[Tg01WHj3ZTg01Ylj1mTg00:fR5j2lTg00>lR2j2DTg00?Hj4RTg00?oj1OTg00C1k10;Tg00D1k20:Tg00DOk109Tg00Dmk408Tg00EKk106Tg00Eik105Tg00G7j2bTg00H_j4WTg00GZk103Tg00Y0k802Tg00IJk201Tg00>5j2dTg00Ilj2}Tg00JXj3~Tg00K7k400Tg00Kij4gTP0j4|Tg01WgR0j2GTg00=5j2{Tg00=Xk307Tg00WAl<YTg00FTj2cTg01XDj3XTP3j4STg00;@j1aTg00O8j3qTg00RKj4`Tg00Vcj3rTg00XLj7yTg00WflB_Tg00H<j3xTf2R3f1R=P9f0R1CSp=]f4R?f3R>A23=132p=0A23=19;?>p=:%H1,N=p=ff7R:f6R<f5R@%a39q?>P=C`;;1p=3P?P>P9AB3=1CSp=<P>P3P=P1C\#Hp=@P?P>P9Ar3=1CSp=C%5==r31p=wP3P=P9P1CS92?>p=Pg00[TR9?;=1p=FP>P3P=P1C\#H,N?p=>%a19q3=p>0@P?P>P3P=C`=;@1p=pP9P?P>P3P=P1Etp==14=1,43p=o14=1,43,4>p=7g00ZXRA/d1p=?P9PAP5P4P2g00]6P@P?P>P3P=P1M<Yp>0<P9PAP;P4P8g01ieP@P?P>P3P=P1M<Yp=QP=g00^?R8g00^^R;P;g00_>R2P1g00_^Fyp=VP9P9P9PAPAPAg01[kP4P4P4P0g01\KP@P?P>P3P=P1MB_p=UP9P9P9PAPAPAg00\3P4P4P4P6g00\SP@P?P>P3P=P1MB_p=MAxA=1p=Jg00aaR6#IR0#I#IR5#u#kRB#^RCp,2evRD'1RE,E1g01_oPCp,3bsbRFPBp,2avRG-0?CRH#HRI%I5#I#IRJ#uRK#kRL%^LRMp,2spRN@04GDRO/eG7sLRP7]BRQ52BRRPBg00[6RS-0IKRT#HRUPBB0FNGDRV/eD9sMLRM9]LBRWPBPUPBp,2phRXB0ENGDp,3uidRYp,2hwRZH0BR[P1D0D0D:R\XFCR]-0>CP7PCP]%nCR]p,4segsR7p,3stkR^PKPN&0=GR_g00Z9#5R`#5#5#5#5#5#5#5Ra/9>'4PaPNPGPDP>Ch,fCG3P1P9PE1E:1X19P@11LMRb1jDVRVEA1E<bPCPWPCPFPBPRPBPUPBP1PBPUPBP[P>D0R>D0D:X2CP=PBPLPBPLP:PMD<PBPLP:PMPTC@PLPBPL%5:PMDCD0RWAzM:1EtPCPFPBPRPBPUPBPWPBPUPBP[P3D0D0D:PCPBPUPBPBPLPBPLf8RWPMD<PBPLPWPMPTC@PLPBPL%5WPMDCD0P>D0R>92BRA;CF1X2CP1PBPIPBPQP>D0RRPBPIPQP>CLEAA;CFRPCPLPBPLf9RRPMD<R>PBPLPRPMPTC@PLPBAwLRMDPRc52BPBPUPBP[P?D0Rd52BPCPFPBPIPBPQPBPUP1D0D:X2CP1PBP>PBPcPdD0RePBP>PcPdCLEAPCPFPBPIPBPQPBPUPeD0D:PCPLf:RePMPTC@RdPLPBPL%5ePMDCRc52BPBPUPBP[P@D0R>52BPCPFPBPIPBPQPBPUPLPBPLf;RfPMD<Rg=2B1D0D:X2CP1PBPdPBPcP>D0RhPBPdPcP>CLEAPCPFPBPIPBPQPBPUPLPBPLPePMD<=2BhD0D:P7PXPNPGPDPYPZp,5rdrawRhPBPIPBPQA2BUgD0RgPLPfPMPTC@RePBPLPBPL%5fPMDCPBPUA2B[<D0R<PaM<vPCPXPNPGPDPYPZPhK0HRfPBPgA2Be<D:PLf<R<PMPTC@Re,1B/Fa20GKN11Bf#6'8%T0%TJ+0D'KRJP]P7PXPNPGPDPYPZPhK0C-0ANRhPKPNPBPIPBPQPLPBPLf>RYPMD<RX92BURgD0,1BPaPLPYPMPTC@RF,NCG3[[[PCPBPQPBPUPLPBPLP<PMD<D0R>92BIPBPePBPLPBPL%5<PMDCPBPUPBP[P:D0D0R:52BA;Cf111BF/FaP]P7PhPKPNPBPQPBPUPLPBPLf@R<PMD<D0Re92BI,1BRcPaPLP<PMPTC@R<,NCRdG3\J[Ri[X2CP1PBPIPBP>P:D0RjPBPIP>P:CLEAA;CfjPLf=RjPMPTC@R:,1B/FaP]P7PhPKPNPBPIPBPQPBPUPLPBf?R>=BLMDPD0,1BPaPLP>PMPTC\Rk#HRl,NCG3Rm\J[[PCPBPUPLPBABLjMDPRn92BQPBP:PBPLPBPL%5jPMDCPBPUPBP[PWD0D0RW52BPCPfPBPIP1D:11Bl/FaP]P7PhPKPNPBPUPLPBfARl=BLMDPRj92BQR:92BI,1BPaPCPLPlPMPTD>RlG3\J[Ro[X2CP1PBPQPBPnPWD0RpPBPQPnPWCLEAPCPfPBPIPpD:Pi[PCPBPFPBPLPBPL%5YPMDCPBPUPBP[PRD0D0RR92BgPCPfPBPIA2BQ1D:11B</FaP]P7PhPKPNPBPIPBPQPLPBPLfBR<PMD<Rg92BUR[D0,1BPaPCPLP<PMPTD>RYG3\J[[X2CP1PBPUPBPXPRD0RJPBPUPXPRCLEAPCPfPBPIA2BQJD:Po[P1P?%[kg01a0O3PmPcP]P7PhB0@KN1RcPaPlEpX19P111BIRm11Be'4RkAZBIeD=P]P7PhPKPNPkPaPdG311B:P]P7PhPKPN14m1PaPYG3X19P111BQR:11Bj'4RdAZBQjD=P]P7PhPKPN14mdPaPlG311B[P]P7PhPKPNAom:1PaPCPLfCR[PMPTD>RlG3X19P111BURd11Bg'4RjAZBUgD=P]P7PhPKPNAom:jPaPYG3P:P]P7PhPKPNPmP1PdfDR:=BLMRY9]LB,1BRjC7PaPCPLP:PMPTD>R:G3X19P111LPRg,9aRU%mPD=P]P7PhPKPNPmPUPdPLPBPLP[PMD<,1BC7PaPlG3PjP]P7PhPKPNPmPUPdP1C7PaPCPLfERjPMPTD>RlG3X19P111LY,9aR[%mYD=P]P7PhPKPNPmPUPdP[C7PaP:G3PgP]P7PhPKPNPm19a1RgPdfFR:=BLM,1LR[,9aC7PaPCPLP:PMPTD>RUG3X19P111CGRY1jGOD=P]P7PhPKPNPm19aYROPdABLjM,1L,9aC7PaPlG3P[P]P7PhPKPNPmPOPdPgC7PaPCPLfGRgPMPTD>R[G3X19P1P:PLPMP:P9PE1lg1X191l:E%6:Rl%6ERj'DP:Pl%?lRPPEPj%?jRQJ0<1E:b%6bRk,KlReP:PlPPPbPk%?kRPEQP>CRPe1EgE%6gRe/KjR>PgPe%?ePEPjPQEQP:CRP>fHR>#O%6>,DS%ObRe1DSkRl%OERI1DSjR?P^PZO1RZ%nBRBg00bFRo$0;RJ%^oRoPA20:A3P=&09AH08Rf&06ARR&05ARXP8P;P;P2PA1bA6R8g01jG1bA0R0CW,VX&03;PAP8g00]XP0CW,VXL02201X2R2P1P3g00dER;g00deRF'd1}13=;;FdA~AS=H00RFb9b:b;X4AX5A1K1=1D=3[^4A^5AP1PjfM#6P@O3b8b?b>b=b<b7b6CgPbPVEAC|D=P]P7PhPKPNPmPOPd19a:C7PaPUG3PmP]P7PhPKPNP1POPd19a>RmC7PaPCPLP>PMPTD>R>G3X19P1Pa%[HD=P]P7PhPKPNPaPOPd19agC7PaP[G3PdP]P7PhPKPNPaPOP1fIRd,9aR[C7PaPCPLPdPMPTD>G3X19P1Pa%[TD=P]P7PhPKPNPaPOPaPmC7PaP>G314a[R>,4ORm,4aRh14Y`Rg,9aRH,4aRU/4[R:'FRV%T5R5%6YR@,G5R3%6dR;,G5Ri,85Rp'8RW'8Rn%T6R6,8@Rq,G5Rr,85Rs/8iRt5;AP9PA%i9P4%iA%6=%615;A1F=11{=1407XI9XH9PhPnPaP5%?5RnPmPWPOP3PaP5PnPYP@%?@R3EUP>PpPaP5PnP[PiPaP5PnPdP;%?;RpEUR>EMEMEMP:PtPUPsPaP5PnPHPrPaP5PnPgPqPYP@P3P`P6%?6EMEUEMP[PiP>EMM<Y1Edb1K;kR>PdP;PpPbPkPPEQP<CRP>fJR>/EE%6>R</KjRPP>P<%?<PEPjPQEQPdCRPPfKRP#O%6P,DS%OY1DS@PePlPIP?PZPBPJPoPfPRPA1cA5RRAXAR8AXAR0R0,JR'J'Jg00c^1cA6,J89XAR,JR/J0CW,VXP2PFb9b:b;X4AX5A1G511G5=RF,85'8,851816,G5,85/8F5;A^4A^5AP1fQ#6P@O2b8b?bCb>b=b<b7b6CgPVPaPOPa19a>R>C7P]P7P^PcPaPCPLPPPMPTD>EpX19P=14U>P1D=b@P]P7P^PKPN14_[PaPNPGPDPdCh,fCG3eb0b0b0b0b0b0b0b0b0b0b0b0b0b0b3b3b3b3bBX3\XGCP=P1O2n2011000000121100000bDWAXE9o"). Qed.

  (* [comment removed for export] *)
  Lemma read_envp_null :
    rdn segs stk (sp + nat_to_word (envp_off av + 8 * length ev)) 8%nat
    = Some (word_le8 (Z_to_bv 64 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) ["Layout"] "p'0h01Hh11nh21lh34__x1h44__x2h51Eh62H0h77__arithh84__ffh98__varmaph:5__with;4cstrh<5cstr0h=1eh>3stkh?9strs_tailh@2tlhA1xi001xhB1yp;1p;2p;3p;4p;<p;7p;6p;Bp-1R0p10000p4p710R1p8P0g000GR2p4p710p8P0P2p4p7210p8P0g000dR3p4p710p8P0P3p4p7210p8P0p1001Ap4p710R0p8g017>R4p4p710R5g002:R6p4p710R7p8P5g002VR8p4p710R9p8p10034p6051000R:P1p8P:P7p8P:p10043p4p710R;p8P:P0p8p1004Up6051000R:P1p8P:P7p8P:P;p8P:P0p8p1005^p6051000R:P1p8P:P;p8P:P0p8p100kFp6051000R0P5p8P0p100NYp4p710R5p8P0g00goR:p4p710R;p8P0g00hOR1p4p710R7p8P0p1006fp4p710R0p8p100mIp6051000R<P5p8P<P9p8P<P;p8P<P7p8P<P0p8p100oRp6051000R<p100nOp4p710R7p8P<P5p8P<P9p8p1011:p6051000R;P7p8P;P5p8P;P9p8p1017\p6051000R=P7p8P=P5p8P=P<p8P=P;p8P0P9p8g007ej1=Tg008Jj1ZTg008hj1LTg007Ej1DTg01MTj2~Tg01:bR9j1UTg01TEj3qTg01KRj2JTP2j3MTP3j4KTP1j35Tg01D1j2_Tg01UIj3\Tg01JPj3}Tg01>Bj4|Tg00<;j32j1VTg01RRR1j2wTg009Kj1OTg01d2j1pTg00@Tj18TP:j26Tg01J9j2?Tg00:Oj20Tg009mj2fTg01\nl<dTg01g<j7cTg01hBj2bTg00<UR:j1>Tg00>OR3j24Tg00QJj1ATg01hlj2aTg013[j2`Tg01^0j7^Tg01^nj2]TP4j4BTP8j6CTg01Zmj1HTg01WHj3GTP6j6WTg01Ylj1{Tg01Xgj2zTg01WgR6j2:Tg00=5j2yTg00=Xj3xTg00>5j2@Tg00WAl<vTg00?oj1RTg00>lj2NTg00C1j1rTg00D1j2oTg00DOj1nTg00Dmj4mTg00EKj1lTg00Eij1kTg00FTj2QTg00G7j2PTg01XDj3FTg00H_j4jTg00XLj7iTg00IJj2hTg00Ilj2gTg00JXj3sTg00K7j4tTg00Kij4uTg00;@j1STg00O8j3TTg00RKj4XTg00WflBITg00H<j3eTf4R8f3R4f2R2f1R0f0R;3535p=3f7f6R=f5R<%S29T84P0CX;2;p=1%S;9T20p=[P8P4P2P0CX=2<;p=Yg00[TR5P8P4P2P0P;EWp=9100;,02p=7P5P5P5g00ZXR7P7P7g01[kP:P:P:P6g01\KP<P8P4P2P0P;MBIp=EP5P5P5P7P7P7g00\3P:P:P:P3g00\SP<P8P4P2P0P;MBIp=;Ae70;p=<g01_og00aaR3#=R6#=#=R>#Z#LR?#DR@p,3bsbP?p,2avRA,~@RB#URC%=>#=#=RD#ZRE#LRFP?P9%DFRGp,2spRHp,2evRI7qARJ/JA7MFRKCKRL55?RMP?g00[6RN,_ERO#URPP?PFP?P9A\HAI/JI9MGFCKRGP?PPp,2phR9A}HAIp,3uidRQp,2hwRRC|RS=5?;D3D352@RTX?@RU'wP1P@PU%O@RUp,4segsR1p,3stkRVPEPH%pAg00Z9#8RW#8#8#8#8#8#8#8RX16@IRY'?RZ'0PX1f@PR[G1R\P;P1P9PHPAPIPQPRp,5rdrawR]A5?PGR^95?MR_PPA5?S0R`PXM<dP9PHPAPIPQPRP]FcRaP?P_P?PPP`D352@16?PR`=25XRb1bEH16?a#>'4%A6%AD'a'`RDPUP1P9PHPAPIPQPRP]F^,]HR]PEPH16?_PXP[G1[[RQ[P@P?PPP?PSP2D3RI95?_A2@a;PQ[X2@R9P;P?PMP?P^PID3RcP?PMP^PICBECA2@acPQ[P@P?P^P?PPA5?S4D3Rc95?MP9P;P?PCP?PLPcD3R9P?PCPLPcCBECA2@a9PQ[P@P?PPP?PSP8D3R895?^P?PCP?PLP;D392@aPQ[X2@P;P?PPP?PGP8D3R9P?PPPGP8CBECP?PCP?PLP9D392@aPQ[P@P_P?PCP?PLP?PPP?PGP?PPP?PSP=D3D3D392@aPUP1P]PEPH16?4PXP[G1\D\b[X2@P;A5?L^R495?CR=P?PCPLP^CBECP?PCP?PLP?PPP?PGP?PPP?PSP<D3D3D392@aPUP1P]PEPH16?=R=PXP[G1Ra\D\b[P;P<%HOROg01a0O3PaP=PUP1P]A[EH;R=PXP[EYX15P;16?CRa16?4R<'0RbAG?C4D9PUP1P]PEPHPbPXP[G1P<PUP1P]PEPH10a;PXP[G1X15P;16?LR<16?^Rb'0R4AG?L^D9PUP1P]PEPH10a4PXP[G1PbPUP1P]PEPHA7a<;PXP[G1X15P;16?GRb,0`R4AG?PGD9PUP1P]PEPHA7a<4PXP[G1P5PbPUP1P]PEPH10`;97a<PXP[G1X15P;PZg01jnEWPUP1P]PEPHA7<`ZRb,0aPXP[G1PaPUP1P]PEPH10;bPXP[G1X15P;PX%HBD9PUP1P]PEPH10XbPXP[G1P`PUP1P]PEPH10;Z97X<PXP[G1X15P;PXPOD9PUP1P]PEPH10XZRO97X<PXP[G1P<PUP1P]PEPHA7X;OPXP[G1X15P;16FKRF,?XR<%{KD9PUP1P]PEPHA7X<OPXP[G1PFPUP1P]PEPH1?X;=7XOPXP[G1X15P;16@ARF1zAJD9PUP1P]PEPH1?XFRH/0ORE,0XR]PXP[G110FWRJ,?XRA,0XR</0ZRK925]R`%A>R>%>FRb,:>RB%>YRa,:>R4,4>RG'4RP'4R^%A3RL,4bRC,:>RD,4>RS/44R_527P5P7%V5P:%V7%>0%>;527A250;1y0;3xXB5XA5P]P^PXP>1@7>R^PEPPPHPBPXP>P^PFPb1@7bRBEEPOPGPXP>P^PZP4PXP>P^PYPa1@7aEERGE;E;E;PKP_P<PSPXP>P^PAPDPXP>P^PJPCPFPbPBPWPL1@7LE;EEE;PZP4PGE;M<v%RF1NNb%RY1NNaPVPRO1%O?g00bFR?#r%D?P71o72P0%n7Cm%l7%k7R?g00^?g00^^RRPRg00_>RRP71Q7>RY1P73R39F7Y1P769F7YR6,<Y'<'<g00c^1Q7L,<39F7Y,<Y/<6Cjg00_^Fi1h?RP;P2g00dERRg00deR?'@1g;2=2R?dAs7N0Ctb8b9b:X37X471:>;1:>0RN,4>'4,4>14;L,:>,4>/4N527^37^47P;PaPbO2b7b>b<b;CuP`P]PUP1PVP=PXP[EYX15P0PKP;D9b6P\eb0b0b0b0b0b0b0b0b0b0b0b0b0b0X5TX@@P0P;O2n2011000000121100000b=o"). Qed.

  (* [comment removed for export] *)
  Lemma read_auxv_all :
    rdn segs stk (sp + nat_to_word (auxv_off av ev)) 160%nat
    = Some (auxv_bytes ph (at_random_ptr sp av ev) uid hw).
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) ["Layout"] "p'0h01Hh11nh21lh34__x1h44__x2h51Eh62H0h77__arithh84__ffh98__varmaph:5__with;4cstrh<5cstr0h=1eh>3stkh?9strs_tailh@2tlhA1xi001xhB1yp&0p;1p;2p;3p;4p;<p;7p;6p;Bp-1R0p10000p4p710R1p8P0g000GR2p4p710p8P0P2p4p7210p8P0g000dR3p4p710p8P0P3p4p7210p8P0p1001Ap4p710R0p8g017>R4p4p710R5g002:R6p4p710R7p8P5g002VR8p4p710R9p8p10034p6051000R:P1p8P:P7p8P:p10043p4p710R;p8P:P0p8p1004Up6051000R:P1p8P:P7p8P:P;p8P:P0p8p1005^p6051000R:P1p8P:P;p8P:P0p8p100kFp6051000R0P5p8P0p100NYp4p710R5p8P0g00goR:p4p710R;p8P0g00hOR1p4p710R7p8P0p1006fp4p710R0p8p100mIp6051000R<P5p8P<P9p8P<P;p8P<P7p8P<P0p8p100oRp6051000R<p100nOp4p710R7p8P<P5p8P<P9p8p1011:p6051000R;P7p8P;P5p8P;P9p8p1017\p6051000R=P7p8P=P5p8P=P<p8P=P;p8P0P9p8g007ej1?Tg008Jj1\Tg008hj1NTg007Ej1ITg01MTk206Tg01:bR9j1TTg01TEj3vTg01KRj2ZTP2j3LTP3j4YTP1j32Tg01D1j2bTg01UIj3`Tg01JPk305Tg01>Bk403Tg01RRR1k201Tg009Kj1KTg01l2j2uTg00@Tj10Tg009mj2gTg01\nl<fTg01g<j7dTP:j25Tg00<;j36j1STg01hBj2cTg00<UR:j1BTg00>OR3j24Tg00QJj1DTg01hlj2aTg013[j2_Tg01^0j7^Tg01^nj2]TP4j4CTP8j6ATg01m1k404Tg00:Oj21Tg01WHj3HTg01J9j2>TP6j6VTg01Zmj1UTg01Ylk100Tg01Xgj2~Tg01WgR6j2:Tg00=5j2}Tg00=Xj3|Tg00>5j2@Tg00WAl<tTg00?oj1RTg00>lj2OTg00C1j1rTg00D1j2qTg00DOj1oTg00Dmj4mTg00EKj1lTg00Eij1pTg00FTj2PTg00G7j2QTg01XDj3FTg00H_j4wTg00XLj7xTg00IJj2iTg00Ilj2hTg00JXj3yTg00K7j4zTg00Kij4{Tg00;@j1JTg00O8j3MTg00RKj4[Tg00WflBXTg00H<j3eTf4R8f3R4f2R2f1R0f0R;3232p=7A220;9684p==%0;#0p=s%0;#0#0#0p=n%0;#0#0#0#0#0#0#0p=k%0;#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=j%0;#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=Ef7R=f6R<f5R5%J29M84P0C[;6;p=3%J;9M20p>02P8P4P2P0C[=65;p=Wg00[TR7P8P4P2P0P;EVp=9110;,12p=8P7P7P7g00ZXR>P>P>g01[kP:P:P:P6g01\KP5P8P4P2P0P;MBXp=GP7P7P7P>P>P>g00\3P:P:P:P3g00\SP5P8P4P2P0P;MBXp=;Ae>0;p=<g01_og00aaR3#?R6#?#?R?#\#NR@#IRAPAp,3bsbP@p,2avRB-06ARC#TRD%??#?#?RE#\RF#NRGP@P9%IGRHp,2spRIp,2evRJ7vBRK/ZB7LGRLCYRM52@RNP@g00[6RO,bFRP#TRQP@PGP@P9A`IBJ/ZJ9LHGCYRHP@PQP@p,2phR9B05IBJRRp,3uidRSp,2hwRTH03RUP;D7D7D=RVX?ARW+01P1PAPW%KARWp,4segsR1p,3stkRXPFPI1uBJg00Z9#0RY#0#s#nRZ#k#j#E#E#E#ER[1gAUR\G3R]P;P1P9PIPBPJPSPTp,5rdrawR^A2@HQR_92@QR`92@NRaPUP0P[M<fPAP9PIPBPJPSPTP^FdRbP@PaA2@U0D=15@U=67[Rc1cFI15@b#B'4%D6%DE'a'_REPWP1P9PIPBPJPSPTP^F^,]IR^PFPI15@aP[P\G3[[Rd[PAA2@U2Re92@aA6Ab;Pd[X2ARfP;P@PNP@P`PeD7RgP@PNP`PeCCEAA6AbgPd[PAP@P`P@PUP4D7Rg92@NPfP;P@PDP@PMPgD7RfP@PDPMPgCCEAA6AbfPd[PAA2@U8R892@`PAPbP@PDA2@M;D=Pd[X2AP;P@PQP@P_P8D7RfP@PQP_P8CCEAPAPbP@PDA2@MfD=Pd[PAA2@U5R592@_PAPbP@PDP@PMP@PQP;D7D=Pd[X2AP;P@PHP@PQP5D7RfP@PHPQP5CCEAPAPbP@PDP@PMP@PQPfD7D=Pd[PAPaPAPbP@PDP@PMP@PQP@PHP@PQA2@U=D7D7D=PWP1P^PFPI15@4P[P\G3\E\c[X2AP;A2@M`R492@DR=P@PDPMP`CCEAPAPbP@PDP@PMP@PQP@PHP@PQA2@U<D7D7D=PWP1P^PFPI15@=R=P[P\G3RU\E\c[P;P<P9PRPSPTH04g01a0O3PUP=PWP1P^B02FI;R=P[P\EWX17P;15@DRU15@4RS'1RRAH@D4D9PWP1P^PFPIPRP[P\G3PSPWP1P^PFPI11U;P[P\G3X17P;15@MRS15@`RR'1R4AH@M`D9PWP1P^PFPI11U4P[P\G3PRPWP1P^PFPIA8US;P[P\G3X17P;15@QRR15@_R4'1R`AH@Q_D9PWP1P^PFPIA8US`P[P\G3P4PWP1P^PFPI11R;98USP[P\G3X17P;15@HR4/1RR`AH@HQD9PWP1P^PFPI11R`98USP[P\G3P7P4PWP1P^PFPIA8R;R98USP[P\G3X17P;15AJRJ,>ZR4g01jnEVPWP1P^PFPI114R98SRR`,1UP[P\G3PUPWP1P^PFPI11;`P[P\G3X17P;PZ%UCD9PWP1P^PFPI11Z`P[P\G3PRPWP1P^PFPIA8;4;98ZSP[P\G3X17P;PZ%UPD9PWP1P^PFPI114ZRP,1ZRR98ZSP[P\G3PSPWP1P^PFPIA8Z;RP[P\G3X17P;15GLRG,>ZRS&00LD9PWP1P^PFPIA8ZSRP[P\G3PGPWP1P^PFPI1>Z;=8ZRP[P\G3X17P;15ABRG1~BKD9PWP1P^PFPI1>ZGRI/1RRF,1ZR^P[P\G311GYRK,>ZRB,1ZRS11JYRL,>ZR`'1RC967^RU%D?R?%BGRH,:?RQ%BJR_,:?RM/4?RD,4?R9'4R<'4Rc%D3RE,4HRb,:?Ra,4?Rd14_ERf,:?R5'4R856>P7P>%S7P:%S>%B0%B;56>A670;1}0;3|XB7XA7P^PcPZP?1@>?RcPFP<PIPQPZP?PcPGPH1@>HRQEGPRP9PZP?PcPPPDP4PMPZP?PcPJP_1@>_RMEGPZP?PcE;E;E;E;PCP8PSPdPZP?PcPBPaPZP?PcPKPbPGPHPQPYPE1@>ERQE;EGE;P`P5PZP?PcPLPfPJP_PMPYPEPQE;EGE;M<t%RG1OOH%RJ1OO_PXPTO1%K@g00bFR@#r%I@P>1q>2P0%o>Cm%l>%p>R@g00^?g00^^RTPTg00_>RTP>1P>?RJ1Q>3R39F>J1Q>6R69F>J/<J,<J'<'<g00c^1P>ERG,<39F>J,<J1<6G9F>J'<Cwg00_^Fx1i@TP;P2g00dERTg00deR@'@1h;2=6T@dAy>O0Czb8b9b:X3>X4>1:?;1:?0/4?,4?'4,4?14;E,:?,4?140E,:?'456>^3>^4>P;P_PHO2b7b>b<b;C{PUP^PWP1PXP=P[P\EWX17P0PCP;D9b6P]eb0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0X5VX@AP0P;O2n2011000010121100000b=o"). Qed.

  (* [comment removed for export] *)
  Lemma read_auxv_word : forall j, (j < 20)%nat ->
    rdn segs stk (sp + nat_to_word (auxv_off av ev + 8 * j)) 8%nat
    = Some (word_le8 (nth j (auxv_words ph (at_random_ptr sp av ev) uid hw) (Z_to_bv 64 0))).
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) ["Layout"] "h04__x1h11nh23Hj0h37__arithh44__ffh58__varmaph65__with74cstrh83stkh91lh:2Hjh;1bh<1jh=1oh>1xh?1yp&0p;2p;1p;3p;4p;5p;<p;6p;8p;9p;Bp;7p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0g000dR2p4p710p8P0P2p4p7210p8P0p1001Ap4p710R0p8p1001]p4p710R3g002:R4p4p710R5p8P3g002VR6p4p710R7p8p10034p6051000R8P1p8P8P5p8P8p10043p4p710R9p8P8P0p8p1004Up6051000R8P1p8P8P5p8P8P9p8P8P0p8p1005^p6051000R8P1p8P8P9p8P8P0p8g00kFR0p6051000R8P3p8P8g00NYR3p4p710R9p8P8g00goR1p4p710R5p8P8g00hOR:p4p710R;p8P8g01c5R8p4p710R<p8g00mIR=p6051000R>P9p8P>P7p8P>P5p8P>P;p8P>P<p8p100oRp6051000R>p100nOp4p710R;p8P>P9p8P>P7p8p1011:p6051000R5P;p8P5P9p8P5P7p8p1017\p6051000R?P;p8P?P9p8P?P>p8P?P5p8P<P7p8g01cZR7j2CTg007ej12Tg008Jj1VTg008hj1RTg01l2j2kTg00;@j1DTg00O8j3GTg01J9j2<Tg007Ej1JTg009Kj1ITg00RKj4[Tg01JPk306Tg01?Ak403Tg01D1j2zTg01iIj4TTg01:bR<j1STg009mj2Qj1gTg00<;j31j1KTg01>Bj4mTg00Vcj38TP3j3;Tg00>5j25TP2j4?Tg00@Tj10TP:j3XTg01Zmj1`TP0j5_TP1j2=Tg00QJj1FTg00<UR1j1:Tg01WgR0j2BTg00=5j2^Tg00=Xj3]Tg00WAl<ETg00U>k108Tg013[R:j2ZTg00?Hk405Tg00?ok104Tg00>lR2j26Tg00C1k102Tg00D1k201Tg00EKj1}Tg00Eij1yTg00FTj2>Tg00G7j2xTg01XDj3vTg00H_j47Tg00IJj2uTg00Ilj2tTg00JXj3sTg00K7j4pTg00Kij4@Tg00:fR3j2ATg00GZj1oTg01n7j4lTP6j64TP8j4nTg01Ylj1jTP=j5iTg01f4j3qTg01o?j4hTg020Fj8rTg00:Oj2MTg00>OR=j2UTg00A3j2LTg00A\j3fTg00BEj2eTg020cj2dTg00CQj3{Tg00H<j3|Tg021Ol9cTg00T;j3~TP4k600Tg00WflBWTg00XLj7bTg00Y0j8aTf0R4#0#0p=Y%04#0#0#0p=H%04#0#0#0#0#0#0#0p=Ng00[TR8P8P8g00ZXR6P6P6g01[kP1P1P1P0g01\Kf5R0f4R5f3R?f2R>f1R9P4MBWp=\P8P6P7P1P:g01ieP0P5P?P>P9P4M<Ep>07P9g00^?R:g00^^R7P7g00_>R;P4g00_^Fbp=9P8P6P3P1P2g00]6P0P5P?P>P9P4M<Ep=PP?P:P7P7P;P>P9P4Gap=O%04#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=3P8P8P8P6P6P6g00\3P1P1P1P=g00\SP0P5P?P>P9P4MBWp=wg00Z9R5#YR=#Y#HR:#H#NR2,C4g00aaR3#2R@#2#2RA#2#2#2#VRB#RRCp,2spRDp,2avREp,2evRF'kRG#D5GBRH1<:9RI#D5GBRJ%VA#RRK#JRL#IRMp,4segsRNp,3stkROP4P:C[PCP>p,2phRPB06DEFRFp,3uidREp,2hwRQH03RRg00[6RS,zBRTCT#SRU,QLRV31X;CPMPPPFPEPQCmRW98KI9;K:RX,QLA1M4VX=MPLPM%gLRVPVPXPCP9PRPTCTRT#SRXPM\L/5VPLPCPKP<PRC?RV1<:>RM=8K49;K:=1LUX9LRYPLPCPKP<A;C9RRZC?R[PCPKP<%09=8CRC?R<9XKXR\5XKR]PYPLP\A;K:4=1LUX9LPKPXP<P:%`TD_A8KI]PKP[P\PIP81=CZR\,<:A184MX18P8P91<:4=18MX18A18II%FARA%:9RM'BR]=16]P8P6%K8P1%K6%:4916MA18941^943]X?8X>8PIP]P:PA156AR1P9PM156MRTE\R<PIP]P<M<E1C92&08@#2#2R@#FRX,ZMRLP9PMPTP2PX156XRUJ07P4H05RYPL&04>R^%:>,6SR_POPQO1R`%IKRag00bFRb$02Rc%JbRd20169Re%}6Rf%y6RgP61>6ARh1x63R35v6Rig00c^PiC7'91ug;R;P4P>g00dERjg00deRk'51t4>=1jkdAs6S9CpRSb4b5b6X061BA4Rk=16k^06P4%:0R0O1b3b8b7b2C@P\PCPRP9P8P21A>4X181A9216MXP9PMPTP2PXPUEPPYPLP^P_P`PaPcPdPePfPgP6P3g01jG1>6XRUC7,9gRT%o7R7P6P3g00]XR3PUC7,9gCOP;PSb4b5b6X061Z4XRU169X[^06P4P0P?O2R?b3b8b7b2C@1=CRRCPPPFPEPQClR0E4CnE41=K[%jZE4DiE4PVP8P21C>4X18P4PCP0E49qR9E4PWPPPFPEPQChE4GrPNPOPJP:C[PNPO%H2#N#3#3#3#3#3#3#3#3R2PHPWPIP:g022O1MI:RW/A21U]ARH%2@#2#2#FR@'6PWPHPIP]P<P:PAP1EwP2P@156@EPPYPLP^P_P`Pa1L65R51L6=9f65g00c2'e'd={bcPdPePfPgPTP7P6A|6ihP31>6@C7,9gCOP;PSb4b5b6X061BA9/UA/6@\U^06P?b3b8b7b2C@M9cE41MGI#D9GBDA~DGIJ00W:X<8o"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma bsb_random_split : exists pre,
    bsb = pre ++ at_random_bytes (ed_random rdraw)
    /\ at_random_ptr sp av ev = sp + nat_to_word (length pre)
    /\ (Z.of_nat (length pre) mod 8 = 0)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) ["Layout"] "p'0h01nh11lh24__x1h33preh41Hh57__arithh64__ffh78__varmaph85__with94cstrh:5cstr0h;5cstr1h<5cstr2h=5cstr3h>5heq_Lh?6heq_L0h@3stkhA1zhB2H0hC2H1hD3H10hE2H2hF2H3hG2H4hH2H5hI2H6hJ2H7hK2H8hL2H9hM6__sat4hN6__sat5hO4__x2hP4__x3hQ4__x4hR4__x5hS1phT1qhU2q0hV1rhW2r0hX3HpdhY1LhZ1xi001xh[1yi019argv_ptrsi021bi03<env_str_basei049envp_ptrsp%0p&0p;1p;2p;4p;3p;6p;Bp;<p;7p;8p-1R0p10000p4p710R1p8P0g000GR2p4p710p8P0P2p4p7210p8P0g000dR3p4p710p8P0P3p4p7210p8P0p1001Ap4p710R0p8g017>R4p4p710R5g002:R6p4p710R7p8P5g002VR8p4p710R9p8p10034p6051000R:P1p8P:P7p8P:p10043p4p710R;p8P:P0p8p1004Up6051000R:P1p8P:P7p8P:P;p8P:P0p8p1005^p6051000R:P1p8P:P;p8P:P0p8p100kFp6051000R0P5p8P0p100NYp4p710R5p8P0g00goR:p4p710R;p8P0g00hOR1p4p710R7p8P0p1006fp4p710R0p8p100mIp6051000R<P5p8P<P9p8P<P;p8P<P7p8P<P0p8p100oRp6051000R<g00nOR7p4p710R;p8P<P5p8P<P9p8p1011:p6051000R=P;p8P=P5p8P=P9p8p1017\p6051000R>P;p8P>P5p8P>P<p8P>P=p8P0P9p8g007ej1ETg008Jk102Tg008hj1|Tg007Ej1jTg018fR9k20kTg00@Tj10TP:j27Tg00:Oj21Tg01J9j2RTg01NLj1vTg00QJj1mTg01>Bk40_Tg01KRj2pTP2k304Tg01LSk100Tg01;Zj4~Tg01MTk20YTg01:bR2j1}TP3j4_Tg01D1j2xTP1j35Tg01PPk10JTg01QNk10ITg01RRj2WTg00<;j36k101Tg00>5j2VTP4j4QTP6j6<Tg00<UR6j14Tg01OPj22Tg012?j2:TP7j3qTg00>OR7j23Tg01WgR4j2DTg00U>k103Tg00=5k20\Tg00=Xk30ZTg00?Hj4oTg00?oj1UTg009Kk10XTg00LTk10VTg00M2k20UTg00A3j2yTg00MSk30TTg00A\k30STg00BEk20RTg00C1k10OTg00CQk30NTg00D1j2nTg00DOk10MTg00Dmj4lTg00EKk10LTg00Eik10KTg00G7j2ZTg00FTj2^Tg01XDj3bTg00GZk10HTg00IJk20FTg00Ilk20ETg00JXk30DTg00K7k40CTg00Kik40BTg01P0j1[Tg00H_j4hTg013[j2>Tg023Sk30Aj2]Tg0147S00j2CTg024:k20@k30?Tg024kj2gTg01DWk10>Tg025Lj2ATg025ij2\Tg00>lj2YTg026Pj2cTg0276j2dTg014lk30=Tg027\k30<TP8j6NTg028Ck30;Tg028jk20PTg00\SR8k20QTg029Hj4tTg029cj1{Tg01m1k40jTg01Zmk10:Tg01Xgk209Tg01Ylk107Tg02:gk30gTg01Rlk40dTg01SFk206Tg01JPk30bTg00;@j1rTg00O8j3sTg00WfmB08Tg00WAm<0aTg00H<k30cTg00XLk70`Tg00Y0k80eTg01WHk30fTf0R1#0#0p>0[%01#0#0#0p>0Wf4R3f3R:f2R0#4f1R='2':/21#['1p=@%r19s0=p=IA50=1953:p=;f5R>%40/2=,::/21#[7q3p=Jg00ZXR<%4=/21g00[6R536p>0GA6:0=/C1p=Mf6R;%r09s3:76>%4=/21=6<5'Cp=917=1,10p=LA6<15p=S%r=9s:096>3/C1p>0i12=1#[p>0511=1,10p=F11=1,10,1:,13p=B12=1,:0p=f%01#0#0#0#0#0#0#0p>0^%01#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p>0]%01#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=eg00[TR??6=1p=TA6<=1p=H1V<1p=GP?P?P?P<P<P<g00\3P6P6P6P7P8P>P3P:P0P=P1NB08p=?P?P?P?P<P<P<g01[kP6P6P6P4g01\KP>P3P:P0P=P1NB08p=aP?P<P1P6P=P0P:P3P>P;f7R6f8R4N<0ap=`1Y51p=8B0c<=1p==P<P=g00c^P1Chp=kP=g00^?R8g00^^R7P7g00_>S01P1g00_^K0`p=XP:P8P7P7Q01P0P=P1L0ep=w13=196<0p=P12=1=6<5p=i%4=/21p=u1:0=/21p=zP?P3P:P0P=P1ENp=KAq0=1,7:p>0hP?P;P>P3P:B0f0=1ENp=Og00aaR8#ER@#ES02#ERA#E#E#E$02RB#|RC#jRD00kCREPDPCp,2spRFg00Z9RG#0RH#0$0[$0WRI&02ARJ#|RK#jRLp,2avRM'7RN/1HS03/RIS04'1S05p,2evRO,7LRP/1HS06/RIS07'1RQp,2phS08g01VJRR,1QRS%vMRT,7KS09'1%vORU,7KRV'1RW%mARAPWPAPAD@9IBFRWp,3uidS0:p,2hwS0;H0_RX,7KRY'15IBRZ/pMS0<:04DCR[&00MR\9IBZR]C~PLP9PDPCPLP=P9PDPCPL1p1OPKPK20YLMS0=#}R^PKPCPKP2P:C_PK1xB5S0>#}R_PKPCPKP2P=C_A5KTUR`95KXRa95K_RbD;RcD;RdPKPK1xJ5RJPA17KdPAPAEJp,5rdraw$0J$0IRdD;n2001100000121104102n2001100000121101103A5K1dRePCPW17K1Rf9IBFS0?20GfAS0@CMS0ACMX3L,WLXSEPEPDPC1p]OS0B:04DCRf&00ORg9IB]C~PLP9PDPCPLP=PKPKP^PKPCPKP2P[C_RhPcD;RcPKPKPJPA17KcPAPAEJPdD;S0Cn2001100000121104102PeQ0ACMX3L,WLXSEPLPLPCPKP2PfC_R2=5KbRE95K_Rc95KhRi95K^RjPKPJPA17KjS0DPAPAEJRk=5KdRl55KRmPeQ0ACMX3LS0EA5KjkRnA5KndRo96LmPCPWPBPF17KnS0FQ0FPAF9PLA5KilRn95K^S0GA6L1oX1LPLA5KclRp95KhS0HA5K^1Rq=6LoX1LPLA5KElRr95K_S0IPKP^PKPhP1D;Rs=6LoX1LPLA5KblRt95K2S0JPKP^PKPhA5K_1RuD;Rv=6LoX1LPLA5KalRw95K_S0KPKP^PKPhPKP_PKP2P1D;D;Rx=6LoX1LPLA5K`lRy95KXRzPKP^PKPhPKP_PKP2PuD;D;Ru=6LoX1LPLPKPTPKPUPlD;R{PKP^PKPhPKP_PKP2PKP_PKPXP1D;D;D;R|=6LoX1LPLPmPKP^PKPhPKP_PKP2PKP_PKPXP{D;D;D;R}=6L1X1LR~PLQ0GP~PLQ0HA6L}qX1LPLQ0IA6L}sX1LPLQ0JA6L}vX1LPLQ0KA6L}xX1LPLPzA6L}uX1LPLP{A6L}|X1L1VL}PyPKPTPUPlCQR}E<PwPKPXP`PlCQR|E<PtPKP_PaPlCQR{E<PrPKP2PbPlCQRuE<PpPKP_PEPlCQRzE<PnPKPhPcPlCQRxE<PmPKP^PiPlCQRlE<PoPKPjPkPdCQE<PyP}E<PwP|E<PtP{E<PrPuE<PpPzE<PnPxE<PmPlE<Q0D?LKkPCPWPBPFP1%41Rl/2ARm#SJ0iX0?17K^Rx17KiS0K'1PCPWPBPF1:Am005AS0J9qKJ9L1KRmPmPAF9X0?17KhRm17KcS0I'1PCPWPBPF11x1RnPKPJPAPnPAPAEJ7LKRnPnPAF9X0?17K_Rn17KES0H'1PCPWPBPFAFxm1RzPKPJPAPzPAPAEJ7LKRzPzPAF9X0?17K2Rz17KbS0G'1PCPWPBPF11n1Rp9FxmRuPKPJPAPuPAPAEJ7LKRuPuPAF9X0?17KaS0L,1nPCPWPBPFPxPmPnPzP1DBRuPKPJPAPuPAPAEJ7LKRuPuPAF9X0?17K`S0M,1YPCPWPBPFPxPmPnPzPpDBRpPKPJPAPpPAPAEJ7LKRpPpPAF9X0?Q09/1VRpPCPWPBPFPxPmPnPzAFnY1DBRuPKPJPAPuPAPAEJ7LKRuPuPAF9X0?11YpRu,1nRr9FnzR{9FxmRt#4=fAA005AS0NPCPWPBPF11t1RtPtPAF9X0?17C[S0O,RIRtPCPWPBPFAFx1{R{PAP{PAPAD@R{P{PAF9X0?17CfS0P,RIR{PCPWPBPFPxPtPnP1PrDBRtPAPtPAPAD@RtPtPAF9X0?PNPCPWPBPFPx1RI1RtPnP{PrDBR{PAP{PAPAD@R{P{PAF9X0?PPPCPWPBPFPx1RINR{PnPtPrDBRtPAPtPAPAD@RtPtPAF9X0?PIPCPWPBPFP1P{Pn1RIPRtPrDBRrPAPrPAPAD@RrPrPAF9X0?PIPCPWPBPFPIP{P1Pt111uDBRuPAPuPAPAD@RuPuPAF9X0?P?PRPCPWPBPFPIP{PIPtAFI1pDBRpPAPpPAPAD@RpPpPAF9X0?P\PC11S1/1VRpPAPpPAPAD@9IBFPBPFPIP{PIPt111V9FIRDBRpPAPpPAPAD@RpPpPAF9X0?PgPC11S\S0Q/11RSPAPSPAPAD@9IBFPBPFPIP{PIPt11\19FIRDBRSPAPSPAPAD@RSPSPAF9X0?&0^I$0]#e#e#e#eRS11\gS0R'1S0S,1IS0T,1tS0U,1IS0V,1{S0W,1IRpP?1V?pS0X1T1pRuePu11QSS0Y/1\S0Z/1gRu,T=%4=Rr%4NR|%m8Rw'3S0[/DAS0\,3AS0]%4PR}/3wS0^/DAS0_'3S0`&03@S0a#E#E#E#E#E#mRy'3S0b%4\Rd'3Ro%4gRv'3Rs'H&01?Rq&01<R~1Hrl1T=120\=140ZX[?XZ?RlP=Pr%GrS0cPuPsQ0ZPoQ0YQ0bPQQ0`Q05Q0]PIPA%GARQQ04Q0\Q03Q0[PNP|%G|S0[PHPw%GwRoE?PIPAPQEaE?Q07Q0_Q06Q0^PPP}%G}S0^PHPwPoE?PIPAPQEaE?PSPy%GyS06E?P\Pd%GdS0_E?PgPv%GvS07E?M9`1T=pS031DA|S0\1DA}S0413dvS0],3yS05,3AS0`'3S0b,3AS0Y'3Ro,3ARs,HrS0ZPqP~PlP=PrQ0cPpPsPIPAPQQ0WPoP{Q0\PIPAPQPNP|Q0[EaQ0VQ0YPIPAPQQ0UQ0bPtQ04PIPAPQPPP}Q0^EaQ0TQ0`PIPAPQQ0SQ05PSPyQ06Q0RQ0]P\PdQ0_PgPvQ07E?E?E?E?E?E?E?S07M9`P1CoQ0Z%U0%40RS#8%UNS0Z%8|S0_%U\S0]%8dS06%UPRP%8}R\%UgRN%8vRQp,3stkQ0;O1S05&0XKS0Sg00bFRo&0V8-0U<1y<H60T<1y<G60S<g00c2+0R&0OoS0`40N%joS0TP<P<1n<3P0&0M<S0^ClP=P<1n<>P:Q0^ClCl&0L<S04&0K<Ro1Z<8RG1^<ARH1Z<@S0b9b<H&038,Z<S0U9b<H1^<yS0YQ02,Z<R8Q0a,Z<R@'='=,=H'=,=H'='='k,Xo&0H7S0aQ0b1^<wR7'==b<H,=HQ0U/=7=b<H'=Q0Y'=/=8/=@,kG,XoCwQ01-0FoR@P1P0g00dER8g00deR7'V20E10=687dB0D<5=H0CR7b6b7b8X2<XO<XP<XQ<XR<1DA=1DA013:3,3y,3A'3,3A'39P1A130w/DA,3A13:w/DA'3/3y/33=P=>[^2<^O<^P<^Q<^R<P1PvPdP}P|f9S01#4S0YP6O6b5b@b=b<b;b:b9b?H0Bb>1T1uP?P=PCQ0J,119IBF12SAR|,:AR}/2ARd#[Rv,10Ry9IBFRw%4yS0J/iAS0UCMX0?AfArARrQ0XQ03eQ031T0pR?1HSsRyPqP~PlP0PS%GSPpPsQ07M9`P1CoPy%U:%4:Ry#8Q0ZQ0_Q0]Q06PPP\PNPQQ05Q0SQ0`Q0TQ0^Q04P<1^<5S0^g01jGPHCh,XoP@P7b6b7b81>5AR8P1b5b@b=b<b;b:b9b?b>80AA12rARr#81>rA'CA6CwwQ0U1VCwP<%4vS0U,3S1i1AXA<S03P<Pd13y1/iAXA<P<13|d/2AS0b%S1XA<RwP<13|}S02/2APwQ0XP?eS0XP?1T:p1HysS0VPqP~PlP:Py%GyPpPsQ07M9`P1CoS07Q0V%U3S0[%43#8S0\Q0ZQ0_Q0]Q06PPP\PNPQQ0Y=fAARs00@AS0Y%8s%8ARsf;#4Rp/2ARl,:AS0W/2A#8[[S0cf:S0d#4@0?A>S0e%8l\sS0f1gpA%SARp$0>Rsf<#4Rl1AlA,DA12lAS0g3P[1]lAf=S0h#4Rl/2AR~#81>~A'C\81\lA1>A5Rlf>#4Rq/2ARw,>A1Yw5'C[1cqAf?#4Rq/AA#S\p1dqAf@#4Rr/2AS0i/Hr\p1ArAP<fA/uAS0jP<1:A1S0k/gA1:A=Rr1ArA,DA12rA3P\s1]rA1:A0S0l/2ARr#81>rA'C\8Q0l/\A1:A:S0l/2ARr,>A1Yr5'C\lQ0l/cA1:A3R3/AA#S\p1d3A1:A>R>/2A/H>\p1A>AP<AzA;AP<Q00%81R;1>1A1:A49PA4fGR>%801>:AQ05Q0SQ0`Q0T1n<=R3Q04B0=<HG,=G,kH,XoP@P7b6b7b8X2<Q0k9PA1^2<P1Q0hO1b5b@WDWLP=P1O2n2001000000120000000bWbUbKbJbIbHbGbVbTbFbEbCbBb4bMbNb=b<b;b:b9b?b>Q02,HAP<PAQ031V<512yARy1:Ay'3P1E<b4Q0bB0<}|AEN13Sd/2AB0;SdAE<Q0UQ0XP?Q07Q0VQ0[Q0\Q0ZQ0_Q0]Q06PPP\PNPQQ0YQ0cQ0eQ0fQ0W/gAQ0g,:ARQ1AQA,DA12QA3P\s1]QA1:A~R~/2ARQ#81>QA'C\81\~A1:AwRw/2AR~,>A1Y~5'C\l1cwAAfAqARq/AA#S\p1dqAQ0i,:ARq/2A/Hq\p1AqAP<Q0j=zAAP<fB#4/gAfC#4Rq1AqA,DA12qA3P\s1]qAfD#4Rq/2ARs#81>sA'C\81\qAfE#4Rq/2AR8,>A1Y85'C\l1cqAfF#4Rq/AA#S\p1dqA%4>Rq/2A/Hq\p1AqAP<fH/uAP<Q00%861>6A%84P>Q01#8Q0d/>AQ05Q0SQ0`Q0TP3Q04PoP<Q0^g00]XPGCh,XoRoQ0aPoCwP@P7b6b7b8X2<%8=\;^2<P1Q0hP:O2b5b@WDWLP=P1O2n2001000000120000000bWbUbKbJbIbHbGbVbTbFbEbCbBb4bMbNb=b<b;b:b9b?b>-0PdENQ0J20Q0vENCtbXPuP1E<b4bYPCQ0Q/1gRgPAPgPAPAD@9IBFPBPFPIP{PIPtQ0R9FIRDBRRPAPRPAPAD@RRPRPAF9ePV%{ODKQ09%{MDKPYQ08PWQ0:Q0;H0jENPnQ0>$0:DKPxQ0=$0:DKQ0P209O]DKQ0O209MZDKPz&07fDKPm&07[DKPKPKPJQ0NH0hQ0N:0gKJDKQ0MPKPTPUFOQ0LPKPXP`FOQ0GPKP_PaFOQ0HPKP2PbFOQ0IPKP_PEFOQ0KPKPhPcFOQ0DPKP^PiFOQ0FPKPjPkFOCtH0dQ0E,WLeQ0B206O]ENPLP9PDPCPLQ0BQ0Cn2001100000121104102PeQ0ACMX3L,WLeQ0<206MZENPLp,3bsbPePCB0bFMOQ0?Q0@CMCMX3L,WLeo"). Qed.

  Lemma at_random_off : exists off : nat,
    at_random_ptr sp av ev = sp + nat_to_word off
    /\ (off + 16 = length bsb)%nat
    /\ (Z.of_nat off mod 8 = 0)%Z
    /\ forall j n, (j + n <= 16)%nat ->
         rdn segs stk (at_random_ptr sp av ev + nat_to_word j) n
         = Some (firstn n (skipn j (at_random_bytes (ed_random rdraw)))).
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) ["Layout"] "p'0h01nh11Eh21Hh32H0h46__sat7h54__x1h64__x2h74__x3h81lh91ah:1xi001xh;2H1h<2H2h=2H3h>2H4h?3HL0h@2HahA4Hjn0hB7__arithhC4__ffhD4__p1hE6__sat5hF6__sat6hG6__sat8hH6__sat9hI8__varmaphJ5__withK4__x4hL1bhM4cstrhN5cstr0hO5cstr1hP5cstr2hQ5cstr3hR5cstr4hS1jhT3prehU1qhV1rhW3stkhX1yhY2H6hZ2HLh[3Hjnh\4Hlenh]5Hlen0h^4Hmodh_2Hph`5cstr5ha1ehb1mhc3offhd2z6p%0p&0p;1p;3p;2p;7p;6p;4p;=p;<p;Bp;8p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000dR2p4p710p8P0P2p4p7210p8P0p1001Ap4p710R0p8g01WHR2p4p710R3g002:R4p4p710R5p8P3g002VR6p4p710R7p8p10034p6051000R8P1p8P8P5p8P8p10043p4p710R9p8P8P0p8p1004Up6051000R8P1p8P8P5p8P8P9p8P8P0p8p1005^p6051000R8P1p8P8P9p8P8P0p8p100kFp6051000R0P3p8P0g00NYR3p4p710R8p8P0g00goR9p4p710R1p8P0g00hOR5p4p710R:p8P0g02;IR0p4p710R;p8p100mIp6051000R<P8p8P<P7p8P<P1p8P<P:p8P<P;p8p100oRp6051000R<p100nOp4p710R:p8P<P8p8P<P7p8p1011:p6051000R1P:p8P1P8p8P1P7p8p1017\p6051000R=P:p8P=P8p8P=P<p8P=P1p8P;P7p8g007ej1JTg008Jk102Tg008hj1jTg007Ej1pTg01PPk10[Tg01QNk10RTP5j33Tg00<;j32j1|Tg01JPk30GTP9j20Tg00QJj1^Tg0147R9j26Tg01RRR5j2}Tg00@Tj1STg00:Oj25Tg00<UR7j11Tg01OPj2?Tg00:fR;j2PTg009Kj1kTg00;@j1vTg00O8j3[Tg00Vcj39TP3j34Tg009mj2FTg02;jk10@Tg00>5j2KTP2j3hTg01g<k70:TP6j6TTP0j3oTg017>k406TP4j6{Tg01\nm=03Tg01hBk20ZTg00>OR4j2ETg01hlk20WTg013[j2ATg01^0k70VTg01^nk20UTg00>lR0j2;Tg00=5k20QTg00=Xk30PTg02=5j3zTg02=[j6yTg00?Hj4LTg00?oj1BTg024:j3xTg02>Ek20NTg02>mk30MTg024kj2uTg01DWk10LTg025Lj2QTg01Wgj2nTg023Sj2mTg025ij2qTg026Pj2rTg0276j2sTg00A3j2XTg00LTk10ITg00M2k20HTg00MSj3iTg00A\j3VTg00BEj2aTg00C1k10FTg00CQj3bTg00D1j2gTg00DOk10DTg00EKk10CTg00Eik10BTg00FTj2fTg00G7j2WTg00GZk10ATg00H<j3dTg00IJk20?Tg00Ilk20>Tg00JXk30=Tg00K7k40<Tg00Kij4cTg01c5j4eTg00iKk20;Tg012?j2RTg012\j2\Tg0139k20ETg014Rj2lTg010Vk608Tg00U>j1wTg014lk30JTg015Ok707Tg02?Qk30KTg00T;k305Tg029Hj4`Tg01Rlk40OTg00RKk404Tg00WAm<01Tg00WflB~Tg00Dmk40STg00H_k400Tg00XLk70TTg00Y0k80YTg0163k70XTf2R6f1R2f0R3#v3[p=8%12/?3p=Hg00ZXR1g00[6R=723p=>%S3#Sp=Ng00[TR<?223p=7f5R8f4R:f3R>P6P2H04;23p=CP<P:P>P6P2P3ETp=M1K13p=@P<P1P;P7P0g00]6P8P:P>P6P2P3N<01p=]A2123p=<P<P1P3P7P2P6P>P:P8f6R0f7R;f8R?N<01p=ZP<P<P<P1P1P1g00\3P7P7P7P4g00\SP8P:P>P6P2P3MB~p=_1;=3p==%13,;=p=G1023#1p=:P1P6P2P3H0Sp=IP1P2g00]XP3H00p=UP2g00^?R4g00^^R@P@g00_>RAP3g00_^K0Tp=DP1P2g00c^P3H00p=YP>P4P@P@PAP6P2P3L0Yp=OP<P<P<P1P1P1g00ibP7P7P7P0g016WP8P:P>P6P2P3MB~p>09P6P4P@P@PAP2P3K0Xp=tg02@2g00aaR7#JRB#JS00#JRC$02#jRD#pREp,3bsbRFp,5rdrawRG$0[RH$0RRI93D352E%JCRJ#J#JRK$02RL#jRMp,2spRNp,2avROp,2evRP40GRQ10D3RR98LN32%^CRS,HR#>'6'6S01XTERT'}P5PEPTA8LN392MQg00Z9RT#SR5#SRU#SRV#SS02#N#N#N#N#N#NRW,5310DFRX'7%13RY/?S#>1523/PWS03%kERZp,4segsR[p,3stkR\%v6R]9[LQP2A9D6IR^94D2,FEEC[^0<^S<R_'6'6'6Xc<R`,}<RaP3Q01P9A3D2I92EF10D2Rb98LN92MQ1HbS#>'6PaP3A3D>I92EF10D:Rb98LN92MQ1HbS#>'6P910D8R998LN92MQ1H9S#>PaP310D;98LN92MQ10D?/HS#>&0@H10DIRH/7WS04P<P`f:R`,0DRaA8LNa92MQ15aWR9/7XRX1HaS#>Rb/6_Rc'6P6PXPcPEA3D`IRcf;Rd,0DRe/5WRf/7RX8E15aH17f3X0<PW15e3,7fX0<1K<9PHP3DM10DcAhD`IDMp,2phRcPNPOPPp,3uidR9p,2hwRfPGK0:ReP0ETPXePbP_P2Q03PMf=R_,0DRb98LNS05PZP[P\A8L3>P6A9D>IRX94D6,FERaECXLMPM15b698LNPZP[P\P3P6PaECXLMPEPIf>RM=3D392EFX8Ef9RaA4D6I=3D^R^AoD6IETA3D_^92EFPEA4D>IR^=3DX93DMA2EF3X8EP3A3DM^=3DXRRPDPMP^PXH06E{A2EFRPEA9D:IRRf@RXA4D8I53DR^=3D392EFX8EP3A4D>RA9D>R53DRgAoD>RETf?RRA4D:I53D=3Dg92EFP[PcPNPOPPP9PfPGP^A9D8IR^94D:RFA9D:^P:P3N=0310DF/7:20ZLNRF10DeRe#1R^'E%^BRg%^KRK+0WRh'ARiPZP[PcPNPOPPP9PfPGK0V-0UNRGfBR9A4D;I53D,0DS0698LNP0A9D;I94D0S07,FEEC[RP[fARO,0DRcA4D0IRj,0DRk'510D9R9/5;Rl,73X0<P01593/7lX0<15c0Rc,K<PkPDPIP01P0H%10Rk%1HR9';P0Pk%@kRmPHP9%@9S08E]A9D0I94D8Rn,0DRo/78RpPZP[PGfCRqA4D?I53D,0DRr98LNP;A9D?IRs94D;Rt,FEEC\iRu[%1oRv%18Rw'<RxPu[RuPpPPPxp-0RxP2\2XXxW:S09P3X:1P^O1,EF/AhS0:PZP[PGA3DOj,0DRF98LNP81FEnECO2Rn%|<Rp%|1Ry%12/<Y172320Q2340PXX<X:<RYPoPv%@vP8Pw%@wM9Z1KxnA2xPne9zPnEyP3CLPu15;0Ru/PW%1;Rn/EkRP%^JRJ';RwPuPPP;Pn%@nS0;P0PkPmE_PWPJ%@JS0<E]P8CLPwQ041<9JRwPpPyPYPHP9Q08PWPJQ0<M9ZS0=PaCLPw%Ba%1aRm#=%BeS0>%=^S0?fFS0@,0DR^#B%G^%Bd%Gdf<ReA9D_I54D,0DRk#B%Gk%BHS0A%=9S0BfJ,:D?xS>%=SS0CfK,0D/HS#=[20NgKS0D1A=gRk%=K1A=hRP[[S0E%=gRug00g5RvB0MgK2UW@S0F%=h\vS0G^@uS0HfMRu,:D/uS%>SRv$0LS0IfNRh,:DRK1QKS,nS1?KS'E'<[1mKS1A=SS0JfO,:DRK/?SRg#=1AgS'6[1qKS1AS=S0KfP,:DRK/?SRg,AS1;g='6[1rKSfQ,:DRg/QS#>\v1sgSfR,:DRo/?S/<o\v1QoSP1fSS0L,:DRo/?SP1P;P`O1Q0GP`PdO1%=2S0MP\PfO1S0N%kDS0OPeP3PMO2X9kPP^9kS0Pg00bFRP1X1VS0Q&0I7-0H1S0R1X1U5i11X151X1T5V15V1RT5V1g00c2R5'a&0FPRU3b%pPS0S1g1>RV&0D1Rf7I>?I6f?I2f&0C1S0T&0B1R\1f1=Rz1W1CRC'U,D\&0A@R{P\1W1BRB1f1JR|'Y,D\P{P\1W17R}=d1C/U|,D\P{1U}B,D\S0UCOCOCO20?\AS0VP3P6g00dERCg00deR~'K20>36=2C~dB0=1=2H0<S0WbCbIbJX51X61X71%=61<6J1E6:/;J1;>:S0X[[[^51^61^71P3%1uP9%1hPOfERhQ0@O6bBbFbWb4bEbVbUb>b=b<b;b3bEbFb4bRbQbPbObNbMb?bAb3CcCeDMPFAhDOjDM17FcP<Q0610DtRt/7;PZP[PGA[LN]PaA9D`I94Da,FES06EC\i[X0<P2PlP3E{Q07,0D/70PZP[PGfDRl,0D/5a98LNP?A9DaI94D?RF,FEECS07\i[P3P;173?X0<1K<;PtPDPsP;20;H?Rt1P?3X0<1P;t%1?Rc,R9,\=Rj,;nP;PnQ0;PtPj1R23,\=Xb1X01PHP9Q08P?Pc%@cRHK09E]10DqRj/5?Rt,7r%1rRn%1jRu/EcR~'<RCPpPyPYPrPn%@nPtP~PjPu%@uP?PcPHE_M9ZP2CLPC10DFRF/7?RCPZP[PG15^d98LNP`A9DdI94D`,FEEC\iRd[%1FR^/<cRuPd[RdPCPZP[PG10Dh/5`98LNPaQ06EC\iRiPuQ09Q0:Q07O2RuPpPyPYPFP^%@^P?PcPHM9Z1KxuA2xiue9ziuEyP2CLPd15`aRd/PW%1`Ru/EmRi/;JRHPdPiP`Pu%@uPaPm%@mE_PWPJQ0<E]P?CLPHQ04PwQ0=PeCLPw%Be%GeQ0>Q0?fIRw,0DRH#B%GH%BM%GMA9DXI94DR,0DRM#B%GMfLA4DOI53D,0DRO#B%GOQ0AQ0B%1q,R9Rq-0E=1A=q1\=qRO/<q'61;q=%>O'6'l%1l,R9,\=P1AxKS0Q0C1?gS#=[Q0DQ0EQ0FQ0H1uoSQ0IfTRo,:DRg1QgS,nS1?gS'E'<[1mgSQ0JfU,:DRg/?SRK#=1AKS'6[1qgSQ0KfV,:DRg/?SRK,AS1;K='6[1rgSfW,:DRg/QS#>\v1sgSfX,:DRg/?S/<g\v1QgSP1fY,0D/HSP1P;PeO1Q0GP`P_O1Q0MQ0NQ0OPeP3PXO2X9kQ0PQ02,X1Q0RQ0Q5i1=V1TRT5V1/a51aT5=bPU5bPQ0S1g1:9If:?I6fAIV:f?I:f7I2Q0TP\P\P4P@P@PAP\P4P@P@PAP0J08%w7#J#J,W1R7Q00#w,W1R060J1RA,YB,D\5t\1UAz,D\1YBz,D\5t\K07P{P\1Y7|,D\P{P\Ad10}/U|,D\P{Q0UCOCOCOQ0VQ0WbCbIbJX51X61X71XK1XDx1R>6R>,<2,6:1;>=%>2'6'l1<:J1E:6/;JQ0X[[[^51^61^71^K1^DxP3%1oRo,R9,A=P9PoPRQ0L#1PXfHPwO8bBbGbWbHb4bVbUb>b=b<b;b3b4bGbHbdbYb`bRbQbPbObNbMb?bAb3b]Cc10DsB0KD?IDMCeDMg01a0O2b2b\b2b1b1b1Q05=[L]B05Nb6ETPQP8ETW[X0<XS<C`C`C`H0ObZW^W_P2P3O2n2001000000121000000W2W1P2P3O2n2001000000121000000W2XTEP2P3O2n2001000000121100000bao"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma lay_bsb_len : (Z.of_nat (length bsb) <= 2240000)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) ["Layout"] "p;9p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000dR2p4p710p8P0P2p4p7210p8P0p1001Ap4p710R0p8p1001]p4p710R2p1002:p4p710R3p8P2p1002Vp4p710R4p8p10034p6051000R5P1p8P5P3p8P5p10043p4p710R6p8P5P0p8p1004Up6051000R5P1p8P5P3p8P5P6p8P5P0p8p1005^p6051000R5P1p8P5P6p8P5P0p8p100kFp6051000R0P2p8P0p100NYp4p710R2p8P0p100gop4p710R5p8P0p100hOp4p710R6p8P0p1006fp4p710R0p8p100mIp6051000R1P2p8P1P4p8P1P5p8P1P6p8P1P0p8p100oRp6051000R1p100nOp4p710R6p8P1P2p8P1P4p8p1011:p6051000R5P6p8P5P2p8P5P4p8p1017\p6051000R3P6p8P3P2p8P3P1p8P3P5p8P0P4p8g02A9l90Tp,2php,2spp,2avp,2evp,3uidp,2hwp,5rdrawp,3Hvap,3HveM90o"). Qed.

  Lemma auxv_off_bound : (auxv_off av ev + 160 + 16 <= length bsb)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) ["Layout"] "p'0h01nh11xi001xh24__p1h34__p2h44__x1h54__x2h64__x3h74__x4h84__x5h94__x6h:4__x7h;4__x8h<4__x9h=1mh>1ph?1Hh@2H0hA2H1hB2H2hC2H3hD2H4hE2H5hF2H6hG2H7hH2H8hI2H9hJ7__arithhK4__ffhL6__sat4hM6__sat5hN8__varmaphO5__withP4cstrhQ5cstr0hR5cstr1hS5cstr2hT1qhU2q0hV1rhW2r0hX3stkhY2z3i019argv_ptrsi021bi03<env_str_basei049envp_ptrsp%0p&0p;1p;2p;3p;4p;6p;7p;Bp;<p;8p-1R0p10000p4p710R1p8P0g000GR2p4p710p8P0P2p4p7210p8P0g000dR3p4p710p8P0P3p4p7210p8P0p1001Ap4p710R0p8g01WHR4p4p710R5p1002:p4p710R6p8P5g002VR7p4p710R8p8p10034p6051000R9P1p8P9P6p8P9p10043p4p710R:p8P9P0p8p1004Up6051000R9P1p8P9P6p8P9P:p8P9P0p8p1005^p6051000R9P1p8P9P:p8P9P0p8p100kFp6051000R0P5p8P0p100NYp4p710R5p8P0g00goR9p4p710R:p8P0g00hOR1p4p710R6p8P0p1006fp4p710R0p8p100mIp6051000R;P5p8P;P8p8P;P:p8P;P6p8P;P0p8p100oRp6051000R;g00nOR6p4p710R:p8P;P5p8P;P8p8p1011:p6051000R<P:p8P<P5p8P<P8p8p1017\p6051000R=P:p8P=P5p8P=P;p8P=P<p8P0P8p8g007ej1<Tg008Jk106Tg008hk104Tg007Ej1jTg018fR8k20sTg00@Tj10TP9j22Tg00:Oj21Tg01J9j2GTg01JPk30QTg01>Bk40JTg00;@j1iTg00O8j3rTg01KRj2qTP2k30=Tg01LSk10<Tg01;Zk40:Tg01l2k20eTg01MTk20]Tg01:bR2k100TP3j4ZTg01D1j2zTg01NLj1yTP1j35Tg00QJj1dTg00<UR1j1=Tg01PPk10NTg01QNk10MTg00:fR3j2ETg01OPR9j26TP6j3nTg012?R6j29Tg01P0R0j1cTg00>OR<j23Tg01WgR=j2;Tg00U>j1bTg012\k20;Tg00>lR;j2PTg00?oj1]Tg0139k20^Tg013[j2ITg0147j2HTg014Rk205Tg024:k203Tg024kk201Tg01DWk10\Tg025Lj2[Tg023Sj2~Tg025ij2}Tg026Pj2|Tg0276j2{Tg009Kk10[Tg00LTk10ZTg00M2k20YTg00MSj3kTg00A3j2xTg02B7k20XTg02B`k30WTg00BEj2wTg020ck20VTg00C1k10UTg00CQj3vTg00DOk10STg00D1j2aTg00EKk10PTg00Eik10OTg00FTj2UTg02CIk60LTg00GZk10KTg014lk30ITg00G7j2uTg015Ok70HTg00IJk20GTg00>5k202Tg00Ilk20FTg00<;j3mTg00JXk30RTg00K7k40ETg00Kik40TTg029ck10DTg01m1k40rTP7j6TTg01Zmk10BTg01Xgk20ATg01Ylk10@Tg02:gk30qTg02;jk10pTg01SFk20?Tg00WflB`Tg02Cmk40nTg00YTm<0>Tg00WAm<0mTg00A\j3oTg00Dmk40lTg00H_j4pTg00XLk70iTg01XDk30hTg00H<k30gTg00Y0k80jTg010Vk60kTg0163k70fTP4k30CTf0R4#0#0p>07%04#0#0#0p>0c%04#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p>0`%04#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=\f2R7f1R5/64'9p=_1654#cp=ef4R:f3R>?n75;54p=g1975/64p=s%c49n75p=NA5754,2>p=F1154,E7p=B%=7/65,9>/64p=S1154,17p=A1154,17,1>,1:p=>f6R?f5R@%=>/67,9:/65#c/14'1'Ep=Cg00ZXRA0024p=@g00[TRBPBPBPAPAPAg00\3P1P1P1P<g00\SP@P:P>P7P5P4MB`p=7PBPBPBPAPAPAg01[kP1P1P1P=g01\KP@P:P>P7P5P4MB`p=^PAPAg02DPP4H0np>09PBPAPAPAP1P1P@P:P>P7P5P4N<0>p>0dPAPAPAPAPAPAP9P4P5P7P9P>P:P@P?f7R9f8R=f9R<MB`p>08PAPAPAPAPAPAP6P4P5P7P6P>P:P@P?P9P=P<MB`p>0bPAPBPAPAP0P:P1P>g02E4P7P5P4N<0>p>0aPBPAP3P1P;g00]6P@P:P>P7P5P4N<0mp>0_g00[6R;/P4p=8AmA54p=MAmA4;p=V1xA4p=KAoA54p=lAoA549oA7p=YPAP7P5P4H0lp=QPAP5g00c^P4Cpp=XP5g00^?R1g00^^R3P3g00_>R0P4g00_^K0ip=:1uA4p=JB0hA54p=RB0gA54p=4P>P1P3P3P0P7P5P4L0jp=?PAP5g01jGP4Cpp=fP5P1P3P3P0P4J0kp=tP7P1P3P3P0P5P4K0fp=hPAP5g00]XP4Cpp=W1354,37p=OPBP:P>P7P5P4ETp=DPB119?P@P:P>B0C754ETp=LPBP?P@P:P>B0C754ETp>0og00aaR6#<RC#<RD#<RE#<RF#<#<$06RG$04RH#jRI00sHRJPIPHp,2spRKg00Z9S00#0RL#0S01#0S02#0S03#0S04$07S05#0RM&06ERN$04RO#jRPp,2avRQ'2RR/1LRS/GM'1p,2evRT,2PRU/1LRV/GM'1p,2phS06B0QKQTS07p,3uidS08p,2hwS09H0JS0:,2ORK'1#i5rGRW/qQS0;:0=IHRX&0<QRY#i9rGWRZH0:20eQT%0MS0<#0S0=$07$0cR[$0`#\#\#\#\R\'1/1[R]P8PIPHPPP4P8PIPHPP1q4T20]PQS0>$00R^PHPOP2P>CZ1zG;S0?$00R_PHPOP2P5CZQ0:%yQS0@%yTS0A55OS0B55OS0C95O_R`55O55ORa55O55ORbPOPO1zN;RN%dERE12Ob#=;_E/eEp,5rdraw$0NS0D$0MRbDg55On2001100000121104102S0En2001100000121101103,2O'EX>JPJPIPH1qZTS0F:0=IHRc&0<TRd#i9rGZH0:P8PIPHPPP4PHPOP2PXCZRG=5Oa95O^RaPOPOPN12Oa#==_EE/eEPbDg55OS0Gn2001100000121104102,2O,E]X>JPHPOP2PcCZR2=5O`RJ95O_Ra95OGS0H95O^S0I,2ORePOPOPN%=e=_EE/eEPbDgS0J,2O1E]4X0B12O^RfQ0H,2OS0KPOPO%=4S0L/6E=sEE9NONPbCF9B]4X0B12OGRg12OaS0M11f4RhPOPOPEPhPEPECS9NONPbCF5B]X0B12O_Rh12OJS0NAAfg4RiPOPOPEPiPEPECS9NONPbCF5B]X0B12O2Ri12O`S0O11h4Rj9AfgRkPOPOPEPkPEPECS9NONPbCF5B]X0BPhQ0C,2OS0PPfPgPhPiP4D>RkPOPOPEPkPEPECS9NONPbCF5B]X0BPKQ0B,2OS0QPfPgPhPiPjD>RjPOPOPEPjPEPECS9NONPbCF5B]X0BQ0@,2OS0RQ0A,2ORj'1RkPfPgPhPiAAhK4D>RlPOPOPEPlPEPECS9NONPbCF5B]X0B11KkRl,1hRm9AhiRn9AfgRo#==_EE/eERp9nONS0S,2ORq12ObS0TAB]o4X0BP[11q49B]oX0BPp114[9B]oX0B12HXS0U,GMRoP]AAf4nRnPEPnPEPEP[FCX0B12HcS0V,GMRnP]PfPoPhP4PmD>RoPEPoPEPEP[FCX0BPRP]Pf1GM4RoPhPnPmD>RnPEPnPEPEP[FCX0BPUP]Pf1GMRRnPhPoPmD>RoPEPoPEPEP[FCX0BPMP]P4PnPh1GMURoPmD>RmPEPmPEPEP[FCX0BPMP]PMPnP4Po114lD>RlPEPlPEPEP[FCX0BPBg01VJRlP]PMPnPMPoAAM4kD>RkPEPkPEPEP[FCX0BPYP]PMPnPMPo114j9AMlD>RkPEPkPEPEP[FCX0BPdP]PMPnPMPo11Y49AMlD>RkPEPkPEPEP[FCX0B1GMSS0W,1MS0X1GMVS0Y'1S0Z/1\S0[/1[S0\11YdRk,1\S0],1MS0^,1oS0_,1MS0`,1nS0a,1MRm%=mS0b/6ES0c,9ES0d/6ES0e#cS0f/1[S0g'1S0h'E%=RRr%d6Rs'3S0i,;ES0j,3ES0k%=URt/3sS0l,;ES0m'3S0n%bCRu#<S0o#<#<#<#<#dRv'3S0p%dFRF'3Rw1;ErS0q1;EtS0r%=YRx%=dRy'3S0s,3vS0t,3ES0u'3S0v,3ES0w'3S0x,3ERz16zER{,9ER|/6ER}-0;;R~/3FS0y'3S0z'PQ0\PwQ0[Q0pQ0ZQ0nQ0XQ0kPMPE%@ERwQ0WQ0jPMPEPwPSQ0iPRPr%@rS0iPLPs%@sRSE7E^E7Q0YQ0mPMPEPwPVQ0lPUPt%@tRVPLPsPSE7E^E7P\Pv%@vRSE7P[PF%@FRLE7Q0hQ0zPmPzPMPEPwQ0aQ0xPnQ0qPMPEPwPRPrQ0iE^Q0`Q0wPMPEPwQ0_Q0vPoQ0rPMPEPwPUPtPVE^Q0^Q0uPMPEPwQ0]Q0tP\PvPSPkQ0sPYPx%@xPdPy%@yE7E7E7E7E7E7E7RSQ0gQ0yQ0fP~P4X1AR\20;;4X1AQ0eP}P\P\P\1654$09#@X=AX0ARVQ0dP|P\P\P\1954$09#@X=AX0APEPEPwQ0cP{P\P\P\PVQ0bPzP\P\Q0L#@X1BPmPzPSJ0dPEPEPwN:08N:0bPEPEPwN:08I0aP[PFPLE7E7J0_%]R%8r%]Y%8x%]U%8t%]d%8y20^;}1I;}1M~}'H1P};%V~'H+05P~PA203zE%8z%8ER~%8{Rd[[203|E%8|%8}\~[201zE%VER~$0\R}1[zER|,;E/3{,Mz[1~zE1I;ERU1I{E,Hd[1}zE1IE;Rd1IE{1P{;'H[1|zE%V|\~1{zE1M{z\~P|PAP{PA19E4001E19E5R{1[{E,;E16{E'3'M\}1~{E19E7R{/6ER}#81I}E'H\U1}{E19E>R{/6ER},IE1P};'H\d1|{E19E:R{/[E#V\~1{{E19E@R{/6E/M{\~1[{EPAAsE?EPAp,3stkQ09O1&0[Op-0R{g00bFRdQ0<#K&0Z6-0YAR}Q05#KR|5kAQ04#KRz9kA}RYQ00,xARR'l3Y20XAE>0WARQ0=#K9kA}%KMQ02#K,lz7Y|3Yg00c2R|'w+0VQ03#KQ01#K/lR5YY/w|&0Ud5vd3v%jd&0SARd1aA<7Q:1aA9?Q<d7Q71aA??Q@d1aA=?Q<d7Q>7Q5&0PA&0OARdPdPdP1P3P3P01UAER|1UA;RY'X,:dJ0LRR&0K3RzQ0o#JR}:0IA|%b6RL#<#<#J,R|%bD#JRw'4'X,:dC?PzPdPd1fY|,:dPzf;RS,td1f}|,:d5hdC?PzPdPdPRPz1uA6R6,R|%JCRC,R|1UAvRR%JLRL%JDRD'4'4,4|'4,4|'4,4|Rm%bu#J,R|/4}'X,:dC?PzPdPdP1P3P3P01fYw,:d%JuRu/Xw,:d5hdf<Rw,td1XuY,:d5hdK0HPzPd1WYD,:dPzPd1WYC,:dPzPd1WYL,:dPzPd1WY6,:dPz1UAsRz,46,R|,4|14Cz,R|'4/4R1UAFRR'414uR,4m'W,:dC?C?C?C?C?C?C?C?20Gd0P4P7g00dERdg00deR0+0220F47=md0dB0RA;5H0EbKbNbOX4AX5AX6AX7AX8AX9AX:AX;AX<AX2{W3g00fX\~R~19E91;E<R5/3?'M[1I=E,HS\U1;E>1;E:13@?9OEv5OE5OEf:R@,;E/3<'M\~1I;=1M9='Hf=%V9'H+05%89R9%8?%8=13=s,;E,3E13<s,;E'3/3v/3F1;E=13@S9OEv9OE55OE?OwF'P\9[[[[[[[^4A^5A^6A^7A^8A^9A^:A^;A^<A^2{^3{P41P7;%8<P>P@P<P7fBPyPxPtPrP=f>f?fCfDfEfFfGOCbJbXbWbUbIbHbGbFbEbVbTbDbBbAb@b?bLbMbYbCbSbRbQbPH0TP]PMPnPMPoAAMlkD>RkPEPkPEPEP[FCePj&0DTDDQ0R&0DQDDPKQ06Q07Q08Q09H0rETPhQ0?$0BDDPfQ0>$0BDDQ0V20ATZDDQ0U20AQWDDPi&0@cDDPg&0@XDDPqB0qONpDDQ0TQ0D$0pDDPOPOQ0SPbCFPOQ0SPbGLQ0QPOQ0@Q0AK0oQ0PPOQ0:Q0BGLQ0OPOP_Q0CGLQ0NPOP2P`GLQ0MPOP_PJGLQ0KPOPGPaGLPePOP^Q0HGLPOPOQ0IQ0JCFR^POQ0IQ0JGL1E]^eQ0F20?TZETP8PIPHPPQ0FQ0Gn2001100000121104102,2O,E]eQ0;20?QWETP8PIPHPPQ0;Q0En2001100000121101103,2O,E]ep,3bsb,2O,E]eo"). Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma cat_envp_ptr_eq : forall k, (k < length ev)%nat ->
    cat_envp_ptr sp av ev k
    = sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat av
                        + total_arg_bytes_nat (firstn k ev)).
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) ["Layout"] "h02Hkh11bh21kh31np;1p;2p;3p;6p;4p-1R0p10000p4p710R1p8P0g000GR2p4p710p8P0P2p4p7210p8P0p1000dR3p4p710p8P0P3p4p7210p8P0p1001Ap4p710R0p8p1001]p4p710R3p1002:p4p710R4p8P3g002VR5p4p710R6p8p10034p6051000R7P1p8P7P4p8P7p10043p4p710R8p8P7P0p8p1004Up6051000R7P1p8P7P4p8P7P8p8P7P0p8p1005^p6051000R7P1p8P7P8p8P7P0p8p100kFp6051000R0P3p8P0g00NYR3p4p710R7p8P0g00goR8p4p710R1p8P0p100hOp4p710R4p8P0p1006fp4p710R0p8p100mIp6051000R9P7p8P9P6p8P9P1p8P9P4p8P9P0p8p100oRp6051000R9p100nOp4p710R4p8P9P7p8P9P6p8p1011:p6051000R1P4p8P1P7p8P1P6p8p1017\p6051000R:P4p8P:P7p8P:P9p8P:P1p8P0P6p8g007ej12Tg008Jj1<Tg008hj1;Tg007Ej18TP8j2HTg01cZj2FTg01UIj3CTP3j39Tg01LSj17Tg00;@j11Tg00O8j30Tg02Eaj2=Tg00:Oj23Tg00<;j36Tg00\3j25Tg00>5j2GTg02Fej3ETP5j64Tg00T;j3:Tg01KRj2BTP2j3@Tg01D1j2ATg01iIj4?Tg02GKj4>Tg01e1j4DTg00[TR2f0R5g00aa#2#2#2R3#<#;#8R8p,2evR6'H'F%23#2#2#<R3#;R0p,2spR1p,2avR:;C6R9f1R7=986#7R4#1R;503R<1=:6R=%7:R>'3R?f2=986#7'3#19031R89605X10R@P0%1=9031RA13>4RB#1503RCP@P013=B#19031P@P215=>/54%159031=608X3213?4#19031R?,G015>4,5=AE=>4E4PCA:1=BE4%1>903A=03;A:A>4E4A60<?eP0P7%801B967@0g00[6,A3C?P6P9P7P5C>E4P1P:P6P7CD=60?eW0W2o"). Qed.

  Lemma total_firstn_ev_bound : forall k,
    (Z.of_nat (total_arg_bytes_nat (firstn k ev)) <= 131072)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) ["Layout"] "h01Hh14Htoth24__x1h34__x2h41eh52H0h62_Hh73_H0h87__arithh94__ffh:8__varmaph;5__with<4cstrh=5cstr0h>1kh?3stkh@1vhA1zp;1p;2p;3p;6p;4p;<p;7p;8p-1R0g01B=R1p4p710R2p8P0p1000GR3p4p710p8P0P3p4p7210p8P0p1000dR3p4p710p8P0P3p4p7210p8P0p1001Ap4p710R0p8p1001]p4p710R3g002:R4p4p710R5p8P3p1002Vp4p710R6p8p10034p6051000R7P2p8P7P5p8P7p10043p4p710R8p8P7P0p8p1004Up6051000R7P2p8P7P5p8P7P8p8P7P0p8p1005^p6051000R7P2p8P7P8p8P7P0p8p100kFp6051000R0P3p8P0g00NYR3p4p710R7p8P0g00goR8p4p710R2p8P0p100hOp4p710R5p8P0p1006fp4p710R0p8p100mIp6051000R9P7p8P9P6p8P9P2p8P9P5p8P9P0p8p100oRp6051000R9p100nOp4p710R5p8P9P7p8P9P6p8p1011:p6051000R2P5p8P2P7p8P2P6p8p1017\p6051000R:P5p8P:P7p8P:P9p8P:P2p8P0P6p8g007ej16Tg008Jj1UTg008hj1KTg007Ej1GTP8j2ETg00<UR8j11Tg00QJj1;Tg00>lR6j20Tg01BTj1OTg01CPj3>Tg01D1j2HTP1j3eTg01DWj1cTg0147R1j28TP3j35Tg01LSj14Tg02HPj1XTP4j6WTg02IOj2VTg00:fR4j2DTg00>5j29Tg00?Hj4STg00?oj1ATg009Kj1PTg00@Tj1?Tg00A3j27Tg00A\j3@Tg00BEj2NTg00C1j1JTg00CQj3LTg00DOj1MTg00D1j2ITg00Dmj4BTg00EKj1QTg00Eij1RTg00G7j2CTg00U>j1<Tg00GZj1dTg00FTj2bTg00IJj2aTg00Ilj2^Tg00<;j3]Tg00JXj3\Tg00K7j4[Tg00WAl<ZTg00H_j4_Tg00XLj7YTg00Y0j8`Tf0R3#6#6p=3%<3#<p=2g00[TR0g00ZXR2P4P8P6g00]6f5f4R6f3R8f2R4f1R:P3M<Zp=TP2P:g00]XP3C_p==P:g00^?R9g00^^R7P7g00_>R5P3g00_^FYp=:P8P9P7P7P5P4P:P3G`p=Fp,3Hveg00aaR9#6R8#3R;#UR<#KR=#GR>p,2evR?'E#1%6;#3#3R;#;'0R@%O?RA%6;#3#3#3#3#;R;'0RB1E=3#1%29#2#2#2#2#2#2#2#;'0X4>=>>?g00[6RC,H<=e=3#cX4>=>>?'8R<'8RD'8P1P@PDA5>4?#4#1/0;P3P1PBP<f6R1=5>?#4#1/0;P3P2PA103;XA2P:%4?RA#1RE%X?EW10E;f:RF/V?A5>F?#4/DAf;=5>?#4RF/DA%1FRG/0ERHPFPG192GPAPE192EETP3CSPHf<=5>?#4RH#A%1H,0C%AA10CEp,3stkp,2hwO1%P=g00bFR=g00Z9RA#?RH#?,72172H172A5@25@2g00c2'N%J=3L%G=P2%M2R=P:P21I24P4P=CBCB%Q2%R2R=1C29R9%<8,C2R8'=,:=%d7R7P=1b2;RA,=8,:=P71=9A,:=CFCF1a=5P3P4g00dER=g00deR5'91^34=]=5dA\2C:C[b9b:b;X22X32103:104;R;P;[[^22^32P3PEf@=5>?#4#1P6P1O4b8b?b=b<b5b0b1X7<X1BP:P3O2n2001000000121000000X0DX6@P:P3O2n2001000000121000000b@X>0o"). Qed.

  Lemma struct_av_bound :
    (Z.of_nat (cat_struct_size av ev + total_arg_bytes_nat av) <= 2107576)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) ["Layout"] "h01ah11xh21Hh33Htah42_Hh54__x1h64__x2h74__x3h81eh91vh:2Hlh;3Hl0h<3Hleh=7__arithh>4__ffh?8__varmaph@5__withA4cstrhB5cstr0hC5cstr1hD3stkhE1yhF1zp;1p;2p;3p;6p;<p;4p;Bp;7p;8p-1R0g01B=R1p4p710R2p8P0p1000GR3p4p710p8P0P3p4p7210p8P0p1000dR3p4p710p8P0P3p4p7210p8P0p1001Ap4p710R0p8p1001]p4p710R3g002:R4p4p710R5p8P3p1002Vp4p710R6p8p10034p6051000R7P2p8P7P5p8P7p10043p4p710R8p8P7P0p8p1004Up6051000R7P2p8P7P5p8P7P8p8P7P0p8p1005^p6051000R7P2p8P7P8p8P7P0p8p100kFp6051000R0P3p8P0p100NYp4p710R3p8P0g00goR7p4p710R8p8P0p100hOp4p710R2p8P0p1006fp4p710R0p8p100mIp6051000R5P3p8P5P6p8P5P8p8P5P2p8P5P0p8p100oRp6051000R5p100nOp4p710R2p8P5P3p8P5P6p8p1011:p6051000R8P2p8P8P3p8P8P6p8p1017\p6051000R9P2p8P9P3p8P9P5p8P9P8p8P0P6p8g00QJj16Tg007ej14Tg008Jj1WTg008hj1yTg007Ej1OTP7j2GTg00<UR7j1:Tg00>lR6j21Tg0147R0j27Tg01BTj1LTg00U>j15Tg01CPj3?Tg01D1j2vTP1j3rTg01DWj1iTg01E0j1fTg00<;j3HTg01F4j2cTg01Fhj2bTg02Eaj2aTg01LSj1`Tg00:Oj2<Tg02HPj1\TP4j6[Tg00@Tj10Tg01J9j2MTg00>OR4j23Tg01WgR1j2DTg02J]j1VTg00WAl<TTg00?oj1JTg009Kj1xTg02B7j2wTg00A3j2ATg02B`j3STg00A\j3ITg00BEj2qTg00C1j1pTg00CQj3oTg00D1j2PTg00Dmj4hTg00EKj1gTg00Eij1eTg00G7j2FTg00GZj1dTg01XDj3NTg00IJj2jTg00>5j2QTg00Ilj2kTg00JXj3lTg00K7j4mTg00Kij4nTg00WflBRTg00YTl<_Tg00FTj2^Tg00H_j4]Tg00XLj7sTg00H<j3tTg00Y0j8uTf0R8#4#4p=2%58#5p=8%08#0#0#0p=Z%08#0#0#0#0#0#0#0p=Y%08#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=X%08#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=@g00ZXR9/Q8p=9g00[TR5P5P5P9P9P9g00\3P7P7P7P4g00\Sf5R4f4R3f3R2f2R:f1R;P8MBRp==P5P5P5P9P9P9g01[kP7P7P7P1g01\KP4P3P2P:P;P8MBRp=KP5P9P9P9P7P7P4P3P2P:P;P8M<_p=U1^98p=;P9P;g00]XP8C]p=CP;g00^?R7g00^^R1P1g00_>R<P8g00_^Fsp=BAt9;8p=>P2P7P1P1P<P:P;P8Gup=Ep,3Hvag00aaR7#6R=%47R>#2R?#WR@#yRA#ORBp,2avRC'GRD#:RE'1RF%2?#2RG#4RH#2RI#6RJ,1ERK'7RL%LCRM%4I#2#2#2RI#2#2#6RN'1RO1GA8#:%57RP#5#8#8#8#8#8#8#8#6'1RQX0B=?BCg00[6RR,v@=rA8#iR@X0B=?BCg01GhRSg00dERT%f8g01HXRU3Hg01I8,c8=HTU'7X0S1bBC3?'7'7RS'7RU'7P0PLPUp,2evRV,aC%`CRW'<#:%5G#4#5#4#2#5#4#5#8#4#2#6RG'1RXP8P0PFPKPX\UP8P0POPSPXP8p,3Hve1GBVRY#:RZ%6HRH'1R[%LV%6I'1PQX8B=?BVP@X8B=?BV'7'7RV'7P0P[PVPXP8P9PM118NXF9f6%:WRM%\CE[11MNg00Z9RC#0R0#0RB#0R@#0#ZRQ1<D0RI/MQR\'<R]1<Y0R^/MQR_'<R`%YQ#X#@#@#@#@Ra'<Rb/<WRc#:Rd/1G%6?R?13E=Re/D?Rf'3Rg13Z=Rh/D?Ri'3Rj%5>#4#2#2#6Rk'3Rl/3MRm/1GP9P9P6P8X19RnP611;8#VXE9X19PdPmPnPn%:8#9X15PcPmPbPlP`PjP]PgPQP?%9?RgP\PfPIPePDPE%9EP0P=%9=ReE=PQP?PgEKE=P_PiP^PhPYPZ%9ZP0P=PeE=PQP?PgEKE=PaPk%9kE=PWPM%9ME=EUPGPG%9GM<T%JD11RE%JW11RM%JY11RZp,3stkp,2hwO1%xAg00bFRA1w9?RY1A9@5S91A9B1A909S9Y1A9C5I95I95I9g00c2'q%pA3o%OAP91P9:P;1P92Ch%g9%e9RA1F9>R>%;H'C,BA%d1R1PA1F9PRP%;N'C,BAP1PA1F97R7%;J'C,BAP1%;?R1%;=RC,>7=N91'>1>>C=N91'>%;k'>/>P%;G'C,BACECECE1jA<P8P:g00deRA,QT1k8:=HTAdAl9R;Cmb>b?b@X59X69X7911;H112N11:J132=/D?,3?133=/D?'3/3k/34/1G[[[^59^69^79P8PMPZPEf7P4f@O6b=bDbCbBbACnPXeb3X4VX<[P;P8O2n2001000000121000000b9X4SX3OP;P8O2n2001000000121000000X2UX:KX;FP;P8O2n2001000000121000000X2LP;P8O2n2001000000121000000b9o"). Qed.

  Lemma u_cat_envp_ptr : forall k, (k < length ev)%nat ->
    bv_unsigned (cat_envp_ptr sp av ev k)
    = (bv_unsigned sp + Z.of_nat (cat_struct_size av ev + total_arg_bytes_nat av
                                 + total_arg_bytes_nat (firstn k ev)))%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) ["Layout"] "h04__x1h14__x2h24__x3h34__x4h41xh52H1h62Hah73Hk0h87__arithh94__ffh:6__sat4h;6__sat5h<8__varmaph=5__with>1ah?4cstrh@5cstr0hA5cstr1hB5cstr2hC5cstr3hD3stkhE1yhF1HhG2H0hH2HkhI1bhJ1khK1mhL1np;1p;2p;3p;4p;<p;6p;Bp;7p;8p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000dR2p4p710p8P0P2p4p7210p8P0p1001Ap4p710R0p8p1001]p4p710R2p1002:p4p710R3p8P2g002VR4p4p710R5p8p10034p6051000R6P1p8P6P3p8P6p10043p4p710R7p8P6P0p8p1004Up6051000R6P1p8P6P3p8P6P7p8P6P0p8p1005^p6051000R6P1p8P6P7p8P6P0p8p100kFp6051000R0P2p8P0g00NYR2p4p710R6p8P0g00goR7p4p710R1p8P0p100hOp4p710R3p8P0p1006fp4p710R0p8p100mIp6051000R8P6p8P8P5p8P8P1p8P8P3p8P8P0p8p100oRp6051000R8p100nOp4p710R3p8P8P6p8P8P5p8p1011:p6051000R1P3p8P1P6p8P1P5p8p1017\p6051000R9P3p8P9P6p8P9P8p8P9P1p8P0P5p8g007ej10Tg008Jj1ZTg008hj1STg007Ej1LTP7j2|Tg01cZR7j2VTg02Eaj2jTg01LSj1:Tg00:Oj2DTP2j3=Tg00;@j1aTg00O8j3_Tg01hBj2]Tg00<UR2j11Tg00>OR5j23Tg00<;j3UTg01D1j2wTg00U>j1;Tg00QJj1>Tg00>lR0j25Tg02K;j1iTg02J]j1PTg00>5j2HTg02Cmj4dTg00WAl<CTg00?Hj4KTg013[R1j29Tg00?oj1ATg009Kj1^Tg00@Tj1FTg00A3j2BTg00A\j3GTg00BEj2\Tg00C1j1{Tg00CQj3YTg00D1j2XTg00DOj1zTg00Dmj4WTg00EKj1yTg00Eij1xTg00FTj2@Tg00G7j2ETg00GZj1vTg00H<j3ITg00IJj2uTg00Ilj2sTg00JXj3rTg00K7j4qTg00Kij4QTg01hlj2nTg02>Ej2mTg02>mj3kTg02LGj3lTg00H_j4RTg02Ljj3oTg02Mej2pTP4j6JTg01e1j4gTg02Nfj2tTg00WflBOTg00YTl<fTg00XLj7[Tg00Y0j8eTf0R4#0#0p=?%;4#;p=6%04#0#0#0#0#0#0#0p=8g00[6R9/54p=2g00ZXR8/H4p=4g00[TR6P6P6P8P8P8g00\3P2P2P2P5g00\Sf5R3f4R:f3R;f2R<f1R=P4MBOp=NP6P8P8P8P2P2P3P:P;P<P=P4M<fp=MP8P8P8P8P8P8P5P4P=P<P5P;P:P3f6R5f7R>f8f9MBOp=cP8P8P0P3P0P:P9P9P;P<P=P4M<Cp=bP6P8P7P2P1g01ieP3P:P;P<P=P4M<Cp=`P<g00^?R2g00^^R7P7g00_>R?P8P=g00]XP4CRg00_^R@F[p=7%04#0#0#0p=TP;P2P7P7P?P<P=P4Gep=<P=P2P7P7P?P4P@F[p=hg00aaR@#0R2#0RA#0RB#Z#SRC#LRDp,2evRE'|RF,V4%0B#?RB#ZRG#SRHp,2spRIp,2avRJ/jERK%:JRL'DRMA=D=E#:'DRN#a5_GRO1]G41]GIRPA=D<E#:RQ,DM#1'35U8XIHRRPH%1N,3P,wGPRg02Ol%1MRR%0BRH#;#0#;#0#?#;#0#;#6#0#?#>RS'5RT%i<%1Q%?H#8RH#>RQ'5A=D;E#:RU,DMRV#1RW,3PRX%2X%1KRY%1LRZ'3R[%1UR\'3R],3PR^#2P4X48R_15=4#PXE8X48R`1H89PXP^P_P_P_P8P8g02DP13=4Cd#4XK8XL8PPPP%4PPWP]P_P_%14#4X46RWPVP]PMP[PKPY%4YPLPZ%4ZENR]PUP\%4\ENEMM:cR\EbPT15[SRTP8P8P0P_P0P`PRP_P[O1P_P_PWPMP[P]EMPSPS%4SM<CP=CKR]PT1V:F%1:R[%1FRM'9RWP:P[%4[PFPM%4ME`P;CKR[PW%A3RR%13#2R`A=D5E#:R0#ARU%10#2R0%ALRL%2ZRV%AKRK%2YRa%AFRF%2MRMp,3stkp,2hwO1Rb%^CRCg00bFRcg00Z9Rd#FRe#FRf#FRg#F,B81B8g1B8f1B8e1B8d5G85G85G8Rd5G8g00c2Re'\%{cRf3Y%LcRgP8P81X8:P<%z8CWP=1X8;CWRh%y8Ri%x8Rj1@89Rk1E82Rl57j%v7R7Pj%;@Rm,E8Rn97jkP7Pj1E8ARA97jkP7Pj%6m#6#6#6#6#6#6#0#?#T#8#8#8#>Rm,@81E8@R@57jP7AI8lnRn=I8A9I8@Rl97jkC<C<C<C<1uj?R?P4P<g00dERkg00deRo'H1s4<=UkodAr89=CqRob9b<b=X08X18X28X38%2=%2;%2315m;1335/3>,3:#2[[[[^08^18^28^38P4f<R>==DE#:#1PZPYPPP;P:P3p,6Hsp_loO8b8bDbCbBbAb@b?b7b5CQ%>2R2%>BRB'nRm,9X19^mP8P8P1P_P119=4#PXE8X48PXP^P\PmPm%4mM<CP]PTP[PWPRP`PUP0PLPVPKPaPFPM1m2B1992RM%2B199mR9[[%22RFg00g5RaAk2B=UW6%2m\aRa^6FP4P;O1PaPbPCP:P4P5O2X>MP9^>M1\de=YcfPgPhPiPj1@8S97jnP7Pj1@8Q97jAP7Pj%?H#T#8#8#8#>RH,@897j@P7P8Plg01jG1@82=l8GCR,hjC<C<C<P?Pob9b<b=X08X18X28X3813=</5S15:Q15<H13:3/35,3;/9m[[[^08^18^28^38P4f@==DE#:#1PZPYPPP>f=p,6Hsp_hiO7b8b;bDb:b:b;bCbBbAb@b?b7b5CQ3obGbFPO1pINEJPIPJPEP=Cg1t=4EJWHXJ6o"). Qed.

  Lemma cat_envp_ptr_nz : forall k, (k < length ev)%nat ->
    bv_unsigned (cat_envp_ptr sp av ev k) <> 0%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) ["Layout"] "h01xh14__x1h24__x2h34__x3h44__x4h52Hkh63Hk0h77__arithh84__ffh98__varmaph:5__with;4cstrh<5cstr0h=5cstr1h>5cstr2h?5cstr3h@1khA1mhB1nhC3stkhD1yhE1zp;1p;2p;3p;4p;<p;6p;Bp;7p;8p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000dR2p4p710p8P0P2p4p7210p8P0p1001Ap4p710R0p8p1001]p4p710R2p1002:p4p710R3p8P2g002VR4p4p710R5p8p10034p6051000R6P1p8P6P3p8P6p10043p4p710R7p8P6P0p8p1004Up6051000R6P1p8P6P3p8P6P7p8P6P0p8p1005^p6051000R6P1p8P6P7p8P6P0p8p100kFp6051000R0P2p8P0g00NYR2p4p710R6p8P0g00goR7p4p710R1p8P0p100hOp4p710R3p8P0p1006fp4p710R0p8p100mIp6051000R8P6p8P8P5p8P8P1p8P8P3p8P8P0p8p100oRp6051000R8p100nOp4p710R3p8P8P6p8P8P5p8p1011:p6051000R1P3p8P1P6p8P1P5p8p1017\p6051000R9P3p8P9P6p8P9P8p8P9P1p8P0P5p8g007ej10Tg008Jj1STg008hj1aTg007Ej1ITP7j2uTg01cZR7j2OTg01hBj2JTg02Eaj2]Tg01LSj1;Tg00:Oj2HTP2j3ATg00<UR2j11Tg00>OR5j22Tg01DWj1BTg00<;j1mj3ETg02J]j1jTg02Cmj4eTg00>5j2CTg00WAl<KTg02Q2j3\Tg013[R0j2[Tg00?Hj4YTg00?oj18Tg009Kj1XTg00@Tj1?Tg00A3j29Tg00A\j3@Tg00BEj2WTg00C1j1VTg00CQj3UTg00D1j2GTg00DOj1tTg00Dmj4TTg00EKj1sTg00Eij1rTg00FTj2QTg00G7j2<Tg00GZj1oTg00U>j1FTg00QJj1lTg00H<j3DTg00H_j4NTg02CIj6iTg00IJj2hTg00Ilj2dTg00JXj3fTg00K7j4gTg00>lj2MTg00Kij4cTg01e1j4kTg02Q[j2bTP4j6nTg00WflBPTg00YTl<_Tg00XLj7pTg00Y0j8qTf0R4#0#0p=Lg00ZXR1g00[6R97E4p=>1C14p=3g00[TR8P8P8P1P1P1g00\3P2P2P2P5g00\Sf5R6f4R3f3R:f2R;f1R<P4MBPp=RP8P1P1P1P2P2P6P3P:P;P<P4M<_p=`P1P1P1P1P1P1P5P4P<P;P5P:P3P6f6R5f7R=f8f9R>MBPp=^P8P1P7P2P0g01ieP6P3P:P;P<P4M<Kp=Z1M94p=4P1P<g00]XP4CNp=:P<g00^?R0g00^^R2P2g00_>R7P4g00_^Fpp=7%F4#Fp=6%04#0#0#0p=5P:P0P2P2P7P;P<P4Gqp==g00aaR?#0R@#0RA#0RB#S#aRC#IRDp,2evRE'uRF,O4P1%0B#L#SRBp,2spRG'JRHp,2avRI/]ERJ%;IRK'HRLAAD<E#;RM'HRN#1RO'2RP%>4#BXE1%>PRQ#B%1JRR%1KRS'2RT%1MRU'2RV,2HRW#>RX#BP1P1%m1RYP4X01RZPYAE1<4#jXD1X01PPPWPZPZPZP1P1g02DP12<4Ce#3XA1XB1PHPH%3HPOPVPZPZ%14#3X08PNPVPLPTPJPR%3RPKPS%3SERPMPU%3UERE`M:^P9P91C19M<K9\QX1O<F%1<RX%1FRQ'[RUP<PX%3XPFPQ%3QEZP4CYPU%8;%1;#4AAD:E#;RU#8%1U#4%8K%4S%8J%4R%8F%4Qp,3stkp,2hwO1%XCg00bFRCg00Z9RQ#?RF#?RJ#?RK#?,91191K191J191F191Q5@15@15@15@1g00c2'W%VC3U%ICP1P11G13P;%t1CTP<1G1:CT%s1%r1RC1Q19RQ1<1@R@':,7C%o2RFPC%F?RJ,<1RK,:Q,7CPFPC1<1ARA,:Q,7CPFPC%6J#6#6#6#6#6#6#0#L#5#5#5#5#5#5#5#lRJ,Q11<1?R?':,7CPFPCP0P2P2P7P1AD1@K=D1A9D1?g00c^PQCN,7CEiC=C=C=C=1hC7P4P;g00dERCg00deR7'C1d4;=EC7dAf19<Cgb8b9b:X11X21X31X41%4<%4:%461MJ:1265/2=,23#>g00fX[[[[[^11^21^31^41P4AAD>E#;#1PSPRPHP:P3P6p,6Hsp_loO8b7bCb?b>b=b<b;b6CcPGPIPEP<Ck,JB1b<4EnW5X@8o"). Qed.

  Lemma u_cat_argv_ptr : forall k, (k < length av)%nat ->
    bv_unsigned (cat_argv_ptr sp av ev k)
    = (bv_unsigned sp + Z.of_nat (cat_struct_size av ev + total_arg_bytes_nat (firstn k av)))%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) ["Layout"] "h02H1h14__x1h24__x2h34__x3h41xh52Hah63Hk0h77__arithh84__ffh96__sat4h:6__sat5h;8__varmaph<5__with=4__x4h>1ah?4cstrh@5cstr0hA5cstr1hB5cstr2hC5cstr3hD3stkhE1yhF1HhG2H0hH2HkhI1bhJ1khK1mhL1np&0p;1p;2p;3p;4p;<p;6p;5p;Bp;7p;8p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000dR2p4p710p8P0P2p4p7210p8P0p1001Ap4p710R0p8p1001]p4p710R2p1002:p4p710R3p8P2g002VR4p4p710R5p8p10034p6051000R6P1p8P6P3p8P6p10043p4p710R7p8P6P0p8p1004Up6051000R6P1p8P6P3p8P6P7p8P6P0p8p1005^p6051000R6P1p8P6P7p8P6P0p8p100kFp6051000R0P2p8P0g00NYR2p4p710R6p8P0g00goR7p4p710R1p8P0p100hOp4p710R3p8P0p1006fp4p710R0p8p100mIp6051000R8P6p8P8P5p8P8P1p8P8P3p8P8P0p8p100oRp6051000R8p100nOp4p710R3p8P8P6p8P8P5p8p1011:p6051000R1P3p8P1P6p8P1P5p8p1017\p6051000R9P3p8P9P6p8P9P8p8P9P1p8P0P5p8g007ej10Tg008Jj1]Tg008hj1VTg007Ej1STP7k201Tg01cZR7j2ZTg01TEj3jTP2j3>Tg01LSj1:Tg00;@j1KTg00O8j3ETg01hBj2HTg02Eak200Tg00:Oj2FTg00<UR2j11Tg00>OR5j24Tg00<;j3PTg01D1j2vTg00U>j1;Tg00QJj1BTg00>lR0j25Tg02IOj2gTg00:fR1j2YTg02J]j1\Tg00>5j2MTg02Cmj4bTg00?Hj4ITg00WAl<ATg013[R9j2<Tg00?oj1?Tg009Kj1~Tg00@Tj1RTg00A3j2GTg00A\j3QTg00BEj2}Tg00C1j1|Tg00CQj3zTg00D1j2JTg00Dmj4LTg00EKj1yTg00Eij1xTg00FTj2@Tg00G7j2CTg00GZj1uTg00H<j3OTg00IJj2pTg00Ilj2oTg00JXj3nTg00K7j4lTg00Kij4WTg01hlj2kTg02>Ej2mTg02>mj3iTg00DOj1hTg02LGj3qTg00H_j4XTg02Ljj3rTg02Mej2sTP4j6NTg00T;j3fTg02R`j4wTg02Saj5eTg00WflB[Tg00YTl<dTg00XLj7cTg00Y0j8{Tf0R4#0#0p=D%;4#;p=6g00[6R8/54p=2g00ZXR6/M4p=3g00[TR3P3P3P6P6P6g00\3P2P2P2P5g00\Sf5R:f4R;f3R<f2R=f1R>P4MB[p=UP3P6P6P6P2P2P:P;P<P=P>P4M<dp=TP6P6P6P6P6P6P5P4P>P=P5P<P;P:f6R5f7f8R?f9MB[p=aP6P6P0P:P0P;P8P8P<P=P>P4M<Ap=`P3P6P1P2P0g00]6P:P;P<P=P>P4M<Ap=_P3P6P7P2P9g01ieP:P;P<P=P>P4M<Ap=^P6P>g00]XP4CXp=9P>g00^?R2g00^^R7P7g00_>R1P4g00_^Fcp=8%04#0#0#0p=t%04#0#0#0#0#0#0#0p=7P<P2P7P7P1P=P>P4G{p==g00aaR2#0R@#0RA#0RB#]#VRC#SRDp,2avRE+01RF,Z4%0B#DRB#]RG#VRHp,2spRIp,2evRJ7jEA>D>E#:RK#KRL5EGRM1HG41HGIRN200EJROA>D=E#:RP'F#1'45P6XIHRQPH1FOKRR#K9EGIRSPQPH%1R,4NRH,vGPQg02Ol%:ERQ,FORT#1RU%0BRV#;#0#;#0#D#;#0#;#6#0#D#BRW'5RX1g=E1YPQA>D<E#:RP,FORY#1RZ,4NR[%2[%1OR\%1PR]'4R^,4NR_#2P4X46R`15>4#\XE6X46Ra1M68P[P_P`P`P`P6P6g02DP14>4Cb#3XK6XL6PNPN%3NPZP^P`P`%14#3X43RZPYP^POP\%3\R^PPP]%3]RYEUETM:aRbE`1YPQ%1QRc,5]RdPPP]PYPQPc%3cRYE_P4CIR]PdPX14\cRX/5WRPP6P6P0P`P0PaPUP`PXO1P`P`PZPTPXPOP\P^PQPcPYEUETPWPW%3WM<AP=CIRYPP1Z:F%1:R^%1FRX'<RTP:P^%3^PFPX%3XE^P;CIR^PT%?5RZ%15#2R5%?FRF%2XRXA>D?E#:R?#?RU%1?#2R?%?QRQ%2cRa%?OR0%2\Rep,3stkp,2hwO1Rf%~CRCg00bFRgg00Z9Rh#RRi#RRj#R,G61G6j1G6i1G6h5Q65Q65Q6g00c2'}%|g3zRh%SgRgP61J6=P>1J6<RiCL%y6Rj%x6Rk1@68Rl1C6@Rm'9,8k%u7R7Pk%;2Rn,C6Ro,9l,8kP7Pk%6n#6#6#6#6#6#6#0#D#t#7#7#7#BRn,@61C62R2'9,8kP7AO6mo9O62Rp,9l,8kC=C=C=1pk1R1P4P=g00dERlg00deRq'M1o4==PlqdAn68>ClRqb8b;b<X16X26X36%2>%2<15n=14;:,4<Rn#2[[[^16^26^36P4f=Rl=>DE#:#1P\PNP=P;p,6Hsp_loO6b7bDbCbBbAb@b?b6b0b0CW%B@R@%BBRB'kRr,<[1<_rP6P6P9P`P91<>4#\XE6X46P[P_PbPrPr%3rM<AP]PdPYPPP^PTPZP5PFPXPUP?PQPaP0Pe1m@B1<8@Re%2B1<8rR8[[%2@R0g00g5RaAi@B>UW5%2r\aRa^50P4P=O1PaPfPCP;P4P:O2X>eP8^>ePhPgP6P61J6;P=%h6CLP>PiCLPjPk1C6ARA9O6m1@6W'9,8kP7Pk19oA,8kP7Pk%7V#7#7#7#7#BRV,@6,92,8kP7P6Ppg01jG1@6@=q6GCX,8kC=C=C=P1Pqb8b;b<X16X26X36X=614></5W15<;15=V1<nr[[[^16^26^36^=6P4PcfA=>DE#:#1P\PNf<Plp,6Hsp_hiO7b7b:bDb9b9b:bCbBbAb@b?b6b0b0CW3rbGbFPS1sIREN%KO9EGI=EGLAfIOKEN1HGM=P6HePIPEPJP>CwPIPEPJP>P4DeENWHXJ3o"). Qed.

  Lemma argv_str_len : forall k, (k < length av)%nat ->
    (Z.of_nat (length (nth k av [])) <= 131071)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) ["Layout"] "h02Hkh11kp;1p;2p;4p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000dR2p4p710p8P0P2p4p7210p8P0p1001Ap4p710R0p8p1001]p4p710R2p1002:p4p710R3p8P2p1002Vp4p710R4p8p10034p6051000R5P1p8P5P3p8P5p10043p4p710R6p8P5P0p8p1004Up6051000R5P1p8P5P3p8P5P6p8P5P0p8p1005^p6051000R5P1p8P5P6p8P5P0p8p100kFp6051000R0P2p8P0p100NYp4p710R2p8P0g00goR5p4p710R6p8P0p100hOp4p710R1p8P0p1006fp4p710R0p8p100mIp6051000R3P2p8P3P4p8P3P6p8P3P1p8P3P0p8p100oRp6051000R3p100nOp4p710R1p8P3P2p8P3P4p8p1011:p6051000R6P1p8P6P2p8P6P4p8p1017\p6051000R7P1p8P7P2p8P7P3p8P7P6p8P0P4p8g007ej10Tg008Jj16Tg008hj12Tg007Ej11TP5j25Tg01cZj24Tg02Tij43Tg00[Tf0R5g00aa#0#0#0#6#2#1p,2avR4'5'4P4f1p,3HvaP5C3W0W1o"). Qed.

  (* [comment removed for export] *)
  Lemma auxv_words_eq : forall rnd,
    auxv_words ph rnd uid hw =
    [AT_PHDR; Z_to_bv 64 (Z.of_N (ph_addr ph)); AT_PHENT; Z_to_bv 64 (Z.of_N (ph_ent ph));
     AT_PHNUM; Z_to_bv 64 (Z.of_N (ph_num ph)); AT_HWCAP; hw; AT_PAGESZ; Z_to_bv 64 4096;
     AT_UID; uid; AT_EUID; uid; AT_SECURE; Z_to_bv 64 0;
     AT_RANDOM; rnd; AT_NULL; Z_to_bv 64 0].
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) ["Layout"] "h03rndp;1p;2p;3p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000dR2p4p710p8P0P2p4p7210p8P0p1001Ap4p710R0p8p1001]p4p710R2p1002:p4p710R3p8P2p1002Vp4p710R4p8p10034p6051000R5P1p8P5P3p8P5p10043p4p710R6p8P5P0p8p1004Up6051000R5P1p8P5P3p8P5P6p8P5P0p8p1005^p6051000R5P1p8P5P6p8P5P0p8p100kFp6051000R0P2p8P0p100NYp4p710R2p8P0p100gop4p710R5p8P0p100hOp4p710R6p8P0p1006fp4p710R0p8p100mIp6051000R1P2p8P1P4p8P1P5p8P1P6p8P1P0p8p100oRp6051000R1p100nOp4p710R6p8P1P2p8P1P4p8p1011:p6051000R5P6p8P5P2p8P5P4p8p1017\p6051000R3P6p8P3P2p8P3P1p8P3P5p8P0P4p8g008Jj1>Tg008hj1<Tg007Ej16Tg02V0j1=Tg02Vmj13Tg01D1j22Tg02WKj1;Tg02XGj1:Tg00QJj18Tg00C1j17Tg00>5j29Tg007ej15Tg00CQj34Tf0R4#5#5p=1f4f3f2f1;4434p=0g00aa#1#1#1R0#>R5#<R3%63P3g02YCP3p,2phR1#=#3,25P3g02Z?P3%;1#3,25P3g02[<P3%:1#3,25P3g02\9P3p,2hwP3g02]6P3%10#1#1#8,25P3g02^4P3p,3uidR0P3g02^oP3P0P3g02_kP3g00[6,25R5P3g02`iP3P4P3g02agP3P5%73D0D0D0D0D0D0D0D0D0D0'9W0o"). Qed.

  (* [comment removed for export] *)
  Lemma rnd_facts : forall (Hal : (bv_unsigned sp mod 16 = 0)%Z),
    (bv_unsigned sp <= bv_unsigned (at_random_ptr sp av ev))%Z
    /\ (bv_unsigned (at_random_ptr sp av ev) + 16 <= bv_unsigned sp + Z.of_nat (length bsb))%Z
    /\ (bv_unsigned sp + Z.of_nat (length bsb) < 2^64)%Z
    /\ (bv_unsigned (at_random_ptr sp av ev) mod 8 = 0)%Z
    /\ (forall j n, (j + n <= 16)%nat ->
          rdn segs stk (Z_to_bv 64 (bv_unsigned (at_random_ptr sp av ev) + Z.of_nat j)) n
          = Some (firstn n (skipn j (at_random_bytes (ed_random rdraw))))).
Proof.
ltac2:(KReplay.run1 (kr_t_RefLayout ()) ["Layout"] "p'0h01Hh14__x1h24__x2h31zh42H0h52H1h62H2h72H3h82H4h92H5h:2H6h;2H7h<2H8h=5Hlen0h>7__arithh?4__ffh@6__sat1hA6__sat2hB6__sat3hC6__sat4hD8__varmaphE5__withF4__x3hG4cstrhH5cstr0hI1qhJ2q0hK1rhL2r0hM1jhN1nhO2HahP4__x4hQ4__x5hR4__x6hS1bhT3offhU3HalhV3HblhW3HjnhX4HlenhY4HmodhZ3Hnwh[2Hph\3Hrdh]2Huh^1eh_1xi001xh`1yp%0p&0p;1p;2p;3p;4p;6p;Bp;<p;7p;8p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000dR2p4p710p8P0P2p4p7210p8P0p1001Ap4p710R0p8p1001]p4p710R2g002:R3p4p710R4p8P2g002VR5p4p710R6p8p10034p6051000R7P1p8P7P4p8P7p10043p4p710R8p8P7P0p8p1004Up6051000R7P1p8P7P4p8P7P8p8P7P0p8p1005^p6051000R7P1p8P7P8p8P7P0p8p100kFp6051000R0P2p8P0g00NYR2p4p710R7p8P0g00goR8p4p710R1p8P0p100hOp4p710R4p8P0p1006fp4p710R0p8p100mIp6051000R9P7p8P9P6p8P9P1p8P9P4p8P9P0p8p100oRp6051000R9p100nOp4p710R4p8P9P7p8P9P6p8p1011:p6051000R1P4p8P1P7p8P1P6p8p1017\p6051000R:P4p8P:P7p8P:P9p8P:P1p8P0P6p8g007ej12Tg008Jj1rTg01hBj2^Tg00QJj1ITg01OPj23Tg008hj1qTg01JPk30?Tg00;@j1STg00O8j3XTg00<;j37j1{Tg00@Tj1@Tg00:Oj2BTP8k20RTg00<UR8j11Tg00:fk20NTg007Ej1tTg009Kk10JTg00RKj4OTg01PPk10FTg01QNk10BTg00Vcj3mTP2j3lTg009mj2kTg0147R2j29Tg01RRR6k208Tg00>lj25Tg00>OR0j20Tg01hlk203Tg013[j26Tg01D1j2UTg00U>j1=Tg00=5k20TTg00=Xk30STg00>5j2HTg00?Hj4xTg00?oj1eTg024:k20Qj3wTg02>Ek20PTg02>mk30OTg024kj2cTg01DWj1vTg025Lj2QTg01Wgj2CTg023Sj2bTg025ij2aTg026Pj2`Tg0276j2]Tg00LTk10MTg00M2k20LTg00MSj3[Tg00A3j2sTg02B7k20HTg02B`k30GTg00BEj2pTg020ck20ETg00C1k10DTg00CQj3oTg00D1j2VTg00DOk10ATg00EKk10>Tg00Eik10=Tg00FTj2gTg00GZk10<Tg00G7j2iTg01XDj3jTg00IJk20:Tg00Ilk20;Tg00JXk307Tg00K7k406Tg02LGk304Tg00H_j4dTg02Ljk30@Tg02Mej2nTP5j6PTg01Rlk40CTg02bck402TP3j6YTg02cIk401Tg02cek400Tg029Hj4ZTg00WfmB0ITg00WAl<~Tg00A\j3_Tg00Dmk40KTg00XLj7uTg02CIj6}Tg00H<j3|Tg00Y0j8\Tf0R3#2#2p=fg00ZXR5g00[6R1773p=;%@3#@p=Wg00[TR:f1R9;73p=?1393=751p=:f2R71993'9p=D%=3#=p=G%23#2#2#2#2#2#2#2p=<A7593p=8P:P:P:P5P5P5g00\3P8P8P8P0g00\Sf5R0f4R4f3R;P7P9P3NB0Ip=zP:P5P3P8P9P7P;P4P0f6R8f7R<f8S00M<~p=y1513p=41s53p=MA_5939_57p=NP5P7P9P3H0Kp=F1g53p=JP7g00^?R=g00^^R>P>g00_>R?P5P9g00c^P3Cdg00_^R@Fup=>P9P=P>P>P?P3E}p=h1i53p=KA|593p=LP;P=P>P>P?P7P9P3G\p=TP5P9g00]XP3Cdp=EP9P=P>P>P?P3P@Fup=A%23#2#2#2p>09P8P=P>P>P?P0P4P;P=P>P>P?P7P9P3G\G\p=RA_593p>05g00aaR=#2R@#2S01#2RA#2RB#fS02#rRCp,2spRD'^RE%IBRB'3RF#;g02dF%qCRGp,2avp,2ev60?DRH%S39XCD37g00Z9RI#WRJ#@RK#@RL#@RM#@RN#@RO#@#W#W#W#WRP,B3%rA#qRQp,3bsb+0RRR'?%13RS%IART':1B9300NPRU%tQS03$0JRVp,4segsRWp,3stkRX%S79XCHS04P9COQ03p,5rdraw$0F$0BS059mQ79lQ9'kRY37[^N:^M:RZ'93DS06XT:R[-08:P6P:P[1^CHR[,5E10[B%1RR6,0ER\'5%I@R]Q02#IR^+03R_,6\R`1:[TPWPX%17S07,0[,UCS08P9CO=7VY\U^N:^M:3D3DRaP3Q06P2%S99XCD97GH1B9P/?R%19Rb/:T;DZPaP3%S;9XCD97GH1B4P/?R%14/:T;DZP21B0P/?R%10/:T/9ZPaP31B<P/?RQ00#1/:T/9ZP2f9S09#1/:TPZPaP3f;S0:#1/:Tg01a0P`g02eJ%=A#2#f#=#2#=#G#2#<#IS0;,56PGf?RA#S9XCDS0<1^C3f@S0=#1Ra,0ER2'8XSGRcPG%1ARd,0ES0>,UCPcQ0>1BAPRc/?R10dBRe/86S0?%{:S0@%{5S0A18bS1?9320T9340SX`:X_:S0BPcPePAPd1H5dPPPB1H5BS0CEzPRP61H56S0DM9yP<CxS0EQ0?%eRRd%46RefARc#eS0F%1cS0G#4S0H20QEBRc%4E%4B%4FRb[[RS20P]^Rf161]%4^161_[[Rg%4]Rhg00g5RiB0O]^9UWOR^%4_\i^OhRhfES0I#1?wT;S0J%4TS0KfFS0L#1S0M/3T#4[S0NQ0M/cTS0O%;TRi#vS0PfG#1Rj1QjT,CT13jTS0Q'0'8[S0R1bjTS0S161TS0TfHS0U#1Rk/3TS0V#4Q0V/6T'9[S0W1akTS0X16T1S0YfIS0Z#1S0[/3TRl,6T15l1'9[S0\Q0[/`TS0]fJ#1Rm/QT#;\iS0^1]mTS0_fK#1Rn/3T/8n\iS0`1QnTS0aP5fL#1S0b/3TS0cP51cEBRo%;BRp#v1QEBRq,CB/0F,8E[Rr1bEBRs161B16FB,9b[Rb1aEBRt16B116BF15F1'9[Ru1`EBRv%;q\pRw1]EBRx18FE\pRyPqP5PFP5g00bFRz&0M=-0L5R{%MNRN5[5%MMRM9[5{%MKS0d9[5{%MJS0e9[5{1s5IS0f3N3N20H5TQ0f60G5%MO%MLS0gQ0dQ0e3N9NNM3Ng00c2S0h'p+0E&0DzRM3o%tzRN1V541V507F7&0A5RL1V587F;7F9&0>5RO&0=5RIPI%JBR{1g51RJ5>I,hI&0<>R>1i5=RK%==R=#=S0i#K9j5{%K=R|'L5>ICTP>PIPI%JTR}=>IJ,hIS0jP>%K@R~%2=#K9j5}Q01#KR}'L5>ICTP>PI1EJ~,AIS01P>PIA>I}JP>PIA>I|JP>PIQ0i#=#G#G#G#G#G#G#2#f$09#<#<#<#IR}#J/EK,AIS0iP>1LK~R=,EJ,AIFRFRFR20:I?R?P3P7g00dES0kg00deRJ'HQ0k20;37;7JdB07519H06RJb?bDbEX15X25XF5XP5XQ5XR5g00fXS0k\p1CB8/0;,89[Q0k\iS0k1CT8/00,8;[%4;%;8Rp15}0108<#4[\p[[[[^15^25^F5^P5^Q5^R5P3P7Q09Q00P9fU#1RpPEP<f>fCS09Q0ZfYp,6Hsp_loR<O<b>bLbJb<b;b:b9b8bKbIb7b6b5b4b0b@bAbBbCbHbGb=Q0EQ0?PdPeQ0FQ0HPcPSPfPgP^PhQ0JQ0NQ0OQ0RQ0SQ0WQ0XQ0\Q0]Q0^Q0_Q0`Q0aP5Q0cP5PoPrPsPbPtPuPvPwPxPyPqP5PFP5Q0gQ0dQ0eQ0f+053NQ0h'p=ozMPN1V57Rz1V5;S0h?F;L7F9POPI1L~{S0g%=@#KR@5>IP>PIQ0;#J,E@,AIP>PIQ02#2#<#<#<#<#<#IR@#J,EK,AIP>PIQ0iP>P5P=g01jG%J]>045CCd,AIS0iFRFRP?PJb?bDbEX15X25XF5109B/87S02Q0;,5;157@15};1040/6_[[[[^15^25^F5P3P6PpPEQ0IQ0Lp,6Hsp_hiP<O7b>bLbJb<b;b:b9b8bKbIb7b6b5b4b0b@bAbBbCbHbGb=40@Q0<1nDAEPPHQ0:EPQ0>,8[P5P215E3103B/5\1:3TS0>PWPXQ07,0;,UCP9CO=7VY\U^N:^M:5D`3DX3515E2102B/5\S0:132TS0<#;S0LPWPXQ09#1,0ES0;Q07'0,UCP9CO=7VY\U^N:^M:S07'9S0d,9`S0f'9Q0=/BPRY/?R10aBR2/86R\Q0@Q0AQ0BPYP2Q0=Pa1H5aPPPBQ0CEzPRP6Q0DM9yQ00CxRRP\PdPefBRP#eR2%1PS00#4RPPcPSPfPgP^PhQ0M?wT;RYQ0KQ0Q#4[RA1cjTRjQ0P1QkT,CTQ0V'0,8k[RD1bkTRkQ0T%4l16lT'9[RlQ0[/aTR<Q0Y13mTRp,6T15p1'9[Rp1`mTRmQ0a#;\iR41]nTRnQ0cQ0b'8\iRiQ0b/QTR}P5fM#1/3TR@P5PoPrPsPbPtPuPvPwPxPyPqP5PFP5PMPNAFz9LS0bPOPIQ01P>1EK=,AICTP?PJb?bDbEX15X25%491097R~,59[^15^25P3fV#1S01PEQ09O3b>bLbJb<b;b:b9b8bKbIb7b6b5b4b0b@bAbBbCbHbGb=Q0:Q0fPRP\PdPeP2PPPcPSPfPgP^PhPYPAPjPDPkPlP<PpPmP4PnPiP}P5P@P5PoPrPsPbPtPuPvPwPxPyPqP5PFP5PMPNQ0h9Fz9POPIQ0g=>I|P>1L={1LK|'E,AICTP?PJb?bDbEX15X25XF5Q0210~B109;'5[^15^25^F5P3P6Q01PEQ0IO4b>bLbJb<b;b:b9b8bKbIb7b6b5b4b0b@bAbBbCbHbGb=P`Q0dPRP\PdPeP2PPPcPSPfPgP^PhPYPAPjPDPkPlP<PpPmP4PnPiP}P5P@P5PoPrPsPbPtPuPvPwPxPyPqP5PFP5PMPNQ0bPOPIQ0iP>Q0iCTP?PJb?bDbEX15X251039/6_16~_[^15^25P3P6PEQ0UO3b>bLbJb<b;b:b9b8bKbIb7b6b5b4b0b@bAbBbCbHbGb=Q0LQ07P513ETR613aT'0/3T%;3X35R~P5P6P1P513FTP~P5P1Q0>X351H51R~PFfDEPP6PEPBPTP51C3T,8BX35P]1C]T,H5H0CH02EYH01A7516P5P1Q00/3T,03/:TX35P5P11013/:TX35P~Q0G/3TP0EPP6P3EYb0Q0<PEPaPTPRP\PdPeP2PPPcPSPfPgP^PhPYPAPjPDPkPlP<PpPmP4PnPiP}P5P@P5PoPrPsPbPtPuPvPwPxPyPqP5PFP5PMPNPLPOQ0jP?PJb?bDbEQ0kP3b>bLbJb<b;b:b9b8bKbIb7b6b5b4b0b@bAbBbCbHbGb=H00EPP5P[PWPX%1;,03,UCP7COQ03Q059mQ;9lQ7'kRQ57VX35PGQ04PWPXP3P7CO=7VQXSGP8P7P9P3O3Q081nH7EYQ0;P;EYXWUXN:XM:CZCZCZCZP[P3EPb]bVbZX\ZWYP9P3O2n2001000010121000000W0WXP9P3O2n2001000010121000000W0W[P9P3O2n2001000010121000000W0XT:P9P3O2n2001000010121100000b^WUo"). Qed.

End Layout.

End RefLayout.
From Stdlib Require ZArith NArith List Lia Bool. From stdpp.bitvector Require definitions. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
Module FrmFastScan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module FRMF.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma expand_c_safe (c : cinstr) : FrmKeep.FRM.instr_frm_safe (expand_c c) = true.
Proof. destruct c; reflexivity. Qed.

(* [comment removed for export] *)
Ltac dcrush1 :=
  match goal with
  | H : ?o <> ?o |- _ => exfalso; exact (H eq_refl)
  | |- ?l = ?l => reflexivity
  | |- context [match ?x with _ => _ end] =>
      lazymatch x with context [match _ with _ => _ end] => fail | _ => idtac end;
      first [ is_var x; destruct x | destruct x ]; cbv beta iota
  end.
Ltac dcrush := repeat dcrush1.

(* [comment removed for export] *)
Lemma decode_safe (w : bv 32) :
  bv_unsigned (bits 0 7 w) <> 115 ->
  match decode w with Some i => FrmKeep.FRM.instr_frm_safe i | None => true end = true.
Proof.
  intros NE. cbv beta zeta delta [decode].
  remember (bv_unsigned (bits 0 7 w)) as o eqn:Ho. clear Ho.
  dcrush; reflexivity.
Qed.

Lemma low7_bits (w : bv 32) : bv_unsigned (bits 0 7 w) = bv_unsigned w mod 128.
Proof. unfold bits. rewrite bv_extract_unsigned, Z.shiftr_0_r. reflexivity. Qed.

Theorem safe_unless_system (w : bv 32) : bv_unsigned w mod 128 <> 115 -> FrmKeep.FRM.word_frm_safe w = true.
Proof.
  intros NE. unfold FrmKeep.FRM.word_frm_safe, decode_any.
  destruct (decide _) as [E3|N3].
  - pose proof (decode_safe w ltac:(rewrite low7_bits; exact NE)) as D.
    destruct (decode w) as [i|]; [exact D| reflexivity].
  - destruct (decode16 _) as [c|]; [apply expand_c_safe| reflexivity].
Qed.
Corollary safe_unless_systemC (w : bv 32) : bv_unsigned w mod 128 <> 115 -> FrmKeepC.FRMC.word_frm_safe w = true.
Proof. intros NE. apply FrmKeepC.FRMC.safe_of_coarse, safe_unless_system, NE. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma low7_concat (X : bv 16) (b1 b0 : bv 8) :
  bv_unsigned (bv_concat 32 X (bv_concat 16 b1 b0)) mod 128 = bv_unsigned b0 mod 128.
Proof.
  rewrite !bv_concat_unsigned'. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 16) with (2 ^ 16).
  change 128 with (2 ^ 7).
  apply Z.bits_inj'. intros n Hn.
  destruct (Z_lt_le_dec n 7) as [LT|GE].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite Z.lor_spec, Z.shiftl_spec by lia.
    rewrite (Z.testbit_neg_r _ (n - Z.of_N 16)) by (cbn; lia). cbn [orb].
    rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lor_spec, Z.shiftl_spec by lia.
    rewrite (Z.testbit_neg_r _ (n - Z.of_N 8)) by (cbn; lia). reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma low7_le4 b3 b2 b1 b0 : bv_unsigned (le4 b3 b2 b1 b0) mod 128 = bv_unsigned b0 mod 128.
Proof. unfold le4, le2. apply low7_concat. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Fast.
Variable wsafe : bv 32 -> bool.
Hypothesis wsafe_sys : forall w, bv_unsigned w mod 128 <> 115 -> wsafe w = true.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition okP (a : Z) : bool :=
  (match fetch_word segs (Z_to_bv 64 a) with Some w => wsafe w | None => true end)
  && (match fetch_tail segs (Z_to_bv 64 a) with Some w => wsafe w | None => true end).
(* [comment removed for export] *)
Definition fposB (base : Z) (s : PrimString.string) (off : N) : bool :=
  match hex_byte_at s off with
  | Some b => if bv_unsigned b mod 128 =? 115 then okP (base + Z.of_N off) else true
  | None => true
  end.
(* [comment removed for export] *)
Definition fpos (base : Z) (s : PrimString.string) (off : N) : bool :=
  match hex_nybble (PrimString.get s (Uint63.of_Z (Z.of_N (2 * off)))) with
  | 7%N | 15%N => fposB base s off
  | _ => true
  end.
Fixpoint fscan1 (base : Z) (s : PrimString.string) (f : nat) (off : N) : bool :=
  match f with O => true | S f' => fpos base s off && fscan1 base s f' (off + 2)%N end.
Fixpoint fscan2 (base : Z) (s : PrimString.string) (g f : nat) (off : N) : bool :=
  match g with O => true | S g' => fscan1 base s f off && fscan2 base s g' f (off + 2 * N.of_nat f)%N end.
(* [comment removed for export] *)
Definition fseg (g f : nat) (seg : Segment) : bool :=
  if seg_executable seg then
    match seg_bytes seg with
    | [chunk] => if (Z.of_N (seg_size seg) <=? 2 * Z.of_nat f * Z.of_nat g) && (Z.of_N (seg_base seg) mod 2 =? 0)
                 then fscan2 (Z.of_N (seg_base seg)) chunk g f 0 else false
    | _ => false
    end
  else true.

Lemma fscan1_sound base s : forall f o0, fscan1 base s f o0 = true ->
  forall o, (o0 <= o < o0 + 2 * N.of_nat f)%N -> (exists k, o = o0 + 2 * k)%N -> fpos base s o = true.
Proof.
  induction f as [|f IH]; intros o0 H o Ho [k Hk]; [cbn [N.of_nat] in Ho; lia|].
  cbn [fscan1] in H. apply andb_true_iff in H as [H0 H1].
  destruct (N.eq_dec o o0) as [->|NE]; [exact H0|].
  apply (IH (o0 + 2)%N H1); [lia|]. exists (k - 1)%N. lia.
Qed.
Lemma fscan2_sound base s : forall g f o0, fscan2 base s g f o0 = true ->
  forall o, (o0 <= o < o0 + 2 * N.of_nat f * N.of_nat g)%N -> (exists k, o = o0 + 2 * k)%N -> fpos base s o = true.
Proof.
  induction g as [|g IH]; intros f o0 H o Ho [k Hk]; [cbn [N.of_nat] in Ho; lia|].
  cbn [fscan2] in H. apply andb_true_iff in H as [H0 H1].
  destruct (N.ltb_spec o (o0 + 2 * N.of_nat f)) as [LT|GE].
  - apply (fscan1_sound base s f o0 H0 o ltac:(lia)). exists k; exact Hk.
  - apply (IH f (o0 + 2 * N.of_nat f)%N H1); [lia|]. exists (k - N.of_nat f)%N. lia.
Qed.

(* [comment removed for export] *)
Lemma hex_byte_sys_hi s off b : hex_byte_at s off = Some b -> bv_unsigned b mod 128 = 115 ->
  hex_nybble (PrimString.get s (Uint63.of_Z (Z.of_N (2 * off)))) = 7%N \/ hex_nybble (PrimString.get s (Uint63.of_Z (Z.of_N (2 * off)))) = 15%N.
Proof.
  unfold hex_byte_at. cbv zeta.
  set (h := hex_nybble (PrimString.get s (Uint63.of_Z (Z.of_N (2 * off))))).
  set (l := hex_nybble (PrimString.get s (Uint63.of_Z (Z.of_N (2 * off + 1))))).
  destruct (_ || _)%bool; [|discriminate].
  destruct (N.ltb_spec h 16) as [Hh|]; cbn [andb]; [|discriminate].
  destruct (N.ltb_spec l 16) as [Hl|]; [|discriminate].
  intros E. injection E as <-. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  rewrite (Z.mod_small _ 256) by lia. intros M.
  pose proof (Z_div_mod_eq_full (Z.of_N (h * 16 + l)) 128) as D. rewrite M in D.
  assert (Q : Z.of_N (h * 16 + l) / 128 = 0 \/ Z.of_N (h * 16 + l) / 128 = 1).
  { assert (0 <= Z.of_N (h * 16 + l) / 128 < 2); [|lia]. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  lia.
Qed.

(* [comment removed for export] *)
Lemma code_read_first a n b0 rest : code_read segs a n = Some (b0 :: rest) ->
  exists seg, In seg segs /\ seg_executable seg = true
    /\ Z.of_N (seg_base seg) <= bv_unsigned a /\ bv_unsigned a + Z.of_N n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg)
    /\ segment_byte_at (seg_bytes seg) (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg))) = Some b0.
Proof.
  unfold code_read. destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:E; [|discriminate].
  destruct (seg_executable seg) eqn:X; cbn [andb]; [|discriminate].
  destruct (negb (seg_writable seg)); [|discriminate].
  intros R. exists seg. split; [exact (FrmKeep.FRM.find_segment_In _ _ _ _ E)|]. split; [exact X|].
  destruct (FrmKeep.FRM.find_segment_range _ _ _ _ E) as [R1 R2]. split; [exact R1|]. split; [exact R2|].
  destruct (N.to_nat n) as [|n']; cbn [segment_read_bytes] in R; [discriminate|].
  destruct (segment_byte_at (seg_bytes seg) _) as [b|]; [|discriminate].
  destruct (segment_read_bytes _ _ n') as [r|]; [|discriminate]. injection R as -> _. reflexivity.
Qed.

(* [comment removed for export] *)
Definition fetched_at (a : word) (w : bv 32) : Prop :=
  bv_unsigned a mod 2 = 0 /\ exists seg b0, In seg segs /\ seg_executable seg = true
    /\ Z.of_N (seg_base seg) <= bv_unsigned a /\ bv_unsigned a + 2 <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg)
    /\ segment_byte_at (seg_bytes seg) (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg))) = Some b0
    /\ bv_unsigned w mod 128 = bv_unsigned b0 mod 128.
Lemma fetch_word_at a w : fetch_word segs a = Some w -> fetched_at a w.
Proof.
  unfold fetch_word. destruct (Z.eqb_spec (bv_unsigned a mod 2) 0) as [E|NE]; cbn [negb]; [|discriminate].
  destruct (code_read segs a 4) as [[|b0 [|b1 [|b2 [|b3 [|? ?]]]]]|] eqn:C; try discriminate. intros H. injection H as <-.
  split; [exact E|]. destruct (code_read_first a 4 b0 _ C) as (seg & IN & X & R1 & R2 & SB).
  exists seg, b0. split; [exact IN|]. split; [exact X|]. split; [exact R1|]. split; [change (Z.of_N 4) with 4 in R2; lia|]. split; [exact SB|]. apply low7_le4.
Qed.
Lemma fetch_tail_at a w : fetch_tail segs a = Some w -> fetched_at a w.
Proof.
  unfold fetch_tail. destruct (Z.eqb_spec (bv_unsigned a mod 2) 0) as [E|NE]; cbn [negb]; [|discriminate].
  unfold fetch_half at 1.
  destruct (code_read segs a 2) as [[|b0 [|b1 [|? ?]]]|] eqn:C; try discriminate. intros H.
  split; [exact E|]. destruct (code_read_first a 2 b0 _ C) as (seg & IN & X & R1 & R2 & SB).
  exists seg, b0. split; [exact IN|]. split; [exact X|]. split; [exact R1|]. split; [exact R2|]. split; [exact SB|].
  destruct (_ =? 3); [destruct (fetch_half segs (a + 2)) as [h1|]; [|discriminate]|]; injection H as <-; unfold le2; apply low7_concat.
Qed.

(* [comment removed for export] *)
Theorem fetch_safe_of_fscan (g f : nat) :
  forallb (fseg g f) segs = true ->
  forall a w, fetch_word segs a = Some w \/ fetch_tail segs a = Some w -> wsafe w = true.
Proof.
  intros SC a w H.
  destruct (Z.eq_dec (bv_unsigned w mod 128) 115) as [SYS|NSYS]; [|exact (wsafe_sys w NSYS)].
  assert (FA : fetched_at a w) by (destruct H as [H|H]; [exact (fetch_word_at a w H)| exact (fetch_tail_at a w H)]).
  destruct FA as (EA & seg & b0 & IN & X & R1 & R2 & SB & LB).
  pose proof (proj1 (forallb_forall _ _) SC seg IN) as FS. unfold fseg in FS. rewrite X in FS.
  destruct (seg_bytes seg) as [|chunk [|? ?]]; try discriminate.
  destruct (_ && _) eqn:FS0 in FS; [|discriminate]. rename FS into F2. apply andb_true_iff in FS0 as [COV EB].
  apply Z.leb_le in COV. apply Z.eqb_eq in EB.
  set (base := Z.of_N (seg_base seg)) in *. set (off := Z.to_N (bv_unsigned a - base)) in *.
  assert (HB : hex_byte_at chunk off = Some b0).
  { cbn [segment_byte_at] in SB. destruct (_ <? _)%N; [exact SB| discriminate]. }
  assert (EO : Z.of_N off = bv_unsigned a - base) by (unfold off; lia).
  assert (FP : fpos base chunk off = true).
  { apply (fscan2_sound base chunk g f 0%N F2); [lia|].
    exists (Z.to_N ((bv_unsigned a - base) / 2)).
    assert (M : (bv_unsigned a - base) mod 2 = 0) by (rewrite Zminus_mod, EA, EB; reflexivity).
    pose proof (Z_div_mod_eq_full (bv_unsigned a - base) 2) as D. lia. }
  assert (FPB : fposB base chunk off = true).
  { unfold fpos in FP. destruct (hex_byte_sys_hi chunk off b0 HB ltac:(rewrite <- LB; exact SYS)) as [HN|HN]; rewrite HN in FP; exact FP. }
  unfold fposB in FPB. rewrite HB in FPB. rewrite <- LB, SYS in FPB. cbn [Z.eqb Pos.eqb] in FPB. rename FPB into FP'.
  clear FP. rename FP' into FP.
  replace (base + Z.of_N off) with (bv_unsigned a) in FP by lia.
  unfold okP in FP. rewrite Z_to_bv_bv_unsigned in FP. apply andb_true_iff in FP as [O1 O2].
  destruct H as [H|H]; [rewrite H in O1; exact O1| rewrite H in O2; exact O2].
Qed.
End Fast.

(* [comment removed for export] *)
Definition fetch_safe_of_fscan_FRM (segs : list Segment) (g f : nat) :=
  fetch_safe_of_fscan FrmKeep.FRM.word_frm_safe safe_unless_system segs g f.
Definition fetch_safe_of_fscan_FRMC (segs : list Segment) (g f : nat) :=
  fetch_safe_of_fscan FrmKeepC.FRMC.word_frm_safe safe_unless_systemC segs g f.
End FRMF.

End FrmFastScan.
Module FrmKit.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.FPSteps.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module FRMK.

Definition frm_ok (fx : FPState) : Prop := frm_zero (@fp_csr fx).

Lemma frm_ok_fx0 : frm_ok fx0.
Proof. exact fp_frm_zero_fx0. Qed.

Lemma frm_ok_unfold fx : frm_ok fx = frm_zero (@fp_csr fx).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma frm_ok_mkFP_same fr (fx : FPState) : frm_ok fx -> frm_ok (mkFP fr (@fp_csr fx)).
Proof. intros H. exact H. Qed.
Lemma frm_ok_mkFP fr cs : frm_zero cs -> frm_ok (mkFP fr cs).
Proof. intros H. exact H. Qed.

(* [comment removed for export] *)
Lemma frm_ok_of_eq (fx fx' : FPState) :
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 -> frm_ok fx -> frm_ok fx'.
Proof. intros E H. unfold frm_ok, frm_zero in *. rewrite E. exact H. Qed.

(* [comment removed for export] *)
Definition msteps_keep_ty (segs : list Segment) : Prop :=
  forall (fx fx' : FPState) R R' pc pc' M M',
    msteps segs (@mkst fx R pc M (seg_rom segs)) (@mkst fx' R' pc' M' (seg_rom segs)) -> frm_zero (@fp_csr fx) -> frm_zero (@fp_csr fx').

(* [comment removed for export] *)
Ltac frm_solve_with L :=
  lazymatch goal with
  | |- frm_ok ?fx => change (frm_zero (@fp_csr fx)); frm_solve_with L
  | |- frm_zero (@fp_csr ?fx) =>
      first [ assumption
            | exact fp_frm_zero_fx0
            | lazymatch fx with
              | mkFP _ (@fp_csr ?f1) => change (frm_zero (@fp_csr f1)); frm_solve_with L
              | mkFP _ ?cs => cbn [fp_csr]; frm_solve_with L
              end
            | match goal with
              | MS : msteps _ (@mkst ?f0 _ _ _ _) (@mkst fx _ _ _ _) |- _ =>
                  lazymatch f0 with fx => fail | _ => idtac end;
                  apply (L _ _ _ _ _ _ _ _ MS); frm_solve_with L
              | E : Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = Z.land (Z.shiftr (bv_unsigned (@fp_csr ?f0)) 5) 7 |- _ =>
                  lazymatch f0 with fx => fail | _ => idtac end;
                  apply (frm_ok_of_eq f0 fx E); change (frm_zero (@fp_csr f0)); frm_solve_with L
              | E : _ /\ Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = Z.land (Z.shiftr (bv_unsigned (@fp_csr ?f0)) 5) 7 |- _ =>
                  lazymatch f0 with fx => fail | _ => idtac end;
                  apply (frm_ok_of_eq f0 fx (proj2 E)); change (frm_zero (@fp_csr f0)); frm_solve_with L
              | H : frm_ok fx |- _ => exact H
              end
            | fail 1 "frm_solve: no frm fact for" fx ]
  | |- frm_zero ?cs => first [ assumption | fail 1 "frm_solve: no frm fact for csr" cs ]
  | |- _ => fail "frm_solve: goal is not an frm obligation"
  end.

End FRMK.

End FrmKit.
