(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr Tac InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import MainExport MainFactsAsan.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg ABase ABytes ALayout FsKit AFake_iface ARepInit_kit.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AFake_init () := "K59OSSVerify5KrLib2AS:MainExport5pfact01C1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6eqb_eqI47Corelib4Init5Logic2eq00C56Stdlib5Arith8PeanoNat3Nat6eqb_eqK47Corelib4Init5Logic2eq01C47Corelib4Init5Logic8eq_ind_rK59OSSVerify5KrLib2AS:MainExport5pfact02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS:MainExport5pfact03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS:MainExport5pfact04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:MainExport8zexp_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:MainExport;zexp_eqb_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW:AFake_init9pfact_eqbC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I59OSSVerify5KrLib2AS:MainExport5pfact00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes4bool02K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes3nat00I59OSSVerify5KrLib2AS:MainExport4zexp00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib2AS:MainExport8pfact_okC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List7existsbC46Stdlib5Lists4List2InI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsc59OSSVerify5KrLib5AsanW:AFake_init<pfact_eqb_eqC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic5proj1K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic7f_equalC45stdpp9bitvector;definitions5bv_eqC35stdpp7tactics<f_equal_helpC47Corelib4Init9Datatypes8list_indC47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init5Logic3and01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib5AsanW4AImg5asegsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib2AS:MainExport8mfact_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<ARepInit_kit2LVC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5AsanW5ABase7alayout01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase7al_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ALayout7al_dtlsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase4al_tC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS:MainExport4zexp01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS:MainExport4zexp02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS:MainExport4zexp04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS:MainExport4zexp03C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K59OSSVerify5KrLib2AS:MainExport5mfact01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS:MainExport5mfact02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS:MainExport5mfact04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:MainExport8mwr_findC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:MainExport2zvC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC59OSSVerify5KrLib2AS:MainExport:mimg_coverC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib2AS:MainExport5zerosC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith6BinInt1Z8mul_commK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03C59OSSVerify5KrLib5AsanW;AFake_iface:afake_geomC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW;AFake_iface;afake_cellsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5FsKit5dc_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW;AFake_iface:fk_nframesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW;AFake_iface7fk_flagC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5AsanW5ABase6abkind02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW;AFake_iface8fk_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW;AFake_iface8fk_fsizeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5AsanW5ABase6ablock01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib3Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC59OSSVerify5KrLib3Lib6MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem:rw_bytes_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem?rw_cells_image0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem?rw_cells_recastC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C47Corelib5Lists7ListDef6repeatc59OSSVerify5KrLib5AsanW:AFake_initDbytes_eq_of_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5FsKit;dc_of_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5FsKit7dc_takeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5FsKit8c8_of_dcC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01c59OSSVerify5KrLib5AsanW:AFake_init:wr_at_sub'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:MainExport>mzero_rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW;AFake_iface=fk_flag_rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transc59OSSVerify5KrLib5AsanW:AFake_init:pfact_findC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:MainExport9mfact_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:MainExport:mfact_findC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib5AsanW6ABytes<rw_cells_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS=MainFactsAsan?asan_pure_factsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS:MainExport5mfact00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS=MainFactsAsan>asan_mem_factsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW5ABase7alayout00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW;AFake_iface6FAKESZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW;AFake_iface7FK_NCLSC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW5ABase6ablock00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_Z".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition pfact_eqb (f g : pfact) : bool :=
  match f, g with
  | PVar n lo hi, PVar n' lo' hi' => Nat.eqb n n' && Z.eqb lo lo' && Z.eqb hi hi'
  | PRange e lo hi, PRange e' lo' hi' => zexp_eqb e e' && Z.eqb lo lo' && Z.eqb hi hi'
  | PDisj a1 n1 a2 n2, PDisj a1' n1' a2' n2' => zexp_eqb a1 a1' && Z.eqb n1 n1' && zexp_eqb a2 a2' && Z.eqb n2 n2'
  | _, _ => false
  end.
Lemma pfact_eqb_eq : forall f g, pfact_eqb f g = true -> f = g.
Proof.
ltac2:(KReplay.run1 (kr_t_AFake_init ()) ["CANSEC1"] "p'0h01Hh12H0h21ni001nh32hii012hih42loi022loh52a1i032a1h62a2i042a2h72n1i052n1h82n2i062n2h91Xh:2X0h;1ei071eh<2n0h=2a0h>2a3h?3hi0h@3lo0hA1mhB2n3hC2X1hD2e0hE1fhF1gi081bi091pp;3p;2p;6p;4g0000j37Tg000jj2;Tg001Jj26Tg001gj2>Tg002Ej3@Tg002hR0j2?Tg003Cj2GTg003cj38Tg004=j2KTg004`j2ETg005:j6CTg005Xj35Tg006Rj44Tg007Lj4ATg008Fj23Tg009Aj3DTg00:?j2JTg00;>j6ITg00;Zj2HTg00<9R1f1R2f0R3'Jg00<YR438p=0g00=9R5?823p=2A8134p=11>23=814p==1623=814p=<g00>3R6?823p=:P6f4R7f3R8f2R9P2P3ECp=BP1g00>QP2g00?1P4P3EIp=FA8592/H3p=91023P510391228]0P9g00?MR4A7923R:f7R;'0P5A7789R</03f5R=?778R>/22]0f8R?f9R@?7?;RA/0:f:RB/;816@9RC'>RD16?2RE;@3%1D%1ERD'?P0f;RF/;716B8RG'=%1CRHf<RI?7FB/2>P3f=R>f6RJ';16I=RK'=%1KRLf?RM/;?RNf>RO/6;RP;@2%1N%1PRN'?P0f@RQ/;@#11<M?RRfARS?7QMA7B@?'2P3fBRT/;F#11<TFRUP01<231:92[RV1:231<92RW[1:89\W1G23P2n2001000000120000000XA6X26RWPV^A6^26RVP3fCRXPIPJO31:XIPWPVP3fFRYPMP8O31:YMP01;23#1A8492[RZA84231;92#1R[[A8489\[1K23P2n2001000000120000000XA4X24PZ^A4^24P3fIRZPTPJO3A84ZTP4PXfJR[=73ZfDR\?7XTR]'2X24PTA7\3Z/2]X46PSA7\X3/2]X36A7XTS,E5fHR]P7DBPZP9DBP[P3ECb0b1b:b1b9b1W:W0P2P3O2n2001000000121000000b0W9W0P2P3O2n2001000000121000000b0W0X?6X@6X<4P9P2P3O3g00?lR^A5923R_,0AP1p-0P3g00@eRAg00ABn0110800020000R`XD1/F3RaPAA7FB@RbA5789Rc;93b1W0X?6X@6W;P9P2P3O3P8P9P2P3C4Rd,0bP`X;1/F3R1PAA7>IFR`P=P7P8P9C4Re;93b1W0X86X6^X76X5^P8P9P2P3O4P8P9P2P3CARf,0bP1PAP=P7P8P9CARb=9`3b1W0X8^X6^X7^X5^P8P9P2P3O4n01109000431100102101301071021014010310510410640103105104106P3O1W0X36X46W2P9P2P3O310_;P510c3A5=78R`/22]0P?A5@?;Rg/0:PaPAA5FB@Rh?9<3b1W0X?6X@6X24P9P2P3O310g_13B8/>CRC?@E3%1C/?DP013F7/=GPHA5IFB/2`P313>J/=K13M?RK?@P2%1K/?NP013Q@#1PRA5SQMA5B@?'2P313TF#1AD\>2A8^\>PWPVP3P\P>P;O31:\>PWPVP3fGRRPQP7O31:RQP^PTA53Z]A5XTSRN'2X;^PSA5X3]/2NX46PQA5XT3/2NX36A5TSQ,E5PRP9DBP]P3DBPZP7ECb:b1b9b1b0X:UW0P2P3O2n2001000000120000000b0X9LW0P2P3O2n2001000000121000000b0W0X?6X@6XD^P9P2P3O310hdPaPAA5>IFRL?9e3b1W0X86X6^X76X5^P8P9P2P3O410hfPaPAA9Lb3b1W0X8^X6^X7^X5^P8P9P2P3O4n01109000430100102101311071021014010310510410640103105104106P3O1W0X36X46X;^P9P2P3O310d@P510e3PJP=P7P8C4RL/22]0PBPBP@P?P;C4Rh/0:P1PAPIPFPBP@C4RU?9<3b1W0X36X46X24P9P2P3O310h_PaPAA9Uc3b1W0X36X46X;^P9P2P3O310Ud13>716I8'>13F9'>Rh16B2RN;@3%1h%1N'?P013O=RN16>7'>13I8'=1<F9PMPOP>PIC4/2LP313Q;RL16MJ'>/=N1<O=13T@16S?'>RN?@L2%1N%1L'?P013XB16T@'=13S?#1P\PXPTPSC4PFPBP@P?C4'2P3fE/3I16\F'=13\F#113RORT16Y>RL;@2%1T%1L'?P013]M#11<ROPZP]PRPYC4R0PQPMPOP>C4'2P313[S#11<[SAD[S=A8^[SfMRS?D\9A8^S\PWPVP3fLRSPXP>O31:SXPWPVP3fPRVPRP=O31:VRP^PZP3fRRWfQRSPVC4P[PZP]PRC4RX'2X5^P]P[P3PSPVC4/2XX76P^PRP[PZP3PVC4/2XX6^PYP[PZP]P3C4/2XX861E50fOP9DBPVP=ECPSP3DBPWP7ECbCb1b9b1b0b:WCW0P2P3O2n2001000000121000000b0W:W0P2P3O2n2001000000121000000b0W9W0P2P3O2n2001000000121000000b0W0XB6X>^X<6X=^P8P9P2P3O410UfP1PAPOP>PIPFC4?9b3b1W0XB^X>^X<^X=^P8P9P2P3O4n01109000430100102101301071021014110310510410640103105104106P3O1W0X86X6^X76X5^P8P9P2P3O410f@P510b3PJP=P7P8CA/22]0PBPBP@P?P;CAR;/0:P1PAPIPFPBP@CAR@?9<3b1W0X36X46X24P9P2P3O310;_PaPAA9@c3b1W0X36X46X;^P9P2P3O310@dP1PAPOP>PIPFCARF?9e3b1W0XB6X>^X<6X=^P8P9P2P3O410@fP1PAA9Fb3b1W0XB^X>^X<^X=^P8P9P2P3O4n01109000430100102101301071021014010310510410640103105104106P3O1W0X8^X6^X7^X5^P8P9P2P3O4n01109000431100102101311071021014110310510410641103105104106P3O1W0XF5XE5o"). Qed.
Lemma pfact_find : forall V (l : list pfact) f,
  Forall (pfact_ok V) l -> existsb (pfact_eqb f) l = true -> pfact_ok V f.
Proof.
ltac2:(KReplay.run1 (kr_t_AFake_init ()) ["CANSEC1"] "p'0h01xi001xh13Hinh21fh31lh41Ah51Hh62HEh72Hgh81gh92HFh:1Vp;1p;3p;2p;6p;7g00A^j1<Tg00B>j17j24Tg00C9j38Tg00:?j1:j23Tg00CZR0j39Tg00D6j36Tg002hR1j22Tg00DMR2j25Tg00Dgj3=Tg00EJj3ATg003cj3;Tg00FLj3@Tg00Fnj6?Tg00;>j7>Tg00<9R3f0R4g00<Y3;p=0g00=9R5f1R6;64p=1g00?Mg00>3[%<5f2R7#7=856%:6=957#0P0p4p710R0P3\4R3%<6R8P1A9764#0f3R9f4R:?647P9P4O1#0'2X09'5[R;A6946P7P4O1#0'2X07,57A9976#0R<[f5R=?649P:P4O1#0'2X0:,5:\<A=764P6n2001000000120000000W3W2W4P;^38^23^40P4P5%:9P:P6O4114=13:4#0'2X05,55P2P5f6R2,1413=4#0'2X05f7R0/4=P4f8R3,141304#0'2P1f9R1,161336#0f;R3/41P41193133:#0f<R3?A=4A;53=P5f=R3f?R=,14fAR:/4=]1X85f>R9,13f@R1#7R0=85=114:fC/46[^05[1141fB/46[^05%7:=851[A@50=P3P9P4E?W1P2P4P7F>b7W7W1P6P4O2n2001000000120000000W5X85P6P4O2n2001000000120100000b6b5W6W9X25W3W:o"). Qed.

(* [comment removed for export] *)
Lemma bytes_eq_of_unsigned : forall (bs bs' : list byte), map bv_unsigned bs = map bv_unsigned bs' -> bs = bs'.
Proof.
ltac2:(KReplay.run1 (kr_t_AFake_init ()) ["CANSEC1"] "p'0h01Hh12H0h21eh32bsh43bs'h52b'h62b1h72b2h84bs'0h91li001lh:1nh;2H1h<2H2h=2IHh>1bi011bi021ai038bv_is_wfi04;bv_unsignedi053mapi061zp;1p;3p;2p;6p;8p;5p;4g00GIj16Tg00Gnj1DTg00HLR0j13Tg00A^R1j17Tg00Hoj1Cj22Tg003cj30Tg00IYj19Tg004`j28Tg00J9j34j2<j1BTg00;>j6:Tg00;Zj2>Tg00JYj6=Tg00K6j3ATg00KZj8;Tg00L7j5?Tg00LYj4@Tf2R2g00>3R3f1R4f0R5C@p=1A4345p=5g00M5#6#6#6#DR6#3R7#7R8P7%73R9%C6R:=174R;A17:5R<30A0824[^48R=X38P1P7%97R>917:R?=09<A08>4[P5A09??188>W0A4745917:R@909?P9%93RAP1P3p-0RBP5g00ABRCg00@eRDn10110000020020000000X29g00?1RE1262/5;RFP5E:PDf3RG=472RH908>/>5b1W0X48X57P4P5O2n10110000020020101100X88P1P7f4RI=47G917:=09<f5R<=47IRJ=084[P5A17:H=09?P9126IR?A17:G'5P1P3PBP5PDPCn10110000020020000000X29PEPAP5E:PDA08J>/>5b1W0f7RJf6R>547917:=09@P9P9P1P3P9P5P9^98P1P7P9P5PA1264PGP5O1'5n10110000020020102100X98p?1000105f8RAO1P5n10110000020020106100X29126AA17:JR@'5PFP5E=A09@;P9P3P1P3P3P5P0P6P3f:R0P4n101101000120104103P4n10110000020020106100X29f9,26R1A17:A'5126GRAA17:2'5P4E=A031A1260=03?A17:0A17:I509P8P8f<R9,<71<7>f;P<P7P8\8R:%B7R?P?P9P>P:\7/8?g00MZR?%35R:%34R>g002h%32?04512G212G4503R9[12241225503%3G?024[R3%3I?0G2\9AA245P5n2001000000120000000W7W6W:P3^7>^6:^:?P5P6f=PJP2O4b0G;P0P<P5O2G;W<W;P5O1b1P5O1b1W0X48X57P4P5O2n10110000020021101100X88X==X38X>7P5D?W3o"). Qed.

Lemma wr_at_sub' : forall m a n a' n', wr_at asegs m a n -> 0 <= a -> a <= a' -> a' + n' <= a + n -> wr_at asegs m a' n'.
Proof.
ltac2:(KReplay.run1 (kr_t_AFake_init ()) ["CANSEC1"] "h04__x1h14__x2h24__x3h31ih47__arithh54__ffh68__varmaph75__with84__x4h91Hh:4__x5h;2H0h<2H1h=2H2h>2Hih?2W1h@2W2hA2W3hB1ahC2a'hD1mhE1nhF2n'hG1zp;1p;4p;2p;3p;6p;7p;8g00GIj1<Tg00Gnj1PTg00HLj1MTg00N8j1YTg00NZj4ITg00OLj1NTg00Ojj2_Tg00PGj29Tg002hR0j22Tg00Pcj20Tg00Q@j1:Tg00Qoj1QTg003cj33Tg00RQj1=Tg00Rjj24Tg00SFj1ETg00Sej2ATg00TNj3@Tg00U7j2HTg00IYj1^Tg00J9j3GTg00A^j1]Tg00Ucj2BTg00VAj1\Tg00V_j1[Tg00W=j1ZTg00Whj2?Tg00XKj2JTg00Xnj2XTg004`j2WTg00YPj2VTg00Z<j3UTg00Z[j4TTg00[Mj1STg00\2j3fTg00\Uj3RTg00]8j4CTg00]cj2DTg00;>j6eTg00^@j4LTg00^[j3dTg00_Xj4cTg00`6j7OTg00`Zj8`Tg00a>j3aTg00aaj7bTg00bER1f0R2'4p=5f2R3f1R4'0/42p=1g00bcR5?d42p=>g00>3R6P3P4P2Ccp=;P3g00cXR7g00d7R8P8g00dWR9P6P4g00e7P2CCg00e^R:FOp=6f3R;P7P8P8P9P3P4P2G`p=8Aa642p=7P4P7P8P8P9P2P:FOp=FP3P7P8P8P9P4P2Fbp=Kg00M5R7#<R:#<R<#<R=#<#<#<R>#PR?#M%P=#MR=#YR@[P5f4RAP;P3CIP0%5A%N:RB%N>'_R>91A;%52RC192A'2f7RDf6RE/04#:'>%Q=R=53@#=[^36'2f5RF#514EA10DERG91FAP5f9RHPEPFCI[[[P2%5E14G>192D,2Cf:RG10H4#:'>=3@=#=[^36'2P0f8R0?1D>1920,2Cf;RD10G4#:'>=3@=#=[^36%5H14G010DG91H0P5f=R5PGPHCI[[[P2A1GH>192D,2Cf>RG1054#:'>=3@=#=[^36f<RH#5145D10G591HD%55A15H>RH1925,2CRCfBRDf?R0/04RI#:'>=3@=#=[^36RJ'2g00f>RKg00fjRL#ERM#ERN,A6RO1A6M1A6LRL5@6RM5@6g00gIRP'H%^KRQ3GRR%]KRS1B63RT%\6RU7;4%[6RV%Z6RW1?6:RX1?67RY56WRZ%Q8R8PW1J61R[=6WXP8A6W[YC8C81XW9R9P2P3g00<9R\g00<YR]'W1V23=3\]dAU614CTR1b5b6b7X06X161442%53R]P][[^06^16P2f@R\PGP3P;O4b4PHPJPRPS1B6A?;3URR1B6;RJ7;4PVPW17YXRH%S7,?6R71?6<R<'7R^56WP8PW1J6B=f6?R?96W^P8A6WH?C8C8P9P1b5b6b7X06X16X26X86103;R?9124A1;A>14?>[[^06^16^26^86P2P0P\P5PGP4PFO6b4PQPSA;T4JPVP6AR6XY/77,7Yg00h517X7CC,FWP9P1b5b6b7X06X16X261D42/03,021043536^06^16^26P2P3P\PDO3b4fARJ1D0J/04'0=36IP61D\D/03RI,0DfD%:2'>=3@=#=XG6PEPI%ENRN,A6A@6OL5@6/HP%EN,A6=@6M/HP=GKQ5GKPS1B6F?;;U9;R4PVPWA6W[7P6P7g00h\RV%S:,?6R:CC,FW5KWP8PW17Y:17X<56WP8PWPZP8AR6YX/77R796W[P6P7PVP<CC,FW5KWC8C8C8P9P1b5b6b7X06X16X26X86X:6193A,2]103A914F14;31D;A/0FR]#519]E'2[[[^06^16^26^86^:6P2P\PDP;fCPJP3PAPFO8b4O210\3P2Eeb9X>CX36CLCLW=W<W;WAW@P4P2O2n2001000000121000000W9W?P4P2O2n2001000000121000000W9XF6XC6XE6XB6WDo"). Qed.

End CANSEC1.
Local Ltac mf V m HM f H := pose proof (mfact_find asegs V m _ f HM ltac:(vm_compute; reflexivity)) as H; cbn [mfact_ok zv cellw] in H.
Local Ltac pf V HP f H := pose proof (pfact_find V _ f HP ltac:(vm_compute; reflexivity)) as H; cbn [pfact_ok zv] in H.

Section CANSEC2. Context {rc : runConstT}.
Theorem afake_init : forall (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem),
  Forall (mfact_ok asegs V m) asan_mem_facts ->
  Forall (pfact_ok V) asan_pure_facts ->
  32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP ->      (* [comment removed for export] *)
  AFAKE (mkALayout (LV V) w U) [] m.
Proof.
  intros V w U m HM HP HAT.
  set (L := mkALayout (LV V) w U).
  assert (EF : al_fake L = 4096 * V 377%nat) by reflexivity.
  assert (ED : al_dtls L = 4096 * V 310%nat) by reflexivity.
  assert (ET : al_t L = 4096 * V 227%nat) by reflexivity.
  pf V HP (PVar 377 1549 34359733495) P393. pf V HP (PVar 310 1 34359736319) P310. pf V HP (PVar 227 1 34359736319) P227.
  pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 377)) 11571200 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW393.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 377)) 11571200 (ZLit 2147446784) 17592186048512) DB393.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW310.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 2147446784) 17592186048512) DB310.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 65536) 6279168) DI310.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW227.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZLit 2147446784) 17592186048512) DB227.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZLit 65536) 6279168) DI227.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 377)) 11571200) D1.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 310)) 4096) D2.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 377)) 11571200) D3.
  mf V m HM (MCell (ZLit 6203656) 8 (ZLit 6203696)) C40.
  mf V m HM (MCell (ZLit 6203664) 8 (ZMul (ZLit 4096) (ZV 377))) C48.
  mf V m HM (MCell (ZLit 6203672) 8 (ZMul (ZLit 4096) (ZV 310))) C70.
  mf V m HM (MCell (ZLit 6203704) 8 (ZLit 6205712)) C98.
  mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 310)) (ZLit 24)) 8 (ZLit 6203664)) CD24.
  mf V m HM (MCell (ZLit 1348912) 8 (ZLit 256)) CCF.
  mf V m HM (MCell (ZLit 1340440) 4 (ZLit 0)) CVERB.
  mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 48)) 8 (ZLit 6205512)) CT48.
  mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 56)) 8 (ZLit 6205732)) CT56.
  mf V m HM (MZeroC (ZMul (ZLit 4096) (ZV 377)) 88) HINTS.
  mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 377)) (ZLit 88)) 8 (ZLit 20)) CLOG.
  mf V m HM (MZero (ZAdd (ZMul (ZLit 4096) (ZV 377)) (ZLit 96)) 11571104) Z96.
  pose proof (mwr_find asegs V m _ (ZMul (ZLit 4096) (ZV 377)) 11571200 HM ltac:(vm_compute; reflexivity)) as WFK. cbn [zv] in WFK.
  mf V m HM (MZero (ZAdd (ZMul (ZLit 512) (ZV 377)) (ZLit 2147450880)) 1446400) ZSH.
  pose proof (mwr_find asegs V m _ (ZAdd (ZMul (ZLit 512) (ZV 377)) (ZLit 2147450880)) 1446400 HM ltac:(vm_compute; reflexivity)) as WSH. cbn [zv] in WSH.
  pose proof (mimg_cover asegs V m _ 0x10000 0xb15e8 HM ltac:(vm_compute; reflexivity)) as IMG.
  rewrite <- EF in *. rewrite <- ED in *. rewrite <- ET in *.
  assert (SHF : shad (al_fake L) = 512 * V 377%nat + 2147450880).
  { unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2, EF by lia. change (2^3) with 8.
    replace (4096 * V 377%nat) with ((512 * V 377%nat) * 8) by lia. rewrite Z.div_mul by lia. lia. }
  assert (SHL : shlen FAKESZ = 1446400) by reflexivity.
  assert (G : afake_geom L).
  { unfold afake_geom, FAKESZ, ablk, sclr, iclr, KLS, AIMG_LO, AIMG_HI. rewrite EF, ED, ET in *.
    repeat lazymatch goal with |- _ /\ _ => split end;
      first [ rewrite Z.mul_comm; apply Z_mod_mult
            | clear - P393 P0 P6 P10 DW393 DB393 HAT; lia
            | clear - P310 P0 P6 P10 DW310 DB310 DI310 HAT; lia
            | clear - P227 P0 P6 P10 DW227 DB227 DI227 HAT; lia
            | clear - D1 D2 D3; lia ]. }
  clearbody L.
  split; [exact G|].
  split.
  { unfold afake_cells. split.
    { eapply rw_cells_recast; [apply (rw_cells_image0 asegs m 0xb14e0 (le8 (Z_to_bv 64 0xa964c)));
        [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply IMG; rewrite length_le8 in Ha; lia
        | vm_compute; reflexivity | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity]. }
    split; [apply (proj2 (rw_cells_app asegs m 6203656 [C8 _] [C8 _])); split; [exact C40| cbn; exact C48]|].
    split; [exact C70|]. split; [exact C98|]. split; [exact CD24|]. split.
    { assert (CF8 : rw_cells asegs m 1348912 ([C1 (Z_to_bv 8 0)] ++ ([C1 (Z_to_bv 8 1)] ++ [CB 6 (repeat (Z_to_bv 8 0) 6)]))).
      { eapply rw_cells_recast; [exact CCF| cbn; repeat split; reflexivity| apply bytes_eq_of_unsigned; vm_compute; reflexivity| reflexivity]. }
      apply (proj1 (rw_cells_app asegs m _ _ _)) in CF8 as [_ CF8]. cbn [cells_size csize Nat.add Z.of_nat Z.add Pos.of_succ_nat] in CF8.
      apply (proj1 (rw_cells_app asegs m _ _ _)) in CF8 as [CF8 _]. exact CF8. }
    split; [exact CVERB|].
    apply (dc_of_cells m (al_t L + 48) [C8 (Z_to_bv 64 6205512); C8 (Z_to_bv 64 6205732)]).
    apply (proj2 (rw_cells_app asegs m _ [C8 _] [C8 _])). split; [exact CT48| cbn [cells_size csize Nat.add]].
    replace (al_t L + 48 + Z.of_nat 8) with (al_t L + 56) by lia. exact CT56. }
  split.
  {
    pose proof (dc_of_cells m _ _ HINTS) as D88. cbn [cells_size csize Nat.add] in D88. change (Z.of_nat (Z.to_nat 88)) with 88 in D88.
    destruct (dc_take m _ 88 8 D88 ltac:(lia)) as [D0 R0]. destruct (c8_of_dc m _ D0) as [h0 H0].
    destruct (dc_take m _ (88 - 8) 8 R0 ltac:(lia)) as [D1' R1]. destruct (c8_of_dc m _ D1') as [h1 H1].
    destruct (dc_take m _ (88 - 8 - 8) 8 R1 ltac:(lia)) as [D2' R2]. destruct (c8_of_dc m _ D2') as [h2 H2].
    destruct (dc_take m _ (88 - 8 - 8 - 8) 64 R2 ltac:(lia)) as [[hs HS] _]. change (Z.to_nat 64) with 64%nat in HS.
    exists h0, h1, h2, hs.
    apply (proj2 (rw_cells_app asegs m _ [C8 h0] _)). split; [exact H0| cbn [cells_size csize Nat.add]].
    apply (proj2 (rw_cells_app asegs m _ [C8 h1] _)). split; [replace (al_fake L + Z.of_nat 8) with (al_fake L + 8) by lia; exact H1| cbn [cells_size csize Nat.add]].
    apply (proj2 (rw_cells_app asegs m _ [C8 h2] _)). split; [replace (al_fake L + Z.of_nat 8 + Z.of_nat 8) with (al_fake L + 8 + 8) by lia; exact H2| cbn [cells_size csize Nat.add]].
    replace (al_fake L + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (al_fake L + 8 + 8 + 8) by lia. exact HS. }
  split; [exact CLOG|].
  split.
  { eapply rw_cells_recast; [apply (mzero_rw_cells asegs m (al_fake L + 96) 1); [intros i Hi; apply Z96; lia| eapply wr_at_sub'; [exact WFK| lia| lia| lia]| lia]
      | cbn; split; [reflexivity| exact I] | reflexivity | reflexivity]. }
  split.
  { exists (zeros (FAKESZ - 4096)). apply mzero_rw_cells; [| eapply wr_at_sub'; [exact WFK| lia| lia| unfold FAKESZ; lia]| unfold FAKESZ; lia].
    intros i Hi. replace (al_fake L + 4096 + i) with (al_fake L + 96 + (4000 + i)) by lia. apply Z96. unfold FAKESZ in Hi. lia. }
  split.
  { rewrite SHF, SHL. exists (zeros 1446400). apply mzero_rw_cells; [exact ZSH| exact WSH| lia]. }
  split.
  - intros c pos b Hc Hp Hb NZ. exfalso. apply NZ. pose proof (fk_flag_range L c pos Hc Hp) as R.
    specialize (Z96 (fk_flag L c pos - (al_fake L + 96)) ltac:(lia)). replace (al_fake L + 96 + (fk_flag L c pos - (al_fake L + 96))) with (fk_flag L c pos) in Z96 by lia.
    congruence.
  - intros c F n Hin. destruct Hin.
Qed.
End CANSEC2.
