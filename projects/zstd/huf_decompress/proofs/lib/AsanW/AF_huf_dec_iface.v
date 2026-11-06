(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
(* [comment removed for export] *)
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require HufHarness.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import Stdio_kit AH_huf_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_dec_iface () := "C46Stdlib5Lists4List2hdK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c59OSSVerify5KrLib5AsanW@AF_huf_dec_iface:huf_dt_okAC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4Spec=HufPure_HufX1;x1_table_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib5Plain<RF_huf_iface8x1_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec=HufPure_HufX2;x2_table_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain<RF_huf_iface8x2_bytesC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00I47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list02c59OSSVerify5KrLib5AsanW@AF_huf_dec_iface7x1_tabAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW@AF_huf_dec_iface7x2_tabAC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or01C47Corelib4Init5Logic8eq_ind_rK47Corelib4Init5Logic2or02I47Corelib4Init5Logic2eq00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef6firstnC59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib5AsanW4AImg5asegsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I59OSSVerify5KrLib4Spec=HufPure_HufX16deltX100C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec=HufPure_HufX26deltX200C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib5AsanW=AMalloc_iface5AHEAPC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5AsanW5ABase6abkind01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5AsanW5ABase6ablock01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=AMalloc_iface8AI_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase<ablock_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~I35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupK47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec8AsanCtrl:chunk_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl>chunk_user_begC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase4ablkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase=ablock_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib6ZArith4ZdivAZ_div_mod_eq_fullC47Corelib4Init5Logic6eq_symI46Stdlib;setoid_ring<Ring_polynom5PExpr00I47Corelib4Init9Datatypes4prod00K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr07I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C46Stdlib6ZArith4Zdiv:Z_mod_multC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib3Lib8RunConst:ATOP_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow:unpoisonedC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib5AsanW9AProg_kitAablock_unpoisonedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib4Spec8AsanCtrl:is_primaryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_liveC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterI59OSSVerify5KrLib5AsanW5ABase7alayout00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW5ABase6ablock00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase7AREQMAXC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC59OSSVerify5KrLib5AsanW5ABase7AIMG_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase3KLSC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01K47Corelib4Init5Logic4True01I46Stdlib;setoid_ring<Ring_polynom3Mon00C59OSSVerify5KrLib3Lib8RunConst8ATOP_MINC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst8ATOP_MAXC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapK59OSSVerify5KrLib5AsanW5ABase6abkind02C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib5AsanW5ABase7ab_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase7ab_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<AH_huf_iface<DTABLE_BYTESC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C59OSSVerify5KrLib5AsanW<AH_huf_iface7src_inAC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9Stdio_kit6rcleanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9Stdio_kit4r_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9Stdio_kit4r_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9Stdio_kit5r_rloC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase6al_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW>AHarness_iface<harness_invAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9Stdio_kit4rrngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<AH_huf_iface=huf_dec_postAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF4evtFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW@AF_huf_dec_iface>dec4_int_stmtAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<AH_huf_iface=huf_dec_stmtAC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffI59OSSVerify5KrLib5AsanW9Stdio_kit6region00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<AH_huf_iface?HUF_DEC_STACK_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase3ATPC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".

Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AHUF_DX1_1X : Z := 0x85154.     (* [comment removed for export] *)
Definition AHUF_DX2_1X : Z := 0x83bb8.     (* [comment removed for export] *)
Definition AHUF_DX1_4X : Z := 0x8ed88.     (* [comment removed for export] *)
Definition AHUF_DX2_4X : Z := 0x85bcc.     (* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition huf_dt_okA (m : amem) (DT mtl : Z) : Prop :=
  exists (tt tl : Z),
    bytes_at asegs m DT [Z_to_bv 8 mtl; Z_to_bv 8 tt; Z_to_bv 8 tl; Z_to_bv 8 mtl]
    /\ ((tt = 0 /\ exists cells : list deltX1, zlen cells = 2^(mtl+1) /\ x1_table_ok cells tl /\ tl <= mtl + 1
                                               /\ bytes_at asegs m (DT + 4) (firstn (Z.to_nat (2 * 2^tl)) (x1_bytes cells)))
        \/ (tt = 1 /\ exists cells : list deltX2, zlen cells = 2^mtl /\ x2_table_ok cells tl /\ tl <= mtl
                                               /\ bytes_at asegs m (DT + 4) (firstn (Z.to_nat (4 * 2^tl)) (x2_bytes cells)))).

Definition x1_tabA (m : amem) (DT mtl : Z) : Prop :=
  exists (tl : Z) (cells : list deltX1),
    bytes_at asegs m DT [Z_to_bv 8 mtl; Z_to_bv 8 0; Z_to_bv 8 tl; Z_to_bv 8 mtl]
    /\ zlen cells = 2^(mtl+1) /\ x1_table_ok cells tl /\ tl <= mtl + 1
    /\ bytes_at asegs m (DT + 4) (firstn (Z.to_nat (2 * 2^tl)) (x1_bytes cells)).

Definition x2_tabA (m : amem) (DT mtl : Z) : Prop :=
  exists (tl : Z) (cells : list deltX2),
    bytes_at asegs m DT [Z_to_bv 8 mtl; Z_to_bv 8 1; Z_to_bv 8 tl; Z_to_bv 8 mtl]
    /\ zlen cells = 2^mtl /\ x2_table_ok cells tl /\ tl <= mtl
    /\ bytes_at asegs m (DT + 4) (firstn (Z.to_nat (4 * 2^tl)) (x2_bytes cells)).

Lemma huf_dt_okA_cases : forall m DT mtl, huf_dt_okA m DT mtl -> x1_tabA m DT mtl \/ x2_tabA m DT mtl.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_dec_iface ()) ["CANSEC1"] "p'0h05cellsh11Hh22tlh32DBh42tth51Bh61Lh71Th82TLh92DTh:1mh;3mtli001xp%0p;1p;3p;2p;4p;7p-1p10000p4p710p8g000Gj1HTg000lj1\Tg001Jj1YTg001mj1`Tg002Oj3fTg003Uj23Tg004;j1aTg004[j1XTg005;j1TTg005Yj20Tg0066j2KTg0079j24Tg007Vj2RTg0083j1ATg0093j2LTg00:6j1BTg00;6R0j2GTg00;PR1j25Tg00;jj26Tg00<Fj37Tg00<fj3^Tg00=ij3]Tg00>lR2j21Tg00?Gj4ETg00?bj4STg00@<j3eTg00@Vj7[Tg00A4j3dTg00ANj3?Tg00Ahj2cTg00BHj1bTg00Bhj1UTg00CHj3VTg00Cgj4OTf4R3f3R4f2R5f1R6f0R73737p=8g00D\R8g00E:R97?7p=<1c67#bp=D%U6=V57p=Zg00EXR:P5P6P7COp=9f6R;f5R</435?81656/17,14'1p=C1567,15p=:A?867p=QP:f7R=P;A745697<3CO/17p=@A^<34A]567'Gp=;A?8341167,15'1p=WA?856/17p=JP:P3P4A7567COp=FP:P<P31R56#U=V47COp=214;<9?8=1K341656/17'1'1p=>1L341656/17'1p=I14569?84/17p=P16=;P:P<P31R56#U=V47CO'1p==A?8341L56/17'1p=M14679?85p=N1K341656/17'1p=_g00FMR:#HR>#HR?#HR@#H#H#H#\#Y%\@R@#YRA#`[Af567P1P8P<P3PA13@4RBPA13@6RCPA13@7RDPAPB%aARED8%<6RFg00G2RG#XRH1DG7RI%T>R>%T:R:,03RJ1K76RKP6PJ%T?R?,0<RJ14>6RL,R>%A7RM5ZARN59;FCX0H3:1Q6:ROg00H2RP#XRQ1DP7RRP>P31L76RSP6P31R?L%B7RL5ZART99;JFCX0Q3:'GG@X28,58X48P3P4P5P3P4P5E;P7P=P;PA13@<RJPAPCPAPDPAPJPED8PIP>10;:RUPKP6PUf8RU10=?RV;9NFCX0H9:FHPR14>;RFPS166;A9UVTDWX0Q9:OQ'GG@X28,58P1P8PUP=PA13@;ROPA13@5PAPDPAPOPED8%<5PIP>10=:ROPKP6POf9RO10U?RV;9NFCX0H7:HPR14>=RWPS166=A9OVTDWX0Q,5Q9J5:'GG@X28PUP=P;PUP=P;E;P7f:RVPOPA13@URXPA13@3PAPDPAPXPED8%<3PIP>10O:RXPKP6PXf;RX10V?RY;9NFCX0H7:HPRP>POPSP6POA9XYTFCX0Q,5Q9J3:'GG@P2PXPVPA13@ORYPAPJPAPCA7AYED8DF%<<PIP>10V:RYP7P5P5PYf<RY10X?RJPAP>14>5RZPME2G>X0H7:HPRP>PVP7P5P5PVPYPJPAP?PZPLE2DICPX0Q,5Q9J<:'GPYPXPVPYPXPVE;P7f=RZPYPA13@XRJPA13@=PAPBA7AJED8DF%<UPIP>10Z:RBP7P<P<PBf?RBf>R5/0?R[PAP>14><R\PME2G>X0H7:HPR14>ZR]P7P<P<PZPBP[PAP?P\PLG=DMX0Q,5Q9JU:'GP0%<OPIP>105:R0P7P;P;P0f@R010B?R\PAP>PFPME2G>X0H7:HPRP>P5P7P;P;P5P0P\PAP?PFPLE2DICPX0Q,5Q9JO:P0PBP5P0PBP5E;P7%<VPIP>10B:RFP7P=P=PFfARF100?S00PAP>PWPME2G>X0H7:HP2%<XPIP>100:R\P7PUPUP\fBR\10F?S01PAP>14>US02PME2G>X0H,5HP\PFP0P\PFP0E;S03P7%<ZP8P9fER[fDR^PAfCR_,3@R`PAPDPAPJA7A`ED8DFR`PIP>10[:RJP7PZPZPJfGRJfFRD/0?S04PAP>P]PME2G>X0HRa,5HPJPDP[PJPDP[E;Rb[]3X48P^P_PA13@\Rc13@9R9PA13@VPAPcPED8Rd57ADFPIP>10^:ReP7PYPYPePD10[?S05PAP>14>YS06PME2G>X0H,5HP1PHPaPbP7PIP>10J:RaP7PBPBPafIRafHRe/0?S07PAP>14>BRfPME2G>P21DG610e:Rg7N>P6P0P0PgfJRg10a?S08PAP>14>0Rh%A6E2D_fKRiPgPaPiPgPaE;S09P71DG410g:7N>P3P_P_10i:fMRjfLRk/0?S0:PAP>14>_S0;%A3E2D_P21K<^P^10k:fNRl10j?S0<PAP>14>^Rm%A<G=fORnPlPjPnPlPjE;S0=P71K=DPJ10n:fQRofPRp/0?S0>PAP>14>JRq%AUG=P210p:,6efRRr10o?S0?PAP>14>eRs%AOE2fSRtPrPoPtPrPoE;S0@P710r:,6gfURtfTRu/0?S0APAP>14>iS0B%AYE2fVRv?^tuRwA]vtuRxP8fXRyfWRzPA13@vR{PAP9PAPCPAP{PED8S0CPIP>10v:RCPKP6PC10z?RC=9yNFCG@X0H,5HX28PkPHPzPvPA13@tRNPAP9PA13@jPAPNPED8S0DPIP>10t:RIP7PjPjPIPz10v?S0EPAP>14>jS0FPME2G>G@X0HPZPvPtPA13@uRMPA13@kPAPMPED8RE97A9DF1DGZ10u:RG7N>R91KZkRI16kGRGPv10t?S0GPAP>14>kRK%AZE2R|'1R}'1R~'1PFP9P~POPIP}P<PGP|P6P7CECECECECSCS3eW5W8P6P7O2n2001000000121000000W1W7P6P7O2n2001000000121000000W1W6P6P7O2n2001000000121000000W1X0HP6P7O2n2001000000121100000W1W3P5P7P;F[W1P6P7O2n2001000000121000000W1P7O1PRPfP7P=P=PBPFQ00PAP?PWPLG=DMX0Q,5Q9JV:P21QX:PRPhP7PUPUP0P\Q01PAP?Q02PLG=DMX0Q,5QQ03P71QZ:P8P:PRP>P[P7PZPZP[PJQ04PAP?P]PLE2DICPX0QR],5QPb[^3`X48P^P_PAPc13@:R:=7AdDFPRPmP7PYPYP^PDQ05PAP?Q06PLG=DMX0Q,5QP1PQP]PbP7PRPqP7PBPBPJPaQ07PAP?PfPLG=DMP21DP6/QsP6P0P0PePgQ08PAP?Ph%B6E2DIQ09P71DP4?N>gP3P_P_PiPjQ0:PAP?Q0;%B3E2DIP21L<^P^PkPlQ0<PAP?Pm%B<G=Q0=P71L=DPJPnPoQ0>PAP?Pq%BUG=P216epPrQ0?PAP?Ps%BOE2Q0@P716grPtQ0APAP?Q0B%BYE2P8PyPzPAP{PAP:Q0CPRP>PvPSP6PvA9yCTFCG@X0Q,5QX28PkPQPzPvPAPNPAP:Q0DPRP>PtP7PjPjPtPzQ0EPAP?Q0FPLE2DICPG@X0QPZPvPtPAPMA7A:EDF1DPZ?N>uR>1LZkRP16kuRuPvQ0GPAP?PK%BZE2RZ'1RK'1R?'1PFP>P?POPPPKP<PuPZP6P7CECECECECSCS9dwxW5W8P6P7O2n2001000000121000000W1W7P6P7O2n2001000000121000000W1W6P6P7O2n2001000000121000000W1X0QP6P7O2n2001000000121100000W1W3P5P7P;F[W1P6P7O2n2001000000121000000W1P7O1n200100000021100011000W1W3P6P7O2n2001000000121000000W1X28P6P7O2n2011000000121100000W1X48P6P7O2n2011000000121100000W1X;8X98W:o"). Qed.

Section Stmts.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable rng_fs : alayout -> footprint -> Prop.    (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma hb_unpoisoned : forall L RNG st LB m p A n, AHEAP AI L RNG st LB m -> In (HB p A n) LB ->
    unpoisoned m A (A + n) /\ A mod 16 = 0 /\ 1 <= n /\ ablk A (A + n) /\ A + n <= ATOP
    /\ rng RNG A n /\ rng RNG (shad A) (shlen (n + 7)) /\ wr_at asegs m A n.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_dec_iface ()) ["CANSEC1"; "Stmts"] "h03RHIh13RLOh22chh31Hh44__p1h54__x1h67__arithh74__ffh88__varmaph95__with:2R1h;1Ah<4__x2h=4__x3h>1zh?2A0h@2A8hA2AHhB2AThC2HNhD3HinhE1LhF2LBhG2R2hH2R3hI2R4hJ2RAhK3RNGhL2RShM3SHBhN2WRhO2_HhP1ahQ7fv_listhR8hyp_listhS3lmphT1mhU1nhV1phW2stp&0p;1p;7p;3p;<p;4p;2p;6p;8p;:g00I2R0p4p70g00IiR1p4p710p8g004[j1XTg000Gj12Tg000lj1oTg001Jj1zTg001mj1xTg00J@k70RTg00K>k10JTg00L7k30DTP1k30>Tg00M0m<07Tg005;j1@Tg00N1j3YTg00Nnj1>Tg00Ofk40XTg00P:k40WTg00PSk20QTg00Q5k10PTg00R2k10ITg005YR1j21Tg00S3R2k20<Tg00SPj1[Tg00TIj3;Tg00U<j1{Tg00V2j3_Tg00;jj23Tg00Vgj3gTg00Wek10VTg00Xcj1CTg004;j1fTg00YHj2tTg00Yfk10OTg00ZDk10NTg00Zoj2QTg00[Rj2eTg00\5k10HTg00\Wk20GTg00]9k20FTg00]Sk20ETg00ANj3GTg00^?k30CTg00^^k40BTg00_Pj2bTg007VR3j2HTg00_mj2ZTg00`Mk20ATg00a4k40@Tg00aPk10?Tg00b:j2`Tg00<Fj3mTg00bZj2aTg00cDk20=Tg00cnj3cTg00dXk10:Tg00e@k408Tg00efk709Tg00fUk206Tg00g5j6lTg00gQk105Tg00@Vj6nTg00h2k104Tg00hnj3pTg00>lR4j20Tg00iij1jTg00jHj2dTg00k1j3qTg00kZk203Tg00lFk102Tg00ldj4rTg00mBk301Tg00mek30KTg0079k200Tg00nHk80LTg00oNk30MTg00?Gj4ITg00oij1~Tg010fj1}Tg011_j6|Tg0123j4VTg00;Pj2RTg012ek40STg013Pk70TTg0144k60UTg014Xk70]Tg015<k80\Tg015`m:0[Tg016Qm<0ZTf0R5#2#2p=Tf3R6f2R7'3f1R8/35'0p=E%C5#Cp=y1185#[p=Ag017>R9%~5g017^3Gp=8g00D\R:?G85p=5AG:78/05p=9f6R;P0g018>R<f5R=f4R>P6%}7E|;G8/05p=6%25#2#2#2p=P1Z85g00E:R?5G:p=<A;=>6g00EXR@P7P8P5CV'0p=7f7RA13=>1167/38/05'0,0;'0p=:1R:5p=4AgA;=P@P>P6P7CV1R<81R:5'0'0'0p==A;;=>A;678/05'0p=M1085,07p=K%>61178#[5;>/05p=\%>=11>6#[5;;P@P7P8P5CV'0p=D13=>A;678/05'0p=O13=>A_678/05'0p=FAp=>61Z78=G:?/05'0p=B13?5p=NP@P7P8P5CVp=^1378/05p=W1167/38/05p>0Y1178/35p=i%>8=;75p=hP@P>P6P7CV1R<8/05'0p=w1R<81R:5'0p=v%C5#C#C#Cp=?%25#2#2#2#2#2#2#2p=S1385,07p=uP:P8g0199P5H0Sp=JP8g019`R@g01:?RBPBg01:_RCP5g01;?K0Tp=LP8P@PBPBPCP5J0Up=sP7P@PBPBPCP8P5K0]p=]P6P@PBPBPCP7P8P5L0\p=UP:P?P8P1P3P2g01;_R@g01<<RDg01<YREP5N:0[p>0;P:P?P7P1P3P2P@PDPEg01=:REP8P5N<0Zp=kg01=ig01>cg01?\g01@WR@#Xg00FMR2#2R3#2R1#2RF#2RG#TRH#oRI#z%oF#z#x[p,2rcRJp,2AIRKPAP;P=P>P6K0R&0J6@0D78>0>@=PJPKf9RKf8R@PAP;P=P>P6P7P8P5N<07%@2RLP7P7g01APRMCEAYJ67P@P6P7P@%>6%y2RN#@RO,A7P=P6P7P=P6P7%x<RPg01BHRQg01BfRRg01C?RSP<H0XRTPQPRPSP<H0WRSP=P@20Q<5RR&0P5RQ%86&0I8RU,5=[796F6X2<%TH#PRV#@RW,<8RX1<5WRW%@HRH,18RYP=11=>RZPHP5f:R[%>8R\20<58#[R]PAP\P]E7G:X0:#4X1:G=FM3KP4PLP6P6PMCEAYJ>6A;K>6PKP>P6POP;P>P6P;P>P6PPPTPSP;PKPR%8>15;U[99Q>F6X2<PXPWPYP;11;=PHP5f;R^P\P]P@P\P]E7G:X0:#4X1:G=D\3KPAP=PZP=%@GRGPLP>PJP=PZPZ%{JRZP[P=P>P[P=P>POPAP=P>FDEOEFEBP5PLP=P=PMCEAYJA;f<R_?;A;P_PAP;POPKPAP;PKPAP;PPPTPSPKP_PR%8A15KU[99QAF6X2<PXPWPYPK11K@R;PHP5f>R`P\P]P^P\P]E7G:X0:#4X1:G=D\3KP4AYJ@Af=RaP@PAPa%>@1AAOP[P@PAP[P@PAPPPTPSP[PaPR%8@15[U[99Q@F6X2<PXPWPYP[11[KPHP5f?RAP\P]P_P\P]E7G:X0:#4X1:G=FMP^PKP;PKPGPLP@PJPKP;P;PZP`PKP@P`PKP@POP^PKP@FDEOEFEBP5AYJ[KP411^[RK9_J^%N[13KZ1<^G3KfARKP_P^PK%>_1A^OP`P_P^P`P_P^PPPTPSP`PKPR%8_15`U[99Q_F6X2<PXPWPYP`11`aR^PHP5fCR[P\P]f@R;P\P]E7G:X0:#4X1:G=FMPAPa11a_RbPaPGA_JabRc13bZfBRbPaP_Pb%>a1A_OA^Aa_FM3K9WL_EB[P5%Na13^Z1<`G3KP4%N`PAP`PZ1<AGH0YfER`P;PAP`%>;1AAOPbP;PAPbP;PAPPPTPSPbP`PR%8;15bU[99Q;F6X2<PXPWPYPb11bKRAPHP5fGR^P\P]fDRaP\P]E7G:X0:#4X1:G=FMP[PK11K;RdPKPGPLP;PJPKPdPdPZfFRdPKP;PdPKP;POP[PKP;FDEOEFEB[P5%N;1<bG9WAZP4Ai[bZ1<[GfIRbPaP[Pb%>a1A[OPdPaP[PdPaP[PPPTPSPdPbPR%8a15dU[99QaF6X2<PXPWPYPd11d`PHP5fKRAP\P]fHRKP\P]E7G:X0:#4X1:G=FMP^P`11`aReP`PGPLPaPJP`Pe13eZRefJRf?;`aPfP`PaPOP^P`PaFD3KEFEB[P51<dGfLRgP^PdPg%>^1AdOPbP^PdPbP^PdPPPTPSPbPgPR%8^15bU[99Q^F6X2<PXPWPYPb11bKRdPHP5fNRhP\P]PAP\P]E7G:X0:#4X1:G=FMP4fMRi?;K^PiPKP^POPfPKP^PfPKP^PPPTPSPfPiPR%8K15fU[99QKF6X2<PXPWPYPf11fbPHP5fORjP\P]PgP\P]E7G:X0:#4X1:G=D\PAPbPdPbPGPLPKPJPbPdPdPZPhPbPKPhPbPKPOPAPbPKFDEOEFEBP5A;jfbfPRbPAPfPOPiPAPfPiPAPfPPPTPSPiPbPR%8A15iU[99QAF6X2<PXPWPYPi11igRKPHP5fRRdP\P]PjP\P]E7G:X0:#4X1:G=D\P4fQRk1AAO7hgPhPgPAPhPgPAPPPTPSPhPkPR%8g15hU[99QgF6X2<PXPWPYPh11hiPHP5fSRAP\P]PbP\P]E7G:X0:#4X1:G=PjPiPKPiPGPLPgPJPiPKPKPZPdPiPgPdPiPgPOPjPiPgFDEOEFEBP51AiO9hAhPkPjPhPkPjPhPPPTPSPkfTRhPR%8j15kU[99QjF6X2<PXPWPYPk11kbRgPHP5fVRKP\P]PAP\P]E7G:X0:#4X1:G=P4AgdbjPdPbPjPPPTPSPdfURjPR%8b15dU[99QbF6X2<PXPWPYPd11dkPHP5fWRlP\P]PhP\P]E7G:X0:#4X1:#4DwPAPkPgPkPGPLPbPJPkPgPgPZPKPkPbPKPkPbPOPAPkPbFDEOEFEBP5AghdkPjPAPdPPPTPSPjfXRdPR%8A15jU[99QAF6X2<PXPWPYPj11jhRkPHP5fZRbP\P]PlP\P]E7G:X0:#4X1:#4DwP4A^KhAPPPTPSPKfYRAPR%8h15KU[99QhF6X2<PXPWPYPK11KjPHP5f[R4P\P]PdP\P]E7G:X0:#4X1:'vPlPjPkPjPGPLPhPJPjPkPkPZPbPjPhPbPjPhPOPlPjPhFDEOEFEBP5A^dKjPPPTPSPAf\RSPR%8l15AU[99QlF6X2<PXPWPYPA11AdRYPHP5f^P\P]P4P\P]E7G:X0:#4X1:'vg00;6g01C]R]Pd11dlRlg01DUR\CE%2V#?#?#?#?#2#T#P#S#@RVPdPlPZCE%NAPfP]PAPYP\CE&0VJR]%?N#?#?RN#2#?#?#2#T#P#S#S#@/3ZRf%CN#?#?#2#T#P#S#S#@RN7uZRlp-0RWg01EIRX#fR<%XXRQ1t:8RU&0O:RR&0N:RT%C2#2#P#y#2#C#P#S#@RP,Q:1e:2Rj'J,LT1sT6Rk5]T&0HBRB1Q:?/Jj,LTRgCU20GTCRCP5P7g01F5Rm-0F9Rn20E57=G9mdB0C:?8H0BRob7b8b9X5:W4AWP58%N8RP[^5:^4WP511S4Rp/3\PSP7O3b6b3W:P5O1PVPAPYPZCEP]PlP<PQPUPRPT1Q:V/Jj,LT=]TkPBPgCUPCPob7b8b9X5:X4WAWV58PP[^5:^4WP513pZPSP7O3b6b3W:P5O1n200100000021100011000%NdP:PA1bAG,HG1ZAG'1Rd20AAGH0@15dAP:1bbGRd,HGRp1ZbGRV'1%@FRF,<5RYX;:P:P?1b4GR\,HGRq/15/<FX>:P:PpPYX>:RY&0?:Rr/`rRr#f%Xr%f:9m:\%X:PEP5P8%@3RE,a:20=:2R25c:1a:F5c:Rr1a:G=c:2R2g01FUPn20;L8g01G1,`:&0::'`#XP:PDAkL5rAkL52H08bS=G9mdK09bQbR1HEd/HF/5pRdePdP:1HE\R\/HFPY206\FPqP5Elb311p?&05pEnPVP[EnPbP5Elb31<AF&04Jg01GYPZPZg01HSCEf]RF114bRA7p41<4GRG13LbR[A_J4ARJ13AZRAf`RV?;4bRp1AbO9hV4RVA^F4bRO'0R?'0Rq'0R\'0RY'0Rd'0PFP4PbP@P8P7P]PlP<PQPUPRPT1Q:L/Jj,LT=]TkPBPgCUPCPob7b8b9X5:X4WAWL58PP[^5:^4WP513SMPSPKO3b6b3P]Plg01IMRl#jR]#j,d:1d:]1d:l5q:5q:g01Il+03=mX<PQP:P:1t:6P7&02:RQCrP8PQCrPRPT1sT=1e:1R11Q:N'J,LT5]TPBPT1e:3:01:jRj/J1,LTPB1Q:E>0K:I,Jj,LTCUCUPCPob7b8b9X5:X<:X=:X4WAu67NAi876200EH9i76[[^5:^<:^=:^4WP5PfPZPSPFP8P^O6b6b3L0LPGPdPaP[PY13bM>0M[hPJP\PiPAPqP`PpP?P;PVPOP_P>CICICICICICICIbBb@b?WOWNP8P5O2n2001000000121000000W3WMP8P5O2n2001000000121000000W3WLP8P5O2n2001000000121000000W3WJP8P5O2n2001000000121000000W3WIXHeP8P5O2n2001000010121000000W3WGP8P5O2n2001000010121000000W3X:cP8P5O2n2001000010121000000W3P8P5O2n2001000000121000000W3WCP8P5O2n2001000000121000000bPWDWAXU:X;:XV0WTWFWWWKWEo"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition dec1_int_stmtA (tab : amem -> Z -> Z -> Prop) (E : Z) : Prop :=
    forall (L : alayout) (RNG : footprint)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock)
           (DST dcap S DT mtl : Z) (pdt : aptr) (src : list Z) (lo : Z) (rstk : region),
    AHEAP AI L RNG st LB m ->
    (forall F k, ~ In (mkABlock (ABFake 0) F k) LB) ->
    (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
    (* [comment removed for export] *)
    1 <= mtl <= 12 -> In (HB pdt DT (DTABLE_BYTES mtl)) LB -> tab m DT mtl ->
    (* [comment removed for export] *)
    ((DST = 0 /\ dcap = 0) \/ (exists pb, In (HB pb DST dcap) LB)) ->
    0 <= dcap < 2^32 ->
    (* [comment removed for export] *)
    bytes_at asegs m S (map (Z_to_bv 8) src) -> Forall (fun c => 0 <= c < 256) src ->
    zlen src < 2^26 -> 16 <= S -> src_inA LB S src ->
    (DT + DTABLE_BYTES mtl <= S \/ S + zlen src <= DT) -> (DST + dcap <= S \/ S + zlen src <= DST) ->
    (DT + DTABLE_BYTES mtl <= DST \/ DST + dcap <= DT) ->
    (* [comment removed for export] *)
    stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - HUF_DEC_STACK_A ->
    rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> ATOP <= r_rlo rstk ->
    bv_unsigned sp + 16 < al_top L -> bv_unsigned sp mod 16 = 0 ->
    mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    (* [comment removed for export] *)
    harness_invA m ->
    rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG -> rrng RNG rstk ->
    a0 = Z_to_bv 64 DST -> a1 = Z_to_bv 64 dcap -> a2 = Z_to_bv 64 S -> a3 = Z_to_bv 64 (zlen src) -> a4 = Z_to_bv 64 DT ->
    evtF asegs RNG (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (Z_to_bv 64 E) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition dec4_int_stmtA (tab : amem -> Z -> Z -> Prop) (E : Z) : Prop :=
    forall (L : alayout) (RNG : footprint)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock)
           (DST dcap S DT mtl flags : Z) (pdt : aptr) (src : list Z) (lo : Z) (rstk : region),
    AHEAP AI L RNG st LB m ->
    (forall F k, ~ In (mkABlock (ABFake 0) F k) LB) ->
    (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
    1 <= mtl <= 12 -> In (HB pdt DT (DTABLE_BYTES mtl)) LB -> tab m DT mtl ->
    ((DST = 0 /\ dcap = 0) \/ (exists pb, In (HB pb DST dcap) LB)) ->
    0 <= dcap < 2^32 ->
    bytes_at asegs m S (map (Z_to_bv 8) src) -> Forall (fun c => 0 <= c < 256) src ->
    zlen src < 2^26 -> 16 <= S -> src_inA LB S src ->
    (DT + DTABLE_BYTES mtl <= S \/ S + zlen src <= DT) -> (DST + dcap <= S \/ S + zlen src <= DST) ->
    (DT + DTABLE_BYTES mtl <= DST \/ DST + dcap <= DT) ->
    stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - HUF_DEC_STACK_A ->
    rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> ATOP <= r_rlo rstk ->
    bv_unsigned sp + 16 < al_top L -> bv_unsigned sp mod 16 = 0 ->
    mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    0 <= flags < 64 ->
    harness_invA m ->
    rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG -> rrng RNG rstk ->
    a0 = Z_to_bv 64 DST -> a1 = Z_to_bv 64 dcap -> a2 = Z_to_bv 64 S -> a3 = Z_to_bv 64 (zlen src) -> a4 = Z_to_bv 64 DT ->
    a5 = Z_to_bv 64 flags ->
    evtF asegs RNG (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (Z_to_bv 64 E) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Lemma dec4_int_stmtA_contract : forall tab E, dec4_int_stmtA tab E <-> huf_dec_stmtA AI rng_fs tab E.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_dec_iface ()) ["CANSEC1"; "Stmts"] "h03DSTh12DTh22FRh31Lh42LBh53RNGh61Sh72a0h82a1h92a2h:2a3h;2a4h<2a5h=2a6h>2a7h?4dcaph@2fchA5flagshB2gphC2lohD1mhE3mtlhF3pdthG2rahH4rstkhI2s0hJ2s1hK3s10hL3s11hM2s2hN2s3hO2s4hP2s5hQ2s6hR2s7hS2s8hT2s9hU2sphV3srchW2sthX2t0hY2t1hZ2t2h[2t3h\2t4h]2t5h^2t6h_2tph`1Eha1Fhb1Hhc1bhd1che1khf2pbhg3tabp%0p;1p;2p;7p;3p;4p;Lp;Op;5g000Gj10Tg000lj1?Tg001Jj1BTg001mj1nTg00Xcj12Tg01JXj2]Tg004[j1ITg00J@j7YTg01KDj1WTg00L7j3ATg00Iij3=Tg01L=j1OTg01LVj1mTg01MNj1gTg005Yj25Tg00V2j3`Tg005;j13Tg00;jj21Tg00>lj2;Tg00K>j1MTg01NFj1DTg00;Pj2ZTg00;6j2>Tg0079j2HTg01OJj28Tg003Uj1Xj26Tg01Ofj4VTg00Cgj4UTg01PBj3TTg00Ahj2<Tg00BHj1@Tg01Pcj3QTg01Qbj27Tg01RLj4PTg00U<j1RTg00S3j2GTg01S>j2STg01T9j1lTg01U2j1kTg01Ukj1jTg01Vej1KTg00_mj2fTg01W\j2eTg00ANj3:Tg01XPj1cTg00TIj3FTg01YVj2_Tg01ZOlLaTg01[TlObTg00\5j1^Tg01\Fj1dTg01]?j7JTg01^1j4LTg00?Gj4\Tg01^ej2hTg01_oj5[Tg01a4j2iTf0R0#0#0p=Ng00D\R1g00E:R27:0p=C%00#0#0#0p=4%20#2p=E%20#2#2#2p=9g00FMR3#0R4#NR5#0R6#0R7#0R8#?R9#BR:%?5R5#BR;#n[R<p-0\1\1[g01=iR=g01>cR>%24#?/]:R?%?7#BR@g01?\RAg01@WRB#IRCg00I2RD%I1REg01aMRFp,2rcRGp,2AIRHf_f^f;RIf:RJf<RKFYRL%W2f1RM;A0f=RN5=B#O^e1^a1ROA=B0N%mMRN%gM,5N5`G[^cBRN%33f8RP'1%23RQ#0RR#0#3,1P';RPf7#Mf9#D7AJf>RS5=BRTffRUfARVPIPJO3f?RW#C%CS';%M0f@RX;AW==BVXfD,ZD'>RB112W%34R4%37'H,8W';R7g00EXRYfDRZPWP1P;%X5PJCVCUR51120%N8R;#3,80';Xd1=T1IR[1<1K#@%2R#0#3,H4'8R4%36R6fBRR'1RKfFR\fCR];QSRS%DR,5]/1Z1<1W#@,5Z/1]'>RWfGR^/5\fER_'11<1X#@,5_/1^'>RX%DZ,5_fHR`'115`^/1_'>R`PYfLPVflR^,79CPRa%RGRb%4;R;#3'5/1RRRfnRc,79g01bJ'G,1]RdfORe/S]R]%lZ/1_RZfqRf,79%k_'1R_%j\,1bRbfsR\,79/56fvRg#K'8RhftRi,79/f6#CR6fU,eYRjg01cQ,699::iRk112e%38,8e';RefX#cR8f{S00fNR2f|Rl#K/G23FR2%4;#3%03#2#E#9#0#2#4#4#4#35FlR;f}Rm%EQ#9#9#9#0#2#0#4#4#4#3%03#2#E#9#0#2#0#4#4#33FR3p,6rng_fsS01p+01@RQf~RnO2RofQ,_QRpf[,699::gRqfW,<1#@,699::gRrf\,699::gRsPYp+01GRtPGPHp+01HPtp+01FRup+01ERvp+01DRwp+01CRxPnPmPiP\frS02PffpRyfoRzPcfmR{P^fkR|PUfeR}fcfbfaf`fYfdR~MLaS03PuPvPwPxp+01Bp+01APQPnPmPlQ00fzfyfxfwPgfuPiP\Q02PfPyPzPcP{P^P|fjfifhfgR|MObR^PUp+01I,69P}%^:R{P~%dYRcFJCL\q[[\q\q[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]H^C1]V]F^A1^E1^11^61^?1^01]4]W^D<]@]2^^:^]:^\:^[:^L:^K:^T:^S:^R:^Q:^P:^O:^N:^M:^>:^=:^<:^;:^::^9:^8:^7:^J:^I:^Z:^Y:^X:^_:^B:^U:^G:]5]3RzP|PVPIPJO3PYPtQ03P^PUp+01J,69P}P{P~PcFJCL\q\s\r\q\q\q\p\o\3\;\2\8\e\k\j\6\h\b\_\Z\]\d\R\a\`\X\W\S\K\4\[\5\7\B[\T\P\N\O\L^HF^C1^VE^FD^A1^E1^11^61^?1^01^4C^WA^D<^@@^2?^^:^]:^\:^[:^L:^K:^T:^S:^R:^Q:^P:^O:^N:^M:^>:^=:^<:^;:^::^9:^8:^7:^J:^I:^Z:^Y:^X:^_:^B:^U:^G:^5>^3=[R=P=P0XbzRzPzC\1hM0PGPHQ01PMP0D['ieX`1Wgo"). Qed.
End Stmts.
End CANSEC1.
