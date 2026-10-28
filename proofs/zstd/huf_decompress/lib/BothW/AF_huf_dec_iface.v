(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require HufHarness.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import Stdio_kit AH_huf_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_dec_iface () := "C46Stdlib5Lists4List2hdK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_dec_iface:huf_dt_okAC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1;x1_table_okC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3mulC5ARocqVerifyHarness?AgentSubmission5Plain<RF_huf_iface8x1_bytesC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2;x2_table_okC5ARocqVerifyHarness?AgentSubmission5Plain<RF_huf_iface8x2_bytesI47Corelib4Init5Logic2or00I47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list02c5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_dec_iface7x1_tabAc5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_dec_iface7x2_tabAI47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or01C47Corelib4Init5Logic8eq_ind_rK47Corelib4Init5Logic2or02I47Corelib4Init5Logic2eq00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef6firstnC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsK47Corelib7Numbers7BinNums8positive03I5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX16deltX100I5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26deltX200C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC46Stdlib5Lists4List2InC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface5AHEAPK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind01K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_blockC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<ablock_rangeC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadI35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupK47Corelib4Init9Datatypes6option01C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:chunk_sizeC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl>chunk_user_begC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC5ARocqVerifyHarness?AgentSubmission5BothW5ABase=ablock_shadowC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeK47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib6ZArith4ZdivAZ_div_mod_eq_fullC47Corelib4Init5Logic6eq_symI46Stdlib;setoid_ring<Ring_polynom5PExpr00I47Corelib4Init9Datatypes4prod00K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr07I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C46Stdlib6ZArith4Zdiv:Z_mod_multC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst:ATOP_rangeC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission5BothW9AProg_kitAablock_unpoisonedC47Corelib4Init5Logic5proj1C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:is_primaryC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_liveC35stdpp4base6lookupC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6achunk00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterI5ARocqVerifyHarness?AgentSubmission5BothW5ABase7alayout00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintI5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6astate00I5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AREQMAXI47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3KLSI46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01K47Corelib4Init5Logic4True01I46Stdlib;setoid_ring<Ring_polynom3Mon00C5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MINC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MAXK47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind02C47Corelib4Init5Logic3notC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_addrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_sizeC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface<DTABLE_BYTESC56Stdlib6ZArith6BinInt1Z2ltC47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface7src_inAC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6rcleanC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_loC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4r_hiC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit5r_rloC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_topC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission5BothW>AHarness_iface<harness_invAC5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4rrngC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface=huf_dec_postAC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFc5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_dec_iface>dec4_int_stmtAC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface=huf_dec_stmtAC47Corelib4Init5Logic3iffI5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit6region00C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface?HUF_DEC_STACK_AC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3ATP".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".

Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AHUF_DX1_1X : Z := 0x84708.     (* [comment removed for export] *)
Definition AHUF_DX2_1X : Z := 0x82ed4.     (* [comment removed for export] *)
Definition AHUF_DX1_4X : Z := 0x87f04.     (* [comment removed for export] *)
Definition AHUF_DX2_4X : Z := 0x85048.     (* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition huf_dt_okA (m : amem) (DT mtl : Z) : Prop :=
  exists (tt tl : Z),
    bytes_at bsegs m DT [Z_to_bv 8 mtl; Z_to_bv 8 tt; Z_to_bv 8 tl; Z_to_bv 8 mtl]
    /\ ((tt = 0 /\ exists cells : list deltX1, zlen cells = 2^(mtl+1) /\ x1_table_ok cells tl /\ tl <= mtl + 1
                                               /\ bytes_at bsegs m (DT + 4) (firstn (Z.to_nat (2 * 2^tl)) (x1_bytes cells)))
        \/ (tt = 1 /\ exists cells : list deltX2, zlen cells = 2^mtl /\ x2_table_ok cells tl /\ tl <= mtl
                                               /\ bytes_at bsegs m (DT + 4) (firstn (Z.to_nat (4 * 2^tl)) (x2_bytes cells)))).

Definition x1_tabA (m : amem) (DT mtl : Z) : Prop :=
  exists (tl : Z) (cells : list deltX1),
    bytes_at bsegs m DT [Z_to_bv 8 mtl; Z_to_bv 8 0; Z_to_bv 8 tl; Z_to_bv 8 mtl]
    /\ zlen cells = 2^(mtl+1) /\ x1_table_ok cells tl /\ tl <= mtl + 1
    /\ bytes_at bsegs m (DT + 4) (firstn (Z.to_nat (2 * 2^tl)) (x1_bytes cells)).

Definition x2_tabA (m : amem) (DT mtl : Z) : Prop :=
  exists (tl : Z) (cells : list deltX2),
    bytes_at bsegs m DT [Z_to_bv 8 mtl; Z_to_bv 8 1; Z_to_bv 8 tl; Z_to_bv 8 mtl]
    /\ zlen cells = 2^mtl /\ x2_table_ok cells tl /\ tl <= mtl
    /\ bytes_at bsegs m (DT + 4) (firstn (Z.to_nat (4 * 2^tl)) (x2_bytes cells)).

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
    /\ rng RNG A n /\ rng RNG (shad A) (shlen (n + 7)) /\ wr_at bsegs m A n.
Proof.
intros L RNG st LB m p A n AH HIN.
destruct (AI_block AI L RNG st LB m p A n AH HIN) as (NR & (BLK & N0 & TOP & A16) & RA & RS & SHB & WR & _).
pose proof (ablk_lin _ _ BLK) as (L1 & L2 & L3 & L4).
split; [| split; [exact A16 | split; [lia | split; [exact BLK | split; [exact TOP | split; [exact RA | split; [exact RS | exact WR]]]]]]].
apply ablock_unpoisoned; [exact SHB | clear - A16; Z.div_mod_to_equations; lia | lia | lia | lia].
Qed.

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
    bytes_at bsegs m S (map (Z_to_bv 8) src) -> Forall (fun c => 0 <= c < 256) src ->
    zlen src < 2^26 -> 16 <= S -> src_inA LB S src ->
    (DT + DTABLE_BYTES mtl <= S \/ S + zlen src <= DT) -> (DST + dcap <= S \/ S + zlen src <= DST) ->
    (DT + DTABLE_BYTES mtl <= DST \/ DST + dcap <= DT) ->
    (* [comment removed for export] *)
    stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - HUF_DEC_STACK_A ->
    rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> ATOP <= r_rlo rstk ->
    bv_unsigned sp + 16 < al_top L -> bv_unsigned sp mod 16 = 0 ->
    mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
    (* [comment removed for export] *)
    harness_invA m ->
    rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG -> rrng RNG rstk ->
    a0 = Z_to_bv 64 DST -> a1 = Z_to_bv 64 dcap -> a2 = Z_to_bv 64 S -> a3 = Z_to_bv 64 (zlen src) -> a4 = Z_to_bv 64 DT ->
    evtF bsegs RNG (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (Z_to_bv 64 E) fc None m (seg_rom bsegs)).

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
    bytes_at bsegs m S (map (Z_to_bv 8) src) -> Forall (fun c => 0 <= c < 256) src ->
    zlen src < 2^26 -> 16 <= S -> src_inA LB S src ->
    (DT + DTABLE_BYTES mtl <= S \/ S + zlen src <= DT) -> (DST + dcap <= S \/ S + zlen src <= DST) ->
    (DT + DTABLE_BYTES mtl <= DST \/ DST + dcap <= DT) ->
    stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - HUF_DEC_STACK_A ->
    rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> ATOP <= r_rlo rstk ->
    bv_unsigned sp + 16 < al_top L -> bv_unsigned sp mod 16 = 0 ->
    mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
    0 <= flags < 64 ->
    harness_invA m ->
    rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG -> rrng RNG rstk ->
    a0 = Z_to_bv 64 DST -> a1 = Z_to_bv 64 dcap -> a2 = Z_to_bv 64 S -> a3 = Z_to_bv 64 (zlen src) -> a4 = Z_to_bv 64 DT ->
    a5 = Z_to_bv 64 flags ->
    evtF bsegs RNG (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (Z_to_bv 64 E) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Lemma dec4_int_stmtA_contract : forall tab E, dec4_int_stmtA tab E <-> huf_dec_stmtA AI rng_fs tab E.
Proof.
intros tab E. unfold dec4_int_stmtA, huf_dec_stmtA. split; intro H; exact H. Qed.
End Stmts.
End CANSEC1.
