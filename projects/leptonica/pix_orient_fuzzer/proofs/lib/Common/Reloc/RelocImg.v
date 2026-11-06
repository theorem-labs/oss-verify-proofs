(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec StreamSim StoreOk.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_RelocImg () := "C47Corelib7Classes?RelationClasses9ReflexiveC47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List7forallbK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC47Corelib4Init9Datatypes6lengthC56Stdlib5Arith8PeanoNat3Nat3eqbC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3sndC46Stdlib5Lists4List7combineC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6eqb_eqC45stdpp9bitvector;definitions5bv_eqC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes8list_indc69OSSVerify5KrLib6Common5Reloc8RelocImg9bytes_eqbC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib7Numbers7BinNums1N00c69OSSVerify5KrLib6Common5Reloc8RelocImg;cells_checkC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01C46Stdlib5Lists4List2Inc69OSSVerify5KrLib6Common5Reloc8RelocImg7cell_okC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC46Stdlib5Lists4List<nth_error_InC69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02c69OSSVerify5KrLib6Common5Reloc8RelocImg6ce_blkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc8RelocImg7ce_addrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc2rlC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc8RelocImg4ce_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc8RelocImg6ce_valC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc8RelocImg:cell_bytesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc8RelocImg>bytes_eqb_trueC1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib6Common5Reloc8RelocImg5ccell00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00i69OSSVerify5KrLib6Common5Reloc8RelocImg9RelocData00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc8RelocImg:rl_data_loC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib6Common5Reloc5Reloc9rl_img_hiC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc8RelocImg:rl_data_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC56Stdlib6ZArith6BinInt1Z6leb_leC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC45stdpp9bitvector;definitions=Z_to_bv_smallC56Stdlib6ZArith6BinInt1Z3maxC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revc69OSSVerify5KrLib6Common5Reloc8RelocImg<rl_data_wsegC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk?store_ok_windowC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK46Stdlib9micromega=RingMicromega3Op201I69OSSVerify5KrLib6Common5Reloc5Reloc5Reloc00C1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega8ZifyInst7Inj_Z_Z".
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Inductive cval :=
| CV_lit (z : Z)                    (* [comment removed for export] *)
| CV_rl (X : positive) (t : Z)      (* [comment removed for export] *)
| CV_rel (X : positive) (t : Z) (Y : positive) (u : Z)
                                    (* [comment removed for export] *)
| CV_bytes (bs : list Z).           (* [comment removed for export] *)

Record ccell := mkCell { ce_blk : positive; ce_addr : Z; ce_n : nat; ce_val : cval }.

Section Cells.
Context {RL : Reloc}.

Definition cell_bytes (n : nat) (v : cval) : list byte :=
  match v with
  | CV_lit z => word_to_le_bytes n (Z_to_bv 64 z)
  | CV_rl X t => word_to_le_bytes n (rl (rl_delta X) t)
  | CV_rel X t Y u => word_to_le_bytes n (Z_to_bv 64 ((t + rl_delta X) - (u + rl_delta Y)))
  | CV_bytes bs => map (Z_to_bv 8) bs
  end.

Definition bytes_eqb (l1 l2 : list byte) : bool :=
  (Nat.eqb (length l1) (length l2)) && forallb (fun p => Z.eqb (bv_unsigned (fst p)) (bv_unsigned (snd p))) (combine l1 l2).

Lemma bytes_eqb_true : forall l1 l2, bytes_eqb l1 l2 = true -> l1 = l2.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocImg ()) ["Cells"] "p'0h01Hh12H0h21nh32l1h42l2h52Hxh62b1h72b2h82l0h91mh:1yh;2Hlh<2IHh=1bi001bh>1eh?1ph@1xi011lp;1p;3p;2p;6p;4p;8p;5p-1R0p10000p4p710p9P0g000\R1p4p710p8P0P1p4p7210p8P0g0019R0p4p710p8g001Uj1=Tg002:j1PTg002Xj19Tg003;R2j1ETg003[j32Tg0045j1JTg004Uj2?Tg004oj34j2Aj1GTg005Oj6FTg005kj2CTg006Jj25Tg006jj2;Tg007Jj20Tg0084j23Tg008Qj2OTP1j3NTg0091j3MTg009Nj47TP0j38Tg009jj2<Tg00:Hj3@Tg00:kR0j2>Tg00;Fj2HTg00;fj3ITg00<Jj8BTg00<gj6KTg00=Ej5DTg00=gj2LTg00>kR1f1R3f0R4'Lg00?KR532p=6A2145p=1g00?kR6?234p=:g00@I#=#=#=#PR7#9R8#ER9P81634f2R:=293[^49R;X39P2P8%J8R</64A29<3[P416<<1?9<W0A4834R=,6<P1g00@nP1p-0P4g00ANR>g00Akn0110000020000X>1g00BGP5P4EFR?P>f3R@=48:RA929</C4b1W0X49X:8P3P4O2n10110100020020100101X89P2P8f4R2=48@RB/64f5RC=482RD=293[P416A<P?P>A29D</C4b1W0f7RDf6R<548/6=158D1583';R=f8R>,07R?107:'31O88RAAN884,07AM884,07'3X?AREP8P8PDP3C738'<RF;@4%1=%1F'>P0158>158:';#1f9RF,07107@'3P8P8P>P:C798AE'<#1f:R==48F=29BP4158=1582';#1f<RB,07107<'3P8P8f;PCC798AE'<#1f=RC,07RG107D'3RHP8P8PBP<C798AER<;@4%1H%1<'>P0f>R<,07/3?#1P8P8PCPDC798AE#1f?RD=48<A48F>529P4f@RF,07107='3#1P8P8PFP=C798AE#1P01334#11::3[R=1:3413:3#1RF[1:@:\F1H34P3n2001000000120000000X96X26P=^96^26P4fCR6,07R=PGP:O31:=GP9P9fDR=,A81A8<P6PCP8P9\9RG%G8RFPFP=P<PG\8/?Fg00BcRF%94RG%93R?P0%9:?23410@:10@3':R0[10:310:4':%9@?2:3[RH%92?2@:\0AI:34P4n2001000000120000000W7W6W2PH^7?^6G^2FP4P7fEPDP3O4b1GBfBPCP1P5P8P8P=P<C798AE,<4#1X=1P:1586158C';P>EK166CeO2GBb5b1W0W5P3P4O2n2001000000121000000b0W0W;P3P4O2n2001000000121000000b0W0X49X:8P3P4O2n10110100020021100101X89X<;X39X@8P4DDW3o"). Qed.

Definition cell_ok (c : ccell) : bool :=
  match rdn rl_segs (fun _ => None) (rl (rl_delta (ce_blk c)) (ce_addr c)) (ce_n c) with
  | Some bs => bytes_eqb bs (cell_bytes (ce_n c) (ce_val c))
  | None => false
  end.

Definition cells_check (tbl : list ccell) : bool := forallb cell_ok tbl.

Theorem cell_fact : forall tbl, cells_check tbl = true -> forall i c, nth_error tbl i = Some c ->
  rdn rl_segs (fun _ => None) (rl (rl_delta (ce_blk c)) (ce_addr c)) (ce_n c) = Some (cell_bytes (ce_n c) (ce_val c)).
Proof.
ltac2:(KReplay.run1 (kr_t_RelocImg ()) ["Cells"] "p'0h01Hh13Hokh21xi001xh32H0h42Hih52bsi012bsh61ch71eh81ih95lemmah:1oi021oh;3tbli031bi041lp;1p;3p;2p;5p;4p;8p;6g003;j1>Tg00CAj1QTg00DGR0j1<Tg00Dij3PTg00EGj2;j1CTg003[j32Tg0019j36Tg00Eij3:Tg00F@R1j1=Tg00GBj2BTg00G[j3@Tg00HLj3?Tg00Hoj5OTg00IPj1NTg001Uj11Tg002:j18Tg002Xj19Tg00JOj14Tg00K1j1ITg00L2j2HTg00M2j1GTg00N4j2FTg00Nnj13Tg00Omj4ETg00Pej15Tg00Qfj27Tg00=gj2DTg004Uj2JTg00Rkj3KTg00<Jj8ATg005Oj6LTg005kj2MTg00>kR2f0R3g00?KR432p=0g00T4R5#>%Q3#0g00U6%<5f3R6f1R75P51;5332f4R89651#0f5R99:53%=7#0R:[^25R;'BA6519#0f6R<9:53P:[^25;@3W9A?518P6O2P;P3f2R;P5P9P6P;P7DOO2%=;#0p,2RLR;#Ng00@I#1#1#1R9#1#1#1#8#9%89#9R9#4U%I6,H;%G6'F%36CE%>9R9#<R6P0P9P0P9P2P3%3<%5<'7R<,D3R0g00@nR;n10110000021010100#01;9<R<9267]0P3%00P9P6%C9R0P0P7f7R8#3%58'7R8P6\9/J0AK783GAW0X59P3O1A22;4P2P;P2p-0P3g00ANR;g00Akn0110300020000X72g00BGP4P3ELP;%49=26</M3b3W0n10110200021010400P7O1b:b0b1W4X65W8W1W;o"). Qed.
End Cells.

(* [comment removed for export] *)
Class RelocData (RL : Reloc) := {
  rl_data_lo : Z;                      (* [comment removed for export] *)
  rl_data_ok : (0 <=? rl_data_lo) && (rl_data_lo <=? rl_img_hi) && (rl_img_hi <=? 2^32) = true;
  rl_data_wseg : wseg_ok rl_segs (Z_to_bv 64 rl_data_lo) (Z.to_nat (rl_img_hi - rl_data_lo)) = true
}.

Lemma rl_store_ok_data : forall {RL : Reloc} {RD : RelocData RL} m (a : word) n,
  rl_data_lo <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= rl_img_hi ->
  store_ok rl_segs m a n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocImg ()) [] "h01Hh11mh24__x1h32Hah44__x2h51nh61xh77__arithh84__ffh96__sat5h:6__sat6h;8__varmaph<5__with=4cstrh>2H1h?2H2h@2H3hA4__p1hB6__sat4hC6__sat7hD4__x3hE2H4hF3HhihG3HlohH2RDhI2RLhJ1ahK1yhL2z4p&0p;1p;2p;3p;4p;<p;6p;7p;>p;8p;Bg00UUk108Tg001Uj1?Tg002:j1PTg002Xj1STg00DGk107Tg00V[j22Tg007Jj2WTg00W`j23Tg00X<R0j1GTg00X\R1j2BTg00Y9j11Tg00Z:j2aTg00[?j24Tg009jj2ATg00[\j1MTg00\:j2YTg00:Hj3XTg00:kR2j27Tg00IPj1QTg00\Wj4VTg00]Wj2kTg00^7j2hTg00^]j2@Tg00_:R3j1eTg00_Zj1dTg00`?j2[Tg00`gj2:Tg00aCj3TTg00agj1LTg00bFj2CTg00boj2ITg0045j1`Tg004oj3HTg003;j1_Tg00c[j2JTg00d9j1^Tg00dWj4RTg00e5k106Tg00eSk105Tg00f>j2FTg00faj2]Tg00gDj3\Tg00JOk104Tg00ggj4OTg00hRk203Tg004Uj2;Tg00i4k202Tg00i`j3zTg00j?j4yTg00k1j3xTg00k]j2ETg003[j1rj3DTg00l:j1qTg00lXj4pTg00m;l<nTg00m`j2jTg00nBj2UTg00n\j1iTg00o:j2sTg00o[j3tTg010Dj6uTg010hj1vTg011Mj3wTg0120j7gTg012Tj3fTg0137j4{Tg013bj2|Tg014il>}Tg015lj3~Tg016Uk700Tg0179k701Tg017]j8cTg018Al<ZTg018flBbTg019LR4f0R5'4p=9g00>kR6g00?KR77D5p=01345p=6g00?kR8f1R9;~5p=<P8P9g019jP5COp=8P9g01:QR:g01;0R;P;g01;PR<P5g01<0K00p=5f2R=P:P;P;P<P9P5K01p=Kf3R>P:P;P;P<P=P9P5Gcp=>AD895p==P8g00U6R?P8P8P3f4R3P0P>g01<PP=P9P5M<Zp=oP?P8P8P8P0P0f5R0P3P>P=P9P5M<Zp=lP8P8P8P8P8P8P1P5P9P=P1P>P3P0f6R1f7R@f8RAf9RBMBbp=mP8P9g01==P5COp=Ng01=d&085g00@IRC#?RD#?RE#?RF#?#?RG#?RH#PRI#SRJ%PF#S$07RF[123>1WI9'31WI=%G9'B%10'31a101210RK#9%11RL,4K'A%MDRK%MGRM'YRN,4L'A#012@1RL#9%1@RO,4L'ARL14ONRO;X5%0L%0O'7P212A@RO#9%1ARA,4O'A#014AN#0%QBP@P1P0CV#0P5f:R1/2BRA#9%11,4A'A#0f;RA#1/4N#0f<RO/2ARL#9RP%1O,4LRL;X9%0P%0L'7P2f=RL/2ORP#9#0%1L,4P#0f>RP#QPOPAP1CV#0P5f?RO/2P#9#0f@RP/2O%1P'4#0P21495#013=9[R2139514=9#0RP[13>=\P1k95P9n2001000000120000000X18X58RPP2^18^58R2P5P4fBROfARL'2RQP=O3%6QPPP2P5fDRQfCRR'2RS%1QRTP>O313STPPP2P5fFR2#1RPPNP1O313PNfGRP#QfE12P2R1,hIPQ%1PRQ/@1RT#eRSPRP1PQ%dRRU%GR#6RR1[KMRV1:4KRW%6M1:4N[[RX%6KRYg00AkRZATKM9UW3RM%6N\Z^3YR[%MHRH,[KR\%6H1YKHR],:4[\WRWATKH9VZX3YRH%6]\Z^3YRYfJfIRZO1R^PFg01>cR_g01?OR`#LRa#LRb#L,C8Rc1C8bRb1C8`R`'<'<g01?nRd'I%`_Re3H%__RfP8P81J8=RgP=%^8RhCRP9PhCR&068Rh&058Ri1F8ERE1]8KRK%PG5\8RG'8,5i&04;RjPi1F8CRk/8E,5iPjPi1]84RE/8k,5iRlPjP8Pkg01@ZA\8KIRKCO,5i9KilC>C>C>203i<RlP5P=1;672025=#0dAz849CyR7b8b;b<X28X48139N139=%6=%6>1:>]'7[[[^28^48P5fNR6#1RmfM,26R6P@PBPAO5b7b1bBb9b:bCb=9xI1%GSRI,B1RA/=Q1E4TRn,B1Ro/=QP8P8%r8RpP5X68RqPp1=95#qXK8X68PAPoPqPqPqP8P8g01AA1B95Cp,;8X18X58P1P11;81PIPnPqPq%G5,;8X6?PSPnPq1E45X68PTPT1;8TDoElM:mPQPQ1;8QM<nPUPRfHRQ#112QP'@RT,j41:4T1E4TRq/=T'713T4AD8q4'7'U%1Z12ZQ'@,E4P8PVPXPMP[P^PFp-0RQ1C8a/<`,<b/Id%iC,s8=t8b/<`R`,<c/Id1I`d=H_e5H_5H_PfP8PgP91J8>CRPhPiPiP:P;P;P<PiP:P;P;P<P0Eu1F8DRD%vC,F8RC=w8kR<'N,5i5Ki18<E,5i1NDE,5i5KiFgPjPi18kC,5iPjAf8kD/NC,5iC>C>PlP7b8b;b<X28X48XD8WA1@=5RC,=9,7>13C4AD894'7'U139>1B=>/=3[[^28^48^D8^AQP51@m6,:4PmP3P6P0PBO6b7b1b9b:bLbEb=C{PUPRPVPXPMP[P\PWPHPYP^PFPePf1J89PhPi18kG,5iPj18kK,5iC>PlP7b8b;b<X28135N139][^28P5PmP@O2b7b1bBb9b:bCb=1|P2POPLM>}b@b0b?b0b>b0W?W>P9P5O2n2001000000121000000b0W@W0P9P5O2n2001000000121000000b0b0WFWGX5?XJJW1WHWIo"). Qed.
