(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufStats HufPure_HufX2
  HufPure_HufTableX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem StrFun.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg RF_huf_iface RF_huf_bdt_model RF_huf_x2t_model RF_huf_x2t_c1.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_x2t_c2 () := "C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3mulI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3lorK47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib6Common6StrFun8lor_add'C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00C59OSSVerify5KrLib6Common6StrFun7lor_addC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C56Stdlib6ZArith6BinInt1Z9lor_assocC56Stdlib6ZArith6BinInt1Z3powc59OSSVerify5KrLib5Plain=RF_huf_x2t_c27d2_baseC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation fmem := (word -> option byte).

(* [comment removed for export] *)
Definition x2c2_stmt (pc : Z) (P : Z -> Prop) : Prop :=
  forall (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32)
         (x5 x10 x26 x28 : word) (x1 x6 x7 x11 x13 x15 x16 x22 x23 x27 x29 : word)
         (m m1 : fmem) (DT SY b e tb tl p len sym1 : Z) (sorted : list (option Z)) (js jt : list byte) (ncells : nat)
         (dt : list (option deltX2)) (r : list (option deltX2) * Z) (POST : machine_state -> Prop),
  P len -> len = 2 ^ (tl - tb) -> 1 <= tb <= tl -> tl <= 12 -> 0 <= sym1 < 256 ->
  fill_for_weight (S (Z.to_nat (e - b))) dt p b e tb tl sym1 2 sorted = Ok r ->
  0 <= b <= e -> e <= 256 -> 0 <= p ->
  length jt = (4 * ncells)%nat -> length js = length sorted -> length sorted = 256%nat ->
  (forall i v, nth i sorted None = Some v -> 0 <= v < 256) ->
  0 < DT -> DT + 4 + 4 * Z.of_nat ncells <= 2^47 -> 0 < SY -> SY + 256 <= 2^47 ->
  (DT + 4 + 4 * Z.of_nat ncells <= SY \/ SY + 256 <= DT + 4) ->
  x2f_inv m m1 DT SY js jt sorted ncells dt ->
  (forall m2 dt' (y5 y8 y9 y10 y14 y17 y21 y25 y26 y28 : word),
     r = (dt', p + (e - b) * len) -> x2f_inv m m2 DT SY js jt sorted ncells dt' ->
     evt psegs POST (MS (mkR x1 sp gp tp y5 x6 x7 y8 y9 y10 x11 (Z_to_bv 64 (Z.lor sym1 33554432)) x13 y14 x15 x16 y17
                             (Z_to_bv 64 2) (Z_to_bv 64 4) (Z_to_bv 64 8) y21 x22 x23 (Z_to_bv 64 SY) y25 y26 x27 y28 x29
                             (Z_to_bv 64 1) (Z_to_bv 64 3))
                        F (Z_to_bv 64 0x140c4) fc None m2 (seg_rom psegs))) ->
  evt psegs POST (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 tb) (Z_to_bv 64 len) x10 x11 (Z_to_bv 64 (Z.lor sym1 33554432)) x13
                          (Z_to_bv 64 (DT + 4 + 4 * p)) x15 x16 (Z_to_bv 64 (SY + b)) (Z_to_bv 64 2) (Z_to_bv 64 4)
                          (Z_to_bv 64 8) (Z_to_bv 64 b) x22 x23 (Z_to_bv 64 SY) (Z_to_bv 64 e) x26 x27 x28 x29
                          (Z_to_bv 64 1) (Z_to_bv 64 3))
                     F (Z_to_bv 64 pc) fc None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Lemma d2_base : forall tb sym1, 0 <= tb < 256 -> 0 <= sym1 < 256 ->
  tb * 65536 + Z.lor sym1 33554432 = sym1 + tb * 65536 + 33554432.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x2t_c2 ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with54__x2h61Hh72H0h82H1h92H2h:2H3h;2Hsh<2Hth=1qh>1rh?4sym1h@2tbhA1zp;2p;1p;3p;4p;6p;7p;8g0000j2:Tg000Lj12Tg0011j1?Tg001Oj24Tg001kj27Tg002Fj20Tg002cj2<Tg003@j33Tg003Zj1OTg004:j1MTg004Zj2HTg0058j1jTg005Vj4ETg0064j1_Tg006Rj1]Tg007=j2ATg007`j28Tg008Cj3JTg008fj39Tg009Ij2XTg009kj2WTg00:Ej2VTg00;1j3UTg00;Pj4TTg00<Bj2QTg00<_j1GTg00=Dj4;Tg00=oj1NTg00>Qj2PTg00?2j1LTg00?Kj2RTg00?hj2STg00@Hj2iTg00@oj2hTg00AVj2gTg00B<j2fTg00Bbj1eTg00C@j2bTg00Caj1DTg00D@j2>Tg00Dij3^Tg00ERj3BTg00F;j2\Tg00Fgj2KTg00GSj3[Tg00H3j6`Tg00HWj6aTg00IRj6ZTg00J0j7cTg00JTj7dTg00K8j8YTf0R0#2#2p=I%20#2#2#2p=6g00K\R1f1R2g00L:P0C;p==P2g00LaR3g00M@R4P4g00M`R5P0g00N@Fcp=1P1P2g00N`P0C;p=@f2R6P3P4P4P5P2P0Fdp=Ff3R7P3P4P4P5P6P2P0GYp=5g00OGR89310p=C1:82R9g00OeR:#2R;#2R<#I#6R=#?R>,42'7R?P1%6=#6R=#2#6#6#?R@,06f4RA%?=R='<RB/00107B/0@531XA1g00PJRB#ORC%MBRDP11H16REP2%j1RFCE%_1RG%]1RH1A1:RI181=5J1RJ1A1;R;181@RK591591A91;J=91K'='11XH5R;P0P6g00Q6RJg00QVRL'W1V06=3JLdAU182CTRLb2b3b4X01X511<0=R=102@'0102=/0@531^01^51P0P7PAO2b11Q6@P6P@%G:#I#G#?RAPCPDPFPGP11818R=g00R6RJ181AC;,1HP;PLb2b3b41:8AP0b1PCPD1H12PGPHP1P=PJPIC;,1HRJ181>,@I,1H5FH%N4RA1@IK,1H9FHJRJC5P;PLb2b3b4X011:80140>'7142@,79R9[^01P0P7P2O2b11P@@%C@R>#L1R@@RM,<@1S@@RN'0931@[1i@@148@RO1:8N14N@'7[1h@@14@814@N1:N8'7[1g@@%CM\>1f@@A31N@\>PMP1PNP1%e:,b1g00R]R:#DRN,>1RM5^11>1:R:5B1%DNRN#D,>11>1N5B1AB1M:g00S<'\'K'K=[BCPDP1P1PEP6PFCEP2PFCEPGPHPH1@=K,1HPAPJC5PAPHPHPHP3P4P4P51=K=,1HE`PA1A1<9J1K=91I,=K,1HC5PA1=I=,1HC5C5P;PLb2b3b4X01X51P9\Og00Sh\>1<@7/06931@[%C6[[^01^51P0P6P2f6f7O4b1b>b=b:b9b8b7b6EaEZX;?W<X?1X@1o"). Qed.

Lemma d2_val : forall tb sym1 sym2, 0 <= tb < 256 -> 0 <= sym1 < 256 -> 0 <= sym2 < 256 ->
  Z.lor (sym2 * 256) (sym1 + tb * 65536 + 33554432) = (sym1 + sym2 * 256) + 65536 * (tb + 256 * 2).
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x2t_c2 ()) [] "h04__x1h17__arithh24__x2h34__ffh48__varmaph55__with64__x3h71zh81Hh92H0h:2H3h;2H4h<2H5h=1qh>1rh?4__x4h@2E1hA2H1hB2H2hC2HthD4sym1hE4sym2hF2tbp%0p;1p;2p;3p;4p;6p;7p;8g000Lj16Tg0011j1CTg002Fj20Tg002cj21Tg003Zj1eTg004:j1dTg004Zj2LTg0058j1bTg0064j1yTg006Rj1xTg007=j2FTg009Ij2pTg009kj2lTg00:Ej2iTg003@j3PTg00;1j3gTg00;Pj4fTg00<Bj2=Tg007`j2]Tg00=oj1cTg00>Qj2QTg00?2j1\Tg00?Kj2;Tg00?hj22Tg00@Hj2[Tg001Oj2@Tg00@oj2ZTg0000j2OTg001kj2MTg00AVj2XTg00B<j2YTg00Bbj1wTg00C@j2vTg00Caj1WTg00D@j2KTg00Dij3uTg00ERj3HTg00F;j2VTg00Fgj2UTg00GSj3TTg00<_j1_Tg00TEj6^Tg00IRj6ITg00U?j2rTg00Uhj3qTg00HWj6oTg00VQj3nTg005Vj4mTg008Cj3kTg008fj3jTg00=Dj4STg00J0j7aTg00JTj7sTg00K8j8tTg00H3j6hTg00OGR0f0R1'Op=9%61#6p=:f2R2f1R3/@1'Mp=A1023/11p=5g00K\R4?P31p=>P4P2P3P1Cmp=B1]41p=DAk431p=8Aj431p=4P2g00LaR5g00M@R6P6g00M`R7P4P3g00L:P1CSg00N@R8Fap=<10319P42p=?P4P3g00R6P1CSp=NP3P5P6P6P7P1P8Fap=7P4P3g00N`P1CSp=GP2P5P6P6P7P3P1Fsp=Rf3R8P5P6P6P7P2P3P1Gtp=3AP410p=EP3P5P6P6P7P1Ehp=`1123/01p=J%92g00OeR5#6R9#6R:#6R;#6R<#:#:R=#CR>7A2R?P4f5R@%6=R=#CRA%6=#:#:#:R=#CRB35RCf4RD'0f6RE/1B,0@%6=#:#:#:#:#CR='0S00/>1X74g00PJRF#eRG%dFRH1L42RI%b4RJ7B3%y4RK%x4RL1F45RM1F49RN%DBRO'8'4%D='4%DA,4N/8ORP/4M3<1pL7R7P1P2g00Q6RQg00QVRR'l1i12=PQRdAg403CfRRb3b4b5X04X24113B,01/0=A53ABRQ;?1^04^24P1PEP@O2b11=CDRSPCPD%C;R;PGPHPJPK1]40RT%D;'N,7LP7PRb3b4b5%9;P1b1RUPGPH1L43S01PKPL1NTM,7LRV%D>RW,GM,7L5RLRX%c6R6PXC3P7PRb3b4b5X04RY%91?A1>RZ%93R[?A3>R\[^04R]P1P@P2O2R^b11QC>%E>RC#\R_A5EABR`1;`>,1>12`>3?[1[`>1@0>Raf7Rb?5ABRc/2>Rd#9?Ad>[1Zc>1@>0Rdf8Re?5ABRf/2>Rg,@>1Og0'M[1Xf>f9Rg?5ABRh/;>#E\C1Yh>f:Ri?5ABRj/2>/>j\C1;j>P4f;?5ABRk/2>P4%w5,v4g00R]Rl#WRm,K4Rn5u41K4lRl5H4%WmRm#W,K4Ro1K4m5H4AH4nlg00S<Rm'V'U'U=TFGRpPH1L48Rq?B8J9BI3PKPLPL1GTW,7LP6PXC3RrP6PLPLA<LWT,`LRsP6%_9,F4,8W/4M9<LPC3P6A<LMTRtC3C3P7PRb3b4b5X04X24X64P\\aR\g00ShRu\CRvA58ABRw11>D;?2[%E2Rx[[^04^24^64P1P2f=P3PEPbO5b1b>b=b<b;b:b9b8E^EI11@B,0D/0=/>SP41=`@RS11@>R=/=110E=%C9R9,1>Ry,0b,1B'0Rz'>X74P411D>R{/=`R|/=@1>1zX74R}P410{`R~1=1E/>zX74P410~@P}PGPHABI3qPK18MWRI/4P%_5R5,F4R}'414}I%D9,8W,4N,8O'45<LP7PRb3b4b5X04X24X64111>RN/0Q/02102N103y,1B3?^04^24^64P1PEPbP@O3b11=~@P~P@P;PUPYP]P1PEP8O2b11Q~>10=cR=1;=>,1>12=>3?\_1[=>AJE>fR=/2>R_#9?A_>\a1Z=>AJb>hR=/2>Ra,@>1Oa0'M\d1X=>AJe>jRe/;>#E\C1Ye>AJg>kRg/2>/>g\C1;g>P4f<Rg?5ABRA9Ji>/2>P4PpPH1L4D9Bq2?B3JPKPLPrP6PLPLPsP61F4:/8W/4P%65,F4R5,8W/4M5<LC3P6PtC3C3P7PRb3b4b5X04X24X64X?410{w11>@;?2\vPx[\\^04^24^64^?4P1P2Pgf>RgP3PEPbO6b1b>b=b<b;b:b9b8E^EIP|P{P`%C<R<PGPHPJPK%D<,NT,7LP7PRb3b4b5%9<P1b11r4>=q4n=H4l/VmAH4lo/Vm,Ul=TFG5TFPHQ01PKPLPXP61NTI,7L1GIO,7L5RLC3P7PRb3b4b5X04113>R>#9?A>B\Z^04P^b11Q`B%EBR^#\1;cB,1B12cB5?c[1[cB1@0BRc12fBRZ#9?AZB[1ZfB1@B012hBRf,@B1Of0'M[1XhB1;jB#E\^1YjB12kB/>k\^1;kBP412ABP4PpPHABJ2q?B3JPKPLPL1GTO,7LP61GMO,7L9RLVC3P6PLPLA<LOT,`LP618O5/4M9<LPC3P6PtC3C3P7PRb3b4b5X04X24X64AA[3B\cPu\^11BD=?w2[Px[[^04^24^64P1P2PgP3PEPbO5b1b>b=b<b;b:b9b8EoEI1={SAn{`@EIQ00P1EIb@XB?XA?WCXE4XD4XF4o"). Qed.

Lemma d2_norm : forall tb sym1, 0 <= tb < 256 -> 0 <= sym1 < 256 -> tb ≪ 16 + Z.lor sym1 33554432 = sym1 + tb * 65536 + 33554432.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x2t_c2 ()) [] "h07__arithh14__ffh28__varmaph35__with44__x1h52Hsh62Hth74sym1h82tbh91zp;2p;1p;3p;4p;7p;8p;6g0000j27Tg000Lj11Tg0011j12Tg001Oj2;Tg001kj2:Tg00W4j2LTg002cj29Tg00<Bj2ATg002Fj24Tg003@j38Tg003Zj1=Tg004:j1<Tg004Zj2QTg0064j1PTg006Rj1OTg007`j23Tg007=j2MTg00=Dj45Tg00JTj7KTg00=oj1HTg00K8j8CTg009Ij2BTg009kj2DTg00:Ej2ETg00;1j3FTg00;Pj4GTg00WQj4@Tg00XQj2ITg0058j1JTg00Y1j3?Tg00IRj6>Tg00J0j7NTf0R0#1#1p=0f1R1g00LaR2g00M@R3P3g00M`R4P0g00N@FNp=6g00K\R5g00OGR6/71g00OeR7#1R8#1#0R9#0#0R:#2R;,;1':R<P5f3R=%28%29R9'L'9%0:#0#0#0R:#1#0#0#0#0#2R8,A=,40f4R>%2:'9,4=/48585X95P=f2R8g00PJR:#=R?%<:R:1Q51%P5R@%O5RAP2P3P3P4PAP2P3P3P4P51356R2g00R6RB1M57R7C5,6AP5P7g00N`135;C5,6AFKR7%H3P7GC1BA4R4P0P8g00Q6R7g00QVR3'D1E08=873dAF561CGR3b1b2b3X45R717601;0;':P<[^45R;P0P>P8O2b0P7P;P0P=P1O2b0C@1I=9P?P:%J5P@P5P2PB1359C5,6AP4P3b1b2b31769P0b09?=9E>X5<W6X75W8o"). Qed.
