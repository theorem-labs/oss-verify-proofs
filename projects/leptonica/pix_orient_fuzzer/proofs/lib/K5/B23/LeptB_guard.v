(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import FarStep.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_LeptB_guard () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z6bits_0C47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z?bits_above_log2C46Stdlib4Bool4Bool;andb_true_rC47Corelib4Init5Logic6eq_indC46Stdlib4Bool4Bool<andb_false_rK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z=pow2_bits_eqbC56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'C56Stdlib6ZArith6BinInt1Z@add_nocarry_lxorC47Corelib4Init5Logic6eq_symK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z3oppC45stdpp9bitvector;definitions8bv_swrapK46Stdlib9micromega7EnvRing5PExpr06C45stdpp9bitvector;definitions?bv_half_modulusC45stdpp9bitvector;definitions>bv_swrap_smallC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions>Z_to_bv_signedC56Stdlib6ZArith6BinInt1Z3mulC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz03K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z9div_smallc69OSSVerify5KrLib2K53B23;LeptB_guard=signed_of_Z64C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01".   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma slt0_nonneg : forall x, 0 <= x < 2^63 -> (Z.lxor x 9223372036854775808 <? 9223372036854775808) = false.
Proof.
ltac2:(KReplay.run1 (kr_t_LeptB_guard ()) [] "p'0h06__sat1h14__p1h24__x1h31bi001bh47__arithh54__ffh66__sat0h78__varmaph85__with91xh:2Hnh;2Hxh<1Hh=2Hah>1ah?1ei011eh@1ni021nhA1yhB1EhC2NEhD2NZhE1ri031rhF1si041shG1zp;1p;2p;3p;7p;6p;4p;8g0000j10Tg000Uj1DTg0013j1:Tg001Xj2GTg0025j21Tg002QR0j2;Tg002lj2CTg003Ij28Tg003ej2WTg004Ej2LTg004cj2FTg005@j2JTg005^j22Tg006?j27Tg006]j33Tg0077j2KTg007Tj2`Tg0086R1j2_Tg008Yj2\Tg0099j1?Tg009RR2j2[Tg00:2j1ITg00:Rj7Zj6<Tg00;0j2YTg00;Xj3XTg00<<j2VTg00<]j2HTg00=7j1UTg00=Wj1RTg00>7j2OTg00>Uj1PTg00?3j1QTg00?^j2>Tg00@Aj2TTg00@dj6vTg00AHj1uTg00Ajj2tTg00BLj2sTg00C8j3rTg00CWj4jTg00DIj1ETg00Dgj3iTg00EMj4@Tg00F8j6hTg00F\j1gTg00G:j3fTg00G]j4eTg00HFj1dTg00Hej7cTg00IAj1bTg00Iaj1aTg00J?j3kTg00Jfj3lTg00KIj3mTg00Klj3nTg00LVj4oTg00M2j3^Tg00MUj7]Tg00N9j7pTg00N]j8qTg00OAR3f0R4'8p=9g00O_R5g00P?R6734p=4%04#0p=S%04#0#0#0p=N%04#0#0#0#0#0#0#0p=5g00P_R7?343p=AP7f1R8g00Q=P4C@p=BP8g00QdR9g00RCR:P:g00RcR;P4g00SCF]p=6f2R<P9P:P:P;P8P4Fpp=Mf3R=P9P:P:P;P<P8P4Gqp==%94R>g00ScR?#0R@#DRA%:?#:#:#:#:RB#DRC'GRD,14RE';RFP01C84#4188<RG[18481C<8#4[RH1C=<#4\G1W84P4n2001000000120000000XA7X97PH^A7^97P4%S@#N#5#5#5#5#5#5#5#DR@,L<RHP@P71F<@RGPH1J<@P5f4RI/2812@8'7123<9354X35P5P6f5R6/2<RJ12@<'7=354X35P51KC8RK17J4#4X351`C8A37C8/_K1KC<P5P1A37C=f8/26R1/78#4P8A37CIRKP7PCf:RJ/28g00THRL'7#4^:>X@7%9CRMP5f9RN/2CRO%44X351\N3%ANRN%?N'[P2%AJRJ%?Jf;RJ/2C#4P4%AJR2P7P3128C#4^;FX971833113DRF';%ICW;f<RNP4PJFZW?P4O1%?2PNPC1YACRN113AR2PF\MRF[RJ%9ARPg00ThRQAXAC8UW=RR%9D\Q^=PRPP8g00UD1V3A'HP2eO1R2PFp-0RQg00UjRS#URT%RSRS1O78RU%P7RV%Q7RW1>73RX1T7?R?'B,6WRYPWP9P:P:P;P=EvRZ5MWR[%u:R\PYC=1tW;RYP4P<1H5L1s4<=35LdAr738CjR5b5b7b8X27W11;>8R]%98R^[^27^1QP4f@R_/1DP_f?O3b4b0b6b01138R`P01GA8,1<%E=/1<[R0%E</181GA<,1=Ra[%EI/1=\aAi<84P8n2001000000120000000UX37X>7P0\`^37^>7P4f=PCPNPJPRPPP2PFPTPSPUPVPWPWP9P:P:P;P7P?g00VVPXC@,6WEhP\PWP[P\P7PXg00W=R;P?C@,6WC=C=PYP5b5b7b8X27X1Q%A4g00Wd[1;^<113<[[^27^1QP4fAR^/1DP^P6P_O4b4b0b6b0PNPJPRPPP2PFPTPSPUPVPWP7P?P;1>7A%gB5f7C@,6WRB9MWZP\PBC=PYP5b5b7b8X27X1Q1;8E118D[^27^1QP4%9^P^P_O3b4b0b6b0O4b<CeWDP4O1n200110400021010111102bF17OL%dOE<W:P6P4PIFcW?P4O1%?K%b1WCP4O1n10210010300021110110102b3bE12D8PNPJPRPPP2PFPTPS%a7PV1>7C,BX,6WPYP5b5b7b8PMP4b4b0b6b09kC8E<1238%I8E<1JI@/28AlI@8E<X:>X@77m39n<@CoA37HGP71F=@18@4XG7PNPJPRPPP2PFPTPSPUPVPWP[P\1>7@R\A^7?\'B,6WC=PYP5b5b7b8X27X1Q1F8@,8@\]^27^1QP4f7RQ/1DPQf6O3b4b0b6b01L=@P4E<bBO3b<W;X97o"). Qed.

Ltac swrap_fix := repeat match goal with |- context [bv_swrap 32 ?z] =>
  rewrite (bv_swrap_small 32 z) by (change (bv_half_modulus 32) with (2^31); lia) end.
Ltac po_fix :=
  repeat match goal with
  | |- context [Z.lxor ?x 9223372036854775808 <? 9223372036854775808] => rewrite (slt0_nonneg x) by lia
  | |- context [?a + ?b <? ?b] => replace (a + b <? b) with false by (symmetry; apply Z.ltb_ge; lia)
  | |- context [?a + ?b <? ?a] => replace (a + b <? a) with false by (symmetry; apply Z.ltb_ge; lia)
  | |- context [?a <? 1] => replace (a <? 1) with false by (symmetry; apply Z.ltb_ge; lia)
  | |- context [?a =? 0] => replace (a =? 0) with false by (symmetry; apply Z.eqb_neq; lia)
  | |- context [0 <? ?a] => replace (0 <? a) with true by (symmetry; apply Z.ltb_lt; lia)
  end; cbn [Z.b2z]; change (Z.lxor 0 0) with 0; change (Z.lxor 0 1) with 1; change (Z.lxor 1 0) with 1.
(* [comment removed for export] *)
Ltac al_fix :=
  repeat match goal with
  | |- context [Z.land ?x 3] => replace (Z.land x 3) with 0
        by (symmetry; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; Z.div_mod_to_equations; lia)
  | |- context [Z.land ?x 7] => replace (Z.land x 7) with 0
        by (symmetry; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia)
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma signed_of_Z64 : forall z, (-2^63 <= z < 2^63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
ltac2:(KReplay.run1 (kr_t_LeptB_guard ()) [] "h02Hah16__sat1h24__x1h31zh42Hzh57__arithh64__ffh76__sat0h88__varmaph95__witp;1p;2p;3p;4p;7p;8p;6g0000j10Tg000Uj15Tg0013j13Tg001Xj2?Tg00XAj1;Tg003Ij21Tg0025j22Tg002Qj24Tg00F\j16Tg00X^j2@Tg006]j39Tg00;0j2=Tg00;Xj3<Tg00<<j2WTg00<]j2:Tg00=7j1VTg00=Wj1UTg00>7j2TTg00>Uj1KTg00?3j1FTg00?^j2ETg00G:j3DTg00YEj2CTg00@Aj2BTg00EMj48Tg00N9j7ATg00AHj1GTg00N]j8HTg00Ajj2ITg00BLj2JTg00C8j3>Tg00CWj4LTg00Yhj1MTg00ZVj3NTg00[Cj2OTg00[ij2PTg00\Qj2QTg00:Rj6RTg00MUj7STf1R0g00QdR1g00RCR2P2g00RcR3f0R4g00SCFSp=7g00P_R5g00ScR6#0R7#5R8%36#3#3#3#3R9#5R:'?R;#;R</14124;'4R=P5%07#0#0#0#0#6R7/@0f2R>9954X351=8:g00OAR?/28R@11?:12?;[RA[11?8RBg00ThRCA<8:0UW011?;\C^0BP0g00UD1W?8':P@eO1PAg00UjRA#V%UA1T50%K5%F5RAP1P2P2P3PAP1P2P2P3P51E58%695D5R9,C5g00Q=1B56R6C8,7AP5P6g00W=P9C8,7AFAR9%G2P9GH1IA3P4P>g00O_RAg00THR3':1J4>=9A3dA>5?0CLb6b8b9X2511<0120;'4\=^25P4f5f4O2b5b1b7b1%M7R4#;/101204'4e9N701O70,P71Q70ERW4W3o"). Qed.
Lemma mulh_guard : forall a b, 0 <= a < 2^31 -> 0 <= b < 2^31 ->
  bv_eqb (Z_to_bv 64 (bv_signed (Z_to_bv 64 a) * bv_signed (Z_to_bv 64 b) / 18446744073709551616))
         (Z_to_bv 64 (bv_signed (Z_to_bv 64 (a mod 18446744073709551616 * b)) / 9223372036854775808)) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_LeptB_guard ()) [] "h06__sat1h14__x1h27__arithh36__sat0h46__sat3h54__x2h61zh72Hah84__ffh98__varmaph:5__with;6__sat2h<2Hbh=1ah>1bp;1p;2p;3p;4p;5p;6p;7p;8g0000j10Tg000Uj13Tg0013j11Tg001Xj2\Tg00F\j1PTg00[Cj26Tg00[ij2FTg00]>j2=Tg00][j3ETg00<]j2VTg00^Hj2QTg00;0j2ZTg0025j2NTg00;Xj3[Tg00<<j2iTg00^ej2WTg00_Fj4dTg00_gj3cTg00`Hj2bTg00a1j1HTg00aPj2CTg00b9j2MTg00=7j1aTg00bej3LTg00=Wj1`Tg00>7j2UTg00Iaj1{Tg00cEj4zTg00>Uj1yTg00?3j1xTg00?^j2OTg00AHj1wTg00ccj5vTg00G:j3^Tg00@Aj2]Tg00dGj3qTg00Ajj2pTg00BLj2oTg00C8j3nTg00CWj4mTg00djj3YTg00:Rj6DTg00YEj2lTg00XAj1kTg003Ij2RTg00eMj2STg00fRj2jTg00g2j3hTg002Qj2gTg006]j3rTg00gUj2sTg00h>j3tTg00hgj3uTg00EMj4XTg00MUj7_Tg00N]j8TTg00N9j7eTg00OAR0f0R1'Rp=7%11#1p=|f2R2f1R3/N1'gp=:%01#0#0#0p=?%01#0#0#0#0#0#0#0p=B%01#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=51Q31,62p=9g00O_R4g00THR57r1p=A%11#1#1#1#1#1#1#1p=f%11#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=K%01#0p=Gg00P_R6/s1p=8At631p=2Au631p=4P2g00QdR7g00RCR8P8g00RcR9P6P3g00Q=P1CXg00SCR:F_p=;f6R;P7P8P8P9f5R<f4R=f3R>P7P8P8P9P2P3P1GTGTp=JP6P3g00W=P1CXp=@P3P7P8P8P9P1P:F_p=>P2P7P8P8P9P3P1Fep=<P>P7P8P8P9P2P3P1GTp=I%73R:g00ScR?#0R@#3RA%1?RB#1#|RC#3RD'\RE7:3RFP6P>%0@#?RG#PRH16H=,FH16H>,FHRI'=%BG#5RG#0#5#5RJ#0#3RK59H1=1>,6H,FH%3JRJ59H3E#AX66P6P>1=1I=9HK1==>RL,6H,FH=9HJRM5EH#AX66P6P21==1=9HK=EHM#AX66P61=>2RMA9HLKA9H1J5EH#AX66P6P016H1RNA9HLJ5EH#AX66P6P016H0=EHN#AX661V45R51QMJ1ZADR41N0ARN%7D1N0E[RL[RO%7ARPg00ThRQA[AD3UW7RD%7E\QRR^7PRSP3g00UD1i0A'VPNeRTO1RUPLg00UjRV%1CRW#f#KRX#1RY#0#G#?#B#5#3#8RZP6%3?,W6P?1W60Cd9c6?,b6g00iPR[#HR\,C6R]'2'2R^%KG#KRG#3#8%H\R\#HR_#HR`#H,C6Ra1C6[R['2Rb'2%0X#G#?#B#5#1#0#G#?#B#5#3#81C6`R`1C6_R_'2'2RX%0G#G#?#B#5#3#812`]R]'212`[,2ZRZ'4'4'4'4g00ioR['M1C6\/2`,2a/4b/M[%aVR`5LVR\3L%`VRGP61U62P3%{6CzRc%y6Rd%x6RePe1O60Rf1O6ARg5;eRh%w8RiPePeP7P8P8P9DvR8Pi%PC9^6gRC9;efFJR7PiPe1]6@R@9;ef1@@C,>e5<eRjPiPe1]6?R?9;efRk1@?C,>e5<eRCPiAq6?@R@9;efRl1O6J,@@,>e5<eCIFJ1pe9R9P1P2P51o12#AdAn603CmR5b8b9b:X16X56PR\PRR%72?:2ERm1=>=Rn#7Ro?:nJ\m[[^16^56P1P;f7R;P2P=P<O5Rpb2b0b3b09YMJED1QMKP4POPDPSPUPL%GB#?#B#5#K#KRB#3#8/2b%0B#G#?#B#5#3#8/2]/4Z,4X'4,4^/M[=LV\PGPcPdPeP7PiPePjPiPePCPi1O6KR7,@@,>e9<elCIFJP9P5b8b9b:X16X56A:onK\m\m\R^16^56Ppb2b0b3b09YMKED16HM,FH%3WRp,ZARR%7p1\ApRo,N0[R0\NRNA[Ap3VQX7PRp%7o\QRQ^7PRAP4POPDPSPUPLP=PTO1RTP0%3Y#812a_'2%8J/2],4b'4/M[=LV\PGPcPdPePePhPiPeP8Pi%PW9^6gRg9;efFJPiPePjPiPePCPi1l6gRj=;e@1@@g,>e5<eCIFJP9P5b8b9b:X16X56PQ\P%koRP/Rn?:no\m\m[^16^56P1f9Rmf:RnP<P;f8RQO5b2b4b0b3b0b;b4,SMED16H2,FHPRPNPpPAP4POPDPSPUPLPTP0P`PG1U63RHPdPePCPiA;ej?1@?g,>e5<eCIP9P5b8b9b:X16Rg%71?:1ERE1RP3?:3o[^16RoP1PmP;O2b2b4b0b3b0b;b4,S2EDPIPRPNPpPAP4POPDPSPUPLPTP0PgPoP1PnPQO2b2b4b0b3b0b;b4,S>ED1j>KP4POPDPSPUPLP`PGPHPdPePCPi1@?7,>e9<ekCIP9P5b8b9b:X16A::3K\E^16P1P;P<O2b2b0b3b09h>KEDX<FW7X>6X=6o"). Qed.
Ltac mulh_fix :=
  lazymatch goal with
  | |- context [bv_signed (Z_to_bv 64 _) * bv_signed (Z_to_bv 64 _) / 18446744073709551616] =>
      (* [comment removed for export] *)
      repeat match goal with
      | |- context [bv_signed (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 ?w) * _)) * bv_signed (Z_to_bv 64 _) / 18446744073709551616] =>
          rewrite (unsigned_lit w) by lia
      end;
      repeat match goal with
      | |- context [bv_eqb (Z_to_bv 64 (bv_signed (Z_to_bv 64 ?a) * bv_signed (Z_to_bv 64 ?b) / 18446744073709551616)) _] =>
          rewrite (mulh_guard a b) by lia
      end
  end.
Ltac guard_fix := try sx32_fix; swrap_fix; po_fix; al_fix; try mulh_fix.

(* [comment removed for export] *)
Ltac gwalk1 :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [ shbr | shbr0 | shbr_inv | shbr_x3 | br | progress guard_fix; br ]
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => first [ shload; lstep; clear_shl | special_step | frame_step | lstep; try sb_fix; try fix_land32; shnorm ]
  end.
Ltac gwalk stops := repeat (tryif at_stop stops then fail else gwalk1).
Ltac show_pc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.

(* [comment removed for export] *)
Ltac awalk1 ::= gwalk1.
Ltac cwalk1 ::= gwalk1.
Ltac lwalk1 ::= gwalk1.
