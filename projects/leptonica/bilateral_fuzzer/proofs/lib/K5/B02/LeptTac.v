(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_LeptTac () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions8bv_swrapI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr06K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC45stdpp9bitvector;definitions>bv_swrap_smallC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions>Z_to_bv_signedC47Corelib4Init5Logic8eq_ind_rK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z3divC35stdpp7tactics<f_equal_helpC69OSSVerify5KrLib2K53Lib3Mem3sxbC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z4lnotC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z5ldiffC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z6shiftlC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z<ldiff_ones_rC56Stdlib6ZArith6BinInt1Z:ldiff_landC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z:land_assocK47Corelib4Init9Datatypes4list02C45stdpp9bitvector;definitions7bv_wrapK47Corelib4Init5Logic2ex01C46Stdlib6ZArith:Znumtheory<Zmod_div_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib2K53Lib3Mem<Z_to_bv8_modC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC69OSSVerify5KrLib2K53Lib3Mem3le1C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_addI47Corelib4Init5Logic5False00I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib2K52AG6Shadow3accC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t03C69OSSVerify5KrLib2K52AG6Shadow4shadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow5sh_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib2K53Lib3Mem2waC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init3Nat3addC47Corelib4Init9Datatypes6lengthC69OSSVerify5KrLib2K53Lib3Mem@bytes_at_ov_readC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z7add_0_rK47Corelib4Init5Logic3and01C69OSSVerify5KrLib2K53Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC46Stdlib9micromega;ZifyClasses5mkrelC69OSSVerify5KrLib2K53B026ImageA5asegsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_lec69OSSVerify5KrLib2K53B027LeptTac3shkC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02c69OSSVerify5KrLib2K53B027LeptTac9acc_read1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03c69OSSVerify5KrLib2K53B027LeptTac8shk_readC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof01C69OSSVerify5KrLib2K52AG6Shadow3SHBC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indI47Corelib4Init5Logic2or00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegc69OSSVerify5KrLib2K53B027LeptTac:shad_rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses8or_morphC69OSSVerify5KrLib2K53Lib9StoreFastFbytes_at_write_other_nC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst7Inj_Z_ZC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics5Riscv3Sem7reg_getK47Corelib4Init5Logic4True01".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac addr_near k ::=
  let inb := eval vm_compute in (andb (Z.leb 0 k) (Z.ltb k 4608))%Z in
  lazymatch inb with true => idtac end.

(* [comment removed for export] *)
Definition hid (P : Prop) : Prop := P.
Ltac hide H := let T := type of H in change (hid T) in H.
Ltac unhide_all := unfold hid in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma signed_lit64 : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
ltac2:(KReplay.run1 (kr_t_LeptTac ()) [] "h02Hah16__sat1h24__x1h31zh42Hzh57__arithh64__ffh76__sat0h88__varmaph95__witp;1p;2p;3p;4p;7p;8p;6g0000j10Tg000Uj1:Tg0013j12Tg001Xj2>Tg0025j1VTg002Rj21Tg002nj23Tg003Jj27Tg003ej18Tg004Cj2?Tg004jj39Tg005Dj2<Tg005lj3;Tg006Pj2UTg0071j24Tg007Kj1TTg007kj1LTg008Kj2KTg008ij1FTg009Gj1ETg00:2j2DTg00:Uj3CTg00;8j2BTg00;[j2ATg00<>j46Tg00<ij7@Tg00=Mj1GTg00=oj8HTg00>Sj2ITg00?5j2JTg00?aj3=Tg00@@j4MTg00A2j3NTg00A_j2OTg00BEj2PTg00Bmj2QTg00CZj6RTg00D8j7STf1R0g00D\R1g00E;R2P2g00E[R3f0R4g00F;FSp=5g00F[R5g00G9R6#0R7#:R8%26#2#2#2#2R9#:R:'>R;#VR</14134;'7R=P5%07#0#0#0#0#8R7/?0f2R>9954X351<8:g00G^R?/38R@11?:13?;[RA[11?8RBg00H<RCA;8:0UW011?;\C^0BP0g00HX1U?8'4P@eO1PAg00I>RA#T%LA1K50%F5%E5RAP1P2P2P3PAP1P2P2P3P51D58%895C5R9,B5g00Ij1A56R6C6,5AP5P6g00JQP9C6,5AF@R9%G2P9GH1IA3P4P>g00K8RAg00KXR3'41J4>=9A3dA=5?0CMb6b8b9X2511<0130;'7\=^25P4f5f4O2b5b1b7b19N701O70,P71Q70ERW4W3o"). Qed.

Lemma sxb_small : forall b : byte, bv_unsigned b < 128 -> sxb b = Z_to_bv 64 (bv_unsigned b).
Proof.
ltac2:(KReplay.run1 (kr_t_LeptTac ()) [] "h06__sat1h14__x1h22Hah37__arithh44__ffh54__p1h66__sat0h78__varmaph85__with92Hbh:1Rh;1bh<1zp;1p;2p;3p;4p;6p;8p;7g0000j10Tg003ej1CTg00L8j1>Tg00L[j25Tg000Uj17Tg002nj21Tg00A_j1Uj2YTg00BEj2?Tg0071j2:Tg00MEj2HTg00N8j1ETg003Jj2;Tg00Naj28Tg00O>j2<Tg004jj33Tg005Dj2XTg001Xj2BTg005lj3VTg006Pj2TTg007Kj1STg007kj1RTg008Kj2NTg008ij1MTg009Gj1LTg00;[j2KTg00:2j29Tg00O[j3JTg00P>j3ITg00<>j44Tg00>Sj2GTg00?5j2FTg00?aj3OTg00@@j4PTg00Paj2@Tg00QAj6QTg00=Mj1DTg00Qej3bTg00CZj6aTg00RHj1`Tg00Rfj2_Tg00SCj8^Tg00S`j1\Tg002Rj2ZTg00D8j7[Tg00<ij7WTg00=oj8]Tg00G^R0f0R1'Zp=2f1R2g00D\R3g00E;R4P4g00E[R5P1g00F;F[p=6f2R6P3P4P4P5P2P1FWp==f3R7P3P4P4P5P6P2P1G]p=Ag00G9R8#0R9#0#0R:#CR;#>15;1%0:#0#0R<#0R=#7R>'1g00F[R?%C<R<#>R@%U<RAPA1?;215;2RBP@\?/:A1H;2%2B%E;,1B';P?15;6RA/8>RC1<1>15;753?X<?%79R9%7:R:'XRD1109RE%2:1B9:RF,10[RG[RH%29RIg00H<RJAV9:2UW2R:%2F\J^2IRIP2g00HX1T09':PEeO1REPGg00I>RJ#SRK%RJRJ1N?2RL%M?RM%L?RNP?1K?8R819?>RO5J?RP=I?Og00TSP8C4'61GN5RQP1P6g00K8RRg00KXRS':1F16=3RSdAO?02CPRSb4b7b8X1?181>/<>=3?1^1?P1f6,5;RRO1b3b0b6b0%0=#7R=,@CPDPHP:PIPEPGp-0RGPKPJPLPMPNP?19?0R0g00IjRMP8C4,6NPNP3P4P4P5P7EQ5=N%D4R4PNP?P8g00JQR8POC4,6NP4P?P0PMPPC4,6NP?PPP819?=C4,6N5=NCACAPQPSb4b7b8X1?W5%21/;2112>186>R>#211>=';[[^1?^5GP111RFPRf4f5O4b3b0b6b09bC=Ea%`;,B9R=/_9R9,8A/@=/<9=3?Ae1?;6=3?Aeb:G^%\21Y<B53@eW9W;o"). Qed.

Lemma land7 : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof.
ltac2:(KReplay.run1 (kr_t_LeptTac ()) [] "h02Hxh17__arithh24__ffh38__varmaph45__with51xh61zp;2p;1p;3p;4p;7p;6g002Rj26Tg0000j12Tg000Uj11Tg0013j17Tg001Xj2GTg00Paj20Tg004jj33Tg0071j24Tg00U:j1<Tg00UXj2;Tg007Kj18Tg007kj19Tg00V6j1:Tg008ij1FTg009Gj1ETg00:2j25Tg00<>j4DTg00D8j7CTg00>Sj2BTg00?5j2?Tg00?aj3@Tg00@@j4ATg00VTj3>Tg00CZj6=Tg00F[R0g00G^R1f0R2'6P0f1R3g00G9R4#2R5#1%74#1R4'G'0f2R6%25#2#1R5'09302X601035,40%<4,;3g00I>R5#8%95%:0%F0%E0R5g00D\g00E;R7P7g00E[R7P01501g00Ij1504CDg00F;FC1B57P2P6g00K8R7g00KXR5'41?26=375dA@013CAb2b3b41614P2b19>34E=W0W5o"). Qed.

(* [comment removed for export] *)
Lemma land_m32 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551584 = 32 * (x / 32).
Proof.
ltac2:(KReplay.run1 (kr_t_LeptTac ()) [] "h06__sat1h17__arithh24__ffh36__sat0h48__varmaph55__with64__x1h71zh82Hah92Hxh:6__sat2h;1xp;1p;2p;3p;4p;6p;7p;8g0000j14Tg000Uj18Tg001Xj2?Tg002nj29Tg003Jj2BTg00U:j1@Tg0013j1PTg00W7j1LTg00UXj22Tg00Rfj27Tg00WUj2:Tg004jj33Tg00Paj2fTg00X2j2CTg00XQj2YTg00Y1j2=Tg00YQj2VTg005Dj2UTg005lj3TTg006Pj2STg0071j2ATg007Kj1OTg007kj1NTg008Kj2MTg008ij1KTg009Gj1JTg00;[j2ITg00:2j26Tg00ZBj3>Tg00<>j4;Tg00>Sj2HTg00?5j2GTg00?aj3FTg00@@j4QTg00V6j1RTg00Zej3ETg00[Nj3eTg00\7j3dTg00\]j2DTg00]Aj6cTg003ej1bTg00:Uj3]Tg00<ij7ZTg00=Mj1[Tg00=oj8\Tg00Qej3XTg00VTj3WTg00]]j3^Tg002Rj2_Tg00D8j7`Tg00CZj6aTg00G^R0f0R1'_p=0f1R2g00D\R3g00E;R4P4g00E[R5P1g00F;F`p=5g00F[R6P2g00IjP1C;p=<P6f4R7f3R8f2R9P2P1Eap=1%01g00G9R:#4R;#8R<%4;#4#4#4R=#4R>#8R?'?R@,91'BRA%@?RB%P;#8R;#@RC#LRD'2RE1291%8=R=179=':RF536X76122BRG/2DA361FX76RH1f2@RI121D=36FX76RJP2PJP61C2CRJPH1Y2;RK/=;PH1?<;RL,72RM1=1;=36FX761:MLPH1V2=%02RH%0=178=#0[[1U<?R8190<RL%0?RF190@[RN[RO%0<RPg00H<RQAT<?2UW8RR%0@\Q^8PRPP2g00HX1S0<'APLeO1RLPNg00I>RQ#ORS%NQRQ1M62RT%K6RU%J6RVP61I6:R:166=RW5>6g00TSA>6W:C;'51HV5RWP1P9g00K8RXg00KXRY'A1G19=3XYdAF602CQRYb2b4b5X661:1=1:=1536^66P1f6/7=O1b1b0b3b0b:1=M;P8POPRPPPLPNPSPQ%R6R=PU1660R0166;'<,5VPWPYb2b4b5%0;P1b1b0b3b0RX9EM;D1PKAe2;XD1PJAd2;XD1122D1D2CEcPIP8POPRPPPLPNPSPQPTPUPVP3P4P4P5PVP3P4P4P51<0:,5VP6P:g00JQ166<%b>5]6C;,5VFZR>%[4P>G\PWPYb2b4b5X66192@,BH\A^66P1f5P7O2b1b0b3b09X2@D1PGP8POPRPPPLPNPSPQP=PU166?,<0,5VPWPYb2b4b5PFP1b1b0b3b09W2?D1122EA^2BDD11CBC1DBCD1W9X;6o"). Qed.
(* [comment removed for export] *)
Ltac fix_land32 :=
  repeat match goal with
  | |- context [Z.land ?x 18446744073709551584] =>
      first [ replace (Z.land x 18446744073709551584) with x by (rewrite land_m32 by lia; Z.div_mod_to_equations; lia)
            | replace (Z.land x 18446744073709551584) with (x + -16) by (rewrite land_m32 by lia; Z.div_mod_to_equations; lia) ]
  end.

(* [comment removed for export] *)
Lemma le1_lit : forall z, le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
ltac2:(KReplay.run1 (kr_t_LeptTac ()) [] "h02Hah16__sat1h21zh37__arithh44__ffh56__sat0h68__varmaph75__witp;1p;2p;3p;4p;6p;8p;7g0000j10Tg003ej1ETg00L8j1PTg007kj1>Tg00A_j28Tg00L[j2WTg00^Aj2@j1Nj3ZTg007Kj1?Tg0071j22Tg00^aj2ITg000Uj15Tg001Xj26Tg00Paj23Tg004jj31Tg005Dj2DTg002nj27Tg002Rj24Tg005lj3ATg006Pj2VTg00V6j1UTg008ij1TTg009Gj1OTg00:2j2;Tg00:Uj39Tg00<>j4=Tg00>Sj2MTg00?5j2LTg00?aj3KTg00@@j4JTg00WUj2:Tg0013j1CTg00_Gj4HTg00_aj6GTg00]Aj6QTg00`Ij2RTg00CZj6FTg00a8j3STg00SCj8BTg00b4j1\Tg00bSj2[Tg00cPj1YTg00D8j7XTf1R0g00D\g00E;R1P1g00E[R1f0R2g00F;FXp=<g00F[R3g00G9R4#0R5#0#0R6#ER7#PR8#>R9P9%06#0#0R:#ER;18;2R<'WR=,87R>,@81872R?,@8%?8R@P@P8P9\9RA%N8RBPBP>P?PA\8/2BP31I;2RB%55R5%56R6'6RA,32R>130ARC513X23P3P>A132CX23123>%5:R:,65RC,32/3APAPCP21D56g00G^RD/75RE14D617DARF[RG[14D5RHg00H<RIAA560UW014DA\I^0HP0g00HX1VD5'2PEeO1R6PGg00I>RG#?RJ%>GRG%U3RK%T3RL%O3RMP31;3DRNg00JQRO1;35RP=937C='<1MM1R1P2f2R7g00K8RQg00KXRR'21L27=1QRdAK3D0CJRRb4b6b7PFP2b3b1b5b11D5:14D:17DCRF[RQ\EAA5:0VIX0H14DC\I^0HP6PQPJPGPKPLP3PNPOA93P;C=,<MP1PRb4b6b7PFP2b3b1b5b1P31:2A913CX23%C4#C#0#0#0#5,65R51:5A,23CHEGEQ13BA=13>eP=1R;2EF9S=2GB129@GBg00dC#\/[=AZ8?@R@519e%Y<=19@eW2o"). Qed.
Ltac sb_fix := lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) => rewrite (le1_lit z); mem_after_store
  end.

(* [comment removed for export] *)
Lemma unsigned_lit_neg : forall e, - 2^63 <= e < 0 -> bv_unsigned (Z_to_bv 64 e) = e + 2^64.
Proof.
ltac2:(KReplay.run1 (kr_t_LeptTac ()) [] "h02Hah16__sat1h26__sat3h37__arithh44__ffh56__sat0h66__sat2h78__varmaph85__with94__x1h:2Heh;1eh<1zp;1p;2p;3p;4p;8p;6p;7g0000j11Tg000Uj17Tg0013j12Tg001Xj2=Tg0025j1`Tg002Rj2?Tg002nj23Tg003Jj2<Tg003ej19Tg00^aj2HTg00Naj28Tg004jj36Tg00WUj2DTg00Paj2CTg005Dj2BTg005lj3@Tg006Pj2VTg0071j2>Tg007Kj1UTg007kj1TTg008Kj2NTg008ij1LTg009Gj1KTg00:2j2;Tg00:Uj3:Tg00;8j2JTg00;[j2ITg00<>j44Tg00=Mj1GTg00O[j3FTg00=oj8MTg00>Sj2ETg00?5j2OTg00?aj3PTg00@@j4QTg00Qej3RTg00V6j1STg00dbj6_Tg00eFj4^Tg00]Aj6]Tg00A_j2ZTg00L[j2YTg00`Ij2XTg00CZj6WTg00D8j7[Tg00<ij7\Tg00G^R0f0R1'?p=0f1R2g00D\R3g00E;R4P4g00E[R5P1g00F;F[p=5f2R6P3P4P4P5P2P1F\p=Ag00F[R7g00G9R8#1R9#7R:%28#2#2#2#2R;#7R<'=R=#`/?11310'<R>P7%19#1#1#1#1R9#9R?/H2R@%79R9,=:RA,869671X<7RBP7%78RC/DA,82/CAPB182ARB1B:<RD130:RE%0<130=[RF[RG%0:RHg00H<RIA@:<2UW0R<%0=\I^0HR=1B:9RJ%09130A[RK\ERLA@:92VIX0HR9%0A\I^0HRHP2g00HX1V0:'>PEeREO1RIPKf4PEO1REPFg00I>RM#URN%TMRM1N72%L7RO%K7RPP3P4P4P5P71;7:R:%9;5:7,J7g00IjR;1I78R8C4,5PP7P8g00JQRQ1;70RRC4,5P5AP%G4P7PRP;A:7:?R:9F78R8C4,5PP7P8PQP:C4,5P5APGM1EP5RQP1P6g00K8R8g00KXR;'>1O16=68;dAP702CQR;b4b7b8X97%0B13BA'<\>^97P1f8f7O2b3b2b1b5b1b6b27RA1C2AP2PCPAPDPGP<P=PJPLP9PHPIPKPEPFPNPM%S7POPPP3P4P4P5P7P:g00TSPRC4,5PE_PQP;b4b7b8A67A0g00eg[P1b3b2b1b5b1b6b2C^E]A67@Be1Z?2,Y?1X?2EWW:W;o"). Qed.

Ltac cnorm :=
  unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb];
  change (bv_unsigned (Z_to_bv 64 0)) with 0;
  fold_lit_ux;
  repeat match goal with
  | |- context [Z.land ?x 7] => rewrite (land7 x) by flia
  end;
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] => first [ rewrite (inr64_unsigned_lit e) by zrange | rewrite (unsigned_lit_neg e) by flia ]
  | |- context [bv_signed (Z_to_bv 64 ?e)] => rewrite (signed_lit64 e) by flia
  end.
Ltac brT := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with true; [cbv iota| symmetry; cnorm; solve_cond_rec] end.
Ltac brF := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with false; [cbv iota| symmetry; cnorm; solve_cond_rec] end.
Ltac br := first [brT | brF].
Ltac brfork H := if_cases H; zify_cond H.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation mem := (word -> option byte).

Lemma acc_read1 : forall (m : mem) a n x, acc asegs m a n -> a <= x < a + n ->
  exists b, ov_read_bytes asegs m (wa (shad x)) 1 = Some [b] /\ sh_ok b x.
Proof.
ltac2:(KReplay.run1 (kr_t_LeptTac ()) [] "p'0h01bh14__x1h24__x2h37__arithh44__ffh58__varmaph65__with71zh82H0h92Hbh:3Hokh;1Rh<4__x3h=1Hh>2Hxh?1ah@1ehA1mhB1nhC1xi001xp;1p;4p;2p;3p;8p;6p;7p;<g0000j17Tg003ej1RTg00L8j1MTg00fDj1HTg00ffj4oTg002RR0j2>Tg00Naj2<Tg002nj2?Tg003JR1j24Tg00O>j2@Tg007Kj1ITg007kj1GTg008Kj2FTg00g[j4QTg008ij1mTg009Gj1iTg00;[j2CTg0013j1\Tg00O[j3NTg00<>j4=Tg00=Mj1YTg00:2j2KTg00P>j3XTg00=oj8WTg00>Sj2VTg0071j2JTg00?5j2UTg004jj33Tg00?aj3TTg00@@j4STg00h9j11Tg00^Aj36Tg00hoj20Tg00ifR2j2ATg00j@j19Tg00b4j1nTg00k2j2;Tg00V6j1lTg00CZj6PTg00kTR3j2OTg000Uj1hTg00knj4bTg00lYj2aTg00m0j2`Tg00mPj8_Tg00nPR4j1^Tg00o0j3BTg00oNj3DTg00omj1]Tg00]Aj6cTg010Nj4dTg00_Gj4[Tg00D8j7fTg00<ij7gTg010ij4ZTg011aj4jTg012fl<kTg00F[R5f1R6g00Ijf0R7C=p=EP6g00D\R8g00E;R9P9g00E[R:P7g00F;Ffp=8f2R;P8P9P9P:P6P7Fgp=L1@67,<;p=2g013KR<P;P6P7CZp=5P<P;P6P7Cjp=:g014CP5P3P4P0g014bf5R0f4R4f3R3P;P6P7M<kp=eg00G9R=#7R>#7#7R?#7#7#7#R#M%R?#MR?#H[P<P3P;P6Co1>361<3;,?6'4P61@;4g00I>R@#IRA%G@R@P51F5;RBP61F53CQ%m5RC%i5RDP8P9P9P:1C5>R>1C5=R8'E,8DP5P8g00JQRE%\=,C5RF9N5>C=,8D5LD%Y9g00G^R9,K5AX58>RG'E,8DP5PGPEPFC=,8D5LDGW1VD:R:P7P;g00K8RFg00KXRE'J1U7;=3FEdAT596CSREb4b5b6X15X25X<51>671<6;,?7'41@6;R;,>91?;3'4[^15^25^<5P7P4P0P3P6O4b3O2f6R;A2030RF#1%I?RH96?7RI35107F'4X0?,A?P2P?f7R2A2;4;RF#1;5I107F'4X0?%G?RF#HRJf8RK%10#9g00dCRL#nRM3:1;FIRN331070'4X0?,A?P7f9R0A2K;KRO#1;5I107O'4P1f:R1A2020RO#1A6?6H35106Of<RO%10#9;:M=3JN1070'4X0?,A?P7f;RI?20I#1A6?3H55OA2O1O,04PAP@P5PBP6%l5RBCQPCP5P8g00TSAN5>GC=,8DP:PEb4b5b6X15X25A26769357^15^25P7f>RGPOO2b3f=R>?2I>935IP5A2GOG1027X75P6POP7EP10;OP5f?RO?2>OfAR;%17A6?KHRI35X75P3P>P6EPf@%1>A6?2H35P?fB%1OR2#9;:MR>=3JN107O'4X0?PK%1GRO#9=:;M1;FI53J10KGP<P;POPIPLPMP71OMM%h=R=/>=R<PMP=1J5=RGPMP=PGEePAP@PBPC1K5=R=/E=,8DP:PEb4b5b6P<P7b3Cb1aLM1`?I'OeG_%^L,<O#9=:;MAB?LI9D?M,;F53JP51<29fC%97;:MA6?1H9B?L9D?M,;F53JX75P7P2%]2EcA6?0H9B?L9D?M,;F93J>P7b;b;P6CdC[b9b:b8W:W9P6P7O2n2001000000121000000W8X0?P6P7O2n2001000000121100000b@W>W=XC5XB5X?5WAo"). Qed.

(* [comment removed for export] *)
Definition shk (m : mem) (b : byte) (X : Z) : Prop := bytes_at asegs m (shad X) [b].

Lemma acc_shk : forall (m : mem) a n x, acc asegs m a n -> a <= x < a + n -> exists b, shk m b x.
Proof.
ltac2:(KReplay.run1 (kr_t_LeptTac ()) [] "p'0h01bh14__x1h24__x2h32H0h42Hbh57__arithh64__ffh78__varmaph85__with94__x3h:1Hh;2Hxh<2_Hh=1ah>1eh?1mh@1nhA1xi001xhB1zp;1p;4p;2p;3p;8p;6p;7g0000j14Tg003ej1ETg00L8j1BTg00fDj1KTg00ffj4\Tg002Rj2>Tg00Naj2<Tg002nj2;Tg003JR0j23Tg00O>j29Tg007Kj1ATg007kj1ITg008Kj2FTg00g[j4GTg008ij1VTg009Gj1UTg00;[j2=Tg00<>j47Tg0013j1TTg00O[j3DTg00=Mj1STg00:2j2RTg00P>j3QTg00=oj8PTg00>Sj2OTg0071j2NTg00?5j2MTg004jj3:Tg00?aj3LTg00@@j4JTg00h9j11Tg00^Aj36Tg00hoj28Tg00ifR1j2@Tg015Dj3?Tg00V6j1HTg00CZj6[Tg00_Gj4ZTg00D8j7YTg00<ij7WTg010ij4XTf1R2g00D\R3g00E;R4P4g00E[R5f0R6g00F;FYp=5f2R7P3P4P4P5P2P6FWp=C1926,<7p=0g013KR8P7P2P6CXp=2g00G9R9#4R:#4#4R;#4#4#4#E#B%E;#BR;#K[g00F[R<P8f3R8P7P2C\1>821<87,;2'3P2f4R=,97g00I>R>#AR?%I>R>P<1F<7R@P21F<8CG%V<RA%U<RBP3P4P4P5P<1=<:R:g00IjR31=<9RCC7,5BP<PCg00JQRD%T9,=<R99D<:C7,5B5CB%S4P<g00G^R4,R<P3AQ<C:R3C7,5BP<P3PDP9C7,5B5CBGP1OB5R5P6P7g00K8R9g00KXRD'N1M67=:9DdAL<42CJRDb6b7b8X1<X2<X9<1>261<27,;6'31927R9,>41;98'3[^1<^2<^9<P6P=f5R9P8P2O4b5O2f6R4A0989RE#1%A;RF96;6RG32186E'3X0;,@;P1P;f7R1A04=4RE#1;2G186E'3X0;f8RE??69X0;,@;P6f9R9A0E4ERE#1;2G186E'3P0f:R0A0919RE#1A6;2F32182Ef<RE??69X0;,@;P6f;RG?09G#1A6;8F52EA0E0E,8=P?P>P<P@P2%H<CGPAP<PCg00TSAD<:3C7,5BP5PDb6b7b8X1<X2<A02629:<6^1<^2<P6f>RDPEO2b5f=R5?0G59:<GP<A0DEDf@%16A6;1F32XB<P7PEP6E[f?%1EA6;4F32P;fA??6DX0;P1P6CZb4b3W<W4P2P6O2n2001000000120000000W3X0;P2P6O2n2001000000121100000b>W;W:XA<X@<W=W?o"). Qed.
Lemma shk_read : forall (m : mem) b X, shk m b X -> ov_read_bytes asegs m (wa (shad X)) 1 = Some [b].
Proof.
ltac2:(KReplay.run1 (kr_t_LeptTac ()) [] "h01Rh12Hbh21Xh37__arithh44__ffh58__varmaph65__with71bh81mh91zp;1p;3p;2p;4p;7p;8p;6p;<g0000j10Tg003ej1@Tg00L8j19Tg00fDj18Tg015Dj3WTg00h9j1<Tg007Kj1;Tg00^Aj32Tg00b4j1ETg00kTR0j2>Tg000Uj1CTg002RR1j2BTg0071j2?Tg007kj1=Tg00V6j1UTg008ij1RTg009Gj1QTg00:2j2PTg00<>j4OTg00D8j7NTg00>Sj2MTg00?5j2JTg004jj31Tg00?aj3ITg00@@j4FTg00knj4GTg00lYj2HTg00m0j2DTg00mPj8KTg00nPR2j1LTg00Naj2:Tg00j@j13Tg011aj46Tg00o0j35Tg00oNj34Tg00k2j27Tg00omj1ATg00]Aj6STg012fl<TTg014Cg00F[R3P0P2P1g014bf5R1f4R2f3R0f2R4f1R5f0R6M<Tp=Vg00G9R7#0#0#0R8#0#0#0#@#9%@8#9R8#8[AW456g013KR9P0%<5R:%;8R;9284R<g00dCR=%E=R>P61>>>%C7R7/B7R?P>P71?37R@P>P7P@EVg00I>R@#;%=@%U3%R3%Q3R@g00D\g00E;RAPAg00E[RAP31P37R7g00IjP7COg00F;FN1M@AP6P4g00K8RAg00KXR@'?1J64=1A@dg00G^R@=I35CFb4b5b6P?P6b3CG1H=>1D8<'>eGK%=8R?#8R5P9P0%L=,::#3P>C6A58=<948>,7?31P3%<4R4/:@P9P1%36P>C6A282;958=948>,7?515X93P6P4%A4ESP9P2%34P>C6A280;958=948>,7?515P6b0b0W1X23X78W8o"). Qed.

Lemma shk_ok : forall (m : mem) a n X sz b, acc asegs m a n -> shk m b X -> a <= X -> X + sz <= a + n -> 0 < sz ->
  X mod 8 + sz - 1 < 8 -> 0 <= X -> sh_ok b (X + sz - 1).
Proof.
ltac2:(KReplay.run1 (kr_t_LeptTac ()) [] "p'0h02H0h14__x1h24__x2h34__x3h44__x4h52OKh61Rh71bi001bh83H11h92H6h:7__arithh;4__ffh<4__p1h=8__varmaph>5__with?4__x5h@4__x6hA4__x7hB2b'hC1ehD1EhE1HhF2H1hG3H10hH3H12hI3H13hJ3H14hK2H2hL2H3hM2H4hN2H5hO2H7hP2H8hQ2H9hR1KhS1XhT6__sat6hU1ahV1mhW1nhX1oi011ohY1qhZ2q0h[1rh\2r0h]2szh^1zi021li031xp&0p;1p;4p;3p;2p;6p;7p;8g0000j1BTg003ej1cTg00L8j1YTg00fDR0j1UTg00ffk408Tg015Dj3}Tg002Rj2=Tg00Naj24Tg002nj21Tg000Uj1bTg00Paj25Tg016;k307Tg00b4j1CTg016lj2aTg017Uj2OTg007Kj1^Tg00^Aj3JTg007kR1j1[Tg008Kj2ITg00V6j1nTg008ij1lTg009Gj1jTg00:2j2PTg0013j1RTg00=Mj1fTg00;[j2TTg00P>j3MTg00>Sj2eTg0071j2dTg00?5k206Tg004jj33Tg00?ak305Tg00@@k404Tg003JR2j26Tg018Ak602Tg00h9j19Tg00hoj2:Tg00ifR3j2|Tg019>j2_Tg019_j1xTg00Rfj2FTg00WUj2NTg01:8j2]Tg01:_j2WTg01;Fj2VTg01;lj2\Tg006Pj2vTg01<Rj1uTg01=0j2tTg01=Qj3ZTg01>:j2sTg01>cj3qTg01?Lj2pTg00QAj6oTg00dbj6rTg00ZBj3XTg00]Aj6`j7kTg01@8j4mTg01A4j6wTg00O>j2yTg01AQj3zTg00g[j4{Tg00<>j4STg00D8j7~Tg00O[j3iTg00<ik700Tg00=ok801Tg00j@j1hTg011aj4gTg00k2k203Tf2R4f1R5'4f0R6'yp=0g00G^R7/=6p=Dg00F[R8/a6p=EAz856p=7P8P4P5P6C{p=A1T86p=@P8P5g00JQP6CSp=HP5g00D\R9g00E;R:P:g00E[R;P6g00F;F~p=2Ai856p=<P8P5g00IjP6CSp=GP4P9P:P:P;P5P6K00p=Lf3R<P9P:P:P;P4P5P6L01p=8g013KR=P4%h5P6Cgp=>AJ456-03<p=?A3867p=QA3856p=;P8P5g00TSP6CSp=Kg00G9R>#BR?#BR@#BRA#B#B#B#c#Y%cA#YRB#U[P=f5R=f4RCP<H08f6RD?}5<1=DC14=Cf7RE/4D'=117=%bARF,5E%b>RG70D/1Ff8RH#DRIf<RJf;RKf:RLf9RM?0HGRNPDB07MF6%DF15LF#D[g00I>ROg00dCRP#CRQ#CRR#CRS#ERT%EQRU1a8PRP'7'7g01B:RV'O%^ORW3J%[ORX1I8C%n8RY7A41I8<7A5%l8RZ%j8R[1P87R\%R>R]#@R^'H,2[%f:R_P[%@?R`/<^Ra1T8>Rb%@@'<Rc'G,2[P_P[1Gb`,2[P_1P8GRd9M8aRa,Gb,2[1Hac,2[5L[C8C8C81e[;RaP6P4g00K8Rcg00KXRe'd20664=3cedB05875H04Reb;b=b>X18X28X38X481174144<145C'=1=4<A0C=GRc,=<14<D,1c'6[[[^18^28^38^48P6PJPLPKf=RcPCP=PDO7b:bTJ02%[BRf#URgA0LMGRh#9=>cQPfPBP6%^BRiC?Rj331:6h'6X7B,|BP3PBf>R3A0KLGRh#9;>Q=3gj1:6h'6X7B1:MhP6f@RhA0cJGRJ#9;>Q=3gj1:6J'6P2fAR2A03cGRJ#9;>QPfPBP5PiC?53g1:5Jf?RJ?03G,:cP6fCR3A0hJG#9;>QPfPBP<PiC?53gA02hG,:CfBRJ?02GR2/_F%QFRj#xRkA03JGRl1FlF,NF15lF'4';[1]lF117FRmfDRn?03GRo/5FRp#D11pF'6[1WoF11F7RofERp?0nGRq/5FRr,1F1=r7'6[1VqFfFRq?0pGRr/FF#Q\j1\rFfGRr?0qGRs/5F/;s\j1FsFP8fHRt?0rGRu/5FP8fIRv/_FfJRw1FwF,NF15wF'4';\k1]wFfKRw/5FRk#D11kF'6\m1WwFfLRk/5FRx,1F1=x7'6\o1VkFfMRo/FF#Q\j1\oFfNRo/5F/;o\j1FoFP8fO/5FP8P=g00HX1v7F'dPmeRmO1%D6116F'6PcPmO111HF,6IRIp-0Rm%CSRS#CRc#CRo#C#E%u>,t8R>%EoRo5Z8%ES1s8F=q8P,7U,7T'7'7'7/OV%EcAZ8>T%ER'7'7,7o17PU/OV'p=JOW5JOPX1I8D?AEY1I8=7A41I8E?ACY?A<Y7A5PZP[%@ARA,G\,2[P[P9P:P:P;PMEo5L[P_P[P[P[P9P:P:P;1P8FR;/K\,2[ErR:P_%R?#@R?AX8;^/<A'K,2[C8P_P[%R@#@R@,G\,2[1H@;,2[5L[P_P[P[P:P_%B]#@R],<?=M8dAX8;b/<@'K,2[C8P_P[1<A]=M8d/H;,2[P_P[1H\],2[P_1<b`1<^`'K,2[C8C8C8C8C8C8PaPeb;b=b>X18X28X38X48X?8X@8XA8W<%D=/6Eg00eg\jRj1NFCRe/4E,;=[A0EHG14eL';\j11NF117M14DE14HE';[[[\I[[^18^28^38^48^?8^@8^A8^<mP611<FPLP<fRfSPCg01BfPKP4PMP5PhPwPkO>b:b9b8b\bZbJbIbHb8bGb[bYbQbPbOb9b0%92%9J';R2eP2P8%9lA>r6QPfPBPEPiC?RE53gX^8P4%93R4P6E`A>q4QPfPBPDPiC?53gPg%9n=>rQPfPBPHPiC?RQ93g6XXgP6PfPBPJPiC?RDPrPJPnPhCmE`A3gDEPgPBP0PfPBP6P1PBPBP6PpP5n10110200020020100102Pnn10110100021010200XCgPfPBP3PiC?PQP6EwA3B3HA3BnMPBPp1:6uA0vtG,:r]5XBB1:psP6W5PLP6P=FkW0P6O1b0b6b6bDW5W6P5P6O2n2001000000121000000W0XBBP5P6O2n2001000000121103000bCWNWMWLWKWFWRWEX7BX]8XS8XW8XU8WVo"). Qed.

(* [comment removed for export] *)
Lemma sh_ok_cases : forall b Y, sh_ok b Y -> bv_unsigned b = 0 \/ (0 < bv_unsigned b < 8 /\ Y mod 8 < bv_unsigned b).
Proof.
ltac2:(KReplay.run1 (kr_t_LeptTac ()) [] "h01Hh11Yh21bp;1p;2g0000j10Tg003ej13Tg00L8j12Tg00hoj21Tg00G9#0#0#0#3#2g00F[f1f0R0'1P0W0W1W2o"). Qed.
Lemma sh_ok_8 : forall b X, sh_ok b (X + 8 - 1) -> X mod 8 = 0 -> bv_unsigned b = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_LeptTac ()) [] "h01Hh12H0h22H2h32H6h42H8h54__p1h64__p2h74__p3h84__x1h94__x2h:4__x3h;4__x4h<4__x5h=4__x6h>2H1h?3H10h@2H3hA2H4hB2H5hC2H7hD2H9hE1XhF7__arithhG4__ffhH8__varmaphI5__withJ1bhK1qhL2q0hM1rhN2r0p;1p;2p;3p;4p;6p;7p;8g0000j1DTg003ej1vTg00L8j1eTg000Uj1NTg00hoj2pTg00L[j25Tg00Paj20Tg002nj24Tg019>j2LTg019_j1uTg00Rfj2?Tg00WUj2JTg00Naj2@Tg01:8j2RTg002Rj27Tg01:_j2STg003JR0j2ATg01;Fj2UTg01;lj2WTg006Pj2aTg0071j2PTg00b4j1<Tg01<Rj1`Tg01=0j2_Tg01=Qj3OTg01>:j2^Tg016lj2MTg01>cj3]Tg017Uj2\Tg01?Lj2[Tg007Kj1ZTg00^Aj3YTg007kj1XTg008Kj2KTg00g[j4ETg00V6j1tTg008ij1sTg009Gj1rTg0013j1VTg00;[j2>Tg00<>j4BTg00=Mj1oTg00:2j2ITg00dbj6lTg00ZBj3TTg00O[j3GTg00P>j3jTg00>Sj2iTg00?5j2hTg004jj3FTg00?aj3gTg00@@j4kTg01C[j2fTg00O>j2mTg01AQj3nTg00D8j7dTg00=oj8cTg00QAj6qTg00<ij7bTf2R1f1R2'@f0R3'mp=2g00F[R4g00G^R57F3p=11453p=:1423,A1p=3AF423p=;1M43p==An423p=9P2g00D\R6g00E;R7P7g00E[R8P3g00F;Fdp=8P4P2g00TSP3CBp=Cf3R9P6P7P7P8P1P2P3Gcp=6P2P6P7P7P8P3Eqp=HP1P6P7P7P8P2P3Fbp=Qg00G9R:#DR;#DR<#DR=#vR>#e%N=R=%N:R?523,p2g01D:15>1R@#1%:@?3@=A22=?/0=;3@101=#1f4R@,5>RA#1[P315>9RB#1109=#1P2W4W0P3O1%:B?3B=A21=?/0=;3BP0%:A?3A=A29=?/0=/4A10@=#1f6RA,5>R0#1[P3%:0?30=A2A=?R0/0=f7RB,5>'410B=#1f9RC,5>#1f8RD?2=?/L=%1=RE#uRFA2C=?RG1?G=,J=10G='@';[1RG=%:=RGf:RH?2=?RI/0=RJ,75?3J=[1SI=14=5RIf;RJ?2=?RK/0=RL,4=17L5'A[1UK=f<RK?2=?RL/?=#1\E1WL=f=RL?2=?RM/0=/;M\E1?M=P4f>RM?2=?/0=P4f?/L=f@RN1?N=,J=10N='@';\F1RN=fARN/0=RF,75?3F=\G1SN=fBRF/0=RO,4=17O5'A\I1UF=fCRI/?=#1\E1WI=fDRI/0=/;I\E1?I=P4fE/0=P4f5ROg00HX1a5='PPGeRGO11753?33=PLPGO1175D?3D=fI,5>,4Cp-0RGg00I>RLg00dCRP#<RQ#<RR#<RS#<RT#=%=S%`:,_4RS%=R5O4%=Q'9'9RQ'91^4=1M4P5]4%<TRT#<#=%=T9O4S/9Q'9'9g01B:'\'[%ZL3Y%XLP4P41K4@P11K4ACEP2P41K4OP9%t4CECE%s4%r4RLP4%V;,>4RQg00JQRS1>4:RTCB,8L%o7RPPLPLPLP6P7P7P81I4=R71I45R6'C,8LElRRPP%V:R:,>4RU%D:,>49T471>4;R;5G4'C,8LC6PPPLP4P6g00IjPQCB,8L1HLD5QLPPPLPLPRPPAG4U71I4?5j41>4<9T47=G4Q'C,8LC6PPPL1C;6,8LPPPL1HLCP4PTPSP7CB,8L5QLPP1HLHC6C6C6C6C6C61iL8P3P1g00K8RLg00KXR8'P1h31=FL8dAg452CkbGbHbIX84X94X:4X;4X<4X=4X5GX6GW714@3g00egR8\ERE1J=BRB/@9,;@[175A/AD1@BD,;0\E%1OA3KO=PM[[[[[[^84^94^:4^;4^<4^=4^5G^6G^7GP3P8fK,5>R>#:14J=POPJPKfJP@P>P2PHP1PNPFPIO?bFW2b1b3bNbLb?bDbCb3bBbMbKbAb@b2b1b0P2O1'fW4W2W>P2P3O2n2001000000121000000W0P3O1n200100000021000011000W1XE4WJo"). Qed.

(* [comment removed for export] *)
Ltac next_instr k :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
      lazymatch fw with
      | Some ?w => let d := eval vm_compute in (decode_any w) in
                   lazymatch d with Some (?i, _) => k i | _ => fail "undecodable" end
      | _ => fail "no instruction"
      end
  end.
Ltac instr_at segs pc k :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w => let d := eval vm_compute in (decode_any w) in
               lazymatch d with Some (?i, _) => k i | _ => fail "undecodable" end
  | _ => fail "no instruction"
  end.

(* [comment removed for export] *)
Ltac reg_val r k :=
  lazymatch goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      let p := eval vm_compute in (bv_key r) in
      let v := eval cbv beta iota delta [tget mkR] in (tget p R) in
      lazymatch v with Some ?x => k x end
  end.

(* [comment removed for export] *)
Ltac shadow_base E :=
  lazymatch E with
  | (?X ≫ 3 + 2147450880)%Z => X
  | (?X ≫ 3 + SHB)%Z => X
  | (SHB + ?X ≫ 3)%Z => X
  | (2147450880 + ?X ≫ 3)%Z => X
  | (?X / 8 + 2147450880)%Z => X
  | (?X / 8 + SHB)%Z => X
  | Zpos _ => let x := eval vm_compute in ((E - 2147450880) * 8)%Z in x      (* [comment removed for export] *)
  end.

(* [comment removed for export] *)
Ltac shload :=
  next_instr ltac:(fun i =>
    lazymatch i with
    | Load SZ1 _ _ ?rs ?imm =>
        reg_val rs ltac:(fun v =>
          lazymatch v with
          | Z_to_bv 64 ?E =>
              let X := shadow_base E in
              lazymatch goal with
              | |- evt _ _ (MS _ _ _ _ _ ?m _) =>
                  first [
                    match goal with
                    | ACC : acc asegs m ?a ?n |- _ =>
                        let b := fresh "shb" in let K := fresh "SHK" in
                        destruct (acc_shk m a n X ACC ltac:(lia)) as (b & K);
                        let HR2 := fresh "SHL" in
                        assert (HR2 : ov_read_bytes asegs m (Z_to_bv 64 E) 1 = Some [b])
                          by (rewrite <- (shk_read m b X K); f_equal; unfold wa, shad, SHB; f_equal;
                              rewrite ?Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia)
                    end
                  | fail 1 "shload: no acc fact covers" X ]
              end
          end)
    end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma shad_range : forall x, 0 <= x < 2^47 -> 2147450880 <= shad x < 17594333495296.
Proof.
ltac2:(KReplay.run1 (kr_t_LeptTac ()) [] "h02H0h12Hah26__sat5h34__x1h44__x2h54__x3h61Hh72H1h82H2h92H3h:2Hxh;7__arithh<4__ffh=6__sat4h>8__varmaph?5__with@1qhA1rhB1xp;1p;2p;3p;4p;6p;7p;8g0000j11Tg000Uj1=Tg001Xj2qTg002nj20Tg003Jj25Tg019>j2[Tg004jj38Tg019_j1STg00Rfj2CTg00WUj2MTg00Paj2<Tg00Naj2GTg01:8j2pTg01:_j2mTg002Rj2ATg01;Fj2bTg01;lj2aTg006Pj2OTg0071j2HTg005Dj2]Tg005lj3\Tg00b4j1>Tg016lj29Tg01<Rj1ZTg01=0j2YTg01=Qj3XTg01>:j2WTg01>cj3VTg017Uj2LTg007Kj1RTg00^Aj3JTg007kj1QTg008Kj2KTg00g[j4PTg008ij1TTg009Gj1UTg00:2j2;Tg0013j17Tg00;[j2ITg00=Mj1oTg00<>j4@Tg00dbj6lTg00ZBj3kTg00O[j3NTg003ej1fTg00:Uj3eTg00>Sj2dTg00?5j2`Tg00?aj3gTg00@@j4hTg00h9j1_Tg01AQj3iTg00D8j7jTg00<ij7^Tg00=oj8nTg00G^R0f0R1'Ap=6%71#7#7#7p=4%11#1p=?g00F[R2f1R3;i1p=:P2P3g00IjP1C@p=DP3g00D\R4g00E;R5P5g00E[R6P1g00F;Fjp=2P2P3g00JQP1C@p=Ef2R7P4P5P5P6P3P1F^p=Ff3R8P4P5P5P6P7P3P1Gnp=B%71#7p=c%11#1#1#1p=3%61R9g00G9R:#1R;#=R<%4;R=#=R>'qR?,01'5%?;R@#=RA,[3A82A0RB#S1C7A,MA1<7A'G9827[1p7A100ARC1<8ARD#610DA'5[1m8A10A0f4RD/<ARE,0A1AE0'5[1bDAf5RE/CA=820\B1aEAf6RF/<A=82F\B1CFAP2f7/<AP2PEg00HXRG1O0A'HPCeO1101A,591]<>100<R9%6>100?[RC[%6<RHg00H<RIA\<>3UW1%6?\I^1HP31O0<,HGP9eO1PCg00I>RCg00dCR9#>RG#>RH#>RI#>R>#>,92%Z:,Y2192IRI5X2192G1W2A19295V2R9':':':g01B:RG'L192>192H/:9,:I':/LG%RC5JC3J%QCP21K27P31K28CP%T2%U2RC1;20RG%7:RI,I2R9'D,2C1;2ARH,E9,2C5FC%o5R>PCPCPCP4P5P5P6P2PHg00TSR5PGC@,2CElP>P21I2;R;P51I2:R:9k2H=N29C@,2CCBP>PC1DG;,2C1;2<%f=5e2,E;,2C5FCP>%cI#4#4#4#1#?#3#3#3#=RI,;2R>AN2:>R>'D,2C%?@#3#3#4#4#4#4#1#?#3#3#3#=R@,;2,E>,2C5FCCBCBCB1dC6P1P7g00K8RCg00KXR6'H1`17=8C6dAg203Chb<b>b?X32X42X52%67107A'5g00eg\B1MA7/GD9828[%68108?'51G8IR8,AI108@'5[[[^32^42^52P1PEf=PFPDf;f<O6b;b2b=b2b0bAb@b9b8b7b0b6%_3R3,AI103@'5eW:XB2o"). Qed.

(* [comment removed for export] *)
Lemma acc_write_out : forall (m : mem) a bs A N (n : Z),
  Z.of_nat (length bs) = n -> 0 <= a -> a + n <= 2^64 ->
  acc asegs m A N -> 0 <= A -> A + N <= 2^47 -> (a + n <= 2147450880 \/ 17594333495296 <= a) ->
  acc asegs (write_to_mem m (wa a) bs) A N.
Proof.
ltac2:(KReplay.run1 (kr_t_LeptTac ()) [] "p'0h01bh12Hah24__x1h34__x2h44__x3h56__sat1h66__sat2h76__sat3h81xi001xh92H0h:7__arithh;4__ffh<6__sat4h=8__varmaph>5__with?4cstrh@1mhA1nhB1AhC1HhD2HAhE2HNhF2HbhG2HdhH2HihI2HlhJ2HnhK1NhL2OKhM6__sat0hN1ahO2bshP1ehQ1ihR1yp&0p;1p;2p;3p;4p;<p;6p;7p;8p;Bg0000j12Tg003ej1PTg00L8j1VTg00fDk100Tg007kj1_Tg00m0j2NTg00nPR0j1BTg004jj3`Tg000Uj1ATg001Xj2UTg00ffj4bTg0013j1?Tg002RR1j24Tg01D:j2CTg002nj2<Tg003JR2j23Tg00NaR3j20Tg00h9j18Tg007Kj1^Tg00^Aj3:Tg00hoj25Tg00ifR4j2OTg00j@j1DTg01DTj3GTg01EXj1YTg005Dj2XTg005lj3WTg006Pj2cTg0071j2@Tg00b4j1KTg016lj2FTg017Uj2JTg00V6j1~Tg008Kj2aTg00g[j4TTg008ij1}Tg009Gj1|Tg00:2j2HTg00;[j2MTg00=Mj1yTg00O[j3LTg00:Uj3xTg00>Sj2wTg00?5j2vTg00?aj3uTg00@@j4rTg01F=j2qTg01G;j1\Tg01GYj4pTg012fl<lTg01H<j6mTg00knj4kTg01Hdl<jTg010Nj4iTg00_Gj4hTg010ij4sTg01AQj3tTg00<>j4ZTg00D8j7]Tg00<ij7gTg00=oj8fTg01J0l<eTg01JUlB{Tg01K;j7dTf0R5#2#2p=Ig00G^R6/45p=1f2R7f1R8'0/45p=9%?5#?#?#?p=;%?5#?p=z%25#2#2#2p==g013KR9P7P8P5Csp=6g00F[R:?t85p=>P7g00D\R;g00E;R<P<g00E[R=P:P8g00IjP5CZg00F;R>F]p=7P:P8g00JQP5CZp=RP8P;P<P<P=P5P>F]p=QP7P;P<P<P=P8P5Fgp=Sf3R>P;P<P<P=P7P8P5Gfp=Eg014CR?P:P:P:P0P0f5R0f4R@P>P7P8P5M<ep=oP:P:P:P:P:P:P3P5P8P7P3P>P@P0f6R3f7RAf8RBf9RCMB{p=nP7P;P<P<P=P8P5Fdp=[g00G9R;#2RD#IRE#2#IRF#P#V%PE#VRE$00[%_E1NE>#B=`:5%10%ADRG%AFRH'URI9937P9PBP0P@Cb%13%;DRJ#ARK,UGRL99A3f:RA%?;RM#z#;#;#;#2#I#=#=#=#ARN793%2F#I#=#;#;#;#;#2#I#=#=#=#ARF/4A'C%151<5C'3P0P8P5O2f?ROf<RP/07RQ#8%^ERR9:E5RS36155Q'3X0E,OEP4PEf@R4f=/0>RQ#8;6S155Q'3X0EfARQ%D4;GOf>/0@RT#8;6S155T'3X0E,OEP5fBRT10O0RU#8;6S155U'3P2fCR21043R3#8A:E8R361583fER3fDRU#D;G210TBRV#8RW;6S155V'3X0E,OEP5A:E>R963W102C,5@PEfHfGRW#DfFRV3Gf;RX,03RY#8RZ;6S155Y'3X0EP0%DV=GW310UARY#8RSA:E0RRR36150YP9PWPVP3PSPRPTPQP4POP81NE3RO#Y%BO#11XGKRO1<6GR4%1K1<6L[R0[R[%1GR\g00H<R]AWGK8UW1RK%1L\]^1\R^1XGHR_%1H1<6I[R`\4RaAWGH8V]X1\RH%1I\]^1\R\P8g00HX1c6G'@P4eR4O1R]P`P@P4O1R4P0g00I>RIg00dCRb#KRc#KRd#KRe,F:Rf1F:dRd1F:bRb'>Rg'>g01B:Rh'J%Ke,F:Re1F:cRi/>b'>/Jh%^IRb5:I3:%_IRjP:P:%~:RkP71a:>RlCTP8PkCT%}:Rk%|:Rm1H:6Rn1M:DRD57m%2M,M:Ro,RD,Qm5Sm%y<R<Pm1M:;Rp=L:o1H:G%PJ5x:RJ57mP<PmA7mnpP<AL:pDRG97mn1RGJ,Qm5SmCECECE1wm=R=P5P7g00K8RGg00KXRJ'@1v57=`GJdAu:68CrR6b;b=b>X2:X3:X4:%181<87'3A98>L%1710>@R@#11<@L'3[[[^2:^3:^4:P5fKRLPTfLPQPUP3O6b:b7b5bMb5b6b7b?,qY14NS1<SF'3%BcRY,0ZR3/4WRQA9W2ZRJ'C%A;R;,0ZRG/4WRn/CJPQPJPnPJP:P:P1P5X8:RnP11485#\XR:X8:P3PGPnPnPnP:P:g01K_1085Cp,@:X@:XA:PZPZ1@:ZPYP;PnPn%B5,@:X8?PcP;1@:;EoM:nPWPW1@:WM<l%\JEm1NEVRJ#Y%BJ#1POP[PKP^P_PaPHP\P]P`P4P01>eg/Jh1>di,>f/Jh=:Ib5:IPjP:1a:7P8PlCTPkPm1H:NRk=7mp1H:FRl,Rp,Qm5SmP<Pm1M:M9L:DRM=7mkA7mlD5[mP<1H:;9L:p=7mDA7mMp5[mCECEP=P6b;b=b>X2:X3:X4:14N51<5F'3A97>N14F7'CA97;>14@7'C[[^2:^3:^4:P5PLfOfM/02#8PBPUO5b:b<b6b5b6b7b<b?Ckb91NER#B=9SVA9VTS'CeM<jP5CiChWLWFP8P5O2n2001000000121000000W9X0EP8P5O2n2001000000121100000bPWHXQ:P9%DX=GPAPCPBCbeWGWEWDWCWIW1WJXA:XK:XB:WOXN:W@o"). Qed.
(* [comment removed for export] *)
Lemma acc_write_gen : forall (m : mem) a bs A N (n : Z),
  Z.of_nat (length bs) = n -> 0 <= a -> a + n <= 2^64 ->
  acc asegs m A N -> 0 <= A -> (a + n <= shad A \/ shad (A + N) < a) ->
  acc asegs (write_to_mem m (wa a) bs) A N.
Proof.
ltac2:(KReplay.run1 (kr_t_LeptTac ()) [] "p'0h01bh14__x1h24__x2h34__x3h44__x4h54__x5h62H0h72Hah81xi001xh92H1h:3H11h;2H6h<7__arithh=4__ffh>4__p1h?4__p2h@7__sat16hA6__sat2hB8__varmaphC5__withD5__x10hE4__x6hF4__x7hG4__x8hH4__x9hI4cstrhJ1mhK1nhL1AhM1HhN3H10hO3H12hP3H13hQ3H14hR2H2hS2H3hT2H4hU2H5hV2H7hW2H8hX2H9hY2HAhZ2Hbh[2Hdh\2Hih]2Hlh^2Hnh_1Nh`2OKha6__sat1hb7__sat15hc1ahd2bshe1ehf1ihg1qhh2q0hi2q1hj1rhk2r0hl2r1hm1yp&0p;1p;2p;4p;3p;6p;<p;7p;8p;Bg0000j1@Tg003ej1pTg00L8j1gTg00fDj1uTg007kj1oTg00m0j2UTg00nPR0j1ITg000Uj1VTg001Xj2tTg00ffj4dTg00h9j11Tg00NaR1j20Tg002nj27Tg01D:j2LTg007Kj1kTg00^Aj3FTg00hoj2CTg003JR2j24Tg00ifR3j2[Tg00j@j1NTg01DTj3PTg019>j2ZTg019_j1yTg00Rfj2BTg00WUj2OTg00Paj22Tg01:8j2`Tg01:_j2aTg002RR4j25Tg01;Fj2XTg01;lj2WTg006Pj2cTg0071j2ETg01EXj1bTg005Dk20FTg005lk30ETg00b4j1DTg01<Rk10DTg01=0k20CTg01=Qj3nTg01>:k20ATg016lj2mTg01>ck30>Tg017Uj2TTg00V6k10=Tg008ik10<Tg009Gk10;Tg0013j1KTg00:2j2]Tg00=Mk108Tg00dbk604Tg00ZBj3\Tg00;[j2hTg00>Sk203Tg00?5k202Tg004jj3YTg00?ak300Tg00@@j4~Tg01G;j1fTg01GYj4{Tg012fl<zTg01H<k601Tg00knj4xTg01Hdm<05Tg010Nk406Tg00_Gj4wTg010ik407Tg01AQj3_Tg008Kj2vTg00g[k409Tg00QAk60:Tg00<>j4^Tg00D8j7jTg00<ij7sTg00O[j3rTg00=ok80?Tg01J0m<0@Tg01JUlBqTg01K;k70BTg00F[R5f1R6f0R73Yp=9g00G^R8/57p=3f2R9/06/57p=>1767,49p=;g013KR:P9P6P7H07p=AAY578p=Q1m57p=?A_567p=lA_5679_59p=J1v57p=HP5P9P6P7H09p=<P6g00D\R;g00E;R<P<g00E[R=P7J0:p=i1h57p=8P5P6g00JQP7C^p=RP6P;P<P<P=P7g00F;R>Fjp=GP9P;P<P<P=P6P7Fsp=MP5P6g00TSP7C^p=SAr567p=:f3R?P;P<P<P=P9P6P7L0?p=6P9P;P<P<P=P5P6g00IjP7C^P>Fjp==g014CR>P5P5P5P0P0f5R0f4R@P?P9P6P7N<0@p=|P5P5P5P5P5P5P1P7P6P9P1P?P@P0f6R1f7RAf8RBf9RCMBqp=}P9P;P<P<P=P6P7K0Bp=eg00G9RD#@RE#@RF#@RG#@#@#@RH#p#g%pG#gRI#u[%oI1UI?#I/97%30%VERJ%VHRH'tRK9>19P:PBP0P@Cd%31%1A9>C010A1#1/7C'L%37RL?;7BP@P6P7O2f>RMf;RN/09RO#1%kIRP9FI7RQ3A1C7O'4X0I,[IP3PIf?R3f<RO/0?RR#1;AQ1C7R'4X0If@RR%N3;PMf=RS/0@RT#1;AQ1C7T'4X0I,[IP7fART10M0RU#1;AQ1C7U'4P2fBR21031RU#1AFI6P3A1C6UfDRUfCRV#N;P210TBRW#1RX;AQ1C7W'4X0I,[IP7AFI?P9AUX102C,C@PIfGRXfFRW#NfERY3P10UNRZ#1R[;AQ1C7Z'4X0IP0%NY=PWUf:RZ,0VRQ#1R\AFI0PRP3A1C0QP:PWPYPUP\PPPTPRP3PMP6%VGRQ,ZV%QQR]#yR^1BUQ,OQ12UQ'0,9U[1`UQ178QR_12YQR`#3?;`Q[1aYQ17Q8R`12WQRa,7Q15a8'4[1XWQ1BXQ#Q\]1WXQfHRa/2Q/9a\]1BaQP5fIRb/2QP5fJ/0T/ZQfKRc/02Rd1BdQ,OQ12dQ'0'9\^1`dQfLRd/0VRe/2QRf#3?;fQ\_1aeQfM/0URU/2QRe,7Q15e8'4\`1XUQfN/0YRU/BQ#Q\]1WUQfO/0WRU/2Q/9U\]1BUQP5fPRU/0X/2QP5fQRe/0U/ZQfRRU/0eRe1BeQ,OQ12eQ'0'9\^1`eQfSRe/0URU/2QR^#3?;^Q\_1aUQfTRU/0eRe/2QR^,7Q15^8'4\`1XeQfURe/0URU/BQ#Q\]1WUQfVRU/0eRe/2Q/9e\]1BeQP5fWRe/0U/2QP5P0g00HXR`1c8Q'EP_eR_O1A;L7QPSP_O1%3BRL?;BQPYP_O1%3R?;RQf\,UIR_#b%I_#320FJHR_178JR^%3H178K[Rf[Rg%3JRhg00H<RiB0EJH6UW7RH%3K\i^7hRhP61c8J,E`P^eO1R^Pfp-0R`g00I>RJg00dCRi#DRK#DRj#DRk#DRl#DRm#DRn#DRo#DRp#D#?%?p%?o&0DD-0C5Ro%?mRm5n5%?KRp20A5Q1m5iRi60>5Rq'l3J3Jg01B:Rr'T%?n%?lRl%?kRk9n5o%?jRj/lq3J7Jm/Tr%kJRm5FJ3F%oJRq%H0Ro%HA7<@&0=5Rn%HC7<Z7<9%HB9<nZ%H1%HZ7<Z7<?7<6&0<5Rs&0;5Rt1itO%KDRu#KRv#K#8Rw1]5QRx'R,Gt5Mt&08<RyPtPtPtP;P<P<P=1]58R<,Sx,GtJ04R;Py%8GRG%@uRz#@#8R{':%8FRF9\5x/:w'S,GtC6PyPt%@v#8Rw9=t<1Rwx,Gt5MtPyPtPtP;Py%KE#K#8R|,:G%8uRu9\5x/:w'S,GtC6PyPt%Kz#8Rw9=t<1itS5MtPyPtPtP;Py1h5DR;9\5x/:w,SG,GtC6PyPtA=t<|1R|{,Gt5MtPy%8ERE,:;1:uER|5=t1:FE9=t|5MtC6C6C6C6C6C6C6203t=R=P7P9g00K8R|g00KXRF'E20279=Y|FdB00586C~R8b=bBbCX15X25X35X45X55XE5XF5XG5XH5XD5X>`W?A;ZCQg00eg\]R]101B1OQ0/0N'9[%3Z?;ZQ10BC1OQ1RF/0O'9\]%3NR|/4310FS,9Z\]A;|NO10CBR|9>AB10ZB,5|'4[[[[[[[^15^25^35^45^55^E5^F5^G5^H5^D5^>`^?`P717WQPLPBP3PWf_Pef`PCPRg01BfPXPAPMP1PYP0PdPUOCb<b@bbb@bIb9b;b:blbibQbPbOb:bNbkbhbXbWbVb;bUbjbgbTbSbRb9b6%1V/5\10V2#1,5\'4RVePV%IKRV,0[RU/5WRdA>W2[R2'L%VDRD,0[R1/5WRM/L2PdP2PMP2P5P5P4P7X85RMP41567#fXm5X85PUP1PMPMPMP5P5g01K_1067C{,E5XJ5XK5P[P[1E5[PVPDPMPM%I7,E5X8>PKPD1E5DE|M:}PWPW1E5WM<z%f2J011UIYR2#b%I2#3P_PgPHPhP^PfAJlji/TrAJkjp/Tr=FJm5FJPq%H@9<n9A<n?o7<6PsPt%8zRz==t;%8vRv9=t;5MtPyPt1:EuRu==tz1RvE,Gt5etPy1]5D,:;==tEA=tu;5etC6C6P=P8b=bBbCX15X25X35X45X5515?7157@'4A>9?@1709'LA>9D?A>?@9'L[[^15^25^35^45^55P710ba#1%1bPXPc10bR#1P0PTO7b<bAbabAbICxb61UIP#I=>\YA>YT\'LeN<05P7H06CwW`WZP6P7O2n2001000000121000000W6X0IP6P7O2n2001000000121100000beW\Xf5P:%NZ=PNCPBPACdeW[WYWMW]W7W^XK5X_5XL5WdXc5WJo"). Qed.
Lemma shk_write : forall (m : mem) a bs b X (n : Z),
  Z.of_nat (length bs) = n -> 0 <= a -> a + n <= 2^64 ->
  shk m b X -> (a + n <= shad X \/ shad X < a) -> shk (write_to_mem m (wa a) bs) b X.
Proof.
ltac2:(KReplay.run1 (kr_t_LeptTac ()) [] "h02Hah11xh26__sat1h34__x1h44__x2h54__x3h61mh71nh81Hh92Hdh:2Hlh;2Hnh<1Xh=7__arithh>4__ffh?6__sat0h@8__varmaphA5__withB1ahC1bhD2bshE4cstrhF1yp;1p;2p;3p;4p;<p;6p;8p;Bp;7g0000j14Tg003ej1DTg00L8j1=Tg00fDj1ITg007kj1ETg00m0j2:Tg00nPR0j15Tg004jj3@Tg002RR1j20Tg00NaR2j21Tg000Uj1;Tg001Xj2GTg015Dj3FTg00h9j18Tg002nj26Tg01D:j23Tg007Kj1CTg00^Aj3WTg00b4j1VTg01G;j1BTg01GYj4UTg0071j22Tg012fl<RTg01H<j6QTg01EXj1PTg005Dj2NTg005lj3KTg006Pj2JTg008Kj2>Tg00g[j4HTg008ij1LTg009Gj1MTg00;[j27Tg0013j1OTg00O[j3?Tg00<>j49Tg00=Mj1dTg00:2j2cTg00=oj8bTg00>Sj2aTg00?5j2`Tg00?aj3]Tg00@@j4ZTg00knj4[Tg01Hdl<\Tg01J0l<YTg01JUlBXTg00D8j7^Tg01K;j7_Tg014CR3g00F[R4P4P4P0P0f5R0f4R5f3R6f2R7f1R8f0R9M<Yp=TP4P4P4P4P4P4P2P9P8P7P2P6P5P0f6R2f7R:f8R;f9R<MBXp=SP8g00D\R=g00E;R>P>g00E[R?P9g00F;F^p=<P7P=P>P>P?P8P9F_p=Ag00G9R@#4RA#4#4RB#4#4#4RC#D#=%DB#=RB#I[%EB1:B6#5=@49g00G^RD/001127%;ARE%;CRC'GRF'0AF;0511;5%80RG'016G;'3g013Kf:RGP<P;%82R2%CB9WB:R:P0P5P6P7P8g00dC#VR5#5RH,12RI/0<RJ11<0/02RK'3%;@RL,12RM/0<RN/3KPJPKPNPKP4P4P1P9X14RNP11089#BXF4X14PIPMPNPNPNP4P4g01K_1189CU,24X64X74P2P21242PHPLPNPN%59,24X13P5PL124LETM:SP<P<124<M<R%BKEQ1:B;R;#P%5;,0D1NEC16DER;10DC16DF[R5[10DER3g00H<RNAKEC8UW010DF\N^03P8g00HX1JDE'2P;eO1P5g00I>R5#C%E5P41>47P81>46CH%L4%M4R5P=P>P>P?P4174ARA%O@,745?4g00IjR=174@R@C9,<5R;P4P@g00JQPAC9,<55A5%d>P41c4L9?4@P=PAC9,<5=A5;Gb1a5?P9P7g00K8R5g00KXR?'21`97=@5?dA]4D8CZb>b@bAX34X44X541187/091698'3118L/071176/08'3[^34^44^54P9PGf>f;#8P0O4b=b2b?b2bEC[1:B:#5,12/0</3KeM<\W9W8W:W0W;X74X<4XCBWDXB4W6o"). Qed.

Ltac lept_transport_extra m a bs n Hn Ha Hl :=
  repeat match goal with
  | H : acc asegs m ?A ?N |- _ =>
      first [ apply (acc_write_out m a bs A N n Hn Ha Hl) in H; [ | tlia | tlia | tlia ]
            | apply (acc_write_gen m a bs A N n Hn Ha Hl) in H; [ | tlia | unfold shad, SHB; Z.div_mod_to_equations; tlia ]
            | idtac "note: dropping acc fact (store may alias its shadow):" H; clear H ]
  | H : shk m ?b ?X |- _ =>
      first [ apply (shk_write m a bs b X n Hn Ha Hl) in H; [ | unfold shad, SHB; Z.div_mod_to_equations; tlia ]
            | clear H ]
  end.
Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= lept_transport_extra m a bs n Hn Ha Hl.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bvmap_set_same_eq : forall (R : bvmap 5 word) r v, reg_get R r = v -> r <> Z_to_bv 5 0 -> True.
Proof.
ltac2:(KReplay.run1 (kr_t_LeptTac ()) [] "h01Rh11rh21vp;1p;2p;3g0000j10Tg0013j18Tg003ej13Tg00L8j11Tg01LCj27Tg01Loj26Tg004jj32Tg00A_j24Tg019_j15Tg00G9#0R0#8#3R1%00#0#0#0#0#3#1R0'7%11R2f2R3f1'6f0520g00G^,419223#5g01MYUUX20W1W0o"). Qed.

(* [comment removed for export] *)
Ltac norm_regset :=
  repeat match goal with
  | |- context [@bvmap_set 5 word ?r ?v ?R] =>
      let p := eval vm_compute in (bv_key r) in
      change (@bvmap_set 5 word r v R) with (tset p v R);
      cbv beta iota delta [tset mkR]
  end.

(* [comment removed for export] *)
Ltac bstep := lstep; try br.
Ltac bsteps_to p := repeat (tryif at_pc p then fail else bstep).

Ltac shbyte_of c :=
  lazymatch c with
  | context [sxb ?b] => b
  | context [@bv_unsigned 8 ?b] => b
  end.


(* [comment removed for export] *)
Ltac shbr_merge ru FAST OK :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F _ ?fc ?rv ?m ?ro) =>
      eapply (evt_cut segs (fun ms' => exists u' : word,
                 ms' = MS (@bvmap_set 5 word ru u' R) F (Z_to_bv 64 FAST) fc rv m ro));
      [ destruct OK as [OK|[OK ?]];
        [ (* [comment removed for export] *)
          brF; apply evt_done;
          lazymatch goal with |- exists u', _ = MS (@bvmap_set 5 word ?r u' ?R') _ _ _ _ _ _ =>
            let p := eval vm_compute in (bv_key r) in
            let v := eval cbv beta iota delta [tget mkR] in (tget p R') in
            lazymatch v with Some ?x => exists x end end;
          norm_regset; reflexivity
        | (* [comment removed for export] *)
          brT; bsteps_to FAST; apply evt_done; eexists; norm_regset; reflexivity ]
      | let u' := fresh "u" in let E := fresh "E" in let ms := fresh "ms" in
        intros ms (u' & E); subst ms; norm_regset; clear OK ]
  end.

(* [comment removed for export] *)
Ltac shbr :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then Z_to_bv 64 ?SLOW else Z_to_bv 64 ?FAST) ?fc ?rv ?m ?ro) =>
      let b := shbyte_of c in
      lazymatch goal with
      | K : shk m b ?X |- _ =>
          instr_at segs SLOW ltac:(fun i =>
            lazymatch i with
            | OpImm ALU_AND ?ru _ _ =>
                (* [comment removed for export] *)
                let szm1 := constr:(0%Z) in
                let S4 := eval vm_compute in (SLOW + 4)%Z in
                instr_at segs S4 ltac:(fun i2 =>
                  let szm1 := lazymatch i2 with
                              | OpImm ALU_ADD _ _ ?imm => eval vm_compute in (bv_unsigned imm)
                              | _ => constr:(0%Z) end in
                  let sz := eval vm_compute in (szm1 + 1)%Z in
                  let OK := fresh "SHOK" in
                  first [
                    match goal with
                    | ACC : acc asegs m ?a ?n |- _ =>
                        assert (OK : sh_ok b (X + sz - 1)) by (apply (shk_ok m a n X sz b ACC K); lia)
                    end
                  | fail 1 "shbr: cannot prove the access addressable:" X sz ];
                  let BB := fresh "BB" in
                  assert (BB : 0 <= bv_unsigned b < 8)
                    by (pose proof (bv_unsigned_in_range 8 b); destruct OK as [?|[? ?]]; lia);
                  rewrite ?(sxb_small b) by lia;
                  shbr_merge ru FAST OK; clear K BB)
            | _ =>
                (* [comment removed for export] *)
                let OK := fresh "SHOK" in
                first [
                  match goal with
                  | ACC : acc asegs m ?a ?n |- _ =>
                      assert (OK : sh_ok b (X + 8 - 1)) by (apply (shk_ok m a n X 8 b ACC K); lia)
                  end
                | fail 1 "shbr: cannot prove the 8-byte access addressable:" X ];
                apply sh_ok_8 in OK; [ | lia ];
                rewrite ?(sxb_small b) by lia;
                brF; clear K OK
            end)
      | _ => fail "shbr: no shk fact for" b
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac shnorm :=
  repeat match goal with
  | |- context [Z.shiftr ?x ?k] => is_Zlit k; rewrite (Z.shiftr_div_pow2 x k) by lia;
        let v := eval vm_compute in (2 ^ k)%Z in change (2 ^ k)%Z with v
  | |- context [Z.shiftl ?x ?k] => is_Zlit k; rewrite (Z.shiftl_mul_pow2 x k) by lia;
        let v := eval vm_compute in (2 ^ k)%Z in change (2 ^ k)%Z with v
  end.

Ltac at_stop stops :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) =>
      let b := eval vm_compute in (existsb (Z.eqb q) stops) in
      lazymatch b with true => idtac end
  end.
Ltac clear_shl := repeat match goal with H : ov_read_bytes _ _ _ 1 = Some [_] |- _ => clear H end.

(* [comment removed for export] *)
Ltac frame_step :=
  next_instr ltac:(fun i =>
    lazymatch i with
    | OpImm ALU_ADD ?rd ?rs ?imm =>
        let d := eval vm_compute in (bv_unsigned rd) in
        let r := eval vm_compute in (bv_unsigned rs) in
        lazymatch d with 2%Z => lazymatch r with 2%Z =>
          let k := eval vm_compute in (bv_signed imm) in
          lazymatch k with
          | Zneg _ =>
              let n := eval vm_compute in (Z.to_nat (- k)) in
              reg_val rs ltac:(fun v =>
                lazymatch v with
                | Z_to_bv 64 ?E =>
                    lazymatch goal with
                    | ST : stk _ _ _ E |- _ => carve_frame n ST; lstep
                    end
                end)
          | Zpos _ =>
              reg_val rs ltac:(fun v =>
                lazymatch v with
                | Z_to_bv 64 ?E =>
                    lazymatch goal with
                    | ST : stk _ _ _ E, FRx : rw_cells _ _ E _ |- _ =>
                        lazymatch E with
                        | (?b + ?c)%Z =>
                            let v := eval vm_compute in (c + k)%Z in
                            lazymatch v with
                            | 0%Z => lstep; release_frame FRx ST b
                            | _ => lstep; release_frame FRx ST (b + v)%Z
                            end
                        end
                    end
                end)
          end end end
    end).

(* [comment removed for export] *)
Ltac special_step := fail.

(* [comment removed for export] *)
Ltac awalk1 :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [ shbr | br ]
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => first [ shload; lstep; clear_shl | special_step | frame_step | lstep; try sb_fix; try fix_land32; shnorm ]
  end.
(* [comment removed for export] *)
Ltac awalk stops := repeat (tryif at_stop stops then fail else awalk1).
Ltac awalk0 := awalk (@nil Z).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac merge3 PC r1 r2 r3 :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F _ ?fc ?rv ?m ?ro) =>
      eapply (evt_cut segs (fun ms' => exists u1 u2 u3 : word,
                 ms' = MS (@bvmap_set 5 word r1 u1 (@bvmap_set 5 word r2 u2 (@bvmap_set 5 word r3 u3 R))) F (Z_to_bv 64 PC) fc rv m ro));
      [ | let u1 := fresh "u" in let u2 := fresh "u" in let u3 := fresh "u" in let E := fresh "E" in
          let ms := fresh "ms" in intros ms (u1 & u2 & u3 & E); subst ms; norm_regset ]
  end.
Ltac merge_done := apply evt_done; do 3 eexists; norm_regset; reflexivity.
