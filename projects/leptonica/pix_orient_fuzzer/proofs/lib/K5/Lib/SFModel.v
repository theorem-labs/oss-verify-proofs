(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Export Walk.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_SFModel () := "C56Stdlib6ZArith6BinInt1Z4landI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z@add_nocarry_lxorC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z8lxor_lorC47Corelib4Init5Logic6eq_indI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z8land_0_rC56Stdlib6ZArith6BinInt1Z:land_assocC56Stdlib6ZArith6BinInt1Z9land_diagC56Stdlib6ZArith6BinInt1Z9land_commc69OSSVerify5KrLib2K53Lib7SFModel@lor_disjoint_addC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z@land_lor_distr_rK47Corelib7Numbers7BinNums8positive01C47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z4onesK46Stdlib9micromega7EnvRing5PExpr01C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z9land_onesK46Stdlib9micromega=RingMicromega3Op203C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundI47Corelib4Init5Logic3and00C56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega:ZMicromega;ZArithProof04K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr05K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z3mulc69OSSVerify5KrLib2K53Lib7SFModel6land_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53Lib7SFModel8land_W64C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53Lib7SFModel>land_even_maskC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib7ZBridge;Z_to_bv_eqmC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z3oppC45stdpp9bitvector;definitions8bv_swrapK46Stdlib9micromega7EnvRing5PExpr06C45stdpp9bitvector;definitions?bv_half_modulusC45stdpp9bitvector;definitions>bv_swrap_smallC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions>Z_to_bv_signed".
Import ListNotations.
Open Scope bv_scope.

Ltac zb_masks_in H :=
  repeat match type of H with
  | context [Z.land ?x ?m] =>
      is_Zlit_zb m;
      let k := eval vm_compute in (Z.log2 (m + 1)) in
      let m' := eval vm_compute in (2 ^ k - 1)%Z in
      constr_eq m m';
      let p := eval vm_compute in (2 ^ k)%Z in
      replace (Z.land x m) with (x mod p)%Z in H
        by (symmetry; change m with (2^k - 1)%Z; change p with (2^k)%Z; apply zb_land_mask; lia)
  end.

(* [comment removed for export] *)
Ltac zs_wrap e ::= zs_wrap_land e.
Ltac zs_wrap_in e H ::= zs_wrap_land_in e H.
Ltac zs_idioms ::= zs_idioms_land.
Ltac zs_idioms_in H ::= zs_idioms_land_in H.

Ltac get_head t := lazymatch t with ?g _ => get_head g | _ => t end.

(* [comment removed for export] *)
Notation W64 := 18446744073709551615%Z.

(* [comment removed for export] *)
Ltac model_eval :=
  lazy -[Z.shiftr Z.shiftl Z.land Z.lor Z.lxor Z.lnot Z.mul Z.add Z.sub Z.opp Z.modulo Z.div
         Z.ltb Z.eqb Z.leb Z.pow bv_unsigned].

(* [comment removed for export] *)
Tactic Notation "model_end" constr(X) constr(t) :=
  replace (Z_to_bv 64 X) with (Z_to_bv 64 t) by (f_equal; model_eval; reflexivity).

Lemma lor_disjoint_add : forall a b, Z.land a b = 0%Z -> Z.lor a b = (a + b)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h01Hh11ah21bh31zp;2p;3p;4p;6g0000j28Tg000Nj31Tg000hj22Tg001Fj20Tg001cj37Tg002Mj46Tg002ij23Tg003Fj34Tg003hj65Tg004DR0f1R1f0R2'8g004b510P0f2R3/21R4f3/039102X30P01031P4A7312C61331A4312E5W0X20W1o"). Qed.

(* [comment removed for export] *)
Lemma land_even_mask : forall y, Z.land y 18446744073709551614 = (Z.land y 18446744073709551615 - Z.land y 1)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h01zh14__x1h24__x2h37__arithh44__ffh58__varmaph65__with71yp;1p;2p;3p;4p;7p;6g005@j17Tg005ej1=Tg0000j20Tg002ij2:Tg006Cj29Tg000Nj34Tg001Fj28Tg006`j1ATg007@j1?Tg007`j2>Tg008>j1STg008\j4RTg009:j1PTg009Xj1MTg00:Cj2;Tg00:fj3LTg00;Ij3JTg00;lj4ITg00<Wj7HTg00=;j2ETg00=]j2DTg00>7j2FTg00>cj3CTg00?Bj4GTg00@4j1BTg00@Vj36Tg003hj6KTg00A:j1@Tg00A]j2<Tg00B@j3NTg00CDj3OTg00Cnj11Tg00DSj6QTf0R0#1#1p=U%10#1#1#1p=T%10#1#1#1#1#1#1#1p=2g004DR1g004bR2740p=5P1f4f3f2R3f1R4P0EQp=3g00E1R5#U#T#2#2#2#2#2#2#2#7#=R6,00R7%=5R8,00R9':R:1046R;1048R<,90541X01R=1879P=g00EVR=#A%?=P11>13P4%S1CR%P1%M1R=g00FBg00FaR>P>g00GAR>P11;15R?g00Ga%75,;1R59L1?=J15CIg00HHFH1E=>P0P3g00HhR>g00IHR='D1F03=4>=dAC124CGb4b5b6X11X211804/949410^11^21P0P<P;O2b3P:1097R:%50X01R;1090R</06P;1009R4%57X01R21000R=/08P2P01096R2#5X01P11086,00P;%B0P2A6086EKP=%@0D3P4A6008D3P<1<90D3P:A6906D310791<79D39N79D31:68,00AO068D3X71o"). Qed.

Lemma land_1 : forall y, Z.land y 1 = (y mod 2)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h07__arithh14__ffh28__varmaph35__with41yh51zp;1p;2p;3p;4p;7p;6g005@j1FTg005ej12Tg00Ihj2;Tg00JEj20Tg000Nj31Tg00=]j23Tg00Jej1<Tg0000j2:Tg006`j17Tg007@j16Tg008>j15Tg009:j18Tg009Xj19Tg00KCj24Tg00;lj4ETg00<Wj7DTg00=;j2=Tg00>7j2>Tg00>cj3?Tg00?Bj4@Tg00Kfj2ATg00LBj3BTg00DSj6CTg004DR0P0f0R1g00E1R2#F#2R3%22R2';'0f1R4/039101X501013,30%<2,:1g00EVR3#7%63%50%80%90R3g00FBg00FaR5P5g00GAR5P0g004bR6,40g00Le1402CEg00HHFD1=35P1f2R5g00HhR3g00IHR7'31>15=137dA?064C@b1b2b31A62P1b09B12ECW4o"). Qed.
Lemma land_W64 : forall y, Z.land y 18446744073709551615 = (y mod 2^64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h07__arithh14__ffh28__varmaph35__with41yp;1p;2p;4p;7p;3g005@j10Tg005ej1ATg006`j13Tg007@j12Tg008>j1@Tg009:j1:Tg009Xj14Tg00KCj21Tg00;lj45Tg00<Wj76Tg00=;j27Tg00=]j28Tg00>7j29Tg000Nj3?Tg00>cj3>Tg00?Bj4;Tg00Kfj2<Tg00LBj3=Tg004DR0f0R1g00E1#0#0#0#0#0#0#AR2g00EVR3#3%23%@0%:0%40R3g00FBg00FaR4P4g00GAR4P0g004bR5,10g00Le1102C5g00HHF61734P1f2R4g00HhR3g00IHR6'81914=?36df19>05C;b1b2b31<52P1b03=W4o"). Qed.

(* [comment removed for export] *)
Lemma round_even_idiom : forall x, (0 <= x)%Z ->
  Z_to_bv 64 (Z.land (x + 1) 18446744073709551614) = Z_to_bv 64 (x + Z.land x 1).
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h01zh12H0h23H10h33H15h43H20h52H5h62Hah77__sat25h84__x1h95__x10h:5__x11h;4__x2h<4__x3h=4__x4h>4__x5h?4__x6h@4__x7hA4__x8hB4__x9hC1HhD2H1hE3H11hF3H12hG3H13hH3H14hI3H16hJ3H17hK3H18hL3H19hM2H2hN3H21hO3H22hP3H23hQ2H3hR2H4hS2H6hT2H7hU2H8hV2H9hW2HxhX7__arithhY4__ffhZ7__sat24h[8__varmaph\5__with]1qh^2q0h_2q1h`2q2ha2q3hb1rhc2r0hd2r1he2r2hf2r3hg1xp%0p&0p;1p;2p;3p;4p;6p;7p;8g005ej1CTg001Fj21Tg00Cnj16Tg005@j14Tg0000j2KTg006Cj2;Tg00Ihj2wTg00JEj20Tg00MLj2[Tg00Mmj1pTg00NFj27Tg00Ncj2RTg00OJj2<Tg00Ofj2VTg00Kfj2FTg00PMj2GTg00Phj2STg00QNj2QTg00R4j2lTg00=]j2dTg00RUj2vTg00S=j3tTg00Saj12Tg00T@j1sTg00T^j2aTg00U?j2gTg00Uhj2_Tg00VQj2fTg00W=j2ZTg00Wik40ATg00XJk30@Tg00Xkk30?Tg006`k10<Tg00YWj3oTg007@k10;Tg007`j2]Tg008>k10:Tg009:k106Tg009Xk105Tg00KCj2bTg00Z7k104Tg00ZYj3UTg00[<k103Tg00[Zk302Tg00:Cj2jTg00;Ik301Tg00=;k200Tg00>7j2~Tg000Nj3LTg00>cj3|Tg00?Bj4}Tg00\=j2iTg00\Zj1qTg00DSj6\Tg00]Tj1{Tg00^Pj1zTg00_Rj3yTg00`Qk307Tg00a:j3^Tg00ack308Tg008\k409Tg00;lj4cTg00<Wj7nTg00bLj7uTg00c0k60=Tg00:fk30>Tg00cTj8eTg004bR0f0R1'Fp=`%61#6#6#6p>0C%61#6#6#6#6#6#6#6p=J%41#4p=mg004DR2f2R3f1R4'0;L1p=AAL241p=rAL210p=If3R51i34/115L2p=@1F031<41'Gp=91041,13p=D1<41,G3p=x1g21p=3B07241p=8A^241p==A^2419^23p=5B08241p=O%41#4#4#4p>0B%41#4#4#4#4#4#4#4p=NA^234/Z1p=:1Z41,Z3p=MP2P3P4P1H09p=H1j21p=?P2P4g00LeP1Ccp=WP4g00FBR6g00FaR7P7g00GAR8P1g00HHR9Fnp=>P2P4g00d8P1Ccp=YP3P6P7P7P8P4P1Fup=XP3P6P7P7P8P2P4g00GaP1CcP9Fnp=BP4P6P7P7P8P1J0=p=kB0>241p=EP5P6P7P7P8P3P4P1Gep=Pf6R9P6P7P7P8f5R:f4R;P5P6P7P7P8P3P4P1GeGep=T11419L23p=h%`1R6g00E1R<#CR=,14R>%6<R?#6R@$0C#J#J#J#J#J#J#JRA#4#C'KS001K4=RB,14P2%6A#C,K>RA1K>=RC';%4<RD#CRE%4DRF#4RG#4#mRH#CRI'wRJ1K3=,13/0JRK5A1X02P210>JRL113=RM/K=,;1?AJKX02P210>ERN10MJRO/;1?AJKX02P2104E10ME,;ORO/0JRM1131/0J'rX021;LN/[J%IJRN#pRLPOPJ17OJPMC@[1ROJ1<0JRO115=RM/0J10ME';RM/0JRK?9KJ[1VMJ1<J0RM11;=RK/0J10KE';RP/0JRQ,<J1FQ0'G[1SPJ11:=RP/0J10PE';RP/7J#I\N1QPJ119=RP/0J10PE';RQ?AJQ\N17QJP2f7RQ/1=RR/0J10RE';/0JP2f8RR?DRE/[Jf9RS?DSERTPJ17TJ10TJC@\L1RTJf:RT?DTERU/0JRV?9VJ\O1VUJf;RU?DUERV/0JRW,<J1FW0'G\M1SVJf<RV?DVERW/7J#I\N1QWJf=RW?DWERX?AJX\N17XJP2f>RX?DXE/0JP2f?RY/[E%IERZ#pR[f@R\PE17\E10\EC@[1R\E1<0ER]fAR^/0ER_?9_E[1V^E1<E0R_fBR`/0ERa,<E1Fa0'G[1S`EfCR`/7E#I\Z1Q`EfDR`?AE`\Z17`EP2fER`/0EP2fFRa/1=/[JfGRb/1=RcPJ17cJ10cJC@\L1RcJfHRc/1=RL/0JRd?9dJ\O1VLJfI/1=RL/0JRd,<J1Fd0'G\M1SLJfJ/1=RL/7J#I\N1QLJfK/1=RL?AJL\N17LJP2fL/1=/0JP2fMRL/1=/[EfNRM/1=RdPE17dE10dEC@\[1RdEfORd/1=R[/0ERe?9eE\]1V[EfPR[/1=Re/0ERf,<E1Ff0'G\_1SeEfQ/1=Re/7E#I\Z1QeEfR/1=Re?AEe\Z17eEP2fS/1=/0EP2P:g00d_Re1l0E'dP]eR_O1Ax61EPW1l0J,dePOeReO1A9RRJR6P`P_O1A9\\EPLPeO1A9ccJfUR`PeO1A9[[J1vEI%`IPO[RO\]%`ER]g00eER[AtEI4UW6%`J\[^6]P4P_O1POg00EVROg00eaR_#2R]#2R[#2RI#2Re#2Rf#2Rg#2Rh#2Ri#2Rj#2Rk#2#2Rl#2Rm#2Rn#2Ro#3Rp%s<,a2Rq%3mRm'8Rr%3jRj%3hRh'=Rs'=1g2_R_18qpRt%3lRl%3gRg,8q%3IRI%3[R['=55j35%3]R]18ql%3kRk;5j%2oRo#2Ru#2#2Rv#2Rw#3Rx%3vRv%3nRn;5r1_2ERy/O]1Oy_Ry%3uRu,8qRz%3i,8q75k75x%2wRw#2Ri#2R{#3R|%3iRi%3oRo,8q,=u35%3f%4H#m$0B#N#N#N#N#N#NRf#4Ru#C,_2/O_?5Ikg00f@R}'f,Z_5:_5M_3:3:5M_5:_3M3:18qkR~/=s18qj,=k95op%3e,8q=5hI95r~%3wRw18qvR~1=pm351=ot95iw%6DRtP2%CfRf,a2P<1a2=H0A60@2A5ix~A5xvz1_2fRf/O_1Of[1=Ig35/f}5:y5:|%2{#2R{#3,8qA5inm%2{R{#2#3%3{18qx75w%4u#C,_2/O[/=l95]_/f}3:3:40?,Z_9:_I5M_5M_9:]_5:o5M_5:l&0<O5oO3o&0;O1]2R&0:2RO7H;1]2T?H9O7H31]2S?H:O1]2U?HQO7H57H4&062&052R51b20RO%?tRl'W,>51b2ER_,Yl,>55X5&047R7P5P5AB5_O,k5RoP7%??R]1b2='ER=%6t#?9U2_/El5B5CPP7P5%?FRI,WO,>5&03H:022_RH,YI,>55X5P7P5P5AB5HO,k5R}P7%4t#?9U2H/EI9B5=CPP7P5%?@R@,WO,>51Y@_,>55X5P7P5P5PoP7%6F#?9U2_/E@9B5]CPP7P5%?DRD,WO,>51YDH,>55X5P7P5P5P}P71E]@%?G9U2H/ED5B5CPP7P51j2<R<,WO,>51Y<H,>55X5P7P5P5P}P7B012Il%4?#?9U2H/E<5B5CPP7AB5<DFTFTFTFTFT20058P1P3g00HhR5g00IHR8'd1~13=L58dA|204C}bYb[b\X82X;2X<2X=2X>2X?2X@2XA2XB2X92X:2A9;;Eg00flR0\ZRZPKPEPVP9C@[A9::JP0\NRNPPPJPWPQC@[A9TTEPRPEPXPVC@\ZA9QQJ11TX1iJYRJ;hS\N1;WX?hJT\N1rTU[\6[[[[[[[[^82^;2^<2^=2^>2^?2^@2^A2^B2^92^:2P1PTP^PcPdPbfVPSP\f]PMP`PRPYPQPaP9PLP:fTP;f[OEbXb7bZb7b1b5b2b3b4bfbabPbObNb4bLbeb`bKbJbIb3bHbdb_bGbFbEb2bVbcb^bUbTbSb5bRbbb]bQbMbDb1bCPB%q4E\PC%q>E\PA%{>E\Q00%z>E\3yWWXg2o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac bool_atom_cases :=
  repeat match goal with
  | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b)
  | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
  | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec0 a b)
  end.

(* [comment removed for export] *)
Ltac weq :=
  first [ reflexivity
        | f_equal; zeq
        | rewrite round_even_idiom by zrange_nonneg; weq_arith
        | weq_arith ]
with weq_arith :=
  apply Z_to_bv_eqm; rewrite ?land_even_mask, ?land_1; zb_masks; cbv delta [Z.b2z]; cbn [negb];
  bool_atom_cases; cbn [negb]; pose_word_ranges; Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
Ltac ms_eq :=
  first [ reflexivity
        | lazymatch goal with
          | |- Z_to_bv 64 _ = Z_to_bv 64 _ => weq
          | |- _ = Z_to_bv 64 (bv_unsigned _) => symmetry; apply Z_to_bv_bv_unsigned
          | |- Z_to_bv 64 (bv_unsigned _) = _ => apply Z_to_bv_bv_unsigned
          | |- context [mkR] => unfold mkR; ms_eq
          | |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => f_equal; ms_eq
          | |- TNode _ _ _ = TNode _ _ _ => f_equal; ms_eq
          | |- Some _ = Some _ => f_equal; ms_eq
          end ].

(* [comment removed for export] *)
Lemma signed_of_Z : forall z, (-2^63 <= z < 2^63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h02Hah16__sat1h24__x1h31zh42Hzh57__arithh64__ffh76__sat0h88__varmaph95__witp;1p;2p;3p;4p;7p;8p;6g005@j10Tg005ej15Tg00Cnj13Tg00Ihj2?Tg00gIj1;Tg00Kfj21Tg00OJj22Tg00PMj24Tg00[<j16Tg00gfj2@Tg000Nj39Tg00RUj2=Tg00S=j3<Tg00R4j2WTg00=]j2:Tg006`j1VTg007@j1UTg007`j2TTg009:j1KTg009Xj1FTg00KCj2ETg00[Zj3DTg00hMj2CTg00:Cj2BTg00;lj48Tg00bLj7ATg00Z7j1GTg00cTj8HTg00=;j2ITg00>7j2JTg00>cj3>Tg00?Bj4LTg00i0j1MTg00i^j3NTg00jKj2OTg00k1j2PTg00kYj2QTg00DSj6RTg00<Wj7STf1R0g00FBR1g00FaR2P2g00GAR3f0R4g00HHFSp=7g004DR5g00E1R6#0R7#5R8%36#3#3#3#3R9#5R:'?R;#;R</14124;'4R=P5%07#0#0#0#0#6R7/@0f2R>9954X351=8:g004bR?/28R@11?:12?;[RA[11?8RBg00eERCA<8:0UW011?;\C^0BP0g00d_1W?8':P@eO1PAg00EVRA#V%UA1T50%K5%F5RAP1P2P2P3PAP1P2P2P3P51E58%695D5R9,C5g00Le1B56R6C8,7AP5P6g00d8P9C8,7AFAR9%G2P9GH1IA3P4P>g00HhRAg00IHR3':1J4>=9A3dA>5?0CLb6b8b9X2511<0120;'4\=^25P4f5f4O2b5b1b7b1%M7R4#;/101204'4e9N701O70,P71Q70ERW4W3o"). Qed.
Ltac signed_lits_in H :=
  repeat match type of H with
  | context [bv_signed (Z_to_bv 64 ?z)] => rewrite (signed_of_Z z) in H by lia
  end.

(* [comment removed for export] *)
Lemma mod64_land63 : forall y, (y mod 64 = Z.land y 63)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h07__arithh14__ffh28__varmaph35__with41yh51zp;1p;2p;3p;4p;7p;6g005@j10Tg005ej11Tg00Cnj1=Tg00Ihj26Tg00JEj25Tg000Nj32Tg00=]j23Tg00Jej1<Tg0000j2;Tg006`j1:Tg007@j17Tg008>j18Tg009:j19Tg009Xj1GTg00KCj24Tg00;lj4FTg00<Wj7ETg00=;j2DTg00>7j2?Tg00>cj3>Tg00?Bj4@Tg00Kfj2ATg00LBj3BTg00DSj6CTg004DR0P0f0R1g00E1R2#0R3#1%=2#0#1R2'6'5R4f1R5%03#0#0#0#0#1'5=201X501304%<2,;1g00EVR4#:%74%80%90%G0R4g00FBg00FaR3P3g00GAR3P0g004bR6,40g00Le1402CFg00HHFE1D43P1f2R3g00HhR4g00IHR7'31?13=247dA>065C@b1b2b31A62P1b09B12ECW4o"). Qed.
Lemma land63_idem : forall y, Z.land (Z.land y 63) 63 = Z.land y 63.
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h01yh11zp;1p;2p;3p;6g00Cnj11Tg005ej16Tg0000j20Tg000Nj32Tg00=]j25Tg00@Vj34Tg003hj63Tg004DR0P0f0R1g00E1#1#1#1#1#1#6R2/02'0f1/029201X101012R3,501032A4122E3W0o"). Qed.

Ltac zs_idioms_sf :=
  match goal with
  | |- context [Z.shiftr (Z.land (Z.shiftl ?x ?k) 18446744073709551615) ?k] =>
      rewrite (zb_shl_shr_land x k) by (first [lia | zrange_nonneg])
  | |- context [(?y mod 64)%Z] => rewrite (mod64_land63 y), ?land63_idem
  end.
Ltac zs_idioms_sf_in H :=
  match type of H with
  | context [Z.shiftr (Z.land (Z.shiftl ?x ?k) 18446744073709551615) ?k] =>
      rewrite (zb_shl_shr_land x k) in H by (first [lia | zrange_nonneg])
  | context [(?y mod 64)%Z] => rewrite (mod64_land63 y), ?land63_idem in H
  end.
Ltac zs_idioms ::= zs_idioms_sf.
Ltac zs_idioms_in H ::= zs_idioms_sf_in H.
