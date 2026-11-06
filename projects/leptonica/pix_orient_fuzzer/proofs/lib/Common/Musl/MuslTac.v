(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import RelocKit.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_MuslTac () := "C56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvC69OSSVerify5KrLib6Common5Reloc5Reloc2rlC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic6eq_indI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z3subK47Corelib7Numbers7BinNums1Z02C69OSSVerify5KrLib6Common5Reloc5Reloc:fetch_evenC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3powC69OSSVerify5KrLib6Common5Reloc5Reloc8rl_u_modC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z9rem_mul_rC56Stdlib6ZArith6BinInt1Z8mul_commC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7mod_addC56Stdlib6ZArith6BinInt1Z7mod_modK46Stdlib9micromega7EnvRing5PExpr04C47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z7add_modC59OSSVerify5KrLib6Common5Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op205C45stdpp9bitvector;definitions7bv_wrapC46Stdlib6ZArith4Zdiv9Zplus_modC69OSSVerify5KrLib6Common5Reloc5Reloc@Z_to_bv64_mod_eqC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedC59OSSVerify5KrLib6Common8PropExec5v_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc8rl_add_lC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc8rl_add_rC1?~~~~~~~~~~~~~~~".
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rl_of_Zsum : forall d c k c', (c + k = c')%Z -> Z_to_bv 64 (c + d + k) = rl d c'.
Proof.
ltac2:(KReplay.run1 (kr_t_MuslTac ()) [] "h04__x1h14__x2h24__x3h32c'h41Hh57__arithh64__ffh78__varmaph85__with91ch:1dh;1kp;2p;3p;1p;4p;7p;8p;6g0000j20Tg000Mj32Tg000gj11Tg001Lj1;Tg001jj1ITg002Mj26j1?Tg0033j27Tg003mj28Tg004Gj1<Tg004gj1:Tg005Gj25Tg005ej49Tg006Cj1HTg006aj1GTg007Lj24Tg007oj33Tg008Rj1FTg0097j4ETg009bj7@Tg00:Fj2ATg00:hj2BTg00;Tj3>Tg00<3j4CTg00<ej8DTg00=Bj6=Tg00=^R0f2R1f1R2'0f0R3520P0f3R4/01R5g00><R6#1R7#1#1#1#1#1#;R8#IR9f4R:f5R;'0/04,6817;332X30P0P9%?8R<P<104:/01R=105:P9\0/8<g00>aR<#<%:<P01501P21504C9%H0%G0R<g00?Mg00?lR>P>g00@LR>P01406R?1407R7530%F6,40R6530g00@lA30?6=307CEg00ASF@1A<>P3P1g00B3R>g00BSR<'81B31=2><dg00C3=>02CCb6b7b8X00X10X201032/011031/02520^00^10^20P3P4P;P:O3b5GD168=17:5529eP2P3E=W4X30X;0X90W:o"). Qed.
Lemma rl_of_Z : forall d c, Z_to_bv 64 (c + d) = rl d c.
Proof.
ltac2:(KReplay.run1 (kr_t_MuslTac ()) [] "h01ch11dp;1p;2g000gj10Tg001Lj14Tg001jj12Tg0033j21Tg003mj23Tg00=^R0g00><#0#0#0#0#0#0#4#2f1f0'1'3X00W1o"). Qed.

(* [comment removed for export] *)
Ltac rl_zaddr H :=
  repeat match type of H with
  | context [Z_to_bv 64 (?c + ?d + ?k)%Z] =>
      is_Z_lit c; is_Z_lit k; tryif is_Z_lit d then fail else
      let c' := eval cbv in (c + k)%Z in rewrite (rl_of_Zsum d c k c' eq_refl) in H
  | context [Z_to_bv 64 (?c + ?d)%Z] =>
      is_Z_lit c; tryif is_Z_lit d then fail else change (Z_to_bv 64 (c + d)%Z) with (rl d c) in H
  | context [Z_to_bv 64 (?a + ?b)%Z] =>
      is_Z_lit a; is_Z_lit b;
      let c := eval cbv in (a + b)%Z in change (a + b)%Z with c in H
  end.
Ltac rl_zaddr_goal :=
  repeat match goal with
  | |- context [Z_to_bv 64 (?c + ?d + ?k)%Z] =>
      is_Z_lit c; is_Z_lit k; tryif is_Z_lit d then fail else
      let c' := eval cbv in (c + k)%Z in rewrite (rl_of_Zsum d c k c' eq_refl)
  | |- context [Z_to_bv 64 (?c + ?d)%Z] =>
      is_Z_lit c; tryif is_Z_lit d then fail else change (Z_to_bv 64 (c + d)%Z) with (rl d c)
  | |- context [Z_to_bv 64 (?a + ?b)%Z] =>
      is_Z_lit a; is_Z_lit b;
      let c := eval cbv in (a + b)%Z in
      lazymatch c with Zpos _ => change (a + b)%Z with c end
  end.

(* [comment removed for export] *)
Ltac rl_zaddr_all :=
  repeat match goal with
  | H : context [Z_to_bv 64 (?c + @rl_delta ?RL ?b)%Z] |- _ =>
      is_Z_lit c; change (Z_to_bv 64 (c + @rl_delta RL b)%Z) with (rl (@rl_delta RL b) c) in H
  | |- context [Z_to_bv 64 (?c + @rl_delta ?RL ?b)%Z] =>
      is_Z_lit c; change (Z_to_bv 64 (c + @rl_delta RL b)%Z) with (rl (@rl_delta RL b) c)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[export] Ltac u_norm ::= rl_unorm; repeat rewrite u_Z2bv by lia.
#[export] Ltac unorm ::=
  rl_unorm;
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
      lazymatch z with
      | context [bv_unsigned (Z_to_bv 64 _)] => fail
      | _ => rewrite (u_Z2bv z) by lia
      end
  end.
Ltac rzsimp := zsimp.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac addrZ a :=
  lazymatch a with
  | rl ?d ?c => constr:((c + d)%Z)
  | Z_to_bv 64 ?z => constr:(z)
  end.
#[export] Ltac rdn_peel1 ::=
  first [ rewrite rdn_wbytes_out_Z by (zlen; lia_fast)
        | lazymatch goal with
          | |- rdn ?segs (wbytes ?m ?b ?bs) ?a ?n = _ =>
              let zb := addrZ b in let za := addrZ a in
              change (rdn segs (wbytes m b bs) a n) with (rdn segs (wbytes m (Z_to_bv 64 zb) bs) (Z_to_bv 64 za) n);
              rewrite (rdn_wbytes_out_Z segs bs m zb za n) by (zlen; lia_fast);
              change (Z_to_bv 64 za) with a
          end
        | rewrite rdn_wbytes_out by (rzsimp; lia_fast) ].

#[export] Ltac rdn_solve ::=
  lazymatch goal with
  | |- rdn _ (wbytes _ ?a _) ?b _ = _ =>
      tryif constr_eq a b then (apply rdn_wbytes_hit8; rzsimp; lia)
      else (rdn_peel1; rdn_solve)
  | |- _ => rdn_hyp
  end.

(* [comment removed for export] *)
#[export] Ltac addr_norm ::=
  match goal with
  | |- context [v_addi (rl ?d ?c) ?i] => rl_val (v_addi (rl d c) i)
  | |- context [v_addi ?x ?i] =>
      let e := constr:(v_addi x i) in
      tryif check_closed_term e then wlit_closed e
      else first
        [ rewrite (v_addi_0 x)
        | let t := zbv_target x i in
          replace e with t by (unfold v_addi; u_norm; first [reflexivity | f_equal; lia]) ]
  | _ => idtac
  end.


(* [comment removed for export] *)
Ltac stepretK F D FK tac :=
  lazymatch type of FK with
  | fetch_word _ ?k = Some _ =>
      stepjr F D k ltac:(gres; tac);
      imm_norm;
      rewrite (fetch_ret_ok _ _ _ FK : v_jalr k 0 = k)
  end.

(* [comment removed for export] *)
Ltac stepjrK F D FK tac :=
  lazymatch type of FK with
  | fetch_word _ ?k = Some _ =>
      stepjr F D k tac;
      imm_norm;
      rewrite (fetch_ret_ok _ _ _ FK : v_jalr k 0 = k)
  end.

Ltac stepretF F D FK :=
  lazymatch type of FK with
  | fetch_word _ ?k = Some _ =>
      stepjr F D k ltac:(gres; first [reflexivity | assumption | bveq]);
      imm_norm;
      rewrite (fetch_ret_ok _ _ _ FK : v_jalr k 0 = k)
  end.

(* [comment removed for export] *)
Lemma rl_ret_ok_near : forall segs d c0 c (w : bv 32),
  fetch_word segs (rl d c0) = Some w -> ((c - c0) mod 2 = 0)%Z -> ret_ok (rl d c).
Proof.
ltac2:(KReplay.run1 (kr_t_MuslTac ()) [] "h02H0h11Eh22H1h32H2h42H3h52H4h62H5h72H6h82H7h92H8h:2H9h;6__sat1h<6__sat2h=1qh>2q0h?1rh@2r0hA1zhB3H10hC3H11hD3H12hE3H13hF3H14hG6__sat3hH2q1hI2r1hJ7__arithhK4__ffhL6__sat4hM6__sat5hN8__varmaphO5__withP2HahQ4__x1hR4__x2hS4__x3hT1HhU3H15hV3H16hW3H17hX3H18hY3H19hZ2Hch[6__sat6h\6__sat7h]1ch^2c0h_1dh`2q2ha2r2hb4segshc1wp%0p;1p;2p;3p;4p;6p;5p;7g004gj1cTg000gj1ITg001Lj1UTg001jj1fTg00CQj1}Tg0033j2LTg00D3j2pTg00E5j2lTg000Mj3BTg00EWj22Tg00F4j1RTg00FRj4eTg00GTj2ZTg00H>j2dTg00H[j2aTg0000j21Tg00I[j20Tg008Rj1MTg00J;j2<Tg00JXj2iTg00K@j2CTg00K\j3gTg00L@j28Tg00M1j2;Tg00MRj1QTg00Mkj29Tg00NRj27Tg00O9j26Tg00O_j2:Tg00PEj24Tg004Gj1|Tg00Pbj1{Tg006Cj1zTg006aj1yTg00Q@j2bTg0097j4XTg00Qcj6xTg00:Fj2wTg003mj2`Tg00:hj2tTg00;Tj3sTg00<3j4rTg00RGj3qTg00Rjj5_Tg00SMj2^Tg00Soj2oTg00T`j4]Tg00UAj3\Tg005Gj2[Tg005ej4mTg007Lj2VTg007oj3STg00Ubj3kTg00VEj6YTg00Vcj4jTg00WDj2uTg00=Bj6vTg00XAj2PTg00X]j2TTg009bj7hTg00=^R0f1R1f0R2'0g00C3R33Bp=>f2R4/11/02p=HP0f4R5f3R6P4P1P2Evp=J1441/02p=G1<12,14p=@1P32p=31012,P3p=EAB023p=?1441,<6/129B05p=A1P341C12'Tp==1C411P23'Tp=51412=B03p=D1041=B02p=FP1g00?MR7g00?lR8P8g00@LR9P2g00ASFhp=W11129B04p=O1C12,T4p=nAB012p=NP0P5P6P4P1P2EYp=Kg00Y8#cg00><R:#IR;#I#I#I#IR<#U#fR=%}=1L64,p51l=23B1246%R;R='>f5R>/L6f6R?1L>5R@P4P1Ce%I<R<#URA/Z@/>=%R<,d=R<9H5?1>2=XA0R@1L?>,ZAP@P2AH>?<R<1a?>DJ1><=f7R<,1>RB/0=%M:S00#M#M#M#MRC#RRD,d=RE9GB=7@=P@11?<RF1<=ERG'0P@P210F=AGF=E7@=RHPFP=PE1i=DRF1C3=RI%3D1C3ERJ[[RK%3=RLg00Z7RMAg=D1UWPRD%3ERN\M^PLRMf8RO,2<RP/8=S01%3Pf9RPf:RQ'2RR/E=\L[S0211PQRS/8GS03%3S%3Gf;RTf<RU'1RV/EG[[S0411QTRW/0GRX/8=S05%3Xf=RX,1URY/0GRZ/E=\L[S061;VGS07%?GR[#QPYPGPYPGPZDA[S0819YGS091C3Gf>RZ,1XR\/0GR]?=]G[S0:17\GS0;1CG3f?R],1ZRZ/0GR^=5G^[S0<16ZGS0=f@R^,1]R]/DG\[S0>1:]GS0?fAR_,1^R^?FG^\[S0@14^GS0AP0fBR[,1_R_/0GR`P01;2=S0B%?=Ra#QRbP1P=P1P=101=DA[S0C191=S0D104=Rc?=c=\IS0E174=S0F1C=3Rc106=Rd=5=d[S0G166=S0H1D5=\aS0I1:5=S0JAF>=>\aS0K14>=S0LP010?=S0MP0fHS0NfIRd'2Re/;=RffJRg,2dRdP=PdP=10d=S0ODA\bRh19d=RifKRj,2gRk/0=Rl?=l=\IRm17k=RnfLRo,2jRp/0=Rq=5=q\cRr16p=RsfMRt,2oRu/D=\aRv1:u=RwfNRx,2tRt?F=t\aRy14t=RzP0fOS0P,2xRx/0=R{P0g00>aR|#|S0Q%c|S0R%{0R|%z0S0S%y0R}P7P8P8P9P01b0=R8g00@lS0T1b03R7CX,W}Ex1w}9S0UP2P4g00B3R9g00BSR~'`1t24=B9~dAs031CrS0VbKbNbOg00ZS\aP2bJR~bIbHbFbEbDbCbBb@b>b:b9b8b7b6b?b=b5b4b3b2b0b;b<bGbLbMS0WPFPKPDPMQ01Q02Q03Q04Q05Q06Q07Q08Q09Q0:Q0;Q0<Q0=Q0>Q0?Q0@Q0AP0P`P0Q0BQ0CQ0DQ0EQ0FQ0GQ0HQ0IQ0JQ0KQ0LP0Q0MP0PfPhPiPmPnPrPsPvPwPyPzP0P{P0Q0QQ0RP|Q0SP0P7g00[0%UC9q08CX,W}Q0UQ0VbKbNbOPJP2bJbIbHbFbEbDbCbBb@b>b:b9b8b7b6b?b=b5b4b3b2b0b;b<bGbLbMS0AD_DJ1>H=11?O?G=ERH/<=11<PS0@/0=R8/12/>=XA011<ORC?G=ER7,<=11OPR|/0=Ry/12/>=XA0P21<7=Rw1^=7DJ10C=/1w/>=108=%?2XA0RwAG|=ER|/<==Hy=PwP210y=RCPyP|P=PFPKPDPM18R=S0?%3R12TU/0=RM#3\L[S0>10V=RDAGV=E;@=RK/8=%3K10\=RK14\=RF/0E;@=/E=\L[18Y=S0=%3Y10Z=R|#3Ry\L[S0<18FE%3F14]=/EE\N[1oZ=%3Z14^=RN#3\L[1;]=1<=N10^=R75O^\b19^=10_=Rv?=v=\I17_=fCRs,1[Rr/0=Rn=5=n\c16r=fDRm,1sRi/D=\a1:i=fERh,1mRf?F=f\a14f=P0fFRf=Hh=P01;1E%?ER`#QP4PEP4PE104EDA[194E106ER9?=9E\J176E1CE3105ERJ=5EJ[165E1D>E\`1:>EAF?E?\`14?EP010<EP0A@<2=/;=A@O1=R`P=P`P=10`=DA\b19`=A@P4=R`/0=RJ?=J=\I17`=A@Q6=R`/0=RJ=5=J\c16`=A@T5=R`/D=\a1:`=A@U>=R>?F=>\a14>=P01<?==HX=P0fSfTR>'2/;=fUR`,2>R>P=P>P=10>=DA\b19>=fVR>,2`R`/0=RJ?=J=\I17`=fWR`,2>R>/0=RJ=5=J\c16>=fXR>,2`R`/D=\a1:`=fYR`,2>R>?F=>\a14>=P0fZ,2`/0=P0P~bab`bYbXbWbVbUbIbHbFbEbDbCbBb@b>b:b9b8b7b6b?b=b5b4b3b2b0b;b<bGbLbMb[b\S0;C]DJ%?C11OQRC/0=R`Pw10S=R>/0=PwP2P>12OPRO/8=%3O12QTRO/0=RJ#3\L[18W=%3W1EY=\L[18D=%3D1EK=\L[1;Y=S0:1<=F=O\K\bS0919\=S08Any|=\IS0717Z=S0610]=Ry=5=y\cS0516]=RF%?N\aRN1:^=RY1Nv_\aRv14_=R9P0PnP0Q0BQ0CQ0DQ0EQ0FQ0GQ0HQ0IQ0JQ0KQ0LP0Q0MP01;d=PkP=PkP=PlDA\b19k=A=qq=\I17p=10u=Rp=5=p\c16u=%?z\a1:t=1N{x\a14x=P0Q0PfP'2/0=P0P~bIbHbFbEbDbCbBb@b>b:b9b8b7b6b?b=b5b4b3b2b0b;b<bGRx9\S=DJ%?>Q0?Q0>18V=%3V%3K\L[Q0:Q09Q08Q07Q06Q05PFPNPYPvP9P0PnP012[s/;=12smRsP=PsP=10s=DA\b19s=12mhRm/0=R[?=[=\I17m=12hfRh/0=Rv=5=v\c16h=fGRY,2fRf/D=\a1:f=Q0N,2YRY?F=Y\a14Y=RNP010e=RFP0Q0QQ0RP01[04P11[06CmQ0SP01V0:R:1V0;R;5S0Q00,V0R6=k0:5S0Q0TAS06;CX,W}Q0UQ0VbKbNbOXQ0XR0XS011211242'1?O41^Q0^R0^S0P2PgPoPjO3bJb@b>b:b9b8b7b6b?b=b5b4b3b2b0b;b<11WR?OPT11VORTP@AHDJ=PwP0P3112M/>=XA0P0P31132/>=XA01`03PJP<EYPDP1EY10T=PVPOP=18O=%3O12UX/E=\L[Q0=Q0<1;\=PZP=PZP=P|DA\b19Z=A=yy=\I17]=A5=77\c16^=%?9\a1:_=1Nnr\a14r=P010i=P01;s=PmP=PmP=P[DA\b19m=A=vv=\I17h=10f=Rh=5=h\c16f=%?N\a1:Y=1NFe\a14e=P0Q0OP0P~b@b>b:b9b8b7b6b?b=b5b4b3b2b0b;b<CjDK11QUP2DJb0b110`=A\C=xDKb1Q0@?G=ERx/<==H8=P8PxP=Q0;C]DKb11<=H1^=HDKb110BGPBP=PEQ0WQ0AD_DKb11L?5,ZA1a?5DKb1'uWZWTWcX]0X^0X_0Wbo"). Qed.

(* [comment removed for export] *)
Lemma rl_rel_add : forall dX t dY u, v_add (Z_to_bv 64 ((t + dX) - (u + dY))) (rl dY u) = rl dX t.
Proof.
ltac2:(KReplay.run1 (kr_t_MuslTac ()) [] "h01zh14__x1h24__x2h34__x3h44__x4h57__arithh64__ffh78__varmaph85__with92dXh:2dYh;1th<1up;2p;1p;3p;4p;7p;8p;6g0000j20Tg000gj13Tg00F4j1=Tg00H>j2DTg00I[R0j22j1@Tg001Lj1VTg001jj1OTg00EWj29Tg002Mj24Tg00GTj27Tg0033j26Tg000Mj31Tg00[Wj2ATg003mj2:Tg004Gj1WTg004gj1UTg005Gj2?Tg00Pbj1TTg005ej4>Tg006Cj1NTg006aj1LTg007Lj25Tg007oj38Tg008Rj1GTg00Ubj3FTg0097j4HTg009bj7ITg00:Fj2ETg00:hj2JTg00;Tj3KTg00<3j4CTg00<ej8<Tg00\=j3MTg00=Bj6BTg00\\j3PTg00]dj2QTg00VEj6;Tg00H[j2RTg00^Sj2STg00=^R1P1f0R2f1R3'0R4g00><R5#3R6#=%36R7#3#3#3#3R8#='DR9'2R:%V8R8#OR;f3R<f4R='0R>f2R?,03R@'9,48,78/02,4816=<RA31X01P110?<RB/94RC,A8RD12@9,02,48=1;AX0110D:RDP110C4RA/2912>99112X01P1P1%@A%@BP9P9P1P1\1R>P0P0PAPBP>\1/:0g00>aR0#W%U0P1P11?1=P?%T1C>P31?1<C>%N1%L1R0g00?Mg00?lR>P>g00@LR>P115151516581R6%G5,511517581R75F1=817g00@lP6CHg00ASFI1E0>P2P?g00B3R>g00BSR0':1J2?=1>0dg00C3=K13CCb6b7b8X11X21X31X41194B/0B=114^11^21^31^41P2P?P3P=P<O4b5G<1:19G<12C9/0:/29AMC49EB7PB148D16<?R?51;e148CR<,781Q8CE;1632RC,781R32E;1S<C=1;?eX<1X:1X;1W9o"). Qed.

(* [comment removed for export] *)
Lemma rl_add_l_lit : forall d c k c', (c + k = c')%Z -> v_add (Z_to_bv 64 k) (rl d c) = rl d c'.
Proof.
ltac2:(KReplay.run1 (kr_t_MuslTac ()) [] "h02c'h11Hh21ch31dh41kp;2p;3p;1p;6g0000j21Tg000Mj33Tg000gj10Tg001Lj14Tg001jj19Tg002Mj28Tg0033j22Tg00^Sj25Tg00_Mj36Tg00=Bj67Tg00=^R0f2R1f1R2'1f0R3530P0f3R4/11g00><#0#0#0#0#0#0#4R5#91854f5R5f4R6'2'5125333X00A6641P2P3E7W1X00X40X20W3o"). Qed.
Lemma rl_add_r_lit : forall d c k c', (c + k = c')%Z -> v_add (rl d c) (Z_to_bv 64 k) = rl d c'.
Proof.
ltac2:(KReplay.run1 (kr_t_MuslTac ()) [] "h02c'h11Hh21ch31dh41kp;2p;3p;1p;6g0000j22Tg000Mj33Tg000gj10Tg001Lj14Tg001jj19Tg0033j21Tg002Mj28Tg00^Sj25Tg00`Mj36Tg00=Bj67Tg00=^R0f2R1f1R2'2f0R3530P0f3R4/21g00><#0#0#0#0#0#0#4R5#9f5R6f4R7'11854'5116333X00A6741P2P3E7W1X00X40X20W3o"). Qed.
Ltac rl_addfold :=
  repeat match goal with
  | |- context [v_add (Z_to_bv 64 ?k) (rl ?d ?c)] =>
      is_Z_lit k; is_Z_lit c; let c' := eval cbv in (c + k)%Z in rewrite (rl_add_l_lit d c k c' eq_refl)
  | |- context [v_add (rl ?d ?c) (Z_to_bv 64 ?k)] =>
      is_Z_lit k; is_Z_lit c; let c' := eval cbv in (c + k)%Z in rewrite (rl_add_r_lit d c k c' eq_refl)
  end.
Lemma rl_wrap64 : forall d c c', (c mod 2^64 = c')%Z -> rl d c = rl d c'.
Proof. intros d c c' <-. unfold rl. apply Z_to_bv64_mod_eq. rewrite Zplus_mod_idemp_l. reflexivity. Qed.
Ltac rl_wrap :=
  repeat match goal with
  | |- context [rl ?d ?c] =>
      is_Z_lit c; let c' := eval cbv in (c mod 2^64)%Z in
      tryif constr_eq c c' then fail else rewrite (rl_wrap64 d c c' eq_refl)
  end.

(* [comment removed for export] *)
Ltac rl_cond :=
  idtac;
  first [ cond_compute
        | rewrite rl_ltu_same by (rl_bounds; lia); reflexivity
        | rewrite rl_eqb_same by (rl_bounds; lia); reflexivity
        | (* [comment removed for export] *)
          unfold c_eq, c_ltu, bv_eqb, bv_ltu; rl_bounds; rl_unorm; rewrite ?u_Z2bv by lia;
          first [ apply Z.eqb_neq | apply Z.eqb_eq | apply Z.ltb_lt | apply Z.ltb_ge ]; lia ].

Ltac rl_ret_ok_at b c k :=
  let c0 := eval vm_compute in (c + k)%Z in
  let z0 := eval vm_compute in (code_lookup canon_code b c0) in
  lazymatch z0 with
  | Some ?w0 =>
      exact (rl_ret_ok_near _ _ c0 c _
               (rl_fetch b c0 (Z_to_bv 32 w0) ltac:(vm_cast_no_check (@eq_refl bool true))) eq_refl)
  | None =>          (* [comment removed for export] *)
      let r := eval vm_compute in (site_find canon_sites 0%nat c0) in
      lazymatch r with
      | Some (?i, _, _) =>
          let s := eval vm_compute in (nth_error canon_sites i) in
          lazymatch s with
          | Some ?cs => exact (rl_ret_ok_near _ _ c0 c _ (rl_site_F i cs (@eq_refl _ (Some cs))) eq_refl)
          end
      end
  end.
Ltac rl_ret_ok :=
  lazymatch goal with
  | |- ret_ok (rl (@rl_delta ?RL ?b) ?c) =>
      first [ rl_ret_ok_at b c 0%Z | rl_ret_ok_at b c (-4)%Z | rl_ret_ok_at b c 4%Z | rl_ret_ok_at b c (-8)%Z | rl_ret_ok_at b c 8%Z
            | rl_ret_ok_at b c (-12)%Z | rl_ret_ok_at b c 12%Z | rl_ret_ok_at b c (-16)%Z | rl_ret_ok_at b c 16%Z ]
  end.
