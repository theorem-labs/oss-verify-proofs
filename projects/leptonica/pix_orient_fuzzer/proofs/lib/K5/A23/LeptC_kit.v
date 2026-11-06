(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import StoreFast Cells Arr RzCPS.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import FarStep.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_LeptC_kit () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib2K52AG6Shadow3accC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A237LeptTac3shkC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive01C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib2K53A237LeptTac9acc_read1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow4shadC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C69OSSVerify5KrLib2K52AG6Shadow5sh_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib2K53A237LeptTac8shk_readC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic9False_indK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C69OSSVerify5KrLib2K53Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesK47Corelib4Init9Datatypes6option01K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula03K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C69OSSVerify5KrLib2K53A236ImageA5asegsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes:comparison00K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00C69OSSVerify5KrLib2K52AG6Shadow3SHBC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C69OSSVerify5KrLib2K53Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z6to_natC46Stdlib5Lists4List9nth_errorC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC69OSSVerify5KrLib2K53Lib3Arr9u8ro_readC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01I47Corelib4Init5Peano2le00C46Stdlib5Lists4List>nth_error_NoneC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib5Lists4List6nth_okC69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rK47Corelib4Init5Logic3and01I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC45stdpp9bitvector;definitions>bv_swrap_smallC69OSSVerify5KrLib2K53Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC69OSSVerify5KrLib2K53Lib3Mem4sx32C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00C69OSSVerify5KrLib2K53A238RT_iface3rtsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib2K53A238RT_iface3ARTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface7rt_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface9rt_framesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface7aclientC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InK47Corelib4Init5Logic2or01C69OSSVerify5KrLib2K53A238RT_iface=af_live_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface6rt_sp0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface=client_staticC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface7in_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface9in_fframeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface@in_fframe_shadowC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init5Logic2or02C69OSSVerify5KrLib2K53A238Lept_kitCclient_static_belowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface9in_rangesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC69OSSVerify5KrLib2K53A238RT_iface<af_live_disjC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface7fs_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface?af_frames_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface@af_fshadow_apartC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib2K53A238RT_iface9STACK_WINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface8SEGTOP_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface:USTACK_TOPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface=CLIENT_STATICC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface9RT_STATICC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Lept_kit5accokC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Lept_kit8own_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Lept_kit9own_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A235D_kit8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow7ushadowC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC69OSSVerify5KrLib2K53A238Lept_kit>ushadow_lengthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A235D_kit9agree_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A235D_kit>bytes_at_agreeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8in_splitC46Stdlib5Lists4List9in_app_orC46Stdlib5Lists4List9in_or_app".   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Ltac cut2f PC r1 r2 P :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F _ ?fc ?rv ?m ?ro) =>
      eapply (evt_cut segs (fun ms' => exists u1 u2 : word,
                 ms' = MS (@bvmap_set 5 word r1 u1 (@bvmap_set 5 word r2 u2 R)) F (Z_to_bv 64 PC) fc rv m ro /\ P u1 u2));
      [ | let u1 := fresh "u" in let u2 := fresh "u" in let E := fresh "E" in let HP := fresh "HP" in
          let ms := fresh "ms" in intros ms (u1 & u2 & E & HP); subst ms; norm_regset ]
  end.
(* [comment removed for export] *)
Ltac cut2f_done tac := apply evt_done; do 2 eexists; split; [ norm_regset; reflexivity | tac ].

Lemma shk_zero : forall (m : mem) a n X b, acc asegs m a n -> shk m b X -> 0 <= X ->
  a <= 8 * (X / 8) -> 8 * (X / 8) + 8 <= a + n -> bv_unsigned b = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_LeptC_kit ()) [] "p'0h02H3h14__x1h24__x2h34__x3h42H4h52H9h62OKh74__x4h81Rh97__arithh:4__ffh;8__varmaph<5__with=1bi001bh>3H10h?3H11h@3H12hA2H5hB2H6hC2H7hD2H8hE3OK2hF4__p1hG4__p2hH4__p3hI2b'hJ1ehK1qhL2q0hM1rhN2r0hO1EhP1HhQ2H0hR2H1hS2H2hT1KhU3OK1hV1XhW6__sat3hX1ahY1mhZ1nh[1oi011oh\1zi021li031xp%0p&0p;1p;4p;3p;2p;6p;7p;8g0000j1GTg000Uj1hTg0013j1aTg001VS00j1_Tg0028k40<Tg002mk306Tg003dj1bTg004Bj2?Tg004^j22Tg005;j1MTg005`k30;Tg006Qj28Tg006nj1gTg007NS01j1eTg007nj2\Tg008Lk101Tg008jk100Tg009Uj2YTg00:8j3RTg00:[j2cTg00;>j1pTg00;`j2lTg00<Bj2^Tg00<\j2kTg00=Hj34Tg00=bj3jTg00>Aj4iTg00?3j2ITg00?Pk60:Tg00@Mj1=Tg00ACj1WTg00Abj2FTg00BYS02j2;Tg00C4R0k209Tg00CNj29Tg00D8j2UTg00DYk105Tg00E2j20Tg00ERj2TTg00F9j2OTg00F`j27Tg00G<j2STg00Gbj2NTg00HHj2~Tg00Hij2LTg00IRj2}Tg00J;j3zTg00Jdj2ZTg00KPj1yTg00Knj2xTg00LOj3wTg00M8j2`Tg00Mdj3PTg00NDj1vTg00Nbj6uTg00OFj6fj7{Tg00Obj4tTg00P^j6sTg00Q;j2rTg00QZj4|Tg00R8j3qTg00R[j4]Tg00SFk702Tg00Sjj7oTg00TNk803Tg00U2k104Tg00Udj4nTg00Vik207Tg00WKk308Tg00X4j6mTg00XXR1f0R2'?p=>f2R3f1R4/82'Ip=df3R51834'I/22p=1g00Y6R6P3P4P2C|p=B1c62p=HAq642p=AP6P4g00YTP2C]p=KP4g00Z;R7g00ZZR8P8g00[:R9P2g00[ZK02p=5P6P4g00\:P2C]p=XP3P7P8P8P9P4P2Fop=VP5P7P8P8P9P3P4P2L03p=<1I34/22p=E1742,;3p=3g00\aR:P3&044P2Cnp=DAP342-075p=CA4621p=:A4642p=61712p=JB08642p=@P6P4g00]YP2C]p=QP4P7P8P8P9P2Emp=[g00^@R;#GR<#GS03#GR=#G#G#G#h#a%h=R>#aR?#_[P:f4R:P5P3H0<f5R@@0643%>5RAf6RB%b=R=?d:='?P=P@P=P=C1f7RC/2B'?f9RDf8REPCP=PBP=%M;RF#MRG#bRHC1P:B0;B=3%>=18C=RI#>[g00^eRJ#gRK%eJRL1\63RM1\65RN7B4&016RO&006RP1Y6=RQ%H<RR5R6RS/AQ1c6;RT%HFRF'ARU'K,5P%p8RVPP1KTS,5PPV1Y6HRW,ASRS,KT,5P1XSU,5P5VPC<C<1lP9S04P2P3g00_QRSg00`1RU'^1k23=4SUdAj614CiRUb:b;b<X16X26X361I=4RS/2=1223'?1I=3RX,?4AE=5HRY,?3123:73Y[[^16^26^36P2PD18E=RZf:R[P3P5O5b9bWJ0:%e?R\#_R]AE=IHRI#=g00`QR^#WR_5D[P\P?P2%g?R`CCRa341F2I';X=?-09?P0P?f;R0AE=ZHRZ#=;D_=4]a1F2Z';X=?19>C#:P2f=RZP=P[P=PHC1RI#=;D_=4]a1F2I';Q02f>RIP=P0P=PHC1Ra#=;D_P\P?P4P`CC54]1F4a19>0#:P2f@RaP=PZP=PHC1#=;D_P\P?P5P`CC54]P=PIP=PHC1,F:P=f?RbP=PHC1Rc/U=%:=Rd$05ReP=PaP=PHC1RfP=PfP=10f=C1'6[1Tf=%J=RgP=fARhP=PHC1Ri/0=Rj#>?3j=[1Oi=17=1RiP=fBRjP=PHC1Rk/0=Rl,7=1?l1';[1Sk=P=fCRkP=PHC1Rl/8=#:\d1Nl=P=fDRlP=PHC1Rm/0=/6m\d18m=P6P=fERnP=PHC1Ro/0=RpP6fFRq/U=fGRrAd=r=Rs10r='2'6\e1Tr=fHRt/0=Ru#>?3u=\g1Ot=fIRu/0=Rv,7=1?v1';\i1Su=fJRv/8=Rw#:\d1Nv=fKRx/0=/6x\d18x=P6fLRy/0=S05P6P@g00a01~1='^PgeRzO1S06%>2?32=S07PZPzO1S08%>E?3E=S09%W_Rz,L6RZ1L6_R{1}6=1L6^R^5z6R|'@'@g00aVR}'Z%WzRz,L6%y;,x6=w6{R;'@1@^{/Z}'`=PJK5PJPL%v6R^1\6:R~7B59BM4POPP1Y61RM%HGRG'K,5P1XGQ,5P5VPPVPPPPPPP7P8P8P91QQM,5PEuR9PVAR6QF/AWRWAR6QT/AG'Q,5PC<PV1ATR1AFR'Q,5PC<C<Q04PUb:b;b<X16X26X36X76A3A5=g00bBRA\dRFAE=:HRR12X@'6[123512:5'6[[^16^26^36^76P2P[P:g00b_P0P4PaO6b9b4b5bNbLb@b?b>b5bDbMbKbCbBbAb4b0%=c%=b'6RbePbP6%=fADl2_P\P?PCP`CCRf54]X\6P3%=aRbP2EfADkb_P\P?PBP`CC54]P]%=h=Dl_P\P?PEP`CCR_94]2X[]P2P\P?PaP`CCRbPlPaPhPICtEfA4]bfP]P?Q00P\P?P2Q01P?P?P2PkP4n10110200020020100102Pjn10110100021010200XJ]P\P?PhP`CCP_P2EsA4?hEA4?jDP?Pk1F2o19>nRn#:Ro]6XI?1Fkmg00cT19>lRl#:%Jl?3l=?3plPoP2P2X6oP2O1%Jn?3n=P=PqP=PHC1/0=;3nQ0219>qRq#J?3q=12sH/0=/7q19>r#:P219>tRt#J?3t=AE=wH/0=19>u'719>v#:1Ux=P=PyP=Q05C1,6y\e1Ty=fMRy/0=Rx#>?3x=\g1Oy=fNRy/0=Rx,7=1?x1';\i1Sy=fORy/8=#:\d1Ny=fPRy/0=/6y\d18y=P6fQ/0=P612SH/U=12XHRXP=PXP=10X=C1'6\e1TX=10Y=RX#>?3X=\g1OY=10R=Rg,7=1?g1';\i1SR=1I=@RR/2HRi/8=#:\d1Ni=AE=BHRi/0=/6i\d18i=P6AE=CH/0=P6Q06Q07Q08Q09fZ,9>,73p-0RH1@Z;%Wz,L61@Z{'@,@|/Z}'`=PJKPLAB~:^9B^:ABN3^?B4^7B:POPP%M<R<#G#HRO%H<R<'X,5PPVPP1KMO,5P1[PB5VPPVPPPPP9PVQ03#M#H9R6Q/AO,QW,5PC<PVPP1[PC1X<Q,5P5VPPV1[PEC<C<C<C<Q04PUb:b;b<X16X26X36X76XFHXGHWH1754%>:/;@12RB,6Y\F17:=R=,;EP[[[[[^16^26^36^76^FH^GH^HHP2PAf\,9>R>#JP=P:P@P>f<P4P5P[PkO;b9WEb4b5bNbLb@b?b>b5bDbMbKbCbBbAb4b0P2O1'rWEWUP4P2O2n2001000000121000000W0P2O1n200100000021000011000W6P[P2P@F{W0P2O1b0b8b8bOW6W8P4P2O2n2001000000121000000W0XI?P4P2O2n2001000000121103000bJWSWRWQWTWPX=?XV6XZ6XX6WYo"). Qed.

(* [comment removed for export] *)
Ltac shbr0 :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then _ else _) ?fc ?rv ?m ?ro) =>
      let b := shbyte_of c in
      lazymatch goal with
      | K : shk m b ?X |- _ =>
          let Z0 := fresh "Z0" in
          first [ match goal with
                  | ACC : acc asegs m ?a ?n |- _ =>
                      assert (Z0 : bv_unsigned b = 0) by (apply (shk_zero m a n X b ACC K); [ lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia ])
                  end
                | fail 1 "shbr0: no acc fact covers the granule of" X ];
          rewrite ?(sxb_small b) by lia;
          first [ brF | brT ]; clear K Z0
      end
  end.

Lemma bytes_at_read1 : forall (m : mem) A bs (i : Z), bytes_at asegs m A bs -> 0 <= i < Z.of_nat (length bs) ->
  exists b, ov_read_bytes asegs m (wa (A + i)) 1 = Some [b].
Proof.
ltac2:(KReplay.run1 (kr_t_LeptC_kit ()) [] "p'0h01Eh14__p1h24__x1h31bi001bh41Ah57__arithh64__ffh74__p2h84__p3h98__varmaph:5__with;4__x2h<4__x3h=4cstrh>1lh?1nh@1xhA2E0hB1HhC2H0hD2HbhE2HihF2bshG1ihH1mhI1oi011ohJ2z0p;1p;4p;2p;3p;;p;7p;6p;8p;<g0000j15Tg000Uj1TTg0013j1MTg001VR0j1ATg007Nj1LTg00cnj4aTg004BR1j21Tg00dfj22Tg00eFR2j19Tg00F`j2;Tg00BYR3j23Tg00efR4j16Tg00fFj34Tg00<Bj2:Tg00=Hj30Tg004^j2KTg00U2j1JTg00ACj1ETg00Udj4ITg006nj1STg00Mdj3HTg00Vij2PTg00C4j2OTg00fdj1NTg007nj2GTg008Lj1\Tg008jj1[Tg009Uj2ZTg00:[j2FTg00R[j4=Tg00;>j1CTg00;`j2YTg00<\j2XTg00=bj3WTg00>Aj4VTg00gIl;UTg00hBj4lTg00h\R5j27Tg00i6j3kTg00iYj2DTg00j6j4gTg00j]j2fTg00cTj2QTg00Hij2BTg00WKj3<Tg00Jdj2RTg00QZj4`Tg005;j1bTg00k?j7cTg00SFj7_Tg00X4j6dTg00Sjj7eTg00TNj8^Tg00kcl<]Tg00lHl<hTf1R6g00Z;R7g00ZZR8P8g00[:R9f0R:g00[ZF_p=8P6P7P8P8P9P:Edp=?f2R;P7P8P8P9P6P:Fep=@f3R<P7P8P8P9P;P6P:G^p=>g00Y6R=g00lmR>P=P=P4f4R4P2P<g00mLP;P6P:M<]p=jP>P=P5P2P1g00n9f5R1P4P<P;P6P:M<hp=ig00^@R2#5R5#5#5R?#5#5#5#T#MR@%T?#MR?#ARA[%L?RBg00\aRCP<P;P6Cag00XXRD/16RE12?;#9,;6'3%6;94?<PA1:A:%6<94?4=0A:P0P?f6R0%6154?=0A:%ABRFPCf:RGf9RHf7RI'K#JRJg00`QRK#ERLCI%S?9H?:,PBRB30X3?,O?]0P6%60RM94?I1P?:50AP?PCf;f8RN,KG#JPLCI=0FBX3?P6PCPGPHPNPIP6PJP0P:12?NRO#N%9ORP,1Dp-0RQg00^eRR#SRS%LRRT1G=6%\=RU%[=RVP=1Z=DRWg00YTRX1F=2RYC=,8VRZ1?V<5@V%C8R[PZC>1YV9R\P:P;g00_QR]g00`1R^':1X:;=0]^dAW=D6CVR^b6b9b:X2=W111D:/36PE[^2=^1QP:12?G#9,;HPHPIO3b5b=1:@JM;UClW0X3?P:O1%6494?1%C?50Ag00n[p4p710RA%L:RJP3%A;A4;6:%C;3012<;/76[R312;6/7:%A<A4<;6%C<30R@[124</7;\@Ak;6:P6n2001000000120000000X?>W>W4P3^?>^>J^4AP:P?PIPMP6O412?I/7M%6IRM,7O1DDI,1PRAPOPP1:=PPM1DD:X@=RMPIO1P:X@=PMPIPI1:=IDjEiP:CgPA12?HRA#N%9A,1D1fDH1;DH1DDHRA=0=H'311HDA0=AD'3'Q1DDGP=%ELRA#E,B=RH1B=ARA1B=L1B=KRK5<=5<=5<=g00aVRM'RA<=AK9<=H/RM=HRS5HRPTP=1G=;P61G=<C`PUPVPVP7P8P8P91?V1P=%b2,F=R2g00]YR1PYC=,8V5@V1?V0P=P2P1PWC=,8V5@VFcP[PVP=1F=5R5PXP2C=,8VP[PVP=PYg00\:P5C=,8V9@VZP[1?VIC>C>C>P\P^b6b9b:X2=X;=X<=X1QX7QX8QA0=;:,3<A0=;D,34'Q11;<11D;1;;<'3PN[[[^2=^;=^<=^1Q^7Q^8QP:PCf@f?f=RC'K#JPLCI=0FBX3?,O?f<RB/1D1;DBP612?C#9PBP;P4PGO9b5bJbCb=bAb0bBW0n10110100021110001P:O1b0bIWEWDXG=WFX4=WHo"). Qed.

(* [comment removed for export] *)
Lemma rw_cells_recell : forall (m : mem) A cs cs', rw_cells asegs m A cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs -> rw_cells asegs m A cs'.
Proof.
ltac2:(KReplay.run1 (kr_t_LeptC_kit ()) [] "h01Hh11Ah22E1h32E2h42Hbh52Hwh63Hwfh72W'h82csh93cs'h:1lh;1mh<1np;1p;4p;3p;6g0000j12Tg000Uj1>Tg0013j1:Tg001Vj1?Tg007Nj1=Tg00o6j49Tg00ooj48Tg010ij10Tg00eFj15Tg011ej46Tg012Zj13Tg013Tj11Tg00=Hj34Tg00cnj47Tg014Qj6<Tg014oj4;Tg00^@#2#2#2R0#2#2#2#>#:%>0#:R0#?[g00Y6g015J#=R1g00\aR2f3R3f2R4f1R5C9g00BYR6P2f4R7P3P4C8P2P7P3%04#5C6%34%=0R0%13%1734g00lmR8%07f5R9#034P2f8R:f7R;P9C9[[[f0R<P2f6R=P9P7C8P6%39P2P;P=%19C7P2P:P;%0=#5C6%3=%1;%1:R=540%0:f9R:#0R9548P2f<R6f;R>P:C9[[[[P<%3;P2f:R;P:P=C7P2P>P;%59C6%3:%1;%1>540%0>%06R>548P2f?R;f>R:P6C8P2P;P:%5>C6%36P2P;P:%16R6C7P4P0f=R4#1P2f@R:P;P<C7X:0P7P6P5E<C;P8%04P2P:P;%5<C6X<8P3P>P<E<C;W3W2W7W5W4W6P5P<O2n2001000000120000000W0P5P<O2n2001000000120000000W0X91W8W1W;o"). Qed.



(* [comment removed for export] *)
Lemma sx32_small : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_LeptC_kit ()) [] "h02Hah16__sat1h24__x1h37__arithh44__ffh56__sat0h66__sat3h78__varmaph85__with91zh:2Hzh;6__sat2p;1p;2p;3p;4p;6p;8p;7g0000j12Tg003dj16Tg005;j13Tg016Bj2CTg00F`j21Tg00BYj2:Tg000Uj18Tg0013j1ITg016_j1Hj2GTg00CNj2ETg017Ej2?Tg00<Bj2;Tg00=Hj37Tg017lj2BTg018Tj3@Tg00HHj2WTg006nj1VTg007Nj1UTg007nj2TTg008Lj1RTg008jj1MTg009Uj2>Tg00:[j2LTg00R[j45Tg0198j3=Tg00;>j1JTg019[j2KTg00;`j2FTg00<\j2NTg00=bj3OTg00>Aj4PTg01:>j1QTg004Bj2<Tg01:[j3DTg01;Hj2STg014Qj6]Tg01<Gj8\Tg01<dj1[Tg00SFj7ZTg00Sjj7YTg00TNj8XTg00XXR0f0R1'<p=0f1R2g00Z;R3g00ZZR4P4g00[:R5P1g00[ZFZp=4f2R6P3P4P4P5P2P1FYp=9f3P3P4P4P5P6P2P1GXp=Ag00Y6R3%01g00^@R7#2R8#6R9%37#3#3#3R:#6R;'CR<,11':R=P3%28#2#2#2R8#2R>#8R?#IR@%H?RAPA%88R81G?2RB,E?RC'?P2P@\3/;AP3P21?81=736X931B9;RA1109RD%0;110<[RE[RF%09RGg01=XRHA@9;2UW0R;%0<\H^0GRIP2g00a01W09';PDeRJO1RKPEg00^eRL#VRM%ULRL1T32RN%R3RO%M3RPP31>30g00YTRQ1L37R7C5,4PRRP3P7g00\:RS1>39RT%8:5=3R:C5,4PRU59PRV%J4R4P31K3:PQP7C5,4P=9PUCA1FP5R5P1P6g00_QRUg00`1RQ';1N16=7UQdAO302CPRQb4b7b8X23%Q</<2112<':\=^23P1f5f4R<O2b3b1b5b19D82PC%6>R>,B9%0>1C9>RC,10[R0\DA@9>2VHX0G%0C\H^0GPAPFP;PIPKPEP<PJO1P0PMPLPNPOPPPVP4P3P7PSA=3T?C5,4P99PRCAP5PQb4b7b8X23%02112C':\=^23P1f8f7O2b3b6b1b5b1b;b6,S2E]G\%[B=7@BeW:W9o"). Qed.
Ltac sx32_fix := repeat match goal with |- context [sx32 (Z_to_bv 64 ?z)] => rewrite (sx32_small z) by lia end.

(* [comment removed for export] *)
Ltac arr_sb A idx E :=
  lazymatch goal with
  | UA : u8arr asegs ?mm A ?bs, UAL : Z.of_nat (length ?bs) = _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let SOK := fresh "SOK" in
    pose proof (u8arr_store_ok asegs mm A bs idx (wa E) UA ltac:(lia) ltac:(f_equal; lia)) as SOK;
    zstep;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem mm _ (le1 (Z_to_bv 64 ?z))) _) => rewrite (le1_lit z) end;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem mm (Z_to_bv 64 ?E') [?b]) _) =>
      let N := fresh "UA" in
      assert (N : u8arr asegs (write_to_mem mm (wa E') [b]) A (upd bs (Z.to_nat idx) b))
        by (replace E' with (A + idx) by lia; apply (u8arr_write asegs mm A bs idx b UA); lia);
      clear UA; store_done; rename N into UA;
      rewrite <- (upd_length bs (Z.to_nat idx) b) in UAL;
      let bs' := fresh "abs" in set (bs' := upd bs (Z.to_nat idx) b) in *; clearbody bs'; try clear bs
    end
  end.

(* [comment removed for export] *)
Section KitC.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Lemma new_chunk_apart : forall Σ' (m : mem) p n live0 frs usp a,
  ART RT Σ' m -> rt_live RT Σ' = (p, n) :: live0 -> rt_frames RT Σ' = frs ->
  rt_sp0 RT Σ' - STACK_WIN <= usp ->
  aclient live0 frs usp a -> a < p \/ p + n <= a.
Proof using AF.
ltac2:(KReplay.run1 (kr_t_LeptC_kit ()) ["KitC"] "p'0h01Hh14__x1h21nh32Hxh41pi001ph54__x2h64__x3h73Hinh87__arithh94__ffh:4__p1h;8__varmaph<5__with=4__x4h>4__x5h?1kh@1lhA1fhB1hhC1EhD2H0hE2_HhF2f'hG2hihH2k'hI3FLVhJ2HfhK3SA1hL1ehM3frshN1DhO3FRShP2HAhQ2HBhR2HahS4Hin'hT2HphU3INLhV2LVhW2P0hX3PHIhY4PSEGhZ3SPLh[1Xh\3_H0h]3_H1h^1ah_5live0h`2loha1mhb2n'hc2p'hd3usphe3Σ'i011xi021zp%0p&0p;1p;2p;3p;4p;6p;8p;=p;7g01>4k10MTg0000j19Tg000Uj1uTg0013j1~Tg001Vk10KTg01>lR0j2yTg007Nj1oTg01?Lk30;Tg01@Dj2nTg00Mdj3qTg00=Hj37Tg01A@j2jTg004Bj20Tg01B>k40JTg01C:j31Tg00<Bj2{Tg01CQk30DTg014Qj6vTg01Ckk80ATg00F`j28Tg004^j22Tg01Dmj2RTg003dj1JTg01Ehj1lTg01Fjj2ZTg01Gfj2LTg01Hdj2OTg00cTR1j2?Tg00ACj1mTg00Hij2iTg00Jdj2hTg006nk100Tg007nj2gTg00NDk10LTg008Lk10ITg008jk10FTg00:[j2}Tg00R8j3pTg01Iij3zTg00;>k10CTg005;j1TTg00;`k20BTg00<\k20@Tg00=bk30?Tg00>Ak40>Tg01JLj2FTg01Jik30=Tg01KCk20<Tg01LKj2YTg00DYj1fTg00C4R2j2MTg01MIk30:Tg01Mfm=09Tg01Ngj1kTg01Ock808Tg00BYR3j2DTg00@Mj1>Tg01Pgk807Tg01Qlj4tTg00WKk306Tg00QZk405Tg009Uk204Tg00R[j4xTg00SFj7|Tg00X4k603Tg00Sjk702Tg00TNk80ETg00P^k601Tg00OFk70GTg00k?k70HTf0R4#9#9p=Ag00Y6R5P5f1R6P4Ctp=31R64g01RLR7'Fp=_1F47,06p=e%94#9#9#9p=Kg01SJR7/04p=If2R8/06/?4p=41D64,D8p=r1086/D4p=Nf4R9f3R:'81286/04'?p=51286/04p=]10:81864'Dp=61?64,?8p=aB06564p=Gg00^eR;?q64p=WP5P8P6P4H05p=V1}54p=^20454p=UP8g00Z;R<g00ZZR=P=g00[:R>P5P6g00YTP4Cxg00[ZR?F|p=@P6P<P=P=P>P4J03p=wP8P<P=P=P>P6P4K02p=SP:P<P=P=P>P8P6P4L0Ep=<1864,D8,D:p=;1864,D8p=X%94#Tp=:%T4#Tp=E%T4#9p=CP9P5P:P8P6P4J01p=\A7564p==P5f5R@P9P:P8P6P4K0Gp=`P5P6g00\:P4Cxp=dP6P<P=P=P>P4P?F|p=cP8P<P=P=P>P6P4K0Hp=b10:81064'?p=H1886/?4p=sP5g00lmR<P6P4Ctp=Q%k4,26p=B1n6491:8p=P%>6/04p=[p,2RTR?$0Mg00^@RA#9RB#9RC#9S00#9#ARD#u#~Q00#u#~$0K[1y55RE#oRF1y5<RG#oRHf7RIf6RJ60;?f8RK,n?13J@=qE957Ff9RL,j?=7H9f:RM,_?/09PIPJP@P9H0JPF13MLRN=qEKf;RO/3M=1E4X@FA7ENNA1ENK1{EN40Df<RF,n?RPP:EvA1ENPP?p,2AFS01f=RPPFPOPMP@P4L0Ag00XXRN/8OS0212OMRQ1R?P'e%AD#K#KRD#JRR%IOS0354Q3rP318NF12FORQf>RS,_?%IF94QR3NPKPPPPPFPKD5P418NSf?RQ/2SRTfARU,_?%IQS0494TR3NP3f@RT/2QRVfBRW,R?'e%IT94VRPFPUPUPTPFD5P4fDRV,_?9]WUfCRX/2W%IXS0574RP1PTPQPQg01TGRYC6%lQ1ZWQ1LUQ1OUQ'?3aPTfERZPZPVPTD5PMPUPTPTPYC6fFR[,8UA][ZUp-0R\g00`QR]#mR^#mR_#mS06,i5S071i5_S081i5^S091i5]S0:'G'G'Gg00aVR]'h&00;R^'W%o;R;1g59S0;&0L5R_7V81g5@S0<?V:_7V6&0I5R`&0F5Ra1}5ARb%^BRc5p5Rd%^C%9D#A#K#JRD#U5z5RC5@a&0C=R=Pa%TB#^RB%TAS0=#^S0>5@a1waI5SaP=PaA@aCBP=Q0>9@adC<C<C<20Ba>R>P4P8g00_QRdg00`1RB'{20@48=7dBdB0?5N6H0>RBb9b;b<X15X55X65X=5X>5W:1F:D9]46AN@:J1F@D/0J12:9RD/0@[[[^15^55^65^=5^>5^:\P418WYPXfIRY,R?PWP[fGRdP9P6PSO9b840=W0P4O1%lT1ZXT1LWT1OWT'?3aP1%lU1ZVU1LXU1OXU3aPWPdPdP[PWD5P4%lW20<X418X7P3g01UFR7/YVg01VHRC/YV#fPZfJRePePYPZD5P61Y7[P2P51364Rf=1E7Rg106YS0?PYP4C;XG5,M5X`5fHRh,YC#fPYfNRiPifMRjPYD5[P4PgfKRg,06S0@PgP4C;XG5,M5P2P51384S0A=1E7fLRk,08S0BPkP4C;XG51YCk#fPjfRRlPlfQRmPjD5[P41394S0C=1E7109iS0DPiP4C;P313@6S0E=1E7fORn,0@S0F?Xn6fPRo,YC#fPmfVRpPpfURqPmD5[P413I:S0G=1E710KlS0H?Xl9fSR7,YC#fP1%9A#A#:#:#:#E#C#:#:#K#JRC%9A#A#C#E#A#E#A#E#:#C#A#JRr'3Rs13MJRt57E%EA#:#:#A#C#C#:#C#:#K#JRu%EA#:#C#A#C#C#:#C#:#K#JRv'3Rw=7Et%EA#C#A#:#A#E#E#E#E#C#A#JRx,3vRy=7Etg00bBRt3a10RqP813OIRz97EsPEP0P5P5P5P4P4n2001100000120102102XLES0IPs13FKR{P4D\1=rKPEP0P5P5P5P4P6n2001100000120102102XLES0JPs13PLS0KP6D\1=CP1=CSPCP4fZRsPsPFC61=rPf\R0,0R[]3X@5PCfYR|P|POC61=rFPrPCP0P0P4C6f]R},0R]3XB5PCf[R~P~PrC6P^P;1g56S0LP`Pa%UC=@ab1wa:S0M5SaP=%URS0N=@abS0OC<P>PBb9b;b<X15X:\ANC4610R6S0P[^15^:\P418}rP}P6O3b8W3PPP4P6E`W0W3PQP4PJE`W0P4O1b0P4O1b0WCP4O1A7EwzA7Eyz;atP1A7Ew{A7Ey{/?tfWR{,0RP4Q0K97EwPEQ0IPw13SMRzP4D\1=vMPEQ0JPw13QORwP6D\1=uQ1=uTPuP4P0P0PSC61=vQf^Rr,0R[]3X@5PuP~P~PPC61=vSPvPuPrPrP4C6f_RC,0R]3XB5PuP}P}PvC6P^P;Q0LP`Pa%Uu=@abQ0M5SaP=Q0OC<P>PBb9b;b<X15X:\ANu46Q0P[^15^:\P418CvPCP6O3b8W3PQP4P6E`W0W3PUP4PKE`W0P4O1b0P4O1b0WCP4O1Q0K97Ey/?tP1A7EyzPt10R|P4A7EywPEQ0IPy13TFP4D\1=xFPEQ0JPy13UPP6D\1=vU1=vWPvP4PrPrPTC61=xUf`Ry,0R[]3X@5PvP}P}PQC61=xTPxPvPyPyP4C6faRw,0R]3XB5PvPCPCPxC6P^P;Q0LP`Pa%Uv=@abQ0M5SaP=Q0OC<P>PBb9b;b<X15X:\ANv46Q0P[^15^:\P418wxPwP6O3b8W3PUP4P6E`W0W3PXP4PME`W0P4O1b0P4O1b0WCP4O1Pt10R~P4n010000000X7tP4O1n200100000021100010000W7P4O1n200100000021100011000W7P4O1n200100000021100011000fTRt,0RQ07Q08Q09'GRx'G/h]Q06#m,i5R\Q08Q0:'G'G/h]/W^'WP;1g581g5:7V6P`PaQ0OP=Pa%EA#C#A#:#:#K#K#K#JRA#URv,db,caP=PaQ0>9p5cRzQ0N5@aA@avc5baP=1dbc,caA@azb5baRvC<C<C<P>PBb9b;b<X15X55X6510R4186APDPRPAP:CH129@RA/0:9s:9[[[^15^55^65P4PsP~PpP6PWPdO6b8b[WEW3W7P6P4O2n2001000000121000000W0XB5P6P4O2n2001000000121101000W0X@5P6P4O2n2001000000121101000W0P6P4O2n2001000000121000000bQW0P4O11ZZW1LVW1OVW3aP11Z[X1LZX1OZX'?PVPYPYPhPVD5P41ZdVP2P5A1Efe106dPd1264RuC;X25,M5X45P[PgPgPeP[D5S0NP4A1EfkQ0?PYPuC;X25,M5P2P5Q0A=1Ej108ePe1284C;X25PePnPnPiPeD5P4Q0C=1En109kPk1294C;P3Q0E=1EoP@PjPj12@6C6PiP7P7PlPiD5P4Q0G=1ElPKPoPo12K9C6P613L@&00ERe>0:Et51EP?Q01P|fXRuP{PpPMPJPePqPmPoP4N=0912{pA]MJ{74M1G\x/h]S0GQ07Q0:'G,G\/h]S0:/W^'WS07P;Q0;9V_8Q0<9V_:7V6S0<P`PaQ0=#9#^R_9@azRzQ0=#T#^R]9p5_R\=@acS0=5baP=PaA@a_bR_1db\,ca5SaP=PvC<C<P>PBb9b;b<X15X55X65X=5X>5A]68:Rx10D6S0;'?1096R{?X6A10D89s8:S0E[[^15^55^65^=5^>5P4PKPFPuP|PtP6P:O7b8bNbSWTW7P6P4O2n2001000000121000000W0Xb5P6P4O2n2001000000121101000W0Xc5P6P4O2n2001000000121101000W0P4O11L[V1O[V'?P11LdZ1OdZQ0NP41Lh[P2P51Q64R1=1GgS0NQ0?PY%k4R|,26RuQ00#JRD'FReC;X?<,M<XA5PhPjPjPkPhD5S00P4A1G1jS0?Q0@PgPeC;X?<,M<P2P<1Q84=1GiS0@Q0BPk128|Re/FDC;X?<PkPmPmPoPkD5S0BP41Q94=1GoS0CQ0DPi129|R|/FDC;P31Q@6=1GmS0DQ0F%k6S0A,2@Rm/FD7XnPoPqPqPtPoD5S0FP41QI:=1G7S0>Q0H1BK9R:/FD7XlPHPq1QMJ=1G4XMHP61j?sRHPoEvS0H1QL@=1GHS0OP?Q01P~PsPMPJP7P4L0818NM1BMJRH1R?~'e%IM94HRPEPfP?P}CPRH1BPLRLP81286RoPPCH[^25^45'D3rP3Q021BOIRI1_?0Q0394IRPEPfP?PrCPRI1BSMR0P8PoPSCH[^25^45'D3NPpP~P~PsPpD5S03P418NP1_?C%IS940RPEPfP?PwCP1BUPRNP8PoPUCH[^25^45'D5N0P31BQORO1R?y'eQ0494ORPEPfP?fbRpCP1BWSRqP8PoPWCH[^25^45'DPsPCPCPrPsD5P41R?p,eN%IW94qRPEPfP?feRqCP1BZURtP8PoPZCH[^25^45'DP31BXQQ0574RPEPfP?ffRjCP1B[WP8PoP[CH[^25^45PrfcRWPWPpPrD5P4%IZ94tRPEPfP?fiCP%kZRZ,2YP8PoPYCH[^25^45P4PjPqP~O31BdXA]jqd74jQ0:Q0G/W^'WP;Q0<P`PaQ0==bazP=Pa%UD9z5\,db,ca9Sa_P=PvC<C<P>PBb9b;b<X15X55X65X=5X>5Q0;/?x1FAD9X{6Q0E[[^15^55^65^=5^>5P4PZPYfgfhPWP6PTO7b8bIWIW]P6P4O2n2001000000121000000W0W\P6P4O2n2001000000121000000W0WEP6P4O2n2001000000121000000b0b7WJW7P6P4O2n2001000000121000000W0X?<P6P4O2n2001000000121101000W0XA5P6P4O2n2001000000121101000W0P4O11Oh[P2P5Q0N%>6Rh/0YPY%>uRuC;X?<,M<XA5Q00P4Q0?10hgPgPuC;X?<,M<P2P<Q0@1[8kPk%>eC;X?<Q0BP4Q0C1[9iPi%>|C;P3Q0D%>@PnPn%>mC6Q0FP4Q0>%>KPlPl%>:C6Q0HQ0OP?Q01P~PsPMPJP7P4L07%>PRP1[L8RL54o\H^25^451j?}91G1Q0A,28RH?4PL[^H<^F5'DP3%>SRS1[08R054o\I^25^451j?r91G1A4HS0[^H<^F5Q03P4PEPfP?PyCP%>T1BTF/[854o[^25^451j?w91G1PH%>URU%>NRNP8CH[^H<^F5P6PrP}P7O312r}%>Q1[Or34Q07P;Q0<P`PaA@a]c9bazP=Pa1db],ca9Sa_P=PvC<C<P>PBb9b;b<X15X55X65X=5X>51?x{AX{6@Q0E[[^15^55^65^=5^>5P4PNPUPCPyP~P6PKO7b8bKWEWKP6P4O2n2001000000121000000b0b7WJW7P6P4O2n2001000000121000000W0X?<P6P4O2n2001000000121101000W0XA5P6P4O2n2001000000121101000W0P4O1n200100000021100011000WDP4O1n200100000021100011000WDP4O1n200100000021100011000WDP4O1n200100000021100011000PQPVPVPXPQD5eWYWXP6P4O2n2001000000121000000W0WWP6P4O2n2001000000121000000b0bUWRWZWOWVWPX^5Xd5WMW_X25X45WaWeo"). Qed.
End KitC.

(* [comment removed for export] *)
Ltac chunk_facts RT AF GP p n :=
  match goal with
  | A : ART RT ?S ?mm |- _ =>
      let IN := fresh "IN" in
      assert (IN : In (p, n) (rt_live RT S)) by (solve [in_live_tac]);
      let R1 := fresh "CKR" in let R2 := fresh "CKS" in let R3 := fresh "CKH" in
      pose proof (af_live_range RT AF S mm p n A IN) as (_ & R1 & R2);
      pose proof (gp_live_hi RT GP S mm p n A IN) as R3;
      unfold STACK_WIN, SEGTOP_A in R1, R2;
      repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H in R1 end
  end.

(* [comment removed for export] *)
Ltac live_add_tac :=
  let e := fresh "e" in let He := fresh "He" in intros e He;
  repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H in * end;
  repeat first [ exact He | right ].

(* [comment removed for export] *)
Lemma client_static_lo : forall a, client_static a -> 0x10000 <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_LeptC_kit ()) [] "p'0h01Hh12Hxh24__p1h34__x1h43Hinh51hh61lh71Eh87__arithh94__ffh:8__varmaph;5__with<2hih=1eh>2_Hh?1ah@2loi001pi011xi021zp;1p;2p;3p;6p;4p;7p;8g01Ehj1aTg01LKj2;Tg00DYj1BTg003dj1@Tg004Bj21Tg01>lR0j2YTg01C:j3ATg00BYR1j2>Tg00C4R2j2KTg0000j19Tg00=Hj35Tg00cTR3j2=Tg006nj1XTg007Nj1WTg007nj2VTg008Lj1UTg008jj1TTg009Uj2DTg00:[j2STg00X4j6OTg00;>j1NTg00;`j2MTg00<Bj2PTg00<\j2QTg00=bj3LTg00>Aj4RTg00F`j2GTg01Qlj4`Tg005;j1FTg00P^j6_Tg00R[j4^Tg00SFj7]Tg00Sjj7\Tg00TNj8[Tg00OFj7ZTf0R4#9#9#9#9p=:g00Y6R5P5f1R6P4C`p=2f3R7f2R8'11G64'>p=0%94#9p=8%94#Fp=4%F4#Fp=7%F4#9p=6f4R9P5P7P8P6P4E_p=<A5564p=3P5P6g00YTP4C^p=EP6g00Z;R:g00ZZR;P;g00[:R<P4g00[ZF]p=CP8P:P;P;P<P6P4F\p=HP7P:P;P;P<P8P6P4G[p=I1186/>4p=JP5f5R=P9P7P8P6P4FZp=?%a4P1g01UFR>/;6g01VHR?/;6#Bg00^@R@#:#:#:#:#@RA/18P41;>7P2P51Y55RB1264;A>RCP6f6RDPDP4C0'>X<5,K5X@51;?=#B11AD[P4P6f8REPEP4C0,>CX<5,K5P2P51284=AB>P8f9R2P2P4C0'>X<51;?2#Bf:RC,1A[P41294=AB>P9f;RFPFP4C0'>P112=6=AB>P=f<R=P=P6C0f=R1,;?#Bf>RG,1A[P4f7RH/27=AB>PEf?R>P>P9C0f@R9,;?#BP3%9@#8#4#4#4#7#6#4#4#:#@R?%9@#8#6#7#8#7#8#7#4#6#8#@RI'2RJ12CDRK55B%7@#4#4#8#6#6#4#6#4#:#@RL%7@#4#6#8#6#6#4#6#4#:#@RM'2RN=5BK%7@#6#8#4#8#7#7#7#7#6#8#@RO,2MRP=5BKg00bBRK'='=fBRQ,1AP812FHRH95BJPBP0P5P5P5P4P4n2001100000120102102X=BRRPJ12=ERSP4D<13IEPBP0P5P5P5P4P6n2001100000120102102X=BR0PJ1212R2P6D<13?113?GP?P4fGRJPJP=C013I1fIRJ,1A[]1X65P?fFRTPTPFC013I=PIP?PJPJP4C0fJRU,1A]1X55P?fHRVPVPIC0p-0RWg00^eRX#XRY%WXRX1V56RZ%U5R[%T5R\1D5?1S5@R@'E,C\P\P:P;P;P<P7EOR75H\%N;R;1D5A/E@,C\R:CI1M\<R<P4P8g00_QR]g00`1R^'P1Q48=5]^dg00XX=L56CRR^b9b:b;X35W2AJ?4611A6R?[^35^2WP41GUIPUP6O3b8W1P1P4P6E?W0W1P>P4PDE?W0P4O1b0P4O1b0W7P4O1A5BNHA5BPH/=K'=P3A5BNSA5BPS/=KfD,1AP4A5BN2PBPRPN12GCRSP4D<13MCPBP0PN12>FRFP6D<13L>13L9PLP4PJPJPGC013M>fKRJ,1A[]1X65PLPVPVP1C013MGPMPLPJPJP4C0fLRG,1A]1X55PLPUPUPMC0PYPXPZP[P\1D5L/E@,C\=H\7P;P:CIP<P^b9b:b;X35X2WAJL46P?[^35^2WP41GGMPGP6O3b8W1P>P4P6E?W0W1fARLP4PEE?W0P4O1b0P4O1b0W7P4O1A5BP2/=KP3A5BPSPK11ATP4A5BPFPBPRPP129=P4D<13O=PBP0PP12L1P6D<13ML13MQPMP4PJPJP9C013OLfMRJ,1A[]1X65PMPUPUP>C013O9POPMPJPJP4C0fNRJ,1A]1X55PMPGPGPOC0PYPXPZP[P\1D5M/E@,C\=H\7P;P:CIP<P^b9b:b;X35X2WAJM46P?[^35^2WP41GJOPJP6O3b8W1PLP4P6E?W0W1fCP4PCE?W0P4O1b0P4O1b0W7P4O1PK11AVP4n010000000X4KP4O1n200100000021100010000W4P4O1n200100000021100011000W4P4O1n200100000021100011000W>W1W4P6P4O2n2001000000121000000W0X55P6P4O2n2001000000121101000W0X65P6P4O2n2001000000121101000W0P6P4O2n2001000000121000000W0X?5o"). Qed.

(* [comment removed for export] *)
Ltac subfp_tac := clear; let z := fresh "z" in let Hz := fresh "Hz" in intros z Hz; cbn [outside] in Hz |- *; tauto.

(* [comment removed for export] *)
Ltac out_range AG side :=
  eapply agree_sub; [exact AG|]; cbv beta;
  let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; cbn [outside]; side Hx.
Ltac static_out side :=
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
  let H1 := fresh "HSB" in let H2 := fresh "HSL" in
  pose proof (client_static_below a Ha) as H1; pose proof (client_static_lo a Ha) as H2; unfold SEGTOP_A in H1;
  let Hx := fresh "Hx" in
  assert (Hx : 65536 <= a < 7757824) by (clear - H1 H2; lia); clear H1 H2; cbn [outside]; side Hx.

(* [comment removed for export] *)
Ltac loop_transport m m' MU' side :=
  lazymatch type of MU' with munch ?W' m m' =>
    let AG := fresh "AGL" in
    pose proof (agree_of_munch W' m m' (outside W') MU' (fun x H => H)) as AG;
    repeat match goal with
    | H : LIBH m |- _ =>
        first [ match goal with GP : rt_gaps ?RT |- _ => apply (fun h => LIBH_agree RT GP _ m m' h AG ltac:(static_out side)) in H end
              | idtac "note: loop_transport drops LIBH"; clear H ]
    | H : io_ssp m |- _ =>
        first [ match goal with GP : rt_gaps ?RT, A : ART ?RT ?S m' |- _ =>
                  apply (fun h => io_ssp_agree RT GP _ S m m' h A AG ltac:(static_out side)) in H end
              | idtac "note: loop_transport drops io_ssp"; clear H ]
    | H : rw_cells asegs m ?A ?cs |- _ =>
        first [ apply (rw_cells_agree_nw asegs m m' A cs) in H; [ | solve [out_range AG side] ]
              | idtac "note: loop_transport drops" H; clear H ]
    | H : ro_cells asegs m ?A ?cs |- _ =>
        first [ apply (ro_cells_agree asegs m m' A cs) in H; [ | solve [out_range AG side] ] | clear H ]
    | H : bytes_at asegs m ?A ?bs |- _ =>
        first [ apply (bytes_at_agree asegs m m' A bs) in H; [ | solve [out_range AG side] ]
              | idtac "note: loop_transport drops" H; clear H ]
    | H : wr_at asegs m ?A ?n |- _ =>
        first [ apply (wr_at_agree_nw asegs m m' A n) in H; [ | solve [out_range AG side] ] | clear H ]
    | H : stk asegs m ?lo ?hi |- _ =>
        first [ apply (stk_agree_nw asegs m m' lo hi) in H; [ | solve [out_range AG side] ]
              | idtac "note: loop_transport drops" H; clear H ]
    | H : wmono asegs ?m0 m |- _ =>
        match goal with WMx : wmono asegs m m' |- _ => apply (fun h => wmono_trans asegs m0 m m' h WMx) in H end
    | H : munch ?W ?m0 m |- _ =>
        first [ apply (fun h => munch_trans W m0 m m' h
                         (munch_weaken W' W m m' ltac:(subfp_tac) MU')) in H
              | idtac "note: loop_transport drops (footprint of the loop not inside)" H; clear H ]
    | H : accok _ _ m _ _ |- _ => idtac "note: loop_transport drops accok fact" H; clear H
    | H : acc asegs m _ _ |- _ => clear H
    | H : shk m _ _ |- _ => clear H
    | H : mem_inv asegs m |- _ => clear H
    end;
    clear AG
  end.

(* [comment removed for export] *)
Ltac loop_art RT AF S m' spz MU' ivt :=
  lazymatch type of MU' with munch ?W' ?mm m' =>
    lazymatch goal with
    | A : ART RT S ?m0, MUx : munch ?W ?m0 mm, WMx : wmono asegs ?m0 mm, WMl : wmono asegs mm m' |- _ =>
        let N := fresh "ARTl" in
        assert (N : ART RT S m')
          by (apply (art_client_writes RT AF S m0 m' spz W A
                       (munch_trans W m0 mm m' MUx (munch_weaken W' W mm m' ltac:(subfp_tac) MU'))
                       (wmono_trans asegs m0 mm m' WMx WMl));
              [ repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul | ivt ])
    end
  end.

(* [comment removed for export] *)
Ltac fframe_open RT AF PF live0 usp k SZ getacl :=
  lazymatch goal with H : rt_frames RT ?S = (?f, k) :: ?frs0 |- _ =>
    let FRS := fresh "FRS" in rename H into FRS;
    let fr := fresh "fr" in set (fr := f) in *;
    change (fs_size k) with SZ in *;
    let sz8 := eval vm_compute in (SZ - 8)%Z in let szs := eval vm_compute in (SZ / 8)%Z in
    change (SZ - 8)%Z with sz8 in *; change (SZ / 8)%Z with szs in *;
    let FRM := fresh "FRM" in let FSH := fresh "FSH" in
    lazymatch goal with Hw : wr_at asegs ?mm fr sz8 |- _ =>
      let jf := fresh "jf" in destruct (wr_at_rw_CB mm fr sz8 Hw ltac:(lia)) as (jf & FRM); clear Hw end;
    lazymatch goal with Hw : wr_at asegs ?mm (shad fr) szs |- _ =>
      let js := fresh "js" in destruct (wr_at_rw_CB mm (shad fr) szs Hw ltac:(lia)) as (js & FSH); clear Hw end;
    let n8 := eval vm_compute in (Z.to_nat sz8) in let ns := eval vm_compute in (Z.to_nat szs) in
    change (Z.to_nat sz8) with n8 in FRM; change (Z.to_nat szs) with ns in FSH;
    lazymatch goal with A : ART RT S ?mm |- cps _ (ASTA RT S _ _) _ =>
      let FR0 := fresh "FR0" in let FRHI := fresh "FRHI" in let FR64 := fresh "FR64" in let FRSEG := fresh "FRSEG" in let FRSH := fresh "FRSH" in
      pose proof (af_frames_range RT AF S mm fr k A ltac:(rewrite FRS; left; reflexivity)) as (FR0 & FRHI & _ & _);
      pose proof (af_frames_align RT AF S mm fr k A ltac:(rewrite FRS; left; reflexivity)) as (FR64 & FRSEG);
      pose proof (af_frames_hi RT AF S mm fr k A ltac:(rewrite FRS; left; reflexivity)) as FRSH;
      change (fs_size k) with SZ in FRHI, FRSH;
      repeat match goal with E : rt_sp0 RT _ = _ |- _ => rewrite E in FRHI end;
      unfold STACK_WIN, SEGTOP_A in FRHI, FRSEG;
      let NFA := fresh "NFA" in
      assert (NFA : forall a, PF a -> (a < fr \/ fr + SZ <= a) /\ (a < shad fr \/ shad (fr + SZ) <= a))
        by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
            apply (new_frame_apart RT AF S mm fr k frs0 live0 usp a A FRS);
            [ let e := fresh "e" in let He := fresh "He" in intros e He;
              repeat match goal with E : rt_live _ _ = _ |- _ => rewrite E end; exact He
            | repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; lia
            | repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia
            | getacl Ha ])
    end
  end.

(* [comment removed for export] *)
Ltac fframe_chunk RT AF fr k SZ p n :=
  match goal with
  | A : ART RT ?S ?mm, FRS : rt_frames RT ?S = (fr, k) :: _ |- _ =>
      let IN := fresh "IN" in
      assert (IN : In (p, n) (rt_live RT S)) by (solve [in_live_tac]);
      let D1 := fresh "FCD" in let D2 := fresh "FCS" in
      pose proof (af_frames_range RT AF S mm fr k A ltac:(rewrite FRS; left; reflexivity)) as (_ & _ & _ & D1);
      specialize (D1 p n IN);
      pose proof (af_fshadow_apart RT AF S mm fr k A ltac:(rewrite FRS; left; reflexivity)) as (D2 & _);
      specialize (D2 p n IN);
      change (fs_size k) with SZ in D1, D2; unfold shad, SHB in D2; clear IN
  end.
(* [comment removed for export] *)
Ltac fframe_optr RT AF fr k SZ OWN usp :=
  lazymatch type of OWN with accok ?lv ?frs ?m0 ?a ?n =>
    match goal with
    | A : ART RT ?S ?mm, FRS : rt_frames RT ?S = (fr, k) :: ?frs0 |- _ =>
        let D1 := fresh "FOD" in let D2 := fresh "FOE" in
        assert (D1 : forall x, a <= x < a + n -> (x < fr \/ fr + SZ <= x) /\ (x < shad fr \/ shad (fr + SZ) <= x))
          by (let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
              apply (new_frame_apart RT AF S mm fr k frs0 lv usp x A FRS);
              [ let e := fresh "e" in let He := fresh "He" in intros e He;
                repeat match goal with E : rt_live _ _ = _ |- _ => rewrite E end; exact He
              | repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; lia
              | repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia
              | exact (accok_aclient lv frs m0 usp a n x OWN Hx) ]);
        pose proof (D1 a ltac:(lia)) as D2; specialize (D1 (a + n - 1) ltac:(lia));
        unfold shad, SHB in D1, D2
    end
  end.

(* [comment removed for export] *)
Module LC1.
  Import Ltac2.
  Ltac2 rec subset (xs : ident list) (ys : ident list) : bool :=
    match xs with
    | [] => true
    | x :: xs' => if List.exist (Ident.equal x) ys then subset xs' ys else false
    end.
  Ltac2 prune_sub () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then (if SF2.clean bad ty then true else subset (SF2.vars_of [] ty) gv)
                              else subset (SF2.vars_of [] ty) gv).
  Ltac2 prune_sub1 () : unit := Control.enter prune_sub.
End LC1.
Ltac zify_prune_sub := ltac2:(LC1.prune_sub1 ()).
Ltac tlia ::= sf_clear_big;
              first [ Zify.zify; xlia zchecker
                    | sf_unhide;
                      first [ zify_prune_sub; Zify.zify; xlia zchecker
                            | zify_prune_neg; Zify.zify; xlia zchecker
                            | zify_prune_plain; Zify.zify; xlia zchecker
                            | Zify.zify; xlia zchecker ] ].

(* [comment removed for export] *)
Definition parked (P : Prop) : Prop := P.
Ltac park H := lazymatch type of H with ?T => change T with (parked T) in H end.
Ltac unpark H := unfold parked in H.
Ltac clear_acc := repeat match goal with H : acc asegs _ _ _ |- _ => clear H end.
(* [comment removed for export] *)
Ltac unpark_accok OWN AGF :=
  unpark OWN;
  lazymatch type of OWN with accok ?lv ?frs ?m0 ?a ?n =>
    lazymatch type of AGF with agree_on _ m0 ?m1 =>
      apply (fun h => accok_keep_sub lv frs m0 m1 _ _ _ a n h AGF ltac:(lia) ltac:(auto)) in OWN
    end end.
(* [comment removed for export] *)
Ltac unpark_accok_munch OWN MU live frames usp side :=
  unpark OWN;
  lazymatch type of OWN with accok ?lv ?frs ?m0 ?a ?n =>
    lazymatch type of MU with munch ?W m0 ?m1 =>
      apply (fun h => accok_keep_sub lv frs m0 m1 live frames usp a n h
                        (agree_of_munch W m0 m1 (aclient live frames usp) MU
                           ltac:(let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; side Hx))
                        ltac:(lia) ltac:(auto)) in OWN
    end end.

(* [comment removed for export] *)
Ltac park_disj :=
  repeat match goal with
  | H : (?A /\ ?B) |- _ => lazymatch A with (_ \/ _) => destruct H | _ => lazymatch B with (_ \/ _) => destruct H end end
  end;
  repeat match goal with
  | H : ?T |- _ => lazymatch T with (?A \/ ?B) => lazymatch type of A with Prop => lazymatch A with
        | context [Z.le] => change T with (parked T) in H | context [Z.lt] => change T with (parked T) in H end end end
  end.
Ltac unpark_all := repeat match goal with H : parked _ |- _ => unfold parked in H end.
(* [comment removed for export] *)
Ltac tlia ::= sf_clear_big;
              first [ Zify.zify; xlia zchecker
                    | sf_unhide;
                      first [ unpark_all; zify_prune_sub; Zify.zify; xlia zchecker
                            | zify_prune_neg; Zify.zify; xlia zchecker
                            | zify_prune_plain; Zify.zify; xlia zchecker
                            | Zify.zify; xlia zchecker ] ].

(* [comment removed for export] *)
Ltac cwalk1 :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [ shbr | shbr0 | br | progress sx32_fix; br ]
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => first [ shload; lstep; clear_shl | special_step | frame_step | lstep; try sb_fix; try fix_land32; shnorm ]
  end.
Ltac cwalk stops := repeat (tryif at_stop stops then fail else cwalk1).

(* [comment removed for export] *)
Lemma accok_keep_P : forall lv frs (m m' : mem) (P : Z -> Prop) a n, accok lv frs m a n -> agree_on P m m' -> 0 <= n ->
  (forall x, shad a <= x < shad a + (n + 7) / 8 -> P x) -> accok lv frs m' a n.
Proof.
ltac2:(KReplay.run1 (kr_t_LeptC_kit ()) [] "p'0h01xi001xh11Hh21kh31fh42AGh52HPh62Hah72Hnh82Hxh97__sat11h:4__x1h;2H0h<2H1h=2H2h>2H3h?2H8h@2HThA2HbhB3HinhC1PhD7__arithhE4__ffhF7__sat10hG6__sat9hH8__varmaphI5__withJ1ahK4cstrhL3frshM2lvhN1mhO2m'hP1nhQ1zp;2p;1p;5p;3p;4p;7p;8p;6g01>lj2]Tg007Nj1PTg0000j1ATg000Uj1WTg0013j1^Tg001Vj1tTg01WFj59Tg01X@j3HTg01Y=j4FTg01Z;j36Tg00@Mj14Tg005;j1CTg003dj1KTg01CQj3wTg01C:j3;Tg004Bj22Tg004^j20Tg01Ngj1=Tg016Bj2cTg00C4R0j2NTg01[5j1DTg00BYR1j23Tg00dfj2RTg00eFj1TTg00fdj1zTg017lj2yTg00F`j2ITg018Tj3xTg01[nj3vTg00E2j2JTg00HHj2uTg00<Bj2ZTg006nj1sTg007nj2rTg008Lj1qTg008jj1pTg009Uj2oTg00:[j2lTg00R[j4kTg00SFj7iTg00;>j1gTg00TNj8fTg00;`j2hTg00<\j2eTg00=Hj3GTg00=bj3jTg00>Aj4dTg01\_j2mTg00OFj6nTg01]bj6bTg01^]j7aTg014oj4BTg00hBj4YTg01Jij3`Tg006Qj2[Tg01Qlj4_Tg01JLj2\Tg00cnj4OTg00XXR2f0R3'2p=1f6R4f5R5'2f4R6f3R7f2R8f1R9'0/[3'0'I'3p=7g00Y6R:g00lmR;P9P3C_p=@1089/\3p=:g00\aR<P8P9%D3COp=>12261078/29/33'3p=512671J89=G:2/33'3p=81393,38p=?1089/23p=EP<P8%49%D3COp=<1289/33p=X1\93,28p=V1J89=G:2/33p=U1J93=G:2p=M1078/29/33p=SP<P8P9P3COp=L12671093,I8'3p=Q1089/[3p={1]::#P1]:;R=#Pg00^@R>#AR?#A#AR@#A#A#A#W#^%W@#^RA#t[RBp-0\:P4P5P6P9P3D9g00cTf7RC?H89P4P5P8P9CFA6645%17%44RDP3P3PDP5%C>#C#KRE%K@R@F7f8RFP9O1[^0:f;RGf:RHPFP4P5D9[[[P3AHF78A65C4%16%4CRIP3P3PIP4PEP@F7f9RIP9O1[^0:f<RJ?HC4PGPIPCP4CF;w7W5W7W4W1P3O1PCP4P7P8CFP0P:1@93RK=;=H12941045RL%=3RM=:9@RNP4P@P4PLP@%K?RL%C?#C#C#C#KR?'cROA>ID5D5D83?X2;,N;X3:A64FC%15%4FR4P3P3P4PCPEP@F7PHP9O1[^0:f=RDPJPHPFPCD9[[[P3A;=KJ129F10FCRPPNPFP@PFPPP@POA>G4CD5D83?X2;,N;P0P;1@83=;=D128I10IFR0A:8M@PIP@%1IR4AE0@OA<JIF3?D83?X2;A6HJG%4JR0P3P3P0PGPEP@F7f>RPP9O1[^0:fARQf@RRPPPJPGD9[\4[P31@63f?R45;=126G10GHRSA:6M@PGP@PGPSP@POA<PGHD5D83?P11@59=;=R10JGRH%=9=:5@PJP@PJPHP@POA>40GD5D89X5JA6PR4%1D%4RR0P3P3P0P4PEP@F7fBRHP9O1[^0:fERSfDRTPHPRP4D9[[[P31@C7=;=H104PRC%=6=:F@P4P@P4PCP@POA<H4PD5D89XF4P112IR10R4RP%=5=:I@PRP@PRPPP@POfCRP?>04D5D8A6HTP%1Q%4TRQP3P3PQPPPEP@F7fFR0P9O1[^0:fIR5fHRCP0PTPPD9[[[P312GH10PHRU%=F=:J@PPP@PPPUP@POA<0PHD5D8P110TPRH%=I,0D;V@PTPHP@POfGRH?>QPD59UT@A60CH%1S%4CRQP3P3PQPHPEP@F7fJRPP9O1[^0:fMRUfLRVPPPCPHD9[[[P3%=G=:4@9E0SPH10H0P@POA<PH0D59UH@P11MC@PC10CHP@POfKR0?>QHD5A6PV0%15%4VR5P3P3P5P0PEP@F7fNRQP9O1[^0:fQRHfPRSPQPVP0D9[[[P31MP@P0100PP@POA<Q0PD5P1%1V10V0P@POfORP?>50CSA6QSP%1U%4SRUP3P3PUPPPEP@F7fRR5P9O1[^0:fUR0fTR4P5PSPPD9[[[P3%1Q10PQP@POA<5PQCSP110SP?E@OfSR1?>UPA6541%1H%44RUP3P3PUP1PEP@F7fVRUP9O1[^0:fYRPfXRQPUP4P1D9[[[P3105H?E@OA<U15fWR1=60U%14%41R4P3P3P4PUPEP@F7PPP9O1[^0:f\R0?H1Uf[R5PPP1PUCFP:f]RG9;=K129P10PQRKPNPPP@PPPKP@PO%4PRK%DQRN5L5D5D83?X2;,N;X3:PSP;1@H3=;=012HQ10Q1RWA:HM@PQP@PQPWP@POfZRW%4QRH%D1RM3LD5D83?X2;PV1@SV=;=512S1R5101UR=%=V,0S;V@RS1M1@RV%11R1AE=@OR=%DURU9LP4RX'3RY'3RZ'3R['3R\'3PCP5P\PTPSP[PRPVPZPJP1PYPFP=PXP6P<PWPPP4PUP7PQPHP3P3PH1RAM#TDQRMX0:PWPPP8P8P9P:1RANRN#TRA%4WRPP8P8PPP3DQXQ:P3A{QE@RE%zN%1A1yL?1I2LRA%1?1I2O[RN[%1LRPg01=XRHAxL?9UW6%1O\H^6PAv0@D%1@1JG@#1[P8g00a01u2L'ZPAeO1PNg00^eRN#s%PN1r:9%q:%p:RNg00Z;RAg00ZZRLPLg00[:RGPNPAPLPLPGP:1o:2g00YT1l:>Ckg00[ZFiR>%gLP>Gf1hNGP3P8g00_QRGg00`1RN'Z1e38=GGNdAj:29CdbEbHbIX::%13%19[^::P3f^PIO2bDb9bGbFb9bK,mQEnPKP9P9PKPEDQP3b8O2X8MX0:PWP9O1\M^0:eEbFaCBCBCBCBCBCBCYCY3`W5W7W4WAW@P9P3O2n2001000000121000000W1W;P9P3O2n2001000000121000000W1W?P9P3O2n2001000000121000000W1W=P9P3O2n2001000000121000000W1W<P9P3O2n2001000000121000000W1WBP9P3O2n2001000000121000000W1X2;P9P3O2n2001000000121100000W1X3:P9P3O2n2001000000121100000W1P3O1n200100000021000011000W>XP:XJ:WCXOBWNWLWMo"). Qed.

(* [comment removed for export] *)
Section KitC2.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Lemma live_apart : forall Σ (m : mem) p1 n1 p2 n2, ART RT Σ m -> In (p1, n1) (rt_live RT Σ) -> In (p2, n2) (rt_live RT Σ) -> p1 <> p2 ->
  p1 + n1 <= p2 \/ p2 + n2 <= p1.
Proof using AF.
ltac2:(KReplay.run1 (kr_t_LeptC_kit ()) ["KitC2"] "p'0h02H2h12l2h21Hh31eh42l1h51Eh62E1h72H1h82HAh92NEh:2_Hh;1lh<1mh=2n1h>2n2h?2p1h@2p2hA2Σi001pi011xi021zp;1p;3p;2p;4p;6p;5p;=g01>4j1LTg0000j17Tg000Uj1=Tg0013j1;Tg001Vj1KTg01?Lj3ITg01>lR0j2FTg01@Dj24Tg01C:j31Tg00=Hj32Tg00DYj1?Tg01_]j4>Tg007Nj1JTg00Mdj33Tg01MIj35Tg00C4R1j2:Tg004^j28Tg004Bj29Tg00cTR2j26Tg00OFj6ETg01`:j5DTg01CQj3CTg00P^j6<Tg00Q;j2BTg01Jij3ATg01`Xj5GTg01Mfl=HTg01Qlj4@Tg00Y6R3P3f1R4f0R5C@p=0p,2RTR6#Lg00^@#7#7#7R7#7#7#7#=#;%=7#;#K[f5R7f4R85I61F33R9f3R:,08f6R;,4631f2R<,0:f7R=,46519A23;8#?P910=;f9R>,46P<C>%J9R?f;R@,46f8RA,0>=395959452?X1?,:?X4?':P1P?f<RB,46f:RC/0>=395959452?X1?,:?X4?18>A/9=18=;/9>'6P5f>RD,4610B@=395959452?X1?,:?P1P?f?R1,46f=RE/0B=395959<52?X1?18EB/9@18@C/9E'6P5fARF,46101DRG=395959852?P6p,2AFfBRHPFf@RIP1PDPEP7P4PBP5P?146HA19G5X;?PC10I1R1=3949597R6P5EE10DE=196P9P;10FIRI=39<R<PGP5DDA19G;A19G<'6P9P=P:P1P2A191=10HFRF=39:9191A19IARAA19I8'6P5A19F>A19F7R7;C5X0AP5O1fCRA/0HRH=398919IP2fDR2/0ARI=29FP7A19HCA19H;R;'6P5fERC/02R2=29HA19I@R@A19I=R='6P9P3P0P3P3P3P5P5n2001100000120102102X39fFRH/0CPIP5E<A23CAP9P3P0P3P3P3P5P4n2001100000120102102X39fGR9/0HP2P4E<A239CfH=23HRHPAP4O1X:HW6P5O1b2P5O1b2'BW0P5O1AA@=5X0;P5O1n200100000021000010000W2P5O1n200100000021000010000DGb0b0M=HW5X1?P4P5O2n2001000000121101000W2X4?P4P5O2n2001000000121101000b3W9W0W7W8X>3X@3X=3X?3W<WAo"). Qed.
End KitC2.
