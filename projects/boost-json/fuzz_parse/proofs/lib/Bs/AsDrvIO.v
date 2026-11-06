(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SReach RegsEquivM MainEqv HeapCeil Frame Spec
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame SymAux RefPrintfLib LibTail RefMemcpyLib
  LazyRestrict LazySR LazyFdNodes LazySym.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Mem Cells Step Frame MState SysStep Exec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsDriverLaws AsLazyRun
  RefExitBase RefStdioDefs AsStdioWrite AsStdioCall AsScLib AsPrintfFirst AsPrintfBuf AsHdrErr AsDrvRun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AsDrvIO () := KReplay.lz_vm "##YRC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC89OSSVerify6Proofs:boost_json:fuzz_parse3lib3Lib2Nd9ex_elimF2C13~~~!sjP2Bs7AsIface5as_St!sj%K47Corelib7Numbers7BinNums8positive02!sKG1!sK=1N02I45stdpp9bitvector;definitions2bv00I!sg+4Init9Datatypes6op!sL#00!ug[6as_VIS!vT&7!skN8PropExec4mks!vQ+!xU9?!s<23Run6config01!u1[8as_AKREL!tJ%I!u3O6CatSim6msteps00!uvV<LazyRestrictEsame_but_materialized!tgV8ShapeAlg8re!sk$!tk+!xr<4prod!y:>4list00!v>Q!uS#SR4lzok!v<e8r!s/&!y}_7seg_rom!~?Y8AsDrvRun7!wp$vm!vs85Logic3and00C!vNV8hid_!t/#!tsb:!ts&_sb!spY9As!wG$unCrz_!{L%_lazy_!}c,!tl\8drv!ss$!vb>2eq!zQ#!~mI>!#8T#!sE+=machine_state00!#6bF3!t:K5S!s{#5Model!xSR!}R+4TSe!vcZ5ASegs5asegs!{tV4Scfg=hunspell_scfg!wK&!tVR=AsPrintfFirst4ap1H!~F'!#:L=Z02C!#:L?7Z_to_bvC!wTQm_fds!sZQ9fd_lookupK!s^P7FdEntry!#=+-!#<C9!sH=!#6Q$1!w;a7ap1Post!w>,!vRPevent!#?g-!tr82!{HY6t_emi!{JZ!u]1>ap!s3$0_f!s5#!#3:2!yz60I!x@Y!s^R!v`&!~b0!uN96images9AsanUbsan1M?loaded_segments!|I3!wS23nat02!#6$2Peano2le00C56Stdlib6ZArith6BinInt1Z6of_nat!sF<3mul!sC=add!zbS;!x''Buf4apb!~u+!~WA4BvWfK!#FHC1!#E9Ygetr!#6,U<RefMemcpyLib8keeps_cs!uFG;bv_unsigned!v~=sub!t^P5Frame9f!s+#_mod!uIV!v2+3rdn!u@'!#<UW@word_to_le_bytesc!#HWTDrvIO:drv!#?J%!#37U!#O$%:and!#O%$6!#3|X!zw/A!#3z'buffer!#HY&K!#Gj@1I!}v@0!~=A1!u$_4ABUF!ts8!#B-$4Tru!#PX@Z!#:-T8AsHdrErr3hf!~F+!sk\6hf!#:m-!#@fQpec1W!xhY!tP+Cas_hdr_short_fwrite!t[[9msg!so%!tcbE!tc&overrun!teb;!te#!sq&!sj%".
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsIface~~~~~~03asr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BscAsDriverLaws~~~~~~k2h0asan_driver_laws" s.   (* [comment removed for export] *)
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Section IO.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {HCEIL : HeapCeil}.
  Variable H : ltac2:(zQ "10!jd$0").
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis DL : ltac2:(zQ "10!o4@1$0?1H").

  Let rom := seg_rom asegs.

  (* [comment removed for export] *)
  Theorem drv_msteps : forall s msF regs pc mem regs' pc' mem' mo T,
    as_VIS H s msF = mkst regs pc mem rom -> as_AKREL H s (mkCfg msF mo) ->
    CatSim.msteps asegs (mkst regs pc mem rom) (mkst regs' pc' mem' rom) ->
    (forall msF' mo', as_VIS H s msF' = mkst regs' pc' mem' rom -> as_AKREL H s (mkCfg msF' mo') ->
       same_but_materialized mo mo' -> realizes asegs (mkCfg msF' mo') T) ->
    realizes asegs (mkCfg msF mo) T.
Proof.
ltac2:(KReplay.run1 (kr_t_AsDrvIO ()) ["IO"] "h03mo'h14msF'h24BACKh32HAh43HA'h52HKh63HS'h72HVh83HV'h93Hmsh:1Lh;2OKh<3OK'h=2RSh>3RS'h?1Sh@3SB'hA1ThB2ZrhC1ahD3memhE4mem'hF2mohG3ms'hH3msFhI2pchJ3pc'hK4regshL5regs'hM1sp;1p;2p;3p;5p;4p;Cp;=g0000R0p4p7210p1000\p4p710p8g001`j1JTg002dj15Tg003Ij1@Tg003nj16Tg004Lj19TP0j2HTg004oj1CTg005Qj33Tg006Vj52Tg007Wj21Tg008Lj34Tg009Sj3=Tg00:Vj2<Tg00;lj4;Tg00=3j2ITg00=Sj1GTg00>3j58Tg00?4j37Tg00@=j1BTg00AAj2ATg00BHR0j2:Tg00Bcj4?Tg00Cfj3DTg00E0lCETg00FDl=>Tg00GLj3FTg00GfR1f1R2f0R33Fp=0p,1HR4#Jg00Hm#5R5#@#6%55#5R5#5#5#5#6#9R6'HR7%65#9#C\6R5g00IRR8g00JHf9R9f8R:534p,2fxR;f7R<f6R=f5R>p,3romR?D2'0f:R@f2RA,19544g00KIRBP;P9P:P<P?D2RCP;P=P>f4RDP?D23=f>RE=342/0Cf?RC11A2RF5441<:APBg00LKRGf3RH,1DP:C;[[[^08^11P;P4p,2DLf=RIf<RJP>f;RKP@P9PDPHPA1I66#GRLPBPAP2P311C:D8f@RM97HAP;PCPEPI%BBD2'0PBP<P=P>PFD81AEAA79:D/0AfHRF=34>/0H11>DRN944F':[[[^G1^08^11P;PBP>PDPHfBRFfAROPMPCP?PEPIPJPKP@PAP2P<PBP<P=P>1123D81<E2P9P:fFREPHC?A7@9DP;fCRKPFPOP?D2'0P=P>PDP;fDRJPKPFP?D2RIPHADODAP3O6fIRD=34>/0IA44DN':P0fJR0=34=P;fERDPJPKP?D2'011=>9440PBPG11<=PFC;P3fL=34:P;fGPEPDP?D2'0fM119:544POP@P9P2P3P<O5W4W8P2P3O2n2001000000120000000bCW>W6W@W<X08X11MCEW2W=W;XBLX?LW:M=>W5W9W3W7WAWFXE5XJ6XL7WDXI6WKXH1WMo"). Qed.

  (* [comment removed for export] *)
  Theorem drv_printf_first : forall s msF mo regs mem (sp : word) (can : Z) (K : TSet),
    ap1H regs mem sp can ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 0x0bed14) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    K [] ->
    (forall regs' mem' msF' mo', ap1Post regs mem sp can regs' mem' ->
       as_VIS H s msF' = mkst regs' (Z_to_bv 64 0x0bec68) mem' rom -> as_AKREL H s (mkCfg msF' mo') ->
       same_but_materialized mo mo' ->
       realizes asegs (mkCfg msF' mo') K) ->
    realizes asegs (mkCfg msF mo) (t_emit [WriteEv (Z_to_bv 64 1) (Z_to_bv 8 48); WriteEv (Z_to_bv 64 1) (Z_to_bv 8 10)] K).
Proof.
ltac2:(KReplay.run1 (kr_t_AsDrvIO ()) ["IO"] "h03mo'h14msF'h24mem'h35regs'h44BACKh52HAh63HA'h72HKh85HKnilh93HS'h:2HVh;3HV'h<4Hfd1h=1Kh>1Lh?2OKh@3OK'hA2PHhB2POhC2RShD3RS'hE1ShF3SB'hG2ZrhH1ahI3canhJ3memhK2mohL3ms'hM3msFhN4regshO1shP2spp;1p;2p;4p;3p;5p;6p;Ap;=g001`j1WTg002dj17Tg003Ij11Tg003nj1=Tg004Lj1GTg0000j2RTg004oj1CTg00MQj4NTg005Qj36Tg00N\j19Tg00O:j2:Tg006Vj54Tg007Wj22Tg008Lj38Tg00O`j1VTg00PTj2UTg00QLj1QTg00RDj2PTg00GLj3ETg00Rfj1OTg00SFj6BTg00:Vj2DTg00;lj4ATg00TTj2>Tg00UJj3?Tg00Ujj2MTg00=3j2LTg00=Sj1KTg00>3j5<Tg00?4j3;Tg00@=j1@Tg00AAj2JTg00BHR0j2FTg00Bcj4ITg00Cfj3HTg00VmlASTg00FDl=TTf0R1#7#7p=3%11#7p=5g00GfR2f1R3;E1p=0p,1HR4#Wg00IRR5g00HmR6#7R7#1R8#=%37R7#7#3#=R9#GR:'RR;%=7R7#G#C\:R<g00X@g00JHf4R=f3R>f2R?P3CNf8R@f7RA564p,2fxRBf5RC%18#1#1#5#1#5RD#5#3#5#1#3#9,:9REP=p,3romRFD4'0f9RG12@ARH584g00X^RI#C%V@%96,:9RJ'U%QJ,PI3EP=g00YVRI#ORKO1f=RLf<RMf;RNf:ROP>P?EBfARP=64?PBP=%3D#1#5#5#3#9,:9R9P>PFD4'0fBRF12>?5841DP>g00KIRDg00LKRQ12C=RRPLCA[[[[^05^12^2<^3;PBP4p,2DLPLPMPNPOPEPG%16#3#3#9,:7,>J%78#9,:7,>J=?IK5?If6RI'MP=P>1L::#KRKPDP?P3P1f?RJf>R7'2D<f@R89;>?PBP7PEPL%@DD4'0PDPAPIPC12?3RDD<fDRE/J?A;G@=/0?fHR6=64C/0>A846R'F[[[^L2^05^12PBPCP=P>P8PJPFPPP7PLPMPNP?P3P@PAPEfCPFPPP>P?EBg00ZLRPPOPGP@PDD<fGRD/D?PMPNfIP=CIA;LMCPBPAP9PI%@PR=D4'0PGPIPCPBP@P9PAP=D4RFP>fJ?HC?P1O6fLR?=64I/0F12IC984?'FP0fMR0=64APBPGP9P@P=D4'012AI9840PPPQPHPDCAP1fO=64GPBPNP9POP=D4'0fP12OG584PEPLPMPNPOPGP3P1PAO8W6W;P3P1O2n2001000000120000000bHWDW9WFW@WBX05X12X2<X3;MASW4WCW?XGKXEKW>M=TW7W8W<W5W:WAW=WIXP:WJWNWKXM2WOo"). Qed.

  (* [comment removed for export] *)
  Theorem drv_printf_buf : forall (j : nat) s msF mo regs mem (sp : word) (can : Z) (K : TSet),
    (j <= 2)%nat ->
    apbH mem sp (ABUF + 2 * Z.of_nat j) can ->
    getr regs 1 = Z_to_bv 64 0x0bec68 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 0x0bed14) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    (forall regs' mem' msF' mo',
       keeps_cs regs regs' ->
       frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 3400), 3400); (Z_to_bv 64 0x1b6e10, 4);
                           (Z_to_bv 64 0x1b6e38, 8); (Z_to_bv 64 (ABUF + 2 * Z.of_nat j), 2)] ->
       rdn asegs mem' (Z_to_bv 64 (ABUF + 2 * Z.of_nat j)) 2 = Some [Z_to_bv 8 0x30; Z_to_bv 8 0x0a] ->
       rdn asegs mem' (Z_to_bv 64 0x1b6e38) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (ABUF + 2 * Z.of_nat j + 2))) ->
       rdn asegs mem' (Z_to_bv 64 0x1b6e10) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5)) ->
       as_VIS H s msF' = mkst regs' (Z_to_bv 64 0x0bec68) mem' rom -> as_AKREL H s (mkCfg msF' mo') ->
       same_but_materialized mo mo' ->
       realizes asegs (mkCfg msF' mo') K) ->
    realizes asegs (mkCfg msF mo) K.
Proof.
ltac2:(KReplay.run1z (kr_t_AsDrvIO ()) ["IO"] "##;:h04mem'h15regs'h23mo'h34msF'h42FMh52HAh63HA'h72HKh82HVh93HV'h:2Hjh;1Kh<3KCSh=2PHh>2R1h?3R11h@2R2hA3RD1hB3RD2hC3RD3hD3RUNhE3SB'hF3canhG1jhH3memhI2mohJ3msFhK4regshL1shM2spp;1p;2p;4p;3p;5p;>p;8p;<p;6g001`j1aTg002dj13Tg003Ij16!s/$nj1DTg004Lj1TTg0000j2X!s8$oj1STg00[Wj17Tg00\6j2WTg00N\j12!s8$Pj1ATg00]0j2?!s/$Mj2:!s/$jj4_Tg00_3j2L!s/$Vj3MTg00`9j2KTg00O:j20Tg00GLj31Tg005Qj3HTg006Vj5>Tg007Wj2<Tg008Lj3FTg00a:j2ITg00=3j2VTg00bCj2R!s/$mj2QTg00Rfj1PTg00UJj35Tg00cJj3G!s\$Sj1UTg00dMj4B!sS$Dj2CTg00eMj2ETg00:Vj2OTg009Sj3`Tg00BHj2@Tg00fUl>^Tg00g^j8]Tg00hcl<Z!vY$\j6[Tg00j7j4\Tg00;lj4YTf0R0#3#3p=4%60#6p=J%3!s-$9%60#3p=8f2R1g00X@R2f1R3P0C\p=;g00KIR4g00LKP3P0CYp=Ng00ZLR5P1!s8$Bp==g00jWp,1HR6#ag00GfR7g00IRR8g00HmR9#3R:#6R;#DR<%3:R=#3R>#3#4#DR?#TR@'XRA%D>RB#TRC#S\@RDg00JHf8REg00k6#7#7RF'Wf4RGf3RHg00kURI%2:R:f9RJ#A'?':P1C_f6RK%29RLg00l\RM1L<Ld5M<'K%6;RL#6#J#9#8RN#3#9#8#8#4#2,0?RO51@f7RPPM1L<:d9M<:'Kf5RQ51@%2LRLP!sr+,KEg00m8,0?51@f<R<f;RL5H6p,2fxRMPJ%6N#4#9#9!t+'NPEp,3romRRD>517f=RS1<<L5F6f?RT/IH1V@2RUf>RV,R?%89R9#6RW!sh$!tr$RX'Q,0?=;@X%6W!u2$J#8#4!sJ&!t6&Y%2=5;@R=%JW!uR,W%2>5;@R>fDRZ#A,?:,:I!ss%:%PUR[55U!s%%35R\9GTH%UCR]#SR^P4PGfER_!s\-R`PFCB%3!uS&B%3;!s-%PC55C55C,C]RC31P4PQPW%7F#7RB#7!s$%R9CBfFRa!sv'/::,0?,E9,C]Rb51^P4PKPYPBCB%2;!sA$B,C]R;51^fGR4=H6KPMPEPOPPP!vj&H1<PK5F61O4P1<JEfCRc'N[!s#&^28^37^0D^1APAPDPMPVPNPSPRD>PMP3POP0!sp$`5R51IV3Rd1R?</QX!w5&fB!t{'R!uu$X=;@:=5U[95U>95U=55U9GS0RUA=0XF=1^CRXA=0W91:I!uT,51^R]A=0YB=1^;R?'@!s$'X0DX1A1<VS/NEP5PdPUPXP]P?f@R?/<Tf:R]'N1IT1AGT1\A=H`!t4$A=GW9=1^bA=Q!s|%P4PaPZPNPcPPPOPKP_P?P]PJPQfIR_=H63PMPJPOPE!vZ'J1<13!vZ$_1PSP<PLPGPHPJPEPPPKPQ!~G%O<WEW6W9X28X37M>^WCWBWAW4W<XD5G]!u8%PMP?!sh$R!tB$!sf%GPHM<ZE[W7W5W8W?W@W>W=W:W;XF2XM@WHWKWIWJWLWGo"). Qed.

  (* [comment removed for export] *)
  Theorem drv_hdr_short : forall s msF mo regs mem (sp : word) (can : Z) (K : TSet),
    hfH regs mem sp can ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 0x0bea74) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    K [] ->
    (forall regs' mem' msF' mo', hfPost regs mem sp can regs' mem' ->
       as_VIS H s msF' = mkst regs' (Z_to_bv 64 0x0beab0) mem' rom -> as_AKREL H s (mkCfg msF' mo') ->
       same_but_materialized mo mo' ->
       realizes asegs (mkCfg msF' mo') K) ->
    realizes asegs (mkCfg msF mo) (t_emit (W 2 msg_short) K).
Proof.
ltac2:(KReplay.run1z (kr_t_AsDrvIO ()) ["IO"] "##7%h03mo'h14msF'h24mem'h35regs'h44BACKh52HAh63HA'h72HKh85HKnilh93HS'h:2HVh;3HV'h<4Hfd2h=1Kh>1Lh?2OKh@3OK'hA2PHhB2POhC2RShD3RS'hE1ShF3SB'hG2ZrhH1ahI3canhJ3memhK2mohL3ms'hM3msFhN4regshO1shP2spp;1p;2p;4p;3p;5p;6p;Ap;=g001`j1TTg002dj10Tg003Ij11!s/$nj19Tg004Lj1CTg0000j2R!s8$oj1ATg00mVj4KTg005Qj36Tg00N\j1:Tg00O:j28Tg006Vj54Tg007Wj23Tg008Lj35!sJ$`j1STg00PTj2QTg00QLj1NTg00RDj2MTg00GLj3@!s8$fj1LTg00n[j6<Tg00:Vj2?Tg00;lj4>Tg00ocj2JTg00Ujj2ITg00=3j2H!s/$Sj1GTg00>3j57Tg00?4j3;Tg00@=j1=Tg00AAj2FTg00BHR0j2B!s1$cj4ETg00Cfj3DTg010]lAOTg00FDl=P!tr$fR1f1R2f0R33@p=2p,1HR4#Tg00IRR5g00Hm#0R6#1R7#9%06#0R8#0!s$$9R9#CR:'RR;%98#C#A\:R8g00X@g00JHf4R<f3R=f2R>P2CKf8R?f7R@564p,2fxRAf5RB%17#1!s$$0!s&'R7!s-$!s:,0#:,89RCP<p,3romRDD4'2f9RE13?@RF554g00X^RG#A%S?%:6R6,89RH'Q%NH,MG3@P<g00YV#LO1f=RGf<RHf;RIf:RJP=P>E<fARK=64>PAP<%1!tP'!u`%!tN&9P=P!tH%BRD13=>5541?K=g00KIR7g00LKRL13B<RMPGC>[[[[^05^11^28^3;PAP4p,2DLPGPHPIPJPCPEg0120,J6f6R6'IP<P=1H::#GRNP7P>P2P3f?ROf>RP'3D7f@RQ9;=>PAPPPCPG%=7D4'2P7P@P6PB13>2R7D7fDRC/F>A;E?</2>fHRR=64B/2=A54RM'B[[[^L1!tk%PAPBP<P=PQPOPDPKPP!tn&>P2P?P@PCfC!s>$!vF$g00ZLRKPJPEP?P7D7fGR7/?>PHPIfIP<CEA;GHBPAP@P9P6%=KR<!tq$EP6PBPAP?P9P@P<D4RDP=fJ?DB>P3O6fLR>=646/2D136B954>'BP0fMR0=64@PAPEP9P?P!ss$13@69540PKPLPFP7C>P3fO=64EPAPIP9PJ!sN%fP13JE554PC!w:+EP2P3P@O8W6W;P2P3O2n20010!s#$12!s-%0bHWDW9WFW@WBX05X11X28X3;MAOW4WCW?XGNXENW>M=PW7W8W<W5W:WAW=WIXP:WJWNWKXM1WOo"). Qed.

  Theorem drv_hdr_overrun : forall s msF mo regs mem (sp : word) (can : Z) (K : TSet),
    hfH regs mem sp can ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 0x0bea90) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    K [] ->
    (forall regs' mem' msF' mo', hfPost regs mem sp can regs' mem' ->
       as_VIS H s msF' = mkst regs' (Z_to_bv 64 0x0beab0) mem' rom -> as_AKREL H s (mkCfg msF' mo') ->
       same_but_materialized mo mo' ->
       realizes asegs (mkCfg msF' mo') K) ->
    realizes asegs (mkCfg msF mo) (t_emit (W 2 msg_overrun) K).
Proof.
ltac2:(KReplay.run1 (kr_t_AsDrvIO ()) ["IO"] "h03mo'h14msF'h24mem'h35regs'h44BACKh52HAh63HA'h72HKh85HKnilh93HS'h:2HVh;3HV'h<4Hfd2h=1Kh>1Lh?2OKh@3OK'hA2PHhB2POhC2RShD3RS'hE1ShF3SB'hG2ZrhH1ahI3canhJ3memhK2mohL3ms'hM3msFhN4regshO1shP2spp;1p;2p;4p;3p;5p;6p;Ap;=g001`j1UTg002dj11Tg003Ij10Tg003nj1:Tg004Lj1DTg0000j2OTg004oj1ATg00mVj4LTg005Qj35Tg00N\j18Tg00O:j2<Tg006Vj54Tg007Wj23Tg008Lj36Tg00O`j1TTg00PTj2STg00QLj1RTg00RDj2NTg00GLj3BTg00Rfj1MTg00n[j6@Tg00:Vj2=Tg00;lj4>Tg00ocj2KTg00Ujj2JTg00=3j2ITg00=Sj1HTg00>3j59Tg00?4j3;Tg00@=j1?Tg00AAj2GTg00BHR0j2CTg00Bcj4FTg00Cfj3PTg0132lAQTg00FDl=ETf0R1#1#1p=7g00GfR2f1R3;B1p=2p,1HR4#Ug00IRR5g00Hm#1R6#0R7#:%76R8#1#7#:R9#DR:'OR;%:8#D#A\:R8g00X@g00JHf4R<f3R=f2R>P3CLf8R?f7R@554p,2fxRAf5RB%07#0#0#0#1#0#1#0#1#0#1R7#1#0#7#7#8,<9RCP<p,3romRDD4'2f9RE13?@RF564g00X^RG#A%T?%86R6,<9RH'S%RH,NG3BP<g00YV#MO1f=RGf<RHf;RIf:RJP=P>E@fARK=54>PAP<%07#0#7#7#8,<9R9P=PDD4'2fBRD13=>5641=K=g00KIR7g00LKRL13B<RMPGC>[[[[^05^12^28^3;PAP4p,2DLPGPHPIPJPCPEg014G,K6f6R6'JP<P=1I::#HRNP7P>P3P1f?ROf>RP'3D9f@RQ9;=>PAPPPCPG%?7D4'2P7P@P6PB13>3R7D9fDRC/G>A;E?</2>fHRR=54B/2=A64RM'C[[[^L2^05^12PAPBP<P=PQPOPDPKPPPGPHPIP>P3P?P@PCfCPDPKP=P>E@g00ZLRKPJPEP?P7D9fGR7/=>PHPIfIP<CFA;GHBPAP@P9P6%?KR<D4'2PEP6PBPAP?P9P@P<D4RDP=fJ?PB>P1O6fLR>=546/2D136B964>'CP0fMR0=54@PAPEP9P?P<D4'213@69640PKPLPFP7C>P1fO=54EPAPIP9PJP<D4'2fP13JE564PCPGPHPIPJPEP3P1P@O8W6W;P3P1O2n2001000000120000000bHWDW9WFW@WBX05X12X28X3;MAQW4WCW?XGNXENW>M=EW7W8W<W5W:WAW=WIXP:WJWNWKXM2WOo"). Qed.
End IO.
