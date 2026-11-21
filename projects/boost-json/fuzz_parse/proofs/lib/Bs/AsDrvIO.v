(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the launch's channel reader. *)
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
  (* LPS 75d69e00, the channel-reader premise.  [aprintf0_first] (Bs/AsPrintfFirst.v:383) gained
     [m_channel_reader mo = true], so this file's replayed application of it was one argument
     short ("Illegal application: @aprintf0_first ... The 16th term has type K [] which should
     be a subtype of m_channel_reader mo = true", a farm round,
     Bs/AsDrvIO.v:64).  A replay cannot be given the extra argument without re-encoding its
     blob, so the three proofs that apply a changed callee -- drv_printf_first, drv_hdr_short
     and drv_hdr_overrun -- are written out as explicit text (rule 11g).  The text is the one
     the As twin (As/AsDrvIO.v) already carries in plain form, which is also the donor's:
     a donor tree:projects/openssl/echconfiglist_parser/proofs/
     lib/As/AsDrvIO.v:51-131.  No address moves: every constant below is this tree's own, as
     the encoded statements already stated them.  drv_msteps and drv_printf_buf apply no
     changed callee and keep their replays untouched. *)
  Theorem drv_printf_first : forall s msF mo regs mem (sp : word) (can : Z) (K : TSet),
    ap1H regs mem sp can ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 0x0bed14) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    m_channel_reader mo = true ->
    K [] ->
    (forall regs' mem' msF' mo', ap1Post regs mem sp can regs' mem' ->
       as_VIS H s msF' = mkst regs' (Z_to_bv 64 0x0bec68) mem' rom -> as_AKREL H s (mkCfg msF' mo') ->
       same_but_materialized mo mo' ->
       realizes asegs (mkCfg msF' mo') K) ->
    realizes asegs (mkCfg msF mo) (t_emit [WriteEv (Z_to_bv 64 1) (Z_to_bv 8 48); WriteEv (Z_to_bv 64 1) (Z_to_bv 8 10)] K).
Proof.
    intros s msF mo regs mem sp can K PH HV HA Hfd1 Hrd1 HKnil HK.
    apply (drv_lazy H DL s msF mo regs _ mem _ HV HA). intros L S Zr OK RS BACK.
    apply (aprintf0_first L S Zr regs mem msF mo sp can K PH OK RS Hfd1 Hrd1 HKnil).
    intros regs' mem' msF' mo' PO OK' SB' HS' RS'. destruct (BACK msF' mo' _ OK' (same_vm_sb _ _ SB') RS') as [HV' HA'].
    exact (HK regs' mem' msF' mo' PO HV' HA' SB').
  Qed.

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
  (* LPS 75d69e00, the channel-reader premise, forwarded to [as_hdr_short_fwrite]
     (Bs/AsHdrErr.v:359), which gained it.  Replay written out -- see drv_printf_first above. *)
  Theorem drv_hdr_short : forall s msF mo regs mem (sp : word) (can : Z) (K : TSet),
    hfH regs mem sp can ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 0x0bea74) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    m_channel_reader mo = true ->
    K [] ->
    (forall regs' mem' msF' mo', hfPost regs mem sp can regs' mem' ->
       as_VIS H s msF' = mkst regs' (Z_to_bv 64 0x0beab0) mem' rom -> as_AKREL H s (mkCfg msF' mo') ->
       same_but_materialized mo mo' ->
       realizes asegs (mkCfg msF' mo') K) ->
    realizes asegs (mkCfg msF mo) (t_emit (W 2 msg_short) K).
Proof.
    intros s msF mo regs mem sp can K PH HV HA Hfd2 Hrd2 HKnil HK.
    apply (drv_lazy H DL s msF mo regs _ mem _ HV HA). intros L S Zr OK RS BACK.
    apply (as_hdr_short_fwrite L S Zr regs mem msF mo sp can K PH OK RS Hfd2 Hrd2 HKnil).
    intros regs' mem' msF' mo' PO OK' SB' HS' RS'. destruct (BACK msF' mo' _ OK' (same_vm_sb _ _ SB') RS') as [HV' HA'].
    exact (HK regs' mem' msF' mo' PO HV' HA' SB').
  Qed.

  (* LPS 75d69e00, the channel-reader premise, forwarded to [as_hdr_overrun_fwrite]
     (Bs/AsHdrErr.v:372), which gained it.  Replay written out -- see drv_printf_first above. *)
  Theorem drv_hdr_overrun : forall s msF mo regs mem (sp : word) (can : Z) (K : TSet),
    hfH regs mem sp can ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 0x0bea90) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    m_channel_reader mo = true ->
    K [] ->
    (forall regs' mem' msF' mo', hfPost regs mem sp can regs' mem' ->
       as_VIS H s msF' = mkst regs' (Z_to_bv 64 0x0beab0) mem' rom -> as_AKREL H s (mkCfg msF' mo') ->
       same_but_materialized mo mo' ->
       realizes asegs (mkCfg msF' mo') K) ->
    realizes asegs (mkCfg msF mo) (t_emit (W 2 msg_overrun) K).
Proof.
    intros s msF mo regs mem sp can K PH HV HA Hfd2 Hrd2 HKnil HK.
    apply (drv_lazy H DL s msF mo regs _ mem _ HV HA). intros L S Zr OK RS BACK.
    apply (as_hdr_overrun_fwrite L S Zr regs mem msF mo sp can K PH OK RS Hfd2 Hrd2 HKnil).
    intros regs' mem' msF' mo' PO OK' SB' HS' RS'. destruct (BACK msF' mo' _ OK' (same_vm_sb _ _ SB') RS') as [HV' HA'].
    exact (HK regs' mem' msF' mo' PO HV' HA' SB').
  Qed.
End IO.
