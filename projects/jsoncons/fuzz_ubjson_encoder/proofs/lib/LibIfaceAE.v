(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec StoreOk ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA LibIface LibIfaceAB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_LibIfaceAE () := "C46Stdlib5Lists4List2InK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:LibIfaceAE>lib_call_okA_xC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8LibIface8ls_stateC13~~~I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:LibIfaceAB8lib_preA00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA6vml_ofC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA6ri_invC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct4MInv00C13~~~K47Corelib4Init9Datatypes4list01I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:LibIfaceAB9lib_postA00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA8model_rtC13~~~C46Stdlib5Lists4List4inclK47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA8ff_countC13~~~C56Stdlib6ZArith6BinInt1Z6of_natC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:LibIfaceAB8lla_leakC13~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:LibIfaceAB5lla_LC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA7hl_segsC13~~~C45stdpp9bitvector;definitions7Z_to_bvC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:LibIfaceAB8lib_cfgAC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg9srealizesC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:LibIfaceAB<lib_call_okAC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:LibIfaceAB;lib_layoutA00C13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA8asan_run00C13~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run;SpuriousCfg00I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA:asan_iface00C13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8LibIface;lib_statics00C13~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7FPState00C13~~~I47Corelib7Numbers7BinNums1Z00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA6fframeC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface6creditC13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00K47Corelib7Numbers7BinNums1Z01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5BMode;bm_off_instC13~~~K47Corelib4Init5Logic4True01i79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:LibIfaceAE?lib_iface_okA_x00C13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:LibIfaceAB=lib_iface_okA00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:LibIfaceABAlib_statics_initAC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:LibIfaceABBlib_statics_frameAC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:LibIfaceAEAlib_call_okA_of_xC13~~~K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:LibIfaceAB=lib_iface_okA01C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:LibIfaceAEElib_call_okA_x_weakenC13~~~k79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:LibIfaceAE?lib_iface_okA_x01C13~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section LibIfaceAE.
Variable Lay : lib_layoutA.
Variable ar : asan_run.
Let L := lla_L Lay.
Variable scfg : SpuriousCfg.
Variable HI : asan_iface.
Variable LSt : lib_statics.
Variables PayOk PayExport : list byte -> Prop.

Definition lib_call_okA_x : Prop :=
  forall (fx : FPState) (g : ls_state LSt) (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z))
         (sp ptr ra : Z) (payload : list byte) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : ShapeAlg.TSet),
    lib_preA Lay ar LSt g LB FF LK cr sp ptr ra payload R M ->
    PayOk payload ->
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    K [] ->
    (forall (fx' : FPState) (g' : ls_state LSt) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (cr' : credit)
            (LK' : list fframe) (A' : list (Z * Z)),
        lib_postA Lay ar LSt g' LB FF cr sp payload R M R' M' cr' ->
        PayExport payload ->
        model_rt model model' -> incl A A' -> m_halted model' = None -> MInv A' model' ->
        (forall k, In k [0; 1; 2; 3; 4; 5] -> Z.of_nat (ff_count k LK') <= Z.of_nat (ff_count k LK) + lla_leak Lay k) ->
        ri_inv HI LB FF LK' cr' A' M' (vml_of model') ->
        srealizes (hl_segs L) scfg (@lib_cfgA Lay fx' R' (Z_to_bv 64 ra) M' model') K) ->
    srealizes (hl_segs L) scfg (@lib_cfgA Lay fx R (Z_to_bv 64 (lla_entry Lay)) M model) K.

Record lib_iface_okA_x : Prop := LIOKAX {
  lioax_call : lib_call_okA_x;
  lioax_init : lib_statics_initA Lay ar LSt;
  lioax_frame : lib_statics_frameA Lay ar LSt
}.
End LibIfaceAE.

(* [comment removed for export] *)
Lemma lib_call_okA_of_x : forall Lay ar scfg HI LSt (PE : list byte -> Prop),
  lib_call_okA_x Lay ar scfg HI LSt (fun _ => True) PE -> lib_call_okA Lay ar scfg HI LSt.
Proof.
ltac2:(KReplay.run1 (kr_t_LibIfaceAE ()) [] "h02A'h13LK'h22M'h32R'h43cr'h53fx'h62g'h71kh86model'h91Ah:4CONTh;2FFh<1Hh=2HIh>2HKh?2Hhh@3Hh'hA2IAhB1KhC2LBhD4LEAKhE2LKhF3LSthG3LayhH1MhI2MIhJ3MI'hK3MRThL2PEhM4POSThN3PREhO1RhP2RIhQ3RI'hR2_HhS2arhT2crhU2fxhV1ghW5modelhX7payloadhY3ptrhZ2rah[4scfgh\2spp;1p;7p;2p;>p;8p;3p;6p;5p-1g0000R0p4p710p8g000Gj11Tg000lj1;Tg001Jj1ATg001mj18Tg002Mj7RTg003aj16Tg004mj2PTg005Mj1@Tg0062j2LTg006^j1=Tg007@l>ITg008Pj19Tg009\j85Tg00:hj1<Tg00;_j1QTg00<Aj37Tg00<[j2:Tg00=ej1FTg00>El>ETg00?Vj2CTg00@dj3BTg00A=j12Tg00A[j30TP0j3MTg00B;j23Tg00CIj14Tg00Cij2?Tg00E7j2DTg00ETj2>Tg00F0j1JTg00G;j1KTg00HHj2HTg00Hnj6NTg00J<j5OTg00KHj5GTg00LZg00Mmg00O=g00P7g00QIg00RZR0#1R1#1R2#1R3#;#AR4#8R5p-0[f5R6f4R7f3R8f2R9f1R:g00S?V5f0R;FRg00S[R<%68g00ThR=/P=R>#8R?g00UF#8R@g00VRRA%@1RB#;%13#1#1#;R3#ARC'LRD%=4\CR4g00W]REg00XSfERFfDRGfARHf=RIf<RJf;RKf:RLf9RMf7RNf6ROP6P7P8P9M>IfCRPPIPJPKPLPMP8%99G5%=CRQ%<8%QCRC371:K7P7g00Y[#FO1fGRR#6fRRSfQRTfNRUPOfIRVfHRWfFPGPHf@RXf?RYP6P7P9M>E1CY7AB>R9%<O=7QC1:7Ng00ZQ%20%21%@0#2%22%2B%F=50=50=50=50=50=50=9M=;RBf8R2,3:#413:U#4fYR0/?:'D'>[^7=fUfOR1PUPNP2POPL%9MG5g00Zo%J0#KfWRUP0f>R0PJ1H3VPKPLENPGDO[[[[[[[^0?^1@^4A^8E^24^3D]6^5<PFPGPPfBRGPHPXPYP0PIPJPKPLPMP2PNPOP6g00\;P7P8P9P:%6WfSPSP1POfJPVPRPFPGPHPXP6P7P9M>EP1PPO11CH6AB>V8%<N=7QC1:6213:M#4fPRC,3:#4f[/?:'D'>\B^7=PUPTPCP2PMPNPK%9LG5PXPYP0PIPJPKPLPMP2PNP6P7P8P9P:P;O?WQWDWJW@WAWKWRWMX0?X1@X4AX8EX24X3DW6X5<OFW:W>WIW?WPWNWBWWWHWOXX5XZ=XY=X\=X9?WTXE@W;WCWVWUPOP6P7P8P9DGeW<WLWFW=W[WSWGo"). Qed.
Lemma lib_iface_okA_of_x : forall Lay ar scfg HI LSt (PE : list byte -> Prop),
  lib_iface_okA_x Lay ar scfg HI LSt (fun _ => True) PE -> lib_iface_okA Lay ar scfg HI LSt.
Proof.
ltac2:(KReplay.run1 (kr_t_LibIfaceAE ()) [] "p'0h01Ch11Fh21Hh32HIh42I0h53LSth63Layh72PEh82arh94scfgi00:lioax_calli01;lioax_framei02:lioax_initp;1p;7p;5p;3p;8g000Gj10Tg000lj1:Tg001Jj12Tg001mj11Tg00\WR0j79Tg00]nj58Tg002Mj73Tg00_Cj34Tg00`Zj35Tg00b2j76Tg00cIj87Tg00LZg00Mmg00O=g00P7g00QIg00RZ#0#0#0#:#2#1R1p-0[f5R2f4R3f3R4f2R5f1R6g00S?V1R1f0R7F9P0f6R0P2P3P4P5P1P6f7R8P0P2P3P4D8P7f9R4f8R9P8P0P2P1P3F3f:R3?440f;R0?538f<R1P0P3P4P9P1P0P3P4P9P8P5F6P6P7G7W1W4W0P5P6P7O3n700000001000000130100102101W2W7W5W3W9W8W6o"). Qed.
(* [comment removed for export] *)
Lemma lib_call_okA_x_weaken : forall Lay ar scfg HI LSt (P P' E E' : list byte -> Prop),
  (forall p, P' p -> P p) -> (forall p, E p -> E' p) ->
  lib_call_okA_x Lay ar scfg HI LSt P E -> lib_call_okA_x Lay ar scfg HI LSt P' E'.
Proof.
ltac2:(KReplay.run1 (kr_t_LibIfaceAE ()) [] "h02A'h13LK'h22M'h32R'h43cr'h53fx'h62g'h71kh86model'h91ph:1Ah;4CONTh<1Eh=2E'h>2EXh?2FFh@1HhA2HEhB2HIhC2HKhD2HPhE2HhhF3Hh'hG2IAhH1KhI2LBhJ4LEAKhK2LKhL3LSthM3LayhN1MhO2MIhP3MI'hQ3MRThR2OKhS1PhT2P'hU4POSThV3PREhW1RhX2RIhY3RI'hZ2arh[2crh\2fxh]1gh^5modelh_7payloadh`3ptrha2rahb4scfghc2spp;1p;7p;2p;>p;8p;3p;6p;5g000Gj10Tg000lj18Tg001Jj1>Tg001mj17Tg002Mj7FTg003aj16Tg004mj2PTg005Mj1=Tg0062j2LTg006^j1:Tg007@l>ITg008Pj19Tg009\j85Tg00:hj1GTg00;_j1QTg00<Aj3ETg00<[j2CTg00=ej1BTg00>El>ATg00?Vj2?Tg00@dj3@Tg00A=j12Tg00A[j31Tg0000j3MTg00B;j24Tg00CIj13Tg00Cij2<Tg00E7j2DTg00ETj2;Tg00F0j1JTg00G;j1KTg00HHj2HTg00Hnj6NTg00J<j5OTg00LZg00Mmg00O=g00P7g00QIg00RZR0#0R1#0R2#0R3#8#>R4#7R5p-0[R6f3R7f0R8O1R9f5R:f1R;O1[^95P7P;O1\9^95f:R9f9R<f8R=f7R>f6R?P:P7FFg00S[R@%6=g00ThRA/PARB#7RCg00UF#7RDg00VRRE%=1RF#8%03#0#0#8R3#>RG'LRH%:4\GR4g00W]RIg00XSfJRJfIRKfFRLf=RMf<RNf;ROP9P<P>P?P:f4RPP7f2RQM>IfERRP:O1PKf>RSPMPNPOP9PP%97G5%:GRT%GP%QGRG3E1CN:P:g00Y[#BO1fM#6fXRUfWRVfTP?PJPKfGPRfBRWfARXf@RYP:PPPQM>AfQRZfCR[O11?X:A@BK7%G>=ETGRG1C:=RTg00ZQ%20%21%=0#2%22%2F%BA51A51A51A51A51A51A9MA8RF14;<#3R2fPR0,4;#3f`R1/<;'D';[^7Af\PZP0P=P<P>PO%99R0G5g00Zo%J1#Kf^P1f?R1PMfKRK,H3PNPOENPLDO[[[[[[[[^0C^1D^4E^8I^24^3H]6^5@PLPRfDRRP[PWPXPYP1PSPMPNPOP9P<P=P>P?fHR3POP:O2PPP7PQP;fN#6fYPUfUP?PKPJP3PLP[PWPXP:PPPQM>AfSPRO11?W:A@BJ714;Z#3fa/<;'D,;2\F^7Af]fRPZP=P<P>POP0G5PYP1PSPMPNPOP9P<P=P>PVPKP?O2P:PPP7PQP;P8O@WYWJXPTXFGWGWQW>WUX0CX1DX4EX8IX24X3HW6X5@OFW;WCWOWEWXWRWVWHW^WNWWX_5XaAX`AXcAX:CW[XKDW?WIW]W\POP9P<P=P>P:P7FFeW@WAWDX=6X<6XT6WSWLWBWbWZWMo"). Qed.
Lemma lib_iface_okA_x_weaken : forall Lay ar scfg HI LSt (P P' E E' : list byte -> Prop),
  (forall p, P' p -> P p) -> (forall p, E p -> E' p) ->
  lib_iface_okA_x Lay ar scfg HI LSt P E -> lib_iface_okA_x Lay ar scfg HI LSt P' E'.
Proof.
ltac2:(KReplay.run1 (kr_t_LibIfaceAE ()) [] "p'0h01ph11Ch21Eh32E'h41Fh51Hh62HEh72HIh82HPh92I0h:3LSth;3Layh<1Ph=2P'h>2arh?4scfgi00:lioax_calli01;lioax_framei02:lioax_initp;1p;7p;3p;<p;:g000Gj10Tg000lj19Tg001Jj13Tg001mj12Tg00\WR0j71Tg002Mj78Tg00_Cj37Tg00`Zj34Tg00d^l<5Tg00f9l:6Tg00LZg00Mmg00O=g00P7g00QIg00RZ#0#0#0#9#3#2R1p-0[R2f3R3f0R4O1R5f5R6f1R7O1[^01P3P7O1\5^01f:R1f9R5f8R8f7R9f6R:P6P3F1P0f;R0P1P5P8P9P:f4R3f<R6P0P1P5P8P:P3F1P4f>R3f=R:P6P0P1P5P9F8f?R;?730f@R<?4;6fAR=P<P;P3P:P0P5P=P<P;P3P:P6P0P1P5P8P9f2R9M<5P7P4M:6W4W9W1P9P7P4O3n700000001000000130100102101W5W6W8X32X22X=2W<W:W7W?W>W;o"). Qed.
(* [comment removed for export] *)
Lemma lib_call_okA_x_of_plain : forall Lay ar scfg HI LSt (P : list byte -> Prop),
  lib_call_okA Lay ar scfg HI LSt -> lib_call_okA_x Lay ar scfg HI LSt P (fun _ => True).
Proof.
ltac2:(KReplay.run1 (kr_t_LibIfaceAE ()) [] "h02A'h13LK'h22M'h32R'h43cr'h53fx'h62g'h71kh86model'h91Ah:4CONTh;2FFh<1Hh=2HIh>2HKh?2Hhh@3Hh'hA2IAhB1KhC2LBhD4LEAKhE2LKhF3LSthG3LayhH1MhI2MIhJ3MI'hK3MRThL1PhM4POSThN3PREhO1RhP2RIhQ3RI'hR2_HhS2arhT2crhU2fxhV1ghW5modelhX7payloadhY3ptrhZ2rah[4scfgh\2spp;1p;5p;2p;>p;8p;3p;6p;7g000Gj11Tg000lj1;Tg001Jj1@Tg001mj15Tg00KHj5RTg003aj14Tg004mj2PTg005Mj1?Tg0062j2LTg006^j1>Tg007@l>GTg008Pj17Tg009\j89Tg00:hj1<Tg00;_j1QTg00<Aj36Tg00<[j2:Tg00=ej1DTg00>El>CTg00?Vj2BTg00@dj3ATg00A=j12Tg00A[j30Tg0000j3MTg00B;j23Tg00CIj18Tg00Cij2KTg00E7j2ITg00ETj2=Tg00F0j1HTg00G;j1JTg00HHj2FTg00Hnj6NTg00J<j5OTg002Mj7ETg00LZg00Mmg00O=g00P7g00QIg00RZR0#1R1#1R2#1R3#;#@R4#5R5p-0[f5R6f4R7f3R8f2R9f1R:DRg00S[R;%48g00ThR</P<R=#5R>g00UF#5R?g00VRR@%?1RA#;%13#1#1#;R3#@RB'LRC%>4\BR4g00W]RDg00XSfEREfDRFfARGf=RHf<RIf;RJf:RKf9RLf7RMf6RNP6P7P8P9M>GPGP6O1PFf>ROPHPIPJPKP7%78G9%>BRP%<7%QBRB361:I6P6g00Y[#DO1fHRQ#4fSRRfRfOPNfJRSfIRTfGPEfBRUPGf@RVP6P7P9M>Cg00S?RW1BG6AA=T8%<M=6PBf8RX,:6f0RYg00ZQ%20%21%?0#2%22%2A%D<50<50<50<50<50<50<5M<RA13:L#8fPR2,3:#8f[R0/K:'IR1'=[^7<fWRZfQR[P2PXPLPMPJ%7KG9g00Zo%H0#JfYP0f?R0PHfKR\,F3PIPJENfFR3DO[[[[[[[[^0>^1?^4@^8D^24^3C]6^5;P3PEPFfCRFPUPGPVP0POPHPIPJPKPLPXPMPNP7P8P9P:%4TfTPRP2PNP\PSPQP3PFPUPGP6P7P9M>C1BG7AA=T9%<N=6PB1:7M13:X#8/=1\A^7<PZP[P2PMPXPNPK%7LG9P0POPHPIPJPKPLPXPMPNg00\;P6P7P8P9P:PYO@WQWDWJW@WAWKWMX0>X1?X4@X8DX24X3CW6X5;OEW:W>WIW?WPWRWNWBWWWHWOXX5XZ<XY<X\<X9>WTXE?W;WCWVWUPNP6P7P8P9P:PWV5FEeW<WLWFW=W[WSWGo"). Qed.
