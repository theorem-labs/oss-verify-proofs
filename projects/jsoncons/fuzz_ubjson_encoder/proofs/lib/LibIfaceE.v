(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec StoreOk ShapeAlg SpinAlg HeapIface LibIface.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_LibIfaceE () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9LibIfaceE=lib_call_ok_xC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8LibIface8ls_stateC13~~~I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8LibIface7lib_pre00C13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface7hi_heapC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyK47Corelib4Init9Datatypes4list01C4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedI79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8LibIface8lib_post00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface<model_but_vmC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8LibIface7ll_heapC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface7hl_segsC13~~~C45stdpp9bitvector;definitions7Z_to_bvC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8LibIface7lib_cfgC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg9srealizesC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8LibIface;lib_call_okC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5BMode5BMode00C13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8LibIface:lib_layout00C13~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run;SpuriousCfg00I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface:heap_iface00C13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8LibIface;lib_statics00C13~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7FPState00C13~~~I47Corelib7Numbers7BinNums1Z00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface6creditC13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00K47Corelib4Init5Logic4True01i79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9LibIfaceE>lib_iface_ok_x00C13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8LibIface<lib_iface_ok00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8LibIface@lib_statics_initC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8LibIfaceAlib_statics_frameC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9LibIfaceE@lib_call_ok_of_xC13~~~K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8LibIface<lib_iface_ok01C13~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section LibIfaceE.
Variable Lay : lib_layout.
Let L := ll_heap Lay.
Variable scfg : SpuriousCfg. Context {bmK : BMode}.
Variable HI : heap_iface.
Variable LSt : lib_statics.
Variables PayOk PayExport : list byte -> Prop.

Definition lib_call_ok_x : Prop :=
  forall (fx : FPState) (g : ls_state LSt) (LB : list (Z * Z)) (cr : credit) (sp ptr ra : Z) (payload : list byte)
         (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : ShapeAlg.TSet),
    lib_pre Lay LSt g LB cr sp ptr ra payload R M ->
    PayOk payload ->
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    K [] ->
    (forall (fx' : FPState) (g' : ls_state LSt) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (cr' : credit),
        lib_post Lay LSt g' LB cr sp payload R M R' M' cr' ->
        PayExport payload ->
        hi_heap HI LB cr' M' (m_vmmaps model') ->
        model_but_vm model model' ->
        srealizes (hl_segs L) scfg (@lib_cfg Lay fx' R' (Z_to_bv 64 ra) M' model') K) ->
    srealizes (hl_segs L) scfg (@lib_cfg Lay fx R (Z_to_bv 64 (ll_entry Lay)) M model) K.

Record lib_iface_ok_x : Prop := LIOKX {
  liox_call : lib_call_ok_x;
  liox_init : lib_statics_init Lay LSt;
  liox_frame : lib_statics_frame Lay LSt
}.
End LibIfaceE.

(* [comment removed for export] *)
Lemma lib_call_ok_of_x {bmK : BMode} : forall Lay scfg HI LSt (PE : list byte -> Prop),
  lib_call_ok_x Lay scfg HI LSt (fun _ => True) PE -> lib_call_ok Lay scfg HI LSt.
Proof.
ltac2:(KReplay.run1 (kr_t_LibIfaceE ()) [] "h02M'h12R'h23bmKh33cr'h43fx'h52g'h66model'h74CONTh81Hh92HBh:2HHh;3HH'h<2HIh=2HKh>2Hhh?2Hlh@2HmhA1KhB2LBhC3LSthD3LayhE1MhF2PEhG4POSThH3PREhI1RhJ2_HhK2crhL2fxhM1ghN5modelhO7payloadhP3ptrhQ2rahR4scfghS2spp;1p;7p;2p;;p;5p;3p;<p;6g0000j10Tg000Uj16Tg0013j1<Tg001Vj11Tg0026j7JTg003Hj12Tg004Tj2:Tg0054j1@Tg005Yj2>Tg006Ej18Tg006gl;=Tg0084j17Tg008kj55Tg00:7j1ITg00:nj1HTg00;Pj34Tg00;jj1CTg00<bj13Tg00=Bj1BTg00>Bl<9Tg00?Pj2;Tg00@aj1ATg00Alj1?Tg00C8j2DTg00C^j6ETg00Dij5FTg00F5j5GTg00GDR0g00HLg00I\g00JVg00Kgg00M8#0R1#0#0R2#6#<R3#1R4p-0[f4R5f3R6f5R7f2R8f1R9g00M]V4f0R:FJg00N9R;%26g00OFR</:<#1g00OdR=%@1#6%02#0#0#6R2#<R1'>R>%83\1R3g00PoR?g00QefAR@f>RAf:RBf9RCf8RDf7REf6RFP7P5P6P8M;=f@RGPBPCP6%78RHD5%81%I6%H1341:11RI#1%C5%3I34%11%B7%3134P7g00Rm#3O1fER1#2fMfJP5P1fDRIfCRJPGf?RKPAP6P8P:M<9fLfFRLP9P6PHD51;K6fQfPRH#A#?fOPHPDPF1D2IP7P5EEPKDF[[[^3=^6?^03^1>]5^4;PJfBRJP@PGPKPAf=f<f;PBPCPDPEPFg00ScP7P5P6P8P9%2LfNRAfKR2P5PLP1PIP@PGPKP6P8P:M<9P2PJO1PAfHP8P5%76D51;@5PBPCPDPEPFP7P5P6P9P:O9W9W;WJWGX3=X6?X03X1>W5X4;ODW7W=W@W?W>W:WHWAWNWEWIXO4XQ<XP<XS<WKWBWMWLP7P5PFP6P8DGeW8WFWCW<WRWDX20P:O1W2o"). Qed.
Lemma lib_iface_ok_of_x {bmK : BMode} : forall Lay scfg HI LSt (PE : list byte -> Prop),
  lib_iface_ok_x Lay scfg HI LSt (fun _ => True) PE -> lib_iface_ok Lay scfg HI LSt.
Proof.
ltac2:(KReplay.run1 (kr_t_LibIfaceE ()) [] "p'0h03bmKh11Ch21Fh31Hh42HIh52I0h63LSth73Layh82PEh94scfgi009liox_calli01:liox_framei029liox_initp;1p;7p;5p;2p;8g0000j10Tg000Uj1:Tg0013j12Tg001Vj11Tg00T?R0j79Tg00UTj58Tg0026j73Tg00Vfj24Tg00X:j25Tg00YOj76Tg00Zdj87Tg00GDR1g00HLg00I\g00JVg00Kgg00M8#0#0#0#:#2#1R2p-0[f4R3f3R4f5R5f2R6f1R7g00M]V2R2f0R8F9P0P5P3f6R0P4P6P2P7P0P5f7R9P3P4D8P8f8R4P9f9R:P0P5P2P3F314:0f:R0/59f;R3P0f<R2P:P4P2P3P0P:P4P9P6F6P7P8G7W2W5W1P6P7P8O3n700000001000000130100102101W3W8W6W4W9W7X01P8O1W0o"). Qed.
(* [comment removed for export] *)
Lemma lib_call_ok_x_weaken {bmK : BMode} : forall Lay scfg HI LSt (P P' E E' : list byte -> Prop),
  (forall p, P' p -> P p) -> (forall p, E p -> E' p) ->
  lib_call_ok_x Lay scfg HI LSt P E -> lib_call_ok_x Lay scfg HI LSt P' E'.
Proof.
ltac2:(KReplay.run1 (kr_t_LibIfaceE ()) [] "h02M'h12R'h23bmKh33cr'h43fx'h52g'h66model'h71ph84CONTh91Eh:2E'h;2EXh<1Hh=2HBh>2HEh?2HHh@3HH'hA2HIhB2HKhC2HPhD2HhhE2HlhF2HmhG1KhH2LBhI3LSthJ3LayhK1MhL2OKhM1PhN2P'hO4POSThP3PREhQ1RhR2crhS2fxhT1ghU5modelhV7payloadhW3ptrhX2rahY4scfghZ2spp;1p;7p;2p;;p;5p;3p;<p;6g0000j10Tg000Uj15Tg0013j1:Tg001Vj11Tg0026j7<Tg003Hj13Tg004Tj28Tg0054j1ATg005Yj2?Tg006Ej17Tg006gl;>Tg0084j1=Tg008kj56Tg00:7j1ITg00:nj1HTg00;Pj32Tg00;jj1GTg00<bj14Tg00=Bj1FTg00>Bl<9Tg00?Pj2;Tg00@aj1BTg00Alj1@Tg00C8j2CTg00C^j6DTg00Dij5ETg00GDR0g00HLg00I\g00JVg00Kgg00M8#0R1#0#0R2#5#:R3#1R4p-0[R5f3R6f0R7O1R8f5R9f1R:O1[^74P6P:O1\8^74f9R8f8R;f:R<f7R=f6R>P9P6F<g00N9R?%3;g00OFR@/8@#1g00OdRA%A1#5%02#0#0#5R2#:R1'?RB%73\1R3g00PoRCg00QefFRDfCREP<P8P;P=P>P9f4RFP6f2RGM;>fBRHP9O1PDf;RIP<PF%=6RJD6%71%IF%H1321811RK#1%G9%4K32%11%F>%4132P>g00Rm#4O1fK#3fSR1fPPFPDfERKfDRLfARMf@RNf?ROP6PGP7M<9fMPHO1P1fHPGPFPJD61;MFfXfWR1#B#@fVP1P8P=1C2DP>P9EDPMDE[[[[^3A^6C^03^1B]5^4?PLPEPHPMPNPOf>f=f<ROPIP<P8P;P=PDPOP>O2P9PFP6PGP:fL#3fTROfQPFfGPDPKPHPMPNP6PGP7M<9fORNPEO1POfIPGPFPJD61;HFP<P8P;P=P>P9PFP6PNPDPGO2P:P7O:W=W@W;WOX3AX6CX03X1BW5X4?ODW8WBWFWEWDW?WLWPWGWUWKWQXV4XX@XW@XZ@WRWHWTWSP<P8PIP;P=P9P6F<eW<W>WCX:5X95XN5WMWIWAWYWJX20P7O1W2o"). Qed.
