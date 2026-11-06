(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import
  PropExec CatExec CatSim StoreOk ShapeAlg SpinAlg AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_As0DrvKitA () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes6option02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct;munrestrictC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct9mrestrictC13~~~K47Corelib4Init5Logic2eq01C47Corelib4Init5Logic6eq_symC46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityK47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct>H_off_segmentsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct>wx_segs_nowrapC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct:lazy_coverC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct4A_wfC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct4MInv00C13~~~K47Corelib4Init9Datatypes4list01K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX29sym_state01C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sym_execC13~~~K47Corelib4Init9Datatypes4prod01C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX25s_logC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX25carryC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=SymExec2Sound4SX2S7regs_okC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=SymExec2Sound4SX2S7know_okC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=SymExec2Sound4SX2S9scs_denotC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26s_regsC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=SymExec2Sound4SX2S9mem_denotC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcctEsame_but_materializedC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4mkstC13~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg9srealizesC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6SymRun9run_soundC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=SymExec2Sound4SX2S8log_flatC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim6msteps00C13~~~I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions7Z_to_bvC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct6hcleanC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6SymRun;carry_afterC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:As0DrvKitAEmrestrict_munrestrictC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanAcctShapeGsrz_msteps_restricted_TC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24s_pcC13~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX27scripts00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX29sym_state00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX23env00C13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26sentry00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5BMode;bm_off_instC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC4ELinuxProcessSemantics?LinuxProcessSem5State?with_vm_backingK4ELinuxProcessSemantics?LinuxProcessSem5State5Model01K4ELinuxProcessSemantics?LinuxProcessSem5State7VmState01I4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State7VmState00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:As0DrvKitA5lzinvC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:As0DrvKitA;sbm_lazy_eqC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:As0DrvKitA=sbm_halted_eqC13~~~K47Corelib4Init5Logic3and01K47Corelib4Init9Datatypes6option01C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indI47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK47Corelib4Init9Datatypes3nat02C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atK47Corelib4Init9Datatypes3nat01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib4Init9Datatypes4list02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec3rdnC13~~~C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_readableC56Stdlib6NArith6BinNat1N6to_natC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBsegment_read_bytesc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:As0DrvKitA9lzinv_sbmC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:As0DrvKitA9rz_run_lzC13~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.

Section FPX_1. Context {fx : PropExec.FPState}.
Section KitA.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.

(* [comment removed for export] *)
Lemma mrestrict_munrestrict : forall (H : word -> bool) (M M' : word -> option byte),
  (forall a, H a = true -> M' a = None) -> mrestrict H (munrestrict H M M') = M'.
Proof.
ltac2:(KReplay.run1 (kr_t_As0DrvKitA ()) ["FPX_1"; "KitA"] "p'0h01Eh11ah21Hh32Hch41Mh52M'h61bi001bp;1p;3p;2p;4p;5p10000p4p70p1000`p4p710R0p8p1001>p4p70P0p8p1001lp4p70P0p8g002bj11Tg003Gj15Tg003ej13Tg004Hj16Tg004jj30Tg005Dj1;Tg005fj34Tg0075j2:j37Tg008Bj22Tg008\j49Tg0098j58Tg00::#1#1#1R0#1#1#1#5#3R1g00:_R2[%50#3R0#6R3\1R4f3R5f0R6O1g00;?R7502f2R8f1R9O1%;0R0503[^11P1P3A4589,:5P9f4R:P6O1P21226f5R;P9O1=026P2f7R<P5O1=026P2P3P9P0P2P3P9P<P:O1f6R<P:O1R=n0100000020000n0100000020000=03=]0P9P<P8O1R<=027P3P;P5O1R;P0P:P5P6O2C9W0g00;_902<123;W0n0110000020000P6O1b0b6A4:58=7:6P8P6O1503eX11D8W3X54W4W2o"). Qed.

(* [comment removed for export] *)
Theorem rz_run_lz : forall (H : word -> bool) (A : list (Z * Z)) fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2
                            E M R model T,
  H_off_segments segs H -> wx_segs_nowrap segs ->
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
  carry (s_log ss') kn [] = (kn', scs2, hs2) ->
  regs_ok E sr R -> know_ok segs E (mrestrict H M) kn ->
  scs_denot segs (mrestrict H M) E scs -> scs_denot segs (mrestrict H M) E scs2 ->
  m_halted model = None ->
  (forall R' MV' model', regs_ok E (s_regs ss') R' -> know_ok segs E MV' kn' ->
     MV' = mem_denot E (mrestrict H M) (s_log ss') ->
     mrestrict H (munrestrict H M MV') = MV' ->
     MInv A model' -> same_but_materialized model model' ->
     srealizes segs scfg (mkCfg (mkst R' (Z_to_bv 64 (s_pc ss')) (munrestrict H M MV') (seg_rom segs)) model') T) ->
  srealizes segs scfg (mkCfg (mkst R (Z_to_bv 64 pc) M (seg_rom segs)) model) T.
Proof.
ltac2:(KReplay.run1 (kr_t_As0DrvKitA ()) ["FPX_1"; "KitA"] "p'0h01Rh12H0h22R'h36model'h41Ah51Eh61Hh72HAh82HCh92HHh:2HIh;3HI'h<2HKh=2HLh>2HRh?3HR'h@2HShA2HahB2HchC5HconthD3HexhE2HhhF3HlfhG3HmshH3HschI4Hsc2hJ3HwxhK1MhL3MV'hM1ThN1ahO1ehP4fuelhQ3hs2hR2knhS3kn'hT5modelhU2nxhV2pchW3scrhX4scr'hY3scshZ4scs2h[2srh\3ss'h]5stopsi001xp;1p;2p;3p;5p;7p;4p;Dp;=p;Ag002bj1<Tg003Gj1CTg003ej1JTg00<?j2=Tg00<_j1;Tg004Hj1KTg00=?j1YTg00=dj2WTg00>Pj2VTg00?bj1STg00A4j1QTg00Alj3NTg00C:j1MTg00DBj2ETg00ELj1DTg00Elj5_Tg00G?j7[Tg00HOj4BTg004jj3:Tg00Hoj11Tg00J<j3XTg00KIj36Tg0075j20Tg00L^j4ITg00N3j4HTg00OJj1UTg005Dj1TTg00PAj1>Tg00QOj32Tg005fj3GTg00Rfj2FTg00T?j1OTg00UJj59Tg00VRj2?Tg00WGj5@Tg00XSlDRTg00Y^j28Tg00[4j37Tg00\>R0j25Tg00\YR1j2bTg00]3j2ATg00]Yj2`Tg00^cl=^Tg008Bj2]Tg00`0j4\Tg00aKlAZTg00bkj1LTf1R2f0R3#L'Ap=Pf5R4f4R5f3R6f2R7'AP2P3D9p=3P4P5%L7,A6P2P3D9p=4f6R8P4P5A2672P3D9p=ag00::#<R9#<#<R:#<#<#<#CR;#JR<g00:_R=[g00d7R>/=>#;g00dUR?%;>g00e4R@g00fE#;g00gS#;RAg00hcRBg00j6RC#;RD%;=REg00kH%C:#J#K\<R:%Y9#C/W<R9g00lURFg00mKp,4segsRGfCRH'V%SGfERI%Q6fDRJ3N%MIfFRK/E41=BDRL/=@PGPKg00;?RMPIPJPHfBRNg00nS#DfAROf@RPD_%DCF[PLP@PBPDf?RBf>RLCBf=RCCB3:1=ADRQ/=E%1P%D=RR7XNPQPEPAPDPCf<RECBf;RQCB3:f9RS96QJPGPEfKRT/0QPJCIPGfLRQ/0EPCPNCHPGfMRU/0CPLPPCH%K<%UE%T<3:fIRV#>RW=6H7PGPJP7fGRXCIfTRY/0JRZ%1TR[52IR\9::6fUR]AG]I5'0=::51E]51FI4g00ocR^PGp,4scfgR_p,2fxR`f8RafORb,P;RcfXRdfHRef7Rf3G%OGRgD9/?8PID@[[[[[[^3F^L:^29P`PGfNR8PUPQPTfJRhPVPePXPKPIPOfPRi/0PPgPBPfP4P5P6MDR%>e=6N3%1eRf,8NP`PPP;PQfQRj/0ORkPgE3P`P3P;PeA2NkfPgE457G'5'5X09,b9P1P9A6HW3%1VRW,8HP`PO1A;UR1fRRk/0NRfPgD9P`P3P;PVA2HfWPgE457G'5'5X09P^PGP_P`POP1PNPgD9/?PPBD@P3%>T=6I318I[P`PHP;PbPZPgE3P`P3P;PTP\PgE457G'5'5P0%>Q=6K2%1QR\,8KP`PJP;Pi10]IRZPgE3P`P2P;PQA2KZ\PgE457G'5P^PGP_P`PIP;PjPKPgE3/?JPHD@P3%>8=6e6%1bRb,8VP`PXP;fSRJ10deRZPgE3P`P5PcPVPZPbPgFa57G'5P0%1iR0,8hP`PeP;PYfY/0VRbPgE3P`P4P;PiA2hb0PgE457GP^PGP_P`PVP;P]PhPgE3/?ePXD@P3%1k,8QP`PTP;fWRbf\R0/0QRZPgE3P`PaP;PJ%1J92UZPgE457GP^PGP_f]R_PVPeP0P`PQP;PdPUPgE3P`PSP;PY10_U%1Y528PgE4PTPhPXPKPIPLP31E_31FU2f`RUP`PEP;Pb10Ui%1b52jPgE4'`POPCfaRC/0jRO%1dRd52kRgP6PSPGPkPOPdfZPRP]PYPJPXP4PIPHM=^1]:gPCPjPgfbP3O1=:=MP7P2P3O2WAXN<C\P7P2O9W8W@W;X3FMAZWGWFP2P3O2n2001000000121000000W1W?P2P3O2n2001000000121000000W1X29P2P3O2n2001000000121100000bOWCWEWIWHW<W>WBWDW:W7W=WJW9WMWTW0WKW5WQXZDXSAXX@WYW\XU?WRW[XV>WWW]WPW4W6o"). Qed.


(* [comment removed for export] *)
Theorem rz_msteps_lz : forall (H : word -> bool) (A : list (Z * Z)) R pc M R' pc' MV' model T,
  H_off_segments segs H -> wx_segs_nowrap segs ->
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model -> m_halted model = None ->
  msteps segs (mkst R pc (mrestrict H M) (seg_rom segs)) (mkst R' pc' MV' (seg_rom segs)) ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
     mrestrict H (munrestrict H M MV') = MV' ->
     srealizes segs scfg (mkCfg (mkst R' pc' (munrestrict H M MV') (seg_rom segs)) model') T) ->
  srealizes segs scfg (mkCfg (mkst R pc M (seg_rom segs)) model) T.
Proof.
ltac2:(KReplay.run1 (kr_t_As0DrvKitA ()) ["FPX_1"; "KitA"] "h06model'h11Ah21Hh32HAh42HCh52HHh62HIh73HI'h82HLh92HSh:2Hah;5Hconth<2Hhh=3Hmsh>3Hwxh?1Mh@3MV'hA1RhB2R'hC1ThD1ahE5modelhF2pchG3pc'p;1p;2p;3p;5p;4p;Ag002bj10Tg003Gj12Tg003ej19Tg00<?j2=Tg00<_j1KTg00=?j1ETg00=dj2CTg004Hj15Tg00>Pj2?Tg00?bj1>Tg00A4j1<Tg00Alj3;Tg00C:j1:Tg00DBj24Tg00OJj1JTg005Dj1ITg004jj33Tg0075j28Tg00T?j1DTg00UJj51Tg00[4j3BTg00Rfj27Tg005fj36Tg00VRj2ATg00WGj5@Tg00]Yj2FTg00`0j4GTg00aKlAHTg00::#0R0#0#0R1#0#0#0#2#9R2g00:_R3[g00d7R4/=4#K%E0#2/C2R0%21#9#5\2R1g00lUR4g00mKp,4segsR5f9R6'?%>5f;R7f3R8#<f:R93;%:7f<R:f5R;'4%52f6R<#J%I233p,2fxR=f=R>P:f?R?/87%D5R@D1P=P9P6f8RAP@D15B5f@RBf0RC'4f1RD,79fCREA6E?:'8=31:g00ocREP5p,4scfgRFP=P?f>RGfDRH?6B>P@D1/A8P7D@[[[^04PEP5PFfARFf7P<PBP=P?PGP>P@D1R>P=P:P7P9P@D1P6PAP;f4R;P8f2RAPD14FC177D1FH>P;P8PAPDfEPFPGfFPCO1g00;?533PAPDPCO2W:XD2CGO4W4W9W7X04MAHW;W=W<W6W3W8W>W5WCWEX@1XG2XB0W?XF2WAW1W2o"). Qed.

(* [comment removed for export] *)
Definition lzinv (H : word -> bool) (A : list (Z * Z)) (model : Model) : Prop :=
  H_off_segments segs H /\ lazy_cover H (m_vm_lazy model) A /\ A_wf A /\ MInv A model /\ m_halted model = None.

Lemma sbm_lazy_eq : forall m m', same_but_materialized m m' -> m_vm_lazy m' = m_vm_lazy m.
Proof.
ltac2:(KReplay.run1 (kr_t_As0DrvKitA ()) ["FPX_1"; "KitA"] "p'0h02m'h11Hh22fdh33fsyh42ioh54lazyh63limh71mi001mh86m_fsysi016m_fsysh94m_ioi024m_ioh:5m_limi035m_limh;6m_proci046m_proch<6m_timei056m_timeh=4m_vmi064m_vmh>4mapsh?3math@2prhA2tmi074m_fdi081vi099vmst_lazyi0:9vmst_mapsi0;Avmst_materializedp;2p;1p;3p;7p;6g00Rfj2=Tg00A4j10Tg010oj13Tg011oj34Tg002bj11Tg003Gj1;Tg003ej1:Tg00<?j28Tg00<_j15Tg004jj32Tg012mj76Tg013cj37Tg008Bj29Tg000`j6<Tg00lUR0f1R1f0R2'=P0f2R3#0%31;43g00::#1#1#1#1#1#1#;#:R4/84#5R5%02R6f3R7#032X00P0%33=462#0=256P3g014[g015SR6P6g016KR6g017CR8g018;R9g0195R:g019nR;f7R<f5R=f4R>P7P3P1P2F6R?#0R@f@#3;4?#0=25@]<]:];]8]9P2g01:h%54f<f6R4=7<=P>P7P3P1P2F6#0,95XA;X6:X@9X38X46W?X55W>P3P1P2O3n0110800013010:10910;W=W2P4P=P>P7P3P1P2O7n01100000170107106102101104103105P1P2E<W1X00W7o"). Qed.
Lemma sbm_halted_eq : forall m m', same_but_materialized m m' -> m_halted m' = m_halted m.
Proof.
ltac2:(KReplay.run1 (kr_t_As0DrvKitA ()) ["FPX_1"; "KitA"] "p'0h02m'h11Hh22fdh33fsyh42ioh54lazyh63limh71mi001mh86m_fsysi016m_fsysh94m_ioi024m_ioh:5m_limi035m_limh;6m_proci046m_proch<6m_timei056m_timeh=4m_vmi064m_vmh>4mapsh?3math@2prhA2tmi074m_fdi081vi099vmst_lazyi0:9vmst_mapsi0;Avmst_materializedp;2p;1p;3p;7p;6g00Rfj2?Tg00A4j15Tg010oj13Tg011oj34Tg002bj10Tg003Gj1;Tg003ej1:Tg004Hj19Tg00OJj11Tg004jj32Tg012mj76Tg00<?j28Tg00<_j17Tg013cj3>Tg008Bj2=Tg000`j6<Tg00lUR0f1R1f0R2'?P0f2R3#5%31;43g00::#0#0#0#0#0#0#;#:R4#9R5%12R6f3R7#132X00P0%52%33;42#1=256P3g014[g015SR6P6g016KR6g017CR8g018;R9g0195R:g019nR;f7R<f5R=f4R>P7P3P1P2F6R?#5f@#3;4?#1%1?525]<]:];]8]9P2g01:h1844#7%74f<f6R4=><=P>P7P3P1P2F6#1,=5XA;X6:X@9X38X46W?W5W>P3P1P2O3n0110800013010:10910;W=W2P4P=P>P7P3P1P2O7n01100000170107106102101104103105P1P2E<W1X00W7o"). Qed.

Lemma lzinv_sbm : forall H A model model',
  lzinv H A model -> MInv A model' -> same_but_materialized model model' -> lzinv H A model'.
Proof.
ltac2:(KReplay.run1 (kr_t_As0DrvKitA ()) ["FPX_1"; "KitA"] "h02H0h11Ah21Hh32H1h42H2h52H3h62H5h72HIh82HSh92_Hh:1lh;5modelh<6model'h=1op;1p;2p;3p;6p;4g002bj16Tg003Gj1ETg003ej1BTg00<?j2=Tg00<_j1?Tg01;_j37Tg00>Pj2<Tg00A4j14Tg00Alj35Tg00C:j13Tg00DBj21Tg004Hj1ATg005Dj1@Tg00\>R0j20Tg00Rfj28Tg00OJj1;Tg004jj3:Tg01<jj3DTg000`j6>Tg01>;j3CTg01?Nj49Tf2R1f1R2#;f0R33:p=2g00::#6#6#6#6#6#6#E#BR4g00:_[g00d7R5/=5#?g00lUR5f3R6?712P0p,4segsR7f4R8'<%41=586%361161%A4R9%@4R:721'0'0'011811886f7R6f6R;;78[[P31<7;f5R8#4=56;%3;11;8A298:'0'0'0P0f8R8%4;;56%36116;A29;:'0'0118;1886f;R;f:R<;78[[P3%48f9R855<%3<11<8A298:'0'0P0%3;11;<A29<:'0f<R8/1<188;f?R<f>R=;78[[P3f=R8#311=8A298:'0P011<=A29=:f@R0/1=180<fCR=fBR8;70[[P3fAR>/10A29>:11=>18=8fFR8,<7%4=R7fER>558R0%3>R?11>=R>%;=R@=:9:RA'0RB'0RC'0P<P0PC1=44#?R4fDRC#4fG?538X:4P;P7ADC=3E>P?PBP6P>PAP2P9%;CA:93:X=9P1P@ACC=3E>C9C9C9C9W8W7W6W9P2P3O2n2001000000121000000W0W5P2P3O2n2001000000121000000W0W4P2P3O2n2001000000121000000W0W3P2P3O2n2001000000121000000W0X<5W;W1W2o"). Qed.

(* [comment removed for export] *)
Lemma mrestrict_some : forall (H : word -> bool) (M : word -> option byte) a b, mrestrict H M a = Some b -> M a = Some b.
Proof.
ltac2:(KReplay.run1 (kr_t_As0DrvKitA ()) ["FPX_1"; "KitA"] "p'0h02H0h11Hh22H1h31Mh41ah51bi001bh62b0h71ei011op;1p;2p;3p;6g002bj10Tg003Gj14Tg003ej13Tg004HR0j15Tg005Dj19Tg01?ij22Tg004jj31Tg01@Kj68Tg01@gj27Tg0075j36Tg00::#0#0#0R1#0#0#0#4#3R2g00:_R3[%41#3R1#5R4\2f3R5f1R6O1P3P3P3P4f0R3%91R7f4R8P5O1n0100000020000f2R9,21R:514f5P8O11215514R8[P31216R;9147P4P7P0P1p-0P3g01AFR0g01Acn10110100021000000X74g01B?P:P3E8P01783b2W0P5P9O1=14;R;P3W0n0110000020000b6A65961213514P;[eX51X42W3W1o"). Qed.

Lemma store_ok_of_mrestrict : forall (H : word -> bool) (M : word -> option byte) n (a : word),
  store_ok segs (mrestrict H M) a n = true -> store_ok segs M a n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_As0DrvKitA ()) ["FPX_1"; "KitA"] "p'0h02Hsh11oi001oh21bi011bh32EHh42H0h51ah61nh72sgh82b0h91Hh:2IHh;1Mh<1ei021si033segi041xp;1p;4p;2p;3p;6g002bj16Tg003Gj1BTg003ej1>Tg004HR0j1=Tg01B[j44Tg008Bj2@Tg01C[j1?Tg004jj37Tg005Dj1DTg01?ij2CTg01D:j25Tg01Ddj1MTg01EBj38Tg01FFj1ATg01GHj1<Tg01HGj1;Tg01IEj1:Tg01Icj3LTg01JFj33Tg01@Kj6JTg01@gj29Tg01Jkj3ITg01Khj4FTg0075j2GTg01LIj2HTg01Lfj1ETg01MDj2KTf4R1f3R2f2R3'Gf1R4f0R5C4p=1g00:_R6g00;?R7775p=01H45#E,K3p=2g00::R8#6#6#6R9#6#6#6#BR:#>R;P6[%B9#>R9#=R<\;g00dUR=p,4segsR>P1P2P5P4D1#0P>P1P4P3C4#0[^5;R?X6=P>P2P3P5g01NKD1#01@67W0X5;P>f5R@P1P5%?3D1#0f6RAP4O1P61@65f7RBP3O1=765P6f9RCP1O1=765P0P9P6P0P9P<P6P<P4%D9RDPCP@O1REn01000000200001C95RFP0g01NjRGP<15:@RH%M8R858>P6P<%A5RI%<5RJ15:ARK%;5#:RL32PDn0100000020000PDn10110400021010300n10110400021010100P>f;RMf:RNg01B?RO9L:8RP93:Af8RQD1g00;_RRn10110400021010100#0P0P9P6P0P9P<PNPAO1PFP0PGP<A8>K8RKP6P<PI15:BRS=2JLPDn0100000020000PDn10110400021010300RTn10110400021010100P>PMA3:BPRUPCC4PRn10110400021010100#0]0]3P4PQP2O1RV#0P0P9P6P0PGP<15:1=8>8P6P<PIA2JHLPDn0100000020000PDn10110400021010300RHP>PNPCA3:@PPBD1RBPRn10110400021010100#0PEP<P0P9P0P9P6P0P9P<P5PFP0PGP<A8>S8RSP6P<PI15:QRW=2JLPDn0100000020000PDn10110400021010300n10110400021010100RXP>f<RYA3:QPRZPNC4PRn10110400021010100#0P5PCPZA8>W8RW%=GR8P0PGP0P9P6P0PGP<P5P6P<PI15:MR[=2JLPDn0100000020000R\PDn10110400021010300P>f@R]f?R^A3:MPR_f=R`D1RaPRn10110400021010100#0%0aRb]0P5P0P9P6P\P>fARcP]A3:YPf>RdD1RePRn10110400021010100#0%A4RfP6P6P0P9P6P6P<P5%<2Rg15:dRh%;2#:Ri32RjPDn0100000020000P>fDRkfCRlA3:^PRmPcD1RnPRn10110400021010100#0%0nRo]0P5P0P9P6%<3Rp15:`Rq%;3#:Rr32P>PlfBRsA3:dPRtP]D1RuPRn10110400021010100#0PjP<P0P9P0P9P6P5P>fFfERjA3:cPRvPlD1RwPRn10110400021010100#0%0wRw]0P5P5X0wX89P5O1A76R7RxP6PRP6p-0P5g01AFRyg01Acn0110100020000X<6POP7P5EJR7Py19w5b4W0n10110000021010100P4O1b1W0P7Py19o5b4X0xn0110100020100P4O1b8W0X7GP5O1P7Py19b5b4X0xn10110000021110200P1O1b1O2X29P5O1PKP8P0PGP0P9P6P0PGP<P5P6P<PI15:C=2JLPDn0100000020000RKPDn10110400021010300P>PdP`A3:CPRbPMD1PRn10110400021010100#0P0P9P6P0PGP<P4P6P<PI15:N=2JLPDn0100000020000RLPDn10110400021010300P>PdA3:NPRJPYC4PRn10110400021010100#0]0P5P0P9P6PKP>P^PdPJPYD1RJPRn10110400021010100#0PfP6P6P0P9P6P6P<P515:YRd=2giRIPDn0100000020000P>PsPcA3:`PP^D1RwPRn10110400021010100#0P0P9P6P6P<P4%<1RO%;1#:Rz72qPDn0100000020000P>PsPtP]C4PRn10110400021010100#0]0P5P0P9P6A2p[rPePRn10110400021010100#0PIP<P0P9P0P9P6P5PnPRn10110400021010100#0P0P9P6P4P>PkA3:]PR]PsC4PRn10110400021010100#0]0P5PcP]P5O2X0oX29P5O1P7Py19x5b4X0xRxn10110000021010100P4O1b1W0Pxn0110100020100P4O1b2W0X7GP5O1Pxn10110001021110200P3O1b1n10110000021110101b1W0W3A76VRP0P9P6P0P9P<PQP1O1PFPHn10110400021010100PBPRn10110400021010100#0PEP<P0P9P0P9P6PXP>P`PYPZPND1RZPRn10110400021010100#0P0P9P6P0P9P<P4PFP0PGP<PWPKPDn10110400021010300n10110400021010100P>P`PbPMC4PRn10110400021010100#0]0P5%0ZPNPbP5O2W0X29P5O1P0P9P6PTP>PYPMPUPCD1PRn10110400021010100#0PSP8P0PGP0P9P6P0PGP<P5PLPDn10110400021010300PJPRn10110400021010100#0P0P9P6P0PGP<P4P\PDn10110400021010300P>P^P_P`C4PRn10110400021010100#0]0P5P0P9P6PLPaPRn10110400021010100#0PfP6P6P0P9P6P6P<P5A2gqiRqPDn0100000020000PuPRn10110400021010100#0P0P9P6P6P<P4A2OhzPDn0100000020000P>PlPmPcC4PRn10110400021010100#0]0P5P0P9P6A2pdrPwPRn10110400021010100#0PqP<P0P9P0P9P6P5P>PjPkP]PsD1R]PRn10110400021010100#0P0P9P6P4P>PjPvPlC4PRn10110400021010100#0]0P5%0]PsPvP5O2W0X29P5O1Pxn10110000021010100P4O1b1W0Pxn0110100020100P4O1b2W0X7GP5O1Pxn10110001021110200P4O1b1W0n10110001021010101P4O1b1W0W3n0110101020101P5P3O2b3b2P0P9P6AI>@4P>PAA3:3PP1C4PRn10110400021010100#0eP>P@P4%?2C4#0eW0X5;X:?X6=P5CFW6W;W9o"). Qed.

Lemma rdn_of_mrestrict : forall (H : word -> bool) (M : word -> option byte), H_off_segments segs H ->
  forall n (a : word) bs, rdn segs (mrestrict H M) a n = Some bs -> rdn segs M a n = Some bs.
Proof.
ltac2:(KReplay.run1 (kr_t_As0DrvKitA ()) ["FPX_1"; "KitA"] "p'0h02Hrh12E2h21oi001oh32EHh42H0h51ah61bi011bh72bsh81nh91rh:1Hh;2HHh<2IHh=1Mh>1ei021li032l0i044resti053segi061xp;1p;2p;3p;4p;6g002bj17Tg003Gj1>Tg003ej1ATg004HR0j1=Tg00>Pj2QTg00<_R1j1NTg0075j26Tg01?ij21Tg01C[j1@Tg008Bj2CTg004jj30Tg005Dj1<Tg00T?j2;Tg01Ddj1PTg01Icj3OTg01JFj32Tg01Oij38Tg01PIj43Tg01D:j2BTg01EBj3MTg01QPj1LTg01GHj1KTg01HGj1JTg01IEj1FTg01LIj2GTg01Lfj1HTg01RRj1ETg01S2j3ITg01@Kj6:Tg01@gj29Tg000`j6?Tg01Khj4DTf5R2f4R3f3R4f2R5f1R6C3f0R730p=5P31645P6P7C3p=4g00::R8#7#7#7R9#7#7#7#>R:#AR;g00:_R<[%>9#AR9#=R=\;p,4segsR>/Q6g00dUR?%N9R@%=@RAP>f6RB/62P6P511@7RCE5PAP>PBP5P411@6RDE5[]7^5;REX8?PAP>1623P6g01NKPCE5P7W0X7@X5;PAP>f7RF/6BP6%@4PCE5f8RGP5O1P<1C<7f9RHP4O1=0<7P<f;R4P2O1=0<7P0P9PAP0P9P=P<P=P6%<9RIP4PBO1RJn01000000200001197RK1;>BRLn10110600021010100P0P@PAP>f=RMf<RN%P8ROg01B?RP5O:RQ92:FRRPHD4A8967,1@RS%<@RTn10110600021010400PTn1011060002101010011@2RU50AP0P9PAP0P9P=PNPFO1PK1;>FRVn10110600021010100P0P@PAP>PMA2:GQRWf:RXC3PSPTn10110600021010400PTn1011060002101010011@BRY50A]0]3P6PXP3O1RZg00;?50<P0P9PA1;>2R[P0P@PAP>PNP4A2:BQPGD4PSPTn10110600021010400R\PTn1011060002101010011@3R]50AP0P9PAP0P9P=PJPKPLn10110600021010100P0P@PAP>PNPRPHC3PSPTn10110600021010400PTn10110600021010100=0AUg01NjRR#=RL1B:B=M>OP0P9PAP0P@P=P0PRPAP7P<PA%L7%K71B:G%J7#F'G#H%>8#E3IPTn0100000020000PTn10110600021010500P1P9P=P7PI1196n10110200020020101103PIn10110600021010200P0P@PAP>f>RIPMPWPXD4PSPTn10110600021010400RWPTn10110600021010100=0AYX2LP7%<RPXPBP6O2E:A0ATUPAPTP0P@p-0P7g01AFRUg01Acn10110000021000000X>ARRPPPYP7E:PU19U7b4b0'9W0W3g00;_90<ZP0P9PAP0P9P=PXP2O1PKP[n10110600021010100P\PTn10110600021010100=0A]PJP=P0P9P0P9PAP0P9P=P7PK1;>GRJn10110600021010100P0P@PAP>f?R]PIA2:HQP4D4PSPTn10110600021010400R\PTn1011060002101010011@F50AP0P9PAP0P9P=P6PK1;>Hn10110600021010100P0P@PAP>P]A2:XQRKPNC3PSPTn10110600021010400PTn1011060002101010011@GRG50A]0P7A0A\GP>f@R\P]PKPND4PA1CA7RKP>fAR[P\A2:4QPMD4R4=0A7P0P@PAP>fCR2fBRZ'6A2:MQP]P7E5R<P0P@PAP6A89B7,1@PTn10110600021010400RL11@MRM50AP0P@PAP>fDR1A2:]QR8P[C3A89F7,1@ROPTn1011060002101040011@IR^50AR_]0]1P6P>P1P2A2:IQP\D4R`=0ACA89B6,1@RB=0A^PA11@5RaP0P@PAP7A89H7,1@PTn10110600021010400Rb11@\Rc50AX2AP7P>fERdA2:\QR\PZC3P[P\P5P6O3E?W0W1X9@P7O1P>PZP[A2:NQRePID4Rf=0AT11@N90ATPAPTPRPPPMP7E:PU19_7b4W0W1n10110001021110201P7P5O2b1b2W0X69P7O1P0P9PAPVPWPTn10110600021010100=0AYPJP=P0P9P0P9PAP7P0P@PAP4PSPTn10110600021010400R4PTn1011060002101010011@HRH50AP0P9PAP6P0P@PAP>P[PePIC3PSPTn10110600021010400PTn1011060002101010011@XRX50A]0P7A0A4XPfPAPKP<P0P@PAP>16d1P8P[P7E511@]R]90ALP0P@PAP>fFR0A2:[QP2C3POPTn10110600021010400=0AcRO]0]1P6PAP>160dP\PZPCE5A0ABcPAPa11@Z90AbX2AP7P>fGA2:ZQRZP1C3P2PZP5P6O3E?W0W1X9@P7O1A0A`TA0AT^PAPTPRPPP]P7E:PU19O7b4W0W1n10110001021110201P7P5O2b1b2W0X69P7O1A0ATGPAPTPRPPPHP7E:PUA0ATX/97b4W0n10110001021110100P6O1b2W0n10110001021110101P6O1b2W0W3n0110101020101P7P5O2b3b6PAP>PFP5%@3PDE5eW0X7@X5;X<EX8?P7CDW8W;W=W:o"). Qed.

(* [comment removed for export] *)
Theorem rz_run_lz2 : forall (H : word -> bool) (A : list (Z * Z)) fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2
                            E M R model T,
  wx_segs_nowrap segs -> lzinv H A model ->
  sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
  carry (s_log ss') kn [] = (kn', scs2, hs2) ->
  regs_ok E sr R -> know_ok segs E (mrestrict H M) kn ->
  scs_denot segs (mrestrict H M) E scs -> scs_denot segs (mrestrict H M) E scs2 ->
  (forall R' M' model', regs_ok E (s_regs ss') R' -> know_ok segs E (mrestrict H M') kn' ->
     mrestrict H M' = mem_denot E (mrestrict H M) (s_log ss') ->
     (forall a, H a = true -> M' a = M a) ->
     lzinv H A model' -> same_but_materialized model model' ->
     srealizes segs scfg (mkCfg (mkst R' (Z_to_bv 64 (s_pc ss')) M' (seg_rom segs)) model') T) ->
  srealizes segs scfg (mkCfg (mkst R (Z_to_bv 64 pc) M (seg_rom segs)) model) T.
Proof.
ltac2:(KReplay.run1 (kr_t_As0DrvKitA ()) ["FPX_1"; "KitA"] "h02H0h12R'h21ah36model'h41oh51Ah61Eh72EQh83EQVh91Hh:2H1h;2H2h<2H3h=2H4h>2H5h?3HI'h@2HKhA3HK'hB2HRhC3HR'hD2HShE2HZhF2HahG2HchH5HconthI3HexhJ3HschK4Hsc2hL3HwxhM1MhN2M'hO3MV'hP1RhQ1ThR1bhS4fuelhT3hs2hU2knhV3kn'hW5modelhX2nxhY2pchZ3scrh[4scr'h\3scsh]4scs2h^2srh_3ss'h`5stopsp;1p;2p;3p;5p;7p;4p;6p;Qg002bj16Tg003Gj1GTg003ej1ITg00<?j2;Tg00<_j17Tg004Hj1NTg00=?j1VTg00=dj2UTg00?bj1STg01;_j3DTg00ELj1BTg00Elj5QTg00G?j7OTg00HOj4ATg004jj31Tg00Hoj1@Tg00J<j3WTg00KIj3FTg0075j22Tg00L^j4>Tg00N3j4MTg00PAj1LTg00QOj3CTg00Rfj2KTg00bkj1TTg00]3j28Tg00T?j1RTg00UJj59Tg00VRj2:Tg00WGj5<Tg00>Pj2HTg00A4j1=Tg00Alj3?Tg00C:j15Tg00DBj23Tg005Dj1PTg00\>R0j20Tg005fj3Jj4[Tg000`j6ETg008Bj2\Tg01T<j7ZTg01UKlQYTg00OJj1XTf2R1f1R2#Xf0R331p=4g00::#6R4#6#6R5#6#6#6#GR6#IR7g00:_R8[g00d7R9/;9#7g00dUR:%79g00e4R;g00fE#7g00gS#7R<g00hcR=g00j6R>#7R?%78R@g00kH%G5#I#NR5\7RA%V4#G/U7R4g00lURBg00mKp,4segsRC#SfDRDfCRE;D11;=?RF/;;PCPEg00;?RGfBRHfARIf@RJf?RKg00nS#Bf>RLf=RMDQ%B>FOPFP;P=P?f<R=f;RFCAf:R>CA311;<?RN/;@%@M%B87WKPNP@P<P?P>f9R@CAf8RNCA31f6RO9FNIPCP@fHRP/2NPIC>PCfIRQ/2@P>PKCMPCfJRR/2>PFPMCMfERS#L=FK1PCPJfORT/21PEC>fPRUf3RV'212UJfGRW#@5CI51AfRRXP3O1=18GPOP2O1PEP2O1515[^27fQRYf4RZ5DXf5R[,KIg00ocR\PCp,4scfgR]p,2fxR^PNfKR_#T,86f7R`%RCRaD9/:OPID<[[[[[[^3B^NA^14P`fLRb?D_>P0fMRc,HC%=F=?cb%5b13bF%N7Rd%P7Re74F'0'0'0P\PCP]P^PM186QPLPaD9/:=PFD<P31HCT%=L=?UT%5T13TLA4dLe'0'0'0P0%=K=?YU%5U13UKA4dKe'0'0P\PCP]P^PI186cPHPaD9/:JPKD<P3fSRK%=I;?X%5K13KHA4dHe'0'0P0fTRI#513IEA4dEe'0P\PCP]P^PS186YfFRJPaD9/:DPED<P3fVRL#5fWRF/3JA4dJe'0P0fXR0/3WA4dWeP\PCP]P^PQfUR^,86PRPaD9/:PPWD<P3fZRP/3QA4dRef]f\f[RePPfYRPP0PFPLP^PIPKPXPYPUPTfNPcPbP_PRPMPQP@P[P2PWPJPSPDPEPHP3%LF=FY1PCPXP1P^C>fb/2X%@P5CK91AVfcRXAJXKZ'2=1AZ13XZ1KK[PRPNffRN?JL`RLPOP[PAP`PCP0P3PeC>X4APZ12NLRLP1EEPAP`fgR`/2Ff^#@5C091A3X4APVPLP1EEP`P3O1=18GP8PGP8P5P3PPP1O1RPP>P1O1n0100000020000=15PXR8P0P2O1R8,\5fhRPP2O1P3EEPPP0P@P2C[=158eWFX27PNfePIPOPYP2P3FZP3O9WDW?W8W7WAWCX3BXOAX14MQYW>W=P2P3O2n2001000000121000000W0W<P2P3O2n2001000000121000000W0W;P2P3O2n2001000000121000000W0W:P2P3O2n2001000000121000000b0WHWKWJW@WBWGWIWEWLWQWWWPWMW6WTX]?XV<X[;W\W_XX:WUW^XY9WZW`WSW5W9o"). Qed.

End KitA.
End FPX_1.


(* [comment removed for export] *)
Ltac run_block_lz_with HR HK HZ Hwx fuel stops scr NX keep :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ (mrestrict ?H ?M) ?kn =>
      lazymatch type of HZ with
      | lzinv _ _ ?A ?model =>
      lazymatch goal with
      | |- srealizes _ ?scfg (mkCfg (mkst R (Z_to_bv 64 ?pc) M _) model) ?T =>
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn NX) []) in
        lazymatch r with
        | (?ss', ?scs, ?scr') =>
          let c := eval vm_compute in (carry (s_log ss') kn []) in
          lazymatch c with
          | (?kn', ?scs2, ?hs2) =>
            eapply (rz_run_lz2 segs scfg H A fuel stops scr pc sr kn NX ss' scs scr' kn' scs2 hs2 E M R model T Hwx HZ);
            [ vm_compute; reflexivity
            | vm_compute; reflexivity
            | exact HR | exact HK
            | split_foralls
            | split_foralls
            | let R' := fresh "R" in let M' := fresh "M" in let model' := fresh "model" in
              let EQM := fresh "EQM" in let EQH := fresh "EQH" in let SBM := fresh "SBM" in
              let HR' := fresh "HR" in let HK' := fresh "HK" in let HZ' := fresh "HZ" in
              intros R' M' model' HR' HK' EQM EQH HZ' SBM; cbn [s_pc s_regs s_log] in HR', EQM |- *;
              lazymatch keep with
              | true => idtac
              | false => clear EQM EQH SBM HR HK HZ; try clear R; try clear M; try clear model;
                         try rename R' into R; try rename M' into M; try rename model' into model;
                         rename HR' into HR; rename HK' into HK; rename HZ' into HZ
              end ]
          end
        end
      end
      end
    end
  end.
