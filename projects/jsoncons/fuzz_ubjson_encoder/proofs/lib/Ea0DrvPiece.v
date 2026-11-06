(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg Hoare AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  HeapIface HeapIfaceA HeapIfaceAEx IcptIfaceA DrvKitA DrvNodesLazyK As0DrvKitA Ea0DrvEntry Ea0Drv_defs Ea0DrvLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Ea0DrvPiece () := "I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9Ea0DrvLib4dinv00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA4ahidC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct9mrestrictC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4mkstC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim6msteps00C13~~~K47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C45stdpp9bitvector;definitions7Z_to_bvC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9Ea0DrvLib3CWAC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcctEsame_but_materializedC13~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9Ea0DrvLib:dinv_lzinvC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:As0DrvKitA5lzinvC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct>H_off_segmentsC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct:lazy_coverC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct4A_wfC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct4MInv00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct6hcleanC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct;munrestrictC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:As0DrvKitAEmrestrict_munrestrictC13~~~K47Corelib4Init5Logic2eq01C47Corelib4Init5Logic8eq_ind_rC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9Ea0DrvLib8ahid_sbmC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9Ea0DrvLib7sbm_vmlC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:As0DrvKitA=sbm_halted_eqC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9Ea0DrvLib:dinv_frameC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanAcctShapeGsrz_msteps_restricted_TC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg9srealizesC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5BMode;bm_off_instC13~~~C79OSSVerify8jsonconsCfuzz_ubjson_encoder6images4Asan1M?loaded_segmentsC13~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA6fframeC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface6creditC13~~~K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7FPState00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~K47Corelib7Numbers7BinNums1Z01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Ea0Drv_defs8asegs_wxC13~~~K47Corelib4Init9Datatypes4bool02".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Piece.
Variable scfg : SpuriousCfg.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable IL : icpt_layout.
Variable HI : asan_iface.
Hypothesis HIok : asan_iface_okB L ar C scfg HI.
Variable sp0 : word.
Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
Hypothesis DL : drv_layoutA L ar IL sp0.
Variable M0 : word -> option byte.

#[local] Notation dinvA := (dinv ar HI sp0 M0).
#[local] Notation rom := (seg_rom ASEGS).

Theorem drv_piece : forall LB LK cr A M (model : Model) (fx fx' : PropExec.FPState) R (pc : word) R' (pc' : word) (MV' : word -> option byte) (W : Z -> Prop) K,
  dinvA LB LK cr A M model ->
  msteps ASEGS (@mkst fx R pc (mrestrict (ahid A model) M) rom) (@mkst fx' R' pc' MV' rom) ->
  (forall a : word, mrestrict (ahid A model) M a <> None -> MV' a <> None) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> MV' (Z_to_bv 64 a) = mrestrict (ahid A model) M (Z_to_bv 64 a)) ->
  (forall a, W a -> CWA sp0 LB a) ->
  (forall M1 (model1 : Model),
      dinvA LB LK cr A M1 model1 -> same_but_materialized model model1 ->
      mrestrict (ahid A model1) M1 = MV' ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      srealizes ASEGS scfg (mkCfg (@mkst fx' R' pc' M1 rom) model1) K) ->
  srealizes ASEGS scfg (mkCfg (@mkst fx R pc M rom) model) K.
Proof.
ltac2:(KReplay.run1 (kr_t_Ea0DrvPiece ()) ["Piece"] "p'0h01ah11Eh21Hh31bi001bh42Hah52Hnh62M1h76model1h81oh91Ah:2AHh;2DIh<3FR1h=2FZh>2GRh?2HAh@2HChA2HHhB2HLhC2HMhD2HhhE2HwhF1KhG4KONThH2LBhI2LKhJ1MhK3MI1hL2MShM3MV'hN1RhO2R'hP3SBMhQ3VIShR1WhS2WChT2crhU2fxhV3fx'hW5modelhX2pchY3pc'p;2p;1p;:p;5p;3p;Ap;4p;6p;Ig0000j2`Tg000Pj1MTg0010j18Tg001Uj1BTg0023j1ITg002Vj1JTg0038j1WTg003]j2STg004Il:ETg005Tj22Tg006^j2?j3@Tg007kj1PTg0096j54Tg00:>j3_Tg00;Hj1KTg00;jj30Tg00<Dj13Tg00<]j2XTg00=9j1HTg00=Wj2VTg00>4j2UTg00>PR0j21Tg00>kj29Tg00?Qj3FTg00@Yj2GTg00B2j2:Tg00BglARTg00D6j4QTg00EAj2DTg00FSj1>Tg00GKj3=Tg00HYj17Tg00Iaj25Tg00Jkj2OTg00L5j3NTg00MDj4TTg00N_j2LTg00O9j6<Tg00OWj4^Tg00Pdj3]Tg00R0j1CTg00Rgj3\Tg00T:lIYTg00UIlAZTg00Vij5[Tg00X5R1g00YAR2f2R3f1R4f0R5D[p=;%C4=035p=6g00ZNR6g00Zn705p=Ag00[NR7/`7#MR8g00[l#Mg00]8g00^C#8R9#8#8R:#8#8#8R;#BR<#IR=%B:#IR:#JR>[R?g00^hR@g00_^RA%W9#B/S=RBp-0\7g00`kp,2arRCp,2HIRDp,3sp0REp,2M0RFf>RGf=RHf<RIf;RJf:RKf9RLM:EPLf7RMf6RN12IK/?J%P2ROD4f8RPf5RQf4RRf3RSPOD45_212GI?@H5%K:R:50>#3PNP4O1RT=0>:#3[^0=g00b3/X5%H9%H;'V,U5'1R;%3TPP19<3RTO1fAR9f?RU'2RVf@RW;@T50>[[^07PNP5O1RXfDRY=FE4[^07PCPDPEPFfERZPYfCR[fBR\P4P5M:E1G9412Y3/?S=0?JPHP4O1#3PMPTO1fGR]PTO150>[\;^07p,4scfgR^P\PUPGPQPOD4/:R;;J[[[[^7@^6?P^p,1LR_PCp,1CR`p,2ILRaPDp,4HIokRbPEp,2DLRcPFPYP[P\P9PWPUPQMARP2PVP9PUCQP012\WRU,D2%>W==U\%7\15\W%J=RU%K=RV76W'1'1'1PWPGPHP\POD4/:9=;^PP512Y\,D212Z[%>[;=Z%7Z15Z[A6U[V'1'1'1P0fFR[/2Y%>Y;=[%7[15[YA6UYV'1'1PYP\P9P[POD4/:Z=;^IP5fHR9/2[%>[;=9fIR\#715\]A6U]V'1'1P0fJR]#715]9A6U9V'1P9P[PZP]POD4/:\=;^WP5fLRW#7fMRZfKRd'5A6UdV'1P0fNR0/5WA6UWVPWP]P\P0POD4/:Z=;^YP5fPRY/50fOR\=6UVfRRe/2YP6\=RfP1P2P^P5PGg00bQfSRGPYP0PZPePOD4P\PWPdP]POD4fQRdP9PKPNP3P4P[fTR[/551GG4PeP\P0PZPOD4,OSfVRO=NR0P?PQfWR0P\%AXPSP4P5O2W4X0=CT1?Q5=0?\PdP4O1#3RdPLPTO1P61L65RXPK19<SO1=065P6PI19<QRZO1R9=065P6P>P4f_RW19<NR2O1R1P0P2O1n0100000020000=0>1]1P4PJ19<RO1R<#Af^R2PZO1R0,L>RgW1g00c`Rh906<P>A@I2ZR<A0>51X8>P6PhP6P>P5P:P1n0100000020000=0>1X36PgP9P5E<A0><0ePOPZO1PYPQPRPSO3E<W1n0110000020001P5O1b1b3PRPTO1f[RYPTO150>RTeW5X4;X07PT\d\;^07fZRdfXRTPNPRC^12dN=0fMRZePZP]PSPMP^P_PCP`PaPDPbPEp,3HspPcPFP2f]f\PYPdPSfYRdPMP\f`R2=FE4#3PRP3P4P[P3O1R[P4P\PSP5O2O1WE%3[eO3W5X4;X07PYP5O1=0>:#3PKP4O1P6PXPJP3O1=065P6PHPRO1RJ=065P6P>P4P2PQO1R2PTPQO1n0100000020000=0>:#3]1P4PIPSO1RI#APSW1A06IhPePRP6PhP6P>P5P:P2n0100000020000=0>:#3X36PSPJP5E<A@HWR=0>:#3eO2W1n0110000020000P5O1b1b3PQP4O1=0>:#3eW4X0=A]dMQPNPU%CdA0U5VX8UPL%CMA\dMQE<MIYPQPfPP1?5R=0?GX3fP312YMP5E<P4O6b:b<bQb6W@WPWKX7@MAZb2WDWCP4P5O2n2001000000121000000W2W?P4P5O2n2001000000121000000W2WBP4P5O2n2001000000121000000W2WAP4P5O2n2001000000121000000b2WGWSW=W>WLW;WFWRXM?XY=XOBXX=WNXVAWUWWWJX98WTWIWHo"). Qed.
End Piece.
