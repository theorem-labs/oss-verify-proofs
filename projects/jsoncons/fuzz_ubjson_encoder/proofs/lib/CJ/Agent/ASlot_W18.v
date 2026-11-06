(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr Bytes.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import Malloc_fp MallocKit_A2 F_malloc_big.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import MallocKit_A3.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_ASlot_W18 () := "C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc1MC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5queueC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<get_meta_recC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6m_nextC13~~~K47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8optr_eqbC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8get_headC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:m_set_prevC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:m_set_nextC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8upd_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8set_headC13~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<undef_reason01C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc2ev06C13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9ASlot_W18;as_queue_stC13~~~K47Corelib4Init5Logic2eq01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6m_prevC13~~~C47Corelib4Init5Logic8eq_ind_rK47Corelib4Init9Datatypes6option01K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree5stree02C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc2ev00C13~~~I47Corelib7Numbers7BinNums1Z00I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5lhead00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4optrC13~~~I47Corelib4Init9Datatypes4bool00I47Corelib4Init9Datatypes6option00I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4meta00C13~~~K47Corelib7Numbers7BinNums8positive03c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9ASlot_W18;as_queue_eqC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9free_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8put_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_ABEget_meta_rec_put_sameC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9ASlot_W188as_fm_stC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5lhead02C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5meta0C13~~~I47Corelib4Init9Datatypes4list00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame7outsideC13~~~I47Corelib4Init9Datatypes4prod00C46Stdlib5Lists4List2InK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00C47Corelib4Init5Logic7f_equalC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7and_indC47Corelib4Init5Logic3notC47Corelib4Init9Datatypes8list_indK47Corelib4Init9Datatypes4prod01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3ivlC13~~~I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9ASlot_W18:outside_InC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame6sub_fpC13~~~K47Corelib4Init5Logic4True01".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition as_fm_link (st0 : mstate) (g head : aptr) : mstate :=
  let hprev := m_prev (get_meta_rec st0 head) in
  let st1 := upd_meta g (fun r => m_set_prev hprev (m_set_next (Some head) r)) st0 in
  let st2 := match hprev with Some pv => upd_meta pv (m_set_next (Some g)) st1 | None => st1 end in
  upd_meta head (m_set_prev (Some g)) st2.

Definition as_fm_single (st0 : mstate) (h : lhead) (g : aptr) : mstate :=
  set_head h (Some g) (upd_meta g (fun r => m_set_prev (Some g) (m_set_next (Some g) r)) st0).

Definition as_queue_st (h : lhead) (g : aptr) (st0 : mstate) : mstate :=
  match get_head st0 h with
  | Some head => as_fm_link st0 g head
  | None => as_fm_single st0 h g
  end.

Lemma as_queue_eq : forall R h g st0 (k : mstate -> Malloc.M R) (bail : Malloc.M R),
  m_next (get_meta_rec st0 g) = None -> m_prev (get_meta_rec st0 g) = None ->
  queue h g st0 k bail = k (as_queue_st h g st0).
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W18 ()) ["CEIL_WRAP_1"] "p'0h01rh11oi001oh22Hnh32Hph41Rh51ai011ah64bailh71gh81hh91kh:3st0i021ci034headi045hprevi052pvi061xp;1p;2p;3p;6p;5p200R0g0000R1p4p710p8P0g001;R2p4p710p8P1j15Tg002Jj2<Tg003`j1?Tg0050j1FTg005Rj33Tg005lj2:Tg007>j2BTg008Pj19j22Tg009dj18j26Tg00;8j30Tg00<Jj3;Tg00=\j1JTg00>Aj1ETg00>_j1DTg00@7j1CTg00AEj3@Tg00B^j2ATg00C8j1>Tg00DHj6=TP2j6ITg00Dfj2HTg00EHj5GTf1R2f0R1'<#>p=1g00FXR3/H1p=4g00Gfg00I4R4f2R5P2P1DGp=7g00IRg00JcR6f4R7#5R8\6g00L5R9f3R:,<5#?%F3R;3311:7=39;P9P;f8R<#5R=g00MCR>f9R?#5R@1:1;RAP>P@f5RBf6RC'1/:;g00McRDP3P@f7RE,BBPB%4ERF#9PDP3P611C1%4<RG#8g00NERH11<5%45/61RI'2W0=0<E50111E2%42/61RJ'2X0H=0ECn10110400021010500501O1P7%4CRK16F1,2FX0H=0CB5;EO1RLn10110600021010300RMg00OURN#J#E#D#CROP7V4RP57<RQn0110200020000%EN#D#CRN=7<PRPn0110200020000P7A@ECBO1RR33X19P9P;P>P@1:;;R;P>P@PAPMPQn0110200020000PPn0110200020000=3=RX191B7CRRP9PDP3PDP3f:#5R9P1PC%9GPDP3P611E1%4?#811?5/2IX0H=0?<50111<2/2JX0H=0<En10110400021010500501R?O1RPPB16G1,2GX0H=0EC9;<FR<O1n10110600021010300PBPDP3P6P1P?P<n10110600021010300O153@P11A9PX53P1O11A=Ln10110000021010100b1%5ERLPDP3P=PRP7%9KPDP3P611B1%8F11E5/2IX0H=0EC50111C2/2JX0H=0CBn10110400021010500501O1P:%4B16K1,2KX0H=0B75;CO1n10110600021010300RHP:A@CB7O1RK33eP>P=P;P>P=P;PHP:V4R497EOn0110200020000A7EN4n0110200020000=3LKe1<7BR4#>P1E=%?4P2E=PEPCPBP7P:P5EI=3LKeW3W2X68W9W:X73W8X40o"). Qed.

Definition as_fm_st (st : mstate) (g : aptr) : mstate := as_queue_st LFree g (put_meta g meta0 st).

Lemma as_free_meta_eq : forall R st g (k : mstate -> Malloc.M R) (bail : Malloc.M R), free_meta g st k bail = k (as_fm_st st g).
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W18 ()) ["CEIL_WRAP_1"] "h01mh11Rh24bailh31gh41kh52stp;1p;3p;2p;6p;8p;5p200R0g00P:R1p6091000p8P0g0000R2p4p710p8P0g00QSR3p4p710p8P2j12Tg00Rfj3<Tg003`j14Tg0050j13Tg005Rj30Tg00B^j2;Tg002Jj2:Tg00T8j35Tg00DHj61Tg00C8j16TP1j87TP3j58Tg00U^j29Tg00JcR3g00FXR1f3R2#2R4\3f4R3g00W4f2R5g00XER6=<52R7f1R8f0R9g00NER:P6g00L5R;%49%31R130X0:1;;1R<1:75R7A5256R=E1P:P6%69=0;1X0:P<P7P=E1G7%23P3P5P2P8P9D8P81925O130eX24W4W3W5X10o"). Qed.

Lemma outside_In W x lo hi : outside W x -> In (lo, hi) W -> ~ (lo <= x < hi).
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W18 ()) ["CEIL_WRAP_1"] "p'0h01Hh12H1h22H0h32HOh41Eh52H2h61Wh72H3h82H4h92HIh:1ah;1bh<1eh=2hih>2loh?1xh@1zi001zhA2H5hB2IHhC2a0hD1lhE1pi011pp;1p;2p;3p;6p;4p;5p;8g00YTj1HTg00Z4j23Tg00[CR0j2BTg00[cj34Tg00\:j1CTg00\Zj39Tg00]:j27Tg005RR1j31Tg00]UR2j2@Tg00]oj6=Tg00^Lj26Tg00^hj25Tg00_Dj4<Tg00__j2FTg00`>j58Tg00`[j1;Tg00DHj8?j6>Tg00B^j2ATg00a4j5DTg00aVj4ETg00I4R3P3f1R4f0R5CEp=0f3R6f2R7'61545'7#;p=21545,77#;p=:1545,77p=Gg00b6R8#HR9P813561B33R:1067R;;44f4R<f5R=P=P6C2R>[[X69g00cAg00c]R?P?P>P5n010000000W9W3%C8R>/371074=4:>P6P<P<P7C2[[eP0P3P3135=10=<R>=4:4f6R@f7RAPAP=C2[[A9874/3@10@=RBA986754:PAf8RCPCP@C2[[[^D9P5135C10CARD=4:4f9REf:RFPFPCC2[[P6PEPEP7C2134E'710<6RG10ECRH51:A4:H7'@P210FER291:>A4:26f;R>f<RIPIPFC2P510>FRJ91:BP1P:10A@R1f>RBf=RK'0RL91:4f?RMf@RNPNPBC2RO[P510I>RP91:110KIR191:DP:P3P0P3P3P3P5P5n2001101000120100100X<:PHPLP5E=A13CKP:P3P0P3P3P3P5P4n2001101000120100100X<:P210MBP4E=A13FMA13>NP5fAR2913IR0P3fBRDA13KDRQfDRRfERS'6RTfCRU7:S[X@3P5PQP3PUPSfFRQPQPRC2X@3P3PRP5PQPQPMC213BQ'7104N10QSRV51:fGRWfHRXPXPQC2RY]4]3X:3A:TSB13KS'710SM10SR51:P3PS10W510WQ51:fIRT,6XRZ?:T4132T'7PTfJR[P[PXC2R\]3]4X;3A1:VV13NX,7YAGZTWRZP\13D[P?fKRT,3UfLRW,6TRY15W[P?fMR[/5TPSP7O110[W=4:QfNRQfORW'6RS?:W[[fPR[/5QRQP@fQRT,6[15TWP4P5C<O1WAX8SP?\QRQ\SP5P6O1RSPQPSP?1F?5b8b2b8b0W7X5YP7D8W1X2\P4D8W0%;ZeW3W4PNP6P5P4G?W4W3PMP6P>PCG?PBP5E>b5X10PKP5E>b1W2P5O1b2P5O1b2W0P5O1W0n2002101000000101A1:51PBPMPMPKC2[XE:PPO1P51A:1O1b0W4P5O1A4:J<P<PAPKPKP@C2RJ13=KR1P113@BRBP@P5O1RMA4:LAPO[RLPSPO16>2RA15D>R0P=16KU15UIP4P5C<O1W7W1RIP?\0\ARA162DR015U2R2P616UR15RDP4P5C<O1W7W0RRP?\2\0R0P<b0b1b5b1W2X0JP6D8PJP1A4:P=PMPLPSPOPIPAPRP0P@b0b1b5b1X2BX0JP6D8O2W9P5O1n200100000021100011000W9W3A98;4/3EA98G794:HPFP>P>PEC2[[eWBX69X;3X:3P4P5O2n2001101000121100100XC8P6DDX=3X>3X?3X69P6P7P4P5O4X=3X>3X?3W6o"). Qed.

Lemma sub_fp_single W lo hi : In (lo, hi) W -> sub_fp [(lo, hi)] W.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W18 ()) ["CEIL_WRAP_1"] "h01Wh12hih22loh32HIh42HOh51xp;2p;1p;3p;6p;4g00[Cj2>Tg00YTj1=Tg00[cj33Tg00Z4j22Tg00^Lj2:Tg00^hj29Tg00]:j24Tg00`[j15Tg00d:j66Tg00_Dj47Tg00\:j18Tg00\Zj31Tg00eRj2<Tg00aVj4;Tg00I4R0P0f1R1f0R2C;p=01>00R3#=R41012f2R5533f4R6/221:61f3R7,91'4#5g00cAf5P1P6P7P2P5E6g00f`C71067%83R6513/21eW4X501051=136/<7eW3X10X20X04P5P1P2O3X10X20W0o"). Qed.
End CEIL_WRAP_1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
