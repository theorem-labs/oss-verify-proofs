(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr Bytes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp MallocKit_A2 F_malloc_big.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_A3.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASlot_W18 () := "C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5queueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib4Spec6Malloc8optr_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8get_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_set_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_set_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8set_headC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K59OSSVerify5KrLib4Spec6Malloc<undef_reason01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_W18;as_queue_stC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00I47Corelib4Init9Datatypes6option00I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03c59OSSVerify5KrLib6Malloc9ASlot_W18;as_queue_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9free_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8put_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_ABEget_meta_rec_put_sameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc9ASlot_W188as_fm_stC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C46Stdlib5Lists4List2InK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00C47Corelib4Init5Logic7f_equalC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7and_indC47Corelib4Init5Logic3notC47Corelib4Init9Datatypes8list_indK47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00c59OSSVerify5KrLib6Malloc9ASlot_W18:outside_InC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01".
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
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
ltac2:(KReplay.run1 (kr_t_ASlot_W18 ()) ["CANSEC1"] "p'0h01rh11oi001oh22Hnh32Hph41Rh51ai011ah64bailh71gh81hh91kh:3st0i021ci034headi045hprevi052pvi061xp;1p;2p;3p;6p;5g0000R0p4p70g000eR1p4p710p8p200R2g001CR3p4p710p8P2g0025R4p4p710p8P3j15Tg002kj2<Tg003hj1?Tg004_j1FTg005Aj33Tg005[j2:Tg006Tj2BTg007Mj19j22Tg008Hj18j26Tg009Cj30Tg00:<j3;Tg00;5j1JTg00;Zj1ETg00<8j1DTg00=7j1CTg00=lj3@Tg00>mj2ATg00?Gj1>TP1j6=TP4j6ITg00@>j2HTg00@`j5GTf1R4f0R1'<#>p=1g00AWR3/H1p=4g00BLg00CAR5f2R6P4P1DGp=7g00C_g00DWR7f4R8#5R9\7f3R:,<6#?%F3R;53011:8=30;P0P;f8R<#5R=g00EPR>f9R?#5R@1:1;RAP>P@f5RBf6RC'1/:;g00F0RDP3P@f7RE,BBPB%4ERF#9PDP3P711C1%4<RG#8g00FRRH11<6%46/61RI'2W0=0<E50111E4%44/61RJ'2X0H=0ECn10110400021010500501O1P8%4CRK16F1,2FX0H=0CB5;EO1RLn10110600021010300RMg00GIRN#J#E#D#CROP8V5RP57<RQn0110200020000%EN#D#CRN=7<PRPn0110200020000P8A@ECBO1RR33X10P0P;P>P@1:;;R;P>P@PAPMPQn0110200020000PPn0110200020000=3=RX101B8CRRP0PDP3PDP3f:#5R0P1PC%9GPDP3P711E1%4?#811?6/2IX0H=0?<50111<4/2JX0H=0<En10110400021010500501R?O1RPPB16G1,2GX0H=0EC9;<FR<O1n10110600021010300PBPDP3P7P1P?P<n10110600021010300O153@P11A0PX53P1O11A=Ln10110000021010100b1%5ERLPDP3P=PRP8%9KPDP3P711B1%8F11E6/2IX0H=0EC50111C4/2JX0H=0CBn10110400021010500501O1P:%4B16K1,2KX0H=0B85;CO1n10110600021010300RHP:A@CB8O1RK33eP>P=P;P>P=P;PHP:V5R597EOn0110200020000A7EN5n0110200020000=3LKe1<8BR5#>P1E=%?5P4E=PEPCPBP8P:P6EI=3LKeW3W2X69W9W:X73W8X42o"). Qed.

Definition as_fm_st (st : mstate) (g : aptr) : mstate := as_queue_st LFree g (put_meta g meta0 st).

Lemma as_free_meta_eq : forall R st g (k : mstate -> Malloc.M R) (bail : Malloc.M R), free_meta g st k bail = k (as_fm_st st g).
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W18 ()) ["CANSEC1"] "h01mh11Rh24bailh31gh41kh52stp;1p;3p;2p;6p;8p;5p200R0g00GnR1p6051000p8P0g001CR2p4p710p8P0g00HoR3p4p710p8P2j12Tg00Iij3<Tg003hj14Tg004_j13Tg005Aj30Tg00>mj2;Tg002kj2:Tg00Jbj35Tg000ej61Tg00?Gj16TP1j87TP3j58Tg00L0j29Tg00DWR3g00AWR1f3R2#2R4\3f4R3g00Lnf2R5g00MfR6=<52R7f1R8f0R9g00FRR:P6g0000R;%49%31R130X0:1;;1R<1:75R7A5256R=E1P:P6%69=0;1X0:P<P7P=E1G7%23P3P5P2P8P9D8P81925O130eX24W4W3W5X10o"). Qed.

Lemma outside_In W x lo hi : outside W x -> In (lo, hi) W -> ~ (lo <= x < hi).
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W18 ()) ["CANSEC1"] "p'0h01Hh12H1h22H0h32HOh41Eh52H2h61Wh72H3h82H4h92HIh:1ah;1bh<1eh=2hih>2loh?1xh@1zi001zhA2H5hB2IHhC2a0hD1lhE1pi011pp;1p;2p;3p;6p;4p;5p;8g00N\j1HTg00O<j23Tg00P2R0j2BTg00PRj34Tg00Pij1CTg00QIj39Tg00Qij27Tg005AR1j31Tg00RDR2j2@Tg00R^j6=Tg00S;j26Tg00SWj25Tg00T3j4<Tg00TNj2FTg00Tmj58Tg00UJj1;Tg000ej8?j6>Tg00>mj2ATg00Ucj5DTg00VEj4ETg00CAR3P3f1R4f0R5CEp=0f3R6f2R7'61545'7#;p=21545,77#;p=:1545,77p=Gg00VeR8#HR9P813561B33R:1067R;;44f4R<f5R=P=P6C2R>[[X69g00WWg00X3R?P?P>P5n010000000W9W3%C8R>/371074=4:>P6P<P<P7C2[[eP0P3P3135=10=<R>=4:4f6R@f7RAPAP=C2[[A9874/3@10@=RBA986754:PAf8RCPCP@C2[[[^D9P5135C10CARD=4:4f9REf:RFPFPCC2[[P6PEPEP7C2134E'710<6RG10ECRH51:A4:H7'@P210FER291:>A4:26f;R>f<RIPIPFC2P510>FRJ91:BP1P:10A@R1f>RBf=RK'0RL91:4f?RMf@RNPNPBC2RO[P510I>RP91:110KIR191:DP:P3P0P3P3P3P5P5n2001101000120100100X<:PHPLP5E=A13CKP:P3P0P3P3P3P5P4n2001101000120100100X<:P210MBP4E=A13FMA13>NP5fAR2913IR0P3fBRDA13KDRQfDRRfERS'6RTfCRU7:S[X@3P5PQP3PUPSfFRQPQPRC2X@3P3PRP5PQPQPMC213BQ'7104N10QSRV51:fGRWfHRXPXPQC2RY]4]3X:3A:TSB13KS'710SM10SR51:P3PS10W510WQ51:fIRT,6XRZ?:T4132T'7PTfJR[P[PXC2R\]3]4X;3A1:VV13NX,7YAGZTWRZP\13D[P?fKRT,3UfLRW,6TRY15W[P?fMR[/5TPSP7O110[W=4:QfNRQfORW'6RS?:W[[fPR[/5QRQP@fQRT,6[15TWP4P5C<O1WAX8SP?\QRQ\SP5P6O1RSPQPSP?1F?5b8b2b8b0W7X5YP7D8W1X2\P4D8W0%;ZeW3W4PNP6P5P4G?W4W3PMP6P>PCG?PBP5E>b5X10PKP5E>b1W2P5O1b2P5O1b2W0P5O1W0n2002101000000101A1:51PBPMPMPKC2[XE:PPO1P51A:1O1b0W4P5O1A4:J<P<PAPKPKP@C2RJ13=KR1P113@BRBP@P5O1RMA4:LAPO[RLPSPO16>2RA15D>R0P=16KU15UIP4P5C<O1W7W1RIP?\0\ARA162DR015U2R2P616UR15RDP4P5C<O1W7W0RRP?\2\0R0P<b0b1b5b1W2X0JP6D8PJP1A4:P=PMPLPSPOPIPAPRP0P@b0b1b5b1X2BX0JP6D8O2W9P5O1n200100000021100011000W9W3A98;4/3EA98G794:HPFP>P>PEC2[[eWBX69X;3X:3P4P5O2n2001101000121100100XC8P6DDX=3X>3X?3X69P6P7P4P5O4X=3X>3X?3W6o"). Qed.

Lemma sub_fp_single W lo hi : In (lo, hi) W -> sub_fp [(lo, hi)] W.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W18 ()) ["CANSEC1"] "h01Wh12hih22loh32HIh42HOh51xp;2p;1p;3p;6p;4g00P2j2>Tg00N\j1=Tg00PRj33Tg00O<j22Tg00S;j2:Tg00SWj29Tg00Qij24Tg00UJj15Tg00XPj66Tg00T3j47Tg00Pij18Tg00QIj31Tg00YPj2<Tg00VEj4;Tg00CAR0P0f1R1f0R2C;p=01>00R3#=R41012f2R5533f4R6/221:61f3R7,91'4#5g00WWf5P1P6P7P2P5E6g00ZEC71067%83R6513/21eW4X501051=136/<7eW3X10X20X04P5P1P2O3X10X20W0o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FAILM.
Variables (st : mstate) (mt : aptr).
Let G := conc st mt.
Hypothesis MST : meta_slot st mt.
(* [comment removed for export] *)
Hypothesis FL : forall h, c_free_meta_head (ctx st) = Some h ->
  meta_slot st h /\ h <> mt /\ exists p, m_prev (get_meta_rec st h) = Some p /\ meta_slot st p /\ p <> mt.

Definition failW : list (Z * Z) :=
  (G, G + 40) :: (CTX + 16, CTX + 24)
  :: match c_free_meta_head (ctx st) with
     | Some h => (conc st h, conc st h + 40)
                 :: match m_prev (get_meta_rec st h) with Some p => [(conc st p, conc st p + 40)] | None => [] end
     | None => []
     end.
End FAILM.


End CANSEC1.
