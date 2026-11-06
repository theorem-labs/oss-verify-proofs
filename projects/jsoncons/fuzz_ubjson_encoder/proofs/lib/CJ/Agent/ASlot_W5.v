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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import Malloc_fp MallocKit_A2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import MallocKit_A3 ASlot_W1.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_ASlot_W5 () := "C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<get_meta_recC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6m_nextC13~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes6option02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:m_set_nextC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:m_set_prevC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8optr_eqbC13~~~C47Corelib4Init9Datatypes4negbC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6m_prevC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8upd_metaC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5lhead01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8get_headC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8set_headC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent8ASlot_W53clrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:set_activeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8put_metaC13~~~K47Corelib4Init5Logic2eq01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_AB<upd_meta_putC13~~~C47Corelib4Init5Logic8eq_ind_rC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8aptr_eqbC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_AB;aptr_eqb_eqC13~~~C47Corelib4Init5Logic5proj2C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7dequeueC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~I47Corelib7Numbers7BinNums1Z00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4optrC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4meta00C13~~~I47Corelib4Init9Datatypes4bool00I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes4bool01C47Corelib4Init5Logic3notC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6activeC13~~~C47Corelib4Init5Logic6eq_symC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_ABFget_meta_rec_put_otherC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_AB>rec_set_activeC13~~~C35stdpp7tactics<f_equal_helpC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_AB<aptr_eqb_neqC13~~~K47Corelib4Init9Datatypes4bool02".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
Definition clr (r : meta) : meta := m_set_prev None (m_set_next None r).

Lemma dequeue_self_eq sc g st :
  m_next (get_meta_rec st g) = Some g ->
  dequeue (LActive sc) g st = put_meta g (clr (get_meta_rec st g)) (set_active sc None st).
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W5 ()) ["CEIL_WRAP_1"] "p'0h01gh12sch22sth32GNh41bh51mh61oh71ri002nxi012pvi021xp;2p;1p;3p;6p;4g0000j25Tg001Fj1ETg002Vj27Tg0038j31Tg003Rj1JTg0044j2Cj16Tg005Hj2Aj19Tg006\j24Tg007nj18Tg008Lj1:Tg009\j30Tg00:nj1DTg00<?j2=Tg00=Qj33Tg00>cj1BTg00@3j3@Tg00AGj3<Tg00BYj2?Tg00C3j3ITg00DPj6;Tg00Dnj2>Tg00F@j2GTg00G\j4FTg00H7j3HTg00IHR0f1R1f0R231p=2g00JZR3g00K8R4g00LFR51521#E174131P5f2R6,74R7f3R8g00MT%J4R91C92'AW7R:g00NdR;P01748R<,42#8P;P0g00ODR=P4P0P2f4R>,58#:R?#9P=P4P0P?%66=02>P8n10110200021010100502P=P4P01568R?#:R@%61=028P6n10110200021010100n10110200021010000RA%D>RB'=/4<A3B2APAn0100000020000A3B96RAn010000002000030%B?A@>965<8R?'2X65P;g00OfR5P;P0%82P;P0%9@P=P4P0P@174>#6=028P6n10110200021010100508R>/=B/4<A3B<>P>n0100000020000PAn0100000020000908:/2?X4;P0A@891RA/56,C9,A9=<6A122?X501516R?#B=<6AR>,?0A06:AAIA6:E;P;P0%85P;P0%:?RA#9P=P4P0PA%6<=026P1n10110200021010100506R<%D8RA'=/47A3A7<P<n0100000020000R<A3A91R9n0100000020000906:/2>e1>66R=A1;=5A1488[A14661>88=1;5[1G661?46CFE;P;P01477#8P<P9n0100000020000906:/2>e%E?P2E;AHA61/2>eW3X20X04X13P6P1P2O3X20W0W1o"). Qed.

Lemma dequeue_other_eq sc g nx pv st :
  m_next (get_meta_rec st g) = Some nx -> m_prev (get_meta_rec st g) = Some pv -> nx <> g -> pv <> g ->
  active st sc = Some g ->
  dequeue (LActive sc) g st =
    let st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st in
    let st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1 in
    let st3 := set_active sc (Some nx) st2 in
    put_meta g (clr (get_meta_rec st g)) st3.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W5 ()) ["CEIL_WRAP_1"] "p'0h01mh11oh21Eh31bh41gh52nxi002nxh62pvi012pvh72sch82sth92GNh:2GPh;2HAh<3NEnh=3NEph>1rh?3st1h@3st2hA3st3i021xp;2p;1p;3p;4p;5p;6p;8g0000j21Tg001Fj1PTg002Vj2<Tg0038j37Tg008Lj1DTg00PFj1BTg00P_j2=Tg003Rj1WTg006\j23Tg007nj1>Tg005Hj1@j2GTg0044j1?j2MTg009\j30Tg00:nj1OTg00<?j2CTg00=Qj3;Tg00>cj1HTg00AGj38j2Nj1VTg00@3j39Tg00BYj2ATg00Qoj4KTg00RKj5JTg00DPj64Tg00T2j4UTg00UQj8ITg00Dnj2FTg00F@j2TTg00G\j4STg00C3j3ETg00Unj3QTg00H7j3RTg00K8R0f1R1f0R237p=:f2R31M12'Gp=L1112,M3p=6f3R41G31;82p=5g00IHR5?712p=2g00JZR6g00LFR71124#P1<03R837f4R9,11#D=778f5R8,:9#Bf6R:,:9#Bf8R;,=9f7R<,<0R=577P7P=f9R>g00MTR?%W0R@?L@2RAW>RBg00NdRCP51<0>RD,32RE#>PCP5g00ODRFP0P5P2f:RG,1<#DRH#@PFP0P5PH%?3=02;P<n10110200021010100502PFP0P511:>RH#D%?1=02<P:n10110200021010100n10110200021010000RI%OGRJ'C/3DA;J2IPIn0100000020000A;J@:RIn010000002000030%HHRH1<0;RKP;P=A6K:<=8<:RL/1;PLC5RL59GRM58>RN'2X17P71<0:ROPCP513KD#>PCP5%@2PFP0P5P2%?D=02<P:n1011020002101010050;RF/CJ/3DA;JKFPFn0100000020000PIn010000002000090>B/2NX17PCg00WKRFPCP5%>2PCP5%@=%?K=0<:50;RP/CJ/3DA;JKPPPn0100000020000PIn010000002000090>B/2NX3CP5P;P@PCP5%@ORI%?=RP=0:8RJ50<RQ/=>/3KA9>=QPQn0100000020000RR=6@;PRC5122NX05P5P<PO11J<PJC5P>P@PCP51=2G/3DA9GK2P2n0100000020000RS=6@>PSC5/2NX05P5A6=8:RS=8:8RTP>P@PCP5P;P=112;P2C5RU/=G/3DA9GKUPUn0100000020000RG=6@>PGC5/2NX05P7PKP>P@PCP5PEPMPLn0100000020000RE=6@>PEC5/2NX17PCg00OfR7P>P@PCP5P2PMPLn0100000020000RL=6@>PLC5/2NX3CP5P511T<,GORO=8<TRN99>=RL/1;RM9L@@RE,N;118;RG#HRV,N;PLPLP?P5\5RW%V;RXPXPEPVPW\?/AXP?11N;RXA7?AHX0?RHP?11T;RAPHP?PGPH1A?VPAP8P:PSP;1:;:RSP3P0P>P<P2CKO1W2%BSeDJE4PXPTP<POP;1:;<ROP4P0P>P;P2CKO1W2%BOeDJE4PMPNP>P=P;CUE4GI1A5LGIA8;ELA8;VLRV'2e1F;;REA7CE71:>>[1:;;1F>>=7C7[1T;;1A0;CSE4P;P@PCP513KKPLPNn0100000020000RN=6@;PNC5/2Ve1=8>P2E4PJAE8:PE4PQAEJ<IE4A0;BRAER;BE4PCP5%>FPCP5%O>R>,CQ/3KA;>=QPQn0100000020000RQA;>@8R@n010000002000090;B/2Ve1F<;AQ<;3E4PCP513=K#>PQP@n010000002000090;B/2Ve%DGP4E4%PGP9E4AR>;8PTP5PUP5f;RU?9D2P511;U#H=8U2bAb@b?'2eW;W=W<W:W9X85X60X50X40X76P9P4P3P1P2O5X85X60X50X40W7o"). Qed.
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
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
