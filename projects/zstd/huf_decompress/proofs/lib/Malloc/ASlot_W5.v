(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast MallocTree MallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp MallocKit_A2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_A3 ASlot_W1.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASlot_W5 () := "C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib4Spec6Malloc:m_set_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_set_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8optr_eqbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8get_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8set_headC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_W53clrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8put_metaC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib6Malloc<MallocKit_AB<upd_meta_putC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8aptr_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_AB;aptr_eqb_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib4Spec6Malloc7dequeueC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes4bool01C47Corelib4Init5Logic3notC59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib6Malloc<MallocKit_ABFget_meta_rec_put_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_AB>rec_set_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_AB<aptr_eqb_neqC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02".
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition clr (r : meta) : meta := m_set_prev None (m_set_next None r).

Lemma dequeue_self_eq sc g st :
  m_next (get_meta_rec st g) = Some g ->
  dequeue (LActive sc) g st = put_meta g (clr (get_meta_rec st g)) (set_active sc None st).
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W5 ()) ["CANSEC1"] "p'0h01gh12sch22sth32GNh41bh51mh61oh71ri002nxi012pvi021xp;2p;1p;3p;6p;4g0000R0p4p70R1g000eR2p4p710p8P1p1001?R3p4p710R4p8P1P3p4p7210R3p8P1g001\R1p4p710R5p8g002:R6p4p70R7P4p8P7P3p8P7P5p8g002oj25Tg003lj1ETg004cj27TP2j31Tg005Ej1JTg005gj2Cj16Tg006bj2Aj19Tg007]j24Tg008Vj18Tg0094j1:Tg009kj30Tg00:dj1DTg00;\j2=Tg00<Uj33Tg00=Nj1BTg00>Fj3@Tg00?Aj3<Tg00@:j2?Tg00@Tj3ITP1j6;Tg00AYj2>Tg00BRj2GTg00CVj4FTg00D1j3HTg00DiR1f1R2f0R531p=2g00EbR71552#E1702516P6f2R3,70R4f3R8g00F@%J0R91C95'AW7R:g00G7R;P11708R<,45#8P;P1g00GWR=P0P1P5f4R>,58#:R?#9P=P0P1P?%63=05>P8n10110200021010100505P=P0P11538R?#:R@%62=058P3n10110200021010100n10110200021010000RA%D>RB'=/4<A3B5APAn0100000020000A3B93RAn010000002000030%B?A@>935<8R?'2X66P;g00H9R6P;P1%85P;P1%9@P=P0P1P@170>#6=058P3n10110200021010100508R>/=B/4<A3B<>P>n0100000020000PAn0100000020000908:/2?X4;P1A@892RA/53,C9,A9=<3A125?X511523R?#B=<3AR>,?1A03:AAIA3:E;P;P1%86P;P1%:?RA#9P=P0P1PA%6<=053P2n10110200021010100503R<%D8RA'=/44A3A4<P<n0100000020000R<A3A92R9n0100000020000903:/2>e1>33R=A1;=6A1088[A10331>88=1;6[1G331?03CFE;P;P11444#8P<P9n0100000020000903:/2>e%E?P5E;AHA32/2>eW3X21X00X17P3P2P5O3X21X00W1o"). Qed.

Lemma dequeue_other_eq sc g nx pv st :
  m_next (get_meta_rec st g) = Some nx -> m_prev (get_meta_rec st g) = Some pv -> nx <> g -> pv <> g ->
  active st sc = Some g ->
  dequeue (LActive sc) g st =
    let st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st in
    let st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1 in
    let st3 := set_active sc (Some nx) st2 in
    put_meta g (clr (get_meta_rec st g)) st3.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W5 ()) ["CANSEC1"] "p'0h01mh11oh21Eh31bh41gh52nxi002nxh62pvi012pvh72sch82sth92GNh:2GPh;2HAh<3NEnh=3NEph>1rh?3st1h@3st2hA3st3i021xp;2p;1p;3p;4p;5p;6p;8g002oj21Tg003lj1PTg004cj2<Tg000ej37Tg0094j1DTg00HYj1BTg00I2j2=Tg005Ej1WTg007]j23Tg008Vj1>Tg006bj1@j2GTg005gj1?j2MTg009kj30Tg00:dj1OTg00;\j2CTg00<Uj3;Tg00=Nj1HTg00?Aj38j2Nj1VTg00>Fj39Tg00@:j2ATg00Iij4KTg00JEj5JTg001\j64Tg00KTj4UTg001?j8ITg00AYj2FTg00BRj2TTg00CVj4STg00@Tj3ETg00L[j3QTg00D1j3RTg0000R0f1R1f0R237p=:f2R31M12'Gp=L1112,M3p=6f3R41G31;82p=5g00DiR5?712p=2g00EbR6g002:R71124#P1<03R837f4R9,11#D=778f5R8,:9#Bf6R:,:9#Bf8R;,=9f7R<,<0R=577P7P=f9R>g00F@R?%W0R@?L@2RAW>RBg00G7RCP51<0>RD,32RE#>PCP5g00GWRFP0P5P2f:RG,1<#DRH#@PFP0P5PH%?3=02;P<n10110200021010100502PFP0P511:>RH#D%?1=02<P:n10110200021010100n10110200021010000RI%OGRJ'C/3DA;J2IPIn0100000020000A;J@:RIn010000002000030%HHRH1<0;RKP;P=A6K:<=8<:RL/1;PLC5RL59GRM58>RN'2X17P71<0:ROPCP513KD#>PCP5%@2PFP0P5P2%?D=02<P:n1011020002101010050;RF/CJ/3DA;JKFPFn0100000020000PIn010000002000090>B/2NX17PCg00M`RFPCP5%>2PCP5%@=%?K=0<:50;RP/CJ/3DA;JKPPPn0100000020000PIn010000002000090>B/2NX3CP5P;P@PCP5%@ORI%?=RP=0:8RJ50<RQ/=>/3KA9>=QPQn0100000020000RR=6@;PRC5122NX05P5P<PO11J<PJC5P>P@PCP51=2G/3DA9GK2P2n0100000020000RS=6@>PSC5/2NX05P5A6=8:RS=8:8RTP>P@PCP5P;P=112;P2C5RU/=G/3DA9GKUPUn0100000020000RG=6@>PGC5/2NX05P7PKP>P@PCP5PEPMPLn0100000020000RE=6@>PEC5/2NX17PCg00H9R7P>P@PCP5P2PMPLn0100000020000RL=6@>PLC5/2NX3CP5P511T<,GORO=8<TRN99>=RL/1;RM9L@@RE,N;118;RG#HRV,N;PLPLP?P5\5RW%V;RXPXPEPVPW\?/AXP?11N;RXA7?AHX0?RHP?11T;RAPHP?PGPH1A?VPAP8P:PSP;1:;:RSP3P0P>P<P2CKO1W2%BSeDJE4PXPTP<POP;1:;<ROP4P0P>P;P2CKO1W2%BOeDJE4PMPNP>P=P;CUE4GI1A5LGIA8;ELA8;VLRV'2e1F;;REA7CE71:>>[1:;;1F>>=7C7[1T;;1A0;CSE4P;P@PCP513KKPLPNn0100000020000RN=6@;PNC5/2Ve1=8>P2E4PJAE8:PE4PQAEJ<IE4A0;BRAER;BE4PCP5%>FPCP5%O>R>,CQ/3KA;>=QPQn0100000020000RQA;>@8R@n010000002000090;B/2Ve1F<;AQ<;3E4PCP513=K#>PQP@n010000002000090;B/2Ve%DGP4E4%PGP9E4AR>;8PTP5PUP5f;RU?9D2P511;U#H=8U2bAb@b?'2eW;W=W<W:W9X85X60X50X40X76P9P4P3P1P2O5X85X60X50X40W7o"). Qed.

Section DEQ.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis HA : active st sc = Some g.
Hypothesis AV0 : m_avail mr = 0.
Hypothesis FR0 : m_freed mr = 0.

Definition deq_regs (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 CTX) a0 a1 a2 (Z_to_bv 64 (CTX + 8 * (sc + 10))) a4 a5 a6 a7
      (Z_to_bv 64 (sc + 10)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.
End DEQ.


End CANSEC1.
