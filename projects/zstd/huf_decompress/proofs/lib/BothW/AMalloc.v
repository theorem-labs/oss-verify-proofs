(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto ABase AMalloc_iface ADepot_iface APoisonR_iface ARep AHeapP ASec
     F_amalloc_arep AMallocPG AMallocS.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AMalloc () := "I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed6aembedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA5implFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA6epostFC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib5BothW4ASec7ASEC_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>F_amalloc_arep2AHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP7AHEAP_PC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00C59OSSVerify5KrLib5BothW=AMalloc_iface4aunwC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface8aresv_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:is_primaryC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib4LibA6NodesA8at_nodeAC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7amallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface<amalloc_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AMallocPG<amalloc_primC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8AMallocS;amalloc_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface<amalloc_stmtC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase7alayout00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase6ablock00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase=AMALLOC_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase3ATPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AREQMAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase:AMALLOC_PCC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AProto6fstepSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase;AMALLOC_SYMC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02".
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section S.
Variable DI : ADepotIface.
Variables (AQ : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC_of AFK).
Hypothesis PR : poison_remap_stmt.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Theorem amalloc_all : amalloc_stmt CI (AHEAP_P (AH DI AQ ASEC_of AFK)).
Proof.
ltac2:(KReplay.run1 (kr_t_AMalloc ()) ["CANSEC1"; "S"] "p'0h01Ph11Fh21Lh32LBh44RESVh53RNGh62a0h72a1h82a2h92a3h:2a4h;2a5h<2a6h=2a7h>1bi001bh?2fch@2gphA2lohB1mhC1nhD2rahE2s0hF2s1hG3s10hH3s11hI2s2hJ2s3hK2s4hL2s5hM2s6hN2s7hO2s8hP2s9hQ2sphR2sthS2t0hT2t1hU2t2hV2t3hW2t4hX2t5hY2t6hZ2tph[2trp;1p;2p;5p;7p;4p;3p;9p;Lp;Op;sp-1R0p10000p4p710p8P0p1000QR1p4p710p8P0P1p4p7210p8g000nR1p4p70R0g001eR2p4p7210p8P0g002_R3p4p7511110p8P0g003UR0p4p710p8g004Lj10Tg0051j16Tg005Oj17Tg0062j1BTg006Wj2[Tg007Cj1>Tg007ej18Tg008Ej2<Tg008ej1DTg009\j5CTg00:Xj7Aj2NTg00;Qj2@Tg00<Ej22Tg00<oj4ZTg00=aj1UTg00>Wj14Tg00?5j2=Tg00?Rj23Tg00?nj2:Tg00@Kj29Tg00A1j31Tg00AKj2RTg00Afl9FTg00Bcj1;Tg00C<j2ETg00C\j3GTg00DOj2HTg00EPj15Tg00FMj2ITg00Fgj1JTg00G`j1KTg00HXj4LTP2j3MTg00IRlLOTP0j2PTg00JWlOQTg00KIj1?Tg00Kkj1STg00Ldj7TTP3l9YTg00MVlsXTg00NWlsWTg00OVj3VTg00P[g00QUg00RNR3#0R0#0#0R2#0R4#0R5#0R6#6R7#7R8%B0#6/[8%65#7%62#7#>\8g00S3R5g00Sn#8g00TgR0%801<00#8p,2rcR9P9p,2DIR:p,2AQR;%D9R<p,3AFKR=DCR>fYR?fXR@f5RAf4RBf6RCFAg00UERDf7RE'@PDf8RFPB127@CZ%U9RG%06#0#0#0#0#0#4R6'=/3AfZRH,27g00V:':,3Cg00W8,97918?fTRIf9RJ,97518%43f:R3'3g00Wl,33'Rf>RKfaRLf`RMP3g00XdRNf^ROP@f_RPPJM9F127?127P%42'=510#;127L,36fbR6,27R2=10N#;%44,E2g00Y_510feR2f?R4fcRN,27/:43GfgRQ/HKfBRR#5g00Z=RSf0RT,ISfCRU#5=1STPSfERV#5=1STg00Z]PD%JDg00[R%>1,<5R5#KfkR1PGPUfHRWfFRXCL9MG5P9p,2CIRG1N9>R>flP1fjRYfiRZfhR[PQPNP6P?P@fWR\fVR]fUR^PIfSR_fRR`fQRafPRbfKRcfJRdPWfGRePXPVfIRfMLO,P5PYPZP[PQffR5P2fdRgPNP6PLPMPPPOf]Rhf\Rif[RjPHP?P@P\P]P^PIP_P`PaPbfORkfNRlfMRmfLRnMOQPcg00\J,97Pd%?8Pf%SDFTM9Y]0f1fDRD#5R7g00]F51SP9P:P;P<P=p,2HLR<PGp,5CI_OKRop,6CI_OK2RpP1PYPZP[PQP5P2PgPNP6PLPMPPPOPhPiPjPHP?P@P\P]P^PIP_P`PaPbPkPlPmPnPcPdPfPWPePXPVPDPUPRPTfARqf@RrP4PKf=Rsf<Rtf;RuP3PJPFPEPCPAPBf3RvMsXW0g00]f91S7P9P:P;P=P<p,2PRPGPoPpP1PYPZP[PQP5P2PgPNP6PLPMPPPOPhPiPjPHP?P@P\P]P^PIP_P`PaPbPkPlPmPnPcPdPfPWPePXPVPDPUPRPTPqPrP4PKPsPtPuP3PJPFPEPCPAPBPvMsWW0n0110000020000PTO1b0b>UUUUUUUUUUUUUUUW4W[XA0WCW3WRWBW?W1XY8XX8XW8XV8XH8XG8XP8XO8XN8XM8XL8XK8XJ8XI8X=8X<8X;8X:8X98X88X78X68XF8XE8XU8XT8XS8XZ8X@8XQ8WDW5W2AV9G>eo"). Qed.
End S.
End CANSEC1.
