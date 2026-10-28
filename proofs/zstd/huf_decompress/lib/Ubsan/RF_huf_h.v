(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas FuzzProducer HufHarness.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import Stdio_pure.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg StdioFiles.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_facts.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RF_huf_h_iface RF_huf_iface_m RF_huf_h_kit RF_huf_h_lib RF_huf_h_split RF_huf_h_asm1 RF_huf_h_asm2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad Stdio Malloc Harness Prog.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_h () := "C5ARocqVerifyHarness?AgentSubmission4Spec6Malloc4aptrC5ARocqVerifyHarness?AgentSubmission4Spec5Monad5implMC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc4optrK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface5RHEAPC45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib5Lists7ListDef6Forall00C45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission4Spec6Prelim7zlengthC5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface=rclient_rangeC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC56Stdlib6ZArith6BinInt1Z3powC5ARocqVerifyHarness?AgentSubmission5Ubsan=Harness_iface=harness_cellsC5ARocqVerifyHarness?AgentSubmission5Ubsan=Harness_iface<stderr_file0C5ARocqVerifyHarness?AgentSubmission5Ubsan;RMallocTree8rauxv_okC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC56Stdlib6ZArith6BinInt1Z3subK47Corelib7Numbers7BinNums1Z03K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib2FP4frm0C5ARocqVerifyHarness?AgentSubmission6Malloc9MallocRep2wzC5ARocqVerifyHarness?AgentSubmission4Spec4Prog8fuzz_oneC5ARocqVerifyHarness?AgentSubmission5Ubsan=Harness_iface=fuzz_one_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_split8hM_stateC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_h_asm29fz_secondC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_h_asm18fz_firstC47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission5Ubsan=Harness_iface=fuzz_one_stmtK47Corelib7Numbers7BinNums8positive03I5ARocqVerifyHarness?AgentSubmission4Spec6PState6PState00C5ARocqVerifyHarness?AgentSubmission6Malloc<MallocBlocks5blockI47Corelib7Numbers7BinNums1Z00C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsK47Corelib7Numbers7BinNums1Z01C5ARocqVerifyHarness?AgentSubmission5Ubsan=Harness_iface=HARNESS_STACKI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep4RATPC5ARocqVerifyHarness?AgentSubmission5Ubsan=Harness_iface;PFUZZ_ENTRYC5ARocqVerifyHarness?AgentSubmission6Malloc8ProgDeps4bptrI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section CANSEC1. Context {rc : runConstT}.
Section FuzzOne.
  Variable dt_ok : (word -> option byte) -> Z -> Z -> Prop.
  Hypothesis CREATE : prod_create_stmt.
  Hypothesis FMALLOC : fuzz_malloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis PFREE : prod_free_stmt.
  Hypothesis U32R : prod_u32r_stmt.
  Hypothesis I32R : prod_i32r_stmt.
  Hypothesis RDT1 : huf_rdt_stmt dt_ok PHUF_RDT_X1.
  Hypothesis RDT2 : huf_rdt_stmt dt_ok PHUF_RDT_X2.
  Hypothesis DEC1 : huf_dec_stmt dt_ok PHUF_DEC_1X.
  Hypothesis DEC4 : huf_dec_stmt dt_ok PHUF_DEC_4X.

  Theorem fuzz_one_proof : fuzz_one_stmt.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_h ()) ["CANSEC1"; "FuzzOne"] "h03ERRh13TP'h22tph32A0h42A1h52ABh64AB47h73AUXh81Dh92D0h:3D16h;4DTOPh<1Fh=2FCh>2HCh?2HMh@2HPhA2LBhB3LOAhC3LOShD2MIhE3PAYhF4PAYBhG4PAYRhH2SEhI4SP16hJ3SPBhK2SThL2SZhM2TPhN2a0hO2a1hP2a2hQ2a3hR2a4hS2a5hT2a6hU2a7hV1chW4dBufhX2dthY4errvhZ2fch[2gph\2loh]1mh^3ms'h_7payloadh`8producerha2rahb1shc2s'hd2s0he2s1hf3s10hg3s11hh2s2hi2s3hj2s4hk2s5hl2s6hm2s7hn2s8ho2s9hp2sphq2t0hr2t1hs2t2ht2t3hu2t4hv2t5hw2t6hx4wkspp;1p;2p;4p;3p;Fp;Op;7p;cp;rp;8p10000p4p70g000eR0p4p710R1p8p1001Zp4p70P1p8g002Oj10Tg0034j19Tg003Rj1=Tg0045j13Tg004Zj2aTg005Fj1CTg005hj1ATg006Hj4RTg007Fj1Nj2DTg007lj4HTg008Hj4GTg009=j24Tg009Yj15Tg00:7j2>Tg00:Sj2]Tg00:nj3VTg00;Oj22Tg00<9j28Tg00=1j4TTg00>7j2@Tg00>Wj31Tg00?1j26Tg00?Nj1QTg00@Dj2?Tg00@aj1PTg00Agj1MTg00Blj3LTg00Ckj4KTg00D]j2ITg00E:j1JTg00EXj1:Tg00FMj1FTg00Fmj3<Tg00GMj4;Tg00HCj2ETg00I7j1OTg00Igj17Tg00J_j1STg00KVlFBTg00L\lO`Tg00MNj1_Tg00N0j1^Tg00Nij7\TP0j7WTg00O[lOXTg00P]lcYTg00Q_lrZTg00R`j8[Tg00S>j1UTg00TDR0#0R1#0#0R2#0R3#0R4#0R5#9R6#=R7%31R8#9/a7%94#=%92R2#=R4#C\7g00TiR9g00Ub#Ag00V`R:%A:p,2rcR;f6R<f5R=f7R>CRg00W>R?f8R@P=P:P4%N2f4R2CHCGg00X3R4f0RA'4%05#0#5,>A']XV:=V:=P@fZR5,26P>18:<CT%53R3,@@=1:4f9RB,>4f:RC18:B'6%Q;RB'418:C%51R1%30#0#3#0#5'?'>f?R0#Pf@RD#MfAREf<RF5L;fbRG,26f='4f>RH%38#3#3#5,?1'4P?fDR1PHfdRI,26CK14B0ffRB,26g00XQ'I,4DP?fGRJfeRK,26%08#0#3#0#0#JR8'6g00YWRL%:D%FLRD3<C;fHRM,E?fJRN#OfhROg00ZLRP#7RQ517fkRR,26/@3=1:4fIR4#7917I18:4#7917If3R3flRS=17QP7PQP?fPRT126A/68%:4=<LDC;f1RU1D6PRP517P9P?P:fNRV#SfQRWP;fsRXfrRYfqRZf2R[PSPRPGfaR\f`R]f_R^f^R_f]R`f\Raf[RbP5fYRcPWPTfMRdfLRefRRfMFBPXPYPZP[fofnRXfmRgPSPRfjRhfiRiPOfgRjPBPKPIfcRkPGP\P]P^P_P`PaPbP5PcfXRlfWRmfVRnfURoMO`fTRpg00[F#7fSRq%_7Pf%^?F\FW]1]0X27P?fOR?126Q/68%:M=<LDC;A17QPP;p,6CREATEp,7FMALLOCp,4U32Rp,4I32RPYPZfpRPPQPXPgPSPRPhPiPOPjPBPKPIPkPGP\P]P^P_P`PaPbP5PcPlPmPnPoPpPqPfPWPTP?PVPdPefKRiPNP;PYPZPPPQPRPhP\P]P^P_P`PaPbP5PcPlPTP?PePiPWMFBP4PMPJfFP1fCfBRJP0PHPFf;PCPUP@PAP=P2P3g00\J#CR@g00]CP;fxRCfwR0fvPZPPPjPBPKPIPkPGP\P]P^P_PcPlPnPoPfPWPpPqPmP=P2P3P[PUPAMOXP;p,5dt_okp,4RDT1p,4RDT2p,4DEC1p,4DEC4p,4FREEp,5PFREEfyPCP0PYPZPOPjPBPKPIPkPGP\P]P^P5PcPlPmPnPoPpPqPfP<P=P2P3P[PUPVPdPePiPNP4fEP1PJPEPHPFPAMcYW?W^Xc9XW@Xx@XX@W`MrZW1W0PgP2P>PAG[b1W4W3WIWMW=WDW0WCWBWKW6WJW7WHW>WLW;W9W:WGWFWEW@XY7X\:X5:W_W8WAWbW]WZW<Xw7Xv7Xu7Xt7Xg7Xf7Xo7Xn7Xm7Xl7Xk7Xj7Xi7Xh7XU7XT7XS7XR7XQ7XP7XO7XN7Xe7Xd7Xs7Xr7Xq7X27X[7Xp7Wa%U;eo"). Qed.
End FuzzOne.
End CANSEC1.
