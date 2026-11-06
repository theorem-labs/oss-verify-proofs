(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_traces RT_gaps_iface Lept_iface LeptC_deser2_defs Lept_deser_defs LeptC_deser0_defs LeptC_deserm1_defs LeptC_deser2 LeptM_deser1_c0 LeptM_deser1_c16 LeptC_deser0 LeptC_deserm1.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_LeptC_deser_tail () := "C69OSSVerify5KrLib2K53A23ALeptC_deser2_defs9deser_ctxC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib2K53A238RT_iface7rt_liveC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z2ltC69OSSVerify5KrLib2K53A238RT_iface9sec_bytesC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leC69OSSVerify5KrLib2K53A23ALeptC_deser2_defs@deser_epi_stmt_0C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2or01K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2or02C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic6or_indC69OSSVerify5KrLib2K53A23<LeptC_deser2?deser_cut2_ok_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23?LeptM_deser1_c0?deser_cut1_ok_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<LeptC_deser0?deser_cut0_ok_0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list02I47Corelib7Numbers7BinNums1Z00C69OSSVerify5KrLib2K53A239RT_tracesADESER_DESTROY_RASC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib2K53A238RT_iface9SEC_BYTESC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23ALeptC_deser2_defsAdeser_epi_stmt_16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<LeptC_deser2@deser_cut2_ok_16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23@LeptM_deser1_c16@deser_cut1_ok_16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<LeptC_deser0@deser_cut0_ok_16C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23@LeptC_deser_tail?deser_tail_ok_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23=LeptC_deserm1@deser_cutm1_ok_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23@LeptC_deser_tail@deser_tail_ok_16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23=LeptC_deserm1Adeser_cutm1_ok_16C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Section TAIL.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis LSE : lept_stderr_cps RT.
Hypothesis RERR : returnError_cps RT e_returnErrorPtr.
Hypothesis HDR : pixCreateHeader_cps RT.
Hypothesis CRE : pixCreate_cps RT.
Hypothesis DES : pixDestroy_cps RT.
Hypothesis CMD : pixcmapDeserialize_cps RT.
Hypothesis SETC : pixSetColormap_cps RT.
Hypothesis VAL : pixcmapIsValid_cps RT.
Variables (Σ : rts RT) (PMc : Model -> Prop) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (usp lo : Z) (m : mem)
          (QF : config -> Prop) (fr : Z) (dp n : Z) (ras : list Z).

Theorem deser_tail_ok_0 :
  (forall rdes, In rdes DESER_DESTROY_RAS -> deser_ctx RT Σ PMc ra s0 usp lo m dp n ras rdes) ->
  (forall p k, In (p, k) (rt_live RT Σ) -> 0 < k) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  deser_epi_stmt_0 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr ->
  deser_cut0_stmt_0 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr dp n.
Proof using AF RC GP LSE RERR HDR CRE DES CMD SETC VAL.
ltac2:(KReplay.run1 (kr_t_LeptC_deser_tail ()) ["TAIL"] "h04rdesh11Hh22H0h32Hrh43CTXh53EPIh63LVPh72R1h83R23h92R4h:4SECBh;1kh<1pp;<p;2p;4p;3p;1p;Fp;6p;Qp;Vp;Sg0000l<QTg0017j2LTg001Wj4ETg0027j2PTg0033j39Tg003Jj2MTg003fj1KTg004dj1;Tg005Bj2CTg005_j2BTg006;lFOTg007Ij22Tg007cj2ATg008=j3<Tg008Wj1JTg0097j37Tg009Qj2GTg00:0j6@Tg00:LlQHTg00;TlVFTg00<_lSITg00=gj14Tg00>Lj1=Tg00?1j3DTg00?Kj3NTg00?kR0f0R1g00@I39p=>%41#4p=3%41#4#4#4p=5%41#=p=1%=1#=p=6%=1#4p=?f1R2=D01p=0g00APR3,21p=:AN021p=8%>1p,2RTR4p,2ΣR5p,3PMcR6p,2raR7p,2s0R8p,3uspR9p,2loR:p,1mR;p,2dpR<p,1nR=p,3rasR>P2M<Q[^001L00P0P0P2P1CE1P45R?39g00Am/M2[^;0^<0%K?g00BKR?#3#5#5#5#5#5#5#;'Cg00C0'BP4P5P6P7p,2gpR@P8p,2s1RAp,2s2RBp,2s3RCp,2s4RDp,2s5REp,2s6RFp,2s7RGp,2s8RHp,2s9RIp,3s10RJp,3s11RKP9P:P;p,2QFRLp,2frRMMFO%1?#1#3#1#6#3#1#?#5#;RN/0N%1?#1#3#1#6#3#6#3#1#3#;RO/0N%1?#1#3#1#6#?#3#6#1#3#;RP/0N%1?#1#3#1#6#?#1#6#1#3#;R?/0N#:'2'21A0N3<%J0RQ,8?,8P,8O,8NRR990Ne%>NRSePS10N?10O?RS10P?RT10??RU#:RV'2RW'21A0?9<U397TV97SW37A90?Re%>?RWePW18PQ,8O9901RQ10O2RW10P2RS#:RV10N210?2#:,2S,2W'2f2RS,0NRT10OSRU10PSRX10?S#:'2RY'2RZA<UY137X1WPXP312TZf3RZ,0NRT10OZRO10PZRP10?Z#:RW'2RY'2RUA<PW197OY37X2X12TU/G1X23P1E@X1VP1E@A902Re%>2RReW3X00PR\Q^00P4p,2AFRRp,2RCRVp,2GPR3p,3LSEp,4RERRRUp,3HDRp,3DESRTP5P6P7P@P8PAPBPCPDPEPFPGPHPIPJPKP9P:P;PLPMP<P=P>f6RXPNPSO2PZP4PRPVP3PUp,3CREPTp,3CMDp,4SETCP5P6P7P@P8PAPBPCPDPEPFPGPHPIPJPKP9P:P;PLPMP<P=P>f8P2PSP2P1O2O2X3QX00f5f4PZP4PRPVP3PUPTp,3VALP5P6P7P@P8PAPBPCPDPEPFPGPHPIPJPKP9P:P;PLPMP<P=P>PXP?P2O2PZMQHMVFMSIb8b9b7W5W:W6W4o"). Qed.

Theorem deser_tail_ok_16 :
  (forall rdes, In rdes DESER_DESTROY_RAS -> deser_ctx RT Σ PMc ra s0 usp lo m dp n ras rdes) ->
  (forall p k, In (p, k) (rt_live RT Σ) -> 0 < k) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  deser_epi_stmt_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr ->
  deser_cut0_stmt_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr dp n.
Proof using AF RC GP LSE RERR HDR CRE DES CMD SETC VAL.
ltac2:(KReplay.run1 (kr_t_LeptC_deser_tail ()) ["TAIL"] "h04rdesh11Hh22H0h32Hrh43CTXh53EPIh63LVPh72R1h83R23h92R4h:4SECBh;1kh<1pp;<p;2p;4p;3p;1p;Fp;6p;Qp;Vp;Sg0000l<QTg0017j2LTg001Wj4ETg0027j2PTg0033j39Tg003Jj2MTg003fj1KTg004dj1;Tg005Bj2CTg005_j2BTg00CnlFOTg007Ij22Tg007cj2ATg008=j3<Tg008Wj1JTg0097j37Tg009Qj2GTg00:0j6@Tg00E=lQHTg00FFlVFTg00GSlSITg00=gj14Tg00>Lj1=Tg00?1j3DTg00?Kj3NTg00?kR0f0R1g00@I39p=>%41#4p=3%41#4#4#4p=5%41#=p=1%=1#=p=6%=1#4p=?f1R2=D01p=0g00APR3,21p=:AN021p=8%>1p,2RTR4p,2ΣR5p,3PMcR6p,2raR7p,2s0R8p,3uspR9p,2loR:p,1mR;p,2dpR<p,1nR=p,3rasR>P2M<Q[^001L00P0P0P2P1CE1P45R?39g00Am/M2[^;0^<0%K?g00BKR?#3#5#5#5#5#5#5#;'Cg00C0'BP4P5P6P7p,2gpR@P8p,2s1RAp,2s2RBp,2s3RCp,2s4RDp,2s5REp,2s6RFp,2s7RGp,2s8RHp,2s9RIp,3s10RJp,3s11RKP9P:P;p,2QFRLp,2frRMMFO%1?#1#3#1#6#3#1#?#5#;RN/0N%1?#1#3#1#6#3#6#3#1#3#;RO/0N%1?#1#3#1#6#?#3#6#1#3#;RP/0N%1?#1#3#1#6#?#1#6#1#3#;R?/0N#:'2'21A0N3<%J0RQ,8?,8P,8O,8NRR990Ne%>NRSePS10N?10O?RS10P?RT10??RU#:RV'2RW'21A0?9<U397TV97SW37A90?Re%>?RWePW18PQ,8O9901RQ10O2RW10P2RS#:RV10N210?2#:,2S,2W'2f2RS,0NRT10OSRU10PSRX10?S#:'2RY'2RZA<UY137X1WPXP312TZf3RZ,0NRT10OZRO10PZRP10?Z#:RW'2RY'2RUA<PW197OY37X2X12TU/G1X23P1E@X1VP1E@A902Re%>2RReW3X00PR\Q^00P4p,2AFRRp,2RCRVp,2GPR3p,3LSEp,4RERRRUp,3HDRp,3DESRTP5P6P7P@P8PAPBPCPDPEPFPGPHPIPJPKP9P:P;PLPMP<P=P>f6RXPNPSO2PZP4PRPVP3PUp,3CREPTp,3CMDp,4SETCP5P6P7P@P8PAPBPCPDPEPFPGPHPIPJPKP9P:P;PLPMP<P=P>f8P2PSP2P1O2O2X3QX00f5f4PZP4PRPVP3PUPTp,3VALP5P6P7P@P8PAPBPCPDPEPFPGPHPIPJPKP9P:P;PLPMP<P=P>PXP?P2O2PZMQHMVFMSIb8b9b7W5W:W6W4o"). Qed.

Theorem deser_front2_ok_0 :
  (forall rdes, In rdes DESER_DESTROY_RAS -> deser_ctx RT Σ PMc ra s0 usp lo m dp n ras rdes) ->
  (forall p k, In (p, k) (rt_live RT Σ) -> 0 < k) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  deser_epi_stmt_0 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr ->
  deser_cutm1_stmt_0 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr dp n.
Proof using AF RC GP LSE RERR HDR CRE DES CMD SETC VAL.
ltac2:(KReplay.run1 (kr_t_LeptC_deser_tail ()) ["TAIL"] "h03CTXh13EPIh23LVPh32R1h44SECBh51kh61ph74rdesp;3p;<p;2p;4p;1p;Fp;Qg0033j39Tg0000l<ITg0017j2ATg001Wj4?Tg0027j2HTg003Jj2GTg003fj1ETg004dj15Tg005Bj2>Tg005_j2=Tg006;lF<Tg00?1j36Tg007Ij2:Tg007cj2FTg008=j3DTg008Wj1BTg00?Kj38Tg00H\j4@Tg00IhlQCTg00=gj12Tg00>Lj17Tf0R0#2#2p=1%20#2#2#2p=3%20#7p=0%70#7p=4%70#2p=;g00?kR1g00@IR29910p,2RTR3p,2ΣR4p,3PMcR5p,2raR6p,2s0R7p,3uspR8p,2loR9p,1mR:p,2dpR;p,1nR<p,3rasR=f1R>M<I[]71A11P1P1P>P0C?1H34R?39g00Am/G>[^51^61%E?g00BKR?#1#3#3#3#3#3#3#5'>g00C0'=P3P4P5P6p,2gpR@P7p,2s1RAp,2s2RBp,2s3RCp,2s4RDp,2s5REp,2s6RFp,2s7RGp,2s8RHp,2s9RIp,3s10RJp,3s11RKP8P9P:p,2QFRLp,2frRMMF<%0?#0#1#0#4#1#0#;#3#5RN=61N%0?#0#1#0#4#1#4#1#0#1#5RO=61N%0?#0#1#0#4#;#1#4#0#1#5RP=61N%0?#0#1#0#4#;#0#4#0#1#5R?=61Ng00AP':':':1F1N3D%B1981?981P981O981N991NeA91N2R2eP2P3p,2AFp,2RCp,2GPp,4RERRP4P5P6P@P7PAPBPCPDPEPFPGPHPIPJPKP8P9P:PLPMP;P<P=PNf4R=PNP0O2P>P=f3f2P>C@MQCb3W1W4W2W0o"). Qed.

Theorem deser_front2_ok_16 :
  (forall rdes, In rdes DESER_DESTROY_RAS -> deser_ctx RT Σ PMc ra s0 usp lo m dp n ras rdes) ->
  (forall p k, In (p, k) (rt_live RT Σ) -> 0 < k) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  deser_epi_stmt_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr ->
  deser_cutm1_stmt_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr dp n.
Proof using AF RC GP LSE RERR HDR CRE DES CMD SETC VAL.
ltac2:(KReplay.run1 (kr_t_LeptC_deser_tail ()) ["TAIL"] "h03CTXh13EPIh23LVPh32R1h44SECBh51kh61ph74rdesp;3p;<p;2p;4p;1p;Fp;Qg0033j39Tg0000l<ITg0017j2ATg001Wj4?Tg0027j2HTg003Jj2GTg003fj1ETg004dj15Tg005Bj2>Tg005_j2=Tg00CnlF<Tg00?1j36Tg007Ij2:Tg007cj2FTg008=j3DTg008Wj1BTg00?Kj38Tg00K2j4@Tg00L?lQCTg00=gj12Tg00>Lj17Tf0R0#2#2p=1%20#2#2#2p=3%20#7p=0%70#7p=4%70#2p=;g00?kR1g00@IR29910p,2RTR3p,2ΣR4p,3PMcR5p,2raR6p,2s0R7p,3uspR8p,2loR9p,1mR:p,2dpR;p,1nR<p,3rasR=f1R>M<I[]71A11P1P1P>P0C?1H34R?39g00Am/G>[^51^61%E?g00BKR?#1#3#3#3#3#3#3#5'>g00C0'=P3P4P5P6p,2gpR@P7p,2s1RAp,2s2RBp,2s3RCp,2s4RDp,2s5REp,2s6RFp,2s7RGp,2s8RHp,2s9RIp,3s10RJp,3s11RKP8P9P:p,2QFRLp,2frRMMF<%0?#0#1#0#4#1#0#;#3#5RN=61N%0?#0#1#0#4#1#4#1#0#1#5RO=61N%0?#0#1#0#4#;#1#4#0#1#5RP=61N%0?#0#1#0#4#;#0#4#0#1#5R?=61Ng00AP':':':1F1N3D%B1981?981P981O981N991NeA91N2R2eP2P3p,2AFp,2RCp,2GPp,4RERRP4P5P6P@P7PAPBPCPDPEPFPGPHPIPJPKP8P9P:PLPMP;P<P=PNf4R=PNP0O2P>P=f3f2P>C@MQCb3W1W4W2W0o"). Qed.
End TAIL.
