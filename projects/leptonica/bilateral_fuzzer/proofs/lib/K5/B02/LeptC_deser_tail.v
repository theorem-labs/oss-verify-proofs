(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_traces RT_gaps_iface Lept_iface LeptC_deser2_defs Lept_deser_defs LeptC_deser0_defs LeptC_deserm1_defs LeptC_deser2 LeptM_deser1_c0 LeptM_deser1_c16 LeptC_deser0 LeptC_deserm1.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_LeptC_deser_tail () := "C69OSSVerify5KrLib2K53B02ALeptC_deser2_defs9deser_ctxC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib2K53B028RT_iface7rt_liveC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z2ltC69OSSVerify5KrLib2K53B028RT_iface9sec_bytesC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leC69OSSVerify5KrLib2K53B02ALeptC_deser2_defs@deser_epi_stmt_0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2or01K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2or02C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic6or_indC69OSSVerify5KrLib2K53B02<LeptC_deser2?deser_cut2_ok_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02?LeptM_deser1_c0?deser_cut1_ok_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<LeptC_deser0?deser_cut0_ok_0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list02I47Corelib7Numbers7BinNums1Z00C69OSSVerify5KrLib2K53B029RT_tracesADESER_DESTROY_RASC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib2K53B028RT_iface9SEC_BYTESC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02ALeptC_deser2_defsAdeser_epi_stmt_16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<LeptC_deser2@deser_cut2_ok_16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02@LeptM_deser1_c16@deser_cut1_ok_16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<LeptC_deser0@deser_cut0_ok_16C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02@LeptC_deser_tail?deser_tail_ok_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02=LeptC_deserm1@deser_cutm1_ok_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02@LeptC_deser_tail@deser_tail_ok_16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02=LeptC_deserm1Adeser_cutm1_ok_16C1?~~~~~~~~~~~~~~~".
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
ltac2:(KReplay.run1 (kr_t_LeptC_deser_tail ()) ["TAIL"] "h04rdesh11Hh22H0h32Hrh43CTXh53EPIh63LVPh72R1h83R23h92R4h:4SECBh;1kh<1pp;<p;2p;4p;3p;1p;Fp;6p;Qp;Vp;Sg0000l<RTg0017j2KTg001Wj4FTg0027j2QTg0033j37Tg003Jj2MTg003fj1JTg004dj1;Tg005Bj2DTg005_j2CTg006;lFPTg007Ij13Tg007nj21Tg008Hj2BTg008bj3?Tg009<j1ITg009\j36Tg00:6j2HTg00:Uj6ATg00;1lQGTg00<9lVLTg00=DlSETg00>Lj12Tg00?1j3NTg00?Kj3OTg00?kR0f0R1g00@I37p=@%21#2p=:%21#2#2#2p=4%31#2p=>%31#3#2#2p=<%21#3p==%31#3p=8f1R2=N01p=0g00APR3,11p=5AO021p=9%@1p,2RTR4p,2ΣR5p,3PMcR6p,2raR7p,2s0R8p,3uspR9p,2loR:p,1mR;p,2dpR<p,1nR=p,3rasR>P2M<R[^001K00P0P0P2P1CF1Q45R?37g00Am/M2[^;0^<0%J?g00BKR?#:#4#4#4#4#4#4#;'Dg00C0'CP4P5P6P7p,2gpR@P8p,2s1RAp,2s2RBp,2s3RCp,2s4RDp,2s5REp,2s6RFp,2s7RGp,2s8RHp,2s9RIp,3s10RJp,3s11RKP9P:P;p,2QFRLp,2frRMMFP%3?#:#>#<#=#=#8#4#;RN/0N%3?#:#>#<#=#8#=#<#;RO/0N%3?#:#>#<#8#=#8#4#;RP/0N%3?#:#>#<#8#>#8#4#;R?/0N#5'1'11B0N3?%I0RQ,9?,9P,9O,9NRR970Ne%@NRSePS10N?10O?RS10P?RT10??RU#5RV'1RW'11B0?9?U396TV96SW36A70?Re%@?RWePW19PQ,9O9701RQ10O2RW10P2RS#5RV10N210?2#5,1S,1W'1f2RS,0NRT10OSRU10PSRX10?S#5'1RY'1RZA?UY136X1WPXP311TZf3RZ,0NRT10OZRO10PZRP10?Z#5RW'1RY'1RUA?PW196OY36X2X11TU/H1X23P1EAX1VP1EAA702Re%@2RReW3X00PR\Q^00P4p,2AFRRp,2RCRVp,2GPR3p,3LSEp,4RERRRUp,3HDRp,3DESRTP5P6P7P@P8PAPBPCPDPEPFPGPHPIPJPKP9P:P;PLPMP<P=P>f6RXPNPSO2PZP4PRPVP3PUp,3CREPTp,3CMDp,4SETCP5P6P7P@P8PAPBPCPDPEPFPGPHPIPJPKP9P:P;PLPMP<P=P>f8P2PSP2P1O2O2X3QX00f5f4PZP4PRPVP3PUPTp,3VALP5P6P7P@P8PAPBPCPDPEPFPGPHPIPJPKP9P:P;PLPMP<P=P>PXP?P2O2PZMQGMVLMSEb8b9b7W5W:W6W4o"). Qed.

Theorem deser_tail_ok_16 :
  (forall rdes, In rdes DESER_DESTROY_RAS -> deser_ctx RT Σ PMc ra s0 usp lo m dp n ras rdes) ->
  (forall p k, In (p, k) (rt_live RT Σ) -> 0 < k) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  deser_epi_stmt_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr ->
  deser_cut0_stmt_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr dp n.
Proof using AF RC GP LSE RERR HDR CRE DES CMD SETC VAL.
ltac2:(KReplay.run1 (kr_t_LeptC_deser_tail ()) ["TAIL"] "h04rdesh11Hh22H0h32Hrh43CTXh53EPIh63LVPh72R1h83R23h92R4h:4SECBh;1kh<1pp;<p;2p;4p;3p;1p;Fp;6p;Qp;Vp;Sg0000l<RTg0017j2KTg001Wj4FTg0027j2QTg0033j37Tg003Jj2MTg003fj1JTg004dj1;Tg005Bj2DTg005_j2CTg00CnlFPTg007Ij13Tg007nj21Tg008Hj2BTg008bj3?Tg009<j1ITg009\j36Tg00:6j2HTg00:Uj6ATg00E=lQGTg00FFlVLTg00GSlSETg00>Lj12Tg00?1j3NTg00?Kj3OTg00?kR0f0R1g00@I37p=@%21#2p=:%21#2#2#2p=4%31#2p=>%31#3#2#2p=<%21#3p==%31#3p=8f1R2=N01p=0g00APR3,11p=5AO021p=9%@1p,2RTR4p,2ΣR5p,3PMcR6p,2raR7p,2s0R8p,3uspR9p,2loR:p,1mR;p,2dpR<p,1nR=p,3rasR>P2M<R[^001K00P0P0P2P1CF1Q45R?37g00Am/M2[^;0^<0%J?g00BKR?#:#4#4#4#4#4#4#;'Dg00C0'CP4P5P6P7p,2gpR@P8p,2s1RAp,2s2RBp,2s3RCp,2s4RDp,2s5REp,2s6RFp,2s7RGp,2s8RHp,2s9RIp,3s10RJp,3s11RKP9P:P;p,2QFRLp,2frRMMFP%3?#:#>#<#=#=#8#4#;RN/0N%3?#:#>#<#=#8#=#<#;RO/0N%3?#:#>#<#8#=#8#4#;RP/0N%3?#:#>#<#8#>#8#4#;R?/0N#5'1'11B0N3?%I0RQ,9?,9P,9O,9NRR970Ne%@NRSePS10N?10O?RS10P?RT10??RU#5RV'1RW'11B0?9?U396TV96SW36A70?Re%@?RWePW19PQ,9O9701RQ10O2RW10P2RS#5RV10N210?2#5,1S,1W'1f2RS,0NRT10OSRU10PSRX10?S#5'1RY'1RZA?UY136X1WPXP311TZf3RZ,0NRT10OZRO10PZRP10?Z#5RW'1RY'1RUA?PW196OY36X2X11TU/H1X23P1EAX1VP1EAA702Re%@2RReW3X00PR\Q^00P4p,2AFRRp,2RCRVp,2GPR3p,3LSEp,4RERRRUp,3HDRp,3DESRTP5P6P7P@P8PAPBPCPDPEPFPGPHPIPJPKP9P:P;PLPMP<P=P>f6RXPNPSO2PZP4PRPVP3PUp,3CREPTp,3CMDp,4SETCP5P6P7P@P8PAPBPCPDPEPFPGPHPIPJPKP9P:P;PLPMP<P=P>f8P2PSP2P1O2O2X3QX00f5f4PZP4PRPVP3PUPTp,3VALP5P6P7P@P8PAPBPCPDPEPFPGPHPIPJPKP9P:P;PLPMP<P=P>PXP?P2O2PZMQGMVLMSEb8b9b7W5W:W6W4o"). Qed.

Theorem deser_front2_ok_0 :
  (forall rdes, In rdes DESER_DESTROY_RAS -> deser_ctx RT Σ PMc ra s0 usp lo m dp n ras rdes) ->
  (forall p k, In (p, k) (rt_live RT Σ) -> 0 < k) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  deser_epi_stmt_0 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr ->
  deser_cutm1_stmt_0 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr dp n.
Proof using AF RC GP LSE RERR HDR CRE DES CMD SETC VAL.
ltac2:(KReplay.run1 (kr_t_LeptC_deser_tail ()) ["TAIL"] "h03CTXh13EPIh23LVPh32R1h44SECBh51kh61ph74rdesp;3p;<p;2p;4p;1p;Fp;Qg0033j3;Tg0000l<JTg0017j2CTg001Wj4@Tg0027j2ITg003Jj2HTg003fj1GTg004dj16Tg005Bj2?Tg005_j2>Tg006;lF=Tg007Ij11Tg00?1j3:Tg007nj2<Tg008Hj2FTg008bj3ETg009<j1BTg00?Kj39Tg00H\j4DTg00IhlQATg00>Lj10Tf0R0#0#0p=5%00#0#0#0p=2%10#0p=7%10#1#0#0p=8%00#1p=4%10#1p=3g00?kR1g00@IR29;10p,2RTR3p,2ΣR4p,3PMcR5p,2raR6p,2s0R7p,3uspR8p,2loR9p,1mR:p,2dpR;p,1nR<p,3rasR=f1R>M<J[]71C11P1P1P>P0C@1I34R?3;g00Am/H>[^51^61%G?g00BKR?#5#2#2#2#2#2#2#6'?g00C0'>P3P4P5P6p,2gpR@P7p,2s1RAp,2s2RBp,2s3RCp,2s4RDp,2s5REp,2s6RFp,2s7RGp,2s8RHp,2s9RIp,3s10RJp,3s11RKP8P9P:p,2QFRLp,2frRMMF=%1?#5#7#8#4#4#3#2#6RN=:1N%1?#5#7#8#4#3#4#8#6RO=:1N%1?#5#7#8#3#4#3#2#6RP=:1N%1?#5#7#8#3#7#3#2#6R?=:1Ng00AP'<'<'<1F1N3E%B1991?991P991O991N9;1NeA;1N2R2eP2P3p,2AFp,2RCp,2GPp,4RERRP4P5P6P@P7PAPBPCPDPEPFPGPHPIPJPKP8P9P:PLPMP;P<P=PNf4R=PNP0O2P>P=f3f2P>CDMQAb3W1W4W2W0o"). Qed.

Theorem deser_front2_ok_16 :
  (forall rdes, In rdes DESER_DESTROY_RAS -> deser_ctx RT Σ PMc ra s0 usp lo m dp n ras rdes) ->
  (forall p k, In (p, k) (rt_live RT Σ) -> 0 < k) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  deser_epi_stmt_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr ->
  deser_cutm1_stmt_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m QF fr dp n.
Proof using AF RC GP LSE RERR HDR CRE DES CMD SETC VAL.
ltac2:(KReplay.run1 (kr_t_LeptC_deser_tail ()) ["TAIL"] "h03CTXh13EPIh23LVPh32R1h44SECBh51kh61ph74rdesp;3p;<p;2p;4p;1p;Fp;Qg0033j3;Tg0000l<JTg0017j2CTg001Wj4@Tg0027j2ITg003Jj2HTg003fj1GTg004dj16Tg005Bj2?Tg005_j2>Tg00CnlF=Tg007Ij11Tg00?1j3:Tg007nj2<Tg008Hj2FTg008bj3ETg009<j1BTg00?Kj39Tg00K2j4DTg00L?lQATg00>Lj10Tf0R0#0#0p=5%00#0#0#0p=2%10#0p=7%10#1#0#0p=8%00#1p=4%10#1p=3g00?kR1g00@IR29;10p,2RTR3p,2ΣR4p,3PMcR5p,2raR6p,2s0R7p,3uspR8p,2loR9p,1mR:p,2dpR;p,1nR<p,3rasR=f1R>M<J[]71C11P1P1P>P0C@1I34R?3;g00Am/H>[^51^61%G?g00BKR?#5#2#2#2#2#2#2#6'?g00C0'>P3P4P5P6p,2gpR@P7p,2s1RAp,2s2RBp,2s3RCp,2s4RDp,2s5REp,2s6RFp,2s7RGp,2s8RHp,2s9RIp,3s10RJp,3s11RKP8P9P:p,2QFRLp,2frRMMF=%1?#5#7#8#4#4#3#2#6RN=:1N%1?#5#7#8#4#3#4#8#6RO=:1N%1?#5#7#8#3#4#3#2#6RP=:1N%1?#5#7#8#3#7#3#2#6R?=:1Ng00AP'<'<'<1F1N3E%B1991?991P991O991N9;1NeA;1N2R2eP2P3p,2AFp,2RCp,2GPp,4RERRP4P5P6P@P7PAPBPCPDPEPFPGPHPIPJPKP8P9P:PLPMP;P<P=PNf4R=PNP0O2P>P=f3f2P>CDMQAb3W1W4W2W0o"). Qed.
End TAIL.
