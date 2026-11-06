(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseWalkKit FseWalkMem HufWalkKit HufWalkKit2 HufWalkKit3.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require KXTac KXGoM.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_fa_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_fa_iface AF_huf_w4s_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AF_huf_z4m AF_huf_w4m AF_huf_w4sb AF_huf_w4skx.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AF_huf_w4s0 AF_huf_w4s01 AF_huf_w4s02 AF_huf_w4s03 AF_huf_w4s04 AF_huf_w4s12_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_w4s0f () := "C46Stdlib5Lists4List2hdC59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<AF_huf_w4s04:w4s04_mainC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C45stdpp9bitvector;definitions7Z_to_bvK59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulK47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib5AsanW;AF_huf_w4sb4W4SFC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib5AsanW;AF_huf_w4sb3HDIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<AH_huf_iface=huf_dec_postAC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF4evtFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<AF_huf_w4s03;w4s03_entryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<AF_huf_w4s02;w4s02_entryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<AF_huf_w4s019w4s01_bigC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<AF_huf_w4s01;w4s01_smallC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib5AsanW;AF_huf_w4s0:w4s0_entryC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic3and00I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib5AsanW4AImg5asegsC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.
Section W4S0F.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock) (rng_fs : alayout -> footprint -> Prop).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX1) (cbs : list byte) (pdt : aptr)
            (SBL SBH : Z) (rstk : region).
  Notation SP := (bv_unsigned sp).
  Notation SPF := (SP + -496).
  Notation n := (zlen src).
  Notation seg := ((dcap + 3) / 4).
  Notation DTL := (DTABLE_BYTES mtl).
  Hypothesis AH : AHEAP AI L RNG st LB m0.
  Hypothesis NFK : forall F k, ~ In (mkABlock (ABFake 0) F k) LB.
  Hypothesis ABL : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b).
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TLM : tl <= mtl + 1.
  Hypothesis HDT : In (HB pdt DT DTL) LB.
  Hypothesis TOK : x1_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (2 * 2^tl)) (x1_bytes cells).
  Hypothesis LCB : zlen cbs = 2 * 2^tl.
  Hypothesis DSTF : (DST = 0 /\ dcap = 0) \/ (exists pb, In (HB pb DST dcap) LB).
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis NSM : n < 2^26.
  Hypothesis S16 : 16 <= SS.
  Hypothesis SRCB : 0 < n -> exists p, In (HB p SBL (SBH - SBL)) LB /\ SBL <= SS /\ SS + n <= SBH.
  Hypothesis DJ1 : DT + DTL <= SS \/ SS + n <= DT.
  Hypothesis DJ2 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis DJ3 : DT + DTL <= DST \/ DST + dcap <= DT.
  Hypothesis LOA : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= SP - HUF_DEC_STACK_A.
  Hypothesis SPT : SP + 16 < al_top L.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis TPA : tp = Z_to_bv 64 ATP.
  Hypothesis HINV : harness_invA m0.
  Hypothesis RCL : rclean m0 rstk.
  Hypothesis RLO : r_lo rstk <= lo.
  Hypothesis RHI : SP <= r_hi rstk.
  Hypothesis RRL : ATOP <= r_rlo rstk.
  Hypothesis RRS : rrng RNG rstk.
  Hypothesis WSK : rng RNG lo (al_top L - lo).
  Hypothesis WIM : rng_aimg RNG.
  Hypothesis WIS : rng_aimg_sh RNG.
  Hypothesis WFS : rng_fs L RNG.

  Notation DW := [(lo, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation WB l := (l AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src
                      cells cbs pdt SBL SBH rstk AH NFK ABL MTL TLM HDT TOK ECB LCB DSTF DC BYS NSM S16 SRCB DJ1 DJ2 DJ3
                      LOA LOS SPT SP16 TPA HINV RCL RLO RHI RRL RRS WSK WIM WIS WFS).
  Notation W4S := (AF_huf_w4s_iface.W4S ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs).

  Hypothesis LOOP : w4s1_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
                      src cbs.
  Hypothesis S2G : w4s2_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
                      src cbs.

  Lemma w4s0_slow : w4_slow_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT
                      mtl tl lo src cbs.
Proof using All.
ltac2:(KReplay.run1 (kr_t_AF_huf_w4s0f ()) ["CANSEC1"; "W4S0F"] "h02LLh12a7h24j112h34j120h44j128h54j144h64j152h73j16h84j160h94j168h:4j176h;4j184h<4j192h=3j40h>3j48h?3j56h@3j64hA3j72hB2j8hC3j80hD3j88hE2jbhF2l1hG2l2hH2l3hI2mmhJ2t0hK2t2hL4j216hM3x22hN3x24hO2a2hP2a6hQ2b1hR2c1hS2j0hT4j104hU4j200hV4j208hW4j224hX3j96hY3pa1hZ2t1h[3x25h\2a1h]2a4h^2a5h_2b2h`2c2ha4j232hb3j32hc3pa2hd3x26he3x27hf2C2hg2C3hh2C4hi2HBhj2HShk2a0hl2b3hm2c3hn3pa3p%0p%1p;{p;1p;2p;Lp;3p;Op;7p;4p;zp-1p10000p4p710R0p8p1000Gp4p70P0p8g001>l{fTg002@j14Tg002ej1TTg003Cj1VTg003fj1^Tg004Hj1[Tg004hj20Tg005Nj16Tg006Cj21Tg0078j1@Tg007]j1ATg008;j23Tg008Xj2dTg0095j2QTg009Rj1\Tg00:2lLKTg00:mj28Tg00;Ij2ZTg00;ij1YTg00<Ij3PTg00<cj2ITg00=@j3JTg00>:lLXTg00??j2WTg00?ij1OTg00@GlOMTg00A9j1eTg00A[j1cTg00BTj7HTg00CFj4GTg00D:lzbTg00E=lzaTg00F@lz`Tg00GAlz]Tg00HDj2UTg00H`l{_Tg00Iaj1?Tg00J@j3>Tg00J`j2NTf0R0#4#4p=5%?0#?#?#?#?#?#?#?p=Ff2R1f1R2/30'0p=9g00K;R3?>20p=Rf4S00f3S01A>3209>315>35>3p=2A>3209>31p=L1112=>30p=;%40#Ap==%40#4#4#4p=<g00L0/80p=B1N20,N1p=CQ011U12'N/N0p=:%@0#@p=E%@0#4#4#4p=S%40#@p=D%@0#4p=7p,2rcR1p,2AIR4p,1LR5p,3RNGR6p,2stR7p,2LBR8p,6rng_fsS02p,2raR9p,2spR:p,2gpR;p,2tpR<p,2s0R=p,2s1R>p,2s2R?p,2s3R@p,2s4RAp,2s5RBp,2s6RCp,2s7RDp,2s8REp,2s9RFp,3s10RGp,3s11RHp,2FRRIp,2fcRJp,2m0RKp,3DSTRLp,4dcapRMp,2SSRNp,2DTROp,3mtlRPp,2tlRQp,2loRRp,3srcRSp,5cellsS03p,3cbsRTp,3pdtS04p,3SBLS05p,3SBHS06p,4rstkS07p,2AHS08p,3NFKS09p,3ABLS0:p,3MTLS0;p,3TLMS0<p,3HDTS0=p,3TOKS0>p,3ECBS0?p,3LCBS0@p,4DSTFS0Ap,2DCS0Bp,3BYSS0Cp,3NSMS0Dp,3S16S0Ep,4SRCBS0Fp,3DJ1S0Gp,3DJ2S0Hp,3DJ3RUp,3LOARVp,3LOSRWp,3SPTRXp,4SP16RYp,3TPARZp,4HINVR[p,3RCLR\p,3RLOR]p,3RHIR^p,3RRLR_p,3RRSR`p,3WSKRap,3WIMRbp,3WISRcp,3WFSRdp,4LOOPp,3S2GM{fg00LNRe#4Rf#4S0I#4S0J#4#5Rg#TRh#VRiQ0J#T#VRj#^[Rk%[jRjg00M3RlP9P:P=P>P?P@PAPBPCPDPEPFPGPHPKPLPMPNPOPPPQPRPSPTfZS0K10hOS0L#6g00MQ#FRmfYS0M'1S0NfX,1mS0O10hLS0P#6S0Q10hMS0R#6S0SfW,1mS0TfV,1mS0UfU,1mS0VfT,1mS0WfS,1mS0XfR,1mS0YfQ,1mS0Z%@eRn#ARo,3MQ0I#A'dRp,0hS0[#6%5gRg#A/QP99hQS0\#6fP,1mS0]fO,1mS0^fN,1mS0_%\3R3'RD2D2D2D2S0`fM,1mS0afL,1mS0bfK,1mS0cfJ,1mS0dfIRq,1mS0efHRr,1mS0ffGRs,1mS0g%Af/Qp99hLS0h#6S0iA9hLpS0j#6S0kfFRt#6fES0l#6fDS0m#6;L3S0n3LD2D2%Fm#F#F#FS0ofCRu;;3S0pMLK%=nRv/8MS0q%@f#=1ZlS#YRf'8S0r%AeS0s/8uRwPu%4g#5#<#=RgfBRx#BPxPgfARy#BPyPgf@Rz13ux/3y/3v5Pl18zf1QopS0t/8MS0u3CC:C:C:3CS0v13NvRp,Ix=JtyS0w13ps,Iy=JtzS0x13prS0y/3sS0z,Izf?Ro5Jtg00N0R{P6P1P4P5P6P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJP7P8PLPMPRPKMLXS0{10hfS0|1Wh:%@n#E#<#O59hS0}P;P<Pof>Rnf=R|13pqS0~/3rRr,0hA9hLMS10f<RqA9hrsf;Rr10htS11f:R}f9R~f8S12f7S13Q0~,0h10hzS0~10hpS1410hxS1510hNS16Q0t99hLS0t10hyS1710huS18Q0l,0hS19Q0m,0hS1:Q0\Q0hQ1610hsMOMPI%5e#S#D#7#<#D#7#=,0hPJ%eiS1;fa%c{RsFHCG[[[\w\w[[^1i^Pi^^i^]i^Oi^ki^Ki^Zi^Ji^ll^nl^_l^cl^Ql^Yl^0l^Hl^Gl]F^Ej^Ri^`i^mi^<j^;j^:j^9j^8j^6j^5j^4j^3j^2j^Dj^Cj^Aj^@j^?j^>j^=j^7j]B]IP1P4P5P6P7P8Q02P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSQ03PTQ04Q05Q06Q07Q08Q09Q0:Q0;Q0<Q0=Q0>Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0FQ0GQ0HPUPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdP0MzbP9P:P=P>P?P@PAPBPCPDPEPFPGPHPKPLPMPNPOPPPQPRPSPTQ0KQ0`Q0aQ0bQ0cQ0dQ0eQ0fQ0gQ0iQ0k11mtRtQ0n3LD2D2Q0pMLKQ0vQ0wQ0xP{P6Q0{Q0|Q0}P;P<PzPoPnQ0z,0hQ10Q0I#S#O,0hS0IP|PqQ19PrP}P~Q12Q0y,0hQ0[Q14Q17Q13Q0tf6S0yQ15Q1:Q18Q0\Q0hQ16Q11MOMPI%5e#S#D#5#D#7#<#=,0hPJQ1;f`S11PsFHCG[[\w\w[[^Ni^Mi^1i^Pi^^i^]i^Oi^\i^Ki^Zi^Ji^_l^cl^Ql^Yl^0l^Hl^Gl^Fl^Ej^Ri^`i^Lj^<j^;j^:j^9j^8j^6j^5j^4j^3j^2j^Dj^Cj^Aj^@j^?j^>j^=j^7j^Bj^IkP1P4P5P6P7P8Q02P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSQ03PTQ04Q05Q06Q07Q08Q09Q0:Q0;Q0<Q0=Q0>Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0FQ0GQ0HPUPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdP0MzaP9P:P=P>P?P@PAPBPCPDPEPFPGPHPKPLPMPNPOPPPQPRPSPTf\S0vf[Q0KQ0NQ0QQ0SQ0OQ0TQ0UQ0VQ0WQ0XQ0YQ0ZQ0]Q0^Q0_Q0a/R33LD2D2D25;m5;mQ0bQ0cQ0dQ0eQ0fQ0gPtQ0l,1mS0lQ0m,1mS0m11muS0K11mxS0S%6yP3D2D2D2Q0o?;z3MLKQ0qQ0rQ0s/8zRwPzPg%BoPoPg%BnPnPg13zo/3n/3v9Pl|18|fQ0u3CC:C:C:3C1Inp=Jx|P{P6Q0{Q0|Q0}P;P<P|PqPrQ0PQ10Q0IP}P~Q0~Q0LQ15Q12Q13A9hpuQ0[Q14Q0jQ0yQ0tf5RuQ0010ho10hnRxQ0\Q0hQ16Q17MOMPI%5e#7#<#7#E#<#7#=,0hPJQ1;Q11PsFHCG[\w[[^[i^Ni^Mi^1i^Pi^Oi^\i^Ki^Zi^Ji^Ql^Yl^0l^Hl^Gl^Fl^Ej^Ri^Wj^Lj^Vj^Uj^<j^;j^:j^9j^8j^6j^5j^4j^3j^2j^Tj^Xj^Dj^Cj^Aj^@j^?j^>j^=j^7j^Bj^Sj^IkP1P4P5P6P7P8Q02P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSQ03PTQ04Q05Q06Q07Q08Q09Q0:Q0;Q0<Q0=Q0>Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0FQ0GQ0HPUPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdP0Mz`P9P:P=P>P?P@PAPBPCPDPEPFPGPHPKPLPMPNPOPPPQPRPSPTQ0MQ0OQ0TQ0UQ0QQ0VQ0WQ0XQ0YQ0ZQ0]Q0^Q0_Q0aQ0bQ0cQ0dQ0e/R3D2D2D2D2Q0fQ0gPtQ0lQ0mQ0KQ0S11myA;m|39;mn9;mo9;mzD2D2Q0o?;q3MLKR3Q0qQ0rQ0s/8qPqPg%BrPrPg%B}P}Pg13qr/3}/3v9Pl~18~fQ0u3CC:C:C:3CRfQ0J#ARv/8|P{P6Q0{Q0|Q0}P;P<P}Q0RP~Q0PQ10Q0I10hv13pnRn%Oe59h10hrQ0L10h|PxQ1210hnQ0[Q14Q0jQ13Q0tQ0yPuQ00Q01Q0\Q0hQ1610hqMOMRqPI%5e#7#<#D#5#E#7#7#=,0hPJQ1;Q0vPsFHCG[[[^ei^di^[i^Ni^Mi^1i^Ki^Ji^0l^Hl^Gl^Fl^Ej^aj^Wj^Lj^Vj^Uj^<j^;j^:j^9j^8j^6j^5j^4j^3j^2j^Tj^Xj^Dj^Cj^Aj^@j^?j^>j^=j^bj^7j^Bj^Sj^IkP1P4P5P6P7P8Q02P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSQ03PTQ04Q05Q06Q07Q08Q09Q0:Q0;Q0<Q0=Q0>Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0FQ0GQ0HPUPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdP2Mz]1U|vP{P6Q0{PqPI%5e#7#<#D#E#5#E#7#=,0hPJQ1;Q0vPsFHCG[\f\3^ei^di^[i^Ni^Mi^1i^Ki^Ji^0l^Hl^Gl^Fl^Ej^aj^Wj^Lj^Vj^Uj^<j^;j^:j^9j^8j^6j^5j^4j^3j^2j^Tj^Xj^Dj^Cj^Aj^@j^?j^>j^=j^bj^7j^Bj^Sj^IkP1P4P5P6P7P8Q02P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSQ03PTQ04Q05Q06Q07Q08Q09Q0:Q0;Q0<Q0=Q0>Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0FQ0GQ0HPUPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdP2P0M{_bjbibfbgbho"). Qed.

End W4S0F.
End CANSEC1.
