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
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseWalkKit FseRdKit HufWalkKit HufWalkKit2 HufWalkKit3.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require KXTac KXGoM.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_z4s_iface AF_huf_z4s3_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AF_huf_z4m AF_huf_z4sb AF_huf_z4spa AF_huf_z4s3b AF_huf_z4skx1.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AF_huf_z4s1_iface AF_huf_z4s2_iface AF_huf_z4s0 AF_huf_z4s01 AF_huf_z4s01s AF_huf_z4s02
  AF_huf_z4s02s AF_huf_z4s03 AF_huf_z4s03s AF_huf_z4s04 AF_huf_z4s1 AF_huf_z4s2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_z4sf () := "C46Stdlib5Lists4List2hdC59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW;AF_huf_z4s2:z4s2_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanWAAF_huf_z4s2_iface9z4s2_goalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW;AF_huf_z4s1:z4s1_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanWAAF_huf_z4s1_iface9z4s1_goalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<AF_huf_z4s048z4s04_j3C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3divC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib5AsanWAAF_huf_z4s3_iface3SPAC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib5AsanWAAF_huf_z4s3_iface4Z4SFC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib5AsanW<AH_huf_iface=huf_dec_postAC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF4evtFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=AF_huf_z4s03s;z4s03_smallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<AF_huf_z4s038z4s03_j2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=AF_huf_z4s02s;z4s02_smallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<AF_huf_z4s028z4s02_j1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<AF_huf_z4s019z4s01_bigC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=AF_huf_z4s01s;z4s01_smallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW;AF_huf_z4s0:z4s0_entryC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic2or00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib5AsanW4AImg5asegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanWAAF_huf_z4s3_iface;z4s31_stmtAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanWAAF_huf_z4s3_iface;z4s32_stmtAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanWAAF_huf_z4s3_iface;z4s33_stmtAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanWAAF_huf_z4s3_iface;z4s34_stmtAC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW=AMalloc_iface<AMallocIface00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC59OSSVerify5KrLib5AsanW=AMalloc_iface5AHEAPC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5AsanW5ABase6abkind02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5AsanW5ABase6ablock01C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib4Init5Logic3notC59OSSVerify5KrLib5AsanW5ABase7ab_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase7ab_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase4ablkC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5AsanW5ABase6abkind01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<AH_huf_iface<DTABLE_BYTESC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec=HufPure_HufX2;x2_table_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib6Common;HufWalkKit39x2_bytes'C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnI47Corelib4Init5Logic2ex00I47Corelib5Lists7ListDef6Forall00C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase6al_topC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib5AsanW>AHarness_iface<harness_invAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9Stdio_kit6rcleanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9Stdio_kit4r_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9Stdio_kit4r_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9Stdio_kit5r_rloC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9Stdio_kit4rrngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW;AF_huf_z4sf8z4s_fullC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW@AF_huf_z4s_iface=z4_slow_stmtAC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib8RunConst9runConstT00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW5ABase7alayout00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW5ABase6ablock00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec=HufPure_HufX26deltX200C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW9Stdio_kit6region00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<AH_huf_iface?HUF_DEC_STACK_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase3ATPC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.
Section Z4SF.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock) (rng_fs : alayout -> footprint -> Prop).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
            (SBL SBH : Z) (rstk : region).
  Notation SP := (bv_unsigned sp).
  Notation SPF := (SP + -576).
  Notation n := (zlen src).
  Notation seg := ((dcap + 3) / 4).
  Notation DTL := (DTABLE_BYTES mtl).
  Hypothesis AH : AHEAP AI L RNG st LB m0.
  Hypothesis NFK : forall F k, ~ In (mkABlock (ABFake 0) F k) LB.
  Hypothesis ABL : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b).
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TLM : tl <= mtl.
  Hypothesis HDT : In (HB pdt DT DTL) LB.
  Hypothesis TOK : x2_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells).
  Hypothesis LCB : zlen cbs = 4 * 2^tl.
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
  Notation ZB l := (l AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src
                      cells cbs pdt SBL SBH rstk AH NFK ABL MTL TLM HDT TOK ECB LCB DSTF DC BYS NSM S16 SRCB DJ1 DJ2 DJ3
                      LOA LOS SPT SP16 TPA HINV RCL RLO RHI RRL RRS WSK WIM WIS WFS) (only parsing).
  Notation Z4SF' mm spl bd4 := (Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm spl bd4)
    (only parsing).

  Hypothesis Y31 : z4s31_stmtA.
  Hypothesis Y32 : z4s32_stmtA.
  Hypothesis Y33 : z4s33_stmtA.
  Hypothesis Y34 : z4s34_stmtA.

  Lemma z4s_full : z4_slow_goal AI L RNG st LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT
                     mtl tl lo src cbs.
Proof using All.
ltac2:(KReplay.run1 (kr_t_AF_huf_z4sf ()) ["CANSEC1"; "Z4SF"] "h02LLh12j0h22j1h32jbh42l1h52l2h62l3h72mmh82p1h94w168h:4w232h;4w240h<4w248h=4w256h>4w264h?4w272h@4w280hA4w296hB4w304hC4w312hD3w40hE3x15hF3x16hG2x5hH2x6hI4w176hJ4w288hK3x10hL3x21hM2b1hN2b2hO2c2hP2p2hQ3pt1hR3pt2hS4w200hT4w224hU3x29hV3x30hW2x7hX4bitshY2pthZ4w184h[4w192h\4w208h]4w216h^3x11h_3x14h`3x17ha3x18hb3x19hc3x22hd3x23he2J1hf2J2hg2J3hh4LOOPhi3S2Ghj3SM2hk3SM3hl2b3hm2c3hn2p3ho3pt3hp3x13hq3x28hr3x31p%0p%1p;}p;Rp;zp;{p;1p;2p;Fp;3p;Kp;Lp;Op;7p;4p-1p10000p4p710R0p8p1000Gp4p70P0p8g001>l}jTg002?lRiTg003Elz[Tg004FlRXTg005Ll{hTg006Lj12Tg0071j1QTg007Oj1PTg0082j1YTg008Tj1WTg0094j1=Tg009Yj1?Tg00:7j23Tg00:Tj2eTg00;1j20Tg00;Wj2MTg00<4lFJTg00=4j2GTg00=ij1ZTg00>Ij3FTg00>ilKETg00?jj21Tg00@Fj2DTg00@bj2;Tg00A=j2VTg00A]j1UTg00B=lLTTg00CBj2STg00Clj1OTg00DJlOLTg00E<j1gTg00E^j1fTg00FWj7KTg00GIj4ITg00H=lzdTg00IAl{`Tg00JAlz_Tg00KEl{^Tg00LElzaTg00MFlzbTg00NJl{]Tg00OKj1ATg00Ojj3NTg00PDj2\Tf0R0#2#2p=:f2R1f1R2/30'0p=5%20#?p=<%A0#A#A#A#A#A#A#Ap=H%20#2#2#2p=91312/30p=Cg00P^R313207N1p=7g00Q<R4/10p=4f3=N341312/10'\p=>1120,;1p=B%=0#=p=6%20#2#2#=p=@%=0#2p=8AN320p=c%20#=p=Rp,2rcR1p,2AIR4p,1LR5p,3RNGR6p,2stR7p,2LBR8p,6rng_fsS00p,2raR9p,2spR:p,2gpR;p,2tpR<p,2s0R=p,2s1R>p,2s2R?p,2s3R@p,2s4RAp,2s5RBp,2s6RCp,2s7RDp,2s8REp,2s9RFp,3s10RGp,3s11RHp,2FRRIp,2fcRJp,2m0RKp,3DSTRLp,4dcapRMp,2SSRNp,2DTROp,3mtlRPp,2tlRQp,2loRRp,3srcRSp,5cellsS01p,3cbsRTp,3pdtS02p,3SBLS03p,3SBHS04p,4rstkS05p,2AHS06p,3NFKS07p,3ABLS08p,3MTLS09p,3TLMS0:p,3HDTS0;p,3TOKS0<p,3ECBS0=p,3LCBS0>p,4DSTFS0?p,2DCS0@p,3BYSS0Ap,3NSMS0Bp,3S16S0Cp,4SRCBRUp,3DJ1RVp,3DJ2RWp,3DJ3RXp,3LOARYp,3LOSRZp,3SPTR[p,4SP16R\p,3TPAR]p,4HINVR^p,3RCLR_p,3RLOR`p,3RHIRap,3RRLRbp,3RRSRcp,3WSKRdp,3WIMRep,3WISRfp,3WFSRgp,3Y31p,3Y32p,3Y33p,3Y34M}jP1P4P5P6P7P8P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTMRiP1P4P5P6P7P8Q00P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSQ01PTQ02Q03Q04Q05Q06Q07Q08Q09Q0:Q0;Q0<Q0=Q0>Q0?Q0@Q0AQ0BQ0CPUPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdPePfPgP0Mz[P1P4P5P6P7P8P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTMRXP1P4P5P6P7P8Q00P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSQ01PTQ02Q03Q04Q05Q06Q07Q08Q09Q0:Q0;Q0<Q0=Q0>Q0?Q0@Q0AQ0BQ0CPUPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdPePfPgP0P2M{hg00QZRh#2Ri#2S0D#2Rj#2#:Rk#QRl#PRm%Qj#PRn#Y[S0E%WnRnP9P:P=P>P?P@PAPBPCPDPEPFPGPHPKPLPMPNPOPPPQPRPSPTf[RofMS0FfLS0GA5lLMS0H%=hS0I#?Rp,3MQ0D#?'eRq95lLS0JQ0I#<Rr,3NRsfZRt'3S0K,0l1Mpq95lLS0L10lsS0M%?i/Mq95lLS0NQ0KfYRq55lfKS0OfJS0PfIS0QfHS0RfGS0SfFS0TfES0UfNS0V,0lfDS0WfCS0XfBS0Yf?S0Zf>S0[MFJg00R?Rpg00S4#H#H#H#H#HS0\f=S0]'G%ZpS0^3FMKE%?hS0_/1o%:kS0`#2#:#9#<S0a,Do';Ruf^Rvf]Rwf\Rx3C=7or1V3S#URy,1x11rMS0b%=i#</1yS0c%4wPvPv%?jRjfcRiC>f_Rz97vsfaR{#4S0d%?kRk7B{11j{11ij[%4zS0ef`R|P|PjfgS0fC>fiS0g,3s=7|{%4i?Bik11jifeR}/1j[Q0dfbR~P~PjfkS0hC>fnS0ifmS0j5Cs=7~i%4}?B}k11j}Q0f/1j[g00SSS0kP6P1P4P5P6P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJP7P8PLPMPRPKMLTS0l10lyS0m1Sl:Q0D#=#:#9#O55lS0DP;P<fSfRfQS0nQ0`#?/MP95lQS0`Q0j,0lfPS0jfqfp5Csfo55lQ0i,0lfOS0iQ0VQ0FQ0GQ0OQ0f,0lS0ofWS0p10lNS0qfjS0r,0lfhS0s,0lS0tfXS0u10lLS0v10lOS0wQ0h,0lQ0I#6#6#6#6#6#6#6#:#9#9#9#<,0lS0IQ0PQ0QQ0RQ0SMOLPI%@h#9#6#8#6#8#8#<,0lPJ%gmS0xfrQ0k#fS0yFKCI[[[[[[[[[[[[[[[[[[[\u\u[[^rm^Vm^Um^qm^`m^Fm^Em^_m^pm^Km^Wm^Hm^Gm^3n^2n]1^mm^Om^Cm^Bm^Am^@m^?m^>m^=m^<m^;m^:m^9m^Dm^n3^o3^l3^P3^R3^N3^83^Q3^M3^03^63^53^43]7P1P4P5P6P7P8Q00P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSQ01PTQ02Q03Q04Q05Q06Q07Q08Q09Q0:Q0;Q0<Q0=Q0>Q0?Q0@Q0AQ0BQ0CPUPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdPePfPgP0MzdQ0EP9P:P=P>P?P@PAPBPCPDPEPFPGPHPKPLPMPNPOPPPQPRPSPTfVRuQ0OQ0PQ0QQ0JfU,3sS0d,0lQ0LQ0MQ0NQ0dfT55lQ0RQ0SQ0TQ0UQ0WQ0XQ0YfAS0df@S0zQ0ZQ0[f<S0{f;S0|MFJQ0\f:S0}'GQ0^5FpMKEQ0_/1uS0~Q0a,DuS10';S11Q11Q0~1Duj';S0~Q0uQ0p5Cq=7urS12Q0p/1yS0pQ0bQ0cQ0u#4S0uPqPqPjPvC>S13Q0K,cqS0K%4xS14?BxkS1511jx11vj[S16%4tS17PoPoPjP~C>fdS18,3s=7ox%4vS19?Bvk11jv11|j[Q0kP6Q0lQ0mQ0DP;P<Q0OQ0PQ0fffS1:5CsS0f,0lQ0`10liS1;Q0QQ0f=5l}Q18,0lS0f10l}S1<10ljS1=Q0RQ0S10l|S1>Q0TQ0UQ0HQ0W10lvS1?Q0iQ0vQ0w10l{S1@Q0IQ0LQ0XQ0YQ0qMOLPI%@h#9#8#6#@#8#<,0lPJQ0xQ0sQ0yFKCI[[[[[[[[[[[[[[[[[[^Vm^Um^Lm^bm^am^Fm^Em^Km^Hm^Gm^3n^2n^1n^Om^Cm^Bm^Am^Jm^@m^?m^>m^=m^<m^;m^:m^Im^9m^Dm^P3^R3^N3^83^Q3^M3^03^63^53^43]7P1P4P5P6P7P8Q00P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSQ01PTQ02Q03Q04Q05Q06Q07Q08Q09Q0:Q0;Q0<Q0=Q0>Q0?Q0@Q0AQ0BQ0CPUPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdPePfPgP2P0M{`Q0EP9P:P=P>P?P@PAPBPCPDPEPFPGPHPKPLPMPNPOPPPQPRPSPTPtQ0iQ0VQ0FQ0JA5lsqQ0GQ0MQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0WQ0XQ0YQ0dQ0zQ0[Q0]MFJQ0\Q0{'GQ0^5FpMKEQ0_/1tQ0a,DtS1A';S1BQ1BQ17Q1A';ACwxo=7tr11oyQ0bQ0cQ14PwPwPjP~C>A7wsv%4|?B|k11j|11~j[Q19PzPzPjQ1:C>Q0s,3s=7z|%4~?B~k11j~Q18/1j[Q0kP6Q0lQ0mQ0DP;P<Q0FQ0GQ0h,3sQ0r55lQ0`Q0oQ0OQ0PQ0tQ0g,0lQ0QQ0RQ0SQ0fQ0TQ0UQ0HQ0W10l~R|Q0nQ0vQ0wQ1<Q0IQ0LQ0XQ0YQ0qMOLPI%@h#9#8#@#6#8#<,0lPJQ0xflQ0yFKCI[[[[[[[[[[[[[[[[[[^Vm^Um^Lm^bm^am^Fm^Em^_m^^m^Km^Hm^Gm^3n^2n^1n^Om^Cm^Bm^Am^Jm^@m^?m^>m^=m^<m^;m^:m^Tm^Sm^Im^9m^Dm^P3^R3^N3^83^Q3^M3^03^63^53^43]7P1P4P5P6P7P8Q00P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSQ01PTQ02Q03Q04Q05Q06Q07Q08Q09Q0:Q0;Q0<Q0=Q0>Q0?Q0@Q0AQ0BQ0CPUPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdPePfPgP0Mz_Q0EP9P:P=P>P?P@PAPBPCPDPEPFPGPHPKPLPMPNPOPPPQPRPSPTPuQ0VQ0FQ0GQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0WQ0XQ0YQ0dQ0zQ0ZQ0[Q0]Q0{Q0|Q0}f9MFJQ0\f8'GQ0^5FpMKEQ11Q0~%4uQ10';Q12Q0pQ0bQ0cQ0uQ13Q0KQ15Q16Q0kP6Q0lQ0mQ0DP;P<Q0WQ0XQ0YQ0`Q1?13s~R~/3{Ru%Oh55lQ1=10lzRvQ1>Q1@Q0dQ0z10lu10l~Q0JQ0HQ0ZQ0[Q0]Q0vQ0w10lxQ0IQ0LQ0NQ0MQ0qMOLPI%@h#:#@#:#6#R#8#<,0lPJQ0xPiQ0yFKCI[[[[[[[[[[[[[^dm^cm^Lm^Fm^Em^Wm^Hm^Gm^3n^2n^1n^Cm^Bm^Am^Jm^@m^?m^>m^=m^<m^;m^:m^Tm^]m^\m^Sm^[m^Zm^Im^9m^Dm^83^Y3^X3^03^63^53^43]7P1P4P5P6P7P8Q00P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSQ01PTQ02Q03Q04Q05Q06Q07Q08Q09Q0:Q0;Q0<Q0=Q0>Q0?Q0@Q0AQ0BQ0CPUPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdPePfPgP2P0M{^Q0EP9P:P=P>P?P@PAPBPCPDPEPFPGPHPKPLPMPNPOPPPQPRPSPTPqQ0nQ0jQ0iQ0VQ0FQ0GQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0WQ0XQ0YQ0dQ0zQ0ZQ0[Q0]Q0{MFJQ0\Q0|'GQ0^5FpMKEQ0_/1qQ0a,DqRp';R2%4q/;pACxot=7qr11tyQ0bQ0c%4oPxPxPjP{C>A7xswQ0e?Bzk11jz11{j[Q0kP6Q0lQ0mQ0DP;P<Q0SQ0TQ0UQ0`Q1@Q0WQ0XP|Q1;Q0fQ0YQ0dQ0zA5ls}Q0JQ0HQ0ZQ0[Q0]Q0vQ0wPvQ0IQ0LQ0NQ0MQ0qMOLPI%@h#:#9#8#R#8#:#<,0lPJQ0xQ1:Q0yFKCI[[[[[[[[[[\2[[^dm^cm^Lm^`m^Fm^Em^^m^Km^Wm^Hm^Gm^3n^2n^1n^Cm^Bm^Am^Jm^@m^?m^>m^=m^<m^;m^:m^Tm^]m^\m^Sm^[m^Zm^Im^9m^Dm^83^Y3^X3^03^63^53^43]7P1P4P5P6P7P8Q00P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSQ01PTQ02Q03Q04Q05Q06Q07Q08Q09Q0:Q0;Q0<Q0=Q0>Q0?Q0@Q0AQ0BQ0CPUPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdPePfPgP1P4P5P6P7P8Q00P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSQ01PTQ02Q03Q04Q05Q06Q07Q08Q09Q0:Q0;Q0<Q0=Q0>Q0?Q0@Q0AQ0BQ0CPUPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdPePfPgP0MzaP1P4P5P6P7P8Q00P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSQ01PTQ02Q03Q04Q05Q06Q07Q08Q09Q0:Q0;Q0<Q0=Q0>Q0?Q0@Q0AQ0BQ0CPUPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdPePfPgP0MzbM{]bebjbfbkbgbhbio"). Qed.
End Z4SF.
End CANSEC1.

Theorem z4_slow_proofA {rc : runConstT} : z4s31_stmtA -> z4s32_stmtA -> z4s33_stmtA -> z4s34_stmtA -> z4_slow_stmtA.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_z4sf ()) [] "p'0h02rch13ABLh22AHh32AIh43BYSh52DCh63DJ1h73DJ2h83DJ3h93DSTh:4DSTFh;2DTh<3ECBh=1Fh>2FRh?3HDTh@4HINVhA1LhB2LBhC3LCBhD3LOAhE3LOShF3MTLhG3NFKhH3NSMhI3RCLhJ3RHIhK3RLOhL3RNGhM3RRLhN3RRShO3S16hP3SBHhQ3SBLhR4SP16hS3SPThT4SRCBhU2SShV3TLMhW3TOKhX3TPAhY3WFShZ3WIMh[3WISh\3WSKh]3Y31h^3Y32h_3Y33h`3Y34ha1bhb1chc3cbshd5cellshe4dcaphf2fchg2gphh1khi2lohj2m0hk3mtlhl1phm2pbhn3pdtho2rahp6rng_fshq4rstkhr2s0hs2s1ht3s10hu3s11hv2s2hw2s3hx2s4hy2s5hz2s6h{2s7h|2s8h}2s9h~2spi003srci012sti022tli032tpp;1p;2p;7p;3p;}g00THj1jTg00UPj1iTg00VXj1WTg00W`j1RTg00Xhj1hTg008Tj1ATg006Lj10Tg0071j1>Tg007Oj1DTg0094j12Tg00Yoj2QTg0082j1OTg00Z[j7NTg00[Yj1gTg00\Rj3?Tg00]Kj3:Tg00]bj1]Tg00^;j1[Tg00_3j1ZTg00:7j25Tg00_kj3XTg009Yj13Tg00?jj21Tg00@bj26Tg00``j1KTg00aYj1ETg00b]j2VTg00c`j2=Tg00;Wj2ITg00d=j1UTg00d]j1TTg00e^j3PTg00Ojj3<Tg00A=j28Tg00A]j17Tg00f=j2JTg00PDj2BTg00@Fj2;Tg00fWj3fTg00g8j2HTg00gUj1MTg00CBj2@Tg00hKj1LTg00iBj2dTg00;1j2cTg00ibj1bTg00jhj2\Tg00kcj1^Tg00l\j1_Tg00mUj1`Tg00nOj2aTg00oHj3GTg010;l}eTg011:j1YTg00P^R0f0R1g00Q<R23<p=C%01#0p=S%01#0#0#0p=4%21#2p=F%21#2#2#2p=9g012CR3%j1f1R4#if2R5#Wf3R6#Rf4R7#hg013@R8g014:R9g0153g015nR:#Ap-0\9\8g00QZR8#0R9#0R;#0R<#0R=#0R>#0R?#>R@#DRA%29#>/QA%>>#D%><#DR<#O\A%A0g016g#A%A<RBg000GRCg017gf[RDfVREfURFfTRGfSRHfRRIf>RJFN%g2??41=::F#]^h0^=0A::1Ff_RK%[4RL%Z4,5L3X[^a:%38f<RL'1%28RM#0RN#0#3,1L'6f=RO,1Lf8RP#Kf?RQ%EJ3?fWRR5::f;RS/VJ%3;R;%39R9/=Q'I#U%TL5P<9<BS18<L#7f@R<,=9,I;5<0fFR;#CfERB#C'6%K1RTfGRU;?;f\RV5::XmC,JC'B112;%3>,=9,;;'61121%S?R?#3,;1'6Xb0fAR>5f0fBRW,80#7%2N#0#3,=9';%3=R=fHR9'1fDRN,80#7,;21H>W9?TWfbRT5::fKR:,1W180;#7,5:R2/1>'6'6XlC,JC[fIRC%E9'5fJRX'1180B#7,5X/1C'BfMRYfLRZ'5/1:112Y'B%EX,5:fNR2'1152Y/1:'BfmR[#M%4?R?#3'5/1C1@@Tg018d'H,1XfcR\,@@/5=fiR]#L';fdR^,@@/d=#Cg019k,c@9<A\%bF1\E9%^CfPR='11@@]%_X'1fvR@#M%`:'1fpR_/aZfqR`frRa#L/HG7GG%4?#3%08#2#F#9#0#2#4#4#4#35GafsR?%FM#9#9#9#0#2#0#4#4#4#3%08#2#F#9#0#2#0#4#4#33GP`fuR8ftRMO2f|fwP@P8PMP?PaP`P_fofnP[flfkfjP]fhfgfffeP^P\PTfaf`PKf^f]PVPDfZfYfXPRPEPFPGPHPIfQP=fOP2PYPZP:PXPCP9PUP;PBPNfCPWP>P<PQPJPOPLPSf:f9PPf7f6f5P7P6P5P4P1f{fzfyfxM}eWYW[WZW\WNWMWJWKWIW@WXWRWSWEWDW8W7W6WTWOWHW4W5W:WCW<WWW?WVWFW1WGW2WqXP0XQ0WnWcWdY00Xi0Z020Xk0X;0XU0Xe0X90WjWfW>XuAXtAX}AX|AX{AXzAXyAXxAXwAXvAXsAXrAZ03AXgAX~AWoWpWBY01WLWAW3%Y7eW`W_W^W]X03P1O1W0o"). Qed.
