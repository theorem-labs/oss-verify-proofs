(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_fa_iface
  RF_huf_x4s RF_huf_x4s31 RF_huf_x4s31b RF_huf_x4s32 RF_huf_x4s32b RF_huf_x4s33 RF_huf_x4s33b RF_huf_x4s34 RF_huf_x4s34b RF_huf_x4s3 RF_huf_x4s2 RF_huf_x4s1 RF_huf_x4s1k RF_huf_x4s0 RF_huf_x4s01 RF_huf_x4s01s
  RF_huf_x4s02 RF_huf_x4s02s RF_huf_x4s03 RF_huf_x4s03s RF_huf_x4s04.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_x4sf () := "C59OSSVerify5KrLib5Plain<RF_huf_x4s04:x4s04_mainC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3divC45stdpp9bitvector;definitions7Z_to_bvK59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib5Plain?RF_huf_fa_iface6jt_lenC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib5Plain:RF_huf_x4s3X4FC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic3and00C59OSSVerify5KrLib5Plain>RF_huf_h_iface<huf_dec_postC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RF_huf_x4s03s;x4s03_smallC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib5Plain<RF_huf_x4s03;x4s03_entryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RF_huf_x4s02s;x4s02_smallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain<RF_huf_x4s02;x4s02_entryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain<RF_huf_x4s019x4s01_bigC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RF_huf_x4s01s;x4s01_smallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RF_huf_x4s0:x4s0_entryC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib5Plain;RF_huf_x4s13HDIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg5psegsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

Section CANSEC1. Context {rc : runConstT}.
Section X4SF.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX1) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Hypothesis TOK : x1_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (2 * 2^tl)) (x1_bytes' cells).
  Hypothesis LCB : zlen cbs = 2 * 2^tl.
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TLM : tl <= mtl + 1.
  Hypothesis D0 : 0 <= DST.
  Hypothesis DP : 0 < dcap -> 8 <= DST.
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis DL : DST + dcap <= lo.
  Hypothesis S0 : 16 <= SS.
  Hypothesis SL : SS + n <= lo.
  Hypothesis NSM : n < 2^26.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis DT0 : 0 < DT.
  Hypothesis CBL : DT + 4 + 2 * 2^tl <= lo.
  Hypothesis DJ1 : DT + 4 + 2 * 2^tl <= DST \/ DST + dcap <= DT.
  Hypothesis DJ3 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis LOS : lo <= SP - 4096.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SP47 : SP <= 2^47.

  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation XB l := (l ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cells cbs
                      TOK ECB LCB MTL TLM D0 DP DC DL S0 SL NSM BYS DT0 CBL DJ1 DJ3 LOS SP16 SP47) (only parsing).
  Notation X4F' mm spl bd4 := (X4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT lo src cbs mm spl bd4).

  Notation DW := [(SP - 4096, SP); (DST, DST + dcap)].
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Notation X4S0' mm := (X4S0 ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm).

  Lemma x4s_slow : forall mm (t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x25 x26 t4 t5 : word),
    X4S0' mm ->
    evt psegs POST (MS (mkR (Z_to_bv 64 n) (Z_to_bv 64 (SP + -416)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                           (Z_to_bv 64 SS) x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 dcap) (Z_to_bv 64 DST) t4 t5 (Z_to_bv 64 DT))
                       F (Z_to_bv 64 0x190c8) fc None mm (seg_rom psegs)).
Proof using All.
ltac2:(KReplay.run1 (kr_t_RF_huf_x4sf ()) ["CANSEC1"; "X4SF"] "h02a0h12a5h22a6h32j0h44j104h54j120h64j128h74j136h84j144h93j16h:3j24h;2j8h<3j88h=2jbh>2mmh?2t0h@2t1hA2t2hB3j48hC3x22hD3x26hE2a4hF2a7hG3bc1hH2c1hI3j64hJ3pa1hK4j112hL4j152hM3j32hN3j40hO3j56hP3x21hQ3bc2hR3pa2hS3x23hT3j72hU3j80hV3j96hW3x24hX2C2hY2C3hZ2C4h[3HB1h\3HS1h]3HS2h^3HS3h_2a1h`2a3ha3bc3hb2c2hc3c3whd3pa3p%0p;bp;1p;2p;Ip;Fp;Op;7p;cp;dp;3g0000lbdTg0012j13Tg001Wj1MTg0025j1NTg002Xj1\Tg003:j1XTg003Zj22Tg004Oj14Tg0054j1=Tg005Rj25Tg005oj2OTg006Lj20Tg0072j16Tg007gj2KTg008Dj2LTg009Ej1YTg009elICTg00:^j28Tg00;:j2WTg00;Zj1VTg00<:j2<Tg00<UlFUTg00=[j2TTg00>Ej1STg00>clOBTg00?Uj1QTg00@7j1PTg00A0j7?Tg00AblcRTg00Bfj2ITg00CBldcTg00DElcbTg00EIldaTg00FLlc`Tg00GMlc^Tg00HQld]Tg00IRj1;Tg00J1j3FTg00JQj2[Tg00Jnj3_Tg00Khj3ZTf0R0#3#3p=7%;0#;#;#;#;#;#;#;p=E%30#=p=:g00LYR1f4S00f3S01f2R2f1R3=F105F15F13Fp=1AF130p=JQ011[23;_0p=9%40#3p=H%30#3#4#3p=@%40#4p=Ag00MNS02?Z30p=>%30#4p=G%40#3#4#3p=Dp,2rcR2p,2raR4p,2spR5p,2gpR6p,2tpR7p,2s0R8p,2s1R9p,2s2R:p,2s3R;p,2s4R<p,2s5R=p,2s6R>p,2s7R?p,2s8R@p,2s9RAp,3s10RBp,3s11RCp,1FRDp,2fcREp,2m0RFp,3DSTRGp,4dcapRHp,2SSRIp,2DTRJp,3mtlRKp,2tlRLp,2loRMp,3srcRNp,5cellsROp,3cbsRPp,3TOKRQp,3ECBRRp,3LCBRSp,3MTLRTp,3TLMRUp,2D0RVp,2DPRWp,2DCRXp,2DLRYp,2S0RZp,2SLR[p,3NSMR\p,3BYSR]p,3DT0R^p,3CBLR_p,3DJ1R`p,3DJ3Rap,3LOSRbp,4SP16Rcp,4SP47RdMbdg00NCRe#3Rf#3Rg#3Rh#3#7Ri#MRj#NRk%Mh#NRl#\[Rmg00NhRn%XlRlP4P5P8P9P:P;P<P=P>P?P@PAPBPCPFPGPHPIPJPMPNPPfMRog00OF#ERpfE'2S03fD,2pS04fC,2pS05fB,2pS06%4eRq#=Rr,5H%=gRg'ORs,5G,0jS07#6S08%3i#:/KK,5L,0jRi#6S09fFS0:#61KrsRr,5G,0jS0;#6S0<%3qRq#=Rt,5IRug00OeRv,LNRw'5S0=%=fRx,LNRy'5Rz,0jS0>#6S0?fIS0@,0j#6S0A1Kxs,5G,0jS0B#6S0CfAS0D,2pS0E10jHS0F#6S0Gf@S0H,2pS0I10jIS0J#6S0Kf?S0L,2pS0Mf>S0N,2pS0Of=Rx,2pS0Pf<R{,2pS0QfHS0R,0j#6S0S%Y1R1D1D1D1D1D1%Ep#E#E#ES0Tf;R|'2/J1S0UMIC18tH%4f#:1WnN#VRf'8%=eR}/8w15wy1LNgRg'5/5tRt/8f18rH18vy18vg'<'<'<'<'<'<Rv18}yRr18}gS0VPwfPR}PuPoC9PyP}Q0=PoC9PgP}PzPoC9P4P5P6P7P8P9P:P;P<P=P>P?P@PAPBPCPDPEPGPHPMPFMFUR~10jfS0W1Tj5%Hq#7#7#S'5,0jS0XP6P7Q0DQ0HQ0L10juS0DQ0=,0jS0YQ0N15zg,0jS0Z10jtS0[PxP{P|f:S0\f9S0]15GH,0jRt10jJRz10jGRqfRS0^,0jfNS0_,0jS0`fQS0a,0jS0bfSS0c,0jS0d10jsS0ef7S0ff8S0gPqPtPiPzMOBPD%4e#@#A#H#A#A#7#:,0jPE%QkRsfTS0hQ02#PRfF?'>[[[[[[[^bk^Hk^Fk^2k^1k^Ek^`k^0k^Ak^@k^?k^=l^8l^7l^6l^5l^4l^<l^:l^9l^;l]3^ck^an^Qn^Gn^dn^Rn]J]>P2P4P5P6P7P8P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdP0McRP4P5P8P9P:P;P<P=P>P?P@PAPBPCPFPGPHPIPJPMPNPPfKS02Q0:,2pS0:Q03Q04Q05Q08Q09Q06Q0<Q0?Q0SQ0CQ0EQ0GQ0IQ0KQ0MQ0OQ0PQ0QfGS0S,0j#6P1D1D1D1D1D1Q0UMICPwPoPuQ02C9PyPoQ0=Q02C9Q0V%=hRh,Ig'<Q0WQ0XP6P7Q0HQ0LQ0NQ0DQ0YPxQ0ZQ0[10jgS0ZP{P|Q0\Q0]Q0JQ0;Q07fORg,0jS0VQ0gQ0>10j}S0?Q0eQ0ff6S0iPqPtPiPzMOBPD%4e#@#A#7#A#G#7#:,0jPEPsQ0aPfF?,>~[[[\r\v[^Hk^Dk^Ck^Fk^2k^1k^Ek^0k^Ak^@k^?k^=l^8l^7l^6l^5l^4l^<l^Bl^:l^9l^;l^3l^Qn^Gn^Rn^Jn^>mP2P4P5P6P7P8P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdP3P0MdcP4P5P8P9P:P;P<P=P>P?P@PAPBPCPFPGPHPIPJPMPNPPPoQ0R,2pS0RQ0S,2pS0SQ0:Q03Q08Q09Q04Q0<Q05fJS0<,0j#6Q0CQ06Q0GQ0EQ0KQ0IQ0MQ0OQ0PQ0AP1D1D1D1D1D1Q0T/2{/J1S0AMICPwPgPuPoC9PyPgQ0=PoC9Q0WQ0XP6P7Q0HQ0LQ0NQ0DQ0YPxP{Q0[Q0ZP|Q0\Q0]Q0gQ0JQ0;Q07Q0?Q0fQ0>Q0bQ0eQ0if5S0bPqPtPiPzMOBPD%4e#7#D#D#A#H#:,0jPEPsQ0^PfF?,>~[[\r\v[^Hk^Dk^Ck^Fk^2k^1k^Ek^_k^0k^Ak^@k^?k^=l^8l^7l^6l^5l^4l^<l^Il^Bl^:l^9l^;l^3l^Qn^Gn^Rn^Jn^>mP2P4P5P6P7P8P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdP0McbP4P5P8P9P:P;P<P=P>P?P@PAPBPCPFPGPHPIPJPMPNPPP}12poS0?fL,2pS0HQ02,2pS02Q0<,2pS0<Q0@,2pRoQ0RQ0SQ0:Q03Q0`#6Q0CQ04Q0GQ05Q06Q0EQ0IQ0MQ0OQ0PP1D1D1D1D1D1Q0AMICPwQ0aPuP}C91Iyh,<rQ0WQ0XP6P7Q0LQ0NPxQ0DQ0YP{10jyRyQ0[Q0ZP|Q0\Q0]Q0gQ0JQ0;Q07Q0fQ0iQ0>Q0dQ0eQ0bQ00PqPtPiPzMOBPD%4e#7#D#@#G#H#:,0jPEPsQ0hPfF?,>~[[\v[^Hk^Dk^Ck^Pk^Fk^2k^1k^Ek^0k^Ak^@k^?k^=l^Ll^8l^7l^6l^5l^Kl^4l^<l^Il^Ol^Bl^Nl^Ml^:l^9l^;l^3l^Gn^Jn^>mP2P4P5P6P7P8P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdP3P0MdaP4P5P8P9P:P;P<P=P>P?P@PAPBPCPFPGPHPIPJPMPNPPQ0aQ0_,2pRrQ0?Q0HQ02Q0<PoQ0RQ0SQ0:Q0V#6Q0CQ03Q0GQ04Q05Q06Q0EQ0IQ0MQ0OP1D1D1D1D1D1Q0T/2x/J1MICPwQ0^PuQ0aC9Q0WQ0XP6P7Q0LQ0NPxQ0DQ0YP{PyQ0[Q0ZP|Q0\Q0]Q0gQ0JQ0;Q07Q0fQ0iQ0bQ0dQ0eQ00Q01PqPtPiPzMOBPD%4e#@#G#D#G#7#:,0jPEPsQ0hPfF?,>~[\v[^Hk^Dk^Sk^Ck^Pk^Fk^2k^1k^Ek^0k^Ak^@k^?k^=l^Ll^8l^7l^6l^5l^Kl^4l^<l^Il^Ol^Bl^Nl^Ml^:l^9l^;l^3l^Gn^Jn^>mP2P4P5P6P7P8P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdP0Mc`P4P5P8P9P:P;P<P=P>P?P@PAPBPCPFPGPHPIPJPMPNPPP}12pgPrQ0?Q0HQ02Q0<PoQ0RQ0SQ0:Q03Q04Q05Q06Q0EQ0IQ0MQ0OQ0PQ0QP1D1D1D1D1D1Q0UMICR118hwQ0WQ0XP6P7PxP{P|Q0DQ0YQ0\PyQ0[Q0Z10jwQ0]Q0gQ0BQ0JQ0;Q07Q0fQ0iQ0bQ00Q0eQ01Q0FPqPtPiPzMOBRzPD%4e#@#7#D#D#:,0jPEPsQ0cPfF?,>~[\v[^Dk^Wk^Sk^Ck^Pk^2k^1k^0k^Ak^@k^?k^=l^Ll^8l^7l^6l^5l^Kl^4l^Vl^<l^Ul^Tl^Il^Ol^Bl^Nl^Ml^:l^9l^;l^3l^>mP2P4P5P6P7P8P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdP3Mc^1IwhPzPD%4e#@#G#@#7#7#:,0jPEPsQ0cPfF?,>~[\v\1^Dk^Wk^Sk^Ck^Pk^2k^1k^0k^Ak^@k^?k^=l^Ll^8l^7l^6l^5l^Kl^4l^Vl^<l^Ul^Tl^Il^Ol^Bl^Nl^Ml^:l^9l^;l^3l^>mP2P4P5P6P7P8P9P:P;P<P=P>P?P@PAPBPCPDPEPFPGPHPIPJPKPLPMPNPOPPPQPRPSPTPUPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdP3P0Md]b\b[bXb]bYb^bZo"). Qed.

End X4SF.
End CANSEC1.
