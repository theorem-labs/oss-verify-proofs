(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import ExitSim PropExec CatSim CatExec SeqExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_StreamExec () := "K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions;bv_unsignedC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7CatExec6wbytesC13~~~I47Corelib4Init5Logic2eq00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7CatExec<wbytes_belowC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7CatExecCwrite_to_mem_wbytesC13~~~C47Corelib4Init5Logic8eq_ind_rC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7CatExec<wbytes_aboveC13~~~I47Corelib4Init5Logic2or00I47Corelib4Init5Logic3and00C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:StreamExecBwrite_to_mem_aboveC13~~~K46Stdlib9micromega=RingMicromega7Formula01c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:StreamExecBwrite_to_mem_belowC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7rdn_extC13~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec3rdnC13~~~K47Corelib4Init9Datatypes6option01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SeqExec>rdn_wbytes_hitC13~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7fp_regsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6fp_csrC13~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01K45stdpp9bitvector;definitions2bv01I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_unmapsC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_unmapsC4ELinuxProcessSemantics?LinuxProcessSem5State9eff_zerosC4ELinuxProcessSemantics?LinuxProcessSem3Run;apply_zerosC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_copiesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_copiesC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_writesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_writesC45stdpp9bitvector;definitions6bv_addC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6regupdC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_addiC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4mkstC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6b_npc4C13~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC45stdpp9bitvector;definitions5bv_eqC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec:bv_eqb_neqC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init5Logic4True01I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic5False00C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess@delivered_writesc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:StreamExec?adv_apply_writeC13~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma v_lui_4096 : v_lui 4096 = Z_to_bv 64 4096.
Proof.
ltac2:(KReplay.run1 (kr_t_StreamExec ()) ["WithFP1"] "p;1p;2g0000j16Tg000Nj13Tg0011j12Tg001Oj25Tg0025j24Tg002Oj11Tf0#1#1p=0g0034#0#0#0R0#6R1#3%00#0#0#2,51'4o"). Qed.

(* [comment removed for export] *)
Lemma c_lts_0_0 : c_lts (Z_to_bv 64 0) (Z_to_bv 64 0) = false.
Proof.
ltac2:(KReplay.run1 (kr_t_StreamExec ()) ["WithFP1"] "p;2g0025j20Tg003Yg0049'0o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma write_to_mem_below : forall data mem (buf a : word),
  (bv_unsigned buf + Z.of_nat (length data) <= 2^64)%Z ->
  (bv_unsigned a < bv_unsigned buf)%Z ->
  write_to_mem mem buf data a = mem a.
Proof.
ltac2:(KReplay.run1 (kr_t_StreamExec ()) ["WithFP1"] "h02Hah13Hnwh21ah33bufh44datah53memh61op;1p;2p;3p;6g002Oj10Tg0000j14Tg000Nj12Tg004Yj15Tg0059j1BTg005[j21Tg006Ej2;Tg006ej17Tg007Ej26Tg0011j13Tg007bj28Tg008?j29Tg008[j2:Tg0097j3ATg00:@j3@Tg00:Zj6?Tg00;ij3<Tg00<mj3=Tg00>Cj6>Tg0034#0R0#0#0R1#4#2R2#5%01#0#0R1#4R3#2R4%B2R5[R6f1R7,13R8f3R9,;2#7'6%30%31'8'9f2R1,13,:8P6f4R8f5R37A9f0R0P9O1P3P9O15@5X66P3P8P9P1P7P0E?A<893A=389E>W0W1X24X34W5W4o"). Qed.

(* [comment removed for export] *)
Lemma write_to_mem_above : forall data mem (buf a : word),
  (bv_unsigned buf + Z.of_nat (length data) <= bv_unsigned a)%Z ->
  write_to_mem mem buf data a = mem a.
Proof.
ltac2:(KReplay.run1 (kr_t_StreamExec ()) ["WithFP1"] "h02Hah11ah23bufh34datah43memh51op;1p;2p;3p;5p;6g002Oj10Tg0000j13Tg000Nj12Tg004Yj14Tg0059j1?Tg005[j21Tg006Ej2;Tg006ej15Tg007Ej26Tg008?j27Tg0097j38Tg00:@j39Tg00>aj5:Tg00;ij3>Tg00<mj3=Tg00>Cj6<Tg0034#0#0#0R0#3#2R1#4%00#0#0#3R0#2R2%?1R3[R4f1R5,10f3R6,;1#5'6f0R1,10'7P4f2R0f4R7586P1P0O1P7P0O1593X54P7P6P0P5P1D:A>607A=760E<W0X12X22W4W3o"). Qed.

(* [comment removed for export] *)
Lemma rdn_wtm_out : forall segs data m (buf a : word) n,
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  (bv_unsigned buf + Z.of_nat (length data) <= 2^64)%Z ->
  ((bv_unsigned buf + Z.of_nat (length data) <= bv_unsigned a)%Z \/
   (bv_unsigned a + Z.of_nat n <= bv_unsigned buf)%Z) ->
  rdn segs (write_to_mem m buf data) a n = rdn segs m a n.
Proof.
ltac2:(KReplay.run1 (kr_t_StreamExec ()) ["WithFP1"] "h04__p1h14__x1h24__x2h34__x3h44__x4h52Hdh61mh72Hah87__arithh94__ffh:6__sat1h;6__sat2h<8__varmaph=5__with>4cstrh?5cstr0h@3HnahA3HnbhB2HxhC1ahD3bufhE4datahF1nhG4segshH1xp;1p;2p;3p;4p;6p;5p;7p;8g004Yj1?Tg002Oj16Tg0000j1ETg000Nj1ATg0059j1gTg005[j20Tg0011j1GTg007bj2WTg006Ej23Tg00@0R0j2QTg00;ij3Mj4]Tg008?j21Tg008[j24Tg00@Jj2=Tg00:@j3HTg00@ej1JTg006ej15Tg00AJj2YTg00B2j3XTg00BVj1DTg00C5j2>Tg00C^j3FTg00DGj2VTg00E3j1UTg00ESj3TTg00F3j2BTg00FQj1RTg00Foj4@Tg00GMj1PTg00Gkj1OTg00HVj29Tg00I9j1NTg00I^j6LTg00JBj1STg00Jdj3KTg00KGj2eTg0025j2dTg00Kij2cTg00LUj3bTg00M4j4^Tg007Ej28Tg00Mfj5\Tg00O>j4<Tg00Oij6_Tg00QAj7[Tg00RLj7`Tg00S0j7aTg00STj8ZTf2R1f1R2#5'8f0R3'1p=2%53,82p=fg00T8R4P2g00TVP3C<p=:P2g00U=R5g00U\R6P6g00V<R7P3g00V\F`p=7P1P5P6P6P7P2P3Fap=Cf3R8P5P6P6P7P1P2P3GZp=;1812/13p=Ig00W<#?g0034R9#6R:#6R;#6R<#E#AR=#?%6<#6#6R<#ER>#AR?%g=R@[g00X;10>2%G:RA%G<R<'WRB72310>8RCf5RD,3=;2Bf4RE,0>RFf6RG,3=;2CA2C1F'Qf8RFP8f7RC9MGDPGPEP110>DRH10>3RI'11fHE,4I'=P010>CR0f9RI,3=10>GRH32A2HD0PIPFf:RHP1C]PIP1O15H@P110>FRJ13=H;20f;RKPHPIP8%JCRLg00XZRM%5C'1RNf<,3=RO#JRP%5O,1MRO1YA<RQ14MA11M<14MB[[RR11MARSg00Y8RTAXA<2UW7R<11MB\T^7SRSf>RTPCO1RCP@p-0RBg00YTRAg00Z@RU#DRV#D,>41>4V1>4U5F45F4g00Z_'V%UA3TRU%?ARAP4P41B4EP1%R4C@P21B48C@RV%P4RW%O4RX194;R;%N9,94RY':,7XPXP5P6P6P7PGELR55CX%S6R6PX1949R9194:R:5K4RZ/:;,7XP61:ZY,7XC;C;1eX7R7P3P1g003YRZg00[KR['d1c31=HZ[dAb4M2C^RMb9b<b=X14X24X34X44W01181/=EAI21E1818R2/1E[[^14^24^34^44^0BP310>IR[10>TRTf=#5RZ'8'4PTP[fA,3=#5f?,0>R>PFPGO7b8b6b:b;b?b>D\W5P3O1A20GJPKPHPIP8PDPLPNPPPOPQPRP<PSPCP@PUPAPVPWPXP4P9g00[kRWAK4Y;RYC<,7X9CX5P6PX1:Y:,7XP6P4P9PWP:C<,7XC;C;P7PMb9b<b=X14X24X34X44X0B1432,=EAI8E11418[[^14^24^34^44^0BP311T[PZPTP>P[PFPGO7b8b6b:b;b?b>E_W5P3O1n200100000021100011000WBXH?F[W5WAW@WFXC?XD?W6WEWGo"). Qed.

(* [comment removed for export] *)
Lemma rdn_write_to_mem : forall segs data mem (buf : word),
  (bv_unsigned buf + Z.of_nat (length data) <= 2^64)%Z ->
  rdn segs (write_to_mem mem buf data) buf (length data) = Some data.
Proof.
ltac2:(KReplay.run1 (kr_t_StreamExec ()) ["WithFP1"] "h03Hnwh13bufh24datah33memh41oh54segsp;1p;2p;3p;4p;5p;6g004Yj13Tg002Oj10Tg0000j12Tg000Nj11Tg0059j16Tg005[j2@Tg006Ej25Tg006ej1;Tg007Ej2:Tg0011j14Tg007bj27Tg008?j28Tg0097j39Tg00\Rj4CTg00]Yj2BTg00:@j3ATg00^;j5?Tg00;ij3=Tg00<mj3>Tg00>Cj6<Tg00W<#3g0034#0R0#0#0R1#2#1R2#3R3%01#0#0R1#2R4#1R5%62[R6f0R7,@4f2R4,52#;':%40%41'7'8P6f1R1f3R0594%63f5P7P4f4R8,52CC1B383AX46P8P0P4P1P7D?A=410A>041E<W0X15W3W2W5o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma adv_apply_write : forall regs pc sv mem rom ret buf data,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := sv; ms_resv := None; ms_fcsr := fp_csr;
       ms_mem := mem; ms_rom := rom |}
    (mkEffect ret [(buf, data)] []))
  = mkst (regupd regs 10 ret) (v_addi pc 4) (write_to_mem mem buf data) rom.
Proof.
ltac2:(KReplay.run1 (kr_t_StreamExec ()) ["WithFP1"] "p'0h01Hh12Hch21bh32b1h42b2h51nh63bufh74datah81eh93memh:2pch;4regsh<3reth=3romh>2svi001zp;1p;2p;8p;3p;4p;6p;5g002Oj15Tg00I9j1gTg0000j1?Tg000Nj14Tg00_Lj2fTg0059j1TTg004Yj1[Tg00`8j1ZTg00JBj1YTg00aCj1XTg00bMj81Tg0011j1DTg00cTj3CTg00d7j2ATg00dWj4RTg00E3j1=Tg00ESj3MTg00e7j6LTg00f5j1ITg00fkj19Tg00gjj5;Tg00hZj1@Tg00iZj18Tg00j[j1<Tg00kaj16Tg00l`j1>Tg00m_j1:Tg00n]j17Tg00o[j1HTg010Tj2JTg011Mj1KTg012Ej2FTg013=j1ETg0146j3NTg014oj1OTg015hj2PTg001Oj2WTg016aj3BTg017Fj3STg018Pj2VTg00;ij3UTg019Zj5GTg00:@j30Tg0025j2eTg01:bj1dTg00>Cj6QTg01;lj3cTg005[j23Tg01<Yj3_Tg01==j6^Tg01=Yj2`Tg01>8j1]Tg01>Qj4aTg01?_j2bTg01@Xj1\Tf7R0f6R1#@f5R2f4R3f3R4f2R5#>f1R6f0R7G1p=2g0034#5R8#gR9#?R:%58R8#5R;#5#5#5#?R<#4R='f%T=%?;#4R;#T\=R>%[;R;g003YR?g0049g01AUR@P?P@P7f8RAp,2fxRB#ZRCP0P1%Y=RD%XBREP2P3G1RFP:P=%59#DR9g01B\RG5C:RHP41A=;RIP=P;P5P6CR%=IRJ3M1A==#=RKPKg01C8#=RLg00X;,A=#=RMELRN#I%9FD;%@FRO%8F%<F%6F%>FRP%:F%7FG1n0100000020001RF#9PF%8F%<F%6FPF%:FRQ%HN,JQ%KN'F%EN3N%ON'P%7FG2RF#9PF%8F%D8R8,W<RN5B<PD%6FPF%:F%7FG2PBASAH41V08RFAU256RQP3DG30X2?P=1V18R8P:P=PHP4PAD;RAPAPAPOP0P1PDPPP2P3G1RPP0P1PDPPPQP3G2RPP7PDPDPPPQP3G2PAPCPFPDPDPEPQP3G150@X2=P:P=PHP5P0D;RQPCP8PDPDPEAU367RFP4G1,e@AB<1NRA%d1EQPQPQPQP0PCP1P2PDPEP3P4G1RE#@RCP1P2PD%>ERQP3P4G1RPP1P2PDPPPFP4G2RPPAPDPDPPPFP4G2PBAS0H5P8PFP4DGRF50@eP:P=PHP5P=P;P6P7CR=MIJPKPKPLPMELRM#I%9ED;PC%8E%<E%6EPQ%:E%7EG1RQ#9PQ%8Q%<Q%6QPQ%:QRC%HM,JC%KM'F%EM3N%OM'P%7QG2RQ#9PQ%8Q=B<NPD%6QPQ%:Q%7QG2=0@FRQePQeg00XZRQ=C:GRD9c:HP:PHPD%4:?0HDRNg01D0R<%47RC%46RLg00@J%45?067g00T8RK1345134630[RJ1356135750K%44?056RI[1334133550K\IA_567P6n2001000000120000000W4W3W5PJ^4L^3C^5<P7P:PHPDP6O413:H13:D50KPKP9PKp-0P7g01DNR9g00Y8P9n011000003001000010000X8KPGPQP7E^P91`97b0b1b0W1%]NeCaEQ1bEM#\=0@FeW7X6=X<=X=>W9W>X:=W;o"). Qed.

(* [comment removed for export] *)
Lemma adv_apply_delivered : forall regs pc sv mem rom ret buf data,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := sv; ms_resv := None; ms_fcsr := fp_csr;
       ms_mem := mem; ms_rom := rom |}
    (mkEffect ret (delivered_writes buf data) []))
  = mkst (regupd regs 10 ret) (v_addi pc 4) (write_to_mem mem buf data) rom.
Proof.
ltac2:(KReplay.run1 (kr_t_StreamExec ()) ["WithFP1"] "p'0h01bi001bh11Hh22Hch32b1h42b2h51nh63bufh74datah81eh93memh:2pch;4regsh<4resth=3reth>3romh?2svi011li021zp;1p;2p;8p;6p;3p;5p;4g002Oj14Tg00I9j1iTg0000j1DTg000Nj15Tg00_Lj2hTg0059j1PTg004YR0j1\Tg00`8j1[Tg00JBj1ZTg00aCj1YTg00bMj80Tg01Dkj2FTg00d7j2GTg00E3j1?Tg00e7j6ATg01?_j2UTg01@Xj1LTg0011j1NTg00cTj3VTg017Fj3MTg018Pj2KTg00;ij3ETg019Zj5>Tg00f5j1JTg00fkj16Tg00gjj5<Tg00hZj1BTg00iZj1;Tg00j[j1=Tg00kaj17Tg00l`j1@Tg00m_j1:Tg00n]j18Tg00o[j1ITg010Tj2HTg011Mj1QTg012Ej2RTg013=j1STg0146j3TTg014oj1XTg015hj2WTg001Oj2gTg016aj3CTg0025j2fTg01:bj1cTg00>Cj6OTg01;lj3bTg00:@j33Tg005[j22Tg01<Yj3_Tg01==j6^Tg01=Yj2`Tg01>8j1aTg01>Qj4]Tg00ESj3dTg01F0j8eTg01AUR1f1R2f0R333p=9f7R4f6R5#Bf5R6f4R7f3R8f2R9#@P2P3G0p=1g0034#4R:#iR;#DR<%4:R:#4R=#4#4#4#DR>#5R?'h%P?%D=#5R=#P\?R@%\=RAP0P=f8R0p,2fxRB#[RCP4P5%Z?RD%YBREP6P7G0RFP81F931G??#?RGPGg01C8#?RHg00X;,G?#?RIEA'U#LPB%4;#NR;g01B\RJ5V<RK=M08RL%N:R:,K4RMAE693P7D>'9P3g003YRNg0049PNP1P3PFP<P?PKP8%?=RO,F9PGPGPHPIEARP#J%6FD<%BFRQ%;F%=F%7F%@FRR%:F%8FG0n0100000020001RF#6PF%;F%=F%7FPF%:FRS%IP,HS%QP'R%SP3T%XP'W%8FG1RF#6PF%;F1g>:RP5C>PD%7FPF%:F%8FG1PBPLPMAE69OP7D>'9X0NP?1K5:R:P<P?PKP8P0D<RNPNPNPQP4P5PDPRP6P7G0RRP4P5PDPRP6P7G1RRP3PDPDPRP6P7G1PNPCPMPDPDPEP6P7G0'9X0?P<P?PKP9P4D<RMPCP:PDPDPEP7P8G0,f1AC>5PR1%c5EOPMPMPMP4PCP5P6PDPEP7P8G0RE#BRCP5P6PD%@ERMP7P8G0RNP5P6PDPNP7P8G1RNP1PDPDPNP7P8G1PBAM4K9RNP:P7P8D>'9eP<P?PKP91F2OPGPGPHPIEARI#J%6ED<PC%;E%=E%7EPM%:E%8EG0RM#6PM%;M%=M%7MPM%:MRC%II,HC%QI'R%SI3T%XI'W%8MG1RM#6PM%;M=C>PPD%7MPM%:M%8MG1PBPNP:AE72OP8D>RO'9R:eP:eg00XZR:=V<JRN9b<KP<PKPN%5<?3KNRBg01D0RM%53RD%52RPg00@J%59?323g00T8R>1289128233[RC1292129353>%58?392RH[1278127953>\HA_923P2n2001000000120000000W4W3W5PC^4P^3D^5MP3P<PKPNP2O412<K12<N53>P>P;P>p-0P3g01DNR;g00Y8P;n011020003001000010000X8>PJP:P3E^P;1`;3b1b2b1W2%aBeC]EO1UEI#L/9Oef;f:f9P0P4P5P6Ad=23GeX<AX0=P2P3O2n10110100020120100101W7X6?X=?X>@W9W?X:?W;o"). Qed.
End WithFP1.
