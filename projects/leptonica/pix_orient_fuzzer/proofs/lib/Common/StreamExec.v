(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import ExitSim PropExec CatSim CatExec SeqExec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_StreamExec () := "K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions;bv_unsignedC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib6Common7CatExec6wbytesC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib6Common7CatExec<wbytes_belowC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC59OSSVerify5KrLib6Common7CatExecCwrite_to_mem_wbytesC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib6Common7CatExec<wbytes_aboveC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00I47Corelib4Init5Logic3and00C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundc59OSSVerify5KrLib6Common:StreamExecBwrite_to_mem_aboveC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01c59OSSVerify5KrLib6Common:StreamExecBwrite_to_mem_belowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7rdn_extC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib6Common7SeqExec>rdn_wbytes_hitC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC59OSSVerify5KrLib6Common8PropExec7fp_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6fp_csrC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01K45stdpp9bitvector;definitions2bv01I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_unmapsC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_unmapsC4ELinuxProcessSemantics?LinuxProcessSem5State9eff_zerosC4ELinuxProcessSemantics?LinuxProcessSem3Run;apply_zerosC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_copiesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_copiesC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_writesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_writesC45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib6Common8PropExec6regupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6v_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6b_npc4C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC45stdpp9bitvector;definitions5bv_eqC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notC59OSSVerify5KrLib6Common8PropExec:bv_eqb_neqC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcC45stdpp9bitvector;definitions4BvWfI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init5Logic4True01I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic5False00C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess@delivered_writesc59OSSVerify5KrLib6Common:StreamExec?adv_apply_writeC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

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
ltac2:(KReplay.run1 (kr_t_StreamExec ()) ["WithFP1"] "h02Hah13Hnwh21ah33bufh44datah53memh61op;1p;2p;3p;6g002Oj10Tg0000j14Tg000Nj12Tg004Yj15Tg0059j1BTg005[j21Tg006Ej2;Tg006ej17Tg007Ej26Tg0011j13Tg007bj28Tg008?j29Tg008[j2:Tg0097j3ATg00:1j3@Tg00:Kj6?Tg00;Kj3<Tg00<Oj3=Tg00=Vj6>Tg0034#0R0#0#0R1#4#2R2#5%01#0#0R1#4R3#2R4%B2R5[R6f1R7,13R8f3R9,;2#7'6%30%31'8'9f2R1,13,:8P6f4R8f5R37A9f0R0P9O1P3P9O15@5X66P3P8P9P1P7P0E?A<893A=389E>W0W1X24X34W5W4o"). Qed.

(* [comment removed for export] *)
Lemma write_to_mem_above : forall data mem (buf a : word),
  (bv_unsigned buf + Z.of_nat (length data) <= bv_unsigned a)%Z ->
  write_to_mem mem buf data a = mem a.
Proof.
ltac2:(KReplay.run1 (kr_t_StreamExec ()) ["WithFP1"] "h02Hah11ah23bufh34datah43memh51op;1p;2p;3p;5p;6g002Oj10Tg0000j13Tg000Nj12Tg004Yj14Tg0059j1?Tg005[j21Tg006Ej2;Tg006ej15Tg007Ej26Tg008?j27Tg0097j38Tg00:1j39Tg00>4j5:Tg00;Kj3>Tg00<Oj3=Tg00=Vj6<Tg0034#0#0#0R0#3#2R1#4%00#0#0#3R0#2R2%?1R3[R4f1R5,10f3R6,;1#5'6f0R1,10'7P4f2R0f4R7586P1P0O1P7P0O1593X54P7P6P0P5P1D:A>607A=760E<W0X12X22W4W3o"). Qed.

(* [comment removed for export] *)
Lemma rdn_wtm_out : forall segs data m (buf a : word) n,
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  (bv_unsigned buf + Z.of_nat (length data) <= 2^64)%Z ->
  ((bv_unsigned buf + Z.of_nat (length data) <= bv_unsigned a)%Z \/
   (bv_unsigned a + Z.of_nat n <= bv_unsigned buf)%Z) ->
  rdn segs (write_to_mem m buf data) a n = rdn segs m a n.
Proof.
ltac2:(KReplay.run1 (kr_t_StreamExec ()) ["WithFP1"] "h04__p1h14__x1h24__x2h34__x3h44__x4h52Hdh61mh72Hah87__arithh94__ffh:6__sat1h;6__sat2h<8__varmaph=5__with>4cstrh?5cstr0h@3HnahA3HnbhB2HxhC1ahD3bufhE4datahF1nhG4segshH1xp;1p;2p;3p;4p;6p;5p;7p;8g004Yj1?Tg002Oj16Tg0000j1ETg000Nj1ATg0059j1gTg005[j20Tg0011j1GTg007bj2WTg006Ej23Tg00?4R0j2QTg00;Kj3Mj4]Tg008?j21Tg008[j24Tg00?Nj2=Tg00:1j3HTg00?ij1JTg006ej15Tg00@Nj2YTg00A6j3XTg00AZj1DTg00B9j2>Tg00Bbj3FTg00CKj2VTg00D7j1UTg00DWj3TTg00E7j2BTg00EUj1RTg00F3j4@Tg00FQj1PTg00Foj1OTg00GZj29Tg00H=j1NTg00Hbj6LTg00IFj1STg00Ihj3KTg00JKj2eTg0025j2dTg00Jmj2cTg00KYj3bTg00L8j4^Tg007Ej28Tg00Ljj5\Tg00N3j4<Tg00N^j6_Tg00Ogj7[Tg00Pcj7`Tg00QGj7aTg00Qkj8ZTf2R1f1R2#5'8f0R3'1p=2%53,82p=fg00ROR4P2g00RmP3C<p=:P2g00STR5g00T3R6P6g00TSR7P3g00U3F`p=7P1P5P6P6P7P2P3Fap=Cf3R8P5P6P6P7P1P2P3GZp=;1812/13p=Ig00US#?g0034R9#6R:#6R;#6R<#E#AR=#?%6<#6#6R<#ER>#AR?%g=R@[g00VR10>2%G:RA%G<R<'WRB72310>8RCf5RD,3=;2Bf4RE,0>RFf6RG,3=;2CA2C1F'Qf8RFP8f7RC9MGDPGPEP110>DRH10>3RI'11fHE,4I'=P010>CR0f9RI,3=10>GRH32A2HD0PIPFf:RHP1C]PIP1O15H@P110>FRJ13=H;20f;RKPHPIP8%JCRLg00W1RM%5C'1RNf<,3=RO#JRP%5O,1MRO1YA<RQ14MA11M<14MB[[RR11MARSg00WORTAXA<2UW7R<11MB\T^7SRSf>RTPCO1RCP@p-0RBg00WkRAg00XWRU#DRV#D,>41>4V1>4U5F45F4g00Y6'V%UA3TRU%?ARAP4P41B4EP1%R4C@P21B48C@RV%P4RW%O4RX194;R;%N9,94RY':,7XPXP5P6P6P7PGELR55CX%S6R6PX1949R9194:R:5K4RZ/:;,7XP61:ZY,7XC;C;1eX7R7P3P1g003YRZg00YbR['d1c31=HZ[dAb4M2C^RMb9b<b=X14X24X34X44W01181/=EAI21E1818R2/1E[[^14^24^34^44^0BP310>IR[10>TRTf=#5RZ'8'4PTP[fA,3=#5f?,0>R>PFPGO7b8b6b:b;b?b>D\W5P3O1A20GJPKPHPIP8PDPLPNPPPOPQPRP<PSPCP@PUPAPVPWPXP4P9g00ZBRWAK4Y;RYC<,7X9CX5P6PX1:Y:,7XP6P4P9PWP:C<,7XC;C;P7PMb9b<b=X14X24X34X44X0B1432,=EAI8E11418[[^14^24^34^44^0BP311T[PZPTP>P[PFPGO7b8b6b:b;b?b>E_W5P3O1n200100000021100011000WBXH?F[W5WAW@WFXC?XD?W6WEWGo"). Qed.

(* [comment removed for export] *)
Lemma rdn_write_to_mem : forall segs data mem (buf : word),
  (bv_unsigned buf + Z.of_nat (length data) <= 2^64)%Z ->
  rdn segs (write_to_mem mem buf data) buf (length data) = Some data.
Proof.
ltac2:(KReplay.run1 (kr_t_StreamExec ()) ["WithFP1"] "h03Hnwh13bufh24datah33memh41oh54segsp;1p;2p;3p;4p;5p;6g004Yj13Tg002Oj10Tg0000j12Tg000Nj11Tg0059j16Tg005[j2@Tg006Ej25Tg006ej1;Tg007Ej2:Tg0011j14Tg007bj27Tg008?j28Tg0097j39Tg00Zij4CTg00[aj2BTg00:1j3ATg00\Cj5?Tg00;Kj3=Tg00<Oj3>Tg00=Vj6<Tg00US#3g0034#0R0#0#0R1#2#1R2#3R3%01#0#0R1#2R4#1R5%62[R6f0R7,@4f2R4,52#;':%40%41'7'8P6f1R1f3R0594%63f5P7P4f4R8,52CC1B383AX46P8P0P4P1P7D?A=410A>041E<W0X15W3W2W5o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_StreamExec ()) ["WithFP1"] "p'0h01Hh12Hch21bh32b1h42b2h51nh63bufh74datah81eh93memh:2pch;4regsh<3reth=3romh>2svi001zp;1p;2p;8p;3p;4p;6p;5g002Oj15Tg00H=j1hTg0000j1@Tg000Nj14Tg00]Ej2gTg0059j1TTg004Yj1[Tg00^1j1ZTg00IFj1YTg00^mj1XTg00_hj81Tg0011j1FTg00`oj3>Tg00aRj2BTg00b2j4STg00D7j1=Tg00DWj3QTg00bRj6PTg00cPj1KTg00dFj19Tg00eEj5<Tg00f5j1ATg00g5j1:Tg00h6j1;Tg00i<j16Tg00j;j1?Tg00k:j17Tg00l8j18Tg00m6j1JTg00moj2ITg00nhj1LTg00o`j2HTg010Xj1GTg011Qj3MTg012Jj1NTg013Cj2OTg001Oj2WTg014<j3DTg014aj3ETg015\j2VTg00;Kj3UTg016Wj5CTg00:1j30Tg0025j2fTg017Pj1eTg00=Vj6RTg018Kj3cTg005[j22Tg0198j3_Tg019\j6^Tg01:8j2`Tg01:Wj1]Tg01;0j4aTg01;oj2bTg01<hj1\Tg01=ej2dTf7R0f6R1#Af5R2f4R3f3R4f2R5#?f1R6f0R7G1p=3g0034#5R8#hR9#@R:%58R8#5R;#5#5#5#@R<#4R='g%T=%@;#4R;#T\=R>%[;R;g003YR?g0049g01>HR@P?P@P7f8RAp,2fxRB#ZRCP0P1%Y=RD%XBREP2P3G1RFP:P=%59#FR9g01?ORG5>:RHP41B=;RIP=P;P5P6CS%=IRJ3Q1B==#=RKPKg01?k#=RLg00VR,B=#=RMEPRN#K%9FD<%AFRO%:F%;F%6F%?FRP%7F%8FG1n0100000020001RF#9PF%:F%;F%6FPF%7FRQ%JN,IQ%LN'H%GN3M%NN'O%8FG3RF#9PF%:F%F8R8,W<RN5D<PD%6FPF%7F%8FG3PBAEAH41V08RFAU256RQP3DC30X2?P=1V18R8P:P=PHP4PAD<RAPAPAPOP0P1PDPPP2P3G1RPP0P1PDPPPQP3G3RPP7PDPDPPPQP3G3PAPCPFPDPDPEPQP3G150@X2=P:P=PHP5P0D<RQPCP8PDPDPEAU367RFP4G1,f@AD<1NRA%e1ERPQPQPQP0PCP1P2PDPEP3P4G1RE#ARCP1P2PD%?ERQP3P4G1RPP1P2PDPPPFP4G3RPPAPDPDPPPFP4G3PBAE0H5P8PFP4DCRP50@eP:P=PHP5P=P;P6P7CS=QIJPKPKPLPMEPRM#K%9ED<PC%:E%;E%6EPQ%7E%8EG1RQ#9PQ%:Q%;Q%6QPQ%7QRC%JM,IC%LM'H%GM3M%NM'O%8QG3RQ#9PQ%:Q=D<NPD%6QPQ%7Q%8QG3=0@PRPePPeg00W1RP=>:GRQ9c:HP:PHPQ%4:?0HQRDg01@cRN%47R<%46RCg00?N%45?067g00RORL1245124630[RK1256125750L%44?056RJ[1234123550L\JA_567P6n2001000000120000000W4W3W5PK^4C^3<^5NP7P:PHPQP6O412:H12:Q50LPLP9PLp-0P7g01AARQg00WOPQn011000003001000010000X8LPGPPP7E^PQ1`Q7b0b1b0W1%]DeCaER1bEM#\PBPG1d:9d9>:9=E05P8PFP4DC50@eW7X6=X<=X=>W9W>X:=W;o"). Qed.

(* [comment removed for export] *)
Lemma adv_apply_delivered : forall regs pc sv mem rom ret buf data,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := sv; ms_resv := None; ms_fcsr := fp_csr;
       ms_mem := mem; ms_rom := rom |}
    (mkEffect ret (delivered_writes buf data) []))
  = mkst (regupd regs 10 ret) (v_addi pc 4) (write_to_mem mem buf data) rom.
Proof.
ltac2:(KReplay.run1 (kr_t_StreamExec ()) ["WithFP1"] "p'0h01bi001bh11Hh22Hch32b1h42b2h51nh63bufh74datah81eh93memh:2pch;4regsh<4resth=3reth>3romh?2svi011li021zp;1p;2p;8p;6p;3p;5p;4g002Oj14Tg00H=j1iTg0000j1DTg000Nj15Tg00]Ej2hTg0059j1PTg004YR0j1\Tg00^1j1[Tg00IFj1ZTg00^mj1YTg00_hj80Tg01A^j2FTg00aRj2GTg00D7j1?Tg00bRj6ATg01;oj2UTg01<hj1LTg0011j1NTg00`oj3VTg014aj3MTg015\j2KTg00;Kj3ETg016Wj5>Tg00cPj1JTg00dFj16Tg00eEj5<Tg00f5j1BTg00g5j1;Tg00h6j1=Tg00i<j17Tg00j;j1@Tg00k:j1:Tg00l8j18Tg00m6j1ITg00moj2HTg00nhj1QTg00o`j2RTg010Xj1STg011Qj3TTg012Jj1XTg013Cj2WTg001Oj2gTg014<j3CTg0025j2fTg017Pj1cTg00=Vj6OTg018Kj3bTg00:1j33Tg005[j22Tg0198j3_Tg019\j6^Tg01:8j2`Tg01:Wj1aTg01;0j4]Tg00DWj3dTg01Bcj8eTg01>HR1f1R2f0R333p=9f7R4f6R5#Bf5R6f4R7f3R8f2R9#@P2P3G0p=1g0034#4R:#iR;#DR<%4:R:#4R=#4#4#4#DR>#5R?'h%P?%D=#5R=#P\?R@%\=RAP0P=f8R0p,2fxRB#[RCP4P5%Z?RD%YBREP6P7G0RFP81F931G??#?RGPGg01?k#?RHg00VR,G?#?RIEA'U#LPB%4;#NR;g01?ORJ5V<RK=M08RL%N:R:,K4RMAE693P7D>'9P3g003YRNg0049PNP1P3PFP<P?PKP8%?=RO,F9PGPGPHPIEARP#J%6FD<%BFRQ%;F%=F%7F%@FRR%:F%8FG0n0100000020001RF#6PF%;F%=F%7FPF%:FRS%IP,HS%QP'R%SP3T%XP'W%8FG1RF#6PF%;F1g>:RP5C>PD%7FPF%:F%8FG1PBPLPMAE69OP7D>'9X0NP?1K5:R:P<P?PKP8P0D<RNPNPNPQP4P5PDPRP6P7G0RRP4P5PDPRP6P7G1RRP3PDPDPRP6P7G1PNPCPMPDPDPEP6P7G0'9X0?P<P?PKP9P4D<RMPCP:PDPDPEP7P8G0,f1AC>5PR1%c5EOPMPMPMP4PCP5P6PDPEP7P8G0RE#BRCP5P6PD%@ERMP7P8G0RNP5P6PDPNP7P8G1RNP1PDPDPNP7P8G1PBAM4K9RNP:P7P8D>'9eP<P?PKP91F2OPGPGPHPIEARI#J%6ED<PC%;E%=E%7EPM%:E%8EG0RM#6PM%;M%=M%7MPM%:MRC%II,HC%QI'R%SI3T%XI'W%8MG1RM#6PM%;M=C>PPD%7MPM%:M%8MG1PBPNP:AE72OP8D>RO'9R:eP:eg00W1R:=V<JRN9b<KP<PKPN%5<?3KNRBg01@cRM%53RD%52RPg00?N%59?323g00ROR>1289128233[RC1292129353>%58?392RH[1278127953>\HA_923P2n2001000000120000000W4W3W5PC^4P^3D^5MP3P<PKPNP2O412<K12<N53>P>P;P>p-0P3g01AAR;g00WOP;n011020003001000010000X8>PJP:P3E^P;1`;3b1b2b1W2%aBeC]EO1UEI#L/9Oef;f:f9P0P4P5P6Ad=23GeX<AX0=P2P3O2n10110100020120100101W7X6?X=?X>@W9W?X:?W;o"). Qed.
End WithFP1.
