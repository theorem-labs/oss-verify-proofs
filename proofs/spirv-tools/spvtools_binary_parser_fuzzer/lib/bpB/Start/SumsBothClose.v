(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BsImages.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BStoreOk BHoare BAgentLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BxSymExec3 BxSymExec3Sound BxSymRun3 BothPlanCore BothPlan BothPlanSound.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothPopFree BothPlanSoundSums SumsBothSpecs BothIStrncpy BothPopFreeBoth BsPlanImages.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_SumsBothClose () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C46Stdlib5Lists4List2InK47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01I47Corelib4Init5Logic2eq00C7ARocqVerifyHarness?AgentSubmission3bpB5Start:BxSymExec33AX24ridxK47Corelib4Init9Datatypes3nat02I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib4Init5Logic6eq_indI47Corelib4Init5Logic5False00I47Corelib4Init9Datatypes3nat00C7ARocqVerifyHarness?AgentSubmission3bpB5Start8BothPlan2AP<caller_savedK47Corelib7Numbers7BinNums8positive03C6ARocqVerifyHarness?AgentSubmission3bpB5Start<BothIStrncpy=istrncpy_clobK47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC7ARocqVerifyHarness?AgentSubmission3bpB5Start8BothPlan2AP8x_sealedC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3powC6ARocqVerifyHarness?AgentSubmission3bpB2HF6BHoare6ret_okC6ARocqVerifyHarness?AgentSubmission3bpB2HF9BPropExec4getrC6ARocqVerifyHarness?AgentSubmission3bpB2HF9BPropExec7seg_romC6ARocqVerifyHarness?AgentSubmission3bpB5Start<BothIStrncpyDasan_istrncpy_sealedI6ARocqVerifyHarness?AgentSubmission3bpB2HF7BCatSim6msteps00C6ARocqVerifyHarness?AgentSubmission3bpB2HF6BHoare:regs_agreeI47Corelib4Init5Logic2ex00C7ARocqVerifyHarness?AgentSubmission3bpB5Start8BothPlan2AP:x_istrncpyC6ARocqVerifyHarness?AgentSubmission3bpB2HF8BCatExec6wbytesC7ARocqVerifyHarness?AgentSubmission3bpB5StartABothPlanSoundSums4APSX7kept_okI47Corelib4Init9Datatypes4list00C45stdpp9bitvector;definitions5bv_eqC6ARocqVerifyHarness?AgentSubmission3bpB5Start=SumsBothSpecsEkept_ok_of_regs_agreeC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C7ARocqVerifyHarness?AgentSubmission3bpB5StartABothPlanSoundSums4APSX=istrncpy_specC6ARocqVerifyHarness?AgentSubmission3bpB2HF9BPropExec4mkstC6ARocqVerifyHarness?AgentSubmission3bpB2HF9BPropExec;dfp_defaultC6ARocqVerifyHarness?AgentSubmission3bpB5Start<BothIStrncpyCasan_istrncpy_entryC6ARocqVerifyHarness?AgentSubmission3bpB5Start<BothIStrncpyDstrncpy_sealed_bytesC6ARocqVerifyHarness?AgentSubmission3bpB5Start<BsPlanImages5ASEGSI47Corelib7Numbers7BinNums1Z00C6ARocqVerifyHarness?AgentSubmission3bpB5Start8BsImages6ASAN_HI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C5ARocqVerifyHarness@ProcessOversightVTgt_spvtools_binary_parser_fuzzer_both1M?loaded_segmentsC7ARocqVerifyHarness?AgentSubmission3bpB5StartABothPlanSoundSums4APSX<SEALED_BYTESI47Corelib7Numbers7BinNums1N00c6ARocqVerifyHarness?AgentSubmission3bpB5Start=SumsBothCloseAistrncpy_clob_subI47Corelib7Numbers7BinNums8positive00I47Corelib4Init5Logic4True00C6ARocqVerifyHarness?AgentSubmission3bpB5Start?BothPopFreeBothAasan_popfree_specC7ARocqVerifyHarness?AgentSubmission3bpB5StartABothPlanSoundSums4APSXEnode_x_sound_XIMemsetC6ARocqVerifyHarness?AgentSubmission3bpB5Start<BsPlanImages7asan_wxC6ARocqVerifyHarness?AgentSubmission3bpB5Start<BsPlanImages<asan_in_hullC6ARocqVerifyHarness?AgentSubmission3bpB5Start<BsPlanImages<asan_hull_okC6ARocqVerifyHarness?AgentSubmission3bpB5Start=SumsBothSpecsFasan_fill_spec_imemsetC7ARocqVerifyHarness?AgentSubmission3bpB5StartABothPlanSoundSums4APSXDnode_x_sound_XMemsetC6ARocqVerifyHarness?AgentSubmission3bpB5Start=SumsBothSpecsEasan_fill_spec_memsetC7ARocqVerifyHarness?AgentSubmission3bpB5StartABothPlanSoundSums4APSXEnode_x_sound_XIMemcpyC6ARocqVerifyHarness?AgentSubmission3bpB5Start<BsPlanImages<asan_segs_wrC6ARocqVerifyHarness?AgentSubmission3bpB5Start=SumsBothSpecsFasan_copy_spec_imemcpyC7ARocqVerifyHarness?AgentSubmission3bpB5StartABothPlanSoundSums4APSXDnode_x_sound_XMemcpyC6ARocqVerifyHarness?AgentSubmission3bpB5Start=SumsBothSpecsEasan_copy_spec_memcpyC7ARocqVerifyHarness?AgentSubmission3bpB5StartABothPlanSoundSums4APSXGnode_x_sound_XMemIsZeroC6ARocqVerifyHarness?AgentSubmission3bpB5Start=SumsBothSpecs=asan_miz_specC7ARocqVerifyHarness?AgentSubmission3bpB5StartABothPlanSoundSums4APSXFnode_x_sound_XIStrncpyc6ARocqVerifyHarness?AgentSubmission3bpB5Start=SumsBothCloseBasan_istrncpy_specC7ARocqVerifyHarness?AgentSubmission3bpB5StartABothPlanSoundSums4APSXEnode_x_sound_XPopFreec6ARocqVerifyHarness?AgentSubmission3bpB5Start=SumsBothCloseBasan_popfree_spec'C7ARocqVerifyHarness?AgentSubmission3bpB5StartABothPlanSoundSums4APSXDnode_fillfz_sound_of".
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma istrncpy_clob_sub : forall r, In r istrncpy_clob -> In (AX2.ridx r) AP.caller_saved.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsBothClose ()) [] "h01Hh11rp;1p;3p;2p;6g0000j1CTg000Uj1;Tg001:j1GTg001Xj1FTg002;j3ETg002Rj1?Tg0030j3>Tg003Sj34Tg003mj16Tg004oj12Tg005NR0j21Tg005hj2@Tg006Bj3<Tg006\j3ATg0076j6=Tf2R1f1R2f0R334g007RR4'1p=9f3R5?412/13p=7g007oR6g008N7E3p=8A4623p=0%23#2p=:1134p=BA4612/13p=Df4R7=465A4612/13'1p=3AA1239A75p=5g009UR8#C#;R9#GR:#FR;g00::9E;3P0%;9#?g00;CR95>:R<=4;2P;%;8R8#CR=#C#?=>:9R>P2P;%;=#?=>:9R=P2P;%;8R8#C#?=>:9R?P2%;8#?=>:9R9=9;2C7C7C7%61#8P3A4;<1P;P<%63#8X1;R2g00;_#2R:%6<R<'0%::#:R8/0<R@%28RA/0<RB%2ARC/0<RD%2C#:RE/0<RF%2ERG/0<RH%2GRIP<%2IRJP<%2JRKP<%2KRLP<%2LRMP<%2MRNP<%2N#:#:#:#:#:ROP<%2ORPP<%2PRQ%2QRR/0<#B7D<D3D3D3D3RS'1RT'1RU'1RV'1RW'1P@PWPBPVPDPU1@6<9<HS9AFTD5D5%8<eP5P3E=W0P3O1P;P>P1P;P=P1P;P?P1A9;91C7C7C7P0A4;>5P;P=P5P;P?P5A9;95C7C7%67#8P3A4;>7P;P>P2%6>R>,0:108>R510A>R110C>R<10E>RT10G>RF10I>RSPJP>PKP>PLP>PMP>PNP>POP>PPP>PQP>10R>#BD3D3D3D3RH'1RU'1RD'1RV'1RB'1RW'1P5PWP1PBP<PVPTPDPFPU1@6>9<SHD5D5D5%8>ef5R>P3E=W0P3O1P;P=P7P;P?P7A9;97C7C7P0A4;=>P;P?P>A9;9>C7f6R>#6#8P3A4;=>P;P=P2%6=R=,0:108=R710A=RH10C=RS10E=RU10G=RF10I=RD10J=RTPKP=PLP=PMP=PNP=POP=PPP=10R=#B9DQ=D3D3D3RV'1R<'1RB'1R1'1RW'1R5'1R@'1P7P@PHP5PSPWPUP1PFPB1@6=9<TV9AD<D5D5D5%8=ef7R=P3E=W0P3O1P;P?P>A9;9>C7P0A4;?=A9;9=f8R=#6#8P3A4;?=P;P?P2%6?R?,0:108?R>10A?R<10C?RD10E?RV10G?RT10I?RB10J?RF10K?R1PLP?PMP?PNP?POP?PPP?PQP?10R?#BD3D3D3RU'1RW'1RS'1R5'1RH'1R@'1R7'1RX'1P>PXP<P7PDP@PVPHPTP5PBPSPFPW1@6?9<1UD5D5D5D5%8?ef9R?P3E=W0P3O1A9;9=P0A4;9?P4f:R?#6#8P3A4;9?P;P9P2%69R9,0:1089R810A9RA10C9RC10E9RE10G9RG10I9RI10J9RJ10K9RK10L9RLPMP9PNP9POP9PPP910R9#B9DQ9D3D3RQ'1RR'1RP'1RO'1RN'1RM'1R:'1R2'1R;'1P8P;PAP2PCP:PEPMPGPNPIPOPJPP1@699<LQ9AKRD5D5D5D5%89ef;P3E=W0P3O1P4f<#6#8P3n010000000X04P3O1n200100000021100010000W0P3O1n200100000021100011000W0P3O1n200100000021100011000W0P3O1n200100000021100011000W0P3O1n200100000021100011000W0W1o"). Qed.

Lemma asan_istrncpy_spec : APSX.istrncpy_spec ASEGS (AP.x_istrncpy ASAN_H) (AP.x_sealed ASAN_H).
Proof.
ltac2:(KReplay.run1 (kr_t_SumsBothClose ()) [] "p'0h01Hh12H0h25regs'h31eh42b1h52b2h63dsth71nh83Hagh95Hdisjh:3Hmsh;5Hnoneh<3Hnwh=4Hreth>3Hsth?2R1h@3R10hA3R11hB3R12hC1bi001bhD1ihE1lhF4mem0hG1rhH4regshI3rethJ1xi011xi028bv_is_wfi03;bv_unsignedi041pi051zp;1p;2p;3p;4p;>p;6p;5g0000j17Tg001:j1LTg001XR0j1:Tg00<>j1RTg000Uj14Tg00<`j2]Tg00=Lj1YTg00>Oj2JTg002Rj15Tg00>kj2HTg00?Hj2MTg00?dR1j26Tg00@?j2ETg00@ej1fTg003Sj32Tg004oj11Tg00AGj4WTg00BGj2<Tg00C1j2VTg005NR2j2?Tg00CNj1UTg00DGj28Tg00EAj1TTg00F>l>STg00GNj3ATg002;j3GTg00HJj3BTg00IGR3j2ITg00Iaj1QTg00Jfj3@Tg00Kaj2FTg00Lnj1eTg005hj2PTg00MNj3dTg0076j69Tg00N2j5cTg00ODj2bTg00Ocj1KTg00P<j1aTg00P\j3DTg00Q<j4NTg00QWj4^Tg00R1j3_Tg0030j3`Tg00SDj5OTf0R4#1#1p=\%14#1#1#1p=[%14#1#1#1#1#1#1#1p=Z%14#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=X%14#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0f1R5g00;CR67`4p=;g00T>R7f2R8g00U?R9P5P4DOp=Cg00VNR:9@54p==P7f3R7P8P5P4DOp=3g00W^R;?A54p=>g009UR<#7R=#7R>#7R?#7#7#7R@#LRA#:RB%L?#:R?#RRC]J%4=RD#LRE/]BRFg00X_RGg00Y=RH#YRI/J4%4>#5,HIR>,M4'6f5RJ1EA5O1%f?52C[]Dg00Z;P;f4RCP7g00;_#1#\#[#Z#X#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0CWg00Z[321<AC%4<RK#4RL#4RM#4#4#4#4#4#4#4#4#5RN'H%5=%5@'V'M1<AJR@/HN/JI1J>@'?%UCf6R@%5<,;E'8=2BJf7R<%7D#5,;ER>'8f8R=52B%4D#5,;ERD,8=1EAI52Bf9RO%7KRK#7#5,;ERP'81EAN52Bf<RNf;RQ%T;RRf:RSPOP=P<P@PJPCP7P8P5P4M>Sg00[;ROf=RT=CQRP4PS1=TNPRC33A%:ERSg00::RU9GS4WGRV?BQ4'6X2F,IFP3PFf>R3=CNRP4PQ1=3TPRC35AOABVN4'6X2FPT%QHRH,EARWf?RXPRC3P4PNg00\YRN9@X3PRC3'>1FT4184>RY=2B3'6'6X2F,IFP4f@RZ=C3RP4PT1=ZXPRC35AOABV34'6P1fART=CXRP5P31=TZPRC35AOABVX5PTPWfCRXPRC3P4PZfBR3=@XNPRC3'>1FT4A2BY3'6'6X2F,IFP4ACTXRP7PZ1=X3PRC35AOABV3CPFfDRVPWfFROPRC3P4PXfERZ=@ONPRC3'>1FV4A2BYZ'6'6X2FPJPXPWPZPRC3PJP3A@ZVNPRC3'>1FXJR318J>=2BVRY'6%e?R?/PNA2?:NP?P:PZPWfGR:PRC3P<PVA@:O4PRC3'>XE?g00]kR?%:4R<%:5RTP1%:8?2541<781<7552GR1[1<851<8452G%:7?285[R[%:C?278\1Ad854P4n2001000000120000000W5W4W7P[^5T^4<^7?P4PAP9PW1<AW,PGO4b0A2B9WPBP9POP4fHROPRC3P=PZ1=O:PRC3'>XCBP7PWP4E9b0PNP4E9b0P3PYPUPXPJg00^IP4DcPB18X>18@>=2B4X6BP4P>A2SD>R@A2SP>RX%4K#5,;ERK=2S>RJ%7L#5,;ERL=2S>RY%5M,;ERM=2S>R3g007RRN'?RW'?R7'?RR'?RO'?R:P2P@POPNP4PSPDP0PEp-0RZP4PGPZP5PNg00_WR=PZP4g00`<R9PNPNn011040003100001000000RAPNn011050003001010410104n101100000120103102X3SR?P6P>P4E9PN1bN4R<b1X0@P4O1P2PXPRPNP4PSPPP0PEPZP4PGPZP5PNP=PZP4PNP=PZP4PNP9PNn011040003100001000000PNn011040003101041010400PNn011050003001010410104n101100000120103102X3SP6P>P4E9PNP<b1X0XP4O1P2PJP7PNP4PSPKP?P6P>P4E9PNP<b1X0JP4O1P2PYPWPNP4PSPLP0PEPZP4PGPZP5PNP=PZP4PNP=PZP4PAPNPNn011040003101041010400PNn011040003101041010400PNn011050003001010410104n101100000120103102X3SP6P>P4E9PNP<b1X0YP4O1P2P3PNPNP4PSPMP?P6P>P4E9PNP<b1X03P4O1PNPNP4n010000000X0NP4O1n200100000021000010000X1WP4O1n200100000021000010000X17P4O1n200100000021000011000X1RP4O1n200100000021000011000X1OP4O1n200100000021000011000W1%K:e%aS9DSM9DSL9DSK9DSP9DSD9GS>#KeAGS>U#KeO2PVPQE9CNCNC^W8W:P5P4O2n2001000000121000000W0X2FP5P4O2n2001000000121101000b3WBWAW@W?W=W9W<W>W;XIBWHX6BWFA_;HIeo"). Qed.

Lemma asan_popfree_spec' : popfree_spec ASEGS (AP.x_popfree ASAN_H).
Proof.
ltac2:(KReplay.run1 (kr_t_SumsBothClose ()) [] "g00`Xo"). Qed.

Section AsanNodes.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> AP.CEIL <= bv_unsigned a.
Hypothesis argH_sp0 : forall E (a : word), argH E a = true -> bv_unsigned (AX2.edenot E AP.e_sp0_early) <= bv_unsigned a.
Hypothesis E_SP0 : AP.expr_vars_lt nx0 AP.e_sp0_early = true.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Variable FS0 : Fs.Fs.

#[local] Notation XSTMT := (APS.x_stmt ASEGS ASAN_H nx0 LIMIT SINV argH FS0).

#[local] Ltac close_with NODE SPEC :=
  eapply NODE; try eassumption;
  first [ exact asan_wx | exact asan_in_hull | exact asan_res_len | exact asan_hull_ok | exact asan_segs_wr | exact SPEC | idtac ].

Theorem asan_node_x_sound_XIMemset : XSTMT AP.XIMemset.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsBothClose ()) ["AsanNodes"] "p;@g00ahl@0Tg00W^g00Y=f0f1g00cCg00dFg00eNf2f3f4f5f6f7f8f9g00fVM@0p=1p,3nx0p,5LIMITp,4SINVp,4argHp,9argH_highp,5E_SP0p,:argH_agreep,:SINV_framep,:SINV_agreep,3FS0M:1o"). Qed.
Theorem asan_node_x_sound_XMemset : XSTMT AP.XMemset.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsBothClose ()) ["AsanNodes"] "p;@g00gil@0Tg00W^g00Y=f0f1g00cCg00dFg00eNf2f3f4f5f6f7f8f9g00iCM@0p=1p,3nx0p,5LIMITp,4SINVp,4argHp,9argH_highp,5E_SP0p,:argH_agreep,:SINV_framep,:SINV_agreep,3FS0M:1o"). Qed.
Theorem asan_node_x_sound_XIMemcpy : XSTMT AP.XIMemcpy.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsBothClose ()) ["AsanNodes"] "p;Ag00jUlA0Tg00W^g00Y=f0f1g00cCg00dFg00eNf2f3f4f5f6f7f8f9g00l0g00m8MA0p=1p,3nx0p,5LIMITp,4SINVp,4argHp,9argH_highp,5E_SP0p,:argH_agreep,:SINV_framep,:SINV_agreep,3FS0M:1o"). Qed.
Theorem asan_node_x_sound_XMemcpy : XSTMT AP.XMemcpy.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsBothClose ()) ["AsanNodes"] "p;Ag00nKlA0Tg00W^g00Y=f0f1g00cCg00dFg00eNf2f3f4f5f6f7f8f9g00l0g00oeMA0p=1p,3nx0p,5LIMITp,4SINVp,4argHp,9argH_highp,5E_SP0p,:argH_agreep,:SINV_framep,:SINV_agreep,3FS0M:1o"). Qed.
Theorem asan_node_x_sound_XMemIsZero : XSTMT AP.XMemIsZero.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsBothClose ()) ["AsanNodes"] "p;@g0117l@0Tg00W^g00Y=f0f1g00cCg00dFg00eNf2f3f4f5f6f7f8f9g012TM@0p=1p,3nx0p,5LIMITp,4SINVp,4argHp,9argH_highp,5E_SP0p,:argH_agreep,:SINV_framep,:SINV_agreep,3FS0M:1o"). Qed.
Theorem asan_node_x_sound_XIStrncpy : XSTMT AP.XIStrncpy.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsBothClose ()) ["AsanNodes"] "p;@g013^l@0Tg00W^g00Y=f0f1g00cCg00dFg00eNf2f3f4f5f6f7f8f9g015:M@0p=1p,3nx0p,5LIMITp,4SINVp,4argHp,9argH_highp,5E_SP0p,:argH_agreep,:SINV_framep,:SINV_agreep,3FS0M:1o"). Qed.
Theorem asan_node_x_sound_XPopFree : XSTMT AP.XPopFree.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsBothClose ()) ["AsanNodes"] "p;@g016Il@0Tg00W^g00Y=f0f1g00cCg00dFg00eNf2f3f4f5f6f7f8f9g017dM@0p=1p,3nx0p,5LIMITp,4SINVp,4argHp,9argH_highp,5E_SP0p,:argH_agreep,:SINV_framep,:SINV_agreep,3FS0M:1o"). Qed.

Theorem asan_node_fillfz_sound : forall hs ws cold fz n0 (i : bool),
  APS.fz_item_stmt ASEGS ASAN_H nx0 LIMIT SINV argH FS0 hs ws cold fz n0
    (fun cs => if AP.fill_in_wins hs ws cs
               then AP.summary_fill ASAN_H nx0 cs (if i then AP.x_imemset ASAN_H else AP.x_memset ASAN_H) (if i then 256 else AX2.two64) else None).
Proof.
ltac2:(KReplay.run1 (kr_t_SumsBothClose ()) ["AsanNodes"] "p;Ag0193lA0Tg00W^g00Y=f0f1g00cCg00dFg00eNf2f3f4f5f6f7f8f9g00fVg00iCMA0p=1p,3nx0p,5LIMITp,4SINVp,4argHp,9argH_highp,5E_SP0p,:argH_agreep,:SINV_framep,:SINV_agreep,3FS0M:1o"). Qed.
End AsanNodes.
