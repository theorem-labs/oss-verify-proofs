(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import PropExec StoreOk Hoare AgentLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import PropExec.  (* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.ASB02 Require Import AsanTablesA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import AsanPopFree AsanPlanSoundSums.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.ASB02 Require Import SumsAsanSpecs AsanIStrncpy AsanPopFreeAsan AsanPlanImages.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_SumsAsanClose () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C46Stdlib5Lists4List2InK47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01I47Corelib4Init5Logic2eq00C79OSSVerify5KrLib2K52AS:AxSymExec33AX24ridxC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib4Init5Logic6eq_indI47Corelib4Init5Logic5False00I47Corelib4Init9Datatypes3nat00C79OSSVerify5KrLib2K52AS8AsanPlan2AP<caller_savedC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib2K55ASB02<AsanIStrncpy=istrncpy_clobC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC79OSSVerify5KrLib2K52AS8AsanPlan2AP8x_sealedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3powC69OSSVerify5KrLib2K52AS5Hoare6ret_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB02<AsanIStrncpyDasan_istrncpy_sealedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8PropExec4mkstC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K52AS6CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS5Hoare:regs_agreeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C79OSSVerify5KrLib2K52AS8AsanPlan2AP:x_istrncpyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS7CatExec6wbytesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52ASAAsanPlanSoundSums4APSX7kept_okC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C45stdpp9bitvector;definitions5bv_eqC69OSSVerify5KrLib2K55ASB02=SumsAsanSpecsEkept_ok_of_regs_agreeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C79OSSVerify5KrLib2K52ASAAsanPlanSoundSums4APSX=istrncpy_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB02<AsanIStrncpy>asanreflect_fxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB02<AsanIStrncpyCasan_istrncpy_entryC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB02<AsanIStrncpyDstrncpy_sealed_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52ASAAsanPlanSoundSums>asanreflect_fxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB02>AsanPlanImages5ASEGSC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C69OSSVerify5KrLib2K55ASB02;AsanTablesA6ASAN_AC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrImgITgt_bilateral_fuzzer_both1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52ASAAsanPlanSoundSums4APSX<SEALED_BYTESC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00c69OSSVerify5KrLib2K55ASB02=SumsAsanCloseAistrncpy_clob_subC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums8positive00I47Corelib4Init5Logic4True00C69OSSVerify5KrLib2K55ASB02?AsanPopFreeAsanAasan_popfree_specC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52ASAAsanPlanSoundSums4APSXEnode_x_sound_XIMemsetC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB02>AsanPlanImages7asan_wxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB02>AsanPlanImages<asan_in_hullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB02>AsanPlanImages<asan_hull_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB02=SumsAsanSpecsFasan_fill_spec_imemsetC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52ASAAsanPlanSoundSums4APSXDnode_x_sound_XMemsetC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB02=SumsAsanSpecsEasan_fill_spec_memsetC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52ASAAsanPlanSoundSums4APSXEnode_x_sound_XIMemcpyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB02=SumsAsanSpecs<asan_segs_wrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB02=SumsAsanSpecsFasan_copy_spec_imemcpyC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52ASAAsanPlanSoundSums4APSXDnode_x_sound_XMemcpyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB02=SumsAsanSpecsEasan_copy_spec_memcpyC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52ASAAsanPlanSoundSums4APSXGnode_x_sound_XMemIsZeroC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB02=SumsAsanSpecs=asan_miz_specC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52ASAAsanPlanSoundSums4APSXFnode_x_sound_XIStrncpyC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02=SumsAsanCloseBasan_istrncpy_specC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52ASAAsanPlanSoundSums4APSXEnode_x_sound_XPopFreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02=SumsAsanCloseBasan_popfree_spec'C1?~~~~~~~~~~~~~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)

Lemma istrncpy_clob_sub : forall r, In r istrncpy_clob -> In (AX2.ridx r) AP.caller_saved.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsAsanClose ()) [] "h01Hh11rp;1p;3p;2p;6g0000j1CTg000Uj1;Tg001:j1GTg001Xj1FTg002;j3ETg002Rj1?Tg0030j3>Tg003Sj34Tg003mj16Tg004kj12Tg005JR0j21Tg005dj2@Tg006>j3<Tg006Xj3ATg0072j6=Tf2R1f1R2f0R334g007NR4'1p=9f3R5?412/13p=7g007kR6g008J7E3p=8A4623p=0%23#2p=:1134p=BA4612/13p=Df4R7=465A4612/13'1p=3AA1239A75p=5g009MR8#C#;R9#GR:#FR;g00:29E;3P0%;9#?g00;:R95>:R<=4;2P;%;8R8#CR=#C#?=>:9R>P2P;%;=#?=>:9R=P2P;%;8R8#C#?=>:9R?P2%;8#?=>:9R9=9;2C7C7C7%61#8P3A4;<1P;P<%63#8X1;R2g00;V#2R:%6<R<'0%::#:R8/0<R@%28RA/0<RB%2ARC/0<RD%2C#:RE/0<RF%2ERG/0<RH%2GRIP<%2IRJP<%2JRKP<%2KRLP<%2LRMP<%2MRNP<%2N#:#:#:#:#:ROP<%2ORPP<%2PRQ%2QRR/0<#B7D<D3D3D3D3RS'1RT'1RU'1RV'1RW'1P@PWPBPVPDPU1@6<9<HS9AFTD5D5%8<eP5P3E=W0P3O1P;P>P1P;P=P1P;P?P1A9;91C7C7C7P0A4;>5P;P=P5P;P?P5A9;95C7C7%67#8P3A4;>7P;P>P2%6>R>,0:108>R510A>R110C>R<10E>RT10G>RF10I>RSPJP>PKP>PLP>PMP>PNP>POP>PPP>PQP>10R>#BD3D3D3D3RH'1RU'1RD'1RV'1RB'1RW'1P5PWP1PBP<PVPTPDPFPU1@6>9<SHD5D5D5%8>ef5R>P3E=W0P3O1P;P=P7P;P?P7A9;97C7C7P0A4;=>P;P?P>A9;9>C7f6R>#6#8P3A4;=>P;P=P2%6=R=,0:108=R710A=RH10C=RS10E=RU10G=RF10I=RD10J=RTPKP=PLP=PMP=PNP=POP=PPP=10R=#B9DQ=D3D3D3RV'1R<'1RB'1R1'1RW'1R5'1R@'1P7P@PHP5PSPWPUP1PFPB1@6=9<TV9AD<D5D5D5%8=ef7R=P3E=W0P3O1P;P?P>A9;9>C7P0A4;?=A9;9=f8R=#6#8P3A4;?=P;P?P2%6?R?,0:108?R>10A?R<10C?RD10E?RV10G?RT10I?RB10J?RF10K?R1PLP?PMP?PNP?POP?PPP?PQP?10R?#BD3D3D3RU'1RW'1RS'1R5'1RH'1R@'1R7'1RX'1P>PXP<P7PDP@PVPHPTP5PBPSPFPW1@6?9<1UD5D5D5D5%8?ef9R?P3E=W0P3O1A9;9=P0A4;9?P4f:R?#6#8P3A4;9?P;P9P2%69R9,0:1089R810A9RA10C9RC10E9RE10G9RG10I9RI10J9RJ10K9RK10L9RLPMP9PNP9POP9PPP910R9#B9DQ9D3D3RQ'1RR'1RP'1RO'1RN'1RM'1R:'1R2'1R;'1P8P;PAP2PCP:PEPMPGPNPIPOPJPP1@699<LQ9AKRD5D5D5D5%89ef;P3E=W0P3O1P4f<#6#8P3n010000000X04P3O1n200100000021100010000W0P3O1n200100000021100011000W0P3O1n200100000021100011000W0P3O1n200100000021100011000W0P3O1n200100000021100011000W0W1o"). Qed.

Lemma asan_istrncpy_spec : APSX.istrncpy_spec ASEGS (AP.x_istrncpy ASAN_A) (AP.x_sealed ASAN_A).
Proof.
ltac2:(KReplay.run1 (kr_t_SumsAsanClose ()) [] "p'0h01Hh12H0h25regs'h31eh42b1h52b2h63dsth71nh83Hagh95Hdisjh:3Hmsh;5Hnoneh<3Hnwh=4Hreth>3Hsth?2R1h@3R10hA3R11hB3R12hC1bi001bhD1ihE1lhF4mem0hG1rhH4regshI3rethJ1xi011xi028bv_is_wfi03;bv_unsignedi041pi051zp;1p;2p;3p;4p;>p;5p;6g0000j17Tg001:j1MTg001XR0j1:Tg00<5j1RTg000Uj13Tg00<Wj2]Tg00=Cj1YTg00>Bj2KTg002Rj16Tg00>^j2ITg00?;j2NTg00?WR1j25Tg00@2j2FTg00@Xj1fTg003Sj32Tg004kj11Tg00A:j4WTg00B:j2;Tg00Bdj2VTg005JR2j2@Tg00CAj1UTg00D8j28Tg00E0j1TTg00Ekl>STg00G:j5<Tg00H2j3BTg002;j3HTg00Hlj3CTg00IgR3j2JTg00JAj1QTg00KBj3?Tg00L;j2GTg00MDj1eTg005dj2PTg00Mdj3dTg0072j69Tg00NHj5cTg00OYj2bTg00P8j1LTg00PQj1^Tg00Q1j3DTg00QQj4OTg00Qlj4_Tg00RFj3`Tg0030j3aTf0R4#1#1p=\%14#1#1#1p=[%14#1#1#1#1#1#1#1p=Z%14#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=X%14#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0f1R5g00;:R67a4p==g00SUR7f2R8g00T^R9P5P4D<p=Eg00UlR:9?54p=>g00W;f3R;P8P5P4D<p=4g00XFR<?B54p=Ag009MR=#7R>#7R?#7R@#7#7#7RA#MRB#:RC%M@#:R@#RRD]J%3>RE#MRF/]CRGg00YHRHg00YfRI#YRJ/K4%3?#6,IJR?,N4'5f5RK1FB5O1%f@52D[]Dg00ZfP<f4RDP;g00;V#1#\#[#Z#X#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0CWg00[F321;BD%3=RL#3RM#3RN#3#3#3#3#3#3#3#3#6RO'I%6>%6A'V'N1;BKRA/IO/KJ1K?A'@%UDf6RA%6=,=F'8=2CKf7R=%7E#6,=FR?'8f8R>52C%3E#6,=FRE,8>1FBJ52Cf9RP%7LRL#7#6,=FRQ'81FBO52Cf<ROf;RR%T<RSf:RTPPP>P=PAPKPDP;P8P5P4M>Sg00[fRPf=RU=ERSP7P4PT1>UOPSD<3B%:FRTg00:2RV9HT4WGRW?CR4'5X2G,JGP3PGf>R3=EOSP7P4PR1>3UPSD<5BPACWO4'5X2GPU%QIRI,FBRXf?RYPSC4P4POg00]7RO9?Y3PSC4'A1GU4184?RZ=2C3'5'5X2G,JGP4f@R[=E3SP7P4PU1>[YPSD<5BPACW34'5P1fARU=EYSP7P5P31>U[PSD<5BPACWY5PUPXfCRYPSC4P4P[fBR3=?YOPSC4'A1GU4A2CZ3'5'5X2G,JGP4AEUYSP7P;P[1>Y3PSD<5BPACW3DPGfDRWPXfFRPPSC4P4PYfER[=?POPSC4'A1GW4A2CZ['5'5X2GPKPYPXP[PSC4PKP3A?[WOPSC4'A1GYKR318K?=2CWRZ'5%e@R@/POA2@:OP@P:P[PXfGR:PSC4P=PWA?:P4PSC4'AXE@g00^ER@%:4R=%:5R7P1%:8?2541;;81;;552HR1[1;851;8452H%:;?285[RU%:D?2;8\1Ad854P4n2001000000120000000W5W4W7PU^57^4=^7@P4PBP9PX1;BX,PHO4b0A2C9XPCP9PPP4fHRPPSC4P>P[1>P:PSC4'AXCCP;PXP4E9b0POP4E9b0P3PZPVPYPKg00^cP4DcPC18Y?18A?=2C4X6CP4P?A2TE?RAA2TQ?RY%3L#6,=FRL=2T?RK%7M#6,=FRM=2T?RZ%6N,=FRN=2T?R3g007NRO'@RX'@R;'@RS'@RP'@R:P2PAPPPOP4PTPEP0PFp-0R[P4PHP[P5POg00`0R>P[P4g00`UR9POPOn011040003100001000000RBPOn011050003001010410104n101100000120103102X3TR@P6P?P4E9PO1bO4R=b1X0AP4O1P2PYPSPOP4PTPQP0PFP[P4PHP[P5POP>P[P4POP>P[P4POP9POn011040003100001000000POn011040003101041010400POn011050003001010410104n101100000120103102X3TP6P?P4E9POP=b1X0YP4O1P2PKP;POP4PTPLP@P6P?P4E9POP=b1X0KP4O1P2PZPXPOP4PTPMP0PFP[P4PHP[P5POP>P[P4POP>P[P4PBPOPOn011040003101041010400POn011040003101041010400POn011050003001010410104n101100000120103102X3TP6P?P4E9POP=b1X0ZP4O1P2P3POPOP4PTPNP@P6P?P4E9POP=b1X03P4O1POPOP4n010000000X0OP4O1n200100000021000010000X1XP4O1n200100000021000010000X1;P4O1n200100000021000011000X1SP4O1n200100000021000011000X1PP4O1n200100000021000011000W1%L:e%^T9DTN9DTM9DTL9DTQ9DTE9HT?#LeAHT?V#LeO2PWPRE9COCOC_W8W:P5P4O2n2001000000121000000W0X2GP5P4O2n2001000000121101000b3WBWAW@W?W=W9W<W>W;XICWHX6CWFA`<IJeo"). Qed.

Lemma asan_popfree_spec' : popfree_spec ASEGS (AP.x_popfree ASAN_A).
Proof.
ltac2:(KReplay.run1 (kr_t_SumsAsanClose ()) [] "g00a1o"). Qed.

(* [comment removed for export] *)

Section AsanNodes.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> AP.CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Variable FS0 : Fs.Fs.

#[local] Notation XSTMT := (APS.x_stmt ASEGS ASAN_A nx0 LIMIT SINV argH FS0).

#[local] Ltac close_with NODE SPEC :=
  eapply NODE; try eassumption;
  first [ exact asan_wx | exact asan_in_hull | exact asan_res_len | exact asan_hull_ok | exact asan_segs_wr | exact SPEC | idtac ].

Theorem asan_node_x_sound_XIMemset : XSTMT AP.XIMemset.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsAsanClose ()) ["AsanNodes"] "p;?g00b@l?0Tg00XFg00Yff0f1g00cWg00d[g00edf2f3f4f5f6f7f8g00fmM?0p=1p,3nx0p,5LIMITp,4SINVp,4argHp,9argH_highp,:argH_agreep,:SINV_framep,:SINV_agreep,3FS0M91o"). Qed.
Theorem asan_node_x_sound_XMemset : XSTMT AP.XMemset.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsAsanClose ()) ["AsanNodes"] "p;?g00h?l?0Tg00XFg00Yff0f1g00cWg00d[g00edf2f3f4f5f6f7f8g00iUM?0p=1p,3nx0p,5LIMITp,4SINVp,4argHp,9argH_highp,:argH_agreep,:SINV_framep,:SINV_agreep,3FS0M91o"). Qed.
Theorem asan_node_x_sound_XIMemcpy : XSTMT AP.XIMemcpy.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsAsanClose ()) ["AsanNodes"] "p;@g00jfl@0Tg00XFg00Yff0f1g00cWg00d[g00edf2f3f4f5f6f7f8g00l=g00mEM@0p=1p,3nx0p,5LIMITp,4SINVp,4argHp,9argH_highp,:argH_agreep,:SINV_framep,:SINV_agreep,3FS0M91o"). Qed.
Theorem asan_node_x_sound_XMemcpy : XSTMT AP.XMemcpy.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsAsanClose ()) ["AsanNodes"] "p;@g00nWl@0Tg00XFg00Yff0f1g00cWg00d[g00edf2f3f4f5f6f7f8g00l=g00omM@0p=1p,3nx0p,5LIMITp,4SINVp,4argHp,9argH_highp,:argH_agreep,:SINV_framep,:SINV_agreep,3FS0M91o"). Qed.
Theorem asan_node_x_sound_XMemIsZero : XSTMT AP.XMemIsZero.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsAsanClose ()) ["AsanNodes"] "p;?g011>l?0Tg00XFg00Yff0f1g00cWg00d[g00edf2f3f4f5f6f7f8g012WM?0p=1p,3nx0p,5LIMITp,4SINVp,4argHp,9argH_highp,:argH_agreep,:SINV_framep,:SINV_agreep,3FS0M91o"). Qed.
Theorem asan_node_x_sound_XIStrncpy : XSTMT AP.XIStrncpy.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsAsanClose ()) ["AsanNodes"] "p;?g013`l?0Tg00XFg00Yff0f1g00cWg00d[g00edf2f3f4f5f6f7f8g0158M?0p=1p,3nx0p,5LIMITp,4SINVp,4argHp,9argH_highp,:argH_agreep,:SINV_framep,:SINV_agreep,3FS0M91o"). Qed.
Theorem asan_node_x_sound_XPopFree : XSTMT AP.XPopFree.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsAsanClose ()) ["AsanNodes"] "p;?g016Fl?0Tg00XFg00Yff0f1g00cWg00d[g00edf2f3f4f5f6f7f8g017]M?0p=1p,3nx0p,5LIMITp,4SINVp,4argHp,9argH_highp,:argH_agreep,:SINV_framep,:SINV_agreep,3FS0M91o"). Qed.
End AsanNodes.
