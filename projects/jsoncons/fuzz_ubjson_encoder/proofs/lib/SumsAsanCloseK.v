(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec StoreOk Hoare AgentLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanCoreK AsanPlanK AsanPlanSoundK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import AsanPopFree AsanPlanSoundSumsK SumsAsanSpecsK AsanIStrncpyK AsanPopFreeAsanK Ea0PlanImagesK.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_SumsAsanCloseK () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C46Stdlib5Lists4List2InK47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01I47Corelib4Init5Logic2eq00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K4ridxC13~~~K47Corelib4Init9Datatypes3nat02I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib4Init5Logic6eq_indI47Corelib4Init5Logic5False00I47Corelib4Init9Datatypes3nat00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK<caller_savedC13~~~K47Corelib7Numbers7BinNums8positive03C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanIStrncpyK=istrncpy_clobC13~~~K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK8x_sealedC13~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3powC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5Hoare6ret_okC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4getrC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanIStrncpyKDasan_istrncpy_sealedC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4mkstC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim6msteps00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5Hoare:regs_agreeC13~~~I47Corelib4Init5Logic2ex00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK:x_istrncpyC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7CatExec6wbytesC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBAsanPlanSoundSumsK5APSXK7kept_okC13~~~I47Corelib4Init9Datatypes4list00C45stdpp9bitvector;definitions5bv_eqC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>SumsAsanSpecsKEkept_ok_of_regs_agreeC13~~~C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBAsanPlanSoundSumsK5APSXK=istrncpy_specC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanIStrncpyK>asanreflect_fxC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanIStrncpyKCasan_istrncpy_entryC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanIStrncpyKDstrncpy_sealed_bytesC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBAsanPlanSoundSumsK>asanreflect_fxC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8Ea0DefsK6ASEGS0C13~~~I47Corelib7Numbers7BinNums1Z00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8Ea0DefsK5ASAN0C13~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C79OSSVerify8jsonconsCfuzz_ubjson_encoder6images4Asan1M?loaded_segmentsC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBAsanPlanSoundSumsK5APSXK<SEALED_BYTESC13~~~I47Corelib7Numbers7BinNums1N00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>SumsAsanCloseKAistrncpy_clob_subC13~~~I47Corelib7Numbers7BinNums8positive00I47Corelib4Init5Logic4True00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@AsanPopFreeAsanKAasan_popfree_specC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBAsanPlanSoundSumsK5APSXKEnode_x_sound_XIMemsetC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Ea0PlanImagesK?Asan0_wx_nowrapC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Ea0PlanImagesK=asan0_in_hullC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Ea0PlanImagesK=asan0_hull_okC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>SumsAsanSpecsKFasan_fill_spec_imemsetC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBAsanPlanSoundSumsK5APSXKDnode_x_sound_XMemsetC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>SumsAsanSpecsKEasan_fill_spec_memsetC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBAsanPlanSoundSumsK5APSXKEnode_x_sound_XIMemcpyC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Ea0PlanImagesK=asan0_segs_wrC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>SumsAsanSpecsKFasan_copy_spec_imemcpyC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBAsanPlanSoundSumsK5APSXKDnode_x_sound_XMemcpyC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>SumsAsanSpecsKEasan_copy_spec_memcpyC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBAsanPlanSoundSumsK5APSXKGnode_x_sound_XMemIsZeroC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>SumsAsanSpecsK=asan_miz_specC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBAsanPlanSoundSumsK5APSXKFnode_x_sound_XIStrncpyC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>SumsAsanCloseKBasan_istrncpy_specC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libBAsanPlanSoundSumsK5APSXKEnode_x_sound_XPopFreeC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>SumsAsanCloseKBasan_popfree_spec'C13~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)

Lemma istrncpy_clob_sub : forall r, In r istrncpy_clob -> In (AX2K.ridx r) APK.caller_saved.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsAsanCloseK ()) [] "h01Hh11rp;1p;3p;2p;6g0000j1CTg000Uj1;Tg001:j1GTg001Xj1FTg002;j3ETg002Rj1?Tg0030j3>Tg003Sj34Tg003mj16Tg005=j12Tg005\R0j21Tg0066j2@Tg006Pj3<Tg006jj3ATg007Dj6=Tf2R1f1R2f0R334g007`R4'1p=9f3R5?412/13p=7g008=R6g008\7E3p=8A4623p=0%23#2p=:1134p=BA4612/13p=Df4R7=465A4612/13'1p=3AA1239A75p=5g00:1R8#C#;R9#GR:#FR;g00:V9E;3P0%;9#?g00;lR95>:R<=4;2P;%;8R8#CR=#C#?=>:9R>P2P;%;=#?=>:9R=P2P;%;8R8#C#?=>:9R?P2%;8#?=>:9R9=9;2C7C7C7%61#8P3A4;<1P;P<%63#8X1;R2g00<H#2R:%6<R<'0%::#:R8/0<R@%28RA/0<RB%2ARC/0<RD%2C#:RE/0<RF%2ERG/0<RH%2GRIP<%2IRJP<%2JRKP<%2KRLP<%2LRMP<%2MRNP<%2N#:#:#:#:#:ROP<%2ORPP<%2PRQ%2QRR/0<#B7D<D3D3D3D3RS'1RT'1RU'1RV'1RW'1P@PWPBPVPDPU1@6<9<HS9AFTD5D5%8<eP5P3E=W0P3O1P;P>P1P;P=P1P;P?P1A9;91C7C7C7P0A4;>5P;P=P5P;P?P5A9;95C7C7%67#8P3A4;>7P;P>P2%6>R>,0:108>R510A>R110C>R<10E>RT10G>RF10I>RSPJP>PKP>PLP>PMP>PNP>POP>PPP>PQP>10R>#BD3D3D3D3RH'1RU'1RD'1RV'1RB'1RW'1P5PWP1PBP<PVPTPDPFPU1@6>9<SHD5D5D5%8>ef5R>P3E=W0P3O1P;P=P7P;P?P7A9;97C7C7P0A4;=>P;P?P>A9;9>C7f6R>#6#8P3A4;=>P;P=P2%6=R=,0:108=R710A=RH10C=RS10E=RU10G=RF10I=RD10J=RTPKP=PLP=PMP=PNP=POP=PPP=10R=#B9DQ=D3D3D3RV'1R<'1RB'1R1'1RW'1R5'1R@'1P7P@PHP5PSPWPUP1PFPB1@6=9<TV9AD<D5D5D5%8=ef7R=P3E=W0P3O1P;P?P>A9;9>C7P0A4;?=A9;9=f8R=#6#8P3A4;?=P;P?P2%6?R?,0:108?R>10A?R<10C?RD10E?RV10G?RT10I?RB10J?RF10K?R1PLP?PMP?PNP?POP?PPP?PQP?10R?#BD3D3D3RU'1RW'1RS'1R5'1RH'1R@'1R7'1RX'1P>PXP<P7PDP@PVPHPTP5PBPSPFPW1@6?9<1UD5D5D5D5%8?ef9R?P3E=W0P3O1A9;9=P0A4;9?P4f:R?#6#8P3A4;9?P;P9P2%69R9,0:1089R810A9RA10C9RC10E9RE10G9RG10I9RI10J9RJ10K9RK10L9RLPMP9PNP9POP9PPP910R9#B9DQ9D3D3RQ'1RR'1RP'1RO'1RN'1RM'1R:'1R2'1R;'1P8P;PAP2PCP:PEPMPGPNPIPOPJPP1@699<LQ9AKRD5D5D5D5%89ef;P3E=W0P3O1P4f<#6#8P3n010000000X04P3O1n200100000021100010000W0P3O1n200100000021100011000W0P3O1n200100000021100011000W0P3O1n200100000021100011000W0P3O1n200100000021100011000W0W1o"). Qed.

Lemma asan_istrncpy_spec : APSXK.istrncpy_spec ASEGS0 (APK.x_istrncpy ASAN0) (APK.x_sealed ASAN0).
Proof.
ltac2:(KReplay.run1 (kr_t_SumsAsanCloseK ()) [] "p'0h01Hh12H0h25regs'h31eh42b1h52b2h63dsth71nh83Hagh95Hdisjh:3Hmsh;5Hnoneh<3Hnwh=4Hreth>3Hsth?2R1h@3R10hA3R11hB3R12hC1bi001bhD1ihE1lhF4mem0hG1rhH4regshI3rethJ1xi011xi028bv_is_wfi03;bv_unsignedi041pi051zp;1p;2p;3p;4p;>p;5p;6g0000j17Tg001:j1MTg001XR0j1:Tg00<gj1RTg000Uj13Tg00=Ij2]Tg00>5j1YTg00?Fj2KTg002Rj16Tg00?bj2ITg00@?j2NTg00@[R1j25Tg00A6j2FTg00A\j1fTg003Sj32Tg005=j11Tg00B>j4WTg00C>j2;Tg00Chj2VTg005\R2j2@Tg00DEj1UTg00ELj28Tg00FTj1TTg00G_l>STg00I<j5<Tg00JDj3BTg002;j3HTg00KNj3CTg00LYR3j2JTg00M3j1QTg00NFj3?Tg00OOj2GTg00Pjj1eTg0066j2PTg00QJj3dTg007Dj69Tg00Qnj5cTg00SMj2bTg00Slj1LTg00TEj1^Tg00Tej3DTg00UEj4OTg00U`j4_Tg00V:j3`Tg0030j3aTf0R4#1#1p=\%14#1#1#1p=[%14#1#1#1#1#1#1#1p=Z%14#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=X%14#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0f1R5g00;lR67a4p==g00W[R7f2R8g00Y2R9P5P4D<p=Eg00ZNR:9?54p=>g00[kf3R;P8P5P4D<p=4g00]GR<?B54p=Ag00:1R=#7R>#7R?#7R@#7#7#7RA#MRB#:RC%M@#:R@#RRD]J%3>RE#MRF/]CRGg00^QRHg00^oRI#YRJ/K4%3?#6,IJR?,N4'5f5RK1FB5O1%f@52D[]Dg00`8P<f4RDP;g00<H#1#\#[#Z#X#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0CWg00`X321;BD%3=RL#3RM#3RN#3#3#3#3#3#3#3#3#6RO'I%6>%6A'V'N1;BKRA/IO/KJ1K?A'@%UDf6RA%6=,=F'8=2CKf7R=%7E#6,=FR?'8f8R>52C%3E#6,=FRE,8>1FBJ52Cf9RP%7LRL#7#6,=FRQ'81FBO52Cf<ROf;RR%T<RSf:RTPPP>P=PAPKPDP;P8P5P4M>Sg00a8RPf=RU=ERSP7P4PT1>UOPSD<3B%:FRTg00:VRV9HT4WGRW?CR4'5X2G,JGP3PGf>R3=EOSP7P4PR1>3UPSD<5BPACWO4'5X2GPU%QIRI,FBRXf?RYPSC4P4POg00bERO9?Y3PSC4'A1GU4184?RZ=2C3'5'5X2G,JGP4f@R[=E3SP7P4PU1>[YPSD<5BPACW34'5P1fARU=EYSP7P5P31>U[PSD<5BPACWY5PUPXfCRYPSC4P4P[fBR3=?YOPSC4'A1GU4A2CZ3'5'5X2G,JGP4AEUYSP7P;P[1>Y3PSD<5BPACW3DPGfDRWPXfFRPPSC4P4PYfER[=?POPSC4'A1GW4A2CZ['5'5X2GPKPYPXP[PSC4PKP3A?[WOPSC4'A1GYKR318K?=2CWRZ'5%e@R@/POA2@:OP@P:P[PXfGR:PSC4P=PWA?:P4PSC4'AXE@g00ceR@%:4R=%:5R7P1%:8?2541;;81;;552HR1[1;851;8452H%:;?285[RU%:D?2;8\1Ad854P4n2001000000120000000W5W4W7PU^57^4=^7@P4PBP9PX1;BX,PHO4b0A2C9XPCP9PPP4fHRPPSC4P>P[1>P:PSC4'AXCCP;PXP4E9b0POP4E9b0P3PZPVPYPKg00dCP4DcPC18Y?18A?=2C4X6CP4P?A2TE?RAA2TQ?RY%3L#6,=FRL=2T?RK%7M#6,=FRM=2T?RZ%6N,=FRN=2T?R3g007`RO'@RX'@R;'@RS'@RP'@R:P2PAPPPOP4PTPEP0PFp-0R[P4PHP[P5POg00e^R>P[P4g00fCR9POPOn011040003100001000000RBPOn011050003001010410104n101100000120103102X3TR@P6P?P4E9PO1bO4R=b1X0AP4O1P2PYPSPOP4PTPQP0PFP[P4PHP[P5POP>P[P4POP>P[P4POP9POn011040003100001000000POn011040003101041010400POn011050003001010410104n101100000120103102X3TP6P?P4E9POP=b1X0YP4O1P2PKP;POP4PTPLP@P6P?P4E9POP=b1X0KP4O1P2PZPXPOP4PTPMP0PFP[P4PHP[P5POP>P[P4POP>P[P4PBPOPOn011040003101041010400POn011040003101041010400POn011050003001010410104n101100000120103102X3TP6P?P4E9POP=b1X0ZP4O1P2P3POPOP4PTPNP@P6P?P4E9POP=b1X03P4O1POPOP4n010000000X0OP4O1n200100000021000010000X1XP4O1n200100000021000010000X1;P4O1n200100000021000011000X1SP4O1n200100000021000011000X1PP4O1n200100000021000011000W1%L:e%^T9DTN9DTM9DTL9DTQ9DTE9HT?#LeAHT?V#LeO2PWPRE9COCOC_W8W:P5P4O2n2001000000121000000W0X2GP5P4O2n2001000000121101000b3WBWAW@W?W=W9W<W>W;XICWHX6CWFA`<IJeo"). Qed.

Lemma asan_popfree_spec' : popfree_spec ASEGS0 (APK.x_popfree ASAN0).
Proof.
ltac2:(KReplay.run1 (kr_t_SumsAsanCloseK ()) [] "g00f_o"). Qed.

(* [comment removed for export] *)

Section AsanNodes.
Variable scfg : SpuriousCfg.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : AX2K.env -> (word -> option byte) -> Prop.
Variable argH : AX2K.env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> APK.CEIL <= bv_unsigned a /\ APSK.uE E APCK.e_sp0 <= bv_unsigned a.   (* [comment removed for export] *)
Hypothesis e_sp0_init : APCK.expr_vars_lt nx0 APCK.e_sp0 = true.                                                                (* [comment removed for export] *)
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Variable FS0 : Fs.Fs.

#[local] Notation XSTMT := (APSK.x_stmt ASEGS0 scfg ASAN0 nx0 LIMIT SINV argH FS0).

#[local] Ltac close_with NODE SPEC :=
  eapply NODE; try eassumption;
  first [ exact Asan0_wx_nowrap | exact asan0_in_hull | exact asan0_res_len | exact asan0_hull_ok | exact asan0_segs_wr | exact SPEC | idtac ].

Theorem asan_node_x_sound_XIMemset : XSTMT APK.XIMemset.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsAsanCloseK ()) ["AsanNodes"] "p;Ag00h<lA0Tg00]Gf0g00^of1f2g00ieg00k>g00lUf3f4f5f6f7f8f9f:g00mlMA0p=1p,4scfgp,3nx0p,5LIMITp,4SINVp,4argHp,9argH_highp,:e_sp0_initp,:argH_agreep,:SINV_framep,:SINV_agreep,3FS0M;1o"). Qed.
Theorem asan_node_x_sound_XMemset : XSTMT APK.XMemset.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsAsanCloseK ()) ["AsanNodes"] "p;Ag00oLlA0Tg00]Gf0g00^of1f2g00ieg00k>g00lUf3f4f5f6f7f8f9f:g0114MA0p=1p,4scfgp,3nx0p,5LIMITp,4SINVp,4argHp,9argH_highp,:e_sp0_initp,:argH_agreep,:SINV_framep,:SINV_agreep,3FS0M;1o"). Qed.
Theorem asan_node_x_sound_XIMemcpy : XSTMT APK.XIMemcpy.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsAsanCloseK ()) ["AsanNodes"] "p;Bg012SlB0Tg00]Gf0g00^of1f2g00ieg00k>g00lUf3f4f5f6f7f8f9f:g014<g015SMB0p=1p,4scfgp,3nx0p,5LIMITp,4SINVp,4argHp,9argH_highp,:e_sp0_initp,:argH_agreep,:SINV_framep,:SINV_agreep,3FS0M;1o"). Qed.
Theorem asan_node_x_sound_XMemcpy : XSTMT APK.XMemcpy.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsAsanCloseK ()) ["AsanNodes"] "p;Bg0173lB0Tg00]Gf0g00^of1f2g00ieg00k>g00lUf3f4f5f6f7f8f9f:g014<g018[MB0p=1p,4scfgp,3nx0p,5LIMITp,4SINVp,4argHp,9argH_highp,:e_sp0_initp,:argH_agreep,:SINV_framep,:SINV_agreep,3FS0M;1o"). Qed.
Theorem asan_node_x_sound_XMemIsZero : XSTMT APK.XMemIsZero.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsAsanCloseK ()) ["AsanNodes"] "p;Ag01::lA0Tg00]Gf0g00^of1f2g00ieg00k>g00lUf3f4f5f6f7f8f9f:g01;eMA0p=1p,4scfgp,3nx0p,5LIMITp,4SINVp,4argHp,9argH_highp,:e_sp0_initp,:argH_agreep,:SINV_framep,:SINV_agreep,3FS0M;1o"). Qed.
Theorem asan_node_x_sound_XIStrncpy : XSTMT APK.XIStrncpy.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsAsanCloseK ()) ["AsanNodes"] "p;Ag01=<lA0Tg00]Gf0g00^of1f2g00ieg00k>g00lUf3f4f5f6f7f8f9f:g01>fMA0p=1p,4scfgp,3nx0p,5LIMITp,4SINVp,4argHp,9argH_highp,:e_sp0_initp,:argH_agreep,:SINV_framep,:SINV_agreep,3FS0M;1o"). Qed.
Theorem asan_node_x_sound_XPopFree : XSTMT APK.XPopFree.
Proof.
ltac2:(KReplay.run1 (kr_t_SumsAsanCloseK ()) ["AsanNodes"] "p;Ag01@BlA0Tg00]Gf0g00^of1f2g00ieg00k>g00lUf3f4f5f6f7f8f9f:g01AkMA0p=1p,4scfgp,3nx0p,5LIMITp,4SINVp,4argHp,9argH_highp,:e_sp0_initp,:argH_agreep,:SINV_framep,:SINV_agreep,3FS0M;1o"). Qed.
End AsanNodes.
