(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import ZBridge Mem Arr Frame Image.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import SeqExec EnframeArith.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_exit_lib A_amem_lib A_imsetv A_vsnp_num.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_PfLib AW_PfNum AW_PfVsn AW_PfLib2 AW_PfVsn2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
Import ListNotations.
#[local] Existing Instance Lib.PropExec.fx0.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00734c151ce24dc8 0 2 0 1 32 1P00f00f47942015cc 0 2 0 1 32 1P00f2aa277c216f48 0 2 0 1 34 1P0116e8ca1b4622b5 0 2 0 1 34 1P01402d7a2af99d78 0 3 1 1 35 1 36 1P019ac09b9517910d 0 2 0 1 28 1P01ae2b17724b8ed0 0 2 0 1 28 1P01ce78fcd1079656 0 2 0 1 28 1P0208351c88154fc0 0 2 0 1 32 1P020e266295c273ee 0 2 0 1 34 1P027df8daa5655003 0 2 0 1 32 1P02abf77070f47aad 0 3 1 1 35 1 36 1P031ec38b4c00bfe4 0 2 0 1 28 1P039655abdc83034f 0 2 0 1 28 1P0407b894db80c1c6 0 3 1 1 29 1 30 1P045f96bdfff65676 0 2 0 1 28 1P04780af970b85db5 0 2 0 1 28 1P0489be6ece69cebc 0 3 1 1 35 1 36 1P05dc7a383922052b 0 3 1 1 35 1 36 1P05e3aba260330d44 0 2 0 1 32 1P060d8fc105fda5a6 0 2 0 1 34 1P063b8f5822b5edd1 0 2 0 1 28 1P0679cb5c8440bf55 0 2 0 1 32 1P0831aac27161da2d 0 2 0 1 32 1P083a4d0140e8d3c6 0 2 0 1 34 1P08dbaf7fec08d6f0 0 3 1 1 29 1 30 1P090b0c9360ea41b7 0 3 1 1 35 1 36 1P09b7f516b15e4cab 0 2 0 1 34 1P09c742bedeecf3b2 0 3 1 1 33 1 34 1P0a1c7e17013d5b61 0 2 0 1 28 1P0aad0eaa2267e165 0 2 0 1 32 1P0ad53acaf03f846e 0 2 0 1 32 1P0b5d6800452b4725 0 3 1 1 29 1 30 1P0c1a3bd8cea0427c 0 2 0 1 28 1P0c269a1b82932b1f 0 2 0 1 28 1P0c761897294a03ea 0 2 0 1 32 1P0ce697ee26451f6a 0 3 1 1 35 1 36 1P0d0fdee97da3e766 0 2 0 1 32 1P0d423d4faf975adf 0 2 0 1 34 1P0db678f8db419bf8 0 2 0 1 34 1P0de8b98300054614 0 3 1 1 29 1 30 1P0df3e0ba0bca5808 0 2 0 1 34 1P0ecdbe949381896e 0 2 0 1 34 1P0f8dfcb5a68344d2 0 2 0 1 28 1P0fa5147046830bab 0 3 1 1 35 1 36 1P0fe9a8df8540956d 0 2 0 1 34 1P0febd9ebc23e8861 0 2 0 1 34 1P0feeb6e8745697c1 0 3 1 1 35 1 36 1P103b1a7c4c065fb3 0 3 1 1 35 1 36 1P1127e57768e2281d 0 2 0 1 34 1P11704ef7c6fa3b10 0 3 1 1 35 1 36 1P11c4034fdcfbc253 0 3 1 1 29 1 30 1P123f4dd2c38cf1e0 0 2 0 1 32 1P128232ba4bd69230 0 2 0 1 28 1P12b3fa3daea9ce01 0 2 0 1 26 1P12ba24b4bf1e63da 0 3 1 1 35 1 36 1P13816461ea1f9de3 0 2 0 1 28 1P1381ce8b7ea7522f 0 2 0 1 34 1P143b398a9b117911 0 3 1 1 29 1 30 1P147e0824cd8a6658 0 2 0 1 34 1P14a42f44ddbe4855 0 2 0 1 28 1P15a22e875d516f5a 0 3 1 1 29 1 30 1P1629c37d57587807 0 3 1 1 35 1 36 1P168b6f16bdd4b518 0 2 0 1 34 1P16bd636868cbd0aa 0 3 1 1 29 1 30 1P16c4798c5f5de1c7 0 2 0 1 28 1P16dd4a8389fd737f 0 2 0 1 34 1P16e5001a8d946ca2 0 3 1 1 35 1 36 1P16fb3559ac043d49 0 3 1 1 35 1 36 1P176c13b7adb40d38 0 3 1 1 35 1 36 1P179c7b51814b7ba6 0 3 1 1 29 1 30 1P18e513755683b441 0 2 0 1 34 1P19136bc2605f805e 0 2 0 1 34 1P193524f1055aeec7 0 3 1 1 35 1 36 1P19f17e6ea10cf592 0 2 0 1 34 1P19ff1fc656314701 0 3 1 1 33 1 34 1P1a19e1e603c70eff 0 2 0 1 32 1P1ae09ff0587b02fa 0 2 0 1 34 1P1c43aa25c6bc7991 0 2 0 1 34 1P1c56d75db4ad61ef 0 2 0 1 27 1P1c9994e056fd38c0 0 2 0 1 34 1P1d5767e94c0fd891 0 2 0 1 28 1P1da890c3261f7f0f 0 2 0 1 34 1P1dd826df69472a89 0 2 0 1 28 1P1e68bc47352f9329 0 2 0 1 32 1P1ec5929c4ad808ad 0 2 0 1 28 1P1ed1c4a8ae839d47 0 3 1 1 35 1 36 1P1ef1d03c22c3d8df 0 2 0 1 34 1P1f22278978f3baac 0 2 0 1 28 1P1f3a0ac7eb395091 0 3 1 1 29 1 30 1P1f3c30587402f58f 0 2 0 1 28 1P1fed8e73a039d1cf 0 3 1 1 35 1 36 1P20a2051a903ee273 0 3 1 1 29 1 30 1P20c11f7d08228b4d 0 3 1 1 29 1 30 1P210ee01124acf038 0 2 0 1 26 1P219878efc81b45ed 0 3 1 1 29 1 30 1P21bbea3a3d38a60c 0 2 0 1 34 1P2283d28e9d5ad17a 0 3 1 1 33 1 34 1P22aea95aed88d1ce 0 2 0 1 34 1P2356854a202ae6f2 0 3 1 1 29 1 30 1P2358ec450c722928 0 3 1 1 29 1 30 1P239fc09394a2005b 0 2 0 1 34 1P23e209c1d0034b97 0 2 0 1 32 1P23fdb7bcef46b9ba 0 2 0 1 28 1P2430ac091cfff962 0 2 0 1 34 1P2479efedcfc78332 0 3 1 1 35 1 36 1P24e2a402b9e28882 0 2 0 1 28 1P255623e70c1070e1 0 3 1 1 29 1 30 1P25aa267c08826ccb 0 3 1 1 33 1 34 1P25dc7b86e12acd7d 0 2 0 1 32 1P26842bb0568c9262 0 2 0 1 32 1P26a24fc93b219b95 0 2 0 1 32 1P26cd04b0b4be8f68 0 2 0 1 34 1P27420ca1de85850a 0 2 0 1 28 1P2760ef0ee0683bd4 0 3 1 1 29 1 30 1P278aac022006170a 0 3 1 1 33 1 34 1P2801062b0e09d667 0 3 1 1 29 1 30 1P2921d2550c1ba1d1 0 2 0 1 28 1P292b011a7fd7179b 0 2 0 1 28 1P29462fce28ec9084 0 2 0 1 28 1P29d31663cbe16325 0 2 0 1 32 1P2a7f875b73e57fd6 0 3 1 1 35 1 36 1P2a9e9f04f0cf3604 0 2 0 1 28 1P2bc8f591cef22e77 0 2 0 1 34 1P2bdb0f444a79e9da 0 3 1 1 35 1 36 1P2c6e6b87a1f2344d 0 3 1 1 35 1 36 1P2c6e88ae1073b61a 0 3 1 1 33 1 34 1P2c95928ca34d89c7 0 2 0 1 34 1P2cea020841505b12 0 2 0 1 32 1P2cf5edeaae9060a2 0 3 1 1 29 1 30 1P2cfe63accda32275 0 2 0 1 32 1P2d3e6eacedeffc5c 0 2 0 1 32 1P2d59bb963aa74c36 0 3 1 1 29 1 30 1P2db276da23f8d7c8 0 3 1 1 29 1 30 1P2dc501a1dd1daabd 0 2 0 1 34 1P2e3ef0d65244bc24 0 2 0 1 32 1P2ecec28a07719ce7 0 2 0 1 28 1P2f0fd6a6405d8fc3 0 2 0 1 28 1P2f74ee0c2ddd9a11 0 3 1 1 29 1 30 1P2ff07ef3e1a7c94f 0 3 1 1 33 1 34 1P301d110cacbbc278 0 3 1 1 35 1 36 1P30415f748dfe1c9b 0 3 1 1 29 1 30 1P30a5f6917f334339 0 2 0 1 32 1P30c3cef2fd951201 0 3 1 1 33 1 34 1P31856235e3462175 0 2 0 1 28 1P3196d30e8191f1b0 0 3 1 1 29 1 30 1P3270bf8eb3231864 0 3 1 1 35 1 36 1P32aa97b02c17527c 0 2 0 1 32 1P335002f39c6f9bd8 0 3 1 1 35 1 36 1P33b52ae0397f0ffc 0 2 0 1 34 1P341bbc5174babe89 0 2 0 1 34 1P34585c5b57dfc260 0 2 0 1 34 1P34801d20a5ea0dad 0 3 1 1 35 1 36 1P350f53a50430176c 0 2 0 1 34 1P3529cb6b913483f7 0 2 0 1 34 1P353f1ac065fbd8a3 0 2 0 1 34 1P3541b292d5325459 0 2 0 1 32 1P35a70fadce481aad 0 3 1 1 35 1 36 1P35e97d81c332bae3 0 2 0 1 32 1P360a353696f99d1d 0 2 0 1 34 1P36153ec3daf5ab49 0 2 0 1 34 1P36de3a5a680e0442 0 2 0 1 32 1P379867a6b34ae966 0 3 1 1 29 1 30 1P37b2e82270f326f3 0 2 0 1 32 1P38eeb4f7b3a739b6 0 2 0 1 28 1P39122246ab62f9b0 0 2 0 1 34 1P39202fb7991fc7ec 0 2 0 1 26 1P3960be2dadce6f73 0 2 0 1 34 1P39918f1f8d9cad85 0 3 1 1 35 1 36 1P3a7b5ab9b860362d 0 2 0 1 28 1P3b5e8c51ff8c4389 0 2 0 1 34 1P3c0cda2968da3fa2 0 2 0 1 34 1P3c5228f7ef4e7481 0 2 0 1 34 1P3c7070cdd6cc86a1 0 3 1 1 35 1 36 1P3c7b76f1455a2225 0 3 1 1 29 1 30 1P3ca309b620791cd7 0 3 1 1 35 1 36 1P3cc90b2aabe9a3b6 0 2 0 1 27 1P3dbf3369f9848437 0 2 0 1 28 1P3df9e8320da10088 0 2 0 1 32 1P3e1e379e503789b7 0 3 1 1 35 1 36 1P3ed8d5d236785f94 0 2 0 1 34 1P3f0c23752c32f1e9 0 3 1 1 35 1 36 1P3fd8bac9ca309984 0 2 0 1 34 1"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_PfShared () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_PfNum.pr_range"; "Stdlib.Lists.List.nth_error"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Walk.pf_frames"; "Walk.vsn_call_T"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "Walk.printf_pre_post"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.B.A_vsnp_num.ndig"].


Local Ltac2 Set LiaOrc.tbl := fun () => "0070>L11607912823.3L24053695604.4L34174747871.4L38559713562.3L45582813826.4L66208786720.4L7327412462.3 00000100400700?00H00Q00YSS1zS1zS1z2Hz1HS1z2Hz2H0S1z2Hz2H0S1z2Hz1H". (* [comment removed for export] *)
Lemma signed_lit64 : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  destruct (Z.lt_ge_cases z 0).
  - rewrite <- (Z.mod_add z 1 (2^64)) by lia. rewrite Z.mod_small by lia. destruct (Z.ltb_spec (z + 1 * 2^64) (2^63)); lia.
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec z (2^63)); lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Definition vsn_call_T (fmt : Z) (x1 x2 x3 x4 x5 x6 x7 : word) (len : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_PfShared ()) "PSP,$0.Plo,$0.PBUF,$0.PVA,$0.Pbs,(1.(2.&8.))Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(3.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(4.(2.&8.))P,(5.$0.(6.(7.(2.&8.)R1>.))+190.)P,(8.$9.R2.R22.R23.)P,(:.+65?000.R23.)P,(:.R24.(;.R25.+1=0.))P,(<.VCS,R25.(;.R26.R25.))P,(:.R27.R25.)P,(=.$9.R7.R26.R24.)P,(<.VCS,R27.+190.)P,(>.(?.R28.+190.)(10.+2.+3?.))P,(11.$9.R:.R28.(12.$13.(14.O8.)(12.$13.(14.O7.)(12.$13.(14.O6.)(12.$13.(14.O5.)(12.$13.(14.O4.)(12.$13.(14.O3.)(12.$13.(14.O2.)(15.$13.)))))))))P,(<.VCS,R29.+38.)P,(:.R2=.R2:.)P,(16.(:.(?.R2;.+38.)R2<.)(:.(?.R2<.+190.)R2;.))P,(:.(?.R2<.+38.)(10.+2.+3?.))P,(17.$9.R?.)(18.$9.VAL,VCS,Lms',$19.(1:.(2.&40.)La1',(2.&40.)(1:.(2.&40.)La2',(2.&40.)(1:.(2.&40.)La3',(2.&40.)(1:.(2.&40.)La4',(2.&40.)(1:.(2.&40.)La5',(2.&40.)(1:.(2.&40.)La6',(2.&40.)(1:.(2.&40.)La7',(2.&40.)(1:.(2.&40.)Lt0',(2.&40.)(1:.(2.&40.)Lt1',(2.&40.)(1:.(2.&40.)Lt2',(2.&40.)(1:.(2.&40.)Lt3',(2.&40.)(1:.(2.&40.)Lt4',(2.&40.)(1:.(1.(2.&8.))Lbs',(1.(2.&8.))(1:.P,(2.&40.)(4.(2.&8.))Lm',P,(2.&40.)(4.(2.&8.))(1;.(5.$19.R?.(1<.(1=.R3;.(1>.&40.R40.)R3:.R39.R7.R6.R5.R35.R34.(1>.&40.O1.)R>.R=.R<.R;.R:.R9.R8.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R4.R3.R23.R22.)R21.(1?.R3;.)R20.(20.(2.&40.))R1.(21.$9.)))(1;.(8.$9.R1.R3?.R40.)(1;.(=.$9.R1.R3>.R2.)(1;.(5.$22.(7.(2.&8.)R2.)(7.(2.&8.)R3<.))(1;.(23.R2.=O1.)(1;.(5.(4.(2.&8.))(24.(2.&8.)R2.(25.O1.))(26.(2.&8.)(1>.&8.=)))(1;.(11.$9.R1.R3=.(12.$13.(14.O8.)(12.$13.(14.O7.)(12.$13.(14.O6.)(12.$13.(14.O5.)(12.$13.(14.O4.)(12.$13.(14.O3.)(12.$13.(14.O2.)(15.$13.)))))))))(1;.(27.(12.(28.$0.$0.)(29.$0.$0.R3?.R40.)(12.(28.$0.$0.)(29.$0.$0.R3>.(?.R3>.+190.))(15.(28.$0.$0.))))R1?.R1.)(1;.(2:.$9.R1?.R1.)(17.$9.R1.))))))))))))))))))))))))(1<.(1=.R2<.(1>.&40.R31.)R2;.R2:.R29.R28.R27.R26.R25.(1>.&40.R2?.)(1>.&40.+190.)(1>.&40.O9.)(1>.&40.R2>.)R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)R12.(1>.&40.+7=810.)R11.(20.(2.&40.))R10.(21.$9.)))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition pf_frames (SP0 : Z) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) (fmt : Z) (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_PfShared ()) "(1:.(1.(2.&8.))Lj8,(1.(2.&8.))(1:.(2.&40.)Lx1,(2.&40.)(1:.(2.&40.)Lx2,(2.&40.)(1:.(2.&40.)Lx3,(2.&40.)(1:.(2.&40.)Lx4,(2.&40.)(1:.(2.&40.)Lx5,(2.&40.)(1:.(2.&40.)Lx6,(2.&40.)(1:.(2.&40.)Lx7,(2.&40.)(1;.(11.$9.O1.(?.O>.-50.)(12.$13.(14.(1>.&40.(?.O>.-38.)))(12.$13.(14.O=.)(12.$13.(2;.#8.R8.)(15.$13.)))))(1;.(11.$9.O1.(?.O>.-38.)(12.$13.(14.R7.)(12.$13.(14.R6.)(12.$13.(14.R5.)(12.$13.(14.R4.)(12.$13.(14.R3.)(12.$13.(14.R2.)(12.$13.(14.R1.)(15.$13.)))))))))(1;.(11.$9.O1.(?.O>.-70.)(12.$13.(14.O:.)(12.$13.(14.O;.)(12.$13.(14.O<.)(12.$13.(14.(1>.&40.+7=>18.))(15.$13.))))))(11.$9.O1.(?.O>.-280.)(12.$13.(14.(1>.&40.=))(12.$13.(14.(1>.&40.=))(12.$13.(14.(1>.&40.=))(12.$13.(14.(1>.&40.(?.O>.-38.)))(12.$13.(14.(1>.&40.(?.O>.-38.)))(12.$13.(14.O3.)(12.$13.(14.O4.)(12.$13.(14.O5.)(12.$13.(14.O6.)(12.$13.(14.O7.)(12.$13.(14.O8.)(12.$13.(14.O9.)(12.$13.(14.(1>.&40.=))(12.$13.(14.(1>.&40.O2.))(12.$13.(14.(1>.&40.(?.O>.-38.)))(12.$13.(14.(1>.&40.+7=>68.))(15.$13.)))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Definition printf_pre_post (fmt len SP0 lo : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_PfShared ()) "Lms',$19.(1:.(2.&40.)Lt0',(2.&40.)(1:.(2.&40.)Lt1',(2.&40.)(1:.(2.&40.)Lt2',(2.&40.)(1:.(2.&40.)La2',(2.&40.)(1:.(2.&40.)La3',(2.&40.)(1:.(2.&40.)La4',(2.&40.)(1:.(2.&40.)La5',(2.&40.)(1:.(2.&40.)La6',(2.&40.)(1:.(2.&40.)La7',(2.&40.)(1:.(2.&40.)Lt3',(2.&40.)(1:.(2.&40.)Lt4',(2.&40.)(1:.(1.(2.&8.))Lbs',(1.(2.&8.))(1:.P,(2.&40.)(4.(2.&8.))Lm',P,(2.&40.)(4.(2.&8.))(1;.(5.$19.R>.(1<.(1=.(1>.&40.+7>4?4.)(1>.&40.(?.O16.-280.))O13.O12.R=.R<.R;.(1>.&40.O18.)(1>.&40.=)(1>.&40.(?.O16.-200.))(1>.&40.+6;948.)R:.R9.R8.R7.R6.R5.(1>.&40.(?.O16.-200.))(1>.&40.+190.)O=.(1>.&40.O17.)O;.O:.O9.O8.O7.O6.R4.R3.O5.O4.)O3.(1>.&40.+6;948.)O2.(20.(2.&40.))R1.(21.$9.)))(1;.(2<.O16.O14.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O18.R1.)(1;.(=.$9.R1.(?.O16.-200.)R2.)(1;.(5.$0.(6.(7.(2.&8.)R2.))+190.)(1;.(23.R2.=O17.)(1;.(5.(4.(2.&8.))(24.(2.&8.)R2.(25.O17.))(26.(2.&8.)(1>.&8.=)))(1;.(8.$9.R1.O15.(?.O16.-280.))(1;.(27.(12.(28.$0.$0.)(29.$0.$0.O15.O16.)(15.(28.$0.$0.)))O1.R1.)(1;.(2:.$9.O1.R1.)(17.$9.R1.)))))))))))))))))))))))")
(* [comment removed for export] *).


  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0190@L13498796098.1  L14228346111.2  L14670875620.7  L16691741877.5  L16809010849.0  L16834874370.56 L16834874370.70 L16834874371.76 L16834874371.79 L16855599955.5  L18749868437.1  L18761010403.4  L21469541623.7  L22373391934.2  L22774446881.0  L23748506894.1  L25107381944.1  L26059861269.1  L26413804241.7  L26682560702.76 L26682560702.79 L26682560703.56 L26682560703.70 L29616115733.1  L31725945991.2  L32657537148.3  L33505959927.7  L35970092053.1  L38768374082.1  L39118425079.5  L39118425079.7  L4015404813.1   L42718379859.5  L42718379859.7  L4409299134.2   L44104789310.2  L46883672865.0  L49058485390.1  L49391787284.5  L49496773493.1  L51352513313.0  L53430737097.100L54111720461.2  L56080470263.5  L5790236941.2   L58804202979.2  L58806826017.4  L58817311264.4  L60922108564.5  L60922108564.7  L65059320382.2  L66566358642.5  L6930241071.47  P13498351985.76 P13498369472.93 P13498369478.103P14230965517.76 P22706564033.101P22706564033.77 P31728589250.103P31728589251.100P31728589252.93 P38768064625.76 P38768082112.93 P38768082118.103P54113274184.103P54113274185.100P54113274190.93 P57622410744.104P57622410744.94 P5788687432.103 P5788687433.100 P5788687438.93  00000100900A00R00S00m01P02702^02g02l03803D03L03M03R03W03\03l04N05005E05c05h05i06506A06F06G06Y06k07007907B07J07R07S07X07]07b07c08=08>08J08K08S08c09409909>09F09W09c0:=0:`0;G0;H0;j0<C0<D0<E0<F0<`0=C0=j0>M0?00?O0@40@U0A80A[0B:FS3SP02loS3len2HLS3len3SP02HL1x2HxSS3SP02lo3SPL3lb03LBL1y3H16S3SP02lo3SPL3lb03LBL3bs14LEN21y3H16S3len3SP02lo3SPL3lb03LBL3bs14LEN21y3H17S3len3SP02lo3SPL3lb03LBL3bs14LEN21y3H17S3SP03SPHS3SP0S3len2HL3bs1S3SP02lo3SPLS3SP02loSS3SP0S3SP0S3SP0S3len3SP02HL3SPHS3len3SP02lo3lb03LBL3bs14LEN21y2HyS3len3SP02lo3lb03LBL3bs14LEN21y2HyS3SP02lo3lb03LBL1y2HyS3SP02lo3lb03LBL3bs14LEN21y2HyS3SP0FS3SP02lo3bs1S3SP02lo3SPLS3SP0FS3SP02lo5LOIMG3SPLS3SP02lo5LOIMG3SPLS3SP0S3SP03SPHS3SP03SPHS3SP02loS3SP02loSS3SP0S3SP0S3SP0SS3len3SP03lb03LBL3bs14LEN2FS3SP02lo3SPLFS3SP02loS3SP02lo3bs13LB1S3SP02lo3bs14LEN2S3SP0S3SP0S3SP02loS3SP02lo3SPL1x2HxS3SP02lo3SPLS3SP02lo5LOIMG3SPL3lb03LBLS3SP02lo5LOIMG3SPL3lb03LBL3bs14LEN2S3len3SP02lo5LOIMG3SPL3lb03LBL3bs14LEN2FS3len3SP02lo3lb03LBL3bs14LEN21x2H0S3SP02lo3SPL3lb03LBL1x2H0FFFS3SP02lo5LOIMG3SPL3lb03LBLS3SP02lo5LOIMG3SPL3lb03LBL3bs14LEN2S3len3SP02lo5LOIMG3SPL3lb03LBL3bs14LEN2S3len3SP02lo5LOIMG3lb03LBL3bs14LEN2S3len3SP02lo5LOIMG3lb03LBL3bs14LEN2S3SP02lo5LOIMG3lb03LBL3bs14LEN2S3len3SP02lo3SPL3lb03LBL3bs14LEN21x1HS3SP02lo3SPL3lb03LBL3bs14LEN21x1HS3len3SP02lo5LOIMG3lb03LBL3bs14LEN2S3len3SP02lo5LOIMG3lb03LBL3bs14LEN2S3SP02lo5LOIMG3lb03LBL3bs14LEN2". (* [comment removed for export] *)
  Theorem printf_pre : ltac2:(CDefT.buildp (gd_tbl_AW_PfShared ()) "Pfmt,$0.Plen,$0.PSP0,$0.Plo,$0.Px1,(2.&40.)Px2,(2.&40.)Px3,(2.&40.)Px4,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(3.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(4.(2.&8.))P,(2=.R24.R20.R1?.R1>.R1=.R1<.R1;.R1:.R23.)P,(1;.(:.+1.R24.)(>.R24.+18?.))P,(1;.(>.=R26.)(>.R26.(10.+2.+2?.)))P,(2>.$9.R4.+?6:18.(12.$13.(14.(1>.&40.+1.))(15.$13.)))P,(2>.$9.R5.+19;710.(12.$13.(14.(1>.&40.+6;948.))(15.$13.)))P,(8.$9.R6.R26.R27.)P,(:.+65?000.R27.)P,(:.R28.(;.R29.+450.))P,(:.R2:.(10.+2.+3?.))P,(<.VCS,R2:.(;.R2;.R2:.))P,(17.$9.R;.)(18.$9.VAL,VCS,(2?.R2?.R2>.R2=.R2<.R24.R23.R22.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R10.R?.R>.R=.R<.)(1<.(1=.R24.(1>.&40.R2=.)R23.R22.R21.R20.R1?.R1>.R1=.(1>.&40.R2?.)R2;.R2:.R29.R28.R27.R26.R25.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.)R>.(1>.&40.+7===8.)R=.(20.(2.&40.))R<.(21.$9.)))")
(* [comment removed for export] *).
  Proof.
    intros until m. intros VSN HL HF GOT CBC ST LOIMG SPL SPH SCS MI. al_facts.
    pose proof (munch_refl [(lo, SP0)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    lx_hide VSN.
    (* [comment removed for export] *)
    lx_run (PLAN [0x7aa58] [] 40%N).
    lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m _ |- _ => lx_hide MUl; lx_hide WMl end.
    (* [comment removed for export] *)
    assert (CRB : crange CS (SP0 + -512) 400) by (intros x Hx; apply SCS; clear -Hx SPL; lia).
    lazymatch goal with STl : stk _ ?mx lo (SP0 + -112) |- _ =>
      lx_carve STl 400%nat ST1 LBUF lb0; replace (SP0 + -112 - Z.of_nat 400) with (SP0 + -512) in ST1, LBUF by (clear; lia) end.
    assert (LBL : length lb0 = 400%nat). { destruct LBUF as [[WF _] _]. cbn in WF. destruct WF as [WF _]. exact WF. }
    apply u8arr_of_rw_cells in LBUF.
    eapply (evtA_cut asegs AL CS);
      [ eapply (imsetv_spec AL IMG ALWF CS CSOK) with (P := SP0 + -512) (n := 400) (b := Z_to_bv 8 170) (ds := lb0);
          first [exact LBUF | rewrite LBL; reflexivity | exact CRB | assumption | reflexivity | clear -SPL LOIMG SPH; lia]
      | ].
    cbn beta. intros ms' (a1m & a3m & m1 & -> & MUc & WMc & MI1 & LBA). clear LBUF. lx_acc_call m MUc WMc. ret_lit.
    (* [comment removed for export] *)
    lx_hide LBA. pose proof (munch_refl [(lo, SP0 + -512); (SP0 + -112, SP0)] m1) as MU2. pose proof (wmono_refl asegs m1) as WM2.
    lx_run (PLAN [0x7d810] [] 40%N). lx_unhide1 LBA.
    lazymatch goal with MUl : munch _ m1 ?mx, WMl : wmono _ m1 _ |- _ =>
      eapply (u8arr_transport asegs) in LBA; [| exact MUl | exact WMl | rewrite repeat_length; cbn [disjoint_from]; clear; lia] end.
    lx_acc_run m m1. lx_clear_mem m1.
    lx_unhide1 VSN.
    lazymatch goal with STl : stk _ ?mx lo (SP0 + -640), VAl : rw_cells _ _ (SP0 + -56) _ |- _ =>
      eapply (evtA_cut asegs AL CS);
      [ eapply (VSN (SP0 + -640) lo (SP0 + -512) (SP0 + -56) (repeat (Z_to_bv 8 170) (Z.to_nat 400)));
          first [ exact STl | exact LBA | exact VAl | exact CRB | assumption | reflexivity
                | intros x Hx; apply SCS; clear -Hx SPL; lia
                | right; clear; lia
                | clear -SPL SPH LOIMG; lia ]
      | ] end.
    clear VSN.
    cbn beta. intros ms' (a1v & a2v & a3v & a4v & a5v & a6v & a7v & t0v & t1v & t2v & t3v & t4v & bs1 & m2 & -> & ST2 & OUT2 & LEN2 & PR2 & NUL2 & VAC2 & MUc & WMc & MI2).
    clear LBA. lx_acc_call m MUc WMc. ret_lit.
    (* [comment removed for export] *)
    lx_hide OUT2. pose proof (munch_refl [(lo, SP0 + -512); (SP0 + -112, SP0)] m2) as MU3. pose proof (wmono_refl asegs m2) as WM3.
    lx_run (PLAN [0x7790c] [] 20%N). lx_unhide1 OUT2.
    lazymatch goal with MUl : munch _ m2 ?mx, WMl : wmono _ m2 _ |- _ =>
      eapply (u8arr_transport asegs) in OUT2; [| exact MUl | exact WMl | cbn [disjoint_from]; clear -LEN2; rewrite repeat_length in LEN2; lia] end.
    lx_acc_run m m2. lx_clear_mem m2.
    (* [comment removed for export] *)
    assert (LB1 : Z.of_nat (length bs1) = 400) by (rewrite LEN2, repeat_length; reflexivity).
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      destruct (out_cstr mx (SP0 + -512) bs1 len OUT2 ltac:(clear -HL LB1; lia) PR2 NUL2) as (CSTR & NOZ & SLEN) end.
    lazymatch goal with STl : stk _ ?mx lo (SP0 + -640) |- _ =>
      eapply (evtA_cut asegs AL CS);
      [ eapply (rawwrite_spec AL IMG ALWF CS CSOK (firstn (Z.to_nat len) bs1) (SP0 + -512) (SP0 + -640) lo);
          first [ exact CSTR | exact NOZ | exact STl | assumption | reflexivity
                | rewrite SLEN; intros x Hx; apply CRB; clear -Hx HL; lia
                | intros x Hx; apply SCS; clear -Hx SPL; lia
                | rewrite ?SLEN; clear -SPL SPH LOIMG HL; lia ]
      | ] end.
    cbn beta. intros ms' (a0r & a1r & a2r & a3r & m3 & -> & ST3 & MUc & WMc & MI3). clear CSTR. lx_acc_call m MUc WMc. ret_lit.
    (* [comment removed for export] *)
    lx_hide OUT2. pose proof (munch_refl [(lo, SP0 + -512); (SP0 + -112, SP0)] m3) as MU4. pose proof (wmono_refl asegs m3) as WM4.
    lx_run (PLAN [0x76de0] [] 20%N). lx_unhide1 OUT2.
    lazymatch goal with MUl : munch _ m3 ?mx, WMl : wmono _ m3 _ |- _ =>
      eapply (u8arr_transport asegs) in OUT2; [| exact MUl | exact WMl | cbn [disjoint_from]; clear -LB1; lia] end.
    lx_acc_run m m3. lx_clear_mem m3.
    lazymatch goal with STl : stk _ ?mx lo (SP0 + -640) |- _ =>
      eapply (evtA_cut asegs AL CS);
      [ eapply (rma_spec AL IMG ALWF CS CSOK len (SP0 + -512) (SP0 + -640) lo bs1);
          first [ exact OUT2 | exact PR2 | exact NUL2 | exact STl | assumption | reflexivity
                | rewrite LB1; exact CRB
                | intros x Hx; apply SCS; clear -Hx SPL; lia
                | rewrite ?LB1; clear -SPL SPH LOIMG HL; lia ]
      | ] end.
    cbn beta. intros ms' (a0a & a1a & a3a & m4 & -> & ST4 & OUT4 & MUc & WMc & MI4).
    rewrite LB1 in MUc. clear OUT2. lx_acc_call m MUc WMc. ret_lit.
    (* [comment removed for export] *)
    lx_hide OUT4. pose proof (munch_refl [(lo, SP0 + -512); (SP0 + -112, SP0)] m4) as MU5. pose proof (wmono_refl asegs m4) as WM5.
    lx_run (PLAN [0x6b948] [] 20%N). lx_unhide1 OUT4.
    lazymatch goal with MUl : munch _ m4 ?mx, WMl : wmono _ m4 _ |- _ =>
      eapply (u8arr_transport asegs) in OUT4; [| exact MUl | exact WMl | cbn [disjoint_from]; clear -LB1; lia] end.
    lx_acc_run m m4. lx_clear_mem m4. lx_unhide.
    (* [comment removed for export] *)
    apply evtA_done. unfold printf_pre_post, pf_frames.
    lazymatch goal with FR6 : rw_cells _ ?mx (SP0 + -112) _, STj : stk _ _ (SP0 + -64) (SP0 + -56) |- _ =>
      chunk_split FR6 4%nat FRs FRp; replace (SP0 + -112 + 32) with (SP0 + -80) in FRp by (clear; lia);
      lx_junk STj 8%nat j8 FRj; chunk_join FRp FRj FR80 end.
    lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m _, FRn : rw_cells _ _ (SP0 + -640) _ |- _ =>
      lx_exs; lx_ands;
      [ lx_mseq
      | do 8 eexists; split; [exact FR80| split; [eassumption| split; [exact FRs| exact FRn]]]
      | exact OUT4 | exact LB1 | exact PR2 | exact NUL2 | assumption | exact MUl | exact WMl | assumption ] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00D0?L11786978302.1 L11982974318.1 L14639577486.1 L16832777353.62L18848568670.1 L25931853483.58L26680463412.62L29105744959.58L34685477558.1 L34970429520.82L3566930558.1  L37991333298.1 L38432104821.1 L41832293902.1 L49480943579.81L58804728848.4 L62368502926.1 L64556073614.1 L6930241071.58 L7379195819.58 00000100600;00N00S00b01201A01F01U01V01[01`01a01l02:02;02<02K02ZFS3SP0S3SP0S3SP02lo2bs3SPL1y1HS3SP0S3SP02lo2bs3SPLS3SP02lo2bs1y2HyS3SP02lo2bs3SPLS3SP0S3SP02lo2bs3SPLFS3SP0S3SP0FS3SP02bs2LBS3SP02lo2bs2LBFFS3SP02lo2bs3SPLS3SP02lo2bs3SPL". (* [comment removed for export] *)
  Theorem printf_post : ltac2:(CDefT.buildp (gd_tbl_AW_PfShared ()) "Pfmt,$0.Plen,$0.PSP0,$0.Plo,$0.Pbs,(1.(2.&8.))Pra,(2.&40.)Pra',(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(3.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(4.(2.&8.))Pm,P,(2.&40.)(4.(2.&8.))P,(2<.R26.R23.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R28.R1.)P,(=.$9.R2.(?.R27.-200.)R25.)P,(5.$0.(6.(7.(2.&8.)R26.))+190.)P,(2>.$9.R4.+?5>40.(12.$13.(14.(1>.&40.+19;528.))(15.$13.)))P,(2>.$9.R5.+19;568.(12.$13.(30.(1>.&8.=))(15.$13.)))P,(8.$9.R6.R2:.(?.R2;.-280.))P,(:.+65?000.R2;.)P,(:.R2<.(;.R2=.+450.))P,(:.R2>.(10.+2.+3?.))P,(<.VCS,R2>.(;.R2?.R2>.))P,(27.(12.(28.$0.$0.)(29.$0.$0.R2?.R30.)(15.(28.$0.$0.)))R<.R;.)P,(2:.$9.R=.R<.)P,(17.$9.R=.)(18.$9.VAL,VCS,Lms',$19.(1:.(2.&40.)Lt0',(2.&40.)(1:.(2.&40.)Lt1',(2.&40.)(1:.(2.&40.)Lt2',(2.&40.)(1:.(2.&40.)La0',(2.&40.)(1:.(2.&40.)La1',(2.&40.)(1:.(2.&40.)La2',(2.&40.)(1:.(2.&40.)La3',(2.&40.)(1:.(2.&40.)La4',(2.&40.)(1:.(2.&40.)La5',(2.&40.)(1:.(2.&40.)La6',(2.&40.)(1:.(2.&40.)La7',(2.&40.)(1:.(2.&40.)Lt3',(2.&40.)(1:.(2.&40.)Lt4',(2.&40.)(1:.(2.&40.)Lt5',(2.&40.)(1:.(2.&40.)Lt6',(2.&40.)(1:.P,(2.&40.)(4.(2.&8.))Lm',P,(2.&40.)(4.(2.&8.))(1;.(5.$19.R11.(1<.(1=.R41.(1>.&40.R44.)R3?.R3>.R10.R?.R>.R3:.R39.R=.R<.R;.R:.R9.R8.R7.R6.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R5.R4.R3.R2.)R22.(1?.R41.)R21.(20.(2.&40.))R1.(21.$9.)))(1;.(8.$9.R1.R43.R44.)(1;.(27.(12.(28.$0.$0.)(29.$0.$0.R43.R44.)(15.(28.$0.$0.)))R20.R1.)(1;.(2:.$9.R20.R1.)(17.$9.R1.)))))))))))))))))))))(1<.(1=.R2?.(1>.&40.(?.R33.-280.))R2>.R2=.R2<.R2;.R2:.(1>.&40.R35.)(1>.&40.=)R1=.R1<.R1;.R1:.R19.R18.R17.R16.(1>.&40.(?.R33.-200.))(1>.&40.+190.)R25.(1>.&40.R34.)R23.R22.R21.R20.R1?.R1>.R15.R14.R13.R12.)R11.(1>.&40.+7>4?4.)R10.(20.(2.&40.))R>.(21.$9.)))")
(* [comment removed for export] *).
  Proof.
    intros until m. intros (j8 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & FRP & VAC & FRS & FRN) OUT LB GOTF LOGS ST LOIMG SPL SPH SCS MU WM MI. al_facts.
    (* [comment removed for export] *)
    lx_hide MU. lx_hide WM. lx_hide OUT.
    pose proof (munch_refl [(lo, SP0 + -512); (SP0 + -112, SP0)] m) as MU1. pose proof (wmono_refl asegs m) as WM1.
    lx_run (PLAN [] [] 60%N). lx_unhide.
    lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m _, STl : stk _ _ lo (SP0 + -512) |- _ =>
      eapply (u8arr_transport asegs) in OUT; [| exact MUl | exact WMl | cbn [disjoint_from]; clear -LB; lia];
      apply rw_cells_of_u8arr in OUT; release_frame OUT STl (SP0 + -112); lx_stk_grow lo;
      apply evtA_done; lx_exs; lx_ands; [ lx_mseq | assumption | lx_munch MU MUl | lx_wmono WM WMl | assumption ] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00>0?L1010978539.62 L34847044128.86L42915951118.64L47268742054.85L47512077707.62L50525402315.85L54082357164.62L56270575527.86L5855841035.62 L64909480552.85L64909923955.62L66239045604.86L68686216788.88L7227512780.62 00000;00N00Z00j01901\01j02D02E02U02\03303K03OS2VA2bs3VAHS2VA2bs3bs'4LEN'2W1S2VA2bs1x2HxS2VA2bs3bs'4LEN'S3BUF2VA2bs3VABS2SP2lo3BUF2VA2bs4SPVA3VAB3bs'4LEN'S2SP2lo2bs3SPLS2VA2bs3VAH3bs'4LEN'2B12B2FS2VA2bs3bs'4LEN'S2VA2bsS2VA2bs3VAH3bs'4LEN'2W2S2VA2bs3bs'2m'4LEN'1i2HiS2bs". (* [comment removed for export] *)
  Lemma vsn_f1_call : forall x2 x3 x4 x5 x6 x7, vsn_call_T 0x221b8 (Z_to_bv 64 0x240fe) x2 x3 x4 x5 x6 x7 33.
  Proof.
    intros x2 x3 x4 x5 x6 x7. unfold vsn_call_T. intros until m. intros LEN ST LOIMG SPL SCS SPB OUT CRB BH VAC CRV SPVA VAB VAH MI.
    destruct (CellsX.rw_cells_split3 asegs m VA [] [C8 (Z_to_bv 64 0x240fe)] [C8 x2; C8 x3; C8 x4; C8 x5; C8 x6; C8 x7] VAC) as (_ & VA1 & VA2).
    cbn [cells_size csize Nat.add] in VA1, VA2. replace (VA + Z.of_nat 0) with VA in * by lia.
    eapply (evtA_mono asegs AL CS).
    { eapply (vsn_f1_spec AL IMG ALWF CS CSOK SP lo BUF 400 VA bs); try eassumption; try lia.
      intros x Hx. apply CRV. lia. }
    cbn beta. intros ms' (a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & bs' & m' & -> & ST' & OUT' & LEN' & PR' & NUL' & VA1' & MU' & WM' & MI').
    eexists _, _, _, _, _, _, _, _, _, _, _, _, bs', m'. split; [reflexivity|].
    split; [exact ST'|]. split; [exact OUT'|]. split; [exact LEN'|]. split; [exact PR'|]. split; [exact NUL'|].
    split; [|split; [exact MU'|split; [exact WM'| exact MI']]].
    apply (CellsX.rw_cells_join3 asegs m' VA [] [C8 (Z_to_bv 64 0x240fe)] [C8 x2; C8 x3; C8 x4; C8 x5; C8 x6; C8 x7]).
    - split; [split; [exact I|]|]; cbn [cells_bytes cells_size]. { apply bytes_at_nil. destruct VA1' as [[_ (B1 & B2 & _)] _]. cbn in B2. lia. }
      destruct VA1' as [_ (W1 & W2 & _)]. split; [lia|]. split; [cbn in *; lia|]. intros i Hi. cbn in Hi. lia.
    - cbn [cells_size csize Nat.add]. replace (VA + Z.of_nat 0) with VA by lia. exact VA1'.
    - cbn [cells_size csize Nat.add]. replace (VA + Z.of_nat 0 + Z.of_nat 8) with (VA + Z.of_nat 8) by lia.
      eapply rw_cells_transport; [exact VA2| exact MU'| exact WM'|]. cbn [disjoint_from cells_size csize Nat.add]. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0?L14723109355.66L22169899659.66L34847044128.90L42915951118.68L47268742054.89L50525402315.89L53094285323.66L56270575527.90L64909480552.89L64909923955.66L65896795100.66L66239045604.90L68686216788.9200000;00J00f01201B01e01f02@02P02W02[03203SS2VA2bs3VAHS3BUF2VA2bs3VABS2v12v22v32VA2bs3bs'4LEN'2W1S2VA2bs1x2HxS2VA2bs3bs'4LEN'S2SP2lo3BUF2VA2bs4SPVA3VAB3bs'4LEN'FS2VA2bs3VAH3bs'4LEN'2B12B2S2VA2bs3bs'4LEN'S2VA2bsS2bsS2VA2bs3VAH3bs'4LEN'2W2S2v12v22v32VA2bs3bs'2m'4LEN'1i2Hi". (* [comment removed for export] *)
  Lemma vsn_f2_call : ltac2:(CDefT.buildp (gd_tbl_AW_PfShared ()) "Pv1,$0.Pv2,$0.Pv3,$0.Px4,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)P,(1;.(:.=R7.)(>.R7.(10.+2.+40.)))P,(1;.(:.=R7.)(>.R7.(10.+2.+40.)))P,(1;.(:.=R7.)(>.R7.(10.+2.+40.)))(2=.+23?;2.(1>.&40.R:.)(1>.&40.R9.)(1>.&40.R8.)R7.R6.R5.R4.(?.(?.(?.+38.(31.+:.#14.R:.))(31.+:.#14.R9.))(31.+:.#14.R8.)))")
(* [comment removed for export] *).
  Proof.
    intros v1 v2 v3 x4 x5 x6 x7 H1 H2 H3. unfold vsn_call_T. intros until m. intros LEN ST LOIMG SPL SCS SPB OUT CRB BH VAC CRV SPVA VAB VAH MI.
    destruct (CellsX.rw_cells_split3 asegs m VA [] [C8 (Z_to_bv 64 v1); C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v3)] [C8 x4; C8 x5; C8 x6; C8 x7] VAC) as (_ & VA1 & VA2).
    cbn [cells_size csize Nat.add] in VA1, VA2. replace (VA + Z.of_nat 0) with VA in * by lia.
    eapply (evtA_mono asegs AL CS).
    { eapply (vsn_f2_spec AL IMG ALWF CS CSOK v1 v2 v3 SP lo BUF 400 VA bs); try eassumption; try lia.
      intros x Hx. apply CRV. lia. }
    cbn beta. intros ms' (a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & bs' & m' & HH). cbn zeta in HH.
    destruct HH as (-> & ST' & OUT' & LEN' & PR' & NUL' & VA1' & MU' & WM' & MI').
    eexists _, _, _, _, _, _, _, _, _, _, _, _, bs', m'. split; [reflexivity|].
    split; [exact ST'|]. split; [exact OUT'|]. split; [exact LEN'|]. split; [exact PR'|]. split; [exact NUL'|].
    split; [|split; [exact MU'|split; [exact WM'| exact MI']]].
    apply (CellsX.rw_cells_join3 asegs m' VA [] [C8 (Z_to_bv 64 v1); C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v3)] [C8 x4; C8 x5; C8 x6; C8 x7]).
    - split; [split; [exact I|]|]; cbn [cells_bytes cells_size]. { apply bytes_at_nil. destruct VA1' as [[_ (B1 & B2 & _)] _]. cbn in B2. lia. }
      destruct VA1' as [_ (W1 & W2 & _)]. split; [lia|]. split; [cbn in *; lia|]. intros i Hi. cbn in Hi. lia.
    - cbn [cells_size csize Nat.add]. replace (VA + Z.of_nat 0) with VA by lia. exact VA1'.
    - cbn [cells_size csize Nat.add]. replace (VA + Z.of_nat 0 + Z.of_nat 24) with (VA + Z.of_nat 24) by lia.
      eapply rw_cells_transport; [exact VA2| exact MU'| exact WM'|]. cbn [disjoint_from cells_size csize Nat.add]. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.
