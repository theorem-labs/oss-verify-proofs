(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import MallocKit_B MallocModel_B MallocKit_B3 F_ntf_B.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_am_A F_am_K.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_F_am_C () := "C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~I35stdpp9countable9Countable00C35stdpp8fin_maps:map_insertC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4gmapBgmap_partial_alterC35stdpp4base4fmapC35stdpp4base6lookupC35stdpp4base6insertC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4optrC13~~~I35stdpp4gmap4gmap00C35stdpp8fin_maps@lookup_insert_neC47Corelib4Init5Logic8eq_ind_rC35stdpp4gmap:gmap_emptyC35stdpp4gmap9gmap_foldC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc3ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc@c_meta_area_tailC13~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes6option00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_areasC13~~~K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notK47Corelib7Numbers7BinNums1Z02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aaddC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocGc_avail_meta_area_countC13~~~C56Stdlib6ZArith6BinInt1Z3subC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocIset_avail_meta_area_countC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocDset_avail_meta_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7upd_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7a_checkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8a_nslotsC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4area01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocBset_meta_area_headC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5s_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocBset_meta_area_tailC13~~~C47Corelib4Init9Datatypes2idC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6a_nextC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9set_areasC13~~~K47Corelib4Init5Logic2eq01C35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent6F_am_K8carve_stC13~~~K47Corelib7Numbers7BinNums8positive02C35stdpp6option;from_optionC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8c_secretC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4area00C13~~~K47Corelib7Numbers7BinNums1Z01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6NSLOTSC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decI47Corelib7Numbers7BinNums1Z00C45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableI47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4mctx00C13~~~K47Corelib7Numbers7BinNums8positive03".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
Definition pgal (z : Z) : Prop := z mod 4096 = 0.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma carve_st_some st p tl ar :
  c_meta_area_tail (ctx st) = Some tl -> (s_areas st) !! tl = Some ar -> (s_areas st) !! p = None ->
  carve_st st p =
    let st1 := upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st in
    let st2 := set_areas (<[tl := mkArea (a_check ar) (Some p) (a_nslots ar)]> (s_areas st1)) st1 in
    let stC := upd_ctx (set_meta_area_tail (Some p)) st2 in
    set_areas (<[p := mkArea (c_secret (ctx st2)) None NSLOTS]> (s_areas stC)) stC.
Proof.
ltac2:(KReplay.run1 (kr_t_F_am_C ()) ["CEIL_WRAP_1"] "p'0h03Harh11oi001oh22HTh31ch42tli012tlh51Hh62arh71ph82sth92Hph:2NEh;1eh<3st1h=3st2h>3stCi021ai031xp;1p;3p;4p;6p;2p;8p;Ap;7p;5g0000R0p4p70R1p1001>p4p710R2p8P1g001\R3p4p710p8P1p10028R4p4p710R5p8P1P4p4p7210R4p8P1g002QR6p4p710p8P1g002jR7p4p710p8P1p1003Jp4p73110R8p8P1g003\R9p4p710p8P1g0040R1p4p710p8g004DR:p4p70R;P3p4p7210p8P;P3p4p73110p8P;P6p4p741110R<p8P;P7p4p741110R=p8P;P9p4p7210p8P;P9p4p73110p8P;P1p4p7210p8P;P1p4p73110p8P2P5p8P2P4p8g005RR;p4p710R>P2p8P>P5p8P>P4p8P>P8p8P;p4p741110R8g005fR>p4p73101R4p8P>p4p73100R5P4p8P>p4p7<111111111110g006HR4p4p710p8P>p4p7511100R2P<p8P<P2p8P>p4p76111100R2g006fR<p4p741110R?p8P?P2p8P>p4p771111100R2P=p8P=P2p8P>p4p7:1111111100R2g007>R=p4p741110R?p8P?P2p8P8P5p8P5P8p8g007Uj16Tg008bj1CTg00:<j33Tg00:VR8j1lTg00;8j4[Tg00;Vj6WTP;j4Uj3iTP6j4Qj3eTg00<7j11Tg00=Hj2;Tg00=jj1KTg00>Lj6OTg00>hj2kTP4j8gj6ATg00?Gj1ZTP7j4Yj3\TP3j4XTg00?`j1MTg00@>j2HTg00ALj1TTg00Bmj2STg00CJj2RTg00Dmj2GTg00FKj22Tg00G\j1FTg00Hmj1ETg00J?j37Tg00KOj1LTg00Lkj1?Tg00N:j2@j1DTg00OVj1PTg00P2j1=Tg00QBj2>Tg00RUj2jTg00Roj3fTP<j3dTg00SFj3]Tg00S]j3^TP=j3_Tg00T5j3`TP>lAaTg00TNj2bTP9j6cTg00Uaj1NTP1j7ITg00VFj5VTg00Vaj1hTf0R1,;0p=5P0g00X3R9f3R>f2R=f1R<P1Ecp=0%N1#Np=8g00YCR3?713p=BP0P9f5R3f4R7P>P=P<FI/>1p=9P9P9P=P<P1DVp=<P0P9f6R4P3P7%h>g00Ya77=P<FI/>1p=4g00[1R6?3<1p=:P0P9P7P>P=P<P1FIp=J%6>#C%5<53:%l9R;P0g00\CR5g00\aR2g00]:R?g00]XR@C[RAP5P2g00^1P?P@g00^OEWR@P9CUR?P0PAP@P9CQR2P=%17C01;9<33P?P2P7%13C0%K9R553;A3073RBP0P4f8RC#6#C%5153:P?P2P<f9RD#1REC01;94RF53;g00^mRG]0]2X40f7RH#6#CRI%54RJ53:P?P2PH%1CRKC01;9353;P;P?P2PCPEC01;9HRE93;1X1;P1P5P>EOA3;5FP;P5P8P9p-0P1PGg00_Jn10110000021000000X;;g00_fPEP1EOPG1kG1b5b0W0W2P3P1P>P=GgW5%ZBRBePBP:%53P?P0P9P?P0PAP@P9CYCXRBPH%5HRGP8P0P6P1P?PBP1P8P9P9P?P2P1g00`BREg00aRRF#8#8#8#8#8#8#MRL,HD#5%T1%MF'S/R1RF'GW3/2DRM#1RNC0%F1RO%5D%E1RP37%5CRQ#Bn10110300021010200PNPME9%LG1HCL#5/GFX3E/2CRC'2n10110300021010100RM#?'@%P9RN%K0RR#BRSP?P2PH%DGRT/2MRM#1RUC03<#=PUPMF4P?PBPHP?PBP4%F3%E377GRM%1CRUPCE9RV#6PR12TVRV#1PVF4':X1:P;1;97P?PBPHP?PBP4P8P9P9P1A7OQPR:%BGRVn10110300021010200PKDJRW/>CRX#?,@GP?P2PHPWC09<NS#=PW12TXF4P?PBPHP?PBP4PMPKDJRK/>CRX#6PRPK12TXRTF4RW':X1;P;P?P2P4%1HRYC0RZP?PBPH%?X,@GA<NS1#=PKPTF4/:WX1;RWP;P5PWP?PBP4P?PBP3%F7%E777JR7PYDJRW1HHL#5/GFX3E/2HRE'>RF#6PRPW%DJRL/2FF4,j6PZP<EAP?P2P4PWC0P0Ai0A@Af0A@Ae0A@Ad0A@A\0A@A]0A@A^0A@A_0A@PAA`0A@P9PYP3P4P7P1MAaEAP?P2P3PYC0P=EAP?PBP4P?PBP3P8P9P9P?P2P3%1ERYC0A7OGP%BJn10110300021010200PYPEE9RP#?,@JP?P2P412LPRP#1ROC09<NS#=POPPF4P?PBP4P?PBP3P7PYPEE9RY#6PR12LYRY#1PYF4RY':ePIP>EAP?PBP4P8P0P6%6E#CP?PBP1P8P9P9P?P2P1PUC0P:PVn10110300021010200PUPCE9%LJ/2En10110300021010100,2LRL#6P?P2P4%1LR2C09<NS#=P2PLF4/:Ye1bH4PEP6P?PBP4PM%11RMP1E9P6%DQ/21P6P?PBPD%6<PRPMP1F4b>b=b<':eb:W9W0W2X69X40X70X86P>P=P<P1O4X69X40X70X86o"). Qed.

Lemma carve_st_none st p :
  c_meta_area_tail (ctx st) = None -> (s_areas st) !! p = None ->
  carve_st st p =
    let st1 := upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st in
    let st2 := upd_ctx (set_meta_area_head (Some p)) st1 in
    let stC := upd_ctx (set_meta_area_tail (Some p)) st2 in
    set_areas (<[p := mkArea (c_secret (ctx st2)) None NSLOTS]> (s_areas stC)) stC.
Proof.
ltac2:(KReplay.run1 (kr_t_F_am_C ()) ["CEIL_WRAP_1"] "p'0h01ch11oh21ph32sth42HTh52Hph63st1h73st2h83stCi001ai012tli021xp;1p;3p;4p;6p;2p;7p;5g007Uj19Tg008bj1ETg00=jj1HTg00:<j36Tg00:VR0j1]Tg00;8j4WTg00;Vj6VTg005Rj4STg002Qj4PTg00<7j12Tg002jj4NTg001\j4LTg00?`j1JTg00@>j2>Tg00ALj1DTg00Bmj2CTg00CJj2BTg00Dmj28Tg00FKj21Tg00G\j1RTg00Hmj1QTg00J?j3<Tg00KOj1Fj2GTg00Lkj1:Tg00N:j2@j1?Tg00OVj1OTg00P2j1;Tg00RUj2MTg006Hj6ITg00TNj2TTg003\j6UTg00=Hj2\Tg00Uaj1KTg0040j7[Tg00QBj2ZTg00VFj5YTg00Vaj1XTg0000R1g00X3R2f3R3f2R4f1R5f0R6EUp=51\16p=3%K6#Kp=7g00YCR7?<67p=AP1P2f5R7f4R8P3P4P5F[/Z6p=0P2P2P4P5P6DYp==%X5g00Ya7<6p=4g00[1R9g004DR:%95R;#E%H1R<36%]2R=P1g00\CR>g00\aR?g00]:R@g00]XRACWRBP>P?g00^1P@PAg00^OEVRAP2CSR@P1PBPAP2CPR?P5%24C5%H2R>36P:P<P@P1P2P@P1PBPAP2CNCLRAP3%33RBP0P1P9P6P@PAP6P0P2P2P@P?P6g00`BRCg00aRRD#7#7#7#7#7#7#JRE,>7#3%D6%JDRD'C/B6RF'8W0/17RG#2RHC5%R6RI%37%Q6RJ3<%38RK#An10110200021010000PHPGE0%FBRG1>8E#3/8FX0C/18RH'1RLn10110200021010100RM#:'@%O2RN%A<ROP@P?P3%?BRP/1MRM#2RQC53=#;'4PQPME0P@PAP31>3E#3RM%:8RQ#D/CD/BQ'8,GB/4<RQ11PLRP#2PPE0569X1:P=P>P@PAP3%:L,@BA=NO6#;'4%28R8PPE0P@PAP3PQP8PPE0569X1=P@PAP4%34R=1>4E#3%:3RE#D/CD/BE'8'G/4<RE%23RD%?=RP%F=18MFX0C/13RC'1RM'1RFE0,M9P@P?P4PDC5P6EIP@PAP4%:M,@=P@P?P4%2FR=C59=NO#;'4P=PFE0P@PAP4PEP=PFE0569e%93#EP5EIP@PAP4P0P1P9%9C#EP@PAP6P0P2P2P@P?P6%2HR2C5A<IKJ%ABn10110200021010000P2PHE0PMn10110200021010100,1PRP#9P@P?P4%2PR?C59=NO#;'4P?PPE0P@PAP4%9M/4<P=PFE0569e1T34PCP911G6P9%?K/16P9P@PAP714;<%26P6E0b8b7b6569eW5W4X21X39P5P6O2X21W3o"). Qed.
End CEIL_WRAP_1.

(* [comment removed for export] *)
