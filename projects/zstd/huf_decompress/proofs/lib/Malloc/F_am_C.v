(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_B MallocModel_B MallocKit_B3 F_ntf_B.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import F_am_A F_am_K.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_am_C () := "C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C47Corelib4Init5Logic8eq_ind_rC35stdpp8fin_maps:map_insertC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC35stdpp8fin_maps@lookup_insert_neC35stdpp4gmap;gmap_finmapC35stdpp4base4fmapC35stdpp4base6lookupC35stdpp4base6insertC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indI35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes6option00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notK47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6MallocIset_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocDset_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7a_checkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8a_nslotsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4area01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBset_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBset_meta_area_tailC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9set_areasC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib6Malloc6F_am_K8carve_stC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02C35stdpp6option;from_optionC59OSSVerify5KrLib4Spec6Malloc8c_secretC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decI47Corelib7Numbers7BinNums1Z00C45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableI47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03".
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition pgal (z : Z) : Prop := z mod 4096 = 0.

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
ltac2:(KReplay.run1 (kr_t_F_am_C ()) ["CANSEC1"] "p'0h03Harh11oi001oh22HTh31ch42tli012tlh51Hh62arh71ph82sth92Hph:2NEh;1eh<3st1h=3st2h>3stCi021ai031xp;1p;3p;4p;6p;2p;8p;Ap;7p;5g0000R0p4p70R1p1000ep4p710R2p8P1g001CR3p4p710R4p8P1g001aR5p4p710p8P1p1002=R6p4p710R7p8P1P6p4p7210R6p8P1g002VR8p4p710p8P1g002oR9p4p710p8P1g003GR:p4p710p8P1g003gR;p4p710p8P1g004>R<p4p710p8P1g004UR=p4p710p8P1g004mR>p4p710p8P1g005DR?p4p710p8P1g005fR@p4p710p8P1p1006?p4p73110RAp8P1g006QRBp4p710p8P1g006eR1p4p710p8g0079RCp4p70RDg007nREp4p710p8PDP4p8PDP5p4p7210p8PDP5p4p73110p8PDP?p4p7511100RFp8PDP?p4p771111100RGp8PDP8p4p741110RHp8PDP:p4p741110RIp8PDPBp4p7210p8PDPBp4p73110p8PDP1p4p7210p8PDP1p4p73110p8PDP?p4p7<111111111110RDp8P2P7p8P2P6p8g008JRJp4p710RKP2p8PKP7p8PKP6p8PKPAp8PJp4p741110RAP?p4p73101RKp8P?p4p73100R6PKp8PDP4p8PAP6p8P6PAp8PHPFp8PFPHp8P9p4p741110RHP?p4p76111100RFp8PFPHp8PIPGp8PGPIp8P>p4p741110RIP?p4p7:1111111100RGp8PGPIp8g008^j16Tg009Rj1CTg00:Sj33Tg00:mRIj1lTg00;Oj4[Tg00;mj6WTPJj4Uj3iTP8j4Qj3eTg00<Nj11Tg00=Fj2;Tg00=hj1KTPEj6OTg00>Jj2kTP3j8gj6ATg00>ij1ZTP:j4Yj3\TP5j4XTg00?Bj1MTg00?`j2HTg00@Uj1TTg00A]j2STg00B:j2RTg00CDj2GTg00DIj22Tg00EAj1FTg00F9j1ETg00G2j37Tg00Gij1LTg00Hlj1?Tg00Ibj2@j1DTg00Jej1PTg00KAj1=Tg00L8j2>Tg00M2j2jTP;j3fTP9j3dTP<j3]TP=j3^TP>j3_TP@j3`TP?lAaTg00MLj2bTPBj6cTg00NGj1NTP1j7ITg00Nlj5VTg00OGj1hTf0R1,;0p=5P0g00P@RBf3R?f2R@f1R>P1Ecp=0%N1#Np=8g00Q7R=?71=p=BP0PBf5R=f4R<P?P@P>FI/>1p=9PBPBP@P>P1DVp=<P0PBf6R9P=P<%h?g00QU77@P>FI/>1p=4g00RLR;?3>1p=:P0PBP<P?P@P>P1FIp=J%6?#C%5>53C%lBR5P0g00SER:g00ScR3g00T<REg00TZR8C[RJP:P3g00U3PEP8g00UQEWR8PBCUREP0PJP8PBCQR3P@%1<C01;B>33PEP3P<%1=C0%KBR:535A30<=RGP0P9f8RH#6#C%5153CPEP3P>f9RF#1RAC01;B9R6535g00UoR4]0]2X40f7RD#6#CRK%59R753CPEP3PD%1HR2C01;B=535P5PEP3PHPAC01;BDRA9351X15P1P:P?EOA35:6P5P:PIPBp-0P1P4g00VLn10110000021000000X;5g00VhPAP1EOP41k41b5b0W0W2P=P1P?P@GgW5%ZGRGePGPC%5=PEP0PBPEP0PJP8PBCYCXRGPD%5DR4PIP0P;P1PEPGP1PIPBPBPEP3P1g00WDRAg00X;R6#8#8#8#8#8#8#MRL,HF#5%T1%M6'S/R1R6'GW3/2FRM#1RNC0%F1RO%5F%E1RP37%5HRQ#Bn10110300021010200PNPME9%L41HHL#5/G6X3A/2HRH'2n10110300021010100RM#?'@%PBRN%K0RR#BRSPEP3PD%D4RT/2MRM#1RUC03<#=PUPMF4PEPGPDPEPGP9%F=%E=774RM%1HRUPHE9RV#6PR12TVRV#1PVF4':X1CP51;B<PEPGPDPEPGP9PIPBPBP1A7OQPRC%B4RVn10110300021010200P2DJRW/>HRX#?,@4PEP3PDPWC09<NS#=PW12TXF4PEPGPDPEPGP9PMP2DJR2/>HRX#6PRP212TXRTF4RW':X15P5PEP3P9%1DRYC0RZPEPGPD%?X,@4A<NS1#=P2PTF4/:WX15RWP5P:PWPEPGP9PEPGP=%F<%E<777R<PYDJRW1HDL#5/G6X3A/2DRA'>R6#6PRPW%D7RL/26F4,j;PZP>EAPEP3P9PWC0P0Ai0J8Af0J8Ae0J8Ad0J8A\0J8A]0J8A^0J8A_0J8PJA`0J8PBPYP=P9P<P1MAaEAPEP3P=PYC0P@EAPEPGP9PEPGP=PIPBPBPEP3P=%1ARYC0A7O4P%B7n10110300021010200PYPAE9RP#?,@7PEP3P912LPRP#1ROC09<NS#=POPPF4PEPGP9PEPGP=P<PYPAE9RY#6PR12LYRY#1PYF4RY':ePKP?EAPEPGP9PIP0P;%6A#CPEPGP1PIPBPBPEP3P1PUC0PCPVn10110300021010200PUPHE9%L7/2An10110300021010100,2LRL#6PEP3P9%1LR3C09<NS#=P3PLF4/:Ye1bD9PAP;PEPGP9PM%11RMP1E9P;%DQ/21P;PEPGPF%6>PRPMP1F4b>b=b<':eb:W9W0W2X6BX40X70X8;P?P@P>P1O4X6BX40X70X8;o"). Qed.

Lemma carve_st_none st p :
  c_meta_area_tail (ctx st) = None -> (s_areas st) !! p = None ->
  carve_st st p =
    let st1 := upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st in
    let st2 := upd_ctx (set_meta_area_head (Some p)) st1 in
    let stC := upd_ctx (set_meta_area_tail (Some p)) st2 in
    set_areas (<[p := mkArea (c_secret (ctx st2)) None NSLOTS]> (s_areas stC)) stC.
Proof.
ltac2:(KReplay.run1 (kr_t_F_am_C ()) ["CANSEC1"] "p'0h01ch11oh21ph32sth42HTh52Hph63st1h73st2h83stCi001ai012tli021xp;1p;3p;4p;6p;2p;7p;5g008^j19Tg009Rj1ETg00=hj1HTg00:Sj36Tg00:mR0j1]Tg00;Oj4WTg00;mj6VTg008Jj4STg002Vj4PTg00<Nj12Tg003Gj4NTg001aj4LTg00?Bj1JTg00?`j2>Tg00@Uj1DTg00A]j2CTg00B:j2BTg00CDj28Tg00DIj21Tg00EAj1RTg00F9j1QTg00G2j3<Tg00Gij1Fj2GTg00Hlj1:Tg00Ibj2@j1?Tg00Jej1OTg00KAj1;Tg00M2j2MTg001Cj6ITg00MLj2TTg006Qj6UTg00=Fj2\Tg00NGj1KTg006ej7[Tg00L8j2ZTg00Nlj5YTg00OGj1XTg0000R1g00P@R2f3R3f2R4f1R5f0R6EUp=51\16p=3%K6#Kp=7g00Q7R7?<67p=AP1P2f5R7f4R8P3P4P5F[/Z6p=0P2P2P4P5P6DYp==%X5g00QU7<6p=4g00RLR9g0079R:%95R;#E%H1R<36%]2R=P1g00SER>g00ScR?g00T<R@g00TZRACWRBP>P?g00U3P@PAg00UQEVRAP2CSR@P1PBPAP2CPR?P5%24C5%H2R>36P:P<P@P1P2P@P1PBPAP2CNCLRAP3%33RBP0P1P9P6P@PAP6P0P2P2P@P?P6g00WDRCg00X;RD#7#7#7#7#7#7#JRE,>7#3%D6%JDRD'C/B6RF'8W0/17RG#2RHC5%R6RI%37%Q6RJ3<%38RK#An10110200021010000PHPGE0%FBRG1>8E#3/8FX0C/18RH'1RLn10110200021010100RM#:'@%O2RN%A<ROP@P?P3%?BRP/1MRM#2RQC53=#;'4PQPME0P@PAP31>3E#3RM%:8RQ#D/CD/BQ'8,GB/4<RQ11PLRP#2PPE0569X1:P=P>P@PAP3%:L,@BA=NO6#;'4%28R8PPE0P@PAP3PQP8PPE0569X1=P@PAP4%34R=1>4E#3%:3RE#D/CD/BE'8'G/4<RE%23RD%?=RP%F=18MFX0C/13RC'1RM'1RFE0,M9P@P?P4PDC5P6EIP@PAP4%:M,@=P@P?P4%2FR=C59=NO#;'4P=PFE0P@PAP4PEP=PFE0569e%93#EP5EIP@PAP4P0P1P9%9C#EP@PAP6P0P2P2P@P?P6%2HR2C5A<IKJ%ABn10110200021010000P2PHE0PMn10110200021010100,1PRP#9P@P?P4%2PR?C59=NO#;'4P?PPE0P@PAP4%9M/4<P=PFE0569e1T34PCP911G6P9%?K/16P9P@PAP714;<%26P6E0b8b7b6569eW5W4X21X39P5P6O2X21W3o"). Qed.

End CANSEC1.
