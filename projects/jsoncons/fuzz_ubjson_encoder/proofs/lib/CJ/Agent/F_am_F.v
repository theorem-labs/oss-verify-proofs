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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_syscalls F_mm_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import MallocKit_B MallocModel_B MallocKit_B3 F_ntf_B.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_am_A F_am_K F_am_C.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac showregs := lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ ?m _) => idtac "REGS" R "PC" pc "MEM" m end.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_F_am_F () := "C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5s_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc@c_meta_area_tailC13~~~I35stdpp4gmap4gmap00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC35stdpp4gmapBgmap_partial_alterC35stdpp8fin_maps:map_insertC35stdpp4gmap;gmap_lookupK47Corelib7Numbers7BinNums1Z02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aaddC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocGc_avail_meta_area_countC13~~~C56Stdlib6ZArith6BinInt1Z3subC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocIset_avail_meta_area_countC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocDset_avail_meta_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7upd_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7a_checkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8a_nslotsC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4area01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9set_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocBset_meta_area_headC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocBset_meta_area_tailC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8c_secretC13~~~C47Corelib4Init9Datatypes2idK47Corelib4Init9Datatypes6option02C35stdpp6option;from_optionC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6a_nextC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9s_regionsC13~~~I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc3ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent6F_am_K8carve_stC13~~~K47Corelib4Init9Datatypes6option01K47Corelib7Numbers7BinNums8positive02C35stdpp4base6lookupC35stdpp4base6insertC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4area00C13~~~K47Corelib7Numbers7BinNums1Z01I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4optrC13~~~I47Corelib4Init9Datatypes6option00I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6region00C13~~~I47Corelib7Numbers7BinNums1Z00C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4mctx00C13~~~K47Corelib7Numbers7BinNums8positive03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6NSLOTSC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6Decode<dec_mprotectC13~~~C56Stdlib6ZArith6BinInt1Z3eqbK99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6Decode9range_ans01C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6Decode9range_ans02C13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent6F_am_F9mp_strictC13~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notC47Corelib4Init5Logic7f_equalI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive01K47Corelib4Init5Logic3and01C47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes?RelationClasses;reflexivityC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog?dec_mprotect_rwC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6Decode9range_ans00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6ENOSYSC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree4respC13~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes4bool02".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma carve_st_regions st p : s_regions (carve_st st p) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_F_am_F ()) ["CEIL_WRAP_1"] "p'0h01ch11ph22sth31ai001ah41oi011oi022tli031xp;1p;4p;6p;2p;3p;5p;7g0000j1ETg001?j1HTg002Yj4?Tg002mj4JTg003Kj6YTg003lj4TTg004Lj4QTg004hj4NTg005Aj1@Tg005_j28Tg006mj1ITg008Nj2XTg008kj2UTg00:Nj25Tg00;lj21Tg00==j19Tg00>Nj1PTg00?_j1OTg00A1j34Tg00BAj2:Tg00CTj1CTg00E0j2Mj1ATg00FLj1=Tg00G^j1LTg00H:j1KTg00H\j5BTg00I7j1FTg00JGj12Tg00KZj3<Tg00L4j2>Tg00LNj1DTg00M[j2RTg00Nnj2STg00OPj1GTg00P5j6WTg00PIj7VTg00P]R0f0R1'Sp=0%G1#Gp=3P0g00QkR2f3R3f2R4f1R5P1EWp=7g00S;R6?416p=;P0P2f4R6P3P4P5P1FVp=6g00SYR7%E5#Hg00Tkg00V9R8P0g00V[R9g00W9R:g00WRR;g00X0C?R<P0P9P:g00YBR=g00Y`R>CJR?P9P:P;P=P>g00Z9EYR>P2C?R=P0P2P=P0P?P>P2CTCQR;P4%04R:P8P0P7P1P=P;P1P8P2P2P=P0P?P>P2CNR>P1g00ZWR?g00[gR9#3#3#3#3#3#3#@R@,86#0%I1%@9'X/U1R9'5W0/16RA#9RBC7%P1RC%06%O1RD34%03#;n10110300021010000PBD6/:A%C:183@#0/59X0?/13'1n10110300021010200RA#E'M#=P2P2%L2RB%K0#;REP=P>P4%A:/1ARA#9RFC7DB#Fg00\LRG34PFD6/:A#2%233<P1%26,><X30P1O1%24,><n10110101021010000b4P=P;P1%01R6#AP8P0P7185@#0/59X0?/15R3#D#HP=P;P1P8P2P2P=P>P1184@#0/59X0?/14R4#9R?C7A4C:D%05#;n10110300021010000P?D6/:4%C6/13n10110300021010200'1R3#D#=P2P2PBPEP=P>P1%93R>C7DB#F;4GP>D6/:3#2%25R35<<e1R51#2=<<3eX10X27P5P1O2X10W2o"). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mp_strict (a : range_ans) : Prop := match a with RgErr e => e <> 38 | RgDone b => b = true end.
Lemma dec_mprotect_rw_weaken A L rsp a : dec_mprotect_rw A L rsp = Some a -> dec_mprotect A L rsp = Some a /\ mp_strict a.
Proof.
ltac2:(KReplay.run1 (kr_t_F_am_F ()) ["CEIL_WRAP_1"] "p'0h01Hh12H0h22H1h31ah41ri001rh51ei011eh61oi021oh71Ah82H2h91Lh:1bi031bh;2e0h<3rsph=2e1h>1ni041ni057changedi061xp;3p;1p;2p;6p;4p;7g00]\j3DTg00V9R0j1NTg00_1j2@Tg00H:j1GTg00_Nj14Tg00`bj1:Tg00KZR1j30j1LTg00b6j12Tg00cJj2FTg00clR2j2ETg00dOj67j7>Tg00dkj2<Tg00eJj1BTg00ecj6ATg00f@j26Tg00L4j28Tg00OPj1;Tg00f[j1?Tg005Aj1MTg00g@j4=Tg00g[j1KTg00hJj4HTg00i8j3ITg00Nnj2JTg00jOR3f0R4'Jp=1f3R5f2R6f1R730/64p=3g00YBR8g00kcR9704p=9%24,67p=CA0374p=5g00m3R:AD567%N3R;P0P3P0P3P;P4P3P;P4g00n?R<P;1@49R=%G3R>%44#1n0100000020000P<P;P4g00n_R?#:R@#1RAP>n0110500020000RBn0110000021010110105RCP>n10110600021010000%16RD50;P;P7%15RE%25RFC3[P4P3f4RG#190;CP;%17RCf5RH#1RI%2HC3[P41F49%94/E=1@79P<P2%96P<P;P7P>%4G#1R2n0100000020000f9R9#1R=50;%4H#1RJf:RK#1RL50;RM/CK[P7%95RNA0;>=P;P>P0P3p-0P4g00o?ROg00o\n10110200021000000RPX=;g0108RQPLP4E7POf6RR#4#1f;RS#1RT50;RU/CS/<4b1W0W;P4O1%BNA0;2=P1P;PJf<RJ#1R290;7P;f8RN#4RV#1f=RW#1%2WC3[P4P;P3P0P3P3P4P4PVn10110200021010000X;;f7RX#4RY#1RZP2P4EA15YJ15VWP4%49f>'5P3%4KRW%4SRV#1RY%14R[50;R\%24R]'6X43P3PWP;%4JR^#1R_P_%2^C3^0\X33%1WRW=0;WA0;YY%2VRV18;YPXg00[g#;#;#?#?#;#M908S#BePVeC=W0f?RVP7PHF>PVP4E7b8W2P4O1b2X1UP4O1X1Mn2002102000000100A0;4TP;PZP2%2JC3[X6;PLO1P418;TO1b1W0W>P4O1n10210310000021010111104b:b4X58P4O1P<%1RRR90;BP;%:7#1%1XRB%2XRXC3[P4A0;AIP1P;PA%1NR190;7P;PAP=%29C3[P4A0;ARA0;ABP;P3P0P3P3P4P4P@n10110200021010000X5;PAP1P4EA15@N15@9P415@KP3P@A0;A[RK/6]X43P3P@A0;AAR]%2@R@'6^0KX33P]P@P;%L;%K;PACH18<?C=X0]PSP7PHF>PSP4E7b8W2P4O1b2W1P4O1W1n2002102000000100A0;4BP;PAP1%2NC3[X6;PRO1P418;BO1b1W0A0;>IP;P>PPX5;RPPQPRP4E7POP;g010T#:#1PBPXC3/<4b1W0n0110300020100X:<P4O1n0110000021110111105X43P4O1A0;>CP;P>PPPQPDP4E7POP;P>PEPFC3/<4b1W0n10110200021110000b6AI567=0;[P;ADG56PC%27C3[eX33X<:X98X78P5P6P7P4O4X33W<X98X78o"). Qed.
End CEIL_WRAP_1.

