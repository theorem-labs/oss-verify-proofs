(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcR.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PStmt. Import PStmt.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BigLinkZA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Jb0PlanKit AsanPlanCore
BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_drA LibSegJb_drB LibSegJb_drD LibSegJb_drDs LibSegJb_drEa LibSegJb_drFa LibSegJb_drGa LibSegJb_dfA LibSegJb_dfG.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module AS0DIAGRP.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_drA : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_drA.regs0 LibSegJb_drA.regs_out0).
Lemma KS_drA_ok : BG.kept_ok 140 LibSegJb_drA.regs0 LibSegJb_drA.regs_out0 KS_drA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition drA_conc_s := ",14A#v2p#2#40A#v21p#2#40A#v22p#2#40S,1#:76>0S,2v2S,:#138;:8S,;#1?0=5S,<v21B#7???7?811000v2#800000000000Hv2#10I_v2#930#930Ja_v2#930#930O#10000#136000B#7???7?811000v21#7?????????>?B#1v22#1P_v2#930#930v21+v22#1La#7???;>18#Na#13=718#1Na#1<>5;<#1La#13<:38#7???8000,1_v2#930#930,1,47X#62=34#66>28Y,T,1#66=20T,2_v2#930T,8_v2#70T,9^#?#???????????????T,:v21T,;#T,<#73T,=#73T,>#T,12#:T,13#1?0>:T,14#15<6?T,15_v2#28T,16v21T,17#9T,18_v2#8?8T,19^#:#:::::::::::::::T,1:^#?#???????????????T,1;#25Nb_v2#8?4#73Lb_v2#900#1?0>:Nb_v2#8?8#Lb_v2#908#1?0>8Lb_v2#910^#?#???????????????Nb_v2#8?1#Nb_v2#8?2#Nb_v2#8?3#Nb_v2#8?5#Nb_v2#8?6#Nb_v2#8?7#Nb_v2#911#Nb_v2#912#Nb_v2#913#Nb_v2#914#Nb_v2#915#Nb_v2#916#Nb_v2#917#Nb_v2#918#Lb_v2#928_v2#>8Lb_v2#920#207?2Lb_v2#=8r1;Lb_v2#=0r1:Lb_v2#<8r19Lb_v2#<0r18Lb_v2#;8r17Lb_v2#;0r16Lb_v2#:8r15Lb_v2#:0r14Lb_v2#98r13Lb_v2#90_v2#30Lb_v2#88#138;:8Lb_v2#80#1?0=5Lb_v2#78#67<:8Lb_v2#60_v2#30Lb_v2#58_v2#30Lb_v2#68_v2#30Lb_v2#18r?Lb_v2#20r>Lb_v2#28r=Lb_v2#30v21Lb_v2#8r11Lb_v2#10r10Lb_v2#50r12Lb_v2#48r9Lb_v2#40r8Lb_v2#38#:76>0Jb_v2#930#8Jb_v2#8?0#818Jb_v2#70#8"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma drA_conc : ltac:(r1mk L5.defined [KS_drA] fx R M V drA_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_drA] LibSegJb_drA.regs0 LibSegJb_drA.kn0 LibSegJb_drA.BR LibSegJb_drA.PSS LibSegJb_drA.NX0 LibSegJb_drA.F0 404788 LibSegJb_drA.seg_sound_ax fx R M V drA_conc_s. Qed.
End SE.
Definition KS_drB : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_drB.regs0 LibSegJb_drB.regs_out0).
Lemma KS_drB_ok : BG.kept_ok 140 LibSegJb_drB.regs0 LibSegJb_drB.regs_out0 KS_drB = true. Proof. vm_compute. reflexivity. Qed.
Definition drB_conc_s := ",49A#v2p#2#40A#v13p#2#40A#v14p#2#40A#v15p#2#40A#v16p#2#40A#v17p#2#40A#v18p#2#40A#v19p#2#40A#v1:p#2#40A#v1;p#2#40A#v21p#2#40A#v22p#2#40A#v28p#2#40A#v78p#2#40A#v79p#2#40A#v7:p#2#40A#v7;p#2#40S,2v2S,8+v2#8<0S,13#1?0>:S,14v78S,15v79S,16v7:S,17v7;S,18+v2#38S,19^#:#:::::::::::::::S,1:^#?#???????????????S,1;#25B#7???7?811000v2#800000000000Hv2#10I_v2#380#<40Ja_v2#380#<40O#10000#136000B#7???7?811000v21#7?????????>?B#1v22#1P_v2#380#<40v21+v22#1Ka+/v2#8#7???80=>#20La#7???;>18#I#138;:8#4I#138;;0#8I#138;;8#8I#138;<8#8I#138;=0#8I#138;>0#8I#138<00#8I#138<08#8I#138<30#4La+v2#8;8#67<:8La+v2#8;0#1?0=5La+v2#8:8#138;:8La+v2#8:0+v2#900La+v2#898v13La+v2#890v14La+v2#888v15La+v2#880v16La+v2#878v17La+v2#870v18La+v2#868v19La+v2#860v1:La+v2#858v1;La#136230#11=??<La+v2#8=8+v2#900La#690;00v28Ma#138<34#????????Ma#138;:8#5La#138<08#La#138<00#6912=8Ma#138<30#Ma#138<38#????????Na#13=719#1La#13<:38#7???8000La#1363:8#1267>4La+v2#900v21,:_v2#380#<40#138;:8#4#138;;0#8#138;;8#8#138;<8#8#138;=0#8#138;>0#8#138<00#8#138<08#8#138<30#4,1,62X#66=8<#62<>8Y,T,1#11>7<4T,2+v2#530T,5#T,6#6?T,7#6>T,8#25T,9#7???????T,:v21T,;#7???????T,<+v2#750T,=+v2#908T,>#1?T,?^#?#?????????????<6T,10#73T,11#8T,12#7?????><T,13#13T,14#138;:8T,15#1?0>:T,16#T,17v21T,18#T,19^#?#???????????????T,1:#T,1;#T,1<#20Lb+v2#5:0v21Lb+v2#750+v2#908Lb#138;=0+v2#773Nb+v2#772#20Nb+v2#771#6>Nb+v2#770#6?Nb+v2#76?#20Nb+v2#76>#72Nb+v2#76=#6?Nb+v2#76<#72Nb+v2#76;#72Nb+v2#76:#65Nb+v2#769#20Nb+v2#768#64Nb+v2#767#61Nb+v2#766#65Nb+v2#765#72Nb+v2#764#20Nb+v2#763#3:Nb+v2#762#69Nb+v2#761#6<Nb+v2#760#63Lb+v2#558^#?#???????<<<<<<<=Lb+v2#560^#?#??????????>????Lb+v2#598#<<<<<<<Lb+v2#580#12889Lb+v2#6>0v28Lb+v2#590#690;00Lb+v2#588#Lb+v2#578+v2#750Lb+v2#568+v2#7;0Lb+v2#570+v2#858Lb+v2#6>8v1;Lb+v2#6?0v1:Lb+v2#6?8v19Lb+v2#700v18Lb+v2#708v17Lb+v2#710v16Lb+v2#718#5Lb+v2#720#6912=8Lb+v2#728#1Lb+v2#730#690;00Lb+v2#738#1?0=5Lb+v2#740#138;:8Lb+v2#748#11>104Lb#138;<8+v2#7;0Lb#138;;8#Lb#138;;0#Lb#138;>0+v2#760Mb#138<30^#?#???????????????Lb#138<08#50Lb#138<00+v2#760Mb#138;:8#5Lb+v2#870#Lb+v2#868#Lb+v2#860#Lb+v2#858#Lb+v2#878#Lb+v2#758+v2#900Lb+v2#880v28Lb+v2#888v15Lb+v2#890v14Lb+v2#898v13Lb+v2#8:0+v2#900Lb+v2#8:8#138;:8Lb+v2#8;0#1?0=5Lb+v2#8;8#67<>8Jb+v2#530#28Jb+v2#5:8#138Jb+v2#773#>5"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma drB_conc : ltac:(r1mk L5KA.zeros_at [KS_drB] fx R M V drB_conc_s).
Proof.
r1pf L5KA.zeros_at [KS_drB] LibSegJb_drB.regs0 LibSegJb_drB.kn0 LibSegJb_drB.BR LibSegJb_drB.PSS LibSegJb_drB.NX0 LibSegJb_drB.F0 421260 LibSegJb_drB.seg_sound_ax fx R M V drB_conc_s. Qed.
End SE.
Definition KS_drD : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_drD.regs0 LibSegJb_drD.regs_out0).
Lemma KS_drD_ok : BG.kept_ok 140 LibSegJb_drD.regs0 LibSegJb_drD.regs_out0 KS_drD = true. Proof. vm_compute. reflexivity. Qed.
Definition drD_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2v2S,8#25S,9#7???????S,:#1S,12#7?????><S,13#13S,14#138;:8S,15#1?0>:S,16#S,17v21S,19^#?#???????????????S,1:#B#7???7?811000v2#800000000000Hv2#10I_v2#8;0#8>0Ja_v2#8;0#8>0O#10000#136000B#7???7?811000v21#7?????????>?B#1v22#1P_v2#8;0#8>0v21+v22#1I#138;=0#8Na#138;:8#5La#138;<8+v2#280La#138;=0+v2#243Ma#138<38#????????Na#13=719#1La#1363:8#1267>4Na+v21#1#,2_v2#8;0#8>0#138;=0#8,1,15X#11>7<4#11>=10Y,T,1#11>;><T,:v21T,;#1T,<#138;:8T,=+v2#243T,>#T,?#3T,12#T,18#T,19#1T,1:#1T,1;#1Lb#138;=0+v2#243Lb+v2#8#Lb+v2#20#1Lb+v2#10#1Lbv2#10=<3Lb+v2#18#Jb+v2#28#8"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma drD_conc : ltac:(r1mk L5.defined [KS_drD] fx R M V drD_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_drD] LibSegJb_drD.regs0 LibSegJb_drD.kn0 LibSegJb_drD.BR LibSegJb_drD.PSS LibSegJb_drD.NX0 LibSegJb_drD.F0 1173444 LibSegJb_drD.seg_sound_ax fx R M V drD_conc_s. Qed.
End SE.
Definition KS_drDs : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_drDs.regs0 LibSegJb_drDs.regs_out0).
Lemma KS_drDs_ok : BG.kept_ok 140 LibSegJb_drDs.regs0 LibSegJb_drDs.regs_out0 KS_drDs = true. Proof. vm_compute. reflexivity. Qed.
Definition drDs_conc_s := ",18A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2v2S,8#25S,9#7???????S,:v21S,;#1S,<#138;:8S,12#S,13#13S,14#138;:8S,15#1?0>:B#7???7?811000v2#800000000000Hv2#10I_v2#40#40Ja_v2#40#40O#10000#136000B#7???7?811000v21#7?????????>?B#1v22#1P_v2#40#40v21+v22#1La#138;<8+v2#280La#138;=0+v2#243Ma#138<38#????????,1_v2#40#40,1,13X#11>=10#77608Y,T,1#11=;;0T,2_v2#40T,8#138;:8T,9#1T,:+v2#243T,;v21T,<#1T,12v21T,13#Lb_v2#38#1?0>:Lb_v2#30#138;:8Lb_v2#28#13Lb_v2#20#Lb_v2#18#7???????Lb_v2#10#25Lb_v2#8#11>=14Jb_v2#40#8"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma drDs_conc : ltac:(r1mk L5.defined [KS_drDs] fx R M V drDs_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_drDs] LibSegJb_drDs.regs0 LibSegJb_drDs.kn0 LibSegJb_drDs.BR LibSegJb_drDs.PSS LibSegJb_drDs.NX0 LibSegJb_drDs.F0 1174800 LibSegJb_drDs.seg_sound_ax fx R M V drDs_conc_s. Qed.
End SE.
Definition KS_drEa : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_drEa.regs0 LibSegJb_drEa.regs_out0).
Lemma KS_drEa_ok : BG.kept_ok 140 LibSegJb_drEa.regs0 LibSegJb_drEa.regs_out0 KS_drEa = true. Proof. vm_compute. reflexivity. Qed.
Definition drEa_conc_s := ",1<A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2v2S,8#138;:8S,9#1S,13#S,1:#1B#7???7?811000v2#800000000000Hv2#10I_v2#10#50Ja_v2#10#50O#10000#136000B#7???7?811000v21#7?????????>?B#1v22#1P_v2#10#50v21+v22#1I#138;=0#8La#138;=0+v2#283La+v2#38#11>=14La+v2#30#25La+v2#28#7???????La+v2#20#La+v2#18#13La+v2#10#138;:8La+v2#8#1?0>:Na#138;:8#5La#138;<8+v2#2<0Ma#138<38#????????,2_v2#10#50#138;=0#8,1,13X#11=;;0#77608Y,T,1#11=;;0T,:+v2#284T,;#1?0>:T,<#1T,12#1?0>:T,14#138;:8T,15#1?0>;T,16#1T,17#1?0>:Lb+v2#8#1?0>;Lb+v2#10#138;:8Lb+v2#18#14Lb+v2#20#7?????>;Lb+v2#28#7???????Lb+v2#30#25Lb+v2#38#11>2?4Lb#138;=0+v2#284"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma drEa_conc : ltac:(r1mk L5.defined [KS_drEa] fx R M V drEa_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_drEa] LibSegJb_drEa.regs0 LibSegJb_drEa.kn0 LibSegJb_drEa.BR LibSegJb_drEa.PSS LibSegJb_drEa.NX0 LibSegJb_drEa.F0 1170352 LibSegJb_drEa.seg_sound_ax fx R M V drEa_conc_s. Qed.
End SE.
Definition KS_drFa : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_drFa.regs0 LibSegJb_drFa.regs_out0).
Lemma KS_drFa_ok : BG.kept_ok 140 LibSegJb_drFa.regs0 LibSegJb_drFa.regs_out0 KS_drFa = true. Proof. vm_compute. reflexivity. Qed.
Definition drFa_conc_s := ",3:A#v2p#2#40A#v16p#2#40A#v17p#2#40A#v18p#2#40A#v19p#2#40A#v1:p#2#40A#v1;p#2#40A#v21p#2#40A#v22p#2#40A#v28p#2#40A#v7;p#2#40A#v7<p#2#40A#v7=p#2#40A#v7?p#2#40S,2v2S,8#138;:8S,9#1S,13#S,16#1S,17v7;S,18v7<S,19v7=S,1:#1S,1;v7?B#7???7?811000v2#800000000000Hv2#10I_v2#10#270Ja_v2#10#270O#10000#136000B#7???7?811000v21#7?????????>?B#1v22#1P_v2#10#270v21+v22#1I#138;=0#8La#138;=0+v2#284La+v2#38#11>2?4La+v2#30#25La+v2#28#7???????La+v2#20#7?????>;La+v2#18#14La+v2#10#138;:8La+v2#8#1?0>;La+v2#:0#690;00La#690;00v28La+v2#1?0v28La+v2#258#11>104La+v2#250#138;:8La+v2#248#1?0=5La+v2#240#690;00La+v2#238#1La+v2#230#6912=8La+v2#228#5La+v2#220v16La+v2#218v17La+v2#210v18La+v2#208v19La+v2#200v1:La+v2#1?8v1;La#138;?0#11=0;4,2_v2#10#270#138;=0#8,1,23X#11=;;0#11=0?0Y,T,1#11>124T,2+v2#1?0T,8#T,9#138;:8T,:v28T,;#T,<#T,=#11=0;4T,12#690;00T,13#1T,14#6912=8T,15#690;00T,16v16T,17v17T,18v18T,19v19T,1:v1:T,1;v1;Lb+v2#218v28Lb+v2#220v16Lb+v2#228#Lb+v2#230#6912=8Lb+v2#238#1Lb+v2#240#690;00Lb+v2#248#15Lb+v2#250#138;:8Lb+v2#258#11>124Lb#138;=0+v2#285Lb+v2#1?0v28Lb+v2#210v18Lb+v2#208v19Lb+v2#200v1:Lb+v2#1?8v1;"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma drFa_conc : ltac:(r1mk L5.defined [KS_drFa] fx R M V drFa_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_drFa] LibSegJb_drFa.regs0 LibSegJb_drFa.kn0 LibSegJb_drFa.BR LibSegJb_drFa.PSS LibSegJb_drFa.NX0 LibSegJb_drFa.F0 1170352 LibSegJb_drFa.seg_sound_ax fx R M V drFa_conc_s. Qed.
End SE.
Definition KS_drGa : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_drGa.regs0 LibSegJb_drGa.regs_out0).
Lemma KS_drGa_ok : BG.kept_ok 140 LibSegJb_drGa.regs0 LibSegJb_drGa.regs_out0 KS_drGa = true. Proof. vm_compute. reflexivity. Qed.
Definition drGa_conc_s := ",3>A#v2p#2#40A#v8p#2#40A#v9p#2#40A#v12p#2#40A#v13p#2#40A#v14p#2#40A#v15p#2#40A#v16p#2#40A#v21p#2#40A#v22p#2#40A#v28p#2#40A#v76p#2#40A#v77p#2#40A#v78p#2#40A#v7:p#2#40S,2v2S,8#S,9#138;:8S,12v76S,13v77S,14v78S,15#690;00S,16v7:B#7???7?811000v2#800000000000Hv2#10I_v2#10#10Ja_v2#10#10O#10000#136000B#7???7?811000v21#7?????????>?B#1v22#1P_v2#10#10v21+v22#1I#138;:8#4I#138;<8#8I#138;=0#8I#138;>0#8I#138<00#8I#138<08#8La#138<00+v2#80La#138<08#50La#690;00v28La+v2#28v28La+v2#68#11>124La+v2#60#138;:8La+v2#58#15La+v2#50#690;00La+v2#48#1La+v2#40#6912=8La+v2#38#La+v2#30v16Ma#138;:8#5La+v2#1:0v28La+v2#1=8#67<>8La+v2#1=0#1?0=5La+v2#1<8#138;:8La+v2#1<0+v2#220La+v2#1;8v13La+v2#1;0v14La+v2#1:8v15La+v2#218#:76>0La+v2#210v8La+v2#208v9La+v2#200v12,7_v2#10#10#138;:8#4#138;<8#8#138;=0#8#138;>0#8#138<00#8#138<08#8,1,14X#11=148#11575<Y,T,1#:770<T,2+v2#250T,8v8T,9v9T,:#2T,;v28T,<v28T,12v12T,13v13T,14v14T,15v15T,16v16Mb#138;:8#5Lb#138<08#Lb#138<00#6912=8Lb#138;>0#Lb#138;=0#Lb#138;<8#"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma drGa_conc : ltac:(r1mk L5.defined [KS_drGa] fx R M V drGa_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_drGa] LibSegJb_drGa.regs0 LibSegJb_drGa.kn0 LibSegJb_drGa.BR LibSegJb_drGa.PSS LibSegJb_drGa.NX0 LibSegJb_drGa.F0 1167688 LibSegJb_drGa.seg_sound_ax fx R M V drGa_conc_s. Qed.
End SE.
Definition KS_dfA : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_dfA.regs0 LibSegJb_dfA.regs_out0).
Lemma KS_dfA_ok : BG.kept_ok 140 LibSegJb_dfA.regs0 LibSegJb_dfA.regs_out0 KS_dfA = true. Proof. vm_compute. reflexivity. Qed.
Definition dfA_conc_s := ",25A#v2p#2#40A#v28p#2#40S,1#:76>0S,2v2S,:#138;:8S,;#1::09S,<#4000000B#7???7?811000v2#800000000000Hv2#10I_v2#<;0#<;0Ja_v2#<;0#<;0O#10000#136000Ka+/v2#8#7???7?88#50La#7???;540#I#138;:8#4I#138;;0#8I#138;;8#8I#138;<8#8I#138;=0#8I#138;>0#8I#138<00#8I#138<08#8I#138<30#4Na#13=718#1Na#1<>5;<#1La#13<:38#7???8000La#136230#11=??<La#690;00v28Ma#138<34#????????Ma#138;:8#5La#138<08#La#138<00#6912=8Ma#138<30#Ma#138<38#????????Na#13=719#1La#1363:8#1267>4La#138;?0#11=0;4,:_v2#<;0#<;0#138;:8#4#138;;0#8#138;;8#8#138;<8#8#138;=0#8#138;>0#8#138<00#8#138<08#8#138<30#4,1,71X#62=34#11=0?0Y,T,1#11>124T,2_v2#250T,5_v2#1:;T,6#72T,7#65T,8#T,9#138;:8T,:v28T,;#T,<#T,=#11=0;4T,>#T,?#73T,10#65T,11#64T,12#690;00T,13#1T,14#6912=8T,15#690;00T,1<#66Lb_v2#228v28Lb_v2#220r16Lb_v2#218#Lb_v2#210#6912=8Lb_v2#208#1Lb_v2#200#690;00Lb_v2#1?8#26Lb_v2#1?0#138;:8Lb_v2#1>8#11>124Lb#138;=0_v2#1::Nb_v2#1:;#:Nb_v2#1:<#64Nb_v2#1:=#65Nb_v2#1:>#73Nb_v2#1:?#75Nb_v2#1;0#66Nb_v2#1;1#65Nb_v2#1;2#72Nb_v2#1;3#20Nb_v2#1;4#2<Nb_v2#1;5#73Nb_v2#1;6#65Nb_v2#1;7#74Nb_v2#1;8#79Nb_v2#1;9#62Nb_v2#1;:#20Nb_v2#1;;#34Nb_v2#1;<#36Nb_v2#1;=#38Nb_v2#1;>#38Nb_v2#1;?#30Nb_v2#1<0#31Nb_v2#1<1#37Nb_v2#1<2#36Lb_v2#1>0_v2#28Nb_v2#1<3#20Nb_v2#1<4#3=Nb_v2#1<5#3>Nb_v2#1<6#20Nb_v2#1<7#74Nb_v2#1<8#75Nb_v2#1<9#70Nb_v2#1<:#6>Nb_v2#1<;#69Nb_v2#1<<#20Nb_v2#1<=#3:Nb_v2#1<>#69Nb_v2#1<?#6<Nb_v2#1=0#63Lb_v2#250v28Lb_v2#248r1;Lb_v2#240r1:Lb_v2#238r19Lb_v2#230r18Lb#138;<8_v2#180Lb#138;;8#Lb#138;;0#Lb#138;>0_v2#1=0Mb#138<30^#?#???????????????Lb#138<08#50Lb#138<00_v2#1=0Mb#138;:8#5Lb_v2#<0#Lb_v2#<8#Lb_v2#=0#Lb_v2#=8#Lb_v2#;8#Lb_v2#1=8_v2#30Lb_v2#;0v28Lb_v2#:8r15Lb_v2#:0r14Lb_v2#98r13Lb_v2#90_v2#30Lb_v2#88#138;:8Lb_v2#80#1::09Lb_v2#78#67<>8Lb_v2#60_v2#30Lb_v2#58_v2#30Lb_v2#68_v2#30Lb_v2#18r?Lb_v2#20r>Lb_v2#28r=Lb_v2#30#4000000Lb_v2#8r11Lb_v2#10r10Lb_v2#50r12Lb_v2#48r9Lb_v2#40r8Lb_v2#38#:76>0Jb_v2#1::#=2Jb_v2#70#8"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma dfA_conc : ltac:(r1mk L5KA.zeros_at [KS_dfA] fx R M V dfA_conc_s).
Proof.
r1pf L5KA.zeros_at [KS_dfA] LibSegJb_dfA.regs0 LibSegJb_dfA.kn0 LibSegJb_dfA.BR LibSegJb_dfA.PSS LibSegJb_dfA.NX0 LibSegJb_dfA.F0 404788 LibSegJb_dfA.seg_sound_ax fx R M V dfA_conc_s. Qed.
End SE.
Definition KS_dfG : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_dfG.regs0 LibSegJb_dfG.regs_out0).
Lemma KS_dfG_ok : BG.kept_ok 140 LibSegJb_dfG.regs0 LibSegJb_dfG.regs_out0 KS_dfG = true. Proof. vm_compute. reflexivity. Qed.
Definition dfG_conc_s := ",39A#v2p#2#40A#v8p#2#40A#v9p#2#40A#v12p#2#40A#v13p#2#40A#v14p#2#40A#v15p#2#40A#v16p#2#40A#v28p#2#40A#v76p#2#40A#v77p#2#40A#v78p#2#40A#v7:p#2#40S,2v2S,8#S,9#138;:8S,12v76S,13v77S,14v78S,15#690;00S,16v7:B#7???7?811000v2#800000000000Hv2#10I_v2#10#10Ja_v2#10#10O#10000#136000I#138;:8#4I#138;<8#8I#138;=0#8I#138;>0#8I#138<00#8I#138<08#8La#138<00+v2#80La#138<08#50La#690;00v28La+v2#28v28La+v2#68#11>124La+v2#60#138;:8La+v2#58#26La+v2#50#690;00La+v2#48#1La+v2#40#6912=8La+v2#38#La+v2#30v16Ma#138;:8#5La+v2#1:0v28La+v2#1=8#67<>8La+v2#1=0#1::09La+v2#1<8#138;:8La+v2#1<0+v2#220La+v2#1;8v13La+v2#1;0v14La+v2#1:8v15La+v2#218#:76>0La+v2#210v8La+v2#208v9La+v2#200v12,7_v2#10#10#138;:8#4#138;<8#8#138;=0#8#138;>0#8#138<00#8#138<08#8,1,14X#11=148#11575<Y,T,1#:770<T,2+v2#250T,8v8T,9v9T,:#2T,;v28T,<v28T,12v12T,13v13T,14v14T,15v15T,16v16Mb#138;:8#5Lb#138<08#Lb#138<00#6912=8Lb#138;>0#Lb#138;=0#Lb#138;<8#"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma dfG_conc : ltac:(r1mk L5.defined [KS_dfG] fx R M V dfG_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_dfG] LibSegJb_dfG.regs0 LibSegJb_dfG.kn0 LibSegJb_dfG.BR LibSegJb_dfG.PSS LibSegJb_dfG.NX0 LibSegJb_dfG.F0 1167688 LibSegJb_dfG.seg_sound_ax fx R M V dfG_conc_s. Qed.
End SE.
End AS0DIAGRP.
