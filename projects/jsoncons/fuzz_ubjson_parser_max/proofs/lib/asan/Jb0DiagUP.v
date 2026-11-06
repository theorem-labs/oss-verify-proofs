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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_duA LibSegJb_duB LibSegJb_duD LibSegJb_duDs LibSegJb_duDl LibSegJb_duEa LibSegJb_duEb LibSegJb_duFa LibSegJb_duGa LibSegJb_duGb1 LibSegJb_duGb2 LibSegJb_duEc LibSegJb_duGc.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module AS0DIAGUP.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_duA : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_duA.regs0 LibSegJb_duA.regs_out0).
Lemma KS_duA_ok : BG.kept_ok 140 LibSegJb_duA.regs0 LibSegJb_duA.regs_out0 KS_duA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition duA_conc_s := ",14A#v2p#2#40A#v21p#2#40A#v22p#2#40S,1#:7630S,2v2S,:#138;:8S,;#16222S,<v21B#7???7?811000v2#800000000000Hv2#10I_v2#930#930Ja_v2#930#930O#10000#136000B#7???7?811000v21#7?????????>?B#v22#1????P_v2#930#930v21+v22#1La#7???:<40#Na#13=718#1Na#1<>5;<#1La#13<:38#7???8000,1_v2#930#930,1,47X#62=34#66>28Y,T,1#66=20T,2_v2#930T,8_v2#70T,9^#?#???????????????T,:v21T,;#T,<#73T,=#73T,>#T,12#:T,13#1622;T,14#15<6?T,15_v2#28T,16v21T,17#9T,18_v2#8?8T,19^#:#:::::::::::::::T,1:^#?#???????????????T,1;#25Nb_v2#8?4#73Lb_v2#900#1622;Nb_v2#8?8#Lb_v2#908#16229Lb_v2#910^#?#???????????????Nb_v2#8?1#Nb_v2#8?2#Nb_v2#8?3#Nb_v2#8?5#Nb_v2#8?6#Nb_v2#8?7#Nb_v2#911#Nb_v2#912#Nb_v2#913#Nb_v2#914#Nb_v2#915#Nb_v2#916#Nb_v2#917#Nb_v2#918#Lb_v2#928_v2#>8Lb_v2#920#207?2Lb_v2#=8r1;Lb_v2#=0r1:Lb_v2#<8r19Lb_v2#<0r18Lb_v2#;8r17Lb_v2#;0r16Lb_v2#:8r15Lb_v2#:0r14Lb_v2#98r13Lb_v2#90_v2#30Lb_v2#88#138;:8Lb_v2#80#16222Lb_v2#78#67<:8Lb_v2#60_v2#30Lb_v2#58_v2#30Lb_v2#68_v2#30Lb_v2#18r?Lb_v2#20r>Lb_v2#28r=Lb_v2#30v21Lb_v2#8r11Lb_v2#10r10Lb_v2#50r12Lb_v2#48r9Lb_v2#40r8Lb_v2#38#:7630Jb_v2#930#8Jb_v2#8?0#818Jb_v2#70#8"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma duA_conc : ltac:(r1mk L5.defined [KS_duA] fx R M V duA_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_duA] LibSegJb_duA.regs0 LibSegJb_duA.kn0 LibSegJb_duA.BR LibSegJb_duA.PSS LibSegJb_duA.NX0 LibSegJb_duA.F0 404788 LibSegJb_duA.seg_sound_ax fx R M V duA_conc_s. Qed.
End SE.
Definition KS_duB : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_duB.regs0 LibSegJb_duB.regs_out0).
Lemma KS_duB_ok : BG.kept_ok 140 LibSegJb_duB.regs0 LibSegJb_duB.regs_out0 KS_duB = true. Proof. vm_compute. reflexivity. Qed.
Definition duB_conc_s := ",49A#v2p#2#40A#v13p#2#40A#v14p#2#40A#v15p#2#40A#v16p#2#40A#v17p#2#40A#v18p#2#40A#v19p#2#40A#v1:p#2#40A#v1;p#2#40A#v21p#2#40A#v22p#2#40A#v28p#2#40A#v78p#2#40A#v79p#2#40A#v7:p#2#40A#v7;p#2#40S,2v2S,8+v2#8<0S,13#1622;S,14v78S,15v79S,16v7:S,17v7;S,18+v2#38S,19^#:#:::::::::::::::S,1:^#?#???????????????S,1;#25B#7???7?811000v2#800000000000Hv2#10I_v2#380#<40Ja_v2#380#<40O#10000#136000B#7???7?811000v21#7?????????>?B#v22#1????P_v2#380#<40v21+v22#1Ka+/v2#8#7???80=>#18La#7???:<40#I#138;:8#4I#138;;0#8I#138;;8#8I#138;<8#8I#138;=0#8I#138;>0#8I#138<00#8I#138<08#8I#138<30#4La+v2#8;8#67<:8La+v2#8;0#16222La+v2#8:8#138;:8La+v2#8:0+v2#900La+v2#898v13La+v2#890v14La+v2#888v15La+v2#880v16La+v2#878v17La+v2#870v18La+v2#868v19La+v2#860v1:La+v2#858v1;La#136230#11=??<La+v2#8=8+v2#900La#690;00v28Ma#138<34#????????Ma#138;:8#5La#138<08#La#138<00#6912=8Ma#138<30#Ma#138<38#????????Na#13=719#1La#13<:38#7???8000La#1363:8#1267>4La+v2#900v21,:_v2#380#<40#138;:8#4#138;;0#8#138;;8#8#138;<8#8#138;=0#8#138;>0#8#138<00#8#138<08#8#138<30#4,1,53X#66=8<#62<>8Y,T,1#11>7<4T,2+v2#530T,5#T,8#25T,9#7???????T,:v21T,;#7???????T,<+v2#750T,=+v2#908T,>#1?T,?^#?#?????????????<6T,10#73T,11#8T,12#7??????8T,13#7T,14#138;:8T,15#1622;T,16#T,17v21T,18#T,19^#?#???????????????T,1:#T,1;#Lb+v2#5:0v21Lb+v2#750+v2#908Lb#138;=0+v2#767Nb+v2#766#20Nb+v2#765#3:Nb+v2#764#65Nb+v2#763#67Nb+v2#762#61Nb+v2#761#73Nb+v2#760#75Lb+v2#558^#?#???????<<<<<<<=Lb+v2#560^#?#??????????>????Lb+v2#598#<<<<<<<Lb+v2#580#12889Lb+v2#6>0v28Lb+v2#590#690;00Lb+v2#588#Lb+v2#578+v2#750Lb+v2#568+v2#7;0Lb+v2#570+v2#858Lb+v2#6>8v1;Lb+v2#6?0v1:Lb+v2#6?8v19Lb+v2#700v18Lb+v2#708v17Lb+v2#710v16Lb+v2#718#5Lb+v2#720#6912=8Lb+v2#728#1Lb+v2#730#690;00Lb+v2#738#16222Lb+v2#740#138;:8Lb+v2#748#11>104Lb#138;<8+v2#7;0Lb#138;;8#Lb#138;;0#Lb#138;>0+v2#760Mb#138<30^#?#???????????????Lb#138<08#50Lb#138<00+v2#760Mb#138;:8#5Lb+v2#870#Lb+v2#868#Lb+v2#860#Lb+v2#858#Lb+v2#878#Lb+v2#758+v2#900Lb+v2#880v28Lb+v2#888v15Lb+v2#890v14Lb+v2#898v13Lb+v2#8:0+v2#900Lb+v2#8:8#138;:8Lb+v2#8;0#16222Lb+v2#8;8#67<>8Jb+v2#530#28Jb+v2#5:8#138Jb+v2#767#?1"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma duB_conc : ltac:(r1mk L5KA.zeros_at [KS_duB] fx R M V duB_conc_s).
Proof.
r1pf L5KA.zeros_at [KS_duB] LibSegJb_duB.regs0 LibSegJb_duB.kn0 LibSegJb_duB.BR LibSegJb_duB.PSS LibSegJb_duB.NX0 LibSegJb_duB.F0 421260 LibSegJb_duB.seg_sound_ax fx R M V duB_conc_s. Qed.
End SE.
Definition KS_duD : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_duD.regs0 LibSegJb_duD.regs_out0).
Lemma KS_duD_ok : BG.kept_ok 140 LibSegJb_duD.regs0 LibSegJb_duD.regs_out0 KS_duD = true. Proof. vm_compute. reflexivity. Qed.
Definition duD_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2v2S,8#25S,9#7???????S,:v22S,12#7??????8S,13#7S,14#138;:8S,15#1622;S,16#S,17v21S,19^#?#???????????????S,1:#B#7???7?811000v2#800000000000Hv2#10I_v2#8;0#8>0Ja_v2#8;0#8>0O#10000#136000B#7???7?811000v21#7?????????>?B#v22#1????P_v2#8;0#8>0v21+v22#1I#138;=0#8Na#138;:8#5La#138;<8+v2#280La#138;=0+v2#237Ma#138<38#????????Na#13=719#1La#1363:8#1267>4Na+v21v22#,2_v2#8;0#8>0#138;=0#8,1,15X#11>7<4#11>=10Y,T,1#11>;><T,:v21T,;v22T,<#138;:8T,=+v2#237T,>#T,?#3T,12#T,18#T,19v22T,1:v22T,1;v22Lb#138;=0+v2#237Lb+v2#8#Lb+v2#20v22Lb+v2#10v22Lbv2#10=<3Lb+v2#18#Jb+v2#28#8"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma duD_conc : ltac:(r1mk L5.defined [KS_duD] fx R M V duD_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_duD] LibSegJb_duD.regs0 LibSegJb_duD.kn0 LibSegJb_duD.BR LibSegJb_duD.PSS LibSegJb_duD.NX0 LibSegJb_duD.F0 1173444 LibSegJb_duD.seg_sound_ax fx R M V duD_conc_s. Qed.
End SE.
Definition KS_duDs : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_duDs.regs0 LibSegJb_duDs.regs_out0).
Lemma KS_duDs_ok : BG.kept_ok 140 LibSegJb_duDs.regs0 LibSegJb_duDs.regs_out0 KS_duDs = true. Proof. vm_compute. reflexivity. Qed.
Definition duDs_conc_s := ",18A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2v2S,8#25S,9#7???????S,:v21S,;v22S,<#138;:8S,12#S,13#7S,14#138;:8S,15#1622;B#7???7?811000v2#800000000000Hv2#10I_v2#40#40Ja_v2#40#40O#10000#136000B#7???7?811000v21#7?????????>?B#v22#49P_v2#40#40v21+v22#1La#138;<8+v2#280La#138;=0+v2#237Ma#138<38#????????,1_v2#40#40,1,13X#11>=10#77608Y,T,1#11=;;0T,2_v2#40T,8#138;:8T,9v22T,:+v2#237T,;v21T,<v22T,12v21T,13#Lb_v2#38#1622;Lb_v2#30#138;:8Lb_v2#28#7Lb_v2#20#Lb_v2#18#7???????Lb_v2#10#25Lb_v2#8#11>=14Jb_v2#40#8"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma duDs_conc : ltac:(r1mk L5.defined [KS_duDs] fx R M V duDs_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_duDs] LibSegJb_duDs.regs0 LibSegJb_duDs.kn0 LibSegJb_duDs.BR LibSegJb_duDs.PSS LibSegJb_duDs.NX0 LibSegJb_duDs.F0 1174800 LibSegJb_duDs.seg_sound_ax fx R M V duDs_conc_s. Qed.
End SE.
Definition KS_duDl : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_duDl.regs0 LibSegJb_duDl.regs_out0).
Lemma KS_duDl_ok : BG.kept_ok 140 LibSegJb_duDl.regs0 LibSegJb_duDl.regs_out0 KS_duDl = true. Proof. vm_compute. reflexivity. Qed.
Definition duDl_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v28p#2#40S,2v2S,8#25S,9#7???????S,:v21S,;v22S,<#138;:8S,12#S,13#7S,14#138;:8S,15#1622;S,16#B#7???7?811000v2#800000000000Hv2#10I_v2#70#70Ja_v2#70#70O#10000#136000B#7???7?811000v21#7?????????>?B#4:v22#1????P_v2#70#70v21+v22#1La#138;<8+v2#280La#138;=0+v2#237La#138;?0#11=0;4La#690;00v28,1_v2#70#70,1,15X#11>=10#11=0?0Y,T,1#11>=14T,2_v2#70T,6#11=0;4T,8v22T,9#138;:8T,:v28T,;v21T,<v22T,15#690;00Lb_v2#48v28Lb_v2#40#Lb_v2#38#1622;Lb_v2#30#138;:8Lb_v2#28#7Lb_v2#20#Lb_v2#18#7???????Lb_v2#10#25Lb_v2#8#11>=14Jb_v2#70#28"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma duDl_conc : ltac:(r1mk L5.defined [KS_duDl] fx R M V duDl_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_duDl] LibSegJb_duDl.regs0 LibSegJb_duDl.kn0 LibSegJb_duDl.BR LibSegJb_duDl.PSS LibSegJb_duDl.NX0 LibSegJb_duDl.F0 1174800 LibSegJb_duDl.seg_sound_ax fx R M V duDl_conc_s. Qed.
End SE.
Definition KS_duEa : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_duEa.regs0 LibSegJb_duEa.regs_out0).
Lemma KS_duEa_ok : BG.kept_ok 140 LibSegJb_duEa.regs0 LibSegJb_duEa.regs_out0 KS_duEa = true. Proof. vm_compute. reflexivity. Qed.
Definition duEa_conc_s := ",1<A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2v2S,8#138;:8S,9v22S,13#S,1:v22B#7???7?811000v2#800000000000Hv2#10I_v2#10#50Ja_v2#10#50O#10000#136000B#7???7?811000v21#7?????????>?B#v22#42P_v2#10#50v21+v22#1I#138;=0#8La#138;=0+v2#277La+v2#38#11>=14La+v2#30#25La+v2#28#7???????La+v2#20#La+v2#18#7La+v2#10#138;:8La+v2#8#1622;Na#138;:8#5La#138;<8+v2#2<0Ma#138<38#????????,2_v2#10#50#138;=0#8,1,15X#11=;;0#77608Y,T,1#11=;;0T,9#7T,:++v2v22#277T,;#1622;T,<#7T,12#1622;T,14#138;:8T,15#16232T,16#7T,17#1622;T,1:#7Lb+v2#8#16232Lb+v2#10#138;:8Lb+v2#18+v22#7Lb+v2#20+*-1v22#7??????8Lb+v2#28#7???????Lb+v2#30#25Lb+v2#38#11>2?4Lb#138;=0++v2v22#277"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma duEa_conc : ltac:(r1mk L5.defined [KS_duEa] fx R M V duEa_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_duEa] LibSegJb_duEa.regs0 LibSegJb_duEa.kn0 LibSegJb_duEa.BR LibSegJb_duEa.PSS LibSegJb_duEa.NX0 LibSegJb_duEa.F0 1170352 LibSegJb_duEa.seg_sound_ax fx R M V duEa_conc_s. Qed.
End SE.
Definition KS_duEb : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_duEb.regs0 LibSegJb_duEb.regs_out0).
Lemma KS_duEb_ok : BG.kept_ok 140 LibSegJb_duEb.regs0 LibSegJb_duEb.regs_out0 KS_duEb = true. Proof. vm_compute. reflexivity. Qed.
Definition duEb_conc_s := ",1>A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v28p#2#40S,2v2S,8#138;:8S,9v22S,13#S,1:v22B#7???7?811000v2#800000000000Hv2#10I_v2#30#70Ja_v2#30#70O#10000#136000B#7???7?811000v21#7?????????>?B#43v22#49P_v2#30#70v21+v22#1I#138;=0#8La#138;=0+v2#277La+v2#38#11>=14La+v2#30#25La+v2#28#7???????La+v2#20#La+v2#18#7La+v2#10#138;:8La+v2#8#1622;Na#138;:8#5La#138;<8+v2#2<0La#138;?0#11=0;4La#690;00v28,2_v2#30#70#138;=0#8,1,1<X#11=;;0#11=0?0Y,T,1#11>2?4T,2_v2#30T,6#11=0;4T,8#7T,9#138;:8T,:v28T,;#1622;T,<#7T,12+*-1v22#7??????8T,13+v22#7T,14#138;:8T,15#690;00T,16#7T,17#1622;T,1:#7Lb_v2#8v28Lbv2#7Lb+v2#8#16232Lb+v2#10#138;:8Lb+v2#18+v22#7Lb+v2#20+*-1v22#7??????8Lb+v2#28#7???????Lb+v2#30#25Lb+v2#38#11>2?4Lb#138;=0++v2v22#277Jb_v2#30#28"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma duEb_conc : ltac:(r1mk L5.defined [KS_duEb] fx R M V duEb_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_duEb] LibSegJb_duEb.regs0 LibSegJb_duEb.kn0 LibSegJb_duEb.BR LibSegJb_duEb.PSS LibSegJb_duEb.NX0 LibSegJb_duEb.F0 1170352 LibSegJb_duEb.seg_sound_ax fx R M V duEb_conc_s. Qed.
End SE.
Definition KS_duFa : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_duFa.regs0 LibSegJb_duFa.regs_out0).
Lemma KS_duFa_ok : BG.kept_ok 140 LibSegJb_duFa.regs0 LibSegJb_duFa.regs_out0 KS_duFa = true. Proof. vm_compute. reflexivity. Qed.
Definition duFa_conc_s := ",3:A#v2p#2#40A#v16p#2#40A#v17p#2#40A#v18p#2#40A#v19p#2#40A#v1:p#2#40A#v1;p#2#40A#v21p#2#40A#v22p#2#40A#v28p#2#40A#v7;p#2#40A#v7<p#2#40A#v7=p#2#40A#v7?p#2#40S,2v2S,8#138;:8S,9#7S,13#S,16#7S,17v7;S,18v7<S,19v7=S,1:#7S,1;v7?B#7???7?811000v2#800000000000Hv2#10I_v2#10#270Ja_v2#10#270O#10000#136000B#7???7?811000v21#7?????????>?B#v22#42P_v2#10#270v21+v22#1I#138;=0#8La#138;=0++v2v22#277La+v2#38#11>2?4La+v2#30#25La+v2#28#7???????La+v2#20_#7??????8v22La+v2#18+v22#7La+v2#10#138;:8La+v2#8#16232La+v2#:0#690;00La#690;00v28La+v2#1?0v28La+v2#258#11>104La+v2#250#138;:8La+v2#248#16222La+v2#240#690;00La+v2#238#1La+v2#230#6912=8La+v2#228#5La+v2#220v16La+v2#218v17La+v2#210v18La+v2#208v19La+v2#200v1:La+v2#1?8v1;La#138;?0#11=0;4,2_v2#10#270#138;=0#8,1,23X#11=;;0#11=0?0Y,T,1#11>124T,2+v2#1?0T,8#T,9#138;:8T,:v28T,;#T,<#T,=#11=0;4T,12#690;00T,13#1T,14#6912=8T,15#690;00T,16v16T,17v17T,18v18T,19v19T,1:v1:T,1;v1;Lb+v2#218v28Lb+v2#220v16Lb+v2#228#Lb+v2#230#6912=8Lb+v2#238#1Lb+v2#240#690;00Lb+v2#248+v22#>Lb+v2#250#138;:8Lb+v2#258#11>124Lb#138;=0++v2v22#27>Lb+v2#1?0v28Lb+v2#210v18Lb+v2#208v19Lb+v2#200v1:Lb+v2#1?8v1;"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma duFa_conc : ltac:(r1mk L5.defined [KS_duFa] fx R M V duFa_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_duFa] LibSegJb_duFa.regs0 LibSegJb_duFa.kn0 LibSegJb_duFa.BR LibSegJb_duFa.PSS LibSegJb_duFa.NX0 LibSegJb_duFa.F0 1170352 LibSegJb_duFa.seg_sound_ax fx R M V duFa_conc_s. Qed.
End SE.
Definition KS_duGa : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_duGa.regs0 LibSegJb_duGa.regs_out0).
Lemma KS_duGa_ok : BG.kept_ok 140 LibSegJb_duGa.regs0 LibSegJb_duGa.regs_out0 KS_duGa = true. Proof. vm_compute. reflexivity. Qed.
Definition duGa_conc_s := ",4?A#v2p#2#40A#v8p#2#40A#v9p#2#40A#v12p#2#40A#v13p#2#40A#v14p#2#40A#v15p#2#40A#v16p#2#40A#v21p#2#40A#v22p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v76p#2#40A#v77p#2#40A#v78p#2#40A#v7:p#2#40S,2v2S,8#S,9#138;:8S,12v76S,13v77S,14v78S,15#690;00S,16v7:B#7???7?811000v2#800000000000Hv2#10I_v2#10#10Ja_v2#10#10O#10000#136000B#7???7?811000v21#7?????????>?B#v22#42P_v2#10#10v21+v22#1I#138;:8#4I#138;<8#8I#138;=0#8I#138;>0#8I#138<00#8I#138<08#8La#138<00+v2#80La#138<08#50La#690;00v28La+v2#28v28La+v2#68#11>124La+v2#60#138;:8La+v2#58+v22#>La+v2#50#690;00La+v2#48#1La+v2#40#6912=8La+v2#38#La+v2#30v16Ma#138;:8#5La+v2#1:0v28La+v2#1=8#67<>8La+v2#1=0#16222La+v2#1<8#138;:8La+v2#1<0+v2#220La+v2#1;8v13La+v2#1;0v14La+v2#1:8v15La+v2#218#:7630La+v2#210v8La+v2#208v9La+v2#200v12La+v2#298#114?94La+v2#290v29La+v2#288v2:La+v2#280v2;La+v2#278v2<La+v2#270v2=La+v2#268v2>La+v2#260v2?La+v2#258v30,7_v2#10#10#138;:8#4#138;<8#8#138;=0#8#138;>0#8#138<00#8#138<08#8,1,15X#11=148#11575<Y,T,1#114?98T,2+v2#2:0T,8v29T,9v2:T,:v8T,;v28T,<v28T,12v2;T,13v2<T,14v2=T,15v2>T,16v2?T,17v30Mb#138;:8#5Lb#138<08#Lb#138<00#6912=8Lb#138;>0#Lb#138;=0#Lb#138;<8#"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma duGa_conc : ltac:(r1mk L5.defined [KS_duGa] fx R M V duGa_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_duGa] LibSegJb_duGa.regs0 LibSegJb_duGa.kn0 LibSegJb_duGa.BR LibSegJb_duGa.PSS LibSegJb_duGa.NX0 LibSegJb_duGa.F0 1167688 LibSegJb_duGa.seg_sound_ax fx R M V duGa_conc_s. Qed.
End SE.
Definition KS_duGb1 : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_duGb1.regs0 LibSegJb_duGb1.regs_out0).
Lemma KS_duGb1_ok : BG.kept_ok 140 LibSegJb_duGb1.regs0 LibSegJb_duGb1.regs_out0 KS_duGb1 = true. Proof. vm_compute. reflexivity. Qed.
Definition duGb1_conc_s := ",40A#v2p#2#40A#v16p#2#40A#v17p#2#40A#v18p#2#40A#v19p#2#40A#v1:p#2#40A#v1;p#2#40A#v21p#2#40A#v22p#2#40A#v28p#2#40A#v7:p#2#40A#v7;p#2#40A#v7<p#2#40A#v7=p#2#40A#v7?p#2#40S,2v2S,8#7S,9#138;:8S,15#690;00S,16v7:S,17v7;S,18v7<S,19v7=S,1:#7S,1;v7?B#7???7?811000v2#800000000000Hv2#10I_v2#10#2:0Ja_v2#10#2:0O#10000#136000B#7???7?811000v21#7?????????>?B#43v22#49P_v2#10#2:0v21+v22#1I#138;<8#8I#138;=0#8I#138;>0#8La#138<00+v2#2:0La#138<08#50La#690;00v28La+v2#28v28La+v2#68#11>2?4La+v2#60#25La+v2#58#7???????La+v2#50_#7??????8v22La+v2#48+v22#7La+v2#40#138;:8La+v2#38#16232La+v2#30#7La+v2#=0#690;00La+v2#220v28La+v2#288#11>104La+v2#280#138;:8La+v2#278#16222La+v2#270#690;00La+v2#268#1La+v2#260#6912=8La+v2#258#5La+v2#250v16La+v2#248v17La+v2#240v18La+v2#238v19La+v2#230v1:La+v2#228v1;La#138;?0#11=0;4,4_v2#10#2:0#138;<8#8#138;=0#8#138;>0#8,1,23X#11=148#11=0?0Y,T,1#11>124T,2+v2#220T,8#T,:v28T,;#T,<#T,=#11=0;4T,12#690;00T,13#1T,14#6912=8T,16v16T,17v17T,18v18T,19v19T,1:v1:T,1;v1;Lb+v2#248v28Lb+v2#250v16Lb+v2#258#Lb+v2#260#6912=8Lb+v2#268#1Lb+v2#270#690;00Lb+v2#278+v22#>Lb+v2#280#138;:8Lb+v2#288#11>124Lb#138;>0+v2#2:0Lb#138;=0+v2#2:0Lb#138;<8+v2#2?0Lb+v2#220v28Lb+v2#240v18Lb+v2#238v19Lb+v2#230v1:Lb+v2#228v1;"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma duGb1_conc : ltac:(r1mk L5.defined [KS_duGb1] fx R M V duGb1_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_duGb1] LibSegJb_duGb1.regs0 LibSegJb_duGb1.kn0 LibSegJb_duGb1.BR LibSegJb_duGb1.PSS LibSegJb_duGb1.NX0 LibSegJb_duGb1.F0 1167688 LibSegJb_duGb1.seg_sound_ax fx R M V duGb1_conc_s. Qed.
End SE.
Definition KS_duGb2 : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_duGb2.regs0 LibSegJb_duGb2.regs_out0).
Lemma KS_duGb2_ok : BG.kept_ok 140 LibSegJb_duGb2.regs0 LibSegJb_duGb2.regs_out0 KS_duGb2 = true. Proof. vm_compute. reflexivity. Qed.
Definition duGb2_conc_s := ",4?A#v2p#2#40A#v8p#2#40A#v9p#2#40A#v12p#2#40A#v13p#2#40A#v14p#2#40A#v15p#2#40A#v16p#2#40A#v21p#2#40A#v22p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v76p#2#40A#v77p#2#40A#v78p#2#40A#v7:p#2#40S,2v2S,8#S,9#138;:8S,12v76S,13v77S,14v78S,15#690;00S,16v7:B#7???7?811000v2#800000000000Hv2#10I_v2#10#10Ja_v2#10#10O#10000#136000B#7???7?811000v21#7?????????>?B#43v22#49P_v2#10#10v21+v22#1I#138;:8#4I#138;<8#8I#138;=0#8I#138;>0#8I#138<00#8I#138<08#8La#138<00+v2#80La#138<08#50La#690;00v28La+v2#28v28La+v2#68#11>124La+v2#60#138;:8La+v2#58+v22#>La+v2#50#690;00La+v2#48#1La+v2#40#6912=8La+v2#38#La+v2#30v16Ma#138;:8#5La+v2#1:0v28La+v2#1=8#67<>8La+v2#1=0#16222La+v2#1<8#138;:8La+v2#1<0+v2#220La+v2#1;8v13La+v2#1;0v14La+v2#1:8v15La+v2#218#:7630La+v2#210v8La+v2#208v9La+v2#200v12La+v2#298#114?94La+v2#290v29La+v2#288v2:La+v2#280v2;La+v2#278v2<La+v2#270v2=La+v2#268v2>La+v2#260v2?La+v2#258v30,7_v2#10#10#138;:8#4#138;<8#8#138;=0#8#138;>0#8#138<00#8#138<08#8,1,15X#11=148#11575<Y,T,1#114?98T,2+v2#2:0T,8v29T,9v2:T,:v8T,;v28T,<v28T,12v2;T,13v2<T,14v2=T,15v2>T,16v2?T,17v30Mb#138;:8#5Lb#138<08#Lb#138<00#6912=8Lb#138;>0#Lb#138;=0#Lb#138;<8#"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma duGb2_conc : ltac:(r1mk L5.defined [KS_duGb2] fx R M V duGb2_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_duGb2] LibSegJb_duGb2.regs0 LibSegJb_duGb2.kn0 LibSegJb_duGb2.BR LibSegJb_duGb2.PSS LibSegJb_duGb2.NX0 LibSegJb_duGb2.F0 1167688 LibSegJb_duGb2.seg_sound_ax fx R M V duGb2_conc_s. Qed.
End SE.
Definition KS_duEc : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_duEc.regs0 LibSegJb_duEc.regs_out0).
Lemma KS_duEc_ok : BG.kept_ok 140 LibSegJb_duEc.regs0 LibSegJb_duEc.regs_out0 KS_duEc = true. Proof. vm_compute. reflexivity. Qed.
Definition duEc_conc_s := ",46A#v2p#2#40A#v16p#2#40A#v17p#2#40A#v18p#2#40A#v19p#2#40A#v1:p#2#40A#v1;p#2#40A#v21p#2#40A#v22p#2#40A#v28p#2#40A#v7:p#2#40A#v7;p#2#40A#v7=p#2#40A#v7?p#2#40S,2v2S,8v22S,9#138;:8S,15#690;00S,16v7:S,17v7;S,18#S,19v7=S,1:v22S,1;v7?B#7???7?811000v2#800000000000Hv2#10I_v2#840#:?0Ja_v2#840#:?0O#10000#136000B#7???7?811000v21#7?????????>?B#4:v22#1????P_v2#840#:?0v21+v22#1Ka+/v2#8#7???8046#18La#7???:<40#I#138;<8#8I#138;=0#8I#138;>0#8La#138<00+v2#2:0La#138<08#50La#690;00v28La+v2#28v28La+v2#68#11>=14La+v2#60#25La+v2#58#7???????La+v2#50#La+v2#48#7La+v2#40#138;:8La+v2#38#1622;La+v2#30#Na#138;:8#5Ma#138<38#????????Na#13=719#1La#13<:38#7???8000La#1363:8#1267>4La+v2#=0#690;00La+v2#220v28La+v2#288#11>104La+v2#280#138;:8La+v2#278#16222La+v2#270#690;00La+v2#268#1La+v2#260#6912=8La+v2#258#5La+v2#250v16La+v2#248v17La+v2#240v18La+v2#238v19La+v2#230v1:La+v2#228v1;La#138;?0#11=0;4,4_v2#840#:?0#138;<8#8#138;=0#8#138;>0#8,1,31X#11=148#11=0?0Y,T,1#11>124T,2+v2#220T,5+v2#2:5T,8#T,:v28T,;#T,<#T,=#11=0;4T,>#54T,?#:T,10+v2#2:7T,11#55T,12#690;00T,13#1T,14#6912=8T,16v16T,17v17T,18v18T,19v19T,1:v1:T,1;v1;Lb+v2#248v28Lb+v2#250v16Lb+v2#258#Lb+v2#260#6912=8Lb+v2#268#1Lb+v2#270#690;00Lb+v2#278+v22#>Lb+v2#280#138;:8Lb+v2#288#11>124Lb#138;=0+v2#2:7Nb+v2#2:6#:Nb+v2#2:5#54Nb+v2#2:4#55Nb+v2#2:3#50Nb+v2#2:2#4>Nb+v2#2:1#49Nb+v2#2:0#20Lb#138;>0+v2#2:0Lb#138;<8+v2#2?0Jb+v2#290#10Jb+v2#2:7#9Lb+v2#220v28Lb+v2#240v18Lb+v2#238v19Lb+v2#230v1:Lb+v2#228v1;"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma duEc_conc : ltac:(r1mk L5KA.zeros_at [KS_duEc] fx R M V duEc_conc_s).
Proof.
r1pf L5KA.zeros_at [KS_duEc] LibSegJb_duEc.regs0 LibSegJb_duEc.kn0 LibSegJb_duEc.BR LibSegJb_duEc.PSS LibSegJb_duEc.NX0 LibSegJb_duEc.F0 1167688 LibSegJb_duEc.seg_sound_ax fx R M V duEc_conc_s. Qed.
End SE.
Definition KS_duGc : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_duGc.regs0 LibSegJb_duGc.regs_out0).
Lemma KS_duGc_ok : BG.kept_ok 140 LibSegJb_duGc.regs0 LibSegJb_duGc.regs_out0 KS_duGc = true. Proof. vm_compute. reflexivity. Qed.
Definition duGc_conc_s := ",4?A#v2p#2#40A#v8p#2#40A#v9p#2#40A#v12p#2#40A#v13p#2#40A#v14p#2#40A#v15p#2#40A#v16p#2#40A#v21p#2#40A#v22p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v76p#2#40A#v77p#2#40A#v78p#2#40A#v7:p#2#40S,2v2S,8#S,9#138;:8S,12v76S,13v77S,14v78S,15#690;00S,16v7:B#7???7?811000v2#800000000000Hv2#10I_v2#10#10Ja_v2#10#10O#10000#136000B#7???7?811000v21#7?????????>?B#4:v22#1????P_v2#10#10v21+v22#1I#138;:8#4I#138;<8#8I#138;=0#8I#138;>0#8I#138<00#8I#138<08#8La#138<00+v2#80La#138<08#50La#690;00v28La+v2#28v28La+v2#68#11>124La+v2#60#138;:8La+v2#58+v22#>La+v2#50#690;00La+v2#48#1La+v2#40#6912=8La+v2#38#La+v2#30v16Ma#138;:8#5La+v2#1:0v28La+v2#1=8#67<>8La+v2#1=0#16222La+v2#1<8#138;:8La+v2#1<0+v2#220La+v2#1;8v13La+v2#1;0v14La+v2#1:8v15La+v2#218#:7630La+v2#210v8La+v2#208v9La+v2#200v12La+v2#298#114?94La+v2#290v29La+v2#288v2:La+v2#280v2;La+v2#278v2<La+v2#270v2=La+v2#268v2>La+v2#260v2?La+v2#258v30,7_v2#10#10#138;:8#4#138;<8#8#138;=0#8#138;>0#8#138<00#8#138<08#8,1,15X#11=148#11575<Y,T,1#114?98T,2+v2#2:0T,8v29T,9v2:T,:v8T,;v28T,<v28T,12v2;T,13v2<T,14v2=T,15v2>T,16v2?T,17v30Mb#138;:8#5Lb#138<08#Lb#138<00#6912=8Lb#138;>0#Lb#138;=0#Lb#138;<8#"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma duGc_conc : ltac:(r1mk L5.defined [KS_duGc] fx R M V duGc_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_duGc] LibSegJb_duGc.regs0 LibSegJb_duGc.kn0 LibSegJb_duGc.BR LibSegJb_duGc.PSS LibSegJb_duGc.NX0 LibSegJb_duGc.F0 1167688 LibSegJb_duGc.seg_sound_ax fx R M V duGc_conc_s. Qed.
End SE.
End AS0DIAGUP.
