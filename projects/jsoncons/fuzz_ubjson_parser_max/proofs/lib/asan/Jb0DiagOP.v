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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_doA LibSegJb_doB LibSegJb_doD LibSegJb_doDl LibSegJb_doDs LibSegJb_doEa LibSegJb_doEb LibSegJb_doEc LibSegJb_doFa LibSegJb_doGa LibSegJb_doGb1 LibSegJb_doGb2 LibSegJb_doGc.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module AS0DIAGOP.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_doA : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_doA.regs0 LibSegJb_doA.regs_out0).
Lemma KS_doA_ok : BG.kept_ok 140 LibSegJb_doA.regs0 LibSegJb_doA.regs_out0 KS_doA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition doA_conc_s := ",14A#v2p#2#40A#v21p#2#40A#v22p#2#40S,1#:76>0S,2v2S,:#138;:8S,;#1?0<0S,<v21B#7???7?811000v2#800000000000Hv2#10I_v2#930#930Ja_v2#930#930O#10000#136000B#7???7?811000v21#7?????????>?B#v22#1????P_v2#930#930v21+v22#1La#7???;>18#Na#13=718#1Na#1<>5;<#1La#13<:38#7???8000,1_v2#930#930,1,47X#62=34#66>28Y,T,1#66=20T,2_v2#930T,8_v2#70T,9^#?#???????????????T,:v21T,;#T,<#73T,=#73T,>#T,12#:T,13#1?0=3T,14#15<6?T,15_v2#28T,16v21T,17#9T,18_v2#8?8T,19^#:#:::::::::::::::T,1:^#?#???????????????T,1;#25Nb_v2#8?4#73Lb_v2#900#1?0=3Nb_v2#8?8#Lb_v2#908#1?0=1Lb_v2#910^#?#???????????????Nb_v2#8?1#Nb_v2#8?2#Nb_v2#8?3#Nb_v2#8?5#Nb_v2#8?6#Nb_v2#8?7#Nb_v2#911#Nb_v2#912#Nb_v2#913#Nb_v2#914#Nb_v2#915#Nb_v2#916#Nb_v2#917#Nb_v2#918#Lb_v2#928_v2#>8Lb_v2#920#207?2Lb_v2#=8r1;Lb_v2#=0r1:Lb_v2#<8r19Lb_v2#<0r18Lb_v2#;8r17Lb_v2#;0r16Lb_v2#:8r15Lb_v2#:0r14Lb_v2#98r13Lb_v2#90_v2#30Lb_v2#88#138;:8Lb_v2#80#1?0<0Lb_v2#78#67<:8Lb_v2#60_v2#30Lb_v2#58_v2#30Lb_v2#68_v2#30Lb_v2#18r?Lb_v2#20r>Lb_v2#28r=Lb_v2#30v21Lb_v2#8r11Lb_v2#10r10Lb_v2#50r12Lb_v2#48r9Lb_v2#40r8Lb_v2#38#:76>0Jb_v2#930#8Jb_v2#8?0#818Jb_v2#70#8"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma doA_conc : ltac:(r1mk L5.defined [KS_doA] fx R M V doA_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_doA] LibSegJb_doA.regs0 LibSegJb_doA.kn0 LibSegJb_doA.BR LibSegJb_doA.PSS LibSegJb_doA.NX0 LibSegJb_doA.F0 404788 LibSegJb_doA.seg_sound_ax fx R M V doA_conc_s. Qed.
End SE.
Definition KS_doB : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_doB.regs0 LibSegJb_doB.regs_out0).
Lemma KS_doB_ok : BG.kept_ok 140 LibSegJb_doB.regs0 LibSegJb_doB.regs_out0 KS_doB = true. Proof. vm_compute. reflexivity. Qed.
Definition doB_conc_s := ",49A#v2p#2#40A#v13p#2#40A#v14p#2#40A#v15p#2#40A#v16p#2#40A#v17p#2#40A#v18p#2#40A#v19p#2#40A#v1:p#2#40A#v1;p#2#40A#v21p#2#40A#v22p#2#40A#v28p#2#40A#v78p#2#40A#v79p#2#40A#v7:p#2#40A#v7;p#2#40S,2v2S,8+v2#8<0S,13#1?0=3S,14v78S,15v79S,16v7:S,17v7;S,18+v2#38S,19^#:#:::::::::::::::S,1:^#?#???????????????S,1;#25B#7???7?811000v2#800000000000Hv2#10I_v2#380#<40Ja_v2#380#<40O#10000#136000B#7???7?811000v21#7?????????>?B#v22#1????P_v2#380#<40v21+v22#1Ka+/v2#8#7???80=>#20La#7???;>18#I#138;:8#4I#138;;0#8I#138;;8#8I#138;<8#8I#138;=0#8I#138;>0#8I#138<00#8I#138<08#8I#138<30#4La+v2#8;8#67<:8La+v2#8;0#1?0<0La+v2#8:8#138;:8La+v2#8:0+v2#900La+v2#898v13La+v2#890v14La+v2#888v15La+v2#880v16La+v2#878v17La+v2#870v18La+v2#868v19La+v2#860v1:La+v2#858v1;La#136230#11=??<La+v2#8=8+v2#900La#690;00v28Ma#138<34#????????Ma#138;:8#5La#138<08#La#138<00#6912=8Ma#138<30#Ma#138<38#????????Na#13=719#1La#13<:38#7???8000La#1363:8#1267>4La+v2#900v21,:_v2#380#<40#138;:8#4#138;;0#8#138;;8#8#138;<8#8#138;=0#8#138;>0#8#138<00#8#138<08#8#138<30#4,1,51X#66=8<#62<>8Y,T,1#11>7<4T,2+v2#530T,5#T,8#25T,9#7???????T,:v21T,;#7???????T,<+v2#750T,=+v2#908T,>#1?T,?^#?#?????????????<6T,10#73T,11#8T,12#7?????>>T,13#11T,14#138;:8T,15#1?0=3T,16#T,17v21T,18#T,19^#?#???????????????T,1:#T,1;#Lb+v2#5:0v21Lb+v2#750+v2#908Lb#138;=0+v2#771Nb+v2#770#20Mb+v2#76<#6>65706?Mb+v2#768#20746?6>Mb+v2#764#6>616320Mb+v2#760#3:696<63Lb+v2#558^#?#???????<<<<<<<=Lb+v2#560^#?#??????????>????Lb+v2#598#<<<<<<<Lb+v2#580#12889Lb+v2#6>0v28Lb+v2#590#690;00Lb+v2#588#Lb+v2#578+v2#750Lb+v2#568+v2#7;0Lb+v2#570+v2#858Lb+v2#6>8v1;Lb+v2#6?0v1:Lb+v2#6?8v19Lb+v2#700v18Lb+v2#708v17Lb+v2#710v16Lb+v2#718#5Lb+v2#720#6912=8Lb+v2#728#1Lb+v2#730#690;00Lb+v2#738#1?0<0Lb+v2#740#138;:8Lb+v2#748#11>104Lb#138;<8+v2#7;0Lb#138;;8#Lb#138;;0#Lb#138;>0+v2#760Mb#138<30^#?#???????????????Lb#138<08#50Lb#138<00+v2#760Mb#138;:8#5Lb+v2#870#Lb+v2#868#Lb+v2#860#Lb+v2#858#Lb+v2#878#Lb+v2#758+v2#900Lb+v2#880v28Lb+v2#888v15Lb+v2#890v14Lb+v2#898v13Lb+v2#8:0+v2#900Lb+v2#8:8#138;:8Lb+v2#8;0#1?0<0Lb+v2#8;8#67<>8Jb+v2#530#28Jb+v2#5:8#138Jb+v2#771#>7"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma doB_conc : ltac:(r1mk L5KA.zeros_at [KS_doB] fx R M V doB_conc_s).
Proof.
r1pf L5KA.zeros_at [KS_doB] LibSegJb_doB.regs0 LibSegJb_doB.kn0 LibSegJb_doB.BR LibSegJb_doB.PSS LibSegJb_doB.NX0 LibSegJb_doB.F0 421260 LibSegJb_doB.seg_sound_ax fx R M V doB_conc_s. Qed.
End SE.
Definition KS_doD : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_doD.regs0 LibSegJb_doD.regs_out0).
Lemma KS_doD_ok : BG.kept_ok 140 LibSegJb_doD.regs0 LibSegJb_doD.regs_out0 KS_doD = true. Proof. vm_compute. reflexivity. Qed.
Definition doD_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2v2S,8#25S,9#7???????S,:v22S,12#7?????>>S,13#11S,14#138;:8S,15#1?0=3S,16#S,17v21S,19^#?#???????????????S,1:#B#7???7?811000v2#800000000000Hv2#10I_v2#8;0#8>0Ja_v2#8;0#8>0O#10000#136000B#7???7?811000v21#7?????????>?B#v22#1????P_v2#8;0#8>0v21+v22#1I#138;=0#8Na#138;:8#5La#138;<8+v2#280La#138;=0+v2#241Ma#138<38#????????Na#13=719#1La#1363:8#1267>4Na+v21v22#,2_v2#8;0#8>0#138;=0#8,1,15X#11>7<4#11>=10Y,T,1#11>;><T,:v21T,;v22T,<#138;:8T,=+v2#241T,>#T,?#1T,12#T,18#T,19v22T,1:v22T,1;v22Lb#138;=0+v2#241Lb+v2#8#Lb+v2#20v22Lb+v2#10v22Lbv2#10=<3Lb+v2#18#Jb+v2#28#8"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma doD_conc : ltac:(r1mk L5.defined [KS_doD] fx R M V doD_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_doD] LibSegJb_doD.regs0 LibSegJb_doD.kn0 LibSegJb_doD.BR LibSegJb_doD.PSS LibSegJb_doD.NX0 LibSegJb_doD.F0 1173444 LibSegJb_doD.seg_sound_ax fx R M V doD_conc_s. Qed.
End SE.
Definition KS_doDl : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_doDl.regs0 LibSegJb_doDl.regs_out0).
Lemma KS_doDl_ok : BG.kept_ok 140 LibSegJb_doDl.regs0 LibSegJb_doDl.regs_out0 KS_doDl = true. Proof. vm_compute. reflexivity. Qed.
Definition doDl_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v28p#2#40S,2v2S,8#25S,9#7???????S,:v21S,;v22S,<#138;:8S,12#S,13#11S,14#138;:8S,15#1?0=3S,16#B#7???7?811000v2#800000000000Hv2#10I_v2#70#70Ja_v2#70#70O#10000#136000B#7???7?811000v21#7?????????>?B#40v22#1????P_v2#70#70v21+v22#1La#138;<8+v2#280La#138;=0+v2#241La#138;?0#11=0;4La#690;00v28,1_v2#70#70,1,15X#11>=10#11=0?0Y,T,1#11>=14T,2_v2#70T,6#11=0;4T,8v22T,9#138;:8T,:v28T,;v21T,<v22T,15#690;00Lb_v2#48v28Lb_v2#40#Lb_v2#38#1?0=3Lb_v2#30#138;:8Lb_v2#28#11Lb_v2#20#Lb_v2#18#7???????Lb_v2#10#25Lb_v2#8#11>=14Jb_v2#70#28"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma doDl_conc : ltac:(r1mk L5.defined [KS_doDl] fx R M V doDl_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_doDl] LibSegJb_doDl.regs0 LibSegJb_doDl.kn0 LibSegJb_doDl.BR LibSegJb_doDl.PSS LibSegJb_doDl.NX0 LibSegJb_doDl.F0 1174800 LibSegJb_doDl.seg_sound_ax fx R M V doDl_conc_s. Qed.
End SE.
Definition KS_doDs : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_doDs.regs0 LibSegJb_doDs.regs_out0).
Lemma KS_doDs_ok : BG.kept_ok 140 LibSegJb_doDs.regs0 LibSegJb_doDs.regs_out0 KS_doDs = true. Proof. vm_compute. reflexivity. Qed.
Definition doDs_conc_s := ",18A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2v2S,8#25S,9#7???????S,:v21S,;v22S,<#138;:8S,12#S,13#11S,14#138;:8S,15#1?0=3B#7???7?811000v2#800000000000Hv2#10I_v2#40#40Ja_v2#40#40O#10000#136000B#7???7?811000v21#7?????????>?B#v22#3?P_v2#40#40v21+v22#1La#138;<8+v2#280La#138;=0+v2#241Ma#138<38#????????,1_v2#40#40,1,13X#11>=10#77608Y,T,1#11=;;0T,2_v2#40T,8#138;:8T,9v22T,:+v2#241T,;v21T,<v22T,12v21T,13#Lb_v2#38#1?0=3Lb_v2#30#138;:8Lb_v2#28#11Lb_v2#20#Lb_v2#18#7???????Lb_v2#10#25Lb_v2#8#11>=14Jb_v2#40#8"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma doDs_conc : ltac:(r1mk L5.defined [KS_doDs] fx R M V doDs_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_doDs] LibSegJb_doDs.regs0 LibSegJb_doDs.kn0 LibSegJb_doDs.BR LibSegJb_doDs.PSS LibSegJb_doDs.NX0 LibSegJb_doDs.F0 1174800 LibSegJb_doDs.seg_sound_ax fx R M V doDs_conc_s. Qed.
End SE.
Definition KS_doEa : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_doEa.regs0 LibSegJb_doEa.regs_out0).
Lemma KS_doEa_ok : BG.kept_ok 140 LibSegJb_doEa.regs0 LibSegJb_doEa.regs_out0 KS_doEa = true. Proof. vm_compute. reflexivity. Qed.
Definition doEa_conc_s := ",1<A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2v2S,8#138;:8S,9v22S,13#S,1:v22B#7???7?811000v2#800000000000Hv2#10I_v2#10#50Ja_v2#10#50O#10000#136000B#7???7?811000v21#7?????????>?B#v22#3>P_v2#10#50v21+v22#1I#138;=0#8La#138;=0+v2#281La+v2#38#11>=14La+v2#30#25La+v2#28#7???????La+v2#20#La+v2#18#11La+v2#10#138;:8La+v2#8#1?0=3Na#138;:8#5La#138;<8+v2#2<0Ma#138<38#????????,2_v2#10#50#138;=0#8,1,15X#11=;;0#77608Y,T,1#11=;;0T,9#1T,:++v2v22#281T,;#1?0=3T,<#1T,12#1?0=3T,14#138;:8T,15#1?0=4T,16#1T,17#1?0=3T,1:#1Lb+v2#8#1?0=4Lb+v2#10#138;:8Lb+v2#18+v22#11Lb+v2#20+*-1v22#7?????>>Lb+v2#28#7???????Lb+v2#30#25Lb+v2#38#11>2?4Lb#138;=0++v2v22#281"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma doEa_conc : ltac:(r1mk L5.defined [KS_doEa] fx R M V doEa_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_doEa] LibSegJb_doEa.regs0 LibSegJb_doEa.kn0 LibSegJb_doEa.BR LibSegJb_doEa.PSS LibSegJb_doEa.NX0 LibSegJb_doEa.F0 1170352 LibSegJb_doEa.seg_sound_ax fx R M V doEa_conc_s. Qed.
End SE.
Definition KS_doEb : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_doEb.regs0 LibSegJb_doEb.regs_out0).
Lemma KS_doEb_ok : BG.kept_ok 140 LibSegJb_doEb.regs0 LibSegJb_doEb.regs_out0 KS_doEb = true. Proof. vm_compute. reflexivity. Qed.
Definition doEb_conc_s := ",1>A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v28p#2#40S,2v2S,8#138;:8S,9#3?S,13#S,1:#3?B#7???7?811000v2#800000000000Hv2#10I_v2#30#70Ja_v2#30#70O#10000#136000B#7???7?811000v21#7?????????>?B#3?v22#3?P_v2#30#70v21+v22#1I#138;=0#8La#138;=0+v2#281La+v2#38#11>=14La+v2#30#25La+v2#28#7???????La+v2#20#La+v2#18#11La+v2#10#138;:8La+v2#8#1?0=3Na#138;:8#5La#138;<8+v2#2<0La#138;?0#11=0;4La#690;00v28,2_v2#30#70#138;=0#8,1,1<X#11=;;0#11=0?0Y,T,1#11>2?4T,2_v2#30T,6#11=0;4T,8#1T,9#138;:8T,:v28T,;#1?0=3T,<#1T,12#7?????:?T,13#50T,14#138;:8T,15#690;00T,16#1T,17#1?0=3T,1:#1Lb_v2#8v28Lbv2#1Lb+v2#8#1?0=4Lb+v2#10#138;:8Lb+v2#18#50Lb+v2#20#7?????:?Lb+v2#28#7???????Lb+v2#30#25Lb+v2#38#11>2?4Lb#138;=0+v2#2<0Jb_v2#30#28"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma doEb_conc : ltac:(r1mk L5.defined [KS_doEb] fx R M V doEb_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_doEb] LibSegJb_doEb.regs0 LibSegJb_doEb.kn0 LibSegJb_doEb.BR LibSegJb_doEb.PSS LibSegJb_doEb.NX0 LibSegJb_doEb.F0 1170352 LibSegJb_doEb.seg_sound_ax fx R M V doEb_conc_s. Qed.
End SE.
Definition KS_doEc : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_doEc.regs0 LibSegJb_doEc.regs_out0).
Lemma KS_doEc_ok : BG.kept_ok 140 LibSegJb_doEc.regs0 LibSegJb_doEc.regs_out0 KS_doEc = true. Proof. vm_compute. reflexivity. Qed.
Definition doEc_conc_s := ",46A#v2p#2#40A#v16p#2#40A#v17p#2#40A#v18p#2#40A#v19p#2#40A#v1:p#2#40A#v1;p#2#40A#v21p#2#40A#v22p#2#40A#v28p#2#40A#v7:p#2#40A#v7;p#2#40A#v7=p#2#40A#v7?p#2#40S,2v2S,8v22S,9#138;:8S,15#690;00S,16v7:S,17v7;S,18#S,19v7=S,1:v22S,1;v7?B#7???7?811000v2#800000000000Hv2#10I_v2#840#:?0Ja_v2#840#:?0O#10000#136000B#7???7?811000v21#7?????????>?B#40v22#1????P_v2#840#:?0v21+v22#1Ka+/v2#8#7???8046#18La#7???;>18#I#138;<8#8I#138;=0#8I#138;>0#8La#138<00+v2#2:0La#138<08#50La#690;00v28La+v2#28v28La+v2#68#11>=14La+v2#60#25La+v2#58#7???????La+v2#50#La+v2#48#11La+v2#40#138;:8La+v2#38#1?0=3La+v2#30#Na#138;:8#5Ma#138<38#????????Na#13=719#1La#13<:38#7???8000La#1363:8#1267>4La+v2#=0#690;00La+v2#220v28La+v2#288#11>104La+v2#280#138;:8La+v2#278#1?0<0La+v2#270#690;00La+v2#268#1La+v2#260#6912=8La+v2#258#5La+v2#250v16La+v2#248v17La+v2#240v18La+v2#238v19La+v2#230v1:La+v2#228v1;La#138;?0#11=0;4,4_v2#840#:?0#138;<8#8#138;=0#8#138;>0#8,1,2;X#11=148#11=0?0Y,T,1#11>124T,2+v2#220T,5#T,8#T,:v28T,;#T,<#T,=#11=0;4T,>#T,?#1T,10#1T,11#:T,12#690;00T,13#1T,14#6912=8T,16v16T,17v17T,18v18T,19v19T,1:v1:T,1;v1;Lb+v2#248v28Lb+v2#250v16Lb+v2#258#Lb+v2#260#6912=8Lb+v2#268#1Lb+v2#270#690;00Lb+v2#278+v22#12Lb+v2#280#138;:8Lb+v2#288#11>124Lb#138;=0+v2#2:1Nb+v2#2:0#:Lb#138;>0+v2#2:0Lb#138;<8+v2#2?0Jb+v2#290#10Jb+v2#2:1#?Lb+v2#220v28Lb+v2#240v18Lb+v2#238v19Lb+v2#230v1:Lb+v2#228v1;"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma doEc_conc : ltac:(r1mk L5KA.zeros_at [KS_doEc] fx R M V doEc_conc_s).
Proof.
r1pf L5KA.zeros_at [KS_doEc] LibSegJb_doEc.regs0 LibSegJb_doEc.kn0 LibSegJb_doEc.BR LibSegJb_doEc.PSS LibSegJb_doEc.NX0 LibSegJb_doEc.F0 1167688 LibSegJb_doEc.seg_sound_ax fx R M V doEc_conc_s. Qed.
End SE.
Definition KS_doFa : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_doFa.regs0 LibSegJb_doFa.regs_out0).
Lemma KS_doFa_ok : BG.kept_ok 140 LibSegJb_doFa.regs0 LibSegJb_doFa.regs_out0 KS_doFa = true. Proof. vm_compute. reflexivity. Qed.
Definition doFa_conc_s := ",3:A#v2p#2#40A#v16p#2#40A#v17p#2#40A#v18p#2#40A#v19p#2#40A#v1:p#2#40A#v1;p#2#40A#v21p#2#40A#v22p#2#40A#v28p#2#40A#v7;p#2#40A#v7<p#2#40A#v7=p#2#40A#v7?p#2#40S,2v2S,8#138;:8S,9#1S,13#S,16#1S,17v7;S,18v7<S,19v7=S,1:#1S,1;v7?B#7???7?811000v2#800000000000Hv2#10I_v2#10#270Ja_v2#10#270O#10000#136000B#7???7?811000v21#7?????????>?B#v22#3>P_v2#10#270v21+v22#1I#138;=0#8La#138;=0++v2v22#281La+v2#38#11>2?4La+v2#30#25La+v2#28#7???????La+v2#20_#7?????>>v22La+v2#18+v22#11La+v2#10#138;:8La+v2#8#1?0=4La+v2#:0#690;00La#690;00v28La+v2#1?0v28La+v2#258#11>104La+v2#250#138;:8La+v2#248#1?0<0La+v2#240#690;00La+v2#238#1La+v2#230#6912=8La+v2#228#5La+v2#220v16La+v2#218v17La+v2#210v18La+v2#208v19La+v2#200v1:La+v2#1?8v1;La#138;?0#11=0;4,2_v2#10#270#138;=0#8,1,23X#11=;;0#11=0?0Y,T,1#11>124T,2+v2#1?0T,8#T,9#138;:8T,:v28T,;#T,<#T,=#11=0;4T,12#690;00T,13#1T,14#6912=8T,15#690;00T,16v16T,17v17T,18v18T,19v19T,1:v1:T,1;v1;Lb+v2#218v28Lb+v2#220v16Lb+v2#228#Lb+v2#230#6912=8Lb+v2#238#1Lb+v2#240#690;00Lb+v2#248+v22#12Lb+v2#250#138;:8Lb+v2#258#11>124Lb#138;=0++v2v22#282Lb+v2#1?0v28Lb+v2#210v18Lb+v2#208v19Lb+v2#200v1:Lb+v2#1?8v1;"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma doFa_conc : ltac:(r1mk L5.defined [KS_doFa] fx R M V doFa_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_doFa] LibSegJb_doFa.regs0 LibSegJb_doFa.kn0 LibSegJb_doFa.BR LibSegJb_doFa.PSS LibSegJb_doFa.NX0 LibSegJb_doFa.F0 1170352 LibSegJb_doFa.seg_sound_ax fx R M V doFa_conc_s. Qed.
End SE.
Definition KS_doGa : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_doGa.regs0 LibSegJb_doGa.regs_out0).
Lemma KS_doGa_ok : BG.kept_ok 140 LibSegJb_doGa.regs0 LibSegJb_doGa.regs_out0 KS_doGa = true. Proof. vm_compute. reflexivity. Qed.
Definition doGa_conc_s := ",3>A#v2p#2#40A#v8p#2#40A#v9p#2#40A#v12p#2#40A#v13p#2#40A#v14p#2#40A#v15p#2#40A#v16p#2#40A#v21p#2#40A#v22p#2#40A#v28p#2#40A#v76p#2#40A#v77p#2#40A#v78p#2#40A#v7:p#2#40S,2v2S,8#S,9#138;:8S,12v76S,13v77S,14v78S,15#690;00S,16v7:B#7???7?811000v2#800000000000Hv2#10I_v2#10#10Ja_v2#10#10O#10000#136000B#7???7?811000v21#7?????????>?B#v22#3>P_v2#10#10v21+v22#1I#138;:8#4I#138;<8#8I#138;=0#8I#138;>0#8I#138<00#8I#138<08#8La#138<00+v2#80La#138<08#50La#690;00v28La+v2#28v28La+v2#68#11>124La+v2#60#138;:8La+v2#58+v22#12La+v2#50#690;00La+v2#48#1La+v2#40#6912=8La+v2#38#La+v2#30v16Ma#138;:8#5La+v2#1:0v28La+v2#1=8#67<>8La+v2#1=0#1?0<0La+v2#1<8#138;:8La+v2#1<0+v2#220La+v2#1;8v13La+v2#1;0v14La+v2#1:8v15La+v2#218#:76>0La+v2#210v8La+v2#208v9La+v2#200v12,7_v2#10#10#138;:8#4#138;<8#8#138;=0#8#138;>0#8#138<00#8#138<08#8,1,14X#11=148#11575<Y,T,1#:770<T,2+v2#250T,8v8T,9v9T,:#2T,;v28T,<v28T,12v12T,13v13T,14v14T,15v15T,16v16Mb#138;:8#5Lb#138<08#Lb#138<00#6912=8Lb#138;>0#Lb#138;=0#Lb#138;<8#"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma doGa_conc : ltac:(r1mk L5.defined [KS_doGa] fx R M V doGa_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_doGa] LibSegJb_doGa.regs0 LibSegJb_doGa.kn0 LibSegJb_doGa.BR LibSegJb_doGa.PSS LibSegJb_doGa.NX0 LibSegJb_doGa.F0 1167688 LibSegJb_doGa.seg_sound_ax fx R M V doGa_conc_s. Qed.
End SE.
Definition KS_doGb1 : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_doGb1.regs0 LibSegJb_doGb1.regs_out0).
Lemma KS_doGb1_ok : BG.kept_ok 140 LibSegJb_doGb1.regs0 LibSegJb_doGb1.regs_out0 KS_doGb1 = true. Proof. vm_compute. reflexivity. Qed.
Definition doGb1_conc_s := ",40A#v2p#2#40A#v16p#2#40A#v17p#2#40A#v18p#2#40A#v19p#2#40A#v1:p#2#40A#v1;p#2#40A#v21p#2#40A#v22p#2#40A#v28p#2#40A#v7:p#2#40A#v7;p#2#40A#v7<p#2#40A#v7=p#2#40A#v7?p#2#40S,2v2S,8#1S,9#138;:8S,15#690;00S,16v7:S,17v7;S,18v7<S,19v7=S,1:#1S,1;v7?B#7???7?811000v2#800000000000Hv2#10I_v2#10#2:0Ja_v2#10#2:0O#10000#136000B#7???7?811000v21#7?????????>?B#3?v22#3?P_v2#10#2:0v21+v22#1I#138;<8#8I#138;=0#8I#138;>0#8La#138<00+v2#2:0La#138<08#50La#690;00v28La+v2#28v28La+v2#68#11>2?4La+v2#60#25La+v2#58#7???????La+v2#50#7?????:?La+v2#48#50La+v2#40#138;:8La+v2#38#1?0=4La+v2#30#1La+v2#=0#690;00La+v2#220v28La+v2#288#11>104La+v2#280#138;:8La+v2#278#1?0<0La+v2#270#690;00La+v2#268#1La+v2#260#6912=8La+v2#258#5La+v2#250v16La+v2#248v17La+v2#240v18La+v2#238v19La+v2#230v1:La+v2#228v1;La#138;?0#11=0;4,4_v2#10#2:0#138;<8#8#138;=0#8#138;>0#8,1,23X#11=148#11=0?0Y,T,1#11>124T,2+v2#220T,8#T,:v28T,;#T,<#T,=#11=0;4T,12#690;00T,13#1T,14#6912=8T,16v16T,17v17T,18v18T,19v19T,1:v1:T,1;v1;Lb+v2#248v28Lb+v2#250v16Lb+v2#258#Lb+v2#260#6912=8Lb+v2#268#1Lb+v2#270#690;00Lb+v2#278#51Lb+v2#280#138;:8Lb+v2#288#11>124Lb#138;>0+v2#2:0Lb#138;=0+v2#2:0Lb#138;<8+v2#2?0Lb+v2#220v28Lb+v2#240v18Lb+v2#238v19Lb+v2#230v1:Lb+v2#228v1;"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma doGb1_conc : ltac:(r1mk L5.defined [KS_doGb1] fx R M V doGb1_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_doGb1] LibSegJb_doGb1.regs0 LibSegJb_doGb1.kn0 LibSegJb_doGb1.BR LibSegJb_doGb1.PSS LibSegJb_doGb1.NX0 LibSegJb_doGb1.F0 1167688 LibSegJb_doGb1.seg_sound_ax fx R M V doGb1_conc_s. Qed.
End SE.
Definition KS_doGb2 : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_doGb2.regs0 LibSegJb_doGb2.regs_out0).
Lemma KS_doGb2_ok : BG.kept_ok 140 LibSegJb_doGb2.regs0 LibSegJb_doGb2.regs_out0 KS_doGb2 = true. Proof. vm_compute. reflexivity. Qed.
Definition doGb2_conc_s := ",3>A#v2p#2#40A#v8p#2#40A#v9p#2#40A#v12p#2#40A#v13p#2#40A#v14p#2#40A#v15p#2#40A#v16p#2#40A#v21p#2#40A#v22p#2#40A#v28p#2#40A#v76p#2#40A#v77p#2#40A#v78p#2#40A#v7:p#2#40S,2v2S,8#S,9#138;:8S,12v76S,13v77S,14v78S,15#690;00S,16v7:B#7???7?811000v2#800000000000Hv2#10I_v2#10#10Ja_v2#10#10O#10000#136000B#7???7?811000v21#7?????????>?B#3?v22#3?P_v2#10#10v21+v22#1I#138;:8#4I#138;<8#8I#138;=0#8I#138;>0#8I#138<00#8I#138<08#8La#138<00+v2#80La#138<08#50La#690;00v28La+v2#28v28La+v2#68#11>124La+v2#60#138;:8La+v2#58#51La+v2#50#690;00La+v2#48#1La+v2#40#6912=8La+v2#38#La+v2#30v16Ma#138;:8#5La+v2#1:0v28La+v2#1=8#67<>8La+v2#1=0#1?0<0La+v2#1<8#138;:8La+v2#1<0+v2#220La+v2#1;8v13La+v2#1;0v14La+v2#1:8v15La+v2#218#:76>0La+v2#210v8La+v2#208v9La+v2#200v12,7_v2#10#10#138;:8#4#138;<8#8#138;=0#8#138;>0#8#138<00#8#138<08#8,1,14X#11=148#11575<Y,T,1#:770<T,2+v2#250T,8v8T,9v9T,:#2T,;v28T,<v28T,12v12T,13v13T,14v14T,15v15T,16v16Mb#138;:8#5Lb#138<08#Lb#138<00#6912=8Lb#138;>0#Lb#138;=0#Lb#138;<8#"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma doGb2_conc : ltac:(r1mk L5.defined [KS_doGb2] fx R M V doGb2_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_doGb2] LibSegJb_doGb2.regs0 LibSegJb_doGb2.kn0 LibSegJb_doGb2.BR LibSegJb_doGb2.PSS LibSegJb_doGb2.NX0 LibSegJb_doGb2.F0 1167688 LibSegJb_doGb2.seg_sound_ax fx R M V doGb2_conc_s. Qed.
End SE.
Definition KS_doGc : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_doGc.regs0 LibSegJb_doGc.regs_out0).
Lemma KS_doGc_ok : BG.kept_ok 140 LibSegJb_doGc.regs0 LibSegJb_doGc.regs_out0 KS_doGc = true. Proof. vm_compute. reflexivity. Qed.
Definition doGc_conc_s := ",3>A#v2p#2#40A#v8p#2#40A#v9p#2#40A#v12p#2#40A#v13p#2#40A#v14p#2#40A#v15p#2#40A#v16p#2#40A#v21p#2#40A#v22p#2#40A#v28p#2#40A#v76p#2#40A#v77p#2#40A#v78p#2#40A#v7:p#2#40S,2v2S,8#S,9#138;:8S,12v76S,13v77S,14v78S,15#690;00S,16v7:B#7???7?811000v2#800000000000Hv2#10I_v2#10#10Ja_v2#10#10O#10000#136000B#7???7?811000v21#7?????????>?B#40v22#1????P_v2#10#10v21+v22#1I#138;:8#4I#138;<8#8I#138;=0#8I#138;>0#8I#138<00#8I#138<08#8La#138<00+v2#80La#138<08#50La#690;00v28La+v2#28v28La+v2#68#11>124La+v2#60#138;:8La+v2#58+v22#12La+v2#50#690;00La+v2#48#1La+v2#40#6912=8La+v2#38#La+v2#30v16Ma#138;:8#5La+v2#1:0v28La+v2#1=8#67<>8La+v2#1=0#1?0<0La+v2#1<8#138;:8La+v2#1<0+v2#220La+v2#1;8v13La+v2#1;0v14La+v2#1:8v15La+v2#218#:76>0La+v2#210v8La+v2#208v9La+v2#200v12,7_v2#10#10#138;:8#4#138;<8#8#138;=0#8#138;>0#8#138<00#8#138<08#8,1,14X#11=148#11575<Y,T,1#:770<T,2+v2#250T,8v8T,9v9T,:#2T,;v28T,<v28T,12v12T,13v13T,14v14T,15v15T,16v16Mb#138;:8#5Lb#138<08#Lb#138<00#6912=8Lb#138;>0#Lb#138;=0#Lb#138;<8#"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma doGc_conc : ltac:(r1mk L5.defined [KS_doGc] fx R M V doGc_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_doGc] LibSegJb_doGc.regs0 LibSegJb_doGc.kn0 LibSegJb_doGc.BR LibSegJb_doGc.PSS LibSegJb_doGc.NX0 LibSegJb_doGc.F0 1167688 LibSegJb_doGc.seg_sound_ax fx R M V doGc_conc_s. Qed.
End SE.
End AS0DIAGOP.
