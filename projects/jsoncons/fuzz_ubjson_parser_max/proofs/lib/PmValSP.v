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
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Js0PlanKit AsanPlanCore
BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_vaE LibSegJs_vaF8 LibSegJs_vaF1 LibSegJs_vaS1 LibSegJs_vaS2_0 LibSegJs_vaS2_1a LibSegJs_vaS2_1b LibSegJs_vaS2_2a LibSegJs_vaS2_2b LibSegJs_vaS2_3a LibSegJs_vaS2_3b LibSegJs_vaS2_big LibSegJs_vaB LibSegJs_vaX.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMVAP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_vaE_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaE.regs0 LibSegJs_vaE.regs_out0).
Lemma KS_vaE_0_ok : BG.kept_ok 60 LibSegJs_vaE.regs0 LibSegJs_vaE.regs_out0 KS_vaE_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaE_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaE.regs0 LibSegJs_vaE.regs_out1).
Lemma KS_vaE_1_ok : BG.kept_ok 60 LibSegJs_vaE.regs0 LibSegJs_vaE.regs_out1 KS_vaE_1 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition vaE_conc_s := ",;A#v2p#2#40A#v21p#2#40A#v23p#2#40S,2v2S,:v21S,;v23B#7???7?800060v2#800000000000Hv2#10I_v2#60#60B#v21#800000000000B#v23#3??????,1_v2#58#58,2,3X#36:><#36<?4Y,C%_v23#p#2#40#1,22X#36:><#36;6<Y,1T,2_v2#60T,5#>?T,6#>0T,7#:0T,8#?4T,9#8?T,;#13;28T,<+v21v23T,=#8T,>#1T,?^#?#?????????????<2T,10#?5T,11^#?#?????????????;?T,12#2T,13#1388=T,14#3T,1<#>=T,1=#9?T,1>#?0T,1?#90Lb_v2#58r1:Lb_v2#50r19Lb_v2#48r18Lb_v2#40r17Lb_v2#38r16Lb_v2#30r15Lb_v2#28r14Lb_v2#20r13Lb_v2#18r12Lb_v2#10r9Lb_v2#8r8D#1%_v23#p#2#40"%pstring.
Lemma vaE_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_vaE_0; KS_vaE_1] fx R M V vaE_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_vaE_0; KS_vaE_1] LibSegJs_vaE.regs0 LibSegJs_vaE.kn0 LibSegJs_vaE.BR LibSegJs_vaE.PSS LibSegJs_vaE.NX0 LibSegJs_vaE.F0 223980 LibSegJs_vaE.seg_sound_ax fx R M V vaE_conc_s. Qed.
Definition KS_vaF8_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaF8.regs0 LibSegJs_vaF8.regs_out0).
Lemma KS_vaF8_0_ok : BG.kept_ok 60 LibSegJs_vaF8.regs0 LibSegJs_vaF8.regs_out0 KS_vaF8_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaF8_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaF8.regs0 LibSegJs_vaF8.regs_out1).
Lemma KS_vaF8_1_ok : BG.kept_ok 60 LibSegJs_vaF8.regs0 LibSegJs_vaF8.regs_out1 KS_vaF8_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaF8_2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaF8.regs0 LibSegJs_vaF8.regs_out2).
Lemma KS_vaF8_2_ok : BG.kept_ok 60 LibSegJs_vaF8.regs0 LibSegJs_vaF8.regs_out2 KS_vaF8_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaF8_3 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaF8.regs0 LibSegJs_vaF8.regs_out3).
Lemma KS_vaF8_3_ok : BG.kept_ok 60 LibSegJs_vaF8.regs0 LibSegJs_vaF8.regs_out3 KS_vaF8_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaF8_4 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaF8.regs0 LibSegJs_vaF8.regs_out4).
Lemma KS_vaF8_4_ok : BG.kept_ok 60 LibSegJs_vaF8.regs0 LibSegJs_vaF8.regs_out4 KS_vaF8_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaF8_5 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaF8.regs0 LibSegJs_vaF8.regs_out5).
Lemma KS_vaF8_5_ok : BG.kept_ok 60 LibSegJs_vaF8.regs0 LibSegJs_vaF8.regs_out5 KS_vaF8_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaF8_6 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaF8.regs0 LibSegJs_vaF8.regs_out6).
Lemma KS_vaF8_6_ok : BG.kept_ok 60 LibSegJs_vaF8.regs0 LibSegJs_vaF8.regs_out6 KS_vaF8_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaF8_7 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaF8.regs0 LibSegJs_vaF8.regs_out7).
Lemma KS_vaF8_7_ok : BG.kept_ok 60 LibSegJs_vaF8.regs0 LibSegJs_vaF8.regs_out7 KS_vaF8_7 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaF8_8 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaF8.regs0 LibSegJs_vaF8.regs_out8).
Lemma KS_vaF8_8_ok : BG.kept_ok 60 LibSegJs_vaF8.regs0 LibSegJs_vaF8.regs_out8 KS_vaF8_8 = true. Proof. vm_compute. reflexivity. Qed.
Definition vaF8_conc_s := ",32A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40S,2_v2#60S,5#>?S,6#>0S,7#:0S,8#?4S,9#8?S,:v21S,<+v21v23S,=#8S,>#1S,?-3>S,10#?5S,11-41S,12#2S,13#1388=S,14#3S,1<#>=S,1=#9?S,1>#?0S,1?#90B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Nav21v24B#v24#??Na+v21#1v25B#v25#??Na+v21#2v26B#v26#??Na+v21#3v27B#v27#??Na+v21#4v28B#v28#??Na+v21#5v29B#v29#??Na+v21#6v2:B#v2:#??Na+v21#7v2;B#v2;#??,,9,3X#36;6<#36;?0Y,T,;v23,4X#36;6<#36;?0Y,1T,:+v21#1T,;v23,4X#36;6<#36;?0Y,2T,:+v21#2T,;v23,4X#36;6<#36;?0Y,3T,:+v21#3T,;v23,4X#36;6<#36;?0Y,4T,:+v21#4T,;v23,4X#36;6<#36;?0Y,5T,:+v21#5T,;v23,4X#36;6<#36;?0Y,6T,:+v21#6T,;v23,4X#36;6<#36;?0Y,7T,:+v21#7T,;v23,4X#36;6<#36<9<Y,8T,;v23T,16+v21#8"%pstring.
Lemma vaF8_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_vaF8_0; KS_vaF8_1; KS_vaF8_2; KS_vaF8_3; KS_vaF8_4; KS_vaF8_5; KS_vaF8_6; KS_vaF8_7; KS_vaF8_8] fx R M V vaF8_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_vaF8_0; KS_vaF8_1; KS_vaF8_2; KS_vaF8_3; KS_vaF8_4; KS_vaF8_5; KS_vaF8_6; KS_vaF8_7; KS_vaF8_8] LibSegJs_vaF8.regs0 LibSegJs_vaF8.kn0 LibSegJs_vaF8.BR LibSegJs_vaF8.PSS LibSegJs_vaF8.NX0 LibSegJs_vaF8.F0 224108 LibSegJs_vaF8.seg_sound_ax fx R M V vaF8_conc_s. Qed.
Definition KS_vaF1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaF1.regs0 LibSegJs_vaF1.regs_out0).
Lemma KS_vaF1_ok : BG.kept_ok 60 LibSegJs_vaF1.regs0 LibSegJs_vaF1.regs_out0 KS_vaF1 = true. Proof. vm_compute. reflexivity. Qed.
Definition vaF1_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#>?S,6#>0S,7#:0S,8#?4S,9#8?S,:v21S,<+v21v23S,=#8S,>#1S,?-3>S,10#?5S,11-41S,12#2S,13#1388=S,14#3S,1<#>=S,1=#9?S,1>#?0S,1?#90B#v21#800000000000B#1v23#7B#1+v21v23#800000000000Nav21v24B#v24#??,,1,3X#36;6<#36;?0Y,T,;v23"%pstring.
Lemma vaF1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_vaF1] fx R M V vaF1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_vaF1] LibSegJs_vaF1.regs0 LibSegJs_vaF1.kn0 LibSegJs_vaF1.BR LibSegJs_vaF1.PSS LibSegJs_vaF1.NX0 LibSegJs_vaF1.F0 224108 LibSegJs_vaF1.seg_sound_ax fx R M V vaF1_conc_s. Qed.
Definition KS_vaS1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS1.regs0 LibSegJs_vaS1.regs_out0).
Lemma KS_vaS1_ok : BG.kept_ok 60 LibSegJs_vaS1.regs0 LibSegJs_vaS1.regs_out0 KS_vaS1 = true. Proof. vm_compute. reflexivity. Qed.
Definition vaS1_conc_s := ",1<A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#>?S,6#>0S,7#:0S,8#?4S,9#8?S,:v21S,<+v21v23S,=#8S,>#1S,?-3>S,10#?5S,11-41S,12#2S,13#1388=S,14#3S,15v24S,1<#>=S,1=#9?S,1>#?0S,1?#90B#v21#800000000000B#1v23#4000000B#1+v21v23#800000000000,,1,4X#36;?0#36;?8Y,W,;%+&v24#??#1388=p#2#40W,17&v24#??"%pstring.
Lemma vaS1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_vaS1] fx R M V vaS1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_vaS1] LibSegJs_vaS1.regs0 LibSegJs_vaS1.kn0 LibSegJs_vaS1.BR LibSegJs_vaS1.PSS LibSegJs_vaS1.NX0 LibSegJs_vaS1.F0 224240 LibSegJs_vaS1.seg_sound_ax fx R M V vaS1_conc_s. Qed.
Definition KS_vaS2_0_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_0.regs0 LibSegJs_vaS2_0.regs_out0).
Lemma KS_vaS2_0_0_ok : BG.kept_ok 60 LibSegJs_vaS2_0.regs0 LibSegJs_vaS2_0.regs_out0 KS_vaS2_0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_0_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_0.regs0 LibSegJs_vaS2_0.regs_out1).
Lemma KS_vaS2_0_1_ok : BG.kept_ok 60 LibSegJs_vaS2_0.regs0 LibSegJs_vaS2_0.regs_out1 KS_vaS2_0_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_0_2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_0.regs0 LibSegJs_vaS2_0.regs_out2).
Lemma KS_vaS2_0_2_ok : BG.kept_ok 60 LibSegJs_vaS2_0.regs0 LibSegJs_vaS2_0.regs_out2 KS_vaS2_0_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition vaS2_0_conc_s := ",20A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#60S,5#>?S,6#>0S,7#:0S,8#?4S,9#8?S,:v21S,<+v21v23S,=#8S,>#1S,?-3>S,10#?5S,11-41S,12#2S,13#1388=S,14#3S,15v24S,17v25S,18#S,1<#>=S,1=#9?S,1>#?0S,1?#90B#v21#800000000000B#1v23#4000000B#1+v21v23#800000000000B#v25#??,,3,5X#36;?<#36<<4Y,T,;#6T,16+v21#1T,19v21,6X#36;?<#36<9<Y,1T,;#6T,16+v21#1T,19v21Cv25#?5,6X#36;?<#36<<4Y,2T,;#6T,16+v21#1T,19v21D#?5v25"%pstring.
Lemma vaS2_0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_vaS2_0_0; KS_vaS2_0_1; KS_vaS2_0_2] fx R M V vaS2_0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_vaS2_0_0; KS_vaS2_0_1; KS_vaS2_0_2] LibSegJs_vaS2_0.regs0 LibSegJs_vaS2_0.kn0 LibSegJs_vaS2_0.BR LibSegJs_vaS2_0.PSS LibSegJs_vaS2_0.NX0 LibSegJs_vaS2_0.F0 224252 LibSegJs_vaS2_0.seg_sound_ax fx R M V vaS2_0_conc_s. Qed.
Definition KS_vaS2_1a : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_1a.regs0 LibSegJs_vaS2_1a.regs_out0).
Lemma KS_vaS2_1a_ok : BG.kept_ok 60 LibSegJs_vaS2_1a.regs0 LibSegJs_vaS2_1a.regs_out0 KS_vaS2_1a = true. Proof. vm_compute. reflexivity. Qed.
Definition vaS2_1a_conc_s := ",20A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#60S,5#>?S,6#>0S,7#:0S,8#?4S,9#8?S,:v21S,<+v21v23S,=#8S,>#1S,?-3>S,10#?5S,11-41S,12#2S,13#1388=S,14#3S,15v24S,17v25S,18#1S,1<#>=S,1=#9?S,1>#?0S,1?#90B#v21#800000000000B#1v23#1B#1+v21v23#800000000000B#v25#??,,1,3X#36;?<#36<<4Y,T,;#5"%pstring.
Lemma vaS2_1a_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_vaS2_1a] fx R M V vaS2_1a_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_vaS2_1a] LibSegJs_vaS2_1a.regs0 LibSegJs_vaS2_1a.kn0 LibSegJs_vaS2_1a.BR LibSegJs_vaS2_1a.PSS LibSegJs_vaS2_1a.NX0 LibSegJs_vaS2_1a.F0 224252 LibSegJs_vaS2_1a.seg_sound_ax fx R M V vaS2_1a_conc_s. Qed.
Definition KS_vaS2_1b_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_1b.regs0 LibSegJs_vaS2_1b.regs_out0).
Lemma KS_vaS2_1b_0_ok : BG.kept_ok 60 LibSegJs_vaS2_1b.regs0 LibSegJs_vaS2_1b.regs_out0 KS_vaS2_1b_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_1b_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_1b.regs0 LibSegJs_vaS2_1b.regs_out1).
Lemma KS_vaS2_1b_1_ok : BG.kept_ok 60 LibSegJs_vaS2_1b.regs0 LibSegJs_vaS2_1b.regs_out1 KS_vaS2_1b_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_1b_2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_1b.regs0 LibSegJs_vaS2_1b.regs_out2).
Lemma KS_vaS2_1b_2_ok : BG.kept_ok 60 LibSegJs_vaS2_1b.regs0 LibSegJs_vaS2_1b.regs_out2 KS_vaS2_1b_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_1b_3 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_1b.regs0 LibSegJs_vaS2_1b.regs_out3).
Lemma KS_vaS2_1b_3_ok : BG.kept_ok 60 LibSegJs_vaS2_1b.regs0 LibSegJs_vaS2_1b.regs_out3 KS_vaS2_1b_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_1b_4 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_1b.regs0 LibSegJs_vaS2_1b.regs_out4).
Lemma KS_vaS2_1b_4_ok : BG.kept_ok 60 LibSegJs_vaS2_1b.regs0 LibSegJs_vaS2_1b.regs_out4 KS_vaS2_1b_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_1b_5 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_1b.regs0 LibSegJs_vaS2_1b.regs_out5).
Lemma KS_vaS2_1b_5_ok : BG.kept_ok 60 LibSegJs_vaS2_1b.regs0 LibSegJs_vaS2_1b.regs_out5 KS_vaS2_1b_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_1b_6 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_1b.regs0 LibSegJs_vaS2_1b.regs_out6).
Lemma KS_vaS2_1b_6_ok : BG.kept_ok 60 LibSegJs_vaS2_1b.regs0 LibSegJs_vaS2_1b.regs_out6 KS_vaS2_1b_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_1b_7 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_1b.regs0 LibSegJs_vaS2_1b.regs_out7).
Lemma KS_vaS2_1b_7_ok : BG.kept_ok 60 LibSegJs_vaS2_1b.regs0 LibSegJs_vaS2_1b.regs_out7 KS_vaS2_1b_7 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_1b_8 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_1b.regs0 LibSegJs_vaS2_1b.regs_out8).
Lemma KS_vaS2_1b_8_ok : BG.kept_ok 60 LibSegJs_vaS2_1b.regs0 LibSegJs_vaS2_1b.regs_out8 KS_vaS2_1b_8 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_1b_9 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_1b.regs0 LibSegJs_vaS2_1b.regs_out9).
Lemma KS_vaS2_1b_9_ok : BG.kept_ok 60 LibSegJs_vaS2_1b.regs0 LibSegJs_vaS2_1b.regs_out9 KS_vaS2_1b_9 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_1b_10 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_1b.regs0 LibSegJs_vaS2_1b.regs_out10).
Lemma KS_vaS2_1b_10_ok : BG.kept_ok 60 LibSegJs_vaS2_1b.regs0 LibSegJs_vaS2_1b.regs_out10 KS_vaS2_1b_10 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_1b_11 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_1b.regs0 LibSegJs_vaS2_1b.regs_out11).
Lemma KS_vaS2_1b_11_ok : BG.kept_ok 60 LibSegJs_vaS2_1b.regs0 LibSegJs_vaS2_1b.regs_out11 KS_vaS2_1b_11 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_1b_12 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_1b.regs0 LibSegJs_vaS2_1b.regs_out12).
Lemma KS_vaS2_1b_12_ok : BG.kept_ok 60 LibSegJs_vaS2_1b.regs0 LibSegJs_vaS2_1b.regs_out12 KS_vaS2_1b_12 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_1b_13 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_1b.regs0 LibSegJs_vaS2_1b.regs_out13).
Lemma KS_vaS2_1b_13_ok : BG.kept_ok 60 LibSegJs_vaS2_1b.regs0 LibSegJs_vaS2_1b.regs_out13 KS_vaS2_1b_13 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_1b_14 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_1b.regs0 LibSegJs_vaS2_1b.regs_out14).
Lemma KS_vaS2_1b_14_ok : BG.kept_ok 60 LibSegJs_vaS2_1b.regs0 LibSegJs_vaS2_1b.regs_out14 KS_vaS2_1b_14 = true. Proof. vm_compute. reflexivity. Qed.
Definition vaS2_1b_conc_s := ",23A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#60S,5#>?S,6#>0S,7#:0S,8#?4S,9#8?S,:v21S,<+v21v23S,=#8S,>#1S,?-3>S,10#?5S,11-41S,12#2S,13#1388=S,14#3S,15v24S,17v25S,18#1S,1<#>=S,1=#9?S,1>#?0S,1?#90B#v21#800000000000B#2v23#4000000B#1+v21v23#800000000000Na+v21#1v27B#v27#??B#v25#??,,?,6X#36;?<#36<<4Y,T,;#2T,16+v21#2T,19+v21#1T,1:+v21#2,7X#36;?<#36<<4Y,1T,;#6T,16+v21#2T,19+v21#1T,1:+v21#2C%_v25#?0p#2#40#1,6X#36;?<#36<9<Y,2T,16+v21#2T,19+v21#1T,1:+v21#2C%_v25#?0p#2#40#1,8X#36;?<#36<<4Y,3T,;#6T,16+v21#2T,19+v21#1T,1:+v21#2C%_v25#?4p#2#40#1D#1%_v25#?0p#2#40,7X#36;?<#36<9<Y,4T,16+v21#2T,19+v21#1T,1:+v21#2C%_v25#?4p#2#40#1D#1%_v25#?0p#2#40,8X#36;?<#36<<4Y,5T,;#6T,16+v21#2T,19+v21#1T,1:+v21#2D#1%_v25#?4p#2#40D#1%_v25#?0p#2#40,9X#36;?<#36<9<Y,6T,;#6T,16+v21#2T,19+v21#1T,1:+v21#2Cv25#?5D#1%_v25#?4p#2#40D#1%_v25#?0p#2#40,9X#36;?<#36<<4Y,7T,;#6T,16+v21#2T,19+v21#1T,1:+v21#2D#?5v25D#1%_v25#?4p#2#40D#1%_v25#?0p#2#40,7X#36;?<#36<<4Y,8T,;#6T,16+v21#2T,19+v21#1T,1:+v21#2C%_v25#>0p#2#40#1,6X#36;?<#36<9<Y,9T,16+v21#2T,19+v21#1T,1:+v21#2C%_v25#>0p#2#40#1,8X#36;?<#36<<4Y,:T,;#6T,16+v21#2T,19+v21#1T,1:+v21#2C%_v25#>=p#2#40#1D#1%_v25#>0p#2#40,7X#36;?<#36<9<Y,;T,16+v21#2T,19+v21#1T,1:+v21#2C%_v25#>=p#2#40#1D#1%_v25#>0p#2#40,8X#36;?<#36<<4Y,<T,;#6T,16+v21#2T,19+v21#1T,1:+v21#2D#1%_v25#>=p#2#40D#1%_v25#>0p#2#40,9X#36;?<#36<9<Y,=T,;#6T,16+v21#2T,19+v21#1T,1:+v21#2Cv25#?5D#1%_v25#>=p#2#40D#1%_v25#>0p#2#40,9X#36;?<#36<<4Y,>T,;#6T,16+v21#2T,19+v21#1T,1:+v21#2D#?5v25D#1%_v25#>=p#2#40D#1%_v25#>0p#2#40"%pstring.
Lemma vaS2_1b_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_vaS2_1b_0; KS_vaS2_1b_1; KS_vaS2_1b_2; KS_vaS2_1b_3; KS_vaS2_1b_4; KS_vaS2_1b_5; KS_vaS2_1b_6; KS_vaS2_1b_7; KS_vaS2_1b_8; KS_vaS2_1b_9; KS_vaS2_1b_10; KS_vaS2_1b_11; KS_vaS2_1b_12; KS_vaS2_1b_13; KS_vaS2_1b_14] fx R M V vaS2_1b_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_vaS2_1b_0; KS_vaS2_1b_1; KS_vaS2_1b_2; KS_vaS2_1b_3; KS_vaS2_1b_4; KS_vaS2_1b_5; KS_vaS2_1b_6; KS_vaS2_1b_7; KS_vaS2_1b_8; KS_vaS2_1b_9; KS_vaS2_1b_10; KS_vaS2_1b_11; KS_vaS2_1b_12; KS_vaS2_1b_13; KS_vaS2_1b_14] LibSegJs_vaS2_1b.regs0 LibSegJs_vaS2_1b.kn0 LibSegJs_vaS2_1b.BR LibSegJs_vaS2_1b.PSS LibSegJs_vaS2_1b.NX0 LibSegJs_vaS2_1b.F0 224252 LibSegJs_vaS2_1b.seg_sound_ax fx R M V vaS2_1b_conc_s. Qed.
Definition KS_vaS2_2a : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_2a.regs0 LibSegJs_vaS2_2a.regs_out0).
Lemma KS_vaS2_2a_ok : BG.kept_ok 60 LibSegJs_vaS2_2a.regs0 LibSegJs_vaS2_2a.regs_out0 KS_vaS2_2a = true. Proof. vm_compute. reflexivity. Qed.
Definition vaS2_2a_conc_s := ",20A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#60S,5#>?S,6#>0S,7#:0S,8#?4S,9#8?S,:v21S,<+v21v23S,=#8S,>#1S,?-3>S,10#?5S,11-41S,12#2S,13#1388=S,14#3S,15v24S,17v25S,18#2S,1<#>=S,1=#9?S,1>#?0S,1?#90B#v21#800000000000B#1v23#2B#1+v21v23#800000000000B#v25#??,,1,3X#36;?<#36<<4Y,T,;#5"%pstring.
Lemma vaS2_2a_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_vaS2_2a] fx R M V vaS2_2a_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_vaS2_2a] LibSegJs_vaS2_2a.regs0 LibSegJs_vaS2_2a.kn0 LibSegJs_vaS2_2a.BR LibSegJs_vaS2_2a.PSS LibSegJs_vaS2_2a.NX0 LibSegJs_vaS2_2a.F0 224252 LibSegJs_vaS2_2a.seg_sound_ax fx R M V vaS2_2a_conc_s. Qed.
Definition KS_vaS2_2b_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out0).
Lemma KS_vaS2_2b_0_ok : BG.kept_ok 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out0 KS_vaS2_2b_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_2b_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out1).
Lemma KS_vaS2_2b_1_ok : BG.kept_ok 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out1 KS_vaS2_2b_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_2b_2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out2).
Lemma KS_vaS2_2b_2_ok : BG.kept_ok 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out2 KS_vaS2_2b_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_2b_3 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out3).
Lemma KS_vaS2_2b_3_ok : BG.kept_ok 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out3 KS_vaS2_2b_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_2b_4 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out4).
Lemma KS_vaS2_2b_4_ok : BG.kept_ok 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out4 KS_vaS2_2b_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_2b_5 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out5).
Lemma KS_vaS2_2b_5_ok : BG.kept_ok 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out5 KS_vaS2_2b_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_2b_6 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out6).
Lemma KS_vaS2_2b_6_ok : BG.kept_ok 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out6 KS_vaS2_2b_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_2b_7 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out7).
Lemma KS_vaS2_2b_7_ok : BG.kept_ok 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out7 KS_vaS2_2b_7 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_2b_8 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out8).
Lemma KS_vaS2_2b_8_ok : BG.kept_ok 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out8 KS_vaS2_2b_8 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_2b_9 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out9).
Lemma KS_vaS2_2b_9_ok : BG.kept_ok 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out9 KS_vaS2_2b_9 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_2b_10 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out10).
Lemma KS_vaS2_2b_10_ok : BG.kept_ok 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out10 KS_vaS2_2b_10 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_2b_11 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out11).
Lemma KS_vaS2_2b_11_ok : BG.kept_ok 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out11 KS_vaS2_2b_11 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_2b_12 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out12).
Lemma KS_vaS2_2b_12_ok : BG.kept_ok 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out12 KS_vaS2_2b_12 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_2b_13 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out13).
Lemma KS_vaS2_2b_13_ok : BG.kept_ok 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out13 KS_vaS2_2b_13 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_2b_14 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out14).
Lemma KS_vaS2_2b_14_ok : BG.kept_ok 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out14 KS_vaS2_2b_14 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_2b_15 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out15).
Lemma KS_vaS2_2b_15_ok : BG.kept_ok 60 LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.regs_out15 KS_vaS2_2b_15 = true. Proof. vm_compute. reflexivity. Qed.
Definition vaS2_2b_conc_s := ",26A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40A#v28p#2#40S,2_v2#60S,5#>?S,6#>0S,7#:0S,8#?4S,9#8?S,:v21S,<+v21v23S,=#8S,>#1S,?-3>S,10#?5S,11-41S,12#2S,13#1388=S,14#3S,15v24S,17v25S,18#2S,1<#>=S,1=#9?S,1>#?0S,1?#90B#v21#800000000000B#3v23#4000000B#1+v21v23#800000000000Na+v21#1v27B#v27#??Na+v21#2v28B#v28#??B#v25#??,,10,6X#36;?<#36<<4Y,T,;#2T,16+v21#3T,19+v21#2T,1:+v21#3,6X#36;?<#36<<4Y,1T,;#2T,16+v21#3T,19+v21#2T,1:+v21#2,7X#36;?<#36<<4Y,2T,;#6T,16+v21#3T,19+v21#2T,1:+v21#2C%_v25#?0p#2#40#1,6X#36;?<#36<9<Y,3T,16+v21#3T,19+v21#2T,1:+v21#2C%_v25#?0p#2#40#1,8X#36;?<#36<<4Y,4T,;#6T,16+v21#3T,19+v21#2T,1:+v21#2C%_v25#?4p#2#40#1D#1%_v25#?0p#2#40,7X#36;?<#36<9<Y,5T,16+v21#3T,19+v21#2T,1:+v21#2C%_v25#?4p#2#40#1D#1%_v25#?0p#2#40,8X#36;?<#36<<4Y,6T,;#6T,16+v21#3T,19+v21#2T,1:+v21#2D#1%_v25#?4p#2#40D#1%_v25#?0p#2#40,9X#36;?<#36<9<Y,7T,;#6T,16+v21#3T,19+v21#2T,1:+v21#2Cv25#?5D#1%_v25#?4p#2#40D#1%_v25#?0p#2#40,9X#36;?<#36<<4Y,8T,;#6T,16+v21#3T,19+v21#2T,1:+v21#2D#?5v25D#1%_v25#?4p#2#40D#1%_v25#?0p#2#40,7X#36;?<#36<<4Y,9T,;#6T,16+v21#3T,19+v21#2T,1:+v21#2C%_v25#>0p#2#40#1,6X#36;?<#36<9<Y,:T,16+v21#3T,19+v21#2T,1:+v21#2C%_v25#>0p#2#40#1,8X#36;?<#36<<4Y,;T,;#6T,16+v21#3T,19+v21#2T,1:+v21#2C%_v25#>=p#2#40#1D#1%_v25#>0p#2#40,7X#36;?<#36<9<Y,<T,16+v21#3T,19+v21#2T,1:+v21#2C%_v25#>=p#2#40#1D#1%_v25#>0p#2#40,8X#36;?<#36<<4Y,=T,;#6T,16+v21#3T,19+v21#2T,1:+v21#2D#1%_v25#>=p#2#40D#1%_v25#>0p#2#40,9X#36;?<#36<9<Y,>T,;#6T,16+v21#3T,19+v21#2T,1:+v21#2Cv25#?5D#1%_v25#>=p#2#40D#1%_v25#>0p#2#40,9X#36;?<#36<<4Y,?T,;#6T,16+v21#3T,19+v21#2T,1:+v21#2D#?5v25D#1%_v25#>=p#2#40D#1%_v25#>0p#2#40"%pstring.
Lemma vaS2_2b_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_vaS2_2b_0; KS_vaS2_2b_1; KS_vaS2_2b_2; KS_vaS2_2b_3; KS_vaS2_2b_4; KS_vaS2_2b_5; KS_vaS2_2b_6; KS_vaS2_2b_7; KS_vaS2_2b_8; KS_vaS2_2b_9; KS_vaS2_2b_10; KS_vaS2_2b_11; KS_vaS2_2b_12; KS_vaS2_2b_13; KS_vaS2_2b_14; KS_vaS2_2b_15] fx R M V vaS2_2b_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_vaS2_2b_0; KS_vaS2_2b_1; KS_vaS2_2b_2; KS_vaS2_2b_3; KS_vaS2_2b_4; KS_vaS2_2b_5; KS_vaS2_2b_6; KS_vaS2_2b_7; KS_vaS2_2b_8; KS_vaS2_2b_9; KS_vaS2_2b_10; KS_vaS2_2b_11; KS_vaS2_2b_12; KS_vaS2_2b_13; KS_vaS2_2b_14; KS_vaS2_2b_15] LibSegJs_vaS2_2b.regs0 LibSegJs_vaS2_2b.kn0 LibSegJs_vaS2_2b.BR LibSegJs_vaS2_2b.PSS LibSegJs_vaS2_2b.NX0 LibSegJs_vaS2_2b.F0 224252 LibSegJs_vaS2_2b.seg_sound_ax fx R M V vaS2_2b_conc_s. Qed.
Definition KS_vaS2_3a : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_3a.regs0 LibSegJs_vaS2_3a.regs_out0).
Lemma KS_vaS2_3a_ok : BG.kept_ok 60 LibSegJs_vaS2_3a.regs0 LibSegJs_vaS2_3a.regs_out0 KS_vaS2_3a = true. Proof. vm_compute. reflexivity. Qed.
Definition vaS2_3a_conc_s := ",20A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#60S,5#>?S,6#>0S,7#:0S,8#?4S,9#8?S,:v21S,<+v21v23S,=#8S,>#1S,?-3>S,10#?5S,11-41S,12#2S,13#1388=S,14#3S,15v24S,17v25S,18#3S,1<#>=S,1=#9?S,1>#?0S,1?#90B#v21#800000000000B#1v23#3B#1+v21v23#800000000000B#v25#??,,1,3X#36;?<#36<<4Y,T,;#5"%pstring.
Lemma vaS2_3a_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_vaS2_3a] fx R M V vaS2_3a_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_vaS2_3a] LibSegJs_vaS2_3a.regs0 LibSegJs_vaS2_3a.kn0 LibSegJs_vaS2_3a.BR LibSegJs_vaS2_3a.PSS LibSegJs_vaS2_3a.NX0 LibSegJs_vaS2_3a.F0 224252 LibSegJs_vaS2_3a.seg_sound_ax fx R M V vaS2_3a_conc_s. Qed.
Definition KS_vaS2_3b_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out0).
Lemma KS_vaS2_3b_0_ok : BG.kept_ok 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out0 KS_vaS2_3b_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out1).
Lemma KS_vaS2_3b_1_ok : BG.kept_ok 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out1 KS_vaS2_3b_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out2).
Lemma KS_vaS2_3b_2_ok : BG.kept_ok 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out2 KS_vaS2_3b_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_3 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out3).
Lemma KS_vaS2_3b_3_ok : BG.kept_ok 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out3 KS_vaS2_3b_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_4 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out4).
Lemma KS_vaS2_3b_4_ok : BG.kept_ok 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out4 KS_vaS2_3b_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_5 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out5).
Lemma KS_vaS2_3b_5_ok : BG.kept_ok 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out5 KS_vaS2_3b_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_6 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out6).
Lemma KS_vaS2_3b_6_ok : BG.kept_ok 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out6 KS_vaS2_3b_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_7 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out7).
Lemma KS_vaS2_3b_7_ok : BG.kept_ok 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out7 KS_vaS2_3b_7 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_8 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out8).
Lemma KS_vaS2_3b_8_ok : BG.kept_ok 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out8 KS_vaS2_3b_8 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_9 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out9).
Lemma KS_vaS2_3b_9_ok : BG.kept_ok 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out9 KS_vaS2_3b_9 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_10 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out10).
Lemma KS_vaS2_3b_10_ok : BG.kept_ok 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out10 KS_vaS2_3b_10 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_11 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out11).
Lemma KS_vaS2_3b_11_ok : BG.kept_ok 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out11 KS_vaS2_3b_11 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_12 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out12).
Lemma KS_vaS2_3b_12_ok : BG.kept_ok 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out12 KS_vaS2_3b_12 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_13 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out13).
Lemma KS_vaS2_3b_13_ok : BG.kept_ok 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out13 KS_vaS2_3b_13 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_14 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out14).
Lemma KS_vaS2_3b_14_ok : BG.kept_ok 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out14 KS_vaS2_3b_14 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_15 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out15).
Lemma KS_vaS2_3b_15_ok : BG.kept_ok 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out15 KS_vaS2_3b_15 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_3b_16 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out16).
Lemma KS_vaS2_3b_16_ok : BG.kept_ok 60 LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.regs_out16 KS_vaS2_3b_16 = true. Proof. vm_compute. reflexivity. Qed.
Definition vaS2_3b_conc_s := ",29A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40S,2_v2#60S,5#>?S,6#>0S,7#:0S,8#?4S,9#8?S,:v21S,<+v21v23S,=#8S,>#1S,?-3>S,10#?5S,11-41S,12#2S,13#1388=S,14#3S,15v24S,17v25S,18#3S,1<#>=S,1=#9?S,1>#?0S,1?#90B#v21#800000000000B#4v23#4000000B#1+v21v23#800000000000Na+v21#1v27B#v27#??Na+v21#2v28B#v28#??Na+v21#3v29B#v29#??B#v25#??,,11,6X#36;?<#36<<4Y,T,;#2T,16+v21#4T,19+v21#3T,1:+v21#3,6X#36;?<#36<<4Y,1T,;#2T,16+v21#4T,19+v21#3T,1:+v21#3,6X#36;?<#36<<4Y,2T,;#2T,16+v21#4T,19+v21#3T,1:+v21#2,7X#36;?<#36<<4Y,3T,;#6T,16+v21#4T,19+v21#3T,1:+v21#2C%_v25#?0p#2#40#1,6X#36;?<#36<9<Y,4T,16+v21#4T,19+v21#3T,1:+v21#2C%_v25#?0p#2#40#1,8X#36;?<#36<<4Y,5T,;#6T,16+v21#4T,19+v21#3T,1:+v21#2C%_v25#?4p#2#40#1D#1%_v25#?0p#2#40,7X#36;?<#36<9<Y,6T,16+v21#4T,19+v21#3T,1:+v21#2C%_v25#?4p#2#40#1D#1%_v25#?0p#2#40,8X#36;?<#36<<4Y,7T,;#6T,16+v21#4T,19+v21#3T,1:+v21#2D#1%_v25#?4p#2#40D#1%_v25#?0p#2#40,9X#36;?<#36<9<Y,8T,;#6T,16+v21#4T,19+v21#3T,1:+v21#2Cv25#?5D#1%_v25#?4p#2#40D#1%_v25#?0p#2#40,9X#36;?<#36<<4Y,9T,;#6T,16+v21#4T,19+v21#3T,1:+v21#2D#?5v25D#1%_v25#?4p#2#40D#1%_v25#?0p#2#40,7X#36;?<#36<<4Y,:T,;#6T,16+v21#4T,19+v21#3T,1:+v21#2C%_v25#>0p#2#40#1,6X#36;?<#36<9<Y,;T,16+v21#4T,19+v21#3T,1:+v21#2C%_v25#>0p#2#40#1,8X#36;?<#36<<4Y,<T,;#6T,16+v21#4T,19+v21#3T,1:+v21#2C%_v25#>=p#2#40#1D#1%_v25#>0p#2#40,7X#36;?<#36<9<Y,=T,16+v21#4T,19+v21#3T,1:+v21#2C%_v25#>=p#2#40#1D#1%_v25#>0p#2#40,8X#36;?<#36<<4Y,>T,;#6T,16+v21#4T,19+v21#3T,1:+v21#2D#1%_v25#>=p#2#40D#1%_v25#>0p#2#40,9X#36;?<#36<9<Y,?T,;#6T,16+v21#4T,19+v21#3T,1:+v21#2Cv25#?5D#1%_v25#>=p#2#40D#1%_v25#>0p#2#40,9X#36;?<#36<<4Y,10T,;#6T,16+v21#4T,19+v21#3T,1:+v21#2D#?5v25D#1%_v25#>=p#2#40D#1%_v25#>0p#2#40"%pstring.
Lemma vaS2_3b_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_vaS2_3b_0; KS_vaS2_3b_1; KS_vaS2_3b_2; KS_vaS2_3b_3; KS_vaS2_3b_4; KS_vaS2_3b_5; KS_vaS2_3b_6; KS_vaS2_3b_7; KS_vaS2_3b_8; KS_vaS2_3b_9; KS_vaS2_3b_10; KS_vaS2_3b_11; KS_vaS2_3b_12; KS_vaS2_3b_13; KS_vaS2_3b_14; KS_vaS2_3b_15; KS_vaS2_3b_16] fx R M V vaS2_3b_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_vaS2_3b_0; KS_vaS2_3b_1; KS_vaS2_3b_2; KS_vaS2_3b_3; KS_vaS2_3b_4; KS_vaS2_3b_5; KS_vaS2_3b_6; KS_vaS2_3b_7; KS_vaS2_3b_8; KS_vaS2_3b_9; KS_vaS2_3b_10; KS_vaS2_3b_11; KS_vaS2_3b_12; KS_vaS2_3b_13; KS_vaS2_3b_14; KS_vaS2_3b_15; KS_vaS2_3b_16] LibSegJs_vaS2_3b.regs0 LibSegJs_vaS2_3b.kn0 LibSegJs_vaS2_3b.BR LibSegJs_vaS2_3b.PSS LibSegJs_vaS2_3b.NX0 LibSegJs_vaS2_3b.F0 224252 LibSegJs_vaS2_3b.seg_sound_ax fx R M V vaS2_3b_conc_s. Qed.
Definition KS_vaS2_big_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_big.regs0 LibSegJs_vaS2_big.regs_out0).
Lemma KS_vaS2_big_0_ok : BG.kept_ok 60 LibSegJs_vaS2_big.regs0 LibSegJs_vaS2_big.regs_out0 KS_vaS2_big_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaS2_big_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaS2_big.regs0 LibSegJs_vaS2_big.regs_out1).
Lemma KS_vaS2_big_1_ok : BG.kept_ok 60 LibSegJs_vaS2_big.regs0 LibSegJs_vaS2_big.regs_out1 KS_vaS2_big_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition vaS2_big_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#60S,5#>?S,6#>0S,7#:0S,8#?4S,9#8?S,:v21S,<+v21v23S,=#8S,>#1S,?-3>S,10#?5S,11-41S,12#2S,13#1388=S,14#3S,15v24S,17v25S,18v26S,1<#>=S,1=#9?S,1>#?0S,1?#90B#v21#800000000000B#1v23#4000000B#1+v21v23#800000000000B#4v26#??B#v25#??,,2,7X#36;?<#36<<4Y,T,;#1T,16++v21v26#1T,19+v21v26T,1:++v21v26#1Cv26v23,4X#36;?<#36<<4Y,1T,;#5Dv23v26"%pstring.
Lemma vaS2_big_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_vaS2_big_0; KS_vaS2_big_1] fx R M V vaS2_big_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_vaS2_big_0; KS_vaS2_big_1] LibSegJs_vaS2_big.regs0 LibSegJs_vaS2_big.kn0 LibSegJs_vaS2_big.BR LibSegJs_vaS2_big.PSS LibSegJs_vaS2_big.NX0 LibSegJs_vaS2_big.F0 224252 LibSegJs_vaS2_big.seg_sound_ax fx R M V vaS2_big_conc_s. Qed.
Definition KS_vaB_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaB.regs0 LibSegJs_vaB.regs_out0).
Lemma KS_vaB_0_ok : BG.kept_ok 60 LibSegJs_vaB.regs0 LibSegJs_vaB.regs_out0 KS_vaB_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vaB_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaB.regs0 LibSegJs_vaB.regs_out1).
Lemma KS_vaB_1_ok : BG.kept_ok 60 LibSegJs_vaB.regs0 LibSegJs_vaB.regs_out1 KS_vaB_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition vaB_conc_s := ",1<A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v25p#2#40S,2_v2#60S,5#>?S,6#>0S,7#:0S,8#?4S,9#8?S,:v25S,<+v21v23S,=#8S,>#1S,?-3>S,10#?5S,11-41S,12#2S,13#1388=S,14#3S,16v21S,1<#>=S,1=#9?S,1>#?0S,1?#90B#v21#800000000000B#v23#800000000000B#+v21v23#800000000000,,2,5X#36<9<#36<<4Y,T,:+v21v23T,;#C%_v21%+v21v23p#2#40p#2#40#1,4X#36<9<#36;6<Y,1T,:v21D#1%_v21%+v21v23p#2#40p#2#40"%pstring.
Lemma vaB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_vaB_0; KS_vaB_1] fx R M V vaB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_vaB_0; KS_vaB_1] LibSegJs_vaB.regs0 LibSegJs_vaB.kn0 LibSegJs_vaB.BR LibSegJs_vaB.PSS LibSegJs_vaB.NX0 LibSegJs_vaB.F0 224412 LibSegJs_vaB.seg_sound_ax fx R M V vaB_conc_s. Qed.
Definition KS_vaX : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_vaX.regs0 LibSegJs_vaX.regs_out0).
Lemma KS_vaX_ok : BG.kept_ok 60 LibSegJs_vaX.regs0 LibSegJs_vaX.regs_out0 KS_vaX = true. Proof. vm_compute. reflexivity. Qed.
Definition vaX_conc_s := ",1;A#v2p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40A#v34p#2#40A#v35p#2#40A#v36p#2#40A#v37p#2#40S,2_v2#60B#7???7?800060v2#800000000000Hv2#10I_v2#60#60La_v2#8v2=La_v2#10v2>La_v2#18v2?La_v2#20v30La_v2#28v31La_v2#30v32La_v2#38v33La_v2#40v34La_v2#48v35La_v2#50v36La_v2#58v37,,1,>X#36<<4#36<?4Y,T,2v2T,8v2=T,9v2>T,12v2?T,13v30T,14v31T,15v32T,16v33T,17v34T,18v35T,19v36T,1:v37"%pstring.
Lemma vaX_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_vaX] fx R M V vaX_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_vaX] LibSegJs_vaX.regs0 LibSegJs_vaX.kn0 LibSegJs_vaX.BR LibSegJs_vaX.PSS LibSegJs_vaX.NX0 LibSegJs_vaX.F0 224452 LibSegJs_vaX.seg_sound_ax fx R M V vaX_conc_s. Qed.
End PMVAP.
