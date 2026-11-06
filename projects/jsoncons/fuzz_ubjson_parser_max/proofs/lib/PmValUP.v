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
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ju0PlanKit AsanPlanCore
BigLinkBase BigLinkGlueUb0 L5Defs L5KnU L5KnAU.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJu_uvaE LibSegJu_uvaF8 LibSegJu_uvaF1 LibSegJu_uvaS1 LibSegJu_uvaS2_0 LibSegJu_uvaS2_1a LibSegJu_uvaS2_1b LibSegJu_uvaS2_2a LibSegJu_uvaS2_2b LibSegJu_uvaS2_3a LibSegJu_uvaS2_3b LibSegJu_uvaS2_big LibSegJu_uvaB LibSegJu_uvaX.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMVAUP.
Module BG := BigLinkGlueUb0.BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcU.
Definition KS_uvaE_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaE.regs0 LibSegJu_uvaE.regs_out0).
Lemma KS_uvaE_0_ok : BG.kept_ok 60 LibSegJu_uvaE.regs0 LibSegJu_uvaE.regs_out0 KS_uvaE_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaE_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaE.regs0 LibSegJu_uvaE.regs_out1).
Lemma KS_uvaE_1_ok : BG.kept_ok 60 LibSegJu_uvaE.regs0 LibSegJu_uvaE.regs_out1 KS_uvaE_1 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition uvaE_conc_s := ",;A#v2p#2#40A#v21p#2#40A#v23p#2#40S,2v2S,:v21S,;v23B#7???7?800060v2#800000000000Hv2#10I_v2#60#60B#1v21#800000000000B#v23#3??????,1_v2#60#60,2,13X#37844#37:68Y,T,2_v2#60T,<+v21v23T,=#1T,>#C%_v23#p#2#40#1Lb_v2#60r1;Lb_v2#58r1:Lb_v2#50r19Lb_v2#48r18Lb_v2#40r17Lb_v2#38r16Lb_v2#30r15Lb_v2#28r14Lb_v2#20r13Lb_v2#18r12Lb_v2#10r9Lb_v2#8r8,25X#37844#378>4Y,1T,2_v2#60T,5#2T,6^#?#?????????????;?T,7#>?T,8#?0T,9#90T,;#1389<T,<+v21v23T,=#8T,>^#?#???????????????T,?#1T,10^#?#?????????????<2T,11#?5T,12#?4T,13#8?T,14#138<1T,15^#?#??????????><73>T,16#3T,1<#>0T,1=#:0T,1>#>=T,1?#9?D#1%_v23#p#2#40Lb_v2#60r1;Lb_v2#58r1:Lb_v2#50r19Lb_v2#48r18Lb_v2#40r17Lb_v2#38r16Lb_v2#30r15Lb_v2#28r14Lb_v2#20r13Lb_v2#18r12Lb_v2#10r9Lb_v2#8r8"%pstring.
Lemma uvaE_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uvaE_0; KS_uvaE_1] fx R M V uvaE_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uvaE_0; KS_uvaE_1] LibSegJu_uvaE.regs0 LibSegJu_uvaE.kn0 LibSegJu_uvaE.BR LibSegJu_uvaE.PSS LibSegJu_uvaE.NX0 LibSegJu_uvaE.F0 227396 LibSegJu_uvaE.seg_sound_ax fx R M V uvaE_conc_s. Qed.
Definition KS_uvaF8_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaF8.regs0 LibSegJu_uvaF8.regs_out0).
Lemma KS_uvaF8_0_ok : BG.kept_ok 60 LibSegJu_uvaF8.regs0 LibSegJu_uvaF8.regs_out0 KS_uvaF8_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaF8_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaF8.regs0 LibSegJu_uvaF8.regs_out1).
Lemma KS_uvaF8_1_ok : BG.kept_ok 60 LibSegJu_uvaF8.regs0 LibSegJu_uvaF8.regs_out1 KS_uvaF8_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaF8_2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaF8.regs0 LibSegJu_uvaF8.regs_out2).
Lemma KS_uvaF8_2_ok : BG.kept_ok 60 LibSegJu_uvaF8.regs0 LibSegJu_uvaF8.regs_out2 KS_uvaF8_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaF8_3 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaF8.regs0 LibSegJu_uvaF8.regs_out3).
Lemma KS_uvaF8_3_ok : BG.kept_ok 60 LibSegJu_uvaF8.regs0 LibSegJu_uvaF8.regs_out3 KS_uvaF8_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaF8_4 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaF8.regs0 LibSegJu_uvaF8.regs_out4).
Lemma KS_uvaF8_4_ok : BG.kept_ok 60 LibSegJu_uvaF8.regs0 LibSegJu_uvaF8.regs_out4 KS_uvaF8_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaF8_5 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaF8.regs0 LibSegJu_uvaF8.regs_out5).
Lemma KS_uvaF8_5_ok : BG.kept_ok 60 LibSegJu_uvaF8.regs0 LibSegJu_uvaF8.regs_out5 KS_uvaF8_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaF8_6 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaF8.regs0 LibSegJu_uvaF8.regs_out6).
Lemma KS_uvaF8_6_ok : BG.kept_ok 60 LibSegJu_uvaF8.regs0 LibSegJu_uvaF8.regs_out6 KS_uvaF8_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaF8_7 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaF8.regs0 LibSegJu_uvaF8.regs_out7).
Lemma KS_uvaF8_7_ok : BG.kept_ok 60 LibSegJu_uvaF8.regs0 LibSegJu_uvaF8.regs_out7 KS_uvaF8_7 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaF8_8 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaF8.regs0 LibSegJu_uvaF8.regs_out8).
Lemma KS_uvaF8_8_ok : BG.kept_ok 60 LibSegJu_uvaF8.regs0 LibSegJu_uvaF8.regs_out8 KS_uvaF8_8 = true. Proof. vm_compute. reflexivity. Qed.
Definition uvaF8_conc_s := ",34A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40S,2_v2#60S,5#2S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<+v21v23S,=#8S,>-1S,?#1S,10-3>S,11#?5S,12#?4S,13#8?S,14#138<1S,15^#?#??????????><73>S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Nav21v24B#v24#??Na+v21#1v25B#v25#??Na+v21#2v26B#v26#??Na+v21#3v27B#v27#??Na+v21#4v28B#v28#??Na+v21#5v29B#v29#??Na+v21#6v2:B#v2:#??Na+v21#7v2;B#v2;#??,,9,2X#378>4#37978Y,,4X#378>4#37978Y,1T,:+v21#1T,;+v21#1,4X#378>4#37978Y,2T,:+v21#2T,;+v21#2,4X#378>4#37978Y,3T,:+v21#3T,;+v21#3,4X#378>4#37978Y,4T,:+v21#4T,;+v21#4,4X#378>4#37978Y,5T,:+v21#5T,;+v21#5,4X#378>4#37978Y,6T,:+v21#6T,;+v21#6,4X#378>4#37978Y,7T,:+v21#7T,;+v21#7,4X#378>4#37:40Y,8T,;+v21#7T,17+v21#8"%pstring.
Lemma uvaF8_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uvaF8_0; KS_uvaF8_1; KS_uvaF8_2; KS_uvaF8_3; KS_uvaF8_4; KS_uvaF8_5; KS_uvaF8_6; KS_uvaF8_7; KS_uvaF8_8] fx R M V uvaF8_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uvaF8_0; KS_uvaF8_1; KS_uvaF8_2; KS_uvaF8_3; KS_uvaF8_4; KS_uvaF8_5; KS_uvaF8_6; KS_uvaF8_7; KS_uvaF8_8] LibSegJu_uvaF8.regs0 LibSegJu_uvaF8.kn0 LibSegJu_uvaF8.BR LibSegJu_uvaF8.PSS LibSegJu_uvaF8.NX0 LibSegJu_uvaF8.F0 227556 LibSegJu_uvaF8.seg_sound_ax fx R M V uvaF8_conc_s. Qed.
Definition KS_uvaF1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaF1.regs0 LibSegJu_uvaF1.regs_out0).
Lemma KS_uvaF1_ok : BG.kept_ok 60 LibSegJu_uvaF1.regs0 LibSegJu_uvaF1.regs_out0 KS_uvaF1 = true. Proof. vm_compute. reflexivity. Qed.
Definition uvaF1_conc_s := ",1<A#v2p#2#40A#v21p#2#40A#v23p#2#40S,2_v2#60S,5#2S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<+v21v23S,=#8S,>-1S,?#1S,10-3>S,11#?5S,12#?4S,13#8?S,14#138<1S,15^#?#??????????><73>S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#1v21#800000000000B#1v23#7B#1+v21v23#800000000000,,1,3X#378>4#37978Y,T,;v23"%pstring.
Lemma uvaF1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uvaF1] fx R M V uvaF1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uvaF1] LibSegJu_uvaF1.regs0 LibSegJu_uvaF1.kn0 LibSegJu_uvaF1.BR LibSegJu_uvaF1.PSS LibSegJu_uvaF1.NX0 LibSegJu_uvaF1.F0 227556 LibSegJu_uvaF1.seg_sound_ax fx R M V uvaF1_conc_s. Qed.
Definition KS_uvaS1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS1.regs0 LibSegJu_uvaS1.regs_out0).
Lemma KS_uvaS1_ok : BG.kept_ok 60 LibSegJu_uvaS1.regs0 LibSegJu_uvaS1.regs_out0 KS_uvaS1 = true. Proof. vm_compute. reflexivity. Qed.
Definition uvaS1_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#2S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<+v21v23S,=#8S,>-1S,?#1S,10-3>S,11#?5S,12#?4S,13#8?S,14#138<1S,15^#?#??????????><73>S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#1v21#800000000000B#1v23#4000000B#1+v21v23#800000000000Nav21v24B#v24#??,,1,4X#37978#37988Y,T,;+v24#138<1T,18v24"%pstring.
Lemma uvaS1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uvaS1] fx R M V uvaS1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uvaS1] LibSegJu_uvaS1.regs0 LibSegJu_uvaS1.kn0 LibSegJu_uvaS1.BR LibSegJu_uvaS1.PSS LibSegJu_uvaS1.NX0 LibSegJu_uvaS1.F0 227704 LibSegJu_uvaS1.seg_sound_ax fx R M V uvaS1_conc_s. Qed.
Definition KS_uvaS2_0_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_0.regs0 LibSegJu_uvaS2_0.regs_out0).
Lemma KS_uvaS2_0_0_ok : BG.kept_ok 60 LibSegJu_uvaS2_0.regs0 LibSegJu_uvaS2_0.regs_out0 KS_uvaS2_0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_0_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_0.regs0 LibSegJu_uvaS2_0.regs_out1).
Lemma KS_uvaS2_0_1_ok : BG.kept_ok 60 LibSegJu_uvaS2_0.regs0 LibSegJu_uvaS2_0.regs_out1 KS_uvaS2_0_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_0_2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_0.regs0 LibSegJu_uvaS2_0.regs_out2).
Lemma KS_uvaS2_0_2_ok : BG.kept_ok 60 LibSegJu_uvaS2_0.regs0 LibSegJu_uvaS2_0.regs_out2 KS_uvaS2_0_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition uvaS2_0_conc_s := ",20A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#2S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<+v21v23S,=#8S,>-1S,?#1S,10-3>S,11#?5S,12#?4S,13#8?S,14#138<1S,15^#?#??????????><73>S,16#3S,18v24S,19#S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#1v21#800000000000B#1v23#4000000B#1+v21v23#800000000000B#v24#??,,3,5X#3798<#37:68Y,T,;#6T,17+v21#1T,1:v21,6X#3798<#37:40Y,1T,;#6T,17+v21#1T,1:v21Cv24#?5,6X#3798<#37:68Y,2T,;#6T,17+v21#1T,1:v21D#?5v24"%pstring.
Lemma uvaS2_0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uvaS2_0_0; KS_uvaS2_0_1; KS_uvaS2_0_2] fx R M V uvaS2_0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uvaS2_0_0; KS_uvaS2_0_1; KS_uvaS2_0_2] LibSegJu_uvaS2_0.regs0 LibSegJu_uvaS2_0.kn0 LibSegJu_uvaS2_0.BR LibSegJu_uvaS2_0.PSS LibSegJu_uvaS2_0.NX0 LibSegJu_uvaS2_0.F0 227724 LibSegJu_uvaS2_0.seg_sound_ax fx R M V uvaS2_0_conc_s. Qed.
Definition KS_uvaS2_1a : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_1a.regs0 LibSegJu_uvaS2_1a.regs_out0).
Lemma KS_uvaS2_1a_ok : BG.kept_ok 60 LibSegJu_uvaS2_1a.regs0 LibSegJu_uvaS2_1a.regs_out0 KS_uvaS2_1a = true. Proof. vm_compute. reflexivity. Qed.
Definition uvaS2_1a_conc_s := ",20A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#2S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<+v21v23S,=#8S,>-1S,?#1S,10-3>S,11#?5S,12#?4S,13#8?S,14#138<1S,15^#?#??????????><73>S,16#3S,18v24S,19#1S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#1v21#800000000000B#1v23#1B#1+v21v23#800000000000B#v24#??,,1,3X#3798<#37:68Y,T,;#5"%pstring.
Lemma uvaS2_1a_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uvaS2_1a] fx R M V uvaS2_1a_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uvaS2_1a] LibSegJu_uvaS2_1a.regs0 LibSegJu_uvaS2_1a.kn0 LibSegJu_uvaS2_1a.BR LibSegJu_uvaS2_1a.PSS LibSegJu_uvaS2_1a.NX0 LibSegJu_uvaS2_1a.F0 227724 LibSegJu_uvaS2_1a.seg_sound_ax fx R M V uvaS2_1a_conc_s. Qed.
Definition KS_uvaS2_1b_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_1b.regs0 LibSegJu_uvaS2_1b.regs_out0).
Lemma KS_uvaS2_1b_0_ok : BG.kept_ok 60 LibSegJu_uvaS2_1b.regs0 LibSegJu_uvaS2_1b.regs_out0 KS_uvaS2_1b_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_1b_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_1b.regs0 LibSegJu_uvaS2_1b.regs_out1).
Lemma KS_uvaS2_1b_1_ok : BG.kept_ok 60 LibSegJu_uvaS2_1b.regs0 LibSegJu_uvaS2_1b.regs_out1 KS_uvaS2_1b_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_1b_2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_1b.regs0 LibSegJu_uvaS2_1b.regs_out2).
Lemma KS_uvaS2_1b_2_ok : BG.kept_ok 60 LibSegJu_uvaS2_1b.regs0 LibSegJu_uvaS2_1b.regs_out2 KS_uvaS2_1b_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_1b_3 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_1b.regs0 LibSegJu_uvaS2_1b.regs_out3).
Lemma KS_uvaS2_1b_3_ok : BG.kept_ok 60 LibSegJu_uvaS2_1b.regs0 LibSegJu_uvaS2_1b.regs_out3 KS_uvaS2_1b_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_1b_4 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_1b.regs0 LibSegJu_uvaS2_1b.regs_out4).
Lemma KS_uvaS2_1b_4_ok : BG.kept_ok 60 LibSegJu_uvaS2_1b.regs0 LibSegJu_uvaS2_1b.regs_out4 KS_uvaS2_1b_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_1b_5 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_1b.regs0 LibSegJu_uvaS2_1b.regs_out5).
Lemma KS_uvaS2_1b_5_ok : BG.kept_ok 60 LibSegJu_uvaS2_1b.regs0 LibSegJu_uvaS2_1b.regs_out5 KS_uvaS2_1b_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_1b_6 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_1b.regs0 LibSegJu_uvaS2_1b.regs_out6).
Lemma KS_uvaS2_1b_6_ok : BG.kept_ok 60 LibSegJu_uvaS2_1b.regs0 LibSegJu_uvaS2_1b.regs_out6 KS_uvaS2_1b_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_1b_7 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_1b.regs0 LibSegJu_uvaS2_1b.regs_out7).
Lemma KS_uvaS2_1b_7_ok : BG.kept_ok 60 LibSegJu_uvaS2_1b.regs0 LibSegJu_uvaS2_1b.regs_out7 KS_uvaS2_1b_7 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_1b_8 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_1b.regs0 LibSegJu_uvaS2_1b.regs_out8).
Lemma KS_uvaS2_1b_8_ok : BG.kept_ok 60 LibSegJu_uvaS2_1b.regs0 LibSegJu_uvaS2_1b.regs_out8 KS_uvaS2_1b_8 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_1b_9 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_1b.regs0 LibSegJu_uvaS2_1b.regs_out9).
Lemma KS_uvaS2_1b_9_ok : BG.kept_ok 60 LibSegJu_uvaS2_1b.regs0 LibSegJu_uvaS2_1b.regs_out9 KS_uvaS2_1b_9 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_1b_10 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_1b.regs0 LibSegJu_uvaS2_1b.regs_out10).
Lemma KS_uvaS2_1b_10_ok : BG.kept_ok 60 LibSegJu_uvaS2_1b.regs0 LibSegJu_uvaS2_1b.regs_out10 KS_uvaS2_1b_10 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_1b_11 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_1b.regs0 LibSegJu_uvaS2_1b.regs_out11).
Lemma KS_uvaS2_1b_11_ok : BG.kept_ok 60 LibSegJu_uvaS2_1b.regs0 LibSegJu_uvaS2_1b.regs_out11 KS_uvaS2_1b_11 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_1b_12 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_1b.regs0 LibSegJu_uvaS2_1b.regs_out12).
Lemma KS_uvaS2_1b_12_ok : BG.kept_ok 60 LibSegJu_uvaS2_1b.regs0 LibSegJu_uvaS2_1b.regs_out12 KS_uvaS2_1b_12 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_1b_13 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_1b.regs0 LibSegJu_uvaS2_1b.regs_out13).
Lemma KS_uvaS2_1b_13_ok : BG.kept_ok 60 LibSegJu_uvaS2_1b.regs0 LibSegJu_uvaS2_1b.regs_out13 KS_uvaS2_1b_13 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_1b_14 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_1b.regs0 LibSegJu_uvaS2_1b.regs_out14).
Lemma KS_uvaS2_1b_14_ok : BG.kept_ok 60 LibSegJu_uvaS2_1b.regs0 LibSegJu_uvaS2_1b.regs_out14 KS_uvaS2_1b_14 = true. Proof. vm_compute. reflexivity. Qed.
Definition uvaS2_1b_conc_s := ",23A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v27p#2#40S,2_v2#60S,5#2S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<+v21v23S,=#8S,>-1S,?#1S,10-3>S,11#?5S,12#?4S,13#8?S,14#138<1S,15^#?#??????????><73>S,16#3S,18v24S,19#1S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#1v21#800000000000B#2v23#4000000B#1+v21v23#800000000000Na+v21#1v27B#v27#??B#v24#??,,?,6X#3798<#37:68Y,T,;#2T,17+v21#2T,1:+v21#1T,1;+v21#2,7X#3798<#37:68Y,1T,;#6T,17+v21#2T,1:+v21#1T,1;+v21#2C%_v24#?0p#2#40#1,6X#3798<#37:40Y,2T,17+v21#2T,1:+v21#1T,1;+v21#2C%_v24#?0p#2#40#1,8X#3798<#37:68Y,3T,;#6T,17+v21#2T,1:+v21#1T,1;+v21#2C%_v24#?4p#2#40#1D#1%_v24#?0p#2#40,7X#3798<#37:40Y,4T,17+v21#2T,1:+v21#1T,1;+v21#2C%_v24#?4p#2#40#1D#1%_v24#?0p#2#40,8X#3798<#37:68Y,5T,;#6T,17+v21#2T,1:+v21#1T,1;+v21#2D#1%_v24#?4p#2#40D#1%_v24#?0p#2#40,9X#3798<#37:40Y,6T,;#6T,17+v21#2T,1:+v21#1T,1;+v21#2Cv24#?5D#1%_v24#?4p#2#40D#1%_v24#?0p#2#40,9X#3798<#37:68Y,7T,;#6T,17+v21#2T,1:+v21#1T,1;+v21#2D#?5v24D#1%_v24#?4p#2#40D#1%_v24#?0p#2#40,7X#3798<#37:68Y,8T,;#6T,17+v21#2T,1:+v21#1T,1;+v21#2C%_v24#>0p#2#40#1,6X#3798<#37:40Y,9T,17+v21#2T,1:+v21#1T,1;+v21#2C%_v24#>0p#2#40#1,8X#3798<#37:68Y,:T,;#6T,17+v21#2T,1:+v21#1T,1;+v21#2C%_v24#>=p#2#40#1D#1%_v24#>0p#2#40,7X#3798<#37:40Y,;T,17+v21#2T,1:+v21#1T,1;+v21#2C%_v24#>=p#2#40#1D#1%_v24#>0p#2#40,8X#3798<#37:68Y,<T,;#6T,17+v21#2T,1:+v21#1T,1;+v21#2D#1%_v24#>=p#2#40D#1%_v24#>0p#2#40,9X#3798<#37:40Y,=T,;#6T,17+v21#2T,1:+v21#1T,1;+v21#2Cv24#?5D#1%_v24#>=p#2#40D#1%_v24#>0p#2#40,9X#3798<#37:68Y,>T,;#6T,17+v21#2T,1:+v21#1T,1;+v21#2D#?5v24D#1%_v24#>=p#2#40D#1%_v24#>0p#2#40"%pstring.
Lemma uvaS2_1b_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uvaS2_1b_0; KS_uvaS2_1b_1; KS_uvaS2_1b_2; KS_uvaS2_1b_3; KS_uvaS2_1b_4; KS_uvaS2_1b_5; KS_uvaS2_1b_6; KS_uvaS2_1b_7; KS_uvaS2_1b_8; KS_uvaS2_1b_9; KS_uvaS2_1b_10; KS_uvaS2_1b_11; KS_uvaS2_1b_12; KS_uvaS2_1b_13; KS_uvaS2_1b_14] fx R M V uvaS2_1b_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uvaS2_1b_0; KS_uvaS2_1b_1; KS_uvaS2_1b_2; KS_uvaS2_1b_3; KS_uvaS2_1b_4; KS_uvaS2_1b_5; KS_uvaS2_1b_6; KS_uvaS2_1b_7; KS_uvaS2_1b_8; KS_uvaS2_1b_9; KS_uvaS2_1b_10; KS_uvaS2_1b_11; KS_uvaS2_1b_12; KS_uvaS2_1b_13; KS_uvaS2_1b_14] LibSegJu_uvaS2_1b.regs0 LibSegJu_uvaS2_1b.kn0 LibSegJu_uvaS2_1b.BR LibSegJu_uvaS2_1b.PSS LibSegJu_uvaS2_1b.NX0 LibSegJu_uvaS2_1b.F0 227724 LibSegJu_uvaS2_1b.seg_sound_ax fx R M V uvaS2_1b_conc_s. Qed.
Definition KS_uvaS2_2a : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_2a.regs0 LibSegJu_uvaS2_2a.regs_out0).
Lemma KS_uvaS2_2a_ok : BG.kept_ok 60 LibSegJu_uvaS2_2a.regs0 LibSegJu_uvaS2_2a.regs_out0 KS_uvaS2_2a = true. Proof. vm_compute. reflexivity. Qed.
Definition uvaS2_2a_conc_s := ",20A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#2S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<+v21v23S,=#8S,>-1S,?#1S,10-3>S,11#?5S,12#?4S,13#8?S,14#138<1S,15^#?#??????????><73>S,16#3S,18v24S,19#2S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#1v21#800000000000B#1v23#2B#1+v21v23#800000000000B#v24#??,,1,3X#3798<#37:68Y,T,;#5"%pstring.
Lemma uvaS2_2a_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uvaS2_2a] fx R M V uvaS2_2a_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uvaS2_2a] LibSegJu_uvaS2_2a.regs0 LibSegJu_uvaS2_2a.kn0 LibSegJu_uvaS2_2a.BR LibSegJu_uvaS2_2a.PSS LibSegJu_uvaS2_2a.NX0 LibSegJu_uvaS2_2a.F0 227724 LibSegJu_uvaS2_2a.seg_sound_ax fx R M V uvaS2_2a_conc_s. Qed.
Definition KS_uvaS2_2b_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out0).
Lemma KS_uvaS2_2b_0_ok : BG.kept_ok 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out0 KS_uvaS2_2b_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_2b_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out1).
Lemma KS_uvaS2_2b_1_ok : BG.kept_ok 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out1 KS_uvaS2_2b_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_2b_2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out2).
Lemma KS_uvaS2_2b_2_ok : BG.kept_ok 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out2 KS_uvaS2_2b_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_2b_3 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out3).
Lemma KS_uvaS2_2b_3_ok : BG.kept_ok 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out3 KS_uvaS2_2b_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_2b_4 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out4).
Lemma KS_uvaS2_2b_4_ok : BG.kept_ok 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out4 KS_uvaS2_2b_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_2b_5 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out5).
Lemma KS_uvaS2_2b_5_ok : BG.kept_ok 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out5 KS_uvaS2_2b_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_2b_6 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out6).
Lemma KS_uvaS2_2b_6_ok : BG.kept_ok 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out6 KS_uvaS2_2b_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_2b_7 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out7).
Lemma KS_uvaS2_2b_7_ok : BG.kept_ok 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out7 KS_uvaS2_2b_7 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_2b_8 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out8).
Lemma KS_uvaS2_2b_8_ok : BG.kept_ok 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out8 KS_uvaS2_2b_8 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_2b_9 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out9).
Lemma KS_uvaS2_2b_9_ok : BG.kept_ok 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out9 KS_uvaS2_2b_9 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_2b_10 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out10).
Lemma KS_uvaS2_2b_10_ok : BG.kept_ok 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out10 KS_uvaS2_2b_10 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_2b_11 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out11).
Lemma KS_uvaS2_2b_11_ok : BG.kept_ok 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out11 KS_uvaS2_2b_11 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_2b_12 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out12).
Lemma KS_uvaS2_2b_12_ok : BG.kept_ok 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out12 KS_uvaS2_2b_12 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_2b_13 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out13).
Lemma KS_uvaS2_2b_13_ok : BG.kept_ok 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out13 KS_uvaS2_2b_13 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_2b_14 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out14).
Lemma KS_uvaS2_2b_14_ok : BG.kept_ok 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out14 KS_uvaS2_2b_14 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_2b_15 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out15).
Lemma KS_uvaS2_2b_15_ok : BG.kept_ok 60 LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.regs_out15 KS_uvaS2_2b_15 = true. Proof. vm_compute. reflexivity. Qed.
Definition uvaS2_2b_conc_s := ",26A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v27p#2#40A#v28p#2#40S,2_v2#60S,5#2S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<+v21v23S,=#8S,>-1S,?#1S,10-3>S,11#?5S,12#?4S,13#8?S,14#138<1S,15^#?#??????????><73>S,16#3S,18v24S,19#2S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#1v21#800000000000B#3v23#4000000B#1+v21v23#800000000000Na+v21#1v27B#v27#??Na+v21#2v28B#v28#??B#v24#??,,10,6X#3798<#37:68Y,T,;#2T,17+v21#3T,1:+v21#2T,1;+v21#3,6X#3798<#37:68Y,1T,;#2T,17+v21#3T,1:+v21#2T,1;+v21#2,7X#3798<#37:68Y,2T,;#6T,17+v21#3T,1:+v21#2T,1;+v21#2C%_v24#?0p#2#40#1,6X#3798<#37:40Y,3T,17+v21#3T,1:+v21#2T,1;+v21#2C%_v24#?0p#2#40#1,8X#3798<#37:68Y,4T,;#6T,17+v21#3T,1:+v21#2T,1;+v21#2C%_v24#?4p#2#40#1D#1%_v24#?0p#2#40,7X#3798<#37:40Y,5T,17+v21#3T,1:+v21#2T,1;+v21#2C%_v24#?4p#2#40#1D#1%_v24#?0p#2#40,8X#3798<#37:68Y,6T,;#6T,17+v21#3T,1:+v21#2T,1;+v21#2D#1%_v24#?4p#2#40D#1%_v24#?0p#2#40,9X#3798<#37:40Y,7T,;#6T,17+v21#3T,1:+v21#2T,1;+v21#2Cv24#?5D#1%_v24#?4p#2#40D#1%_v24#?0p#2#40,9X#3798<#37:68Y,8T,;#6T,17+v21#3T,1:+v21#2T,1;+v21#2D#?5v24D#1%_v24#?4p#2#40D#1%_v24#?0p#2#40,7X#3798<#37:68Y,9T,;#6T,17+v21#3T,1:+v21#2T,1;+v21#2C%_v24#>0p#2#40#1,6X#3798<#37:40Y,:T,17+v21#3T,1:+v21#2T,1;+v21#2C%_v24#>0p#2#40#1,8X#3798<#37:68Y,;T,;#6T,17+v21#3T,1:+v21#2T,1;+v21#2C%_v24#>=p#2#40#1D#1%_v24#>0p#2#40,7X#3798<#37:40Y,<T,17+v21#3T,1:+v21#2T,1;+v21#2C%_v24#>=p#2#40#1D#1%_v24#>0p#2#40,8X#3798<#37:68Y,=T,;#6T,17+v21#3T,1:+v21#2T,1;+v21#2D#1%_v24#>=p#2#40D#1%_v24#>0p#2#40,9X#3798<#37:40Y,>T,;#6T,17+v21#3T,1:+v21#2T,1;+v21#2Cv24#?5D#1%_v24#>=p#2#40D#1%_v24#>0p#2#40,9X#3798<#37:68Y,?T,;#6T,17+v21#3T,1:+v21#2T,1;+v21#2D#?5v24D#1%_v24#>=p#2#40D#1%_v24#>0p#2#40"%pstring.
Lemma uvaS2_2b_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uvaS2_2b_0; KS_uvaS2_2b_1; KS_uvaS2_2b_2; KS_uvaS2_2b_3; KS_uvaS2_2b_4; KS_uvaS2_2b_5; KS_uvaS2_2b_6; KS_uvaS2_2b_7; KS_uvaS2_2b_8; KS_uvaS2_2b_9; KS_uvaS2_2b_10; KS_uvaS2_2b_11; KS_uvaS2_2b_12; KS_uvaS2_2b_13; KS_uvaS2_2b_14; KS_uvaS2_2b_15] fx R M V uvaS2_2b_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uvaS2_2b_0; KS_uvaS2_2b_1; KS_uvaS2_2b_2; KS_uvaS2_2b_3; KS_uvaS2_2b_4; KS_uvaS2_2b_5; KS_uvaS2_2b_6; KS_uvaS2_2b_7; KS_uvaS2_2b_8; KS_uvaS2_2b_9; KS_uvaS2_2b_10; KS_uvaS2_2b_11; KS_uvaS2_2b_12; KS_uvaS2_2b_13; KS_uvaS2_2b_14; KS_uvaS2_2b_15] LibSegJu_uvaS2_2b.regs0 LibSegJu_uvaS2_2b.kn0 LibSegJu_uvaS2_2b.BR LibSegJu_uvaS2_2b.PSS LibSegJu_uvaS2_2b.NX0 LibSegJu_uvaS2_2b.F0 227724 LibSegJu_uvaS2_2b.seg_sound_ax fx R M V uvaS2_2b_conc_s. Qed.
Definition KS_uvaS2_3a : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_3a.regs0 LibSegJu_uvaS2_3a.regs_out0).
Lemma KS_uvaS2_3a_ok : BG.kept_ok 60 LibSegJu_uvaS2_3a.regs0 LibSegJu_uvaS2_3a.regs_out0 KS_uvaS2_3a = true. Proof. vm_compute. reflexivity. Qed.
Definition uvaS2_3a_conc_s := ",20A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#2S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<+v21v23S,=#8S,>-1S,?#1S,10-3>S,11#?5S,12#?4S,13#8?S,14#138<1S,15^#?#??????????><73>S,16#3S,18v24S,19#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#1v21#800000000000B#1v23#3B#1+v21v23#800000000000B#v24#??,,1,3X#3798<#37:68Y,T,;#5"%pstring.
Lemma uvaS2_3a_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uvaS2_3a] fx R M V uvaS2_3a_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uvaS2_3a] LibSegJu_uvaS2_3a.regs0 LibSegJu_uvaS2_3a.kn0 LibSegJu_uvaS2_3a.BR LibSegJu_uvaS2_3a.PSS LibSegJu_uvaS2_3a.NX0 LibSegJu_uvaS2_3a.F0 227724 LibSegJu_uvaS2_3a.seg_sound_ax fx R M V uvaS2_3a_conc_s. Qed.
Definition KS_uvaS2_3b_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out0).
Lemma KS_uvaS2_3b_0_ok : BG.kept_ok 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out0 KS_uvaS2_3b_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_3b_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out1).
Lemma KS_uvaS2_3b_1_ok : BG.kept_ok 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out1 KS_uvaS2_3b_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_3b_2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out2).
Lemma KS_uvaS2_3b_2_ok : BG.kept_ok 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out2 KS_uvaS2_3b_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_3b_3 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out3).
Lemma KS_uvaS2_3b_3_ok : BG.kept_ok 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out3 KS_uvaS2_3b_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_3b_4 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out4).
Lemma KS_uvaS2_3b_4_ok : BG.kept_ok 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out4 KS_uvaS2_3b_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_3b_5 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out5).
Lemma KS_uvaS2_3b_5_ok : BG.kept_ok 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out5 KS_uvaS2_3b_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_3b_6 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out6).
Lemma KS_uvaS2_3b_6_ok : BG.kept_ok 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out6 KS_uvaS2_3b_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_3b_7 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out7).
Lemma KS_uvaS2_3b_7_ok : BG.kept_ok 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out7 KS_uvaS2_3b_7 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_3b_8 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out8).
Lemma KS_uvaS2_3b_8_ok : BG.kept_ok 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out8 KS_uvaS2_3b_8 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_3b_9 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out9).
Lemma KS_uvaS2_3b_9_ok : BG.kept_ok 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out9 KS_uvaS2_3b_9 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_3b_10 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out10).
Lemma KS_uvaS2_3b_10_ok : BG.kept_ok 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out10 KS_uvaS2_3b_10 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_3b_11 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out11).
Lemma KS_uvaS2_3b_11_ok : BG.kept_ok 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out11 KS_uvaS2_3b_11 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_3b_12 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out12).
Lemma KS_uvaS2_3b_12_ok : BG.kept_ok 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out12 KS_uvaS2_3b_12 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_3b_13 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out13).
Lemma KS_uvaS2_3b_13_ok : BG.kept_ok 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out13 KS_uvaS2_3b_13 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_3b_14 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out14).
Lemma KS_uvaS2_3b_14_ok : BG.kept_ok 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out14 KS_uvaS2_3b_14 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_3b_15 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out15).
Lemma KS_uvaS2_3b_15_ok : BG.kept_ok 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out15 KS_uvaS2_3b_15 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_3b_16 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out16).
Lemma KS_uvaS2_3b_16_ok : BG.kept_ok 60 LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.regs_out16 KS_uvaS2_3b_16 = true. Proof. vm_compute. reflexivity. Qed.
Definition uvaS2_3b_conc_s := ",29A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40S,2_v2#60S,5#2S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<+v21v23S,=#8S,>-1S,?#1S,10-3>S,11#?5S,12#?4S,13#8?S,14#138<1S,15^#?#??????????><73>S,16#3S,18v24S,19#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#1v21#800000000000B#4v23#4000000B#1+v21v23#800000000000Na+v21#1v27B#v27#??Na+v21#2v28B#v28#??Na+v21#3v29B#v29#??B#v24#??,,11,6X#3798<#37:68Y,T,;#2T,17+v21#4T,1:+v21#3T,1;+v21#3,6X#3798<#37:68Y,1T,;#2T,17+v21#4T,1:+v21#3T,1;+v21#3,6X#3798<#37:68Y,2T,;#2T,17+v21#4T,1:+v21#3T,1;+v21#2,7X#3798<#37:68Y,3T,;#6T,17+v21#4T,1:+v21#3T,1;+v21#2C%_v24#?0p#2#40#1,6X#3798<#37:40Y,4T,17+v21#4T,1:+v21#3T,1;+v21#2C%_v24#?0p#2#40#1,8X#3798<#37:68Y,5T,;#6T,17+v21#4T,1:+v21#3T,1;+v21#2C%_v24#?4p#2#40#1D#1%_v24#?0p#2#40,7X#3798<#37:40Y,6T,17+v21#4T,1:+v21#3T,1;+v21#2C%_v24#?4p#2#40#1D#1%_v24#?0p#2#40,8X#3798<#37:68Y,7T,;#6T,17+v21#4T,1:+v21#3T,1;+v21#2D#1%_v24#?4p#2#40D#1%_v24#?0p#2#40,9X#3798<#37:40Y,8T,;#6T,17+v21#4T,1:+v21#3T,1;+v21#2Cv24#?5D#1%_v24#?4p#2#40D#1%_v24#?0p#2#40,9X#3798<#37:68Y,9T,;#6T,17+v21#4T,1:+v21#3T,1;+v21#2D#?5v24D#1%_v24#?4p#2#40D#1%_v24#?0p#2#40,7X#3798<#37:68Y,:T,;#6T,17+v21#4T,1:+v21#3T,1;+v21#2C%_v24#>0p#2#40#1,6X#3798<#37:40Y,;T,17+v21#4T,1:+v21#3T,1;+v21#2C%_v24#>0p#2#40#1,8X#3798<#37:68Y,<T,;#6T,17+v21#4T,1:+v21#3T,1;+v21#2C%_v24#>=p#2#40#1D#1%_v24#>0p#2#40,7X#3798<#37:40Y,=T,17+v21#4T,1:+v21#3T,1;+v21#2C%_v24#>=p#2#40#1D#1%_v24#>0p#2#40,8X#3798<#37:68Y,>T,;#6T,17+v21#4T,1:+v21#3T,1;+v21#2D#1%_v24#>=p#2#40D#1%_v24#>0p#2#40,9X#3798<#37:40Y,?T,;#6T,17+v21#4T,1:+v21#3T,1;+v21#2Cv24#?5D#1%_v24#>=p#2#40D#1%_v24#>0p#2#40,9X#3798<#37:68Y,10T,;#6T,17+v21#4T,1:+v21#3T,1;+v21#2D#?5v24D#1%_v24#>=p#2#40D#1%_v24#>0p#2#40"%pstring.
Lemma uvaS2_3b_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uvaS2_3b_0; KS_uvaS2_3b_1; KS_uvaS2_3b_2; KS_uvaS2_3b_3; KS_uvaS2_3b_4; KS_uvaS2_3b_5; KS_uvaS2_3b_6; KS_uvaS2_3b_7; KS_uvaS2_3b_8; KS_uvaS2_3b_9; KS_uvaS2_3b_10; KS_uvaS2_3b_11; KS_uvaS2_3b_12; KS_uvaS2_3b_13; KS_uvaS2_3b_14; KS_uvaS2_3b_15; KS_uvaS2_3b_16] fx R M V uvaS2_3b_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uvaS2_3b_0; KS_uvaS2_3b_1; KS_uvaS2_3b_2; KS_uvaS2_3b_3; KS_uvaS2_3b_4; KS_uvaS2_3b_5; KS_uvaS2_3b_6; KS_uvaS2_3b_7; KS_uvaS2_3b_8; KS_uvaS2_3b_9; KS_uvaS2_3b_10; KS_uvaS2_3b_11; KS_uvaS2_3b_12; KS_uvaS2_3b_13; KS_uvaS2_3b_14; KS_uvaS2_3b_15; KS_uvaS2_3b_16] LibSegJu_uvaS2_3b.regs0 LibSegJu_uvaS2_3b.kn0 LibSegJu_uvaS2_3b.BR LibSegJu_uvaS2_3b.PSS LibSegJu_uvaS2_3b.NX0 LibSegJu_uvaS2_3b.F0 227724 LibSegJu_uvaS2_3b.seg_sound_ax fx R M V uvaS2_3b_conc_s. Qed.
Definition KS_uvaS2_big_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_big.regs0 LibSegJu_uvaS2_big.regs_out0).
Lemma KS_uvaS2_big_0_ok : BG.kept_ok 60 LibSegJu_uvaS2_big.regs0 LibSegJu_uvaS2_big.regs_out0 KS_uvaS2_big_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaS2_big_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaS2_big.regs0 LibSegJu_uvaS2_big.regs_out1).
Lemma KS_uvaS2_big_1_ok : BG.kept_ok 60 LibSegJu_uvaS2_big.regs0 LibSegJu_uvaS2_big.regs_out1 KS_uvaS2_big_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition uvaS2_big_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v26p#2#40S,2_v2#60S,5#2S,6-41S,7#>?S,8#?0S,9#90S,:v21S,<+v21v23S,=#8S,>-1S,?#1S,10-3>S,11#?5S,12#?4S,13#8?S,14#138<1S,15^#?#??????????><73>S,16#3S,18v24S,19v26S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#1v21#800000000000B#1v23#4000000B#1+v21v23#800000000000B#4v26#??B#v24#??,,2,7X#3798<#37:68Y,T,;#1T,17++v21v26#1T,1:+v21v26T,1;++v21v26#1Cv26v23,4X#3798<#37:68Y,1T,;#5Dv23v26"%pstring.
Lemma uvaS2_big_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uvaS2_big_0; KS_uvaS2_big_1] fx R M V uvaS2_big_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uvaS2_big_0; KS_uvaS2_big_1] LibSegJu_uvaS2_big.regs0 LibSegJu_uvaS2_big.kn0 LibSegJu_uvaS2_big.BR LibSegJu_uvaS2_big.PSS LibSegJu_uvaS2_big.NX0 LibSegJu_uvaS2_big.F0 227724 LibSegJu_uvaS2_big.seg_sound_ax fx R M V uvaS2_big_conc_s. Qed.
Definition KS_uvaB_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaB.regs0 LibSegJu_uvaB.regs_out0).
Lemma KS_uvaB_0_ok : BG.kept_ok 60 LibSegJu_uvaB.regs0 LibSegJu_uvaB.regs_out0 KS_uvaB_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uvaB_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaB.regs0 LibSegJu_uvaB.regs_out1).
Lemma KS_uvaB_1_ok : BG.kept_ok 60 LibSegJu_uvaB.regs0 LibSegJu_uvaB.regs_out1 KS_uvaB_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition uvaB_conc_s := ",1>A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v25p#2#40S,2_v2#60S,5#2S,6-41S,7#>?S,8#?0S,9#90S,:v25S,<+v21v23S,=#8S,>-1S,?#1S,10-3>S,11#?5S,12#?4S,13#8?S,14#138<1S,15^#?#??????????><73>S,16#3S,17v21S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#1v21#800000000000B#v23#800000000000B#1+v21v23#800000000000,,2,5X#37:40#37:68Y,T,:+v21v23T,;#C%_v21%+v21v23p#2#40p#2#40#1,4X#37:40#378>4Y,1T,:v21D#1%_v21%+v21v23p#2#40p#2#40"%pstring.
Lemma uvaB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uvaB_0; KS_uvaB_1] fx R M V uvaB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uvaB_0; KS_uvaB_1] LibSegJu_uvaB.regs0 LibSegJu_uvaB.kn0 LibSegJu_uvaB.BR LibSegJu_uvaB.PSS LibSegJu_uvaB.NX0 LibSegJu_uvaB.F0 227904 LibSegJu_uvaB.seg_sound_ax fx R M V uvaB_conc_s. Qed.
Definition KS_uvaX : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uvaX.regs0 LibSegJu_uvaX.regs_out0).
Lemma KS_uvaX_ok : BG.kept_ok 60 LibSegJu_uvaX.regs0 LibSegJu_uvaX.regs_out0 KS_uvaX = true. Proof. vm_compute. reflexivity. Qed.
Definition uvaX_conc_s := ",1=A#v2p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40A#v34p#2#40A#v35p#2#40A#v36p#2#40A#v37p#2#40A#v38p#2#40S,2_v2#60B#7???7?800060v2#800000000000Hv2#10I_v2#60#60La_v2#8v2=La_v2#10v2>La_v2#18v2?La_v2#20v30La_v2#28v31La_v2#30v32La_v2#38v33La_v2#40v34La_v2#48v35La_v2#50v36La_v2#58v37La_v2#60v38,,1,?X#37:68#37:9<Y,T,2v2T,8v2=T,9v2>T,12v2?T,13v30T,14v31T,15v32T,16v33T,17v34T,18v35T,19v36T,1:v37T,1;v38"%pstring.
Lemma uvaX_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uvaX] fx R M V uvaX_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uvaX] LibSegJu_uvaX.regs0 LibSegJu_uvaX.kn0 LibSegJu_uvaX.BR LibSegJu_uvaX.PSS LibSegJu_uvaX.NX0 LibSegJu_uvaX.F0 227944 LibSegJu_uvaX.seg_sound_ax fx R M V uvaX_conc_s. Qed.
End PMVAUP.
