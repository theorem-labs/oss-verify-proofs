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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_srAlt LibSegJs_srAge LibSegJs_srBeq LibSegJs_srBne LibSegJs_srA0f LibSegJs_srA0e LibSegJs_srA0d LibSegJs_srC0 LibSegJs_srClt LibSegJs_srCge LibSegJs_srD LibSegJs_srE1 LibSegJs_srE2.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMSRDP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_srAlt : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_srAlt.regs0 LibSegJs_srAlt.regs_out0).
Lemma KS_srAlt_ok : BG.kept_ok 48 LibSegJs_srAlt.regs0 LibSegJs_srAlt.regs_out0 KS_srAlt = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition srAlt_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v26B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>=8Hv24#8P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120v21Ja+v24#100#8I+v24#100#28B#2v21#4000B#1v26#3???B#1_v21v26#3???B#1000v23#7???????<000,1_v2#30#30,1,?X#36830#:9160Y,T,1#36878T,2_v2#30T,8v24T,9v26T,:v25T,;v23T,12v25T,13v26Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma srAlt_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_srAlt] fx R M V srAlt_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_srAlt] LibSegJs_srAlt.regs0 LibSegJs_srAlt.kn0 LibSegJs_srAlt.BR LibSegJs_srAlt.PSS LibSegJs_srAlt.NX0 LibSegJs_srAlt.F0 223280 LibSegJs_srAlt.seg_sound_ax fx R M V srAlt_conc_s. Qed.
Definition KS_srAge : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_srAge.regs0 LibSegJs_srAge.regs_out0).
Lemma KS_srAge_ok : BG.kept_ok 48 LibSegJs_srAge.regs0 LibSegJs_srAge.regs_out0 KS_srAge = true. Proof. vm_compute. reflexivity. Qed.
Definition srAge_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v26B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>=8Hv24#8P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120v21Ja+v24#100#8I+v24#100#28B#1v21#4000B#1v26#4000B#+*-1v21v26#3???B#1000v23#7???????<000,1_v2#30#30,1,10X#36830#:9160Y,T,1#36878T,2_v2#30T,8v24T,9v21T,:v25T,;v23T,<v21T,12v25T,13v26Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma srAge_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_srAge] fx R M V srAge_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_srAge] LibSegJs_srAge.regs0 LibSegJs_srAge.kn0 LibSegJs_srAge.BR LibSegJs_srAge.PSS LibSegJs_srAge.NX0 LibSegJs_srAge.F0 223280 LibSegJs_srAge.seg_sound_ax fx R M V srAge_conc_s. Qed.
Definition KS_srBeq : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_srBeq.regs0 LibSegJs_srBeq.regs_out0).
Lemma KS_srBeq_ok : BG.kept_ok 48 LibSegJs_srBeq.regs0 LibSegJs_srBeq.regs_out0 KS_srBeq = true. Proof. vm_compute. reflexivity. Qed.
Definition srBeq_conc_s := ",26A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#30S,8v24S,9v27S,12v25S,13v27B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>=8Hv24#8P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120v21Ja+v24#100#8I+v24#100#28La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<B#1v21#4000B#1v27#4000B#_v21v27#3???B#1000v23#7???????<000,2_v2#30#30+v24#100#28,1,13X#36878#369:<Y,T,1v28T,2v2T,8v29T,9v2:T,:v27T,;_v21v27T,12v2;T,13v2<Lb+v24#120_v21v27Lb+v24#118+v23v27Lb+v24#108v22Lb+v24#110#4000Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;Lb_v2#28v2<"%pstring.
Lemma srBeq_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_srBeq] fx R M V srBeq_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_srBeq] LibSegJs_srBeq.regs0 LibSegJs_srBeq.kn0 LibSegJs_srBeq.BR LibSegJs_srBeq.PSS LibSegJs_srBeq.NX0 LibSegJs_srBeq.F0 223352 LibSegJs_srBeq.seg_sound_ax fx R M V srBeq_conc_s. Qed.
Definition KS_srBne : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_srBne.regs0 LibSegJs_srBne.regs_out0).
Lemma KS_srBne_ok : BG.kept_ok 48 LibSegJs_srBne.regs0 LibSegJs_srBne.regs_out0 KS_srBne = true. Proof. vm_compute. reflexivity. Qed.
Definition srBne_conc_s := ",26A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#30S,8v24S,9v27S,12v25S,13v26B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>=8Hv24#8P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120v27Ja+v24#100#8I+v24#100#28La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<B#1v27#3???B#2v26#4000B#1_v26v27#3???B#1000v23#7???????<000,2_v2#30#30+v24#100#28,1,10X#36878#36:08Y,T,1#368<8T,:v24T,;v22T,<#4000T,13_v26v27Lb+v24#118v22Lb+v24#120#Lb+v24#108v22Lb+v24#110#4000Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;Lb_v2#28v2<"%pstring.
Lemma srBne_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_srBne] fx R M V srBne_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_srBne] LibSegJs_srBne.regs0 LibSegJs_srBne.kn0 LibSegJs_srBne.BR LibSegJs_srBne.PSS LibSegJs_srBne.NX0 LibSegJs_srBne.F0 223352 LibSegJs_srBne.seg_sound_ax fx R M V srBne_conc_s. Qed.
Definition KS_srA0f : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_srA0f.regs0 LibSegJs_srA0f.regs_out0).
Lemma KS_srA0f_ok : BG.kept_ok 48 LibSegJs_srA0f.regs0 LibSegJs_srA0f.regs_out0 KS_srA0f = true. Proof. vm_compute. reflexivity. Qed.
Definition srA0f_conc_s := ",17A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v26B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>=8Hv24#8P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120#Ja+v24#100#8I+v24#100#28B#1v26#3???,2_v2#30#30+v24#100#28,1,14X#36830#36:08Y,T,1#368<8T,2_v2#30T,8v24T,9#T,;v22T,<#4000T,12v25T,13v26Lb+v24#118v22Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1Lb+v24#108v22Lb+v24#110#4000Lb+v24#120#Jb+v24#100#8"%pstring.
Lemma srA0f_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_srA0f] fx R M V srA0f_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_srA0f] LibSegJs_srA0f.regs0 LibSegJs_srA0f.kn0 LibSegJs_srA0f.BR LibSegJs_srA0f.PSS LibSegJs_srA0f.NX0 LibSegJs_srA0f.F0 223280 LibSegJs_srA0f.seg_sound_ax fx R M V srA0f_conc_s. Qed.
Definition KS_srA0e : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_srA0e.regs0 LibSegJs_srA0e.regs_out0).
Lemma KS_srA0e_ok : BG.kept_ok 48 LibSegJs_srA0e.regs0 LibSegJs_srA0e.regs_out0 KS_srA0e = true. Proof. vm_compute. reflexivity. Qed.
Definition srA0e_conc_s := ",22A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v2=p#2#40S,2v2S,:v24S,;v25S,<#4000B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>=8Hv24#8P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120#Ja+v24#100#8I+v24#100#28B#7???7?800030v2=#7????????>?0Hv2=#8P_v2#30#30v2=#110O#10000#;60=0Pv24#128v2=#110La+v24#?0v2=La+v24#?8+v2=#10Lav2=#;2:98La+v2=#10#;29:8Ma+v2=#98#2Ma+v2=#9<#La+v2=#:0+v2=#10,2_v2#30#30+v24#100#28,1,>X#36830#369:<Y,T,:#T,;#78Lb+v24#120#Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1Lb+v24#108v22Lb+v24#110#4000Lb+v24#118v23Jb+v24#100#8"%pstring.
Lemma srA0e_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_srA0e] fx R M V srA0e_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_srA0e] LibSegJs_srA0e.regs0 LibSegJs_srA0e.kn0 LibSegJs_srA0e.BR LibSegJs_srA0e.PSS LibSegJs_srA0e.NX0 LibSegJs_srA0e.F0 223280 LibSegJs_srA0e.seg_sound_ax fx R M V srA0e_conc_s. Qed.
Definition KS_srA0d : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_srA0d.regs0 LibSegJs_srA0d.regs_out0).
Lemma KS_srA0d_ok : BG.kept_ok 48 LibSegJs_srA0d.regs0 LibSegJs_srA0d.regs_out0 KS_srA0d = true. Proof. vm_compute. reflexivity. Qed.
Definition srA0d_conc_s := ",22A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v2=p#2#40S,2v2S,:v24S,;v25S,<#4000B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>=8Hv24#8P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120#Ja+v24#100#8I+v24#100#28B#7???7?800030v2=#7????????>?0Hv2=#8P_v2#30#30v2=#110O#10000#;60=0Pv24#128v2=#110La+v24#?0v2=La+v24#?8+v2=#10Lav2=#;2:98La+v2=#10#;29:8Ma+v2=#98#Ma+v2=#9<#La+v2=#:0+v2=#10,1_v2#30#30,1,?X#36830#5;254Y,T,1#36948T,2_v2#30T,8v24T,9#T,:+v2=#10T,=#5;254T,12v25T,13#4000Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma srA0d_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_srA0d] fx R M V srA0d_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_srA0d] LibSegJs_srA0d.regs0 LibSegJs_srA0d.kn0 LibSegJs_srA0d.BR LibSegJs_srA0d.PSS LibSegJs_srA0d.NX0 LibSegJs_srA0d.F0 223280 LibSegJs_srA0d.seg_sound_ax fx R M V srA0d_conc_s. Qed.
Definition KS_srC0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_srC0.regs0 LibSegJs_srC0.regs_out0).
Lemma KS_srC0_ok : BG.kept_ok 48 LibSegJs_srC0.regs0 LibSegJs_srC0.regs_out0 KS_srC0 = true. Proof. vm_compute. reflexivity. Qed.
Definition srC0_conc_s := ",22A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#30S,8v24S,9v27S,:#S,12v25S,13v26B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>=8Hv24#8P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v22La+v24#120#Ja+v24#100#8I+v24#100#28La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<,2_v2#30#30+v24#100#28,1,13X#368<8#369:<Y,T,1v28T,2v2T,8v29T,9v2:T,:v27T,12v2;T,13v2<Lb+v24#120#Lb+v24#108v22Lb+v24#110#4000Lb+v24#118v22Jb+v24#100#8Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;Lb_v2#28v2<"%pstring.
Lemma srC0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_srC0] fx R M V srC0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_srC0] LibSegJs_srC0.regs0 LibSegJs_srC0.kn0 LibSegJs_srC0.BR LibSegJs_srC0.PSS LibSegJs_srC0.NX0 LibSegJs_srC0.F0 223432 LibSegJs_srC0.seg_sound_ax fx R M V srC0_conc_s. Qed.
Definition KS_srClt : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_srClt.regs0 LibSegJs_srClt.regs_out0).
Lemma KS_srClt_ok : BG.kept_ok 48 LibSegJs_srClt.regs0 LibSegJs_srClt.regs_out0 KS_srClt = true. Proof. vm_compute. reflexivity. Qed.
Definition srClt_conc_s := ",28A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#30S,8v24S,9v27S,:v21S,12v25S,13v26B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>=8Hv24#8P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v22La+v24#120#Ja+v24#100#8I+v24#100#28La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<B#2v21#4000B#1v26#3???B#1_v21v26#3???B#v27#3???B#v25#800000000000,2_v2#30#30+v24#100#28,1,10X#368<8#:9160Y,T,1#368>8T,:+v25v27T,;v22T,<v26Lb+v24#120v21Lb+v24#108v22Lb+v24#110#4000Lb+v24#118v22Jb+v24#100#8Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;Lb_v2#28v2<"%pstring.
Lemma srClt_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_srClt] fx R M V srClt_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_srClt] LibSegJs_srClt.regs0 LibSegJs_srClt.kn0 LibSegJs_srClt.BR LibSegJs_srClt.PSS LibSegJs_srClt.NX0 LibSegJs_srClt.F0 223432 LibSegJs_srClt.seg_sound_ax fx R M V srClt_conc_s. Qed.
Definition KS_srCge : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_srCge.regs0 LibSegJs_srCge.regs_out0).
Lemma KS_srCge_ok : BG.kept_ok 48 LibSegJs_srCge.regs0 LibSegJs_srCge.regs_out0 KS_srCge = true. Proof. vm_compute. reflexivity. Qed.
Definition srCge_conc_s := ",28A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#30S,8v24S,9v27S,:v21S,12v25S,13v26B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>=8Hv24#8P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v22La+v24#120#Ja+v24#100#8I+v24#100#28La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<B#1v21#3???B#1v26#3???B#+*-1v21v26#3???B#v27#3???B#v25#800000000000,2_v2#30#30+v24#100#28,1,11X#368<8#:9160Y,T,1#368>8T,:+v25v27T,;v22T,<v21T,13v21Lb+v24#120v21Lb+v24#108v22Lb+v24#110#4000Lb+v24#118v22Jb+v24#100#8Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;Lb_v2#28v2<"%pstring.
Lemma srCge_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_srCge] fx R M V srCge_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_srCge] LibSegJs_srCge.regs0 LibSegJs_srCge.kn0 LibSegJs_srCge.BR LibSegJs_srCge.PSS LibSegJs_srCge.NX0 LibSegJs_srCge.F0 223432 LibSegJs_srCge.seg_sound_ax fx R M V srCge_conc_s. Qed.
Definition KS_srD : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_srD.regs0 LibSegJs_srD.regs_out0).
Lemma KS_srD_ok : BG.kept_ok 48 LibSegJs_srD.regs0 LibSegJs_srD.regs_out0 KS_srD = true. Proof. vm_compute. reflexivity. Qed.
Definition srD_conc_s := ",28A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#30S,8v24S,9v27S,12v25S,13v26B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>=8Hv24#8P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120v21Ja+v24#100#8I+v24#100#28La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<B#1v21#4000B#1v26#3???B#_v21v26#3???B#v27#3???B#1000v23#7???????<000,2_v2#30#30+v24#100#28,1,13X#368>8#369:<Y,T,1v28T,2v2T,8v29T,9v2:T,:+v26v27T,;_v21v26T,12v2;T,13v2<Lb+v24#120_v21v26Lb+v24#118+v23v26Lb+v24#108v22Lb+v24#110#4000Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;Lb_v2#28v2<"%pstring.
Lemma srD_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_srD] fx R M V srD_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_srD] LibSegJs_srD.regs0 LibSegJs_srD.kn0 LibSegJs_srD.BR LibSegJs_srD.PSS LibSegJs_srD.NX0 LibSegJs_srD.F0 223464 LibSegJs_srD.seg_sound_ax fx R M V srD_conc_s. Qed.
Definition KS_srE1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_srE1.regs0 LibSegJs_srE1.regs_out0).
Lemma KS_srE1_ok : BG.kept_ok 48 LibSegJs_srE1.regs0 LibSegJs_srE1.regs_out0 KS_srE1 = true. Proof. vm_compute. reflexivity. Qed.
Definition srE1_conc_s := ",2>A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#30S,8v24S,9#S,:#4000S,12v25S,13#4000B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>=8Hv24#8P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120#Ja+v24#100#8I+v24#100#28B#7???7?800030v2=#7????????>?0Hv2=#8P_v2#30#30v2=#110O#10000#;60=0Pv24#128v2=#110La+v24#?0v2=La+v24#?8+v2=#10Lav2=#;2:98La+v2=#10#;29:8Ma+v2=#98#Ma+v2=#9<#La+v2=#:0+v2=#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<,2_v2#30#30+v24#100#28,1,11X#36948#369:<Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;T,13v2<Lb+v24#108v22Lb+v24#110#4000Lb+v24#118v23Lb+v24#120#Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;Lb_v2#28v2<"%pstring.
Lemma srE1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_srE1] fx R M V srE1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_srE1] LibSegJs_srE1.regs0 LibSegJs_srE1.kn0 LibSegJs_srE1.BR LibSegJs_srE1.PSS LibSegJs_srE1.NX0 LibSegJs_srE1.F0 223560 LibSegJs_srE1.seg_sound_ax fx R M V srE1_conc_s. Qed.
Definition KS_srE2 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_srE2.regs0 LibSegJs_srE2.regs_out0).
Lemma KS_srE2_ok : BG.kept_ok 48 LibSegJs_srE2.regs0 LibSegJs_srE2.regs_out0 KS_srE2 = true. Proof. vm_compute. reflexivity. Qed.
Definition srE2_conc_s := ",31A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#30S,8v24S,9#S,:v21S,12v25S,13#4000B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>=8Hv24#8P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120#Ja+v24#100#8I+v24#100#28B#7???7?800030v2=#7????????>?0Hv2=#8P_v2#30#30v2=#110O#10000#;60=0Pv24#128v2=#110La+v24#?0v2=La+v24#?8+v2=#10Lav2=#;2:98La+v2=#10#;29:8Ma+v2=#98#Ma+v2=#9<#La+v2=#:0+v2=#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<B#v21#3???I+v2=#98#4,3_v2#30#30+v24#100#28+v2=#98#4,1,15X#36948#369:<Y,T,1v28T,2v2T,8v29T,9v2:T,;#2T,<#T,=#T,12v2;T,13v2<Mb+v2=#98#2Lb+v24#108v22Lb+v24#110#4000Lb+v24#118v23Lb+v24#120#Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;Lb_v2#28v2<"%pstring.
Lemma srE2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_srE2] fx R M V srE2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_srE2] LibSegJs_srE2.regs0 LibSegJs_srE2.kn0 LibSegJs_srE2.BR LibSegJs_srE2.PSS LibSegJs_srE2.NX0 LibSegJs_srE2.F0 223560 LibSegJs_srE2.seg_sound_ax fx R M V srE2_conc_s. Qed.
End PMSRDP.
