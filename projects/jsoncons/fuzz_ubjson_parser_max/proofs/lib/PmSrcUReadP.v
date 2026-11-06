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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJu_usrAlt LibSegJu_usrAge LibSegJu_usrBeq LibSegJu_usrBne LibSegJu_usrA0f LibSegJu_usrA0e LibSegJu_usrA0d LibSegJu_usrC0 LibSegJu_usrClt LibSegJu_usrCge LibSegJu_usrD LibSegJu_usrE1 LibSegJu_usrE2.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMUSRDP.
Module BG := BigLinkGlueUb0.BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcU.
Definition KS_usrAlt : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_usrAlt.regs0 LibSegJu_usrAlt.regs_out0).
Lemma KS_usrAlt_ok : BG.kept_ok 48 LibSegJu_usrAlt.regs0 LibSegJu_usrAlt.regs_out0 KS_usrAlt = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition usrAlt_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v26B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>=8Hv24#8P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120v21Ja+v24#100#8I+v24#100#28B#2v21#4000B#1v26#3???B#1_v21v26#3???B#1000v23#7???????<000,1_v2#30#30,1,?X#374;8#::1;4Y,T,1#37500T,2_v2#30T,8v24T,9v26T,:v25T,;v23T,12v26T,13v25Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma usrAlt_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_usrAlt] fx R M V usrAlt_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_usrAlt] LibSegJu_usrAlt.regs0 LibSegJu_usrAlt.kn0 LibSegJu_usrAlt.BR LibSegJu_usrAlt.PSS LibSegJu_usrAlt.NX0 LibSegJu_usrAlt.F0 226488 LibSegJu_usrAlt.seg_sound_ax fx R M V usrAlt_conc_s. Qed.
Definition KS_usrAge : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_usrAge.regs0 LibSegJu_usrAge.regs_out0).
Lemma KS_usrAge_ok : BG.kept_ok 48 LibSegJu_usrAge.regs0 LibSegJu_usrAge.regs_out0 KS_usrAge = true. Proof. vm_compute. reflexivity. Qed.
Definition usrAge_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v26B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>=8Hv24#8P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120v21Ja+v24#100#8I+v24#100#28B#1v21#4000B#1v26#4000B#+*-1v21v26#3???B#1000v23#7???????<000,1_v2#30#30,1,10X#374;8#::1;4Y,T,1#37500T,2_v2#30T,8v24T,9v21T,:v25T,;v23T,<v21T,12v26T,13v25Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma usrAge_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_usrAge] fx R M V usrAge_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_usrAge] LibSegJu_usrAge.regs0 LibSegJu_usrAge.kn0 LibSegJu_usrAge.BR LibSegJu_usrAge.PSS LibSegJu_usrAge.NX0 LibSegJu_usrAge.F0 226488 LibSegJu_usrAge.seg_sound_ax fx R M V usrAge_conc_s. Qed.
Definition KS_usrBeq : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_usrBeq.regs0 LibSegJu_usrBeq.regs_out0).
Lemma KS_usrBeq_ok : BG.kept_ok 48 LibSegJu_usrBeq.regs0 LibSegJu_usrBeq.regs_out0 KS_usrBeq = true. Proof. vm_compute. reflexivity. Qed.
Definition usrBeq_conc_s := ",26A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#30S,8v24S,9v27S,12v27S,13v25B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>=8Hv24#8P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120v21Ja+v24#100#8I+v24#100#28La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<B#1v21#4000B#1v27#4000B#_v21v27#3???B#1000v23#7???????<000,2_v2#30#30+v24#100#28,1,13X#37500#376;0Y,T,1v28T,2v2T,8v29T,9v2:T,:v27T,;_v21v27T,12v2;T,13v2<Lb+v24#120_v21v27Lb+v24#118+v23v27Lb+v24#108v22Lb+v24#110#4000Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;Lb_v2#28v2<"%pstring.
Lemma usrBeq_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_usrBeq] fx R M V usrBeq_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_usrBeq] LibSegJu_usrBeq.regs0 LibSegJu_usrBeq.kn0 LibSegJu_usrBeq.BR LibSegJu_usrBeq.PSS LibSegJu_usrBeq.NX0 LibSegJu_usrBeq.F0 226560 LibSegJu_usrBeq.seg_sound_ax fx R M V usrBeq_conc_s. Qed.
Definition KS_usrBne : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_usrBne.regs0 LibSegJu_usrBne.regs_out0).
Lemma KS_usrBne_ok : BG.kept_ok 48 LibSegJu_usrBne.regs0 LibSegJu_usrBne.regs_out0 KS_usrBne = true. Proof. vm_compute. reflexivity. Qed.
Definition usrBne_conc_s := ",26A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#30S,8v24S,9v27S,12v26S,13v25B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>=8Hv24#8P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120v27Ja+v24#100#8I+v24#100#28La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<B#1v27#3???B#2v26#4000B#1_v26v27#3???B#1000v23#7???????<000,2_v2#30#30+v24#100#28,1,10X#37500#37720Y,T,1#37564T,:v24T,;v22T,<#4000T,12_v26v27Lb+v24#118v22Lb+v24#120#Lb+v24#108v22Lb+v24#110#4000Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;Lb_v2#28v2<"%pstring.
Lemma usrBne_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_usrBne] fx R M V usrBne_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_usrBne] LibSegJu_usrBne.regs0 LibSegJu_usrBne.kn0 LibSegJu_usrBne.BR LibSegJu_usrBne.PSS LibSegJu_usrBne.NX0 LibSegJu_usrBne.F0 226560 LibSegJu_usrBne.seg_sound_ax fx R M V usrBne_conc_s. Qed.
Definition KS_usrA0f : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_usrA0f.regs0 LibSegJu_usrA0f.regs_out0).
Lemma KS_usrA0f_ok : BG.kept_ok 48 LibSegJu_usrA0f.regs0 LibSegJu_usrA0f.regs_out0 KS_usrA0f = true. Proof. vm_compute. reflexivity. Qed.
Definition usrA0f_conc_s := ",17A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v26B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>=8Hv24#8P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120#Ja+v24#100#8I+v24#100#28B#1v26#3???,2_v2#30#30+v24#100#28,1,14X#374;8#37720Y,T,1#37564T,2_v2#30T,8v24T,9#T,;v22T,<#4000T,12v26T,13v25Lb+v24#118v22Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1Lb+v24#108v22Lb+v24#110#4000Lb+v24#120#Jb+v24#100#8"%pstring.
Lemma usrA0f_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_usrA0f] fx R M V usrA0f_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_usrA0f] LibSegJu_usrA0f.regs0 LibSegJu_usrA0f.kn0 LibSegJu_usrA0f.BR LibSegJu_usrA0f.PSS LibSegJu_usrA0f.NX0 LibSegJu_usrA0f.F0 226488 LibSegJu_usrA0f.seg_sound_ax fx R M V usrA0f_conc_s. Qed.
Definition KS_usrA0e : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_usrA0e.regs0 LibSegJu_usrA0e.regs_out0).
Lemma KS_usrA0e_ok : BG.kept_ok 48 LibSegJu_usrA0e.regs0 LibSegJu_usrA0e.regs_out0 KS_usrA0e = true. Proof. vm_compute. reflexivity. Qed.
Definition usrA0e_conc_s := ",22A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v2=p#2#40S,2v2S,:v24S,;v25S,<#4000B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>=8Hv24#8P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120#Ja+v24#100#8I+v24#100#28B#7???7?800030v2=#7????????>?0Hv2=#8P_v2#30#30v2=#110O#10000#;7120Pv24#128v2=#110La+v24#?0v2=La+v24#?8+v2=#10Lav2=#;3:>8La+v2=#10#;39?8Ma+v2=#98#2Ma+v2=#9<#La+v2=#:0+v2=#10,2_v2#30#30+v24#100#28,1,>X#374;8#376;0Y,T,:#T,;#Lb+v24#120#Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1Lb+v24#108v22Lb+v24#110#4000Lb+v24#118v23Jb+v24#100#8"%pstring.
Lemma usrA0e_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_usrA0e] fx R M V usrA0e_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_usrA0e] LibSegJu_usrA0e.regs0 LibSegJu_usrA0e.kn0 LibSegJu_usrA0e.BR LibSegJu_usrA0e.PSS LibSegJu_usrA0e.NX0 LibSegJu_usrA0e.F0 226488 LibSegJu_usrA0e.seg_sound_ax fx R M V usrA0e_conc_s. Qed.
Definition KS_usrA0d : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_usrA0d.regs0 LibSegJu_usrA0d.regs_out0).
Lemma KS_usrA0d_ok : BG.kept_ok 48 LibSegJu_usrA0d.regs0 LibSegJu_usrA0d.regs_out0 KS_usrA0d = true. Proof. vm_compute. reflexivity. Qed.
Definition usrA0d_conc_s := ",23A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v2=p#2#40S,2v2S,:v24S,;v25S,<#4000B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>=8Hv24#8P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120#Ja+v24#100#8I+v24#100#28B#7???7?800030v2=#7????????>?0Hv2=#8P_v2#30#30v2=#110O#10000#;7120Pv24#128v2=#110La+v24#?0v2=La+v24#?8+v2=#10Lav2=#;3:>8La+v2=#10#;39?8Ma+v2=#98#Ma+v2=#9<#La+v2=#:0+v2=#10B#1000v25#800000000000,1_v2#30#30,1,?X#374;8#5<2:8Y,T,1#3763<T,2_v2#30T,8v24T,9#T,:+v2=#10T,=#5<2:8T,12#4000T,13v25Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma usrA0d_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_usrA0d] fx R M V usrA0d_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_usrA0d] LibSegJu_usrA0d.regs0 LibSegJu_usrA0d.kn0 LibSegJu_usrA0d.BR LibSegJu_usrA0d.PSS LibSegJu_usrA0d.NX0 LibSegJu_usrA0d.F0 226488 LibSegJu_usrA0d.seg_sound_ax fx R M V usrA0d_conc_s. Qed.
Definition KS_usrC0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_usrC0.regs0 LibSegJu_usrC0.regs_out0).
Lemma KS_usrC0_ok : BG.kept_ok 48 LibSegJu_usrC0.regs0 LibSegJu_usrC0.regs_out0 KS_usrC0 = true. Proof. vm_compute. reflexivity. Qed.
Definition usrC0_conc_s := ",22A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#30S,8v24S,9v27S,:#S,12v26S,13v25B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>=8Hv24#8P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v22La+v24#120#Ja+v24#100#8I+v24#100#28La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<,2_v2#30#30+v24#100#28,1,13X#37564#376;0Y,T,1v28T,2v2T,8v29T,9v2:T,:v27T,12v2;T,13v2<Lb+v24#120#Lb+v24#108v22Lb+v24#110#4000Lb+v24#118v22Jb+v24#100#8Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;Lb_v2#28v2<"%pstring.
Lemma usrC0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_usrC0] fx R M V usrC0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_usrC0] LibSegJu_usrC0.regs0 LibSegJu_usrC0.kn0 LibSegJu_usrC0.BR LibSegJu_usrC0.PSS LibSegJu_usrC0.NX0 LibSegJu_usrC0.F0 226660 LibSegJu_usrC0.seg_sound_ax fx R M V usrC0_conc_s. Qed.
Definition KS_usrClt : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_usrClt.regs0 LibSegJu_usrClt.regs_out0).
Lemma KS_usrClt_ok : BG.kept_ok 48 LibSegJu_usrClt.regs0 LibSegJu_usrClt.regs_out0 KS_usrClt = true. Proof. vm_compute. reflexivity. Qed.
Definition usrClt_conc_s := ",28A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#30S,8v24S,9v27S,:v21S,12v26S,13v25B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>=8Hv24#8P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v22La+v24#120#Ja+v24#100#8I+v24#100#28La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<B#2v21#4000B#1v26#3???B#1_v21v26#3???B#v27#3???B#1000v25#800000000000,2_v2#30#30+v24#100#28,1,10X#37564#::1;4Y,T,1#37598T,:+v25v27T,;v22T,<v26Lb+v24#120v21Lb+v24#108v22Lb+v24#110#4000Lb+v24#118v22Jb+v24#100#8Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;Lb_v2#28v2<"%pstring.
Lemma usrClt_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_usrClt] fx R M V usrClt_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_usrClt] LibSegJu_usrClt.regs0 LibSegJu_usrClt.kn0 LibSegJu_usrClt.BR LibSegJu_usrClt.PSS LibSegJu_usrClt.NX0 LibSegJu_usrClt.F0 226660 LibSegJu_usrClt.seg_sound_ax fx R M V usrClt_conc_s. Qed.
Definition KS_usrCge : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_usrCge.regs0 LibSegJu_usrCge.regs_out0).
Lemma KS_usrCge_ok : BG.kept_ok 48 LibSegJu_usrCge.regs0 LibSegJu_usrCge.regs_out0 KS_usrCge = true. Proof. vm_compute. reflexivity. Qed.
Definition usrCge_conc_s := ",28A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#30S,8v24S,9v27S,:v21S,12v26S,13v25B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>=8Hv24#8P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v22La+v24#120#Ja+v24#100#8I+v24#100#28La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<B#1v21#3???B#1v26#3???B#+*-1v21v26#3???B#v27#3???B#1000v25#800000000000,2_v2#30#30+v24#100#28,1,11X#37564#::1;4Y,T,1#37598T,:+v25v27T,;v22T,<v21T,12v21Lb+v24#120v21Lb+v24#108v22Lb+v24#110#4000Lb+v24#118v22Jb+v24#100#8Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;Lb_v2#28v2<"%pstring.
Lemma usrCge_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_usrCge] fx R M V usrCge_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_usrCge] LibSegJu_usrCge.regs0 LibSegJu_usrCge.kn0 LibSegJu_usrCge.BR LibSegJu_usrCge.PSS LibSegJu_usrCge.NX0 LibSegJu_usrCge.F0 226660 LibSegJu_usrCge.seg_sound_ax fx R M V usrCge_conc_s. Qed.
Definition KS_usrD : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_usrD.regs0 LibSegJu_usrD.regs_out0).
Lemma KS_usrD_ok : BG.kept_ok 48 LibSegJu_usrD.regs0 LibSegJu_usrD.regs_out0 KS_usrD = true. Proof. vm_compute. reflexivity. Qed.
Definition usrD_conc_s := ",28A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#30S,8v24S,9v27S,12v26S,13v25B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>=8Hv24#8P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120v21Ja+v24#100#8I+v24#100#28La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<B#1v21#4000B#1v26#3???B#_v21v26#3???B#v27#3???B#1000v23#7???????<000,2_v2#30#30+v24#100#28,1,13X#37598#376;0Y,T,1v28T,2v2T,8v29T,9v2:T,:+v26v27T,;_v21v26T,12v2;T,13v2<Lb+v24#120_v21v26Lb+v24#118+v23v26Lb+v24#108v22Lb+v24#110#4000Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;Lb_v2#28v2<"%pstring.
Lemma usrD_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_usrD] fx R M V usrD_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_usrD] LibSegJu_usrD.regs0 LibSegJu_usrD.kn0 LibSegJu_usrD.BR LibSegJu_usrD.PSS LibSegJu_usrD.NX0 LibSegJu_usrD.F0 226712 LibSegJu_usrD.seg_sound_ax fx R M V usrD_conc_s. Qed.
Definition KS_usrE1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_usrE1.regs0 LibSegJu_usrE1.regs_out0).
Lemma KS_usrE1_ok : BG.kept_ok 48 LibSegJu_usrE1.regs0 LibSegJu_usrE1.regs_out0 KS_usrE1 = true. Proof. vm_compute. reflexivity. Qed.
Definition usrE1_conc_s := ",2>A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#30S,8v24S,9#S,:#4000S,12#4000S,13v25B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>=8Hv24#8P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120#Ja+v24#100#8I+v24#100#28B#7???7?800030v2=#7????????>?0Hv2=#8P_v2#30#30v2=#110O#10000#;7120Pv24#128v2=#110La+v24#?0v2=La+v24#?8+v2=#10Lav2=#;3:>8La+v2=#10#;39?8Ma+v2=#98#Ma+v2=#9<#La+v2=#:0+v2=#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<,2_v2#30#30+v24#100#28,1,11X#3763<#376;0Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;T,13v2<Lb+v24#108v22Lb+v24#110#4000Lb+v24#118v23Lb+v24#120#Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;Lb_v2#28v2<"%pstring.
Lemma usrE1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_usrE1] fx R M V usrE1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_usrE1] LibSegJu_usrE1.regs0 LibSegJu_usrE1.kn0 LibSegJu_usrE1.BR LibSegJu_usrE1.PSS LibSegJu_usrE1.NX0 LibSegJu_usrE1.F0 226876 LibSegJu_usrE1.seg_sound_ax fx R M V usrE1_conc_s. Qed.
Definition KS_usrE2 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_usrE2.regs0 LibSegJu_usrE2.regs_out0).
Lemma KS_usrE2_ok : BG.kept_ok 48 LibSegJu_usrE2.regs0 LibSegJu_usrE2.regs_out0 KS_usrE2 = true. Proof. vm_compute. reflexivity. Qed.
Definition usrE2_conc_s := ",31A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#30S,8v24S,9#S,:v21S,12#4000S,13v25B#7???7?800030v2#800000000000Hv2#10I_v2#30#30B#7???7?800030v24#7????????>=8Hv24#8P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120#Ja+v24#100#8I+v24#100#28B#7???7?800030v2=#7????????>?0Hv2=#8P_v2#30#30v2=#110O#10000#;7120Pv24#128v2=#110La+v24#?0v2=La+v24#?8+v2=#10Lav2=#;3:>8La+v2=#10#;39?8Ma+v2=#98#Ma+v2=#9<#La+v2=#:0+v2=#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<B#v21#3???I+v2=#98#4,3_v2#30#30+v24#100#28+v2=#98#4,1,15X#3763<#376;0Y,T,1v28T,2v2T,8v29T,9v2:T,;#2T,<#T,=#T,12v2;T,13v2<Mb+v2=#98#2Lb+v24#108v22Lb+v24#110#4000Lb+v24#118v23Lb+v24#120#Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;Lb_v2#28v2<"%pstring.
Lemma usrE2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_usrE2] fx R M V usrE2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_usrE2] LibSegJu_usrE2.regs0 LibSegJu_usrE2.kn0 LibSegJu_usrE2.BR LibSegJu_usrE2.PSS LibSegJu_usrE2.NX0 LibSegJu_usrE2.F0 226876 LibSegJu_usrE2.seg_sound_ax fx R M V usrE2_conc_s. Qed.
End PMUSRDP.
