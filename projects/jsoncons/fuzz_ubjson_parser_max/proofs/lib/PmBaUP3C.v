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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJu_ubaCs0 LibSegJu_ubaCs1 LibSegJu_ubaCs2 LibSegJu_ubaCs3 LibSegJu_ubaCs4 LibSegJu_ubaCs5 LibSegJu_ubaCs6 LibSegJu_ubaCs7 LibSegJu_ubaCs8 LibSegJu_ubaCs9 LibSegJu_ubaCs10.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBAUP3C.
Module BG := BigLinkGlueUb0.BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcU.
Definition KS_ubaCs0 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaCs0.regs0 LibSegJu_ubaCs0.regs_out0).
Lemma KS_ubaCs0_ok : BG.kept_ok 64 LibSegJu_ubaCs0.regs0 LibSegJu_ubaCs0.regs_out0 KS_ubaCs0 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition ubaCs0_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#20La+v24#178+v22#20B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#:0#40_v2#60#28,1,14X#37?;<#:?0><Y,T,1#363><T,2_v2#:0T,8#2T,9#1T,:#40T,;#2T,<#1T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#38194"%pstring.
Lemma ubaCs0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaCs0] fx R M V ubaCs0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaCs0] LibSegJu_ubaCs0.regs0 LibSegJu_ubaCs0.kn0 LibSegJu_ubaCs0.BR LibSegJu_ubaCs0.PSS LibSegJu_ubaCs0.NX0 LibSegJu_ubaCs0.F0 229308 LibSegJu_ubaCs0.seg_sound_ax fx R M V ubaCs0_conc_s. Qed.
Definition KS_ubaCs1 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaCs1.regs0 LibSegJu_ubaCs1.regs_out0).
Lemma KS_ubaCs1_ok : BG.kept_ok 64 LibSegJu_ubaCs1.regs0 LibSegJu_ubaCs1.regs_out0 KS_ubaCs1 = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaCs1_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#40La+v24#178+v22#40B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#:0#40_v2#60#28,1,14X#37?;<#:?0><Y,T,1#363><T,2_v2#:0T,8#4T,9#2T,:#80T,;#4T,<#2T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#38194"%pstring.
Lemma ubaCs1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaCs1] fx R M V ubaCs1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaCs1] LibSegJu_ubaCs1.regs0 LibSegJu_ubaCs1.kn0 LibSegJu_ubaCs1.BR LibSegJu_ubaCs1.PSS LibSegJu_ubaCs1.NX0 LibSegJu_ubaCs1.F0 229308 LibSegJu_ubaCs1.seg_sound_ax fx R M V ubaCs1_conc_s. Qed.
Definition KS_ubaCs2 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaCs2.regs0 LibSegJu_ubaCs2.regs_out0).
Lemma KS_ubaCs2_ok : BG.kept_ok 64 LibSegJu_ubaCs2.regs0 LibSegJu_ubaCs2.regs_out0 KS_ubaCs2 = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaCs2_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#80La+v24#178+v22#80B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#:0#40_v2#60#28,1,14X#37?;<#:?0><Y,T,1#363><T,2_v2#:0T,8#8T,9#4T,:#100T,;#8T,<#4T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#38194"%pstring.
Lemma ubaCs2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaCs2] fx R M V ubaCs2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaCs2] LibSegJu_ubaCs2.regs0 LibSegJu_ubaCs2.kn0 LibSegJu_ubaCs2.BR LibSegJu_ubaCs2.PSS LibSegJu_ubaCs2.NX0 LibSegJu_ubaCs2.F0 229308 LibSegJu_ubaCs2.seg_sound_ax fx R M V ubaCs2_conc_s. Qed.
Definition KS_ubaCs3 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaCs3.regs0 LibSegJu_ubaCs3.regs_out0).
Lemma KS_ubaCs3_ok : BG.kept_ok 64 LibSegJu_ubaCs3.regs0 LibSegJu_ubaCs3.regs_out0 KS_ubaCs3 = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaCs3_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#100La+v24#178+v22#100B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#:0#40_v2#60#28,1,14X#37?;<#:?0><Y,T,1#363><T,2_v2#:0T,8#10T,9#8T,:#200T,;#10T,<#8T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#38194"%pstring.
Lemma ubaCs3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaCs3] fx R M V ubaCs3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaCs3] LibSegJu_ubaCs3.regs0 LibSegJu_ubaCs3.kn0 LibSegJu_ubaCs3.BR LibSegJu_ubaCs3.PSS LibSegJu_ubaCs3.NX0 LibSegJu_ubaCs3.F0 229308 LibSegJu_ubaCs3.seg_sound_ax fx R M V ubaCs3_conc_s. Qed.
Definition KS_ubaCs4 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaCs4.regs0 LibSegJu_ubaCs4.regs_out0).
Lemma KS_ubaCs4_ok : BG.kept_ok 64 LibSegJu_ubaCs4.regs0 LibSegJu_ubaCs4.regs_out0 KS_ubaCs4 = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaCs4_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#200La+v24#178+v22#200B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#:0#40_v2#60#28,1,14X#37?;<#:?0><Y,T,1#363><T,2_v2#:0T,8#20T,9#10T,:#400T,;#20T,<#10T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#38194"%pstring.
Lemma ubaCs4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaCs4] fx R M V ubaCs4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaCs4] LibSegJu_ubaCs4.regs0 LibSegJu_ubaCs4.kn0 LibSegJu_ubaCs4.BR LibSegJu_ubaCs4.PSS LibSegJu_ubaCs4.NX0 LibSegJu_ubaCs4.F0 229308 LibSegJu_ubaCs4.seg_sound_ax fx R M V ubaCs4_conc_s. Qed.
Definition KS_ubaCs5 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaCs5.regs0 LibSegJu_ubaCs5.regs_out0).
Lemma KS_ubaCs5_ok : BG.kept_ok 64 LibSegJu_ubaCs5.regs0 LibSegJu_ubaCs5.regs_out0 KS_ubaCs5 = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaCs5_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#400La+v24#178+v22#400B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#:0#40_v2#60#28,1,14X#37?;<#:?0><Y,T,1#363><T,2_v2#:0T,8#40T,9#20T,:#800T,;#40T,<#20T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#38194"%pstring.
Lemma ubaCs5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaCs5] fx R M V ubaCs5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaCs5] LibSegJu_ubaCs5.regs0 LibSegJu_ubaCs5.kn0 LibSegJu_ubaCs5.BR LibSegJu_ubaCs5.PSS LibSegJu_ubaCs5.NX0 LibSegJu_ubaCs5.F0 229308 LibSegJu_ubaCs5.seg_sound_ax fx R M V ubaCs5_conc_s. Qed.
Definition KS_ubaCs6 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaCs6.regs0 LibSegJu_ubaCs6.regs_out0).
Lemma KS_ubaCs6_ok : BG.kept_ok 64 LibSegJu_ubaCs6.regs0 LibSegJu_ubaCs6.regs_out0 KS_ubaCs6 = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaCs6_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#800La+v24#178+v22#800B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#:0#40_v2#60#28,1,14X#37?;<#:?0><Y,T,1#363><T,2_v2#:0T,8#80T,9#40T,:#1000T,;#80T,<#40T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#38194"%pstring.
Lemma ubaCs6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaCs6] fx R M V ubaCs6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaCs6] LibSegJu_ubaCs6.regs0 LibSegJu_ubaCs6.kn0 LibSegJu_ubaCs6.BR LibSegJu_ubaCs6.PSS LibSegJu_ubaCs6.NX0 LibSegJu_ubaCs6.F0 229308 LibSegJu_ubaCs6.seg_sound_ax fx R M V ubaCs6_conc_s. Qed.
Definition KS_ubaCs7 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaCs7.regs0 LibSegJu_ubaCs7.regs_out0).
Lemma KS_ubaCs7_ok : BG.kept_ok 64 LibSegJu_ubaCs7.regs0 LibSegJu_ubaCs7.regs_out0 KS_ubaCs7 = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaCs7_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#1000La+v24#178+v22#1000B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#:0#40_v2#60#28,1,14X#37?;<#:?0><Y,T,1#363><T,2_v2#:0T,8#100T,9#80T,:#2000T,;#100T,<#80T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#38194"%pstring.
Lemma ubaCs7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaCs7] fx R M V ubaCs7_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaCs7] LibSegJu_ubaCs7.regs0 LibSegJu_ubaCs7.kn0 LibSegJu_ubaCs7.BR LibSegJu_ubaCs7.PSS LibSegJu_ubaCs7.NX0 LibSegJu_ubaCs7.F0 229308 LibSegJu_ubaCs7.seg_sound_ax fx R M V ubaCs7_conc_s. Qed.
Definition KS_ubaCs8 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaCs8.regs0 LibSegJu_ubaCs8.regs_out0).
Lemma KS_ubaCs8_ok : BG.kept_ok 64 LibSegJu_ubaCs8.regs0 LibSegJu_ubaCs8.regs_out0 KS_ubaCs8 = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaCs8_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#2000La+v24#178+v22#2000B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#:0#40_v2#60#28,1,14X#37?;<#:?0><Y,T,1#363><T,2_v2#:0T,8#200T,9#100T,:#4000T,;#200T,<#100T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#38194"%pstring.
Lemma ubaCs8_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaCs8] fx R M V ubaCs8_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaCs8] LibSegJu_ubaCs8.regs0 LibSegJu_ubaCs8.kn0 LibSegJu_ubaCs8.BR LibSegJu_ubaCs8.PSS LibSegJu_ubaCs8.NX0 LibSegJu_ubaCs8.F0 229308 LibSegJu_ubaCs8.seg_sound_ax fx R M V ubaCs8_conc_s. Qed.
Definition KS_ubaCs9 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaCs9.regs0 LibSegJu_ubaCs9.regs_out0).
Lemma KS_ubaCs9_ok : BG.kept_ok 64 LibSegJu_ubaCs9.regs0 LibSegJu_ubaCs9.regs_out0 KS_ubaCs9 = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaCs9_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#4000La+v24#178+v22#4000B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#:0#40_v2#60#28,1,14X#37?;<#:?0><Y,T,1#363><T,2_v2#:0T,8#400T,9#200T,:#8000T,;#400T,<#200T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#38194"%pstring.
Lemma ubaCs9_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaCs9] fx R M V ubaCs9_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaCs9] LibSegJu_ubaCs9.regs0 LibSegJu_ubaCs9.kn0 LibSegJu_ubaCs9.BR LibSegJu_ubaCs9.PSS LibSegJu_ubaCs9.NX0 LibSegJu_ubaCs9.F0 229308 LibSegJu_ubaCs9.seg_sound_ax fx R M V ubaCs9_conc_s. Qed.
Definition KS_ubaCs10 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_ubaCs10.regs0 LibSegJu_ubaCs10.regs_out0).
Lemma KS_ubaCs10_ok : BG.kept_ok 64 LibSegJu_ubaCs10.regs0 LibSegJu_ubaCs10.regs_out0 KS_ubaCs10 = true. Proof. vm_compute. reflexivity. Qed.
Definition ubaCs10_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#8000La+v24#178+v22#8000B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#:0#40_v2#60#28,1,14X#37?;<#:?0><Y,T,1#363><T,2_v2#:0T,8#800T,9#400T,:#10000T,;#800T,<#400T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#38194"%pstring.
Lemma ubaCs10_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ubaCs10] fx R M V ubaCs10_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ubaCs10] LibSegJu_ubaCs10.regs0 LibSegJu_ubaCs10.kn0 LibSegJu_ubaCs10.BR LibSegJu_ubaCs10.PSS LibSegJu_ubaCs10.NX0 LibSegJu_ubaCs10.F0 229308 LibSegJu_ubaCs10.seg_sound_ax fx R M V ubaCs10_conc_s. Qed.
End PMBAUP3C.
