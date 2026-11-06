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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJu_uboCs0 LibSegJu_uboCs1 LibSegJu_uboCs2 LibSegJu_uboCs3 LibSegJu_uboCs4 LibSegJu_uboCs5 LibSegJu_uboCs6 LibSegJu_uboCs7 LibSegJu_uboCs8 LibSegJu_uboCs9 LibSegJu_uboCs10.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBOUP3C.
Module BG := BigLinkGlueUb0.BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcU.
Definition KS_uboCs0 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboCs0.regs0 LibSegJu_uboCs0.regs_out0).
Lemma KS_uboCs0_ok : BG.kept_ok 64 LibSegJu_uboCs0.regs0 LibSegJu_uboCs0.regs_out0 KS_uboCs0 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition uboCs0_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#20La+v24#178+v22#20B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#:0#40_v2#60#28,1,14X#38484#:?0><Y,T,1#363><T,2_v2#:0T,8#2T,9#1T,:#40T,;#2T,<#1T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#3865<"%pstring.
Lemma uboCs0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboCs0] fx R M V uboCs0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboCs0] LibSegJu_uboCs0.regs0 LibSegJu_uboCs0.kn0 LibSegJu_uboCs0.BR LibSegJu_uboCs0.PSS LibSegJu_uboCs0.NX0 LibSegJu_uboCs0.F0 230532 LibSegJu_uboCs0.seg_sound_ax fx R M V uboCs0_conc_s. Qed.
Definition KS_uboCs1 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboCs1.regs0 LibSegJu_uboCs1.regs_out0).
Lemma KS_uboCs1_ok : BG.kept_ok 64 LibSegJu_uboCs1.regs0 LibSegJu_uboCs1.regs_out0 KS_uboCs1 = true. Proof. vm_compute. reflexivity. Qed.
Definition uboCs1_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#40La+v24#178+v22#40B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#:0#40_v2#60#28,1,14X#38484#:?0><Y,T,1#363><T,2_v2#:0T,8#4T,9#2T,:#80T,;#4T,<#2T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#3865<"%pstring.
Lemma uboCs1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboCs1] fx R M V uboCs1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboCs1] LibSegJu_uboCs1.regs0 LibSegJu_uboCs1.kn0 LibSegJu_uboCs1.BR LibSegJu_uboCs1.PSS LibSegJu_uboCs1.NX0 LibSegJu_uboCs1.F0 230532 LibSegJu_uboCs1.seg_sound_ax fx R M V uboCs1_conc_s. Qed.
Definition KS_uboCs2 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboCs2.regs0 LibSegJu_uboCs2.regs_out0).
Lemma KS_uboCs2_ok : BG.kept_ok 64 LibSegJu_uboCs2.regs0 LibSegJu_uboCs2.regs_out0 KS_uboCs2 = true. Proof. vm_compute. reflexivity. Qed.
Definition uboCs2_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#80La+v24#178+v22#80B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#:0#40_v2#60#28,1,14X#38484#:?0><Y,T,1#363><T,2_v2#:0T,8#8T,9#4T,:#100T,;#8T,<#4T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#3865<"%pstring.
Lemma uboCs2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboCs2] fx R M V uboCs2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboCs2] LibSegJu_uboCs2.regs0 LibSegJu_uboCs2.kn0 LibSegJu_uboCs2.BR LibSegJu_uboCs2.PSS LibSegJu_uboCs2.NX0 LibSegJu_uboCs2.F0 230532 LibSegJu_uboCs2.seg_sound_ax fx R M V uboCs2_conc_s. Qed.
Definition KS_uboCs3 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboCs3.regs0 LibSegJu_uboCs3.regs_out0).
Lemma KS_uboCs3_ok : BG.kept_ok 64 LibSegJu_uboCs3.regs0 LibSegJu_uboCs3.regs_out0 KS_uboCs3 = true. Proof. vm_compute. reflexivity. Qed.
Definition uboCs3_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#100La+v24#178+v22#100B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#:0#40_v2#60#28,1,14X#38484#:?0><Y,T,1#363><T,2_v2#:0T,8#10T,9#8T,:#200T,;#10T,<#8T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#3865<"%pstring.
Lemma uboCs3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboCs3] fx R M V uboCs3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboCs3] LibSegJu_uboCs3.regs0 LibSegJu_uboCs3.kn0 LibSegJu_uboCs3.BR LibSegJu_uboCs3.PSS LibSegJu_uboCs3.NX0 LibSegJu_uboCs3.F0 230532 LibSegJu_uboCs3.seg_sound_ax fx R M V uboCs3_conc_s. Qed.
Definition KS_uboCs4 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboCs4.regs0 LibSegJu_uboCs4.regs_out0).
Lemma KS_uboCs4_ok : BG.kept_ok 64 LibSegJu_uboCs4.regs0 LibSegJu_uboCs4.regs_out0 KS_uboCs4 = true. Proof. vm_compute. reflexivity. Qed.
Definition uboCs4_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#200La+v24#178+v22#200B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#:0#40_v2#60#28,1,14X#38484#:?0><Y,T,1#363><T,2_v2#:0T,8#20T,9#10T,:#400T,;#20T,<#10T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#3865<"%pstring.
Lemma uboCs4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboCs4] fx R M V uboCs4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboCs4] LibSegJu_uboCs4.regs0 LibSegJu_uboCs4.kn0 LibSegJu_uboCs4.BR LibSegJu_uboCs4.PSS LibSegJu_uboCs4.NX0 LibSegJu_uboCs4.F0 230532 LibSegJu_uboCs4.seg_sound_ax fx R M V uboCs4_conc_s. Qed.
Definition KS_uboCs5 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboCs5.regs0 LibSegJu_uboCs5.regs_out0).
Lemma KS_uboCs5_ok : BG.kept_ok 64 LibSegJu_uboCs5.regs0 LibSegJu_uboCs5.regs_out0 KS_uboCs5 = true. Proof. vm_compute. reflexivity. Qed.
Definition uboCs5_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#400La+v24#178+v22#400B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#:0#40_v2#60#28,1,14X#38484#:?0><Y,T,1#363><T,2_v2#:0T,8#40T,9#20T,:#800T,;#40T,<#20T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#3865<"%pstring.
Lemma uboCs5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboCs5] fx R M V uboCs5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboCs5] LibSegJu_uboCs5.regs0 LibSegJu_uboCs5.kn0 LibSegJu_uboCs5.BR LibSegJu_uboCs5.PSS LibSegJu_uboCs5.NX0 LibSegJu_uboCs5.F0 230532 LibSegJu_uboCs5.seg_sound_ax fx R M V uboCs5_conc_s. Qed.
Definition KS_uboCs6 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboCs6.regs0 LibSegJu_uboCs6.regs_out0).
Lemma KS_uboCs6_ok : BG.kept_ok 64 LibSegJu_uboCs6.regs0 LibSegJu_uboCs6.regs_out0 KS_uboCs6 = true. Proof. vm_compute. reflexivity. Qed.
Definition uboCs6_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#800La+v24#178+v22#800B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#:0#40_v2#60#28,1,14X#38484#:?0><Y,T,1#363><T,2_v2#:0T,8#80T,9#40T,:#1000T,;#80T,<#40T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#3865<"%pstring.
Lemma uboCs6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboCs6] fx R M V uboCs6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboCs6] LibSegJu_uboCs6.regs0 LibSegJu_uboCs6.kn0 LibSegJu_uboCs6.BR LibSegJu_uboCs6.PSS LibSegJu_uboCs6.NX0 LibSegJu_uboCs6.F0 230532 LibSegJu_uboCs6.seg_sound_ax fx R M V uboCs6_conc_s. Qed.
Definition KS_uboCs7 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboCs7.regs0 LibSegJu_uboCs7.regs_out0).
Lemma KS_uboCs7_ok : BG.kept_ok 64 LibSegJu_uboCs7.regs0 LibSegJu_uboCs7.regs_out0 KS_uboCs7 = true. Proof. vm_compute. reflexivity. Qed.
Definition uboCs7_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#1000La+v24#178+v22#1000B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#:0#40_v2#60#28,1,14X#38484#:?0><Y,T,1#363><T,2_v2#:0T,8#100T,9#80T,:#2000T,;#100T,<#80T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#3865<"%pstring.
Lemma uboCs7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboCs7] fx R M V uboCs7_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboCs7] LibSegJu_uboCs7.regs0 LibSegJu_uboCs7.kn0 LibSegJu_uboCs7.BR LibSegJu_uboCs7.PSS LibSegJu_uboCs7.NX0 LibSegJu_uboCs7.F0 230532 LibSegJu_uboCs7.seg_sound_ax fx R M V uboCs7_conc_s. Qed.
Definition KS_uboCs8 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboCs8.regs0 LibSegJu_uboCs8.regs_out0).
Lemma KS_uboCs8_ok : BG.kept_ok 64 LibSegJu_uboCs8.regs0 LibSegJu_uboCs8.regs_out0 KS_uboCs8 = true. Proof. vm_compute. reflexivity. Qed.
Definition uboCs8_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#2000La+v24#178+v22#2000B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#:0#40_v2#60#28,1,14X#38484#:?0><Y,T,1#363><T,2_v2#:0T,8#200T,9#100T,:#4000T,;#200T,<#100T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#3865<"%pstring.
Lemma uboCs8_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboCs8] fx R M V uboCs8_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboCs8] LibSegJu_uboCs8.regs0 LibSegJu_uboCs8.kn0 LibSegJu_uboCs8.BR LibSegJu_uboCs8.PSS LibSegJu_uboCs8.NX0 LibSegJu_uboCs8.F0 230532 LibSegJu_uboCs8.seg_sound_ax fx R M V uboCs8_conc_s. Qed.
Definition KS_uboCs9 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboCs9.regs0 LibSegJu_uboCs9.regs_out0).
Lemma KS_uboCs9_ok : BG.kept_ok 64 LibSegJu_uboCs9.regs0 LibSegJu_uboCs9.regs_out0 KS_uboCs9 = true. Proof. vm_compute. reflexivity. Qed.
Definition uboCs9_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#4000La+v24#178+v22#4000B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#:0#40_v2#60#28,1,14X#38484#:?0><Y,T,1#363><T,2_v2#:0T,8#400T,9#200T,:#8000T,;#400T,<#200T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#3865<"%pstring.
Lemma uboCs9_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboCs9] fx R M V uboCs9_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboCs9] LibSegJu_uboCs9.regs0 LibSegJu_uboCs9.kn0 LibSegJu_uboCs9.BR LibSegJu_uboCs9.PSS LibSegJu_uboCs9.NX0 LibSegJu_uboCs9.F0 230532 LibSegJu_uboCs9.seg_sound_ax fx R M V uboCs9_conc_s. Qed.
Definition KS_uboCs10 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJu_uboCs10.regs0 LibSegJu_uboCs10.regs_out0).
Lemma KS_uboCs10_ok : BG.kept_ok 64 LibSegJu_uboCs10.regs0 LibSegJu_uboCs10.regs_out0 KS_uboCs10 = true. Proof. vm_compute. reflexivity. Qed.
Definition uboCs10_conc_s := ",27A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18S,15#?>00B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v24#7????????>80Hv24#8P_v2#:0#:0v24#180B#7???7?8000:0v26#7??????????0Hv26#8P_v2#:0#:0v26#10B#7???7?8000:0v25#7??????????8Hv25#8P_v2#:0#:0v25#8O#10000#;7120Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#8000La+v24#178+v22#8000B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#:0#40_v2#60#28,1,14X#38484#:?0><Y,T,1#363><T,2_v2#:0T,8#800T,9#400T,:#10000T,;#800T,<#400T,=+v24#168T,>v22T,13v30T,14+v24#168Lb_v2#:0_v2#60Lb_v2#98#36208Lb_v2#40+v24#168Lb_v2#48#Lb_v2#88v26Lb_v2#80v24Lb_v2#78#3865<"%pstring.
Lemma uboCs10_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uboCs10] fx R M V uboCs10_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uboCs10] LibSegJu_uboCs10.regs0 LibSegJu_uboCs10.kn0 LibSegJu_uboCs10.BR LibSegJu_uboCs10.PSS LibSegJu_uboCs10.NX0 LibSegJu_uboCs10.F0 230532 LibSegJu_uboCs10.seg_sound_ax fx R M V uboCs10_conc_s. Qed.
End PMBOUP3C.
